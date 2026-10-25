// Matchmaking backend for the ranked beta - HTTP long-poll version (no dependencies).
// Run: node server.js        (Node 18+)
//
// Same match logic as the WebSocket prototype; only the transport changed so the
// UE4SS Lua mod can talk to it through curl.exe.
//
// POST /hello        {playerId}            -> {token}        (all other calls need header X-Token)
// POST /queue        {}                    -> {ok}
// POST /leave_queue  {}                    -> {ok}
// POST /ready        {}                    -> {ok}
// POST /leave        {}                    -> {ok}          (player quit: ends their match right away)
// POST /map_complete {mapIndex:0..4}       -> {ok}
// GET  /leaderboard                       -> {top:[{pos,name,elo,you}], you:{pos,name,elo}, total}

// GET  /events?since=N                     -> {events:[{seq,type,...}], last}   (long-poll, holds ~20s)
// GET  /health                             -> {ok}
//
// Event types (same as before): queued, left_queue, match_found, start,
// opponent_progress, match_cancelled, result

const http = require("http");
const crypto = require("crypto");
const fs = require("fs");
const pathLib = require("path");

const PORT = process.env.PORT || 8080;
const MAPS = ["level0", "garagelevel2", "thehub", "electricalstation", "office", "hotel", "boilerroom", "levelfun", "poolrooms", "levelrun", "theend", "animatedkingdom", "lightsout", "cavelevel", "level05", "level9", "level10", "level3999", "level07", "snackrooms", "leveldash", "level188_expanded", "waterpark_level01_p", "waterpark_level02_p", "waterpark_level03_p", "zone1_modified", "zone2_modified", "zone3_baked", "level52", "tunnellevel", "grassrooms_expanded"]; // TODO: your real map IDs
const MAPS_PER_MATCH = 5;
const COUNTDOWN_MS = 3000;
const READY_TIMEOUT_MS = 60000; // time allowed for both players to load their saves
const POLL_HOLD_MS = 20000;     // how long an /events request is held open
const PLAYER_TIMEOUT_MS = 30000; // no poll for this long = player disconnected

const players = new Map();  // playerId -> player
const sessions = new Map(); // token -> player
const queue = [];           // players waiting for a match
const matches = new Map();  // matchId -> match

// Track which players have frozen (CanMove=false)
const frozenPlayers = new Map(); // playerId -> bool

// ---------- Elo ratings ----------
// Same formulas as the Desmos version:
//   E(x,y) = 1 / (1 + 10^((y-x)/400))     K = 32 (flat)
//   delta  = K * (s - E)                  new elo = max(0, elo + delta)
// s = 1 win / 0 loss.
// Placements: a new player is UNRATED (elo = null) for their first 5 matches. When the 5th match
// ends their elo becomes (placement wins) * 240, so 5/5 wins = 1200. After that normal Elo applies.
// An unrated opponent counts as UNRATED_ASSUMED_ELO in a rated player's Elo calculation.
// A forfeit / disconnect during a running match counts as a loss. Cancelled matches (nobody
// finished loading) are not rated.
const PLACEMENT_MATCHES = 5;
const PLACEMENT_ELO_PER_WIN = 240;
const UNRATED_ASSUMED_ELO = 1000;
const K_FACTOR = 32;

// Matchmaking: a rated pair may play when their elo difference is within BOTH players' search
// range. The range starts at +-250 and grows by 100 every 10 seconds in the queue. Unrated players
// can be matched with anyone (other unrated players, or rated players below UNRATED_MAX_OPP_ELO).
const MM_START_RANGE = 250;
const MM_RANGE_STEP = 100;
const MM_STEP_MS = Number(process.env.MM_STEP_MS) || 10000;
const UNRATED_MAX_OPP_ELO = 2000;
const RATINGS_FILE = process.env.RATINGS_FILE || pathLib.join(__dirname, "ratings.json");

const eloExpected = (x, y) => 1 / (1 + 10 ** ((y - x) / 400));
const eloDelta = (x, y, s) => Math.round(K_FACTOR * (s - eloExpected(x, y)));

const isRated = (r) => r.elo !== null && r.elo !== undefined;
const effElo = (r) => (isRated(r) ? r.elo : UNRATED_ASSUMED_ELO);
const pubElo = (r) => (isRated(r) ? r.elo : null);        // what clients see: null = unrated
const placedOf = (r) => (isRated(r) ? null : r.played);   // placement matches played so far

let ratings = {}; // playerId -> { elo (null = unrated), played, wins, pwins (placement wins), name }
try { ratings = JSON.parse(fs.readFileSync(RATINGS_FILE, "utf8")); } catch { ratings = {}; }
// Records from before placements existed: anyone with fewer than 5 matches goes back to unrated.
for (const r of Object.values(ratings)) {
  if (r.pwins === undefined) {
    if ((r.played || 0) < PLACEMENT_MATCHES) { r.elo = null; r.pwins = Math.min(r.wins || 0, r.played || 0); }
    else r.pwins = 0;
  }
}

let saveTimer = null;
function saveRatings() {
  if (saveTimer) return;
  saveTimer = setTimeout(() => {
    saveTimer = null;
    const tmp = RATINGS_FILE + ".tmp";
    fs.writeFile(tmp, JSON.stringify(ratings), (err) => {
      if (err) return console.error("ratings save failed:", err.message);
      fs.rename(tmp, RATINGS_FILE, (e) => { if (e) console.error("ratings save failed:", e.message); });
    });
  }, 1000);
}

function getRating(id, name) {
  let r = ratings[id];
  if (!r) {
    r = ratings[id] = { elo: null, played: 0, wins: 0, pwins: 0, name: name || id };
    saveRatings();
  }
  return r;
}

function applyResult(r, oppElo, won) {
  if (isRated(r)) {
    r.elo = Math.max(0, r.elo + eloDelta(r.elo, oppElo, won ? 1 : 0));
  } else {
    if (won) r.pwins = (r.pwins || 0) + 1;
    if (r.played + 1 >= PLACEMENT_MATCHES) r.elo = (r.pwins || 0) * PLACEMENT_ELO_PER_WIN;
  }
  r.played++;
  if (won) r.wins++;
}

// Top 100 by Elo. Only display names go out, never player ids; "you" is flagged server-side
// (by the caller's token) so two players with the same name can't be confused.
const LEADERBOARD_SIZE = 100;
const shownName = (id, r) => (!r.name || r.name === id ? "Unknown" : r.name);

function buildLeaderboard(me) {
  const all = Object.entries(ratings)
    .filter(([, r]) => isRated(r))
    .map(([id, r]) => ({ id, name: shownName(id, r), elo: r.elo, wins: r.wins || 0, played: r.played }))
    .sort((x, y) => y.elo - x.elo || y.wins - x.wins || x.played - y.played);
  const top = all.slice(0, LEADERBOARD_SIZE).map((e, i) => ({ pos: i + 1, name: e.name, elo: e.elo, you: e.id === me.id }));
  const idx = all.findIndex((e) => e.id === me.id);
  const mine = ratings[me.id];
  const you = {
    pos: idx === -1 ? null : idx + 1, // null = still unrated (placements)
    name: mine ? shownName(me.id, mine) : "Unknown",
    elo: mine ? pubElo(mine) : null,
    placed: mine ? placedOf(mine) : 0,
  };
  return { top, you, total: all.length };
}

// ---------- transport helpers ----------

function json(res, code, obj) {
  res.writeHead(code, { "Content-Type": "application/json" });
  res.end(JSON.stringify(obj));
}

function readJson(req) {
  return new Promise((resolve) => {
    let data = "";
    req.on("data", (c) => { data += c; if (data.length > 10000) req.destroy(); });
    req.on("end", () => { try { resolve(JSON.parse(data || "{}")); } catch { resolve({}); } });
    req.on("error", () => resolve({}));
  });
}

// Queue an event for a player and wake their held /events request (if any).
function send(p, msg) {
  p.events.push({ seq: ++p.seq, ...msg });
  flushPoll(p);
}

// Check if both players in a match are frozen, and start countdown
function checkBothFrozen(match) {
  const a = match.players[0];
  const b = match.players[1];
  const aFrozen = frozenPlayers.get(a.id);
  const bFrozen = frozenPlayers.get(b.id);

        if (aFrozen && bFrozen) {
        // Both players are frozen, start countdown!
    clearTimeout(match.readyTimer);
    match.state = "running";
    match.startsAt = Date.now() + COUNTDOWN_MS;

        console.log(`Match ${match.id} starting (frozen start)`);
    
    // Generate fusebox configuration using the match seed
    const fuseboxes = generateFuseboxConfiguration(match.seed);
    console.log(`Match ${match.id} fusebox config:`, fuseboxes);
    
    for (const x of match.players) {
      send(x, { type: "start", countdownMs: COUNTDOWN_MS, fuseboxes });
    }
    
    // Clear frozen status
    frozenPlayers.delete(a.id);
    frozenPlayers.delete(b.id);
  }
}

function flushPoll(p, force = false) {
  if (!p.poll) return;
  if (!force && p.events.length === 0) return;
  const { res, timer } = p.poll;
  clearTimeout(timer);
  p.poll = null;
  p.lastSeen = Date.now();
  json(res, 200, { events: p.events, last: p.seq });
}

// ---------- match logic (unchanged from the prototype) ----------

function pickMaps() {
  const pool = [...MAPS];
  for (let i = pool.length - 1; i > 0; i--) {
    const j = crypto.randomInt(i + 1);
    [pool[i], pool[j]] = [pool[j], pool[i]];
  }
  return pool.slice(0, MAPS_PER_MATCH);
}

// Current search range of a queued player (+- this many elo).
function searchRange(p, now) {
  return MM_START_RANGE + MM_RANGE_STEP * Math.floor((now - (p.queuedAt || now)) / MM_STEP_MS);
}

function compatible(p, q, now) {
  const rp = getRating(p.id, p.name), rq = getRating(q.id, q.name);
  if (!isRated(rp) && !isRated(rq)) return true;                    // both unrated
  if (!isRated(rp)) return rq.elo < UNRATED_MAX_OPP_ELO;            // unrated vs rated
  if (!isRated(rq)) return rp.elo < UNRATED_MAX_OPP_ELO;
  return Math.abs(rp.elo - rq.elo) <= Math.min(searchRange(p, now), searchRange(q, now));
}

// Longest-waiting player first; each gets the closest compatible opponent.
function tryMatch() {
  const now = Date.now();
  let found = true;
  while (found && queue.length >= 2) {
    found = false;
    for (let i = 0; i < queue.length && !found; i++) {
      let best = -1, bestDiff = Infinity;
      for (let j = 0; j < queue.length; j++) {
        if (j === i || !compatible(queue[i], queue[j], now)) continue;
        const d = Math.abs(effElo(getRating(queue[i].id)) - effElo(getRating(queue[j].id)));
        if (d < bestDiff) { best = j; bestDiff = d; }
      }
      if (best !== -1) {
        const p = queue[i], q = queue[best];
        queue.splice(Math.max(i, best), 1);
        queue.splice(Math.min(i, best), 1);
        console.log(`Matchmaking: ${p.name} (${pubElo(getRating(p.id))}) vs ${q.name} (${pubElo(getRating(q.id))}), ranges ${searchRange(p, now)}/${searchRange(q, now)}`);
        createMatch(p, q);
        found = true;
      }
    }
  }
}

function createMatch(a, b) {
  const match = {
    id: crypto.randomUUID(),
    players: [a, b],
    maps: pickMaps(), // same maps, same order for both players
    state: "loading", // loading -> running -> ended
    startsAt: 0,
    readyTimer: null,
    mapSplits: {}, // track split times per player per map
    seed: generateSeed(), // generate seed immediately when match is created
  };
  matches.set(match.id, match);
  console.log(`Match ${match.id} created with seed: ${match.seed}`);
  for (const p of match.players) {
    p.matchId = match.id;
    p.progress = 0;
    p.ready = false;
    match.mapSplits[p.id] = {};
  }
    match.readyTimer = setTimeout(() => cancelMatch(match, "ready_timeout"), READY_TIMEOUT_MS);
  const ra = getRating(a.id, a.name), rb = getRating(b.id, b.name);
  send(a, { type: "match_found", matchId: match.id, maps: match.maps, opponent: b.id, opponentName: b.name, seed: match.seed.toString(), elo: pubElo(ra), opponentElo: pubElo(rb), placed: placedOf(ra), opponentPlaced: placedOf(rb), playerName: a.name });
  send(b, { type: "match_found", matchId: match.id, maps: match.maps, opponent: a.id, opponentName: a.name, seed: match.seed.toString(), elo: pubElo(rb), opponentElo: pubElo(ra), placed: placedOf(rb), opponentPlaced: placedOf(ra), playerName: b.name });
}

function cancelMatch(match, reason) {
  if (match.state !== "loading") return;
  match.state = "ended";
  clearTimeout(match.readyTimer);
  for (const p of match.players) {
    p.matchId = null;
    send(p, { type: "match_cancelled", reason });
  }
  matches.delete(match.id);
}

function endMatch(match, winner, reason) {
  if (match.state === "ended") return;
  match.state = "ended";
  clearTimeout(match.readyTimer);

    // Calculate cumulative splits for both players
  const getSplits = (p) => {
    const splits = [];
    let cumulative = 0;
    for (const mapName of match.maps) {
      const mapTime = match.mapSplits && match.mapSplits[p.id] && match.mapSplits[p.id][mapName];
      if (mapTime !== undefined) {
        cumulative += mapTime;
        splits.push(cumulative);
      } else {
        splits.push(null);
      }
    }
    return splits;
  };

  const a = match.players[0];
  const b = match.players[1];
  const aSplits = getSplits(a);
  const bSplits = getSplits(b);
  const aTotal = aSplits.length > 0 && aSplits[aSplits.length - 1] ? aSplits[aSplits.length - 1] : 0;
  const bTotal = bSplits.length > 0 && bSplits[bSplits.length - 1] ? bSplits[bSplits.length - 1] : 0;

  // Rate the match. Both sides use the opponent's PRE-match rating.
  const ra = getRating(a.id, a.name), rb = getRating(b.id, b.name);
  const before = { [a.id]: pubElo(ra), [b.id]: pubElo(rb) };
  const oppOfA = effElo(rb), oppOfB = effElo(ra);
  applyResult(ra, oppOfA, winner === a);
  applyResult(rb, oppOfB, winner === b);
  saveRatings();
  console.log(`Match ${match.id} rated: ${a.name} ${before[a.id]} -> ${pubElo(ra)}, ${b.name} ${before[b.id]} -> ${pubElo(rb)}`);

  for (const p of match.players) {
    const won = p === winner;
    p.matchId = null;
    const opp = p === a ? b : a;
    const oppSplits = p === a ? bSplits : aSplits;
    const oppTotal = p === a ? bTotal : aTotal;
    const pSplits = p === a ? aSplits : bSplits;
    const pTotal = p === a ? aTotal : bTotal;
    const mine = p === a ? ra : rb;
    const theirs = p === a ? rb : ra;
    send(p, {
      type: "result",
      won,
      reason,
      message: won ? "You won!" : "You lost!",
      timeMs: pTotal,
      splits: pSplits,
      oppSplits: oppSplits,
      oppTimeMs: oppTotal,
      eloBefore: before[p.id],                 // null = was unrated
      eloAfter: pubElo(mine),                  // null = still unrated
      eloDelta: (before[p.id] !== null && isRated(mine)) ? mine.elo - before[p.id] : null,
      oppEloAfter: pubElo(theirs),
      played: mine.played,
      placed: placedOf(mine),                  // placement matches played, only while unrated
      placementWins: mine.pwins || 0
    });
  }
  matches.delete(match.id);
}

const opponentOf = (match, p) => match.players.find((x) => x !== p);

function handleLeave(p) {
  const qi = queue.indexOf(p);
  if (qi !== -1) queue.splice(qi, 1);
  const match = p.matchId && matches.get(p.matchId);
  if (!match) return;
  if (match.state === "running") endMatch(match, opponentOf(match, p), "opponent_left");
  else if (match.state === "loading") cancelMatch(match, "opponent_left");
}

function dropPlayer(p) {
  handleLeave(p);
  if (p.poll) {
    clearTimeout(p.poll.timer);
    json(p.poll.res, 200, { events: [], last: p.seq });
    p.poll = null;
  }
  if (players.get(p.id) === p) players.delete(p.id);
  sessions.delete(p.token);
}

// ---------- actions ----------

function doQueue(p) {
  if (p.matchId || queue.includes(p)) return;
  p.queuedAt = Date.now();
  queue.push(p);
  send(p, { type: "queued" });
  tryMatch();
}

function doLeaveQueue(p) {
  const i = queue.indexOf(p);
  if (i !== -1) { queue.splice(i, 1); send(p, { type: "left_queue" }); }
}

// Generate a random seed for the match
function generateSeed() {
  return Math.floor(Math.random() * 9000000000) + 1000000000;
}

// Seeded random number generator (uses match seed for deterministic results)
function seededRandom(seed, min, max) {
  const x = Math.sin(seed++) * 10000;
  const rand = x - Math.floor(x);
  return Math.floor(rand * (max - min + 1)) + min;
}

// Fisher-Yates shuffle with seed
function shuffleWithSeed(array, seed) {
  const arr = [...array];
  let currentSeed = seed;
  for (let i = arr.length - 1; i > 0; i--) {
    const j = seededRandom(currentSeed++, 0, i);
    [arr[i], arr[j]] = [arr[j], arr[i]];
  }
  return arr;
}

// Generate fusebox configuration using the match seed
function generateFuseboxConfiguration(seed) {
  // East: 0-7 except 3
  const eastPool = [0, 1, 2, 4, 5, 6, 7];
  // West: 8-11 and 3
  const westPool = [3, 8, 9, 10, 11];
  // Generator: 12-27 except 26
  const generatorPool = [12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 27];
  
  return {
    EastFuseboxes: shuffleWithSeed(eastPool, seed).slice(0, 3),
    WestFuseboxes: shuffleWithSeed(westPool, seed + 1).slice(0, 3),
    GeneratorFuseboxes: shuffleWithSeed(generatorPool, seed + 2).slice(0, 3),
    GarageElevatorExit: seededRandom(seed + 3, 0, 2)
  };
}

function doReady(p) {
  const match = p.matchId && matches.get(p.matchId);
  if (!match || match.state !== "loading") return;
  p.ready = true;
        if (match.players.every((x) => x.ready)) {
        clearTimeout(match.readyTimer);
        match.state = "running";
        match.startsAt = Date.now() + COUNTDOWN_MS;

        console.log(`Match ${match.id} starting`);
    
        // Generate fusebox configuration using the match seed
        const fuseboxes = generateFuseboxConfiguration(match.seed);
        console.log(`Match ${match.id} fusebox config:`, fuseboxes);
    
        for (const x of match.players) {
          send(x, { type: "start", countdownMs: COUNTDOWN_MS, fuseboxes });
        }
  }
}

function doMapComplete(p, mapIndex, timeMs) {
  const match = p.matchId && matches.get(p.matchId);
  if (!match || match.state !== "running") return;
  if (Date.now() < match.startsAt) return;  // ignore before countdown ends
  if (mapIndex !== p.progress) return;      // must finish maps in order

  // Track split time for this map
  if (!match.mapSplits[p.id]) match.mapSplits[p.id] = {};
  match.mapSplits[p.id][match.maps[mapIndex]] = timeMs;

  p.progress++;
  send(opponentOf(match, p), { type: "opponent_progress", mapsDone: p.progress, timeMs: timeMs });
  if (p.progress >= match.maps.length) endMatch(match, p, "finished");
}

// ---------- HTTP server ----------

const server = http.createServer(async (req, res) => {
  try {
    const url = new URL(req.url, "http://localhost");
    const path = url.pathname;

    if (req.method === "GET" && path === "/health") return json(res, 200, { ok: true });

        if (req.method === "POST" && path === "/hello") {
      const body = await readJson(req);
      const id = String(body.playerId || "").slice(0, 64);
      const name = String(body.playerName || id).slice(0, 32);
      if (!id) return json(res, 400, { error: "playerId required" });
      const old = players.get(id);
      if (old) dropPlayer(old); // same player reconnecting
      const p = {
        id, name, token: crypto.randomBytes(16).toString("hex"),
        matchId: null, progress: 0, ready: false,
        events: [], seq: 0, poll: null, lastSeen: Date.now(),
      };
      players.set(id, p);
      sessions.set(p.token, p);
      const rating = getRating(id, name);
      rating.name = name;
      return json(res, 200, { token: p.token, elo: pubElo(rating), placed: placedOf(rating), played: rating.played });
    }

    const player = sessions.get(req.headers["x-token"]);
    if (!player) return json(res, 401, { error: "unauthorized" });
    player.lastSeen = Date.now();

    if (req.method === "GET" && path === "/leaderboard") return json(res, 200, buildLeaderboard(player));

    if (req.method === "GET" && path === "/events") {
      const since = parseInt(url.searchParams.get("since")) || 0;
      player.events = player.events.filter((e) => e.seq > since); // client acks what it has seen
      if (player.poll) flushPoll(player, true);                   // release any older held request
      player.poll = { res, timer: setTimeout(() => flushPoll(player, true), POLL_HOLD_MS) };
      res.on("close", () => {
        if (player.poll && player.poll.res === res) {
          clearTimeout(player.poll.timer);
          player.poll = null;
          player.lastSeen = Date.now();
        }
      });
      flushPoll(player); // answer immediately if events are already waiting
      return;
    }

        if (req.method === "POST") {
      const body = await readJson(req);
      switch (path) {
        case "/queue": doQueue(player); break;
        case "/leave_queue": doLeaveQueue(player); break;
        case "/ready": doReady(player); break;
        case "/frozen": // player has set CanMove=false on their character
          if (player.matchId) {
            frozenPlayers.set(player.id, true);
            const match = matches.get(player.matchId);
            if (match && match.state === "loading") {
              checkBothFrozen(match);
            }
          }
          break;
                case "/leave": // game closed: end the match at once (opponent gets result/opponent_left)
                  console.log(`player ${player.id} left`);
                  dropPlayer(player);
                  break;
                case "/leave_match": // player forfeited by returning to menu/lobby during match
                  console.log(`player ${player.id} forfeited match (reason: ${body.reason || 'unknown'})`);
                  const forfeitMatch = player.matchId && matches.get(player.matchId);
                  if (forfeitMatch && forfeitMatch.state === "running") {
                    // Opponent wins
                    endMatch(forfeitMatch, opponentOf(forfeitMatch, player), "opponent_left");
                  }
                  // Clean up player state
                  player.matchId = null;
                  player.progress = 0;
                  player.ready = false;
                  break;
        case "/map_complete": doMapComplete(player, body.mapIndex, body.timeMs); break;
        case "/update_name": 
          if (body.playerName) {
            player.name = String(body.playerName).slice(0, 32);
            if (ratings[player.id]) ratings[player.id].name = player.name;
            console.log(`Player ${player.id} updated name to: ${player.name}`);
          }
          break;
        default: return json(res, 404, { error: "not_found" });
      }
      return json(res, 200, { ok: true });
    }

    json(res, 404, { error: "not_found" });
  } catch (e) {
    console.error(e);
    json(res, 500, { error: "server_error" });
  }
});

// Search ranges widen with time, so re-check the queue regularly.
setInterval(tryMatch, 1000);

// Disconnect detection: a player who isn't holding a poll and hasn't been seen recently is gone.
setInterval(() => {
  const now = Date.now();
  for (const p of [...players.values()]) {
    if (!p.poll && now - p.lastSeen > PLAYER_TIMEOUT_MS) {
      console.log(`player ${p.id} timed out`);
      dropPlayer(p);
    }
  }
}, 5000);

server.listen(PORT, () => console.log(`Matchmaking server (HTTP) listening on :${PORT}`));
