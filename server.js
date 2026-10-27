// Hurdle Jump multiplayer relay ("matchmaker") + global leaderboard.
//
// MULTIPLAYER. Players connect over WebSocket. Private race: a host CREATES a race with a name and
// up to 3 more players JOIN it with the same name. Public race: QUICK puts you in any open public
// lobby (or makes you the host of a new one). Empty spots are filled with CPU runners by the game
// itself; the server only forwards each player's small messages to the others in the same race.
//
// Protocol (JSON text frames). "v" = the game's multiplayer version: players only race the same v.
//   client -> server: {op:"create", room, info, v} | {op:"join", room, info, v} | {op:"quick", info, v}
//                     {op:"send", data} | {op:"lock"} (host: no more joins) | {op:"unlock"} | {op:"leave"}
//                     {op:"kick", id} (host: remove a player, e.g. one who stopped responding)
//   server -> client: {op:"joined", id, host, room, public, players:[{id, info}]} | {op:"peer_joined", id, info}
//                     {op:"peer_left", id} | {op:"host", id} (public race: the host left, this is the new one)
//                     {op:"msg", from, data} | {op:"closed"} (private race: the host left) | {op:"error", msg}
//                     {op:"kicked"} (you were removed by the host)
//
// LEADERBOARD (plain web requests, so it also works from the browser build). A player's "id" is a
// private random key their game made; "ref" is a public tag for an entry (a hash of the id) used to
// report it, so ids are never shown to anyone else.
//   GET  /leaderboard?id=<id>            -> {top: [{rank, ref, name, score, runner, champ, pic, border}], you: {rank, score, ref, name} | null, total}
//   POST /leaderboard        {id, num, score, runner, champ, pic, border, stats} -> the board (as GET) - your best run,
//                                           plus your profile (picture, border and stats others can look at)
//   GET  /leaderboard/profile?ref=<ref>  -> one player's profile: {rank, ref, name, score, runner, champ, pic, border,
//                                           stats, badges: {gold, silver, bronze}} (tap a picture on the board)
//   POST /leaderboard/name   {id, name}  -> the board, or {error} if the name isn't allowed
//   POST /leaderboard/delete {id}        -> {ok}: deletes everything the server keeps about that player (entry,
//                                           name, profile, stats, daily runs and medals, reports) - "Delete my data"
//   POST /leaderboard/report {id, ref}   -> {ok}. Reports never hide anything by themselves (no trolling):
//                                           they go on a list for the admin to review.
//   GET  /daily?id=<id>                  -> today's Daily Challenge: {day, seed, ends_in, today: top 3, yesterday,
//                                           you: {played, score, rank}, badges: {gold, silver, bronze}, total}
//   POST /daily  {id, num, day, score, secs} -> your one run for the day (the first one counts)
//   GET  /admin?key=<ADMIN_KEY>          (you only) a page listing reported names and the top 50, with
//                                           buttons to clear a name, remove an entry or dismiss reports
// Names: unique (ignoring capitals), 3-12 letters, numbers and single spaces, checked against a profanity filter (the "obscenity"
// package) and a reserved list. No name = "Player <number>".
// Storage: an Upstash Redis database when UPSTASH_REDIS_REST_URL and UPSTASH_REDIS_REST_TOKEN are set
// (see MULTIPLAYER_SETUP.md); otherwise memory only, which is wiped whenever the server restarts.
//
// Deploy: any Node 18+ host. Start command: `node server.js` (listens on $PORT, default 8080).
const http = require("http");
const crypto = require("crypto");
const { WebSocketServer } = require("ws");

const MAX_PLAYERS = 4;
const rooms = new Map(); // NAME -> {host, locked, public, v, players: Map(id -> {ws, info})}

// ---------------------------------------------------------------- names

// The profanity filter: the "obscenity" package, plus extra rules for spellings it misses and an
// allow-list for innocent words it trips on. If the package is missing for some reason, a small
// built-in list stands in so the server keeps running.

// Lower case, look-alike digits turned into letters ("sh1t" -> "shit").
function normalize(s) {
  return s.toLowerCase().replace(/0/g, "o").replace(/1/g, "i").replace(/3/g, "e").replace(/4/g, "a")
    .replace(/5/g, "s").replace(/7/g, "t").replace(/8/g, "b");
}

// Extra rules, checked on the normalized name (with and without its spaces). \b ("word edge") keeps
// innocent words safe, e.g. "grape", "Sussex", "Dickens", "Peacock".
const EXTRA = [/ph+u+c*k/, /\bf+u+c*k+/, /\bk+u+n+t/, /butt ?hole/, /butt ?plug/, /\bnazi/, /hitler/, /\bkkk\b/,
  /\brap(e|ist)\b/, /\bporn/, /\bcum\b/, /\banus\b/, /\btits?\b/, /\bboobs?\b/, /\bjizz/, /\bdildo/, /\bwhore/,
  /\bslut/, /\bhoe\b/, /\bpiss/, /\bwank/, /\btwat/, /\bpussy/, /\bdick\b/, /\bcock\b/, /\bfag/];
function extraBad(s) {
  const n = normalize(s);
  return EXTRA.some((r) => r.test(n) || r.test(n.replace(/ /g, "")));
}

// Innocent words a filter can trip on (taken out before checking).
const ALLOWED = ["shiitake"];
function withoutAllowed(s) {
  let out = s;
  for (const w of ALLOWED) out = out.replace(new RegExp(w, "ig"), " ");
  return out;
}

let packageBad;
try {
  const { RegExpMatcher, englishDataset, englishRecommendedTransformers } = require("obscenity");
  const matcher = new RegExpMatcher({ ...englishDataset.build(), ...englishRecommendedTransformers });
  packageBad = (s) => matcher.hasMatch(s);
} catch (err) {
  console.log("Name filter: the 'obscenity' package isn't installed - using a small built-in list.");
  const words = ["fuck", "shit", "cunt", "bitch", "nigg", "faggot", "pussy", "slut", "whore", "nazi", "penis", "vagina", "porn", "twat", "wank", "asshole"];
  packageBad = (s) => {
    const flat = normalize(s).replace(/[^a-z]/g, "");
    return words.some((w) => flat.includes(w));
  };
}

function isProfane(s) {
  const t = withoutAllowed(s);
  return packageBad(t) || extraBad(t);
}
// Names the game uses itself, or that could pass for staff.
const RESERVED = /^(cpu|admin|administrator|mod|moderator|staff|dev|developer|owner|official|support|player ?\d*|hurdle ?jump|rex|dash|bolt|you)$/i;

// Returns [cleanName, null] or [null, reason].
function checkName(raw) {
  const name = String(raw || "").trim().replace(/\s+/g, " ");
  if (name.length < 3 || name.length > 12) return [null, "Names are 3 to 12 characters long"];
  if (!/^[A-Za-z0-9]+( [A-Za-z0-9]+)*$/.test(name)) return [null, "Use only letters, numbers and spaces"];
  if (RESERVED.test(name)) return [null, "That name is reserved - try another"];
  if (isProfane(name) || isProfane(name.replace(/ /g, ""))) return [null, "That name isn't allowed"];
  return [name, null];
}

// ---------------------------------------------------------------- leaderboard storage

const RUNNERS = ["Tim", "Jim", "Jen", "Lyn"];
const TOP_N = 50;
const ADMIN_KEY = process.env.ADMIN_KEY || "";
const UPSTASH_URL = process.env.UPSTASH_REDIS_REST_URL;
const UPSTASH_TOKEN = process.env.UPSTASH_REDIS_REST_TOKEN;

// Public tag for an entry: the start of a hash of the private id (same formula in tools/relay_server.gd).
function refOf(id) {
  return crypto.createHash("sha256").update("hj:" + id).digest("hex").slice(0, 12);
}

async function redis(cmd) {
  const r = await fetch(UPSTASH_URL, {
    method: "POST",
    headers: { Authorization: "Bearer " + UPSTASH_TOKEN },
    body: JSON.stringify(cmd),
  });
  const j = await r.json();
  if (j.error) throw new Error(j.error);
  return j.result;
}

function parseMeta(json) {
  try { return JSON.parse(json || "{}") || {}; } catch { return {}; }
}

const board = UPSTASH_URL && UPSTASH_TOKEN
  ? {
      // hj:scores = sorted set of best runs (only ever raised: GT), hj:meta = id -> details (JSON),
      // hj:refs = ref -> id, hj:rep:<id> = set of players who reported that name (one report each),
      // hj:reported = reported ids by number of reports (the admin's list).
      async meta(id) { return parseMeta(await redis(["HGET", "hj:meta", id])); },
      async saveMeta(id, m) {
        await redis(["HSET", "hj:meta", id, JSON.stringify(m)]);
        await redis(["HSET", "hj:refs", refOf(id), id]);
      },
      async idOf(ref) { return await redis(["HGET", "hj:refs", ref]); },
      async submit(e) {
        await redis(["ZADD", "hj:scores", "GT", String(e.score), e.id]);
        const m = await this.meta(e.id);
        await this.saveMeta(e.id, { ...m, num: e.num, runner: e.runner, champ: e.champ, pic: e.pic, border: e.border, stats: e.stats });
        if (m.name) await redis(["HSETNX", "hj:names", nameKey(m.name), e.id]);   // names from before they were unique
      },
      // One player by public ref: {id, meta, score, rank} or null.
      async lookup(ref) {
        const id = await this.idOf(ref);
        if (!id) return null;
        const score = await redis(["ZSCORE", "hj:scores", id]);
        const rank = await redis(["ZREVRANK", "hj:scores", id]);
        return { id, meta: await this.meta(id), score: score === null ? 0 : Number(score), rank: rank === null ? 0 : Number(rank) + 1 };
      },
      // Names are unique (ignoring capitals): hj:names = name key -> id. False if someone else has it.
      async setName(id, name) {
        const key = nameKey(name);
        await redis(["HSETNX", "hj:names", key, id]);
        if ((await redis(["HGET", "hj:names", key])) !== id) return false;
        const m = await this.meta(id);
        if (m.name && nameKey(m.name) !== key) await this.releaseName(id, m.name);
        await this.saveMeta(id, { ...m, name });
        await this.clearReports(id);   // a new name starts with no reports
        return true;
      },
      async releaseName(id, name) {
        if ((await redis(["HGET", "hj:names", nameKey(name)])) === id) await redis(["HDEL", "hj:names", nameKey(name)]);
      },
      async report(reporter, ref) {
        const target = await this.idOf(ref);
        if (!target || target === reporter) return;
        await redis(["SADD", "hj:rep:" + target, reporter]);
        const n = Number(await redis(["SCARD", "hj:rep:" + target]));
        await redis(["ZADD", "hj:reported", String(n), target]);
      },
      async clearReports(id) {
        await redis(["DEL", "hj:rep:" + id]);
        await redis(["ZREM", "hj:reported", id]);
      },
      async dismiss(ref) {
        const id = await this.idOf(ref);
        if (!id) return false;
        await this.clearReports(id);
        return true;
      },
      async clearName(ref) {
        const id = await this.idOf(ref);
        if (!id) return false;
        const m = await this.meta(id);
        if (m.name) await this.releaseName(id, m.name);
        await this.saveMeta(id, { ...m, name: "" });
        await this.clearReports(id);
        return true;
      },
      // Delete my data: everything about this player.
      async forget(id) {
        const m = await this.meta(id);
        if (m.name) await this.releaseName(id, m.name);
        await redis(["ZREM", "hj:scores", id]);
        await redis(["HDEL", "hj:meta", id]);
        await redis(["HDEL", "hj:refs", refOf(id)]);
        await this.clearReports(id);
      },
      async remove(ref) {
        const id = await this.idOf(ref);
        if (!id) return false;
        const m = await this.meta(id);
        if (m.name) await this.releaseName(id, m.name);
        await redis(["ZREM", "hj:scores", id]);
        await redis(["HDEL", "hj:meta", id]);
        await this.clearReports(id);
        return true;
      },
      // The admin's list: reported entries, most reports first.
      async reported() {
        const flat = await redis(["ZREVRANGE", "hj:reported", "0", "49", "WITHSCORES"]);
        const out = [];
        for (let i = 0; i < flat.length; i += 2) {
          const id = flat[i];
          const score = await redis(["ZSCORE", "hj:scores", id]);
          out.push({ ...entryOut(0, id, score === null ? 0 : Number(score), await this.meta(id)), reports: Number(flat[i + 1]) });
        }
        return out;
      },
      async entry(id) { return entryOut(0, id, 0, await this.meta(id)); },
      async touch(id, num) {
        const m = await this.meta(id);
        if (m.num !== num) await this.saveMeta(id, { ...m, num });
      },
      async view(id) {
        const flat = await redis(["ZREVRANGE", "hj:scores", "0", String(TOP_N - 1), "WITHSCORES"]);
        const ids = [];
        const scores = [];
        for (let i = 0; i < flat.length; i += 2) { ids.push(flat[i]); scores.push(Number(flat[i + 1])); }
        const metas = ids.length ? await redis(["HMGET", "hj:meta", ...ids]) : [];
        const top = ids.map((pid, i) => entryOut(i + 1, pid, scores[i], parseMeta(metas[i])));
        let you = null;
        if (id) {
          const rank = await redis(["ZREVRANK", "hj:scores", id]);
          const score = await redis(["ZSCORE", "hj:scores", id]);
          const mine = entryOut(0, id, 0, await this.meta(id));
          you = { rank: rank === null ? 0 : Number(rank) + 1, score: score === null ? 0 : Number(score), ref: mine.ref, name: mine.name };
          if (rank === null && !mine.custom) you = null;
        }
        const total = Number(await redis(["ZCARD", "hj:scores"]));
        return { top, you, total };
      },
    }
  : (() => {
      console.log("Leaderboard: no UPSTASH_REDIS_REST_URL / _TOKEN set - keeping scores in memory (lost on restart).");
      const mem = new Map();     // id -> {score (-1 = no run yet), num, runner, champ, name}
      const reports = new Map(); // id -> Set(reporters)
      const idOf = (ref) => [...mem.keys()].find((id) => refOf(id) === ref);
      const names = new Map();   // name key -> id (names are unique, ignoring capitals)
      const release = (id) => { const n = (mem.get(id) || {}).name; if (n && names.get(nameKey(n)) === id) names.delete(nameKey(n)); };
      return {
        async submit(e) {
          const old = mem.get(e.id) || { score: -1 };
          mem.set(e.id, { ...old, score: Math.max(e.score, old.score), num: e.num, runner: e.runner, champ: e.champ, pic: e.pic, border: e.border, stats: e.stats });
        },
        async lookup(ref) {
          const id = idOf(ref);
          if (!id) return null;
          const m = mem.get(id);
          const all = [...mem.entries()].filter(([, x]) => x.score >= 0).sort((a, b) => b[1].score - a[1].score);
          return { id, meta: m, score: Math.max(0, m.score), rank: all.findIndex(([pid]) => pid === id) + 1 };
        },
        async setName(id, name) {
          const owner = names.get(nameKey(name));
          if (owner && owner !== id) return false;
          release(id);
          names.set(nameKey(name), id);
          mem.set(id, { score: -1, ...(mem.get(id) || {}), name });
          reports.delete(id);
          return true;
        },
        async report(reporter, ref) {
          const target = idOf(ref);
          if (!target || target === reporter) return;
          const set = reports.get(target) || new Set();
          set.add(reporter);
          reports.set(target, set);
        },
        async dismiss(ref) {
          const id = idOf(ref);
          if (!id) return false;
          reports.delete(id);
          return true;
        },
        async reported() {
          return [...reports.entries()].filter(([id, s]) => s.size > 0 && mem.has(id))
            .sort((a, b) => b[1].size - a[1].size)
            .map(([id, s]) => ({ ...entryOut(0, id, Math.max(0, mem.get(id).score), mem.get(id)), reports: s.size }));
        },
        async clearName(ref) {
          const id = idOf(ref);
          if (!id) return false;
          release(id);
          mem.get(id).name = "";
          reports.delete(id);
          return true;
        },
        async forget(id) {
          release(id);
          mem.delete(id);
          reports.delete(id);
        },
        async remove(ref) {
          const id = idOf(ref);
          if (!id) return false;
          release(id);
          mem.delete(id);
          reports.delete(id);
          return true;
        },
        async entry(id) { return entryOut(0, id, 0, mem.get(id) || {}); },
        async touch(id, num) {
          const m = mem.get(id);
          if (!m) mem.set(id, { score: -1, num });
          else m.num = num;
        },
        async view(id) {
          const all = [...mem.entries()].filter(([, m]) => m.score >= 0).sort((a, b) => b[1].score - a[1].score);
          const top = all.slice(0, TOP_N).map(([pid, m], i) => entryOut(i + 1, pid, m.score, m));
          let you = null;
          if (id && mem.has(id)) {
            const at = all.findIndex(([pid]) => pid === id);
            const mine = entryOut(0, id, 0, mem.get(id));
            you = { rank: at + 1, score: at >= 0 ? all[at][1].score : 0, ref: mine.ref, name: mine.name };
          }
          return { top, you, total: all.length };
        },
      };
    })();

function entryOut(rank, id, score, m) {
  const num = Number.isInteger(m.num) ? m.num : 0;
  const custom = typeof m.name === "string" && m.name !== "";
  return { rank, ref: refOf(id), name: custom ? m.name : "Player " + num, custom, score,
    runner: RUNNERS.includes(m.runner) ? m.runner : "", champ: m.champ === true,
    pic: Number.isInteger(m.pic) ? m.pic : 0, border: Number.isInteger(m.border) ? m.border : 0 };
}

// Profile stats a player shares (whole numbers only; anything else is dropped).
const STAT_KEYS = ["best", "total", "race_wins", "circuit_on", "circuit", "champs", "mp_wins", "mp_races", "crashes", "birds", "gophers"];
function cleanStats(s) {
  const out = {};
  if (!s || typeof s !== "object") return out;
  for (const k of STAT_KEYS) {
    const v = Number(s[k]);
    if (Number.isInteger(v) && v >= 0 && v <= 10000000) out[k] = v;
  }
  return out;
}

function smallInt(v) {
  const n = Number(v);
  return Number.isInteger(n) && n >= 0 && n < 64 ? n : 0;
}

// Two names count as the same if they only differ in capitals or spacing ("Phil" = "phil").
function nameKey(name) {
  return String(name).toLowerCase().replace(/\s+/g, " ").trim();
}

function validId(id) {
  return /^[0-9a-f]{16,40}$/.test(String(id || ""));
}

function validEntry(b) {
  if (!b || typeof b !== "object" || !validId(b.id)) return null;
  const num = Number(b.num), score = Number(b.score);
  if (!Number.isInteger(num) || num < 1000 || num > 9999) return null;
  if (!Number.isInteger(score) || score < 0 || score > 5000) return null;
  const runner = RUNNERS.includes(b.runner) ? b.runner : "";
  return { id: String(b.id), num, score, runner, champ: b.champ === true, pic: smallInt(b.pic), border: smallInt(b.border), stats: cleanStats(b.stats) };
}

// Each address may send a handful of requests a minute (a run takes far longer than that).
const posts = new Map(); // ip -> [timestamps]
function rateLimited(ip) {
  const now = Date.now();
  const list = (posts.get(ip) || []).filter((t) => now - t < 60000);
  list.push(now);
  posts.set(ip, list);
  return list.length > 12;
}
setInterval(() => posts.clear(), 10 * 60000);

// ---------------------------------------------------------------- daily challenge
//
// One course a day for everyone: the day is the date in US Eastern time (it changes at midnight in
// New York, daylight saving included) and the course comes from a seed made from that date. Each
// player gets one run (their first score counts). When a day ends, its top 3 get a crown (1st),
// silver (2nd) or bronze (3rd) badge, counted per player; 1st place also unlocks the Champion Band
// wristband in the game. Ties: whoever ran first.

const TZ = "America/New_York";
const DAY_SCALE = 100000;   // stored value = score * DAY_SCALE + a tie-break (earlier = higher)

function easternParts(date = new Date()) {
  const f = new Intl.DateTimeFormat("en-CA", { timeZone: TZ, year: "numeric", month: "2-digit", day: "2-digit",
    hour: "2-digit", minute: "2-digit", second: "2-digit", hour12: false });
  return Object.fromEntries(f.formatToParts(date).map((p) => [p.type, p.value]));
}
// Testing only: DAILY_TEST_DAY_FILE (never set on Render) names a file holding "today", so a test can
// move to the next day without waiting for midnight.
const TEST_DAY_FILE = process.env.DAILY_TEST_DAY_FILE || "";
function easternDay(date) {
  if (!date && TEST_DAY_FILE) return require("fs").readFileSync(TEST_DAY_FILE, "utf8").trim();
  const p = easternParts(date || new Date());
  return `${p.year}-${p.month}-${p.day}`;
}
function secondsIntoDay() {
  const p = easternParts();
  return (Number(p.hour) % 24) * 3600 + Number(p.minute) * 60 + Number(p.second);
}
// Seconds until the Eastern date changes (exact, even on daylight-saving days).
function secondsToNextDay() {
  const now = Date.now(), today = easternDay();
  let lo = 0, hi = 26 * 3600;
  while (hi - lo > 1) {
    const mid = Math.floor((lo + hi) / 2);
    if (easternDay(new Date(now + mid * 1000)) === today) lo = mid; else hi = mid;
  }
  return hi;
}
function prevDay(day) {
  const [y, m, d] = day.split("-").map(Number);
  return new Date(Date.UTC(y, m - 1, d) - 86400000).toISOString().slice(0, 10);
}
function daySeed(day) {
  return parseInt(crypto.createHash("sha256").update("hj-daily:" + day).digest("hex").slice(0, 8), 16);
}
function parseObj(json) {
  try { return JSON.parse(json || "{}") || {}; } catch { return {}; }
}

// Tiny storage layer for the daily data: Upstash Redis, or memory (same fallback as the leaderboard).
const kv = UPSTASH_URL && UPSTASH_TOKEN
  ? {
      zaddNX: async (k, s, m) => Number(await redis(["ZADD", k, "NX", String(s), m])),
      top: async (k, n) => {
        const f = await redis(["ZREVRANGE", k, "0", String(n - 1), "WITHSCORES"]);
        const out = [];
        for (let i = 0; i < f.length; i += 2) out.push([f[i], Number(f[i + 1])]);
        return out;
      },
      rank: (k, m) => redis(["ZREVRANK", k, m]),
      score: async (k, m) => { const s = await redis(["ZSCORE", k, m]); return s === null ? null : Number(s); },
      card: async (k) => Number(await redis(["ZCARD", k])),
      hget: (k, f) => redis(["HGET", k, f]),
      hset: (k, f, v) => redis(["HSET", k, f, v]),
      get: (k) => redis(["GET", k]),
      set: (k, v) => redis(["SET", k, v]),
      setnx: async (k, v) => (await redis(["SET", k, v, "NX"])) === "OK",
      expire: (k, s) => redis(["EXPIRE", k, String(s)]),
      zrem: (k, m) => redis(["ZREM", k, m]),
      hdel: (k, f) => redis(["HDEL", k, f]),
    }
  : (() => {
      const z = new Map(), h = new Map(), s = new Map();
      const zset = (k) => { if (!z.has(k)) z.set(k, new Map()); return z.get(k); };
      const sorted = (k) => [...zset(k).entries()].sort((a, b) => b[1] - a[1]);
      return {
        zaddNX: async (k, sc, m) => { const zz = zset(k); if (zz.has(m)) return 0; zz.set(m, sc); return 1; },
        top: async (k, n) => sorted(k).slice(0, n),
        rank: async (k, m) => { const i = sorted(k).findIndex(([id]) => id === m); return i < 0 ? null : i; },
        score: async (k, m) => (zset(k).has(m) ? zset(k).get(m) : null),
        card: async (k) => zset(k).size,
        hget: async (k, f) => (h.get(k) || new Map()).get(f) ?? null,
        hset: async (k, f, v) => { if (!h.has(k)) h.set(k, new Map()); h.get(k).set(f, v); },
        get: async (k) => s.get(k) ?? null,
        set: async (k, v) => { s.set(k, v); },
        setnx: async (k, v) => { if (s.has(k)) return false; s.set(k, v); return true; },
        expire: async () => {},
        zrem: async (k, m) => { zset(k).delete(m); },
        hdel: async (k, f) => { (h.get(k) || new Map()).delete(f); },
      };
    })();

// The first request of a new day closes the previous one: badges for its top 3, and its results
// kept as "yesterday's best".
async function finalizeDays(today) {
  const cur = await kv.get("hj:daily:current");
  if (cur === today) return;
  if (cur && cur < today && await kv.setnx("hj:daily:final:" + cur, "1")) {
    await kv.expire("hj:daily:final:" + cur, 7 * 86400);
    const top = await kv.top("hj:day:" + cur, 3);
    for (let i = 0; i < top.length; i++) {
      const b = parseObj(await kv.hget("hj:badges", top[i][0]));
      const k = ["gold", "silver", "bronze"][i];
      b[k] = (b[k] || 0) + 1;
      await kv.hset("hj:badges", top[i][0], JSON.stringify(b));
    }
    await kv.set("hj:daily:last", JSON.stringify({ day: cur, top: top.map(([id, v]) => ({ id, score: Math.floor(v / DAY_SCALE) })) }));
  }
  if (!cur || cur < today) await kv.set("hj:daily:current", today);
}

async function placeList(rows) {
  const out = [];
  for (let i = 0; i < rows.length; i++) {
    const e = await board.entry(rows[i].id);
    const b = parseObj(await kv.hget("hj:badges", rows[i].id));
    out.push({ rank: i + 1, name: e.name, ref: e.ref, pic: e.pic, border: e.border, score: rows[i].score, times: b[["gold", "silver", "bronze"][i]] || 0 });
  }
  return out;
}

// Delete my data: the player's daily runs (today and the last few days), medals and their place in
// "yesterday's best".
async function forgetDaily(id) {
  const today = easternDay();
  let day = today;
  for (let i = 0; i < 5; i++) {
    await kv.zrem("hj:day:" + day, id);
    day = prevDay(day);
  }
  await kv.hdel("hj:badges", id);
  const last = parseObj(await kv.get("hj:daily:last"));
  if (Array.isArray(last.top) && last.top.some((e) => e.id === id)) {
    last.top = last.top.filter((e) => e.id !== id);
    await kv.set("hj:daily:last", JSON.stringify(last));
  }
}

async function dailyView(id) {
  const today = easternDay();
  await finalizeDays(today);
  const key = "hj:day:" + today;
  const today3 = await placeList((await kv.top(key, 3)).map(([pid, v]) => ({ id: pid, score: Math.floor(v / DAY_SCALE) })));
  const last = parseObj(await kv.get("hj:daily:last"));
  const yesterday = last.day ? { day: last.day, is_yesterday: last.day === prevDay(today), top: await placeList(last.top || []) } : null;
  let you = { played: false, score: 0, rank: 0 };
  let badges = { gold: 0, silver: 0, bronze: 0 };
  if (id) {
    const v = await kv.score(key, id);
    if (v !== null) you = { played: true, score: Math.floor(v / DAY_SCALE), rank: Number(await kv.rank(key, id)) + 1 };
    badges = { ...badges, ...parseObj(await kv.hget("hj:badges", id)) };
  }
  return { day: today, seed: daySeed(today), ends_in: secondsToNextDay(), today: today3, yesterday, you, badges, total: await kv.card(key) };
}

async function dailySubmit(b) {
  if (!b || !validId(b.id)) return { error: "bad request" };
  const num = Number(b.num), score = Number(b.score), secs = Number(b.secs);
  if (!Number.isInteger(num) || num < 1000 || num > 9999) return { error: "bad request" };
  if (!Number.isInteger(score) || score < 0 || score > 5000 || !(secs >= 0 && secs <= 7200)) return { error: "bad request" };
  if (score > secs / 0.6 + 3) return { error: "That score doesn't add up" };   // faster than any run can clear hurdles
  const today = easternDay();
  let day = String(b.day || "");
  // A run that started before midnight and ended just after still counts for the day it started.
  const late = day === prevDay(today) && secondsIntoDay() < 600 && !(await kv.get("hj:daily:final:" + day));
  if (day !== today && !late) return { error: "That daily challenge has ended", ...(await dailyView(String(b.id))) };
  await board.touch(String(b.id), num);
  const tiebreak = DAY_SCALE - 1 - Math.min(DAY_SCALE - 1, late ? 86399 : secondsIntoDay());
  const added = await kv.zaddNX("hj:day:" + day, score * DAY_SCALE + tiebreak, String(b.id));
  await kv.expire("hj:day:" + day, 4 * 86400);
  const view = await dailyView(String(b.id));
  return added ? { ...view, accepted: true } : { ...view, accepted: false, error: "You've already run today's challenge" };
}

// ---------------------------------------------------------------- admin page
function esc(s) {
  return String(s).replace(/[&<>"']/g, (c) => ({ "&": "&amp;", "<": "&lt;", ">": "&gt;", '"': "&quot;", "'": "&#39;" }[c]));
}

function adminPage(key, reported, top, msg) {
  const link = (action, ref, label, confirmText) =>
    `<a class="b ${action}" href="/admin?key=${encodeURIComponent(key)}&action=${action}&ref=${ref}"` +
    (confirmText ? ` onclick="return confirm('${confirmText}')"` : "") + `>${label}</a>`;
  const row = (e, withReports) => `<tr><td>${esc(e.name)}${e.custom ? "" : " <i>(no custom name)</i>"}</td>` +
    (withReports ? `<td>${e.reports}</td>` : `<td>#${e.rank}</td>`) + `<td>${e.score}</td><td class="acts">` +
    (e.custom ? link("clear", e.ref, "Clear name") : "") +
    link("remove", e.ref, "Remove entry", "Delete this entry and its score?") +
    (withReports ? link("dismiss", e.ref, "Dismiss reports") : "") + `</td></tr>`;
  const notes = { clear: "Name cleared.", remove: "Entry removed.", dismiss: "Reports dismissed.", "not-found": "That entry no longer exists." };
  return `<!doctype html><html><head><meta charset="utf-8"><meta name="viewport" content="width=device-width,initial-scale=1">
<title>Hurdle Jump admin</title><style>
body{font-family:system-ui,sans-serif;margin:16px;background:#1e2a44;color:#fff}h1{color:#ffd23a;font-size:22px}
h2{font-size:17px;margin-top:22px;color:#bfe3ff}table{border-collapse:collapse;width:100%}td,th{padding:8px 6px;border-bottom:1px solid #34405e;text-align:left;font-size:15px}
.acts{white-space:nowrap}.b{display:inline-block;margin:2px;padding:7px 10px;border-radius:8px;color:#fff;text-decoration:none;font-size:13px}
.clear{background:#3a86f0}.remove{background:#e8403a}.dismiss{background:#5a6070}.msg{background:#4cc94c;padding:8px 12px;border-radius:8px;display:inline-block}
i{color:#9aa4b8}</style></head><body><h1>Hurdle Jump leaderboard admin</h1>
${msg ? `<p class="msg">${esc(notes[msg] || msg)}</p>` : ""}
<h2>Reported names (${reported.length})</h2>
${reported.length ? `<table><tr><th>Name</th><th>Reports</th><th>Best</th><th></th></tr>${reported.map((e) => row(e, true)).join("")}</table>` : "<p>Nothing reported.</p>"}
<h2>Top ${top.length}</h2>
${top.length ? `<table><tr><th>Name</th><th>Rank</th><th>Best</th><th></th></tr>${top.map((e) => row(e, false)).join("")}</table>` : "<p>No scores yet.</p>"}
<p><i>Clear name = back to "Player ####". Remove entry = deletes the score (e.g. a faked one). Dismiss reports = the name is fine.</i></p>
</body></html>`;
}

// ---------------------------------------------------------------- web requests

const CORS = {
  "Access-Control-Allow-Origin": "*",
  "Access-Control-Allow-Methods": "GET, POST, OPTIONS",
  "Access-Control-Allow-Headers": "Content-Type",
};

function reply(res, code, obj) {
  res.writeHead(code, { "Content-Type": "application/json", ...CORS });
  res.end(JSON.stringify(obj));
}

async function readBody(req) {
  let body = "";
  for await (const chunk of req) {
    body += chunk;
    if (body.length > 2048) return null;
  }
  try { return JSON.parse(body); } catch { return null; }
}

const server = http.createServer(async (req, res) => {
  const url = new URL(req.url, "http://relay");
  if (req.method === "OPTIONS") {
    res.writeHead(204, CORS);
    return res.end();
  }
  try {
    if (url.pathname === "/daily" && req.method === "GET") {
      return reply(res, 200, await dailyView(url.searchParams.get("id") || ""));
    }
    if (url.pathname === "/daily" && req.method === "POST") {
      const ip = String(req.headers["x-forwarded-for"] || req.socket.remoteAddress || "").split(",").pop().trim();
      if (rateLimited(ip)) return reply(res, 429, { error: "Too many tries - wait a minute" });
      return reply(res, 200, await dailySubmit(await readBody(req)));
    }
    if (url.pathname === "/leaderboard/profile" && req.method === "GET") {
      const ref = String(url.searchParams.get("ref") || "");
      const p = /^[0-9a-f]{12}$/.test(ref) ? await board.lookup(ref) : null;
      if (!p) return reply(res, 200, { error: "That player isn't on the board any more" });
      const badges = { gold: 0, silver: 0, bronze: 0, ...parseObj(await kv.hget("hj:badges", p.id)) };
      return reply(res, 200, { ...entryOut(p.rank, p.id, p.score, p.meta), stats: cleanStats(p.meta.stats), badges });
    }
    if (url.pathname === "/leaderboard" && req.method === "GET") {
      return reply(res, 200, await board.view(url.searchParams.get("id") || ""));
    }
    if (url.pathname.startsWith("/leaderboard") && req.method === "POST") {
      // The address the host's proxy saw (it adds it LAST - earlier entries can be faked by the sender).
      const ip = String(req.headers["x-forwarded-for"] || req.socket.remoteAddress || "").split(",").pop().trim();
      if (rateLimited(ip)) return reply(res, 429, { error: "Too many tries - wait a minute" });
      const b = await readBody(req);
      if (url.pathname === "/leaderboard") {
        const e = validEntry(b);
        if (!e) return reply(res, 400, { error: "bad entry" });
        await board.submit(e);
        return reply(res, 200, await board.view(e.id));
      }
      if (url.pathname === "/leaderboard/name") {
        if (!b || !validId(b.id)) return reply(res, 400, { error: "bad request" });
        const [name, why] = checkName(b.name);
        if (!name) return reply(res, 200, { error: why });
        if (!(await board.setName(String(b.id), name))) {
          return reply(res, 200, { error: name.length < 12 ? "Someone already has that name - try " + name + "1" : "Someone already has that name" });
        }
        return reply(res, 200, await board.view(String(b.id)));
      }
      if (url.pathname === "/leaderboard/delete") {
        if (!b || !validId(b.id)) return reply(res, 400, { error: "bad request" });
        await board.forget(String(b.id));
        await forgetDaily(String(b.id));
        return reply(res, 200, { ok: true });
      }
      if (url.pathname === "/leaderboard/report") {
        if (!b || !validId(b.id) || !/^[0-9a-f]{12}$/.test(String(b.ref || ""))) return reply(res, 400, { error: "bad request" });
        await board.report(String(b.id), String(b.ref));
        return reply(res, 200, { ok: true });
      }
    }
    if (url.pathname === "/admin") {
      // You only (ADMIN_KEY on Render): a page with reported names and the top 50, each with buttons
      // to clear the name (back to "Player ####"), remove the entry, or dismiss its reports.
      // Off unless ADMIN_KEY is set.
      const key = url.searchParams.get("key") || "";
      if (!ADMIN_KEY || key !== ADMIN_KEY) return reply(res, 403, { error: "not allowed" });
      const action = url.searchParams.get("action");
      if (action) {
        const ref = String(url.searchParams.get("ref") || "");
        const done = action === "clear" ? await board.clearName(ref)
          : action === "remove" ? await board.remove(ref)
          : action === "dismiss" ? await board.dismiss(ref) : false;
        res.writeHead(303, { Location: "/admin?key=" + encodeURIComponent(key) + "&msg=" + (done ? action : "not-found") });
        return res.end();
      }
      res.writeHead(200, { "Content-Type": "text/html; charset=utf-8" });
      return res.end(adminPage(key, await board.reported(), (await board.view("")).top, url.searchParams.get("msg") || ""));
    }  } catch (err) {
    console.error("leaderboard:", err.message);
    return reply(res, 500, { error: "The leaderboard isn't available right now" });
  }  res.writeHead(200, { "Content-Type": "text/plain", ...CORS });
  res.end("Hurdle Jump relay is running. Rooms open: " + rooms.size + "\n");
});

// ---------------------------------------------------------------- multiplayer rooms

const wss = new WebSocketServer({ server });

function send(ws, obj) {
  if (ws.readyState === 1) ws.send(JSON.stringify(obj));
}

function roomName(raw) {
  return String(raw || "").trim().toUpperCase().slice(0, 20);
}

function leave(ws) {
  const room = ws.room ? rooms.get(ws.room) : null;
  if (!room) return;
  room.players.delete(ws.id);
  if (room.players.size === 0) {
    rooms.delete(ws.room);
  } else if (ws.id === room.host && !room.public) {
    // Private race: the host left, so the race ends for everyone.
    for (const p of room.players.values()) {
      send(p.ws, { op: "closed" });
      p.ws.room = null;
    }
    rooms.delete(ws.room);
  } else {
    for (const p of room.players.values()) send(p.ws, { op: "peer_left", id: ws.id });
    if (ws.id === room.host) {
      // Public race: the longest-waiting player takes over as host.
      room.host = Math.min(...room.players.keys());
      room.locked = false;
      for (const p of room.players.values()) send(p.ws, { op: "host", id: room.host });
    }
  }
  ws.room = null;
}

function enter(ws, name, room, info) {
  let id = 1;
  while (room.players.has(id)) id++;
  ws.id = id;
  ws.room = name;
  for (const p of room.players.values()) send(p.ws, { op: "peer_joined", id, info });
  room.players.set(id, { ws, info });
  const players = [...room.players.entries()].map(([pid, p]) => ({ id: pid, info: p.info }));
  send(ws, { op: "joined", id, host: room.host, room: name, public: room.public, players });
}

function version(m) {
  return Number.isInteger(m.v) ? m.v : 1;
}

function newRoom(v, isPublic) {
  return { host: 1, locked: false, public: isPublic, v, players: new Map() };
}

wss.on("connection", (ws) => {
  ws.isAlive = true;
  ws.on("pong", () => (ws.isAlive = true));
  ws.on("message", (raw) => {
    let m;
    try { m = JSON.parse(raw); } catch { return; }
    const room = ws.room ? rooms.get(ws.room) : null;
    switch (m.op) {
      case "create": {
        leave(ws);
        const name = roomName(m.room);
        if (!name) return send(ws, { op: "error", msg: "Enter a race name" });
        if (rooms.has(name)) return send(ws, { op: "error", msg: "That race name is taken" });
        const r = newRoom(version(m), false);
        rooms.set(name, r);
        enter(ws, name, r, m.info || {});
        break;
      }
      case "join": {
        leave(ws);
        const name = roomName(m.room);
        const r = rooms.get(name);
        if (!r || r.public) return send(ws, { op: "error", msg: "No race called " + name });
        if (r.v !== version(m)) return send(ws, { op: "error", msg: "That race is on a different version of the game - both players need the latest version" });
        if (r.locked) return send(ws, { op: "error", msg: "That race has already started" });
        if (r.players.size >= MAX_PLAYERS) return send(ws, { op: "error", msg: "That race is full" });
        enter(ws, name, r, m.info || {});
        break;
      }
      case "quick": {
        // Public race: the open lobby with the most players waiting (fills races up fastest),
        // or a brand new one with you as host.
        leave(ws);
        const v = version(m);
        let best = null;
        for (const [name, r] of rooms) {
          if (r.public && !r.locked && r.v === v && r.players.size < MAX_PLAYERS &&
              (!best || r.players.size > best[1].players.size)) best = [name, r];
        }
        if (best) return enter(ws, best[0], best[1], m.info || {});
        let name;
        do { name = "PUBLIC-" + Math.random().toString(36).slice(2, 6).toUpperCase(); } while (rooms.has(name));
        const r = newRoom(v, true);
        rooms.set(name, r);
        enter(ws, name, r, m.info || {});
        break;
      }
      case "send":
        if (!room) return;
        {
          const out = JSON.stringify({ op: "msg", from: ws.id, data: m.data });   // once, not per player
          for (const [pid, p] of room.players) if (pid !== ws.id && p.ws.readyState === 1) p.ws.send(out);
        }
        break;
      case "lock":
      case "unlock":
        if (room && ws.id === room.host) room.locked = m.op === "lock";
        break;
      case "leave":
        leave(ws);
        break;
      case "kick": {
        // Host only: remove another player even if their game has frozen, freeing the spot.
        if (!room || ws.id !== room.host || m.id === room.host) return;
        const target = room.players.get(Number(m.id));
        if (!target) return;
        send(target.ws, { op: "kicked" });
        leave(target.ws);
        break;
      }
    }
  });
  ws.on("close", () => leave(ws));
});

// Keep connections alive through proxies and drop dead ones.
setInterval(() => {
  for (const ws of wss.clients) {
    if (!ws.isAlive) { ws.terminate(); continue; }
    ws.isAlive = false;
    ws.ping();
  }
}, 25000);

const port = process.env.PORT || 8080;
server.listen(port, () => console.log("Hurdle Jump relay listening on port " + port));
