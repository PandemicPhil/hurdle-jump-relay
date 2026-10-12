// Hurdle Jump multiplayer relay ("matchmaker").
//
// Players connect over WebSocket. A host CREATES a race with a name; up to 3 more players JOIN it
// with the same name. After that the server just forwards each player's small messages to the
// others in the same race. It never runs the game itself.
//
// Protocol (JSON text frames):
//   client -> server: {op:"create", room, info} | {op:"join", room, info} | {op:"send", data}
//                     {op:"lock"} (host: no more joins) | {op:"unlock"} | {op:"leave"}
//                     {op:"kick", id} (host: remove a player, e.g. one who stopped responding)
//   server -> client: {op:"joined", id, host, players:[{id, info}]} | {op:"peer_joined", id, info}
//                     {op:"peer_left", id} | {op:"msg", from, data} | {op:"closed"} | {op:"error", msg}
//                     {op:"kicked"} (you were removed by the host)
//
// Deploy: any Node 18+ host. Start command: `node server.js` (listens on $PORT, default 8080).
const http = require("http");
const { WebSocketServer } = require("ws");

const MAX_PLAYERS = 4;
const rooms = new Map(); // NAME -> {host, locked, players: Map(id -> {ws, info})}

const server = http.createServer((req, res) => {
  res.writeHead(200, { "Content-Type": "text/plain" });
  res.end("Hurdle Jump relay is running. Rooms open: " + rooms.size + "\n");
});
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
  if (ws.id === room.host) {
    // Host left: the race ends for everyone.
    for (const p of room.players.values()) {
      send(p.ws, { op: "closed" });
      p.ws.room = null;
    }
    rooms.delete(ws.room);
  } else {
    for (const p of room.players.values()) send(p.ws, { op: "peer_left", id: ws.id });
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
  send(ws, { op: "joined", id, host: room.host, room: name, players });
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
        const r = { host: 1, locked: false, players: new Map() };
        rooms.set(name, r);
        enter(ws, name, r, m.info || {});
        break;
      }
      case "join": {
        leave(ws);
        const name = roomName(m.room);
        const r = rooms.get(name);
        if (!r) return send(ws, { op: "error", msg: "No race called " + name });
        if (r.locked) return send(ws, { op: "error", msg: "That race has already started" });
        if (r.players.size >= MAX_PLAYERS) return send(ws, { op: "error", msg: "That race is full" });
        enter(ws, name, r, m.info || {});
        break;
      }
      case "send":
        if (!room) return;
        for (const [pid, p] of room.players) if (pid !== ws.id) send(p.ws, { op: "msg", from: ws.id, data: m.data });
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
