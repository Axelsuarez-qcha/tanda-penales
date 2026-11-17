'use strict';
/* Servidor de partidas de "Tanda de penales". El servidor es el árbitro: guarda la subasta (pistas ocultas y reloj),
   recibe las elecciones de pateador y arquero y recién las muestra cuando llegaron las dos. */
const http = require('http'), fs = require('fs'), path = require('path');
const { WebSocketServer } = require('ws');
const E = require('./engine.js');
const PLAYERS = require('./players.json');
E.calibrate(PLAYERS);
const BY = {}; PLAYERS.forEach(p => BY[p.id] = p);

const PORT = process.env.PORT || 3000;
const INDEX = fs.readFileSync(path.join(__dirname, 'public', 'index.html'));
const SOLD_MS = 6000, SHOT_MS = 15000, SHOW_MS = 5500, ORDER_MS = 15000, OVER_MS = 30000, IDLE_MS = 20 * 60 * 1000;

const server = http.createServer((req, res) => {
  if (req.url.startsWith('/health')) { res.writeHead(200, { 'Content-Type': 'text/plain' }); return res.end('ok'); }
  res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8', 'Cache-Control': 'no-cache' }); res.end(INDEX);
});
const wss = new WebSocketServer({ server, maxPayload: 16 * 1024 });
const rooms = new Map();
const rnd32 = () => (Math.random() * 4294967296) >>> 0;
const send = (ws, m) => { if (ws && ws.readyState === 1) ws.send(JSON.stringify(m)); };
function newCode() {
  const L = 'ABCDEFGHJKLMNPQRSTUVWXYZ'; let c;
  do { c = ''; for (let i = 0; i < 5; i++) c += L[Math.floor(Math.random() * L.length)]; } while (rooms.has(c));
  return c;
}
const cleanName = s => String(s || 'Jugador').replace(/[<>&"]/g, '').trim().slice(0, 16) || 'Jugador';
const names = r => [r.p[0] ? r.p[0].name : '', r.p[1] ? r.p[1].name : ''];
const online = r => [!!(r.p[0] && r.p[0].ws), !!(r.p[1] && r.p[1].ws)];
const mir = (seat, x) => x === null ? null : (x === seat ? 0 : 1);

/* ---------- vistas por fase (se reenvían completas al reconectar) ---------- */
function view(r, seat) {
  const now = Date.now(), base = { seat, names: names(r), now, code: r.code };
  if (r.phase === 'lobby') return Object.assign({ t: 'lobby', opts: r.opts, online: online(r) }, base);
  if (r.phase === 'toss') return Object.assign({ t: 'toss', winner: r.toss.winner, face: r.toss.face }, base);
  if (r.phase === 'au') return Object.assign(auView(r, seat, now), base);
  if (r.phase === 'order') {
    const A = r.au.A;
    return Object.assign({ t: 'order', teams: [A.teams[seat], A.teams[1 - seat]], first: A.S === seat, deadline: r.ord.deadline, locked: !!r.ord.orders[seat] }, base);
  }
  if (r.phase === 'match' || r.phase === 'end') {
    const m = r.m, A = r.au.A;
    return Object.assign({ t: 'match', mode: r.opts.mode, seed: m.seed, nseed: m.nseed, teams: [A.teams[seat], A.teams[1 - seat]],
      orders: [m.orders[seat], m.orders[1 - seat]], first: A.S === seat ? 0 : 1, history: m.history, deadline: m.deadline,
      sent: !!(m.choice[seat]), shown: m.stage === 'show', final: r.phase === 'end' || (m.stage === 'show' && m.sh.winner !== null) }, base);
  }
}
function auView(r, seat, now) {
  const a = r.au, A = a.A, c = A.cur, v = {
    t: 'au', phase: a.phase, lot: A.lot, total: A.lots.length, lotSec: A.lotSec, until: a.until || 0,
    budget: [A.budget[seat], A.budget[1 - seat]], teams: [A.teams[seat], A.teams[1 - seat]],
    kickFirst: A.S === seat,
    sold: A.log.map(e => ({ team: mir(seat, e.team), id: e.id, price: e.price, fair: e.fair, nobids: !!e.nobids, auto: !!e.auto, gk: !!e.gk, left: !!e.left })),
    cur: null, over: null, ready: [a.ready[seat], a.ready[1 - seat]]
  };
  if (a.phase === 'lot' && c) {
    v.cur = { start: c.start, end: c.end, bid: c.bid, leader: mir(seat, c.leader), done: [c.done[seat], c.done[1 - seat]], ext: c.ext,
      pair: c.pair || null, clues: c.pair ? [] : E.auClues(A, c.id, (now - c.start) / 1000) };
  }
  if (a.phase === 'pick' && c && c.pick) v.cur = { pair: c.pair, pick: { team: mir(seat, c.pick.team), price: c.pick.price, nobids: !!c.pick.nobids, until: c.pick.until } };
  if (a.phase === 'over') v.over = { theme: { id: A.theme.id, name: A.theme.name }, wildGK: A.wildGK };
  return v;
}
function push(r) { for (const s of [0, 1]) if (r.p[s]) send(r.p[s].ws, view(r, s)); }
function presence(r) { for (const s of [0, 1]) if (r.p[s]) send(r.p[s].ws, { t: 'presence', online: online(r), names: names(r) }); }

/* ---------- transiciones ---------- */
function startAuction(r, kicker, now) {
  const A = E.auNew(PLAYERS, E.mulberry32(rnd32()), { lotSec: r.opts.lotSec });
  E.auStart(A, kicker); E.auNext(A, now);
  r.au = { A, phase: A.over ? 'over' : 'lot', until: 0, ready: [false, false], overAt: now, sig: '' };
  r.phase = 'au'; push(r);
}
function startOrder(r, now) {
  r.phase = 'order'; r.ord = { deadline: now + ORDER_MS + 2500, orders: [null, null] }; push(r);
}
function startMatch(r, now) {
  const A = r.au.A, orders = [0, 1].map(s => {
    const field = A.teams[s].map(id => BY[id]).filter(p => !p.gk);
    return r.ord.orders[s] || E.aiOrder(field).map(p => p.id);
  });
  const teams = [0, 1].map(s => ({ name: 'S' + s, gk: BY[A.teams[s].find(id => BY[id].gk)], order: orders[s].map(id => BY[id]) }));
  const seed = rnd32(), nseed = rnd32();
  const sh = new E.Shootout(teams, A.S, E.mulberry32(seed), { mode: r.opts.mode });
  r.m = { sh, seed, nseed, orders, history: [], stage: 'wait', pk: sh.peek(), choice: [null, null], deadline: now + SHOT_MS + 800, until: 0 };
  r.phase = 'match'; push(r);
}
function autoKick(r) {
  const g = r.rng;
  if (r.opts.mode === 'zonas') { const z = E.ZONES[Math.floor(g() * 9)]; return { x: z.x, y: z.y, type: 'normal' }; }
  return { x: (g() < .5 ? -1 : 1) * (.8 + g() * 1.8), y: .5 + g() * 1.3, type: 'normal' };
}
function resolveKick(r, now) {
  const m = r.m, pk = m.pk, kSeat = pk.team, gSeat = 1 - pk.team;
  const kick = m.choice[kSeat] || autoKick(r), dive = m.choice[gSeat] != null ? m.choice[gSeat].dive : Math.floor(r.rng() * 9);
  m.sh.play(pk, kick, dive); m.history.push({ kick, dive });
  m.stage = 'show'; m.until = now + SHOW_MS; m.choice = [null, null];
  for (const s of [0, 1]) send(r.p[s] && r.p[s].ws, { t: 'reveal', kick, dive, n: m.history.length });
}
function nextKick(r, now) {
  const m = r.m;
  if (m.sh.winner !== null) { r.phase = 'end'; r.rematch = [false, false]; for (const s of [0, 1]) send(r.p[s] && r.p[s].ws, { t: 'turn', n: m.history.length, final: true }); return; }
  m.pk = m.sh.peek(); m.stage = 'wait'; m.deadline = now + SHOT_MS + 800;
  for (const s of [0, 1]) send(r.p[s] && r.p[s].ws, { t: 'turn', n: m.history.length, deadline: m.deadline, now });
}
function tickRoom(r, now) {
  if (r.phase === 'au') {
    const a = r.au, A = a.A;
    if (a.phase === 'lot') {
      const ev = E.auTick(A, now);
      if (ev.length) { if (ev[0].type === 'gkwin') { a.phase = 'pick'; a.until = A.cur.pick.until; return push(r); } a.phase = 'sold'; a.until = now + SOLD_MS; return push(r); }
      if (A.cur.pair) return;
      const shown = E.auClues(A, A.cur.id, (now - A.cur.start) / 1000).filter(x => x.shown).length;
      if (shown !== a.sig) { a.sig = shown; push(r); }
    } else if (a.phase === 'pick') {
      if (E.auTick(A, now).length) { a.phase = 'sold'; a.until = now + SOLD_MS; push(r); }
    } else if (a.phase === 'sold' && now >= a.until) {
      E.auNext(A, now);
      if (A.over) { a.phase = 'over'; a.overAt = now; a.ready = [false, false]; } else { a.phase = 'lot'; a.sig = ''; }
      push(r);
    } else if (a.phase === 'over' && ((a.ready[0] && a.ready[1]) || now > a.overAt + OVER_MS)) startOrder(r, now);
  } else if (r.phase === 'order') {
    if ((r.ord.orders[0] && r.ord.orders[1]) || now > r.ord.deadline) startMatch(r, now);
  } else if (r.phase === 'match') {
    const m = r.m;
    if (m.stage === 'wait') {
      const k = m.choice[m.pk.team], g = m.choice[1 - m.pk.team];
      if ((k && g) || now > m.deadline) resolveKick(r, now);
    } else if (m.stage === 'show' && now >= m.until) nextKick(r, now);
  }
}
setInterval(() => {
  const now = Date.now();
  for (const [code, r] of rooms) {
    try { tickRoom(r, now); } catch (e) { console.error('tick', code, e); }
    if (!online(r)[0] && !online(r)[1] && now - r.last > IDLE_MS) rooms.delete(code);
  }
}, 200);
setInterval(() => { wss.clients.forEach(ws => { if (ws.alive === false) return ws.terminate(); ws.alive = false; ws.ping(); }); }, 25000);

/* ---------- mensajes ---------- */
function bind(ws, r, seat) { ws.ctx = { r, seat }; r.p[seat].ws = ws; r.last = Date.now(); send(ws, view(r, seat)); presence(r); }
wss.on('connection', ws => {
  ws.alive = true; ws.on('pong', () => { ws.alive = true; });
  ws.on('message', raw => {
    let m; try { m = JSON.parse(raw); } catch (e) { return; }
    try { handle(ws, m); } catch (e) { console.error('msg', e); send(ws, { t: 'err', text: 'Algo salió mal en el servidor.' }); }
  });
  ws.on('close', () => { const c = ws.ctx; if (c && c.r.p[c.seat] && c.r.p[c.seat].ws === ws) { c.r.p[c.seat].ws = null; c.r.last = Date.now(); presence(c.r); } });
});
function handle(ws, m) {
  const now = Date.now();
  if (m.t === 'create') {
    const code = newCode(), r = { code, p: [{ token: String(m.token || ''), name: cleanName(m.name), ws: null }, null], opts: { lotSec: 30, mode: 'libre' },
      phase: 'lobby', last: now, rng: E.mulberry32(rnd32()), rematch: [false, false] };
    rooms.set(code, r); return bind(ws, r, 0);
  }
  if (m.t === 'join') {
    const r = rooms.get(String(m.code || '').toUpperCase().trim()), tok = String(m.token || '');
    if (!r) return send(ws, { t: 'err', fatal: true, text: 'No existe esa sala. Revisá el código o pedile otro link a tu rival.' });
    for (const s of [0, 1]) if (r.p[s] && r.p[s].token === tok) { if (r.p[s].ws && r.p[s].ws !== ws) { r.p[s].ws.ctx = null; r.p[s].ws.close(); } return bind(ws, r, s); }
    if (!r.p[1] && r.phase === 'lobby') { r.p[1] = { token: tok, name: cleanName(m.name), ws: null }; bind(ws, r, 1); return push(r); }
    return send(ws, { t: 'err', fatal: true, text: 'La sala ya está llena o la partida ya empezó.' });
  }
  const c = ws.ctx; if (!c) return; const { r, seat } = c; r.last = now;
  switch (m.t) {
    case 'opts':
      if (seat !== 0 || r.phase !== 'lobby') return;
      if (m.mode === 'libre' || m.mode === 'zonas') r.opts.mode = m.mode;
      return push(r);
    case 'start':
      if (seat !== 0 || r.phase !== 'lobby' || !r.p[1]) return;
      r.toss = { winner: Math.random() < .5 ? 0 : 1, face: Math.random() < .5 ? 'CARA' : 'CRUZ' }; r.phase = 'toss'; return push(r);
    case 'toss':
      if (r.phase !== 'toss' || seat !== r.toss.winner) return;
      return startAuction(r, m.kickFirst ? seat : 1 - seat, now);
    case 'bid': {
      if (r.phase !== 'au' || r.au.phase !== 'lot') return;
      const res = E.auBid(r.au.A, seat, Number(m.amount), now);
      if (!res.ok) return send(ws, { t: 'info', text: 'Esa oferta ya no es válida.' });
      return push(r);
    }
    case 'drop': if (r.phase === 'au' && r.au.phase === 'lot') { E.auDrop(r.au.A, seat); } return;
    case 'pass': if (r.phase === 'au' && r.au.phase === 'lot') { E.auPass(r.au.A, seat); } return;
    case 'pick': if (r.phase === 'au' && r.au.phase === 'pick' && E.auPickGK(r.au.A, seat, Number(m.id)).length) { r.au.phase = 'sold'; r.au.until = now + SOLD_MS; push(r); } return;
    case 'ready': if (r.phase === 'au' && r.au.phase === 'over') { r.au.ready[seat] = true; push(r); } return;
    case 'order': {
      if (r.phase !== 'order' || r.ord.orders[seat]) return;
      const A = r.au.A, field = A.teams[seat].filter(id => !BY[id].gk), ids = Array.isArray(m.ids) ? m.ids.map(Number) : [];
      if (ids.length !== 5 || new Set(ids).size !== 5 || !ids.every(id => field.includes(id))) return;
      r.ord.orders[seat] = ids; return;
    }
    case 'chat': {
      if (r.phase !== 'match' || !r.p[1 - seat]) return;
      const now = Date.now(); if (now - (r.p[seat].lastChat || 0) < 700) return; r.p[seat].lastChat = now;
      const text = String(m.text || '').replace(/[\u0000-\u001f\u007f<>]/g, '').trim().slice(0, 60); if (!text) return;
      send(r.p[1 - seat].ws, { t: 'chat', text, n: Number(m.n) || 0 }); return;
    }
    case 'choice': {
      if (r.phase !== 'match' || r.m.stage !== 'wait') return;
      const mm = r.m, pk = mm.pk;
      if (seat === pk.team) {
        const k = m.kick || {}, x = Number(k.x), y = Number(k.y);
        if (!isFinite(x) || !isFinite(y) || !E.TYPES.includes(k.type)) return;
        mm.choice[seat] = { x: Math.max(-3.9, Math.min(3.9, x)), y: Math.max(.02, Math.min(2.6, y)), type: k.type };
      } else {
        const d = Math.floor(Number(m.dive)); if (!(d >= 0 && d <= 8)) return;
        mm.choice[seat] = { dive: d };
      }
      return;
    }
    case 'rematch':
      if (r.phase !== 'end') return;
      r.rematch[seat] = true;
      if (r.rematch[0] && r.rematch[1]) { r.toss = { winner: Math.random() < .5 ? 0 : 1, face: Math.random() < .5 ? 'CARA' : 'CRUZ' }; r.phase = 'toss'; return push(r); }
      return send(r.p[1 - seat] && r.p[1 - seat].ws, { t: 'info', text: 'Tu rival quiere la revancha.' });
  }
}
server.listen(PORT, () => console.log('Tanda de penales online escuchando en el puerto ' + PORT));
