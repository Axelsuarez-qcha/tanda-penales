/* Tanda de penales — motor del juego (puro, sin DOM, determinista con semilla). */
(function (root) {
'use strict';
const clamp = (x, a, b) => Math.max(a, Math.min(b, x));
const logit = p => Math.log(p / (1 - p));
const sig = x => 1 / (1 + Math.exp(-x));
const shrink = (g, n, prior, k) => (g + prior * k) / (n + k);
function mulberry32(a) { return function () { a |= 0; a = a + 0x6D2B79F5 | 0; let t = Math.imul(a ^ a >>> 15, 1 | a); t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t; return ((t ^ t >>> 14) >>> 0) / 4294967296; }; }
const pick = (rng, arr) => arr[Math.floor(rng() * arr.length)];
function shuffle(rng, arr) { const a = arr.slice(); for (let i = a.length - 1; i > 0; i--) { const j = Math.floor(rng() * (i + 1)); [a[i], a[j]] = [a[j], a[i]]; } return a; }

const SIDES = ['L', 'C', 'R'];
const TYPES = ['normal', 'fuerte', 'picada'];

/* ---------- 1) FÍSICA DEL PENAL (coordenadas en metros) ----------
   Arco 7,32 x 2,44. x: -3,66 (izq) a 3,66 (der). y: 0 (piso) a 2,44 (travesaño).
   El pateador elige un punto de puntería. La pelota cae en ese punto + un error gaussiano
   (el "diámetro" de incertidumbre) que depende del tipo de remate y del jugador.
   Después se clasifica: palo / travesaño / afuera / adentro. Si está adentro, el arquero
   la ataja según su alcance (elipse alrededor de su zona de tiro). */
const GW = 3.66, GH = 2.44, TOL = .08, PX = 480 / 7.32;
const KICK = {
  normal: { sx: .375, sy: .375, pm: .04 },
  fuerte: { sx: .65, sy: .65, pm: .065 },
  picada: { sx: .50, sy: .69, pm: .38 },
};
const MISHIT = 2.6;
const PHYS = { rxS: 1.5, rxD: 2.0, ryM: 1.5, ryE: 1.35, s0n: .90, s0f: .72, s0ps: 4, s0pd: .50 }; // alcance y fuerza del arquero (calibrado)
const MORALE = { goal: .35, miss: -.12 };
/* Zonas del arquero (3x3): idx = fila*3 + columna. Fila 0 = abajo. Columna 0 = izquierda */
const DX = [-2.3, 0, 2.3], DY = [.55, 1.2, 1.85];
const DIVES = []; for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) DIVES.push({ i: r * 3 + c, c, r, x: DX[c], y: DY[r] });
/* Zonas de puntería en el modo 9 zonas */
const ZX = [-2.85, 0, 2.85], ZY = [.5, 1.2, 1.95];
const ZONES = []; for (let r = 0; r < 3; r++) for (let c = 0; c < 3; c++) ZONES.push({ i: r * 3 + c, c, r, x: ZX[c], y: ZY[r] });
const physOf = x => x < -1.22 ? 'L' : x > 1.22 ? 'R' : 'C';
const clampAim = (x, y) => ({ x: clamp(x, -GW - .1, GW + .1), y: clamp(y, .05, GH + .1) });

/* Muestras fijas de ruido (determinista, cobertura pareja del plano) */
const NS = (() => { const n = 120, out = []; for (let i = 0; i < n; i++) { const u = (i + .5) / n, r = Math.sqrt(-2 * Math.log(1 - u)), th = 2 * Math.PI * ((i * 0.6180339887) % 1); out.push([r * Math.cos(th), r * Math.sin(th)]); } return out; })();

function classify(x, y) {
  y = Math.abs(y); const ax = Math.abs(x);
  if (ax > GW + TOL || y > GH + TOL) return 'wide';
  if (Math.abs(ax - GW) <= TOL) return 'post';
  if (Math.abs(y - GH) <= TOL) return 'bar';
  return 'in';
}
/* Parámetros de arquero para una zona de tiro y un tipo de remate */
function keeperParams(d, type, m) {
  const stay = Math.abs(d.x) < 1;
  const reach = Math.exp(.18 * m.bg);
  const Rx = (stay ? PHYS.rxS : PHYS.rxD) * reach, Ry = (d.r === 1 ? PHYS.ryM : PHYS.ryE) * reach;
  let s0 = type === 'normal' ? PHYS.s0n : type === 'fuerte' ? PHYS.s0f : (stay ? PHYS.s0ps : PHYS.s0pd);
  s0 = clamp(s0 * (1 + .08 * m.bg), .05, 2.2);
  return { kx: d.x, ky: d.y, Rx, Ry, s0 };
}
function savep(x, y, kv) {
  const dx = (x - kv.kx) / kv.Rx, dy = (y - kv.ky) / kv.Ry, d2 = dx * dx + dy * dy;
  return d2 >= 1 ? 0 : clamp(kv.s0 * (1 - d2), 0, 1);
}
function kickParams(type, m) {
  const b = KICK[type], f = Math.exp(-.35 * m.bk);
  return { sx: b.sx * f, sy: b.sy * f, pm: clamp(b.pm * Math.exp(-.45 * m.bk), .004, .5) };
}
/* Probabilidades (por cuadratura) de un punto de puntería + tipo contra una zona del arquero */
function cellStats(aim, type, g, kv) {
  const acc = { goal: 0, save: 0, post: 0, bar: 0, wide: 0 };
  for (const sc of [1, MISHIT]) {
    const w = sc === 1 ? 1 - g.pm : g.pm, scx = type === 'picada' && sc !== 1 ? 1.3 : sc;
    let goal = 0, save = 0, post = 0, bar = 0, wide = 0;
    for (let i = 0; i < NS.length; i++) {
      const x = aim.x + NS[i][0] * g.sx * scx, y = aim.y + NS[i][1] * g.sy * sc;
      const c = classify(x, y);
      if (c === 'in') { const sp = savep(x, Math.abs(y), kv); save += sp; goal += 1 - sp; }
      else if (c === 'post') post++; else if (c === 'bar') bar++; else wide++;
    }
    const n = NS.length; acc.goal += w * goal / n; acc.save += w * save / n; acc.post += w * post / n; acc.bar += w * bar / n; acc.wide += w * wide / n;
  }
  acc.miss = acc.post + acc.bar + acc.wide; return acc;
}

/* ---------- 2) STATS, JERARQUÍA Y PERKS ---------- */
function dataSide(player, phys) {
  if (phys === 'C') return 'M';
  const zurdo = player.pierna === 'I';
  if (phys === 'R') return zurdo ? 'P2' : 'P1';
  return zurdo ? 'P1' : 'P2';
}
function physSide(player, d) {
  if (d === 'M') return 'C';
  const zurdo = player.pierna === 'I';
  if (d === 'P1') return zurdo ? 'L' : 'R';
  return zurdo ? 'R' : 'L';
}
let GS = { P1: .78, P2: .77, M: .64 };
let GKS = { P1: .20, P2: .25, M: .33 };
function calibrate(players) {
  const k = { P1: [0, 0], P2: [0, 0], M: [0, 0] }, a = { P1: [0, 0], P2: [0, 0], M: [0, 0] };
  for (const p of players) {
    if (p.k) for (const s in k) { k[s][0] += p.k.s[s][0]; k[s][1] += p.k.s[s][1]; }
    if (p.a) for (const s in a) { a[s][0] += p.a.ks[s][0]; a[s][1] += p.a.ks[s][1]; }
  }
  for (const s in k) if (k[s][0] >= 20) GS[s] = k[s][1] / k[s][0];
  for (const s in a) if (a[s][0] >= 20) GKS[s] = a[s][1] / a[s][0];
  return { GS: { ...GS }, GKS: { ...GKS } };
}
const PEN_BASE = .82; // conversión asumida de penales de partido (la base solo tiene los convertidos, no los errados)
const keeperStop = A => shrink(A.sv, Math.max(0, A.n - A.afuera), .33, 8);
/* Efectividad: tandas + penales convertidos en partidos oficiales (sin errados cargados, se asume la media) */
function kickerRate(p) {
  const K = p.k || { n: 0, g: 0 }, pen = p.pen || 0;
  return shrink(K.g + pen, K.n + pen / PEN_BASE, .75, 6);
}
const H = p => p.h == null ? .5 : p.h;
/* Series definidas: se netean aciertos y errores. Queda un solo perk y, si hubo de los dos, pesa un poco menos */
function clutch(K) {
  if (!K) return null; const dw = K.dw || 0, mw = K.mw || 0;
  if (dw >= mw && dw > 0) return { kind: 'pos', w: dw - .5 * mw };
  if (mw > dw) return { kind: 'neg', w: mw - .5 * dw };
  return null;
}
function topSide(K) {
  let best = null; for (const s of ['P1', 'P2', 'M']) { const [n, g] = K.s[s]; if (n >= 4 && g / n >= .8 && (!best || g / n > best.r)) best = { s, r: g / n, n }; } return best;
}
function perksOf(p) {
  const out = [], K = p.k, A = p.a, h = H(p);
  if (K) {
    const cl = clutch(K);
    if (cl && cl.kind === 'pos') out.push({ id: 'definidor', label: cl.w >= 4 ? 'Definidor de finales' : 'Definidor', tone: 'pos', desc: `Definió series convirtiendo (peso neto ${cl.w.toFixed(1)}: una final internacional vale mucho más que un cuarto de copa).${K.mw > 0 ? ' Erró alguna, y eso le resta un poco.' : ''}` });
    if (cl && cl.kind === 'neg') out.push({ id: 'seachica', label: 'Se achica', tone: 'neg', desc: `Erró penales que definían series (peso neto ${cl.w.toFixed(1)}): baja su chance en penales decisivos.` });
    const net = K.abre[1] - (K.abre[0] - K.abre[1]);
    if (net > 0) out.push({ id: 'abridor', label: 'Abridor', tone: 'pos', desc: 'Abrió una tanda y convirtió: bonus si patea el primer penal.' });
    if (net < 0) out.push({ id: 'malabridor', label: 'Mal abridor', tone: 'neg', desc: 'Abrió una tanda y erró: penalización si patea el primer penal.' });
    if (K.n >= 4 && K.g / K.n >= .82) out.push({ id: 'frio', label: 'Sangre fría', tone: 'pos', desc: 'Efectividad altísima en tandas reales.' });
    if (K.tandas >= 4) out.push({ id: 'veterano', label: 'Veterano de tandas', tone: 'pos', desc: 'Jugó 4 o más tandas: se mantiene sereno en los penales decisivos.' });
    if (K.out >= 2 && K.out / K.n >= .2) out.push({ id: 'afuera', label: 'Se le va afuera', tone: 'neg', desc: 'Tiene antecedentes de mandarla afuera: su puntería es menos precisa.' });
    if (topSide(K)) out.push({ id: 'rinconero', label: 'Rinconero', tone: 'pos', desc: 'Convierte más del 80% hacia su zona favorita: más preciso cuando apunta ahí.' });
  }
  if ((p.pen || 0) >= 5) out.push({ id: 'penalista', label: (p.pen >= 15 ? 'Penalista histórico' : 'Penalista'), tone: 'pos', desc: `Convirtió ${p.pen} penales en partidos.` });
  if (!p.gk && h >= .9 && (p.pj || 0) >= 150) out.push({ id: 'referente', label: 'Referente', tone: 'pos', desc: 'Ídolo con gran jerarquía histórica: se agranda en los momentos clave.' });
  if (A) {
    if (A.n >= 8 && A.sv / Math.max(1, A.n - A.afuera) >= .35) out.push({ id: 'ataja', label: 'Atajapenales', tone: 'pos', desc: 'Ataja bastante más que el promedio.' });
    if (A.dw > 0) out.push({ id: 'heroe', label: 'Héroe de tandas', tone: 'pos', desc: `Definió series con una atajada (peso ${A.dw.toFixed(1)}): incomoda al pateador en penales decisivos.` });
    if (A.adiv && A.adiv[0] >= 10 && A.adiv[1] / A.adiv[0] >= .55) out.push({ id: 'olfato', label: 'Olfato', tone: 'pos', desc: 'Adivina el lado en más de la mitad de los penales: llega un poco más lejos.' });
  }
  if (p.gk && h >= .9) out.push({ id: 'referente', label: 'Referente', tone: 'pos', desc: 'Arquero de gran jerarquía histórica: pesa en los momentos clave.' });
  return out;
}
/* Nivel de penal 30-99 */
function ovr(p) {
  let v;
  if (p.gk) {
    const A = p.a; v = A ? 40 + (keeperStop(A) - .2) * 200 : 55;
    v += (H(p) - .5) * 30; if (A && A.dw > 0) v += Math.min(10, 2 * A.dw);
  } else {
    v = 40 + (kickerRate(p) - .55) * 130 + (H(p) - .5) * 30;
    const cl = clutch(p.k); if (cl && cl.kind === 'pos') v += Math.min(12, 1.5 * cl.w); if (cl && cl.kind === 'neg') v -= Math.min(10, 2 + 1.5 * cl.w);
    if ((p.pen || 0) >= 5) v += 3;
    for (const pk of perksOf(p)) if (!['definidor', 'seachica', 'penalista'].includes(pk.id)) v += pk.tone === 'pos' ? 2 : -3;
  }
  return Math.round(clamp(v, 30, 99));
}

/* ---------- 3) MODIFICADORES (log-odds: + favorece a su dueño) ----------
   bk (pateador) achica el círculo de error; bg (arquero) agranda su alcance. */
/* ctx: { decisive, first, morale, gkKick, streak, hot } */
function modifiers(kicker, keeper, aimSide, ctx) {
  const parts = [];
  const add = (v, l, who) => { if (Math.abs(v) > 1e-9) parts.push({ v, l, who }); };
  const K = kicker.k, A = keeper.a, sd = dataSide(kicker, aimSide), hk = H(kicker), hg = H(keeper);
  add(clamp(2.2 * (kickerRate(kicker) - .75), -.45, .45), 'Trayectoria como pateador (tandas y penales de partido)', 'k');
  if (!K && !(kicker.pen > 0)) add(-.15, 'Sin antecedentes como pateador', 'k');
  add(.5 * (hk - .5), 'Jerarquía histórica', 'k');
  if (kicker.pen >= 15) add(.2, 'Penalista histórico', 'k'); else if (kicker.pen >= 5) add(.1, 'Penalista', 'k');
  if (K && sd) { const s = K.s[sd]; add(clamp(1.0 * (shrink(s[1], s[0], GS[sd], 4) - GS[sd]), -.25, .25), 'Historial por zona', 'k'); const ts = topSide(K); if (ts && ts.s === sd) add(.2, 'Rinconero', 'k'); }
  if (K && K.out >= 2 && K.out / K.n >= .2) add(-.2, 'Se le va afuera', 'k');
  if (ctx.gkKick && !K) add(-.2, 'Arquero pateando', 'k');
  if (A) {
    add(clamp(1.8 * (keeperStop(A) - .33), -.4, .4), 'Trayectoria del arquero', 'g');
    if (sd) { const s = A.ks[sd]; add(clamp(1.0 * (shrink(s[1], s[0], GKS[sd], 5) - GKS[sd]), -.25, .25), 'Historial del arquero en esa zona', 'g'); }
    if (A.adiv && A.adiv[0] >= 10 && A.adiv[1] / A.adiv[0] >= .55) add(.12, 'Olfato', 'g');
  }
  add(.35 * (hg - .5), 'Jerarquía del arquero', 'g');
  if (ctx.decisive) {
    if (hk > .5) add(.45 * (hk - .5) * 2, 'Referente en momentos clave', 'k');
    const cl = clutch(K);
    if (cl && cl.kind === 'pos') add(clamp(.12 + .09 * cl.w, 0, .8), 'Definidor (saldo de series definidas)', 'k');
    if (cl && cl.kind === 'neg') add(-clamp(.08 + .05 * cl.w, 0, .5), 'Se achica (saldo de series definidas)', 'k');
    if (K && K.tandas >= 4) add(.12, 'Veterano de tandas', 'k');
    if (A && A.dw > 0) add(clamp(.1 + .08 * A.dw, 0, .6), 'Héroe de tandas (arquero)', 'g');
    if (hg > .5) add(.3 * (hg - .5) * 2, 'Arquero referente en momentos clave', 'g');
  }
  if (ctx.first && K) { const net = K.abre[1] - (K.abre[0] - K.abre[1]); if (net > 0) add(.25, 'Abridor', 'k'); else if (net < 0) add(-.25, 'Mal abridor', 'k'); }
  if (ctx.streak > 0) add(Math.min(.2, .06 * ctx.streak), 'Racha de goles del equipo', 'k');
  if (ctx.morale) add(ctx.morale, ctx.morale > 0 ? 'Moral alta' : 'Moral golpeada', 'k');
  if (ctx.hot) add(.12, 'Arquero crecido tras atajar', 'g');
  const sum = w => clamp(parts.filter(x => x.who === w).reduce((s, x) => s + x.v, 0), -1.2, 1.2);
  return { bk: sum('k'), bg: sum('g'), parts };
}
function resolveKick(rng, kicker, keeper, kick, diveIdx, ctx) {
  const side = physOf(kick.x), m = modifiers(kicker, keeper, side, ctx);
  const g = kickParams(kick.type, m), kv = keeperParams(DIVES[diveIdx], kick.type, m);
  const mis = rng() < g.pm, sc = mis ? MISHIT : 1;
  const u1 = Math.max(1e-9, rng()), u2 = rng(), r = Math.sqrt(-2 * Math.log(u1));
  const scx = kick.type === 'picada' && mis ? 1.3 : sc;
  const x = kick.x + r * Math.cos(2 * Math.PI * u2) * g.sx * scx, y = Math.abs(kick.y + r * Math.sin(2 * Math.PI * u2) * g.sy * sc);
  const cls = classify(x, y); let result = cls, sp = 0;
  if (cls === 'in') { sp = savep(x, y, kv); result = rng() < sp ? 'save' : 'goal'; }
  const st = cellStats(kick, kick.type, g, kv);
  const guess = Math.hypot(x - kv.kx, Math.abs(y) - kv.ky) < 1.2 && cls === 'in';
  return { result, land: { x, y }, guess, mishit: mis, sp, p: { ...st, parts: m.parts, bk: m.bk, bg: m.bg }, kick, dive: diveIdx, sigma: { x: g.sx, y: g.sy } };
}

/* ---------- 4) TANDA ---------- */
class Shootout {
  /* teams[i] = { name, gk, order:[5 jugadores de campo] } · first = equipo que patea primero · opts.mode: 'libre' | 'zonas' */
  constructor(teams, first, rng, opts = {}) {
    this.t = teams; this.first = first; this.rng = rng; this.mode = opts.mode || 'libre';
    this.sc = [0, 0]; this.kk = [0, 0]; this.gk = [0, 0]; this.sd = [0, 0];
    this.phase = 'reg'; this.winner = null; this.morale = [0, 0]; this.streak = [0, 0]; this.hot = [0, 0]; this.log = []; this.n = 0;
  }
  _cnt(phase) { return phase === 'reg' ? this.kk : phase === 'gk' ? this.gk : this.sd; }
  _state() { return { sc: this.sc.slice(), kk: this.kk.slice(), gk: this.gk.slice(), sd: this.sd.slice(), phase: this.phase }; }
  static check(s) {
    if (s.phase === 'reg') {
      const r0 = 5 - s.kk[0], r1 = 5 - s.kk[1];
      if (s.sc[0] > s.sc[1] + r1) return { w: 0 };
      if (s.sc[1] > s.sc[0] + r0) return { w: 1 };
      if (s.kk[0] === 5 && s.kk[1] === 5) return s.sc[0] === s.sc[1] ? { phase: 'gk' } : { w: s.sc[0] > s.sc[1] ? 0 : 1 };
    } else if (s.phase === 'gk') {
      if (s.gk[0] === 1 && s.gk[1] === 1) return s.sc[0] === s.sc[1] ? { phase: 'sd' } : { w: s.sc[0] > s.sc[1] ? 0 : 1 };
    } else if (s.phase === 'sd') {
      if (s.sd[0] === s.sd[1] && s.sd[0] > 0 && s.sc[0] !== s.sc[1]) return { w: s.sc[0] > s.sc[1] ? 0 : 1 };
    }
    return {};
  }
  _hyp(team, goal) {
    const s = this._state(); const key = s.phase === 'reg' ? 'kk' : s.phase;
    s[key][team]++; if (goal) s.sc[team]++;
    const c = Shootout.check(s); return c.w !== undefined ? c.w : null;
  }
  peek() {
    if (this.winner !== null) return null;
    const cnt = this._cnt(this.phase), o = 1 - this.first;
    const team = cnt[this.first] === cnt[o] ? this.first : o;
    const T = this.t[team], O = this.t[1 - team];
    const kicker = this.phase === 'reg' ? T.order[this.kk[team]] : this.phase === 'gk' ? T.gk : T.order[this.sd[team] % 5];
    const winOnGoal = this._hyp(team, true) === team, loseOnMiss = this._hyp(team, false) === 1 - team;
    const secondOfPair = this.phase !== 'reg' && cnt[team] < cnt[1 - team];
    return {
      team, kicker, keeper: O.gk, phase: this.phase, no: this.n + 1,
      round: (this.phase === 'reg' ? this.kk[team] : this.phase === 'sd' ? this.sd[team] : 0) + 1,
      winOnGoal, loseOnMiss, decisive: secondOfPair || winOnGoal || loseOnMiss,
      first: this.n === 0, morale: this.morale[team], gkKick: this.phase === 'gk', streak: this.streak[team], hot: this.hot[1 - team],
    };
  }
  ctxOf(pk) { return { decisive: pk.decisive, first: pk.first, morale: pk.morale, gkKick: pk.gkKick, streak: pk.streak, hot: pk.hot }; }
  /* kick = {x, y, type} (en modo zonas el punto se ajusta al centro de la zona) · dive = índice 0..8 */
  play(pk, kick, dive) {
    if (this.mode === 'zonas') { let b = ZONES[0], bd = 1e9; for (const z of ZONES) { const d = Math.hypot(z.x - kick.x, z.y - kick.y); if (d < bd) { bd = d; b = z; } } kick = { x: b.x, y: b.y, type: kick.type }; }
    else { const c = clampAim(kick.x, kick.y); kick = { x: c.x, y: c.y, type: kick.type }; }
    const out = resolveKick(this.rng, pk.kicker, pk.keeper, kick, dive, this.ctxOf(pk));
    const goal = out.result === 'goal';
    const key = this.phase === 'reg' ? 'kk' : this.phase;
    this[key][pk.team]++; if (goal) this.sc[pk.team]++; this.n++;
    this.morale[pk.team] = kick.type === 'picada' ? (goal ? MORALE.goal : MORALE.miss) : 0;
    this.streak[pk.team] = goal ? this.streak[pk.team] + 1 : 0;
    this.hot[1 - pk.team] = out.result === 'save' ? 1 : 0;
    const rec = { ...out, pk, scoreAfter: this.sc.slice() };
    this.log.push(rec);
    const c = Shootout.check(this._state());
    if (c.w !== undefined) this.winner = c.w; else if (c.phase) this.phase = c.phase;
    rec.phaseAfter = this.phase; rec.winner = this.winner;
    return rec;
  }
}

/* ---------- 5) IA (equilibrio mixto por regret matching) ---------- */
const XS = [-3.3, -2.6, -1.4, 0, 1.4, 2.6, 3.3], YS = [.4, 1.2, 2.05];
function options(mode) {
  const out = [];
  if (mode === 'zonas') for (const t of TYPES) for (const z of ZONES) out.push({ x: z.x, y: z.y, type: t });
  else for (const t of TYPES) for (const y of YS) for (const x of XS) out.push({ x, y, type: t });
  return out;
}
const OPT = { libre: options('libre'), zonas: options('zonas') };
function payoffMatrix(sh, pk) {
  const ctx = sh.ctxOf(pk), opts = OPT[sh.mode], mc = {};
  const modsFor = side => mc[side] || (mc[side] = modifiers(pk.kicker, pk.keeper, side, ctx));
  return opts.map(o => {
    const m = modsFor(physOf(o.x)), g = kickParams(o.type, m);
    return DIVES.map(d => {
      const st = cellStats(o, o.type, g, keeperParams(d, o.type, m));
      return st.goal + (o.type === 'picada' ? st.goal * .03 - (1 - st.goal) * .01 : 0);
    });
  });
}
function solve(M, iters = 400) {
  const R = M.length, C = M[0].length;
  const rr = new Array(R).fill(0), rc = new Array(C).fill(0), sr = new Array(R).fill(0), sc = new Array(C).fill(0);
  const norm = reg => { let s = 0; const pos = reg.map(x => { const v = x > 0 ? x : 0; s += v; return v; }); return s > 0 ? pos.map(x => x / s) : reg.map(() => 1 / reg.length); };
  for (let t = 0; t < iters; t++) {
    const p = norm(rr), q = norm(rc);
    const up = M.map(row => { let s = 0; for (let j = 0; j < C; j++) s += row[j] * q[j]; return s; });
    const uq = new Array(C).fill(0); for (let i = 0; i < R; i++) if (p[i] > 0) for (let j = 0; j < C; j++) uq[j] += M[i][j] * p[i];
    let vp = 0, vq = 0; for (let i = 0; i < R; i++) vp += p[i] * up[i]; for (let j = 0; j < C; j++) vq += q[j] * uq[j];
    for (let i = 0; i < R; i++) { rr[i] += up[i] - vp; sr[i] += p[i]; }
    for (let j = 0; j < C; j++) { rc[j] += vq - uq[j]; sc[j] += q[j]; }
  }
  const ns = a => { const s = a.reduce((x, y) => x + y, 0); return a.map(x => x / s); };
  const p = ns(sr), q = ns(sc);
  let value = 0; for (let i = 0; i < R; i++) for (let j = 0; j < C; j++) value += p[i] * q[j] * M[i][j];
  return { p, q, value };
}
const DIFF = { facil: .55, normal: .18, dificil: .03 };
function sampleIdx(rng, w) { let r = rng(), a = 0; for (let i = 0; i < w.length; i++) { a += w[i]; if (r < a) return i; } return w.length - 1; }
const _cache = { sh: null, n: -1, sol: null };
function solved(sh, pk) { if (_cache.sh !== sh || _cache.n !== sh.n) { _cache.sh = sh; _cache.n = sh.n; _cache.sol = solve(payoffMatrix(sh, pk)); } return _cache.sol; }
function aiKick(sh, pk, rng, diff = 'normal') {
  const { p } = solved(sh, pk), e = DIFF[diff], opts = OPT[sh.mode];
  // "estilo" de la IA: usa la picada con moderación (más natural), salvo en dificultad difícil
  const taste = { normal: 1, fuerte: .85, picada: diff === 'dificil' ? .6 : .3 };
  let tp = p.map((x, i) => x * taste[opts[i].type]); const ts = tp.reduce((a, b) => a + b, 0); tp = tp.map(x => x / ts);
  const w = tp.map(x => (1 - e) * x + e / p.length), o = opts[sampleIdx(rng, w)];
  const j = sh.mode === 'zonas' ? 0 : .12;
  return { x: o.x + (rng() - .5) * 2 * j, y: o.y + (rng() - .5) * 2 * j, type: o.type };
}
function aiDive(sh, pk, rng, diff = 'normal') {
  const { q } = solved(sh, pk), e = DIFF[diff];
  return sampleIdx(rng, q.map(x => (1 - e) * x + e / q.length));
}
function aiOrder(field) {
  const r = field.slice().sort((a, b) => ovr(b) - ovr(a));
  return [r[0], r[2], r[3], r[4], r[1]];
}

/* ---------- 6) DRAFT ----------
   Rondas (F = el que elige 1° al arrancar, S = el otro):
   R1: F elige 1, S se lleva los 2 restantes · R2: F elige 1, S elige 1, el que sobra queda y se suman 2 nuevos
   R3: S elige 1, F se lleva los 2 restantes · R4: S elige 1, F se lleva los 2 restantes · el último pasa a S.
   Total 6 y 6. Nadie puede quedarse con los 2 arqueros: el motor conoce el mazo y bloquea las jugadas que lo fuerzan. */
const STEPS = [{ k: 'rest', who: 'F' }, { k: 'one', first: 'F', second: 'S' }, { k: 'rest', who: 'S' }, { k: 'rest', who: 'S' }, { k: 'last', to: 'S' }];
function cloneS(s) { return { deck: s.deck, dealt: s.dealt, vis: s.vis.slice(), teams: [s.teams[0].slice(), s.teams[1].slice()], F: s.F, S: s.S, step: s.step, sub: s.sub, entered: s.entered, log: s.log.slice(), byId: s.byId }; }
function gkCount(s, t) { return s.teams[t].filter(id => s.byId[id].gk).length; }
function advance(s) {
  for (;;) {
    if (s.step >= STEPS.length) return s;
    const st = STEPS[s.step];
    if (!s.entered) {
      const need = Math.min(3 - s.vis.length, s.deck.length - s.dealt);
      for (let i = 0; i < need; i++) s.vis.push(s.deck[s.dealt++]);
      s.entered = true; s.log.push({ type: 'deal', ids: s.vis.slice() });
    }
    if (st.k === 'last') { const to = s[st.to]; s.teams[to].push(...s.vis); s.log.push({ type: 'auto', team: to, ids: s.vis.slice() }); s.vis = []; s.step++; s.entered = false; s.sub = 0; continue; }
    return s;
  }
}
function turn(s) {
  if (s.step >= STEPS.length) return null;
  const st = STEPS[s.step];
  const team = st.k === 'rest' ? s[st.who] : (s.sub === 0 ? s[st.first] : s[st.second]);
  return { team, step: s.step, sub: s.sub, options: s.vis.slice() };
}
function applyPick(s0, id) {
  const s = cloneS(s0), st = STEPS[s.step], t = turn(s).team;
  s.teams[t].push(id); s.vis = s.vis.filter(x => x !== id); s.log.push({ type: 'pick', team: t, id });
  if (st.k === 'rest') {
    const o = 1 - t; s.teams[o].push(...s.vis); s.log.push({ type: 'rest', team: o, ids: s.vis.slice() }); s.vis = []; s.step++; s.entered = false; s.sub = 0;
  } else if (s.sub === 0) s.sub = 1;
  else { s.step++; s.entered = false; s.sub = 0; }
  return advance(s);
}
function valid(s) { return gkCount(s, 0) <= 1 && gkCount(s, 1) <= 1; }
function feasible(s) {
  if (!valid(s)) return false;
  if (s.step >= STEPS.length) return gkCount(s, 0) === 1 && gkCount(s, 1) === 1 && s.teams[0].length === 6 && s.teams[1].length === 6;
  return s.vis.some(id => feasible(applyPick(s, id)));
}
function legalPicks(s) { return s.vis.filter(id => feasible(applyPick(s, id))); }
function newDraft(players, rng) {
  const gks = players.filter(p => p.gk), fld = players.filter(p => !p.gk);
  const g = shuffle(rng, gks).slice(0, 2), f = shuffle(rng, fld).slice(0, 10);
  const deck = shuffle(rng, g.concat(f)); const byId = {}; deck.forEach(p => byId[p.id] = p);
  return { deck: deck.map(p => p.id), dealt: 0, vis: [], teams: [[], []], F: 0, S: 1, step: 0, sub: 0, entered: false, log: [], byId };
}
function startDraft(s, F) { const c = cloneS(s); c.F = F; c.S = 1 - F; return advance(c); }


/* ---------- 6b) DRAFT "VETO + PRESUPUESTO" ----------
   Cada ronda muestra 4 cartas. El que NO elige primero veta 1 (la carta se va del juego; los arqueros son inmunes).
   Después elige 1 el primero de la ronda y luego 1 el otro. La carta que sobra queda para la ronda siguiente, donde
   los roles se invierten. 6 rondas = 6 jugadores por equipo. Cada jugador tiene un precio según su nivel y cada
   equipo tiene un tope de fichas. Se necesita 1 ficha como mínimo por casillero libre. */
const VT = { CAP: 32, SHOW: 4, DECK: 19, ROUNDS: 6, FIELD: 5 };
function vtPrice(p) { return clamp(Math.round(1 + 14 * Math.pow(Math.max(0, ovr(p) - 35) / 64, 2)), 1, 15); }
function vtClone(s) { return Object.assign({}, s, { vis: s.vis.slice(), teams: [s.teams[0].slice(), s.teams[1].slice()], spent: s.spent.slice(), vetoed: s.vetoed.slice(), log: s.log.slice() }); }
function vtNew(players, rng, cap) {
  const gks = players.filter(p => p.gk), fld = players.filter(p => !p.gk);
  const g = shuffle(rng, gks).slice(0, 2), f = shuffle(rng, fld).slice(0, VT.DECK - 2);
  const deck = shuffle(rng, g.concat(f));
  // los dos arqueros tienen que salir en las primeras 3 rondas (10 cartas)
  for (const gp of g) {
    let i = deck.indexOf(gp);
    if (i >= 10) { let j; do { j = Math.floor(rng() * 10); } while (deck[j].gk); [deck[i], deck[j]] = [deck[j], deck[i]]; }
  }
  const byId = {}, price = {}; deck.forEach(p => { byId[p.id] = p; price[p.id] = vtPrice(p); });
  return { mode: 'veto', cap: cap || VT.CAP, deck: deck.map(p => p.id), dealt: 0, vis: [], teams: [[], []], spent: [0, 0], vetoed: [], F: 0, S: 1, round: 0, phase: 'veto', log: [], byId, price };
}
function vtDeal(s) {
  if (s.round >= VT.ROUNDS) return s;
  const need = Math.min(VT.SHOW - s.vis.length, s.deck.length - s.dealt);
  for (let i = 0; i < need; i++) s.vis.push(s.deck[s.dealt++]);
  s.log.push({ type: 'deal', round: s.round, ids: s.vis.slice() });
  return s;
}
function vtStart(s0, F) { const s = vtClone(s0); s.F = F; s.S = 1 - F; s.round = 0; s.phase = 'veto'; return vtDeal(s); }
function vtFirst(s) { return s.round % 2 === 0 ? s.F : s.S; }       // el que elige primero en la ronda
function vtTurn(s) {
  if (s.round >= VT.ROUNDS) return null;
  const A = vtFirst(s), B = 1 - A;
  return { team: s.phase === 'p1' ? A : B, phase: s.phase === 'veto' ? 'veto' : 'pick', sub: s.phase, round: s.round, first: A, options: s.vis.slice() };
}
const gkOf = (s, t) => s.teams[t].some(id => s.byId[id].gk);
function vtRoleOk(s, t, id) { return s.byId[id].gk ? !gkOf(s, t) : s.teams[t].filter(x => !s.byId[x].gk).length < VT.FIELD; }
function vtMax(s, t) { return s.cap - s.spent[t] - (5 - s.teams[t].length); }
function vtLegal(s) {
  const t = vtTurn(s); if (!t) return [];
  if (t.phase === 'veto') return s.vis.filter(id => !s.byId[id].gk).map(id => ({ id, cost: 0 }));
  const max = vtMax(s, t.team), ok = s.vis.filter(id => vtRoleOk(s, t.team, id));
  const aff = ok.filter(id => s.price[id] <= max).map(id => ({ id, cost: s.price[id] }));
  return aff.length ? aff : ok.map(id => ({ id, cost: Math.min(s.price[id], max) }));
}
function vtApply(s0, id) {
  const s = vtClone(s0), t = vtTurn(s), L = vtLegal(s).find(o => o.id === id);
  if (!L) throw new Error('jugada ilegal');
  s.vis = s.vis.filter(x => x !== id);
  if (t.phase === 'veto') { s.vetoed.push(id); s.log.push({ type: 'veto', team: t.team, id }); s.phase = 'p1'; return s; }
  s.teams[t.team].push(id); s.spent[t.team] += L.cost; s.log.push({ type: 'pick', team: t.team, id, cost: L.cost });
  if (s.phase === 'p1') s.phase = 'p2'; else { s.round++; s.phase = 'veto'; vtDeal(s); }
  return s;
}
/* IA */
function vtVal(s, t, id) {
  if (!vtRoleOk(s, t, id)) return null;
  const p = s.byId[id], slots = 6 - s.teams[t].length, c = Math.min(s.price[id], vtMax(s, t));
  const per = (s.cap - s.spent[t]) / Math.max(1, slots), lam = 3.5 * clamp(5.7 / per, .6, 1.8);
  let v = ovr(p) - lam * c;
  if (p.gk) v += 1.5 * (6 - slots);
  return v;
}
function vtAI(s, rng, diff) {
  const t = vtTurn(s), me = t.team, ri = 1 - me, L = vtLegal(s);
  const eps = { facil: .45, normal: .12, dificil: 0 }[diff] || 0;
  if (L.length === 1 || rng() < eps) return pick(rng, L).id;
  const best = (ids, team) => { let b = null, bv = -Infinity; for (const x of ids) { const v = vtVal(s, team, x); if (v !== null && v > bv) { bv = v; b = x; } } return b === null ? null : { id: b, v: bv }; };
  if (t.phase === 'veto') {
    let bid = null, bs = -Infinity;
    for (const o of L) {
      const rem = s.vis.filter(x => x !== o.id), a = best(rem, ri), rem2 = rem.filter(x => !a || x !== a.id), b = best(rem2, me);
      const left = b ? rem2.filter(x => x !== b.id) : rem2, lv = left.length ? (vtVal(s, me, left[0]) || 0) : 0;
      const sc = (b ? b.v : 0) - 0.7 * (a ? a.v : 0) + 0.25 * lv;
      if (sc > bs) { bs = sc; bid = o.id; }
    }
    return bid;
  }
  let bid = null, bs = -Infinity;
  for (const o of L) { const sv = vtVal(s, me, o.id), rv = vtVal(s, ri, o.id); const sc = sv + 0.3 * (rv === null ? 0 : rv); if (sc > bs) { bs = sc; bid = o.id; } }
  return bid;
}

/* ---------- 6c) SUBASTA CIEGA CON PATRÓN ----------
   12 lotes (2 arqueros + 10 de campo). Todos los de campo comparten un rasgo oculto (el patrón). Cada lote dura
   LOT_SEC segundos y va soltando pistas. Gana la oferta más alta al terminar el tiempo (o cuando el rival se retira).
   Una oferta en los últimos 3 s estira la subasta 5 s. Presupuesto: 100 fichas por equipo (el que patea primero parte con 95). */
const AU = { SLOTS: 6, FIELD: 5, BUDGET: 100, FIRST_COST: 5, SNIPE: 3000, EXTEND: 5000, MAXEXT: 8, LOT_SEC: 60 };
const THEMES = [
  { id: 'inf', name: 'Surgidos de las inferiores', dim: 'org', test: p => p.org === 'Inferiores' },
  { id: 'zur', name: 'Zurdos', dim: 'pierna', test: p => p.pierna === 'I' },
  { id: 'ext', name: 'Nacidos fuera de la Argentina', dim: 'pais', test: p => !!p.pais && p.pais !== 'Argentina' },
  { id: 'alt', name: 'Altos: 1,85 m o más', dim: 'alt', test: p => p.alt != null && p.alt >= 1.85 },
  { id: 'baj', name: 'Bajos: 1,75 m o menos', dim: 'alt', test: p => p.alt != null && p.alt <= 1.75 },
  { id: 'sel', name: 'Jugaron en una selección', dim: 'sel', test: p => !!p.sel },
  { id: 'd80', name: 'Jugaron sobre todo en los años 80', dim: 'dec', test: p => p.dec === 1980 },
  { id: 'd90', name: 'Jugaron sobre todo en los años 90', dim: 'dec', test: p => p.dec === 1990 },
  { id: 'd00', name: 'Jugaron sobre todo en los 2000', dim: 'dec', test: p => p.dec === 2000 },
  { id: 'd10', name: 'Jugaron sobre todo en los 2010', dim: 'dec', test: p => p.dec === 2010 },
  { id: 'd20', name: 'Jugaron sobre todo en los 2020', dim: 'dec', test: p => p.dec === 2020 },
];
const AU_CLUES = [['pos', 0], ['dec', 0], ['tray', 12], ['nombre', 24], ['perks', 36], ['nivel', 48]];
const AU_LBL = { pos: 'Puesto', dec: 'Época', org: 'Cuna', pais: 'Nació en', pierna: 'Pierna', alt: 'Altura', sel: 'Selección', tray: 'En Boca', tandas: 'En tandas', perks: 'Perks', nombre: 'Nombre', nivel: 'Nivel' };
const POS_LBL = { ARQ: 'Arquero', DFC: 'Defensor central', DFI: 'Lateral izquierdo', DFD: 'Lateral derecho', LI: 'Lateral izquierdo', LD: 'Lateral derecho', MC: 'Volante central', MCD: 'Volante defensivo', MCO: 'Volante ofensivo', MI: 'Volante izquierdo', MD: 'Volante derecho', ENG: 'Enganche', ED: 'Extremo derecho', EI: 'Extremo izquierdo', EXT: 'Extremo', DC: 'Delantero', SD: 'Segundo delantero' };
const decTxt = d => d === 1980 ? 'Años 80' : d === 1990 ? 'Años 90' : d === 2000 ? 'Años 2000' : d === 2010 ? 'Años 2010' : d === 2020 ? 'Años 2020' : 'Décadas del ' + d;
function auThemesFor(players) {
  return THEMES.filter(t => players.filter(p => !p.gk && t.test(p)).length >= 10);
}
function auClueText(p, k) {
  switch (k) {
    case 'pos': return p.gk ? 'Arquero' : (POS_LBL[p.pos] || p.pos);
    case 'dec': return decTxt(p.dec) + ' (debutó en ' + p.deb + ')';
    case 'org': return p.org === 'Inferiores' ? 'Surgido de las inferiores' : 'Llegó desde ' + p.org;
    case 'pais': return p.pais ? 'Nació en ' + p.pais : 'Sin dato de nacimiento';
    case 'pierna': return p.pierna === 'I' ? 'Zurdo' : p.pierna === 'D' ? 'Derecho' : 'Sin dato de pierna';
    case 'alt': return p.alt ? p.alt.toFixed(2).replace('.', ',') + ' m' : 'Sin dato de altura';
    case 'sel': return p.sel ? 'Jugó en su selección' : 'Nunca jugó en su selección';
    case 'tray': return p.pj + ' partidos' + (p.gk ? '' : ', ' + p.gol + ' goles') + ' · ' + p.deb + '–' + (p.ult >= 2026 ? 'hoy' : p.ult);
    case 'tandas': return p.gk ? (p.a && p.a.n ? 'Enfrentó ' + p.a.n + ' penales en tandas y atajó ' + p.a.sv : 'Sin tandas registradas') : (p.k && p.k.n ? 'Pateó ' + p.k.n + ' en tandas y convirtió ' + p.k.g : 'Sin penales en tandas registrados');
    case 'perks': { const ps = perksOf(p); return ps.length ? ps.map(x => x.label).join(' · ') : 'Sin perks'; }
    case 'nombre': return p.nombre;
    case 'nivel': return String(ovr(p));
  }
}
function auClues(A, id, tSec) {
  const p = A.byId[id], skip = A.wild[id] ? null : A.theme.dim, sc = A.lotSec / 60;
  return AU_CLUES.filter(([k]) => k !== skip).map(([k, at]) => { const a = at * sc, shown = tSec >= a; return { k, label: AU_LBL[k], at: a, shown, text: shown ? auClueText(p, k) : null }; });
}
const auFairC = n => 1 + 14 * Math.pow(Math.max(0, n - 35) / 64, 2);
function auNew(players, rng, o = {}) {
  const themes = auThemesFor(players), th = (o.themeId && themes.find(t => t.id === o.themeId)) || pick(rng, themes);
  const fm = players.filter(p => !p.gk && th.test(p)), gm = players.filter(p => p.gk && th.test(p));
  const f = shuffle(rng, fm).slice(0, 10);
  const wildGK = gm.length < 2, g = shuffle(rng, wildGK ? players.filter(p => p.gk) : gm).slice(0, 2);
  const lots = shuffle(rng, f.concat(g)), byId = {}, wild = {};
  lots.forEach(p => { byId[p.id] = p; wild[p.id] = p.gk && wildGK; });
  const raw = lots.map(p => auFairC(ovr(p))), sc = (2 * AU.BUDGET) / raw.reduce((a, b) => a + b, 0), fair = {};
  lots.forEach((p, i) => fair[p.id] = raw[i] * sc);
  return { mode: 'subasta', theme: th, wildGK, lots: lots.map(p => p.id), byId, wild, fair, mu: 2 * AU.BUDGET / 12, rng, lotSec: o.lotSec || AU.LOT_SEC,
    teams: [[], []], budget: [AU.BUDGET, AU.BUDGET], S: 0, F: 1, lot: -1, cur: null, over: false, log: [] };
}
function auStart(A, firstKicker) { A.S = firstKicker; A.F = 1 - firstKicker; A.budget[firstKicker] -= AU.FIRST_COST; return A; }
function auElig(A, t, id) { return A.byId[id].gk ? !A.teams[t].some(x => A.byId[x].gk) : A.teams[t].filter(x => !A.byId[x].gk).length < AU.FIELD; }
const auMax = (A, t) => A.budget[t] - (AU.SLOTS - 1 - A.teams[t].length);
function auSell(A, t, id, price, extra) { A.teams[t].push(id); A.budget[t] -= price; const ev = Object.assign({ type: 'sold', team: t, id, price, fair: A.fair[id] }, extra || {}); A.log.push(ev); return ev; }
/* arranca el siguiente lote. Si un solo equipo puede recibirlo, se lo lleva directo por 1 ficha. */
function auNext(A, now) {
  const evs = [];
  for (;;) {
    A.lot++;
    if (A.lot >= A.lots.length) { A.over = true; A.cur = null; return evs; }
    const id = A.lots[A.lot], el = [0, 1].filter(t => auElig(A, t, id));
    if (el.length === 1) { evs.push(auSell(A, el[0], id, Math.min(1, auMax(A, el[0])), { auto: true })); continue; }
    A.cur = { id, start: now, end: now + A.lotSec * 1000, bid: 0, leader: null, done: [false, false], ext: 0, closed: null, bids: [] };
    evs.push({ type: 'lot', lot: A.lot, id }); return evs;
  }
}
function auBid(A, t, amount, now) {
  const c = A.cur; if (!c || c.closed) return { ok: false, why: 'cerrada' };
  amount = Math.floor(amount);
  if (c.leader === t) return { ok: false, why: 'ya lideras' };
  if (amount <= c.bid || amount < 1) return { ok: false, why: 'baja' };
  if (amount > auMax(A, t)) return { ok: false, why: 'presupuesto' };
  c.bid = amount; c.leader = t; c.done[t] = true; c.done[1 - t] = false; c.bids.push({ t, amount, at: now });
  let extended = false;
  if (c.end - now <= AU.SNIPE && c.ext < AU.MAXEXT) { c.end += AU.EXTEND; c.ext++; extended = true; }
  return { ok: true, extended };
}
/* darse de baja: si nadie ofertó, el rival se lleva el lote por 1 ficha y se cierra ya */
function auDrop(A, t) {
  const c = A.cur; if (!c || c.closed) return;
  if (c.leader === null) { c.leader = 1 - t; c.bid = 1; c.bids.push({ t: 1 - t, amount: 1, at: 0 }); }
  c.done[0] = c.done[1] = true;
}
function auPass(A, t) { if (A.cur && !A.cur.closed) A.cur.done[t] = true; }
function auTick(A, now) {
  const c = A.cur; if (!c || c.closed) return [];
  if (!(now >= c.end || (c.done[0] && c.done[1]))) return [];
  let ev;
  if (c.leader === null) { const w = A.rng() < .5 ? 0 : 1; ev = auSell(A, w, c.id, Math.min(1, auMax(A, w)), { nobids: true }); }
  else ev = auSell(A, c.leader, c.id, c.bid, { timeout: now >= c.end });
  c.closed = ev; return [ev];
}
/* IA subastadora (sirve para cualquiera de los dos equipos) */
const AU_AI = {
  facil:   { noise: .28, rmax: .70, tfull: 60, react: [1.6, 4.0], snipe: .10, aggr: 1.12, tmin: [24, 46] },
  normal:  { noise: .12, rmax: .92, tfull: 46, react: [.8, 2.4],  snipe: .30, aggr: 1.32, tmin: [20, 38] },
  dificil: { noise: .05, rmax: 1.0, tfull: 38, react: [.5, 1.4],  snipe: .45, aggr: 1.42, tmin: [18, 34] } };
function auAIInit(A, rng, diff, me) {
  const P = AU_AI[diff] || AU_AI.normal, sc = A.lotSec / 60, c = A.cur, r = (a, b) => a + rng() * (b - a);
  return { P, me, noise: (rng() * 2 - 1) * P.noise * A.mu, tmin: r(P.tmin[0], P.tmin[1]) * sc * 1000, react: r(P.react[0], P.react[1]) * 1000,
    nextAct: c.start + r(2, 14) * sc * 1000, seen: 0, snipe: rng() < P.snipe, rng };
}
function auAIMax(A, ai, now) {
  const c = A.cur, P = ai.P, tSec = (now - c.start) / 1000 / (A.lotSec / 60), r = Math.min(P.rmax, .2 + .8 * tSec / P.tfull);
  const est = A.mu + (A.fair[c.id] - A.mu) * r + ai.noise, slots = AU.SLOTS - A.teams[ai.me].length, per = A.budget[ai.me] / slots;
  const mult = Math.pow(clamp(per / A.mu, .7, 2.4), .8);
  return Math.min(Math.floor(est * mult * P.aggr), auMax(A, ai.me));
}
function auAIStep(A, ai, now) {
  const c = A.cur; if (!c || c.closed || c.leader === ai.me) return null;
  if (c.bid !== ai.seen) {
    ai.seen = c.bid; ai.nextAct = now + ai.react * (.7 + ai.rng() * .6);
    if (ai.snipe && c.bid > 0) ai.nextAct = Math.max(ai.nextAct, c.end - (2.2 + ai.rng() * 2) * 1000);
  }
  if (now < ai.nextAct) return null;
  const max = auAIMax(A, ai, now), price = c.bid;
  if (max >= price + 1) {
    const amount = Math.min(max, price + 1 + Math.floor(ai.rng() * (1 + (max - price) * .15)));
    ai.nextAct = now + 600; return { type: 'bid', amount };
  }
  if (now - c.start >= ai.tmin) return { type: 'pass' };
  ai.nextAct = now + 600; return null;
}
/* ---------- 7) RELATO ---------- */
function placeText(x, y) {
  const ax = Math.abs(x), side = x < 0 ? 'izquierdo' : 'derecho';
  if (ax > 2.5 && y > 1.7) return `al ángulo ${side}`;
  if (ax > 2.5 && y < .8) return `pegada al palo ${side}, a ras del piso`;
  if (ax > 2.5) return `junto al palo ${side}`;
  if (ax < 1.0 && y > 1.7) return 'al medio, por arriba';
  if (ax < 1.0 && y < .8) return 'al medio, bien abajo';
  if (ax < 1.0) return 'al medio';
  if (y > 1.7) return `arriba, hacia el lado ${side}`;
  if (y < .8) return `abajo, hacia el lado ${side}`;
  return `al lado ${side}`;
}
function narratePre(rng, pk) {
  const K = pk.kicker.ap, G = pk.keeper.ap, L = [];
  if (pk.phase === 'gk') L.push(`¡Insólito! Patean los arqueros. ${K} se hace cargo de la pelota ante ${G}.`, `Y se viene lo más raro de la noche: ${K}, el arquero, camina hacia el punto penal.`);
  else if (pk.phase === 'sd') L.push(`Muerte súbita. Se juega todo en cada disparo. Va ${K}, enfrente ${G}.`, `Ya no hay margen. ${K} acomoda la pelota. ${G} se agranda bajo los tres palos.`);
  else if (pk.first) L.push(`Arranca la tanda. ${K} acomoda la pelota en el punto penal y ${G} espera con los brazos abiertos.`, `Silencio en la Bombonera. Primer penal: ${K} contra ${G}.`);
  else if (pk.winOnGoal) L.push(`¡Si convierte, se termina! ${K} tiene en sus pies la definición. ${G}, el último obstáculo.`, `Penal para ganarla. ${K} mira al arco, mira a ${G}... respira hondo.`);
  else if (pk.loseOnMiss) L.push(`¡Está obligado! Si ${K} falla, se termina todo. ${G} lo espera.`, `Pelota al punto penal: ${K} no puede errar. El estadio contiene la respiración.`);
  else L.push(`Va ${K}. Frente a él, ${G}.`, `Se prepara ${K}. ${G} camina sobre la línea.`, `Turno de ${K}. Acomoda, retrocede, mira al arquero.`);
  if (pk.morale > 0) L.push(`Llega con la moral por las nubes después de la última picada.`);
  if (pk.morale < 0) L.push(`Se nota el golpe de la picada fallada del compañero.`);
  return pick(rng, L);
}
function narrateKick(rng, rec) {
  const pk = rec.pk, K = pk.kicker.ap, G = pk.keeper.ap, { kick, result, land, dive } = rec;
  const dv = DIVES[dive], dTxt = Math.abs(dv.x) < 1 ? `${G} se queda en el medio` : `${G} se tira ${dv.x < 0 ? 'a su izquierda' : 'a su derecha'}`;
  const where = placeText(land.x, Math.abs(land.y)), aimed = placeText(kick.x, kick.y);
  const run = kick.type === 'picada' ? pick(rng, [`${K} se anima a la picada ${aimed}`, `${K} frena la carrera y levanta la pelota con delicadeza ${aimed}`, `¡Panenka! ${K} se la juega con un toque suave ${aimed}`])
    : kick.type === 'fuerte' ? pick(rng, [`${K} toma carrera y le pega con todo ${aimed}`, `${K} la patea con furia ${aimed}`, `Zapatazo de ${K} ${aimed}`])
    : pick(rng, [`${K} define con calma ${aimed}`, `${K} la acomoda con el borde interno ${aimed}`, `${K} la coloca ${aimed}`]);
  let out;
  if (result === 'goal') {
    if (kick.type === 'picada') out = pick(rng, [`¡GOOOL! ¡Qué personalidad! ${dTxt} y la pelota entra suave, descolgada.`, `¡Gol! La picada que enloquece a todos. ${dTxt}.`]);
    else if (rec.guess) out = pick(rng, [`¡GOOOL! ${G} llegó a tocarla pero no alcanzó. ¡Está adentro!`, `¡Gol! ${G} casi la saca, pero tenía demasiada violencia.`, `¡Adentro! Rozó los guantes de ${G} y se metió.`]);
    else out = pick(rng, [`¡GOOOL! ${dTxt}. No había nada que hacer.`, `¡Gol, gol, gol! ${dTxt} y la red se infla.`, `Adentro. ${dTxt}; el arquero la vio pasar.`]);
  } else if (result === 'save') {
    if (kick.type === 'picada') out = pick(rng, [`¡Y ${G} no se la cree! La picada terminó en sus manos. ¡Qué papelón!`, `¡Atajó ${G}! Se quedó esperando la picada y la abrazó.`]);
    else out = pick(rng, [`¡ATAJÓ ${G}! ¡Tapó con la mano de abajo!`, `¡Se la sacó ${G}! ¡Adivinó y la desvió!`, `¡Qué atajada! ${G} se estira y la manda al córner. ¡Increíble!`]);
  } else if (result === 'post') out = pick(rng, [`¡AL PALO! ¡Pegó en el palo y salió! ¡Increíble!`, `¡El palo! ¡Cuánta mala suerte! La pelota vuelve al campo.`]);
  else if (result === 'bar') out = pick(rng, [`¡AL TRAVESAÑO! ¡Casi la rompe! Se va desviada.`, `¡Travesaño! La pelota pega arriba y se va... ¡afuera!`]);
  else out = rec.mishit ? pick(rng, [`¡Le pegó mal! La pelota se fue muy lejos del arco.`, `¡Mal impacto! Se le escapó y se fue ${where.includes('arriba') ? 'por arriba' : 'afuera'}.`]) : pick(rng, [`¡Y la tiró afuera! La buscó demasiado cerca del palo.`, `¡Se fue desviada! Nadie lo puede creer.`, `¡Afuera! La pelota pasó lejos del palo.`]);
  return `${run}. ${out}`;
}
function narrateEnd(rng, sh, names) {
  const w = sh.winner, a = sh.sc[w], b = sh.sc[1 - w];
  return pick(rng, [`¡Se terminó! ${names[w]} se queda con la tanda ${a} a ${b}.`, `¡Final! ${names[w]} gana ${a} a ${b} y lo festeja con todo.`]);
}

const Engine = { PHYS, SIDES, TYPES, DIVES, ZONES, GW, GH, PX, KICK, MORALE, mulberry32, shuffle, pick, clamp, shrink, calibrate, dataSide, physSide, physOf, perksOf, ovr, kickerRate, keeperStop,
  modifiers, kickParams, keeperParams, savep, classify, cellStats, resolveKick, Shootout, payoffMatrix, solve, aiKick, aiDive, aiOrder, options, placeText,
  newDraft, startDraft, turn, applyPick, legalPicks, feasible, AU, THEMES, auThemesFor, auClues, auNew, auStart, auElig, auMax, auNext, auBid, auPass, auDrop, auTick, auAIInit, auAIStep, auAIMax, VT, vtPrice, vtNew, vtStart, vtTurn, vtLegal, vtApply, vtAI, vtVal, vtFirst, narratePre, narrateKick, narrateEnd, get GS() { return GS; }, get GKS() { return GKS; } };
if (typeof module !== 'undefined' && module.exports) module.exports = Engine; else root.Engine = Engine;
})(typeof window !== 'undefined' ? window : globalThis);
