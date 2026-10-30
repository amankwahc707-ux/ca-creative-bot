/* C.A. Creative Bot — created and owned by Charles Amankwah */

// ===================== CONSTANTS =====================
const API = "https://api.hyperliquid.xyz/info";
const WS_URL = "wss://api.hyperliquid.xyz/ws";
const IV_MS = { "1m": 60000, "5m": 300000, "15m": 900000, "1h": 3600000, "4h": 14400000, "1d": 86400000 };
const HIP3_DEX = "xyz";
const STOCKS = ["NVDA","TSLA","AAPL","MSFT","GOOGL","AMZN","META","PLTR"];
const COMMODITIES = ["GOLD","SILVER","BRENTOIL"];
const MIN_CRYPTO_VOL = 2_000_000;
const TOP_N_CRYPTO = 20;
const SCAN_INTERVAL = 90_000;
const CANDLE_CACHE_MS = 90_000;
const STATE_POLL_MS = 2_000;
const MAINT_FRAC = 0.9;

const $ = id => document.getElementById(id);
const fmt = x => x == null ? "—" : (x >= 1000 ? Number(x).toLocaleString(undefined,{maximumFractionDigits:2}) : Number(x).toPrecision(6)).toString();
const fmt2 = x => x == null ? "—" : Number(x).toLocaleString(undefined,{minimumFractionDigits:2,maximumFractionDigits:2});
const esc = s => String(s).replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;","'":"&#39;"}[c]));

// ===================== STORAGE =====================
const store = {
  getTrades: () => { try { return JSON.parse(localStorage.getItem("legend_trades") || "[]"); } catch { return []; } },
  setTrades: t => localStorage.setItem("legend_trades", JSON.stringify(t)),
  getCap: () => parseFloat($("capital").value) || 10000,
  getLastSignals: () => { try { return JSON.parse(localStorage.getItem("legend_last_signals") || "{}"); } catch { return {}; } },
  setLastSignals: m => localStorage.setItem("legend_last_signals", JSON.stringify(m)),
  getLastConf: () => { try { return JSON.parse(localStorage.getItem("legend_last_confidence") || "{}"); } catch { return {}; } },
  setLastConf: m => localStorage.setItem("legend_last_confidence", JSON.stringify(m)),
  getBtLast: () => { try { return JSON.parse(localStorage.getItem("legend_backtest_last") || "null"); } catch { return null; } },
  setBtLast: x => localStorage.setItem("legend_backtest_last", JSON.stringify(x)),
  getBtBatch: () => { try { return JSON.parse(localStorage.getItem("legend_backtest_batch") || "[]"); } catch { return []; } },
  setBtBatch: x => localStorage.setItem("legend_backtest_batch", JSON.stringify(x)),
};

// ===================== STATE =====================
const STATE = { status: "starting", lastScan: null, error: null, mids: {}, coins: {}, watchlist: [] };
let currentCoin = null, currentIv = "5m", assetFilter = "ALL";
let chart, candleSeries, ema20S, ema50S, ema200S;
let lastBars = [], lastBarTime = 0;
let priceLines = []; // {line, trade, field}
let dragState = { active: false, line: null, trade: null, field: null };

// ===================== INDICATORS =====================
function ema(vals, n) {
  if (vals.length < n) return null;
  const k = 2 / (n + 1);
  let e = vals.slice(0, n).reduce((a, b) => a + b, 0) / n;
  for (let i = n; i < vals.length; i++) e = vals[i] * k + e * (1 - k);
  return e;
}
function emaSeries(vals, n) {
  if (vals.length < n) return [];
  const k = 2 / (n + 1);
  let e = vals.slice(0, n).reduce((a, b) => a + b, 0) / n;
  const out = [e];
  for (let i = n; i < vals.length; i++) { e = vals[i] * k + e * (1 - k); out.push(e); }
  return out;
}
function wilderLast(vals, n) {
  if (vals.length < n) return null;
  let a = vals.slice(0, n).reduce((x, y) => x + y, 0) / n;
  for (let i = n; i < vals.length; i++) a = (a * (n - 1) + vals[i]) / n;
  return a;
}
function wilderSeries(vals, n) {
  if (vals.length < n) return [];
  let a = vals.slice(0, n).reduce((x, y) => x + y, 0) / n;
  const out = [a];
  for (let i = n; i < vals.length; i++) { a = (a * (n - 1) + vals[i]) / n; out.push(a); }
  return out;
}
function rsi(cs, n = 14) {
  if (cs.length <= n + 1) return null;
  const g = [], l = [];
  for (let i = 1; i < cs.length; i++) {
    g.push(Math.max(cs[i] - cs[i - 1], 0));
    l.push(Math.max(cs[i - 1] - cs[i], 0));
  }
  const ag = wilderLast(g, n), al = wilderLast(l, n);
  if (ag == null || al == null) return null;
  return al === 0 ? 100 : 100 - 100 / (1 + ag / al);
}
function atr(cs, n = 14) {
  if (cs.length <= n) return null;
  const trs = [];
  for (let i = 1; i < cs.length; i++) {
    trs.push(Math.max(cs[i].h - cs[i].l, Math.abs(cs[i].h - cs[i-1].c), Math.abs(cs[i].l - cs[i-1].c)));
  }
  return wilderLast(trs, n);
}
function adx(cs, n = 14) {
  if (cs.length < 2 * n + 1) return { adx: null, pdi: null, mdi: null };
  const pdm = [], mdm = [], trs = [];
  for (let i = 1; i < cs.length; i++) {
    const up = cs[i].h - cs[i-1].h, dn = cs[i-1].l - cs[i].l;
    pdm.push(up > dn && up > 0 ? up : 0);
    mdm.push(dn > up && dn > 0 ? dn : 0);
    trs.push(Math.max(cs[i].h - cs[i].l, Math.abs(cs[i].h - cs[i-1].c), Math.abs(cs[i].l - cs[i-1].c)));
  }
  const st = wilderSeries(trs, n), sp = wilderSeries(pdm, n), sm = wilderSeries(mdm, n);
  if (!st.length) return { adx: null, pdi: null, mdi: null };
  const dx = [];
  let lp = 0, lm = 0;
  for (let i = 0; i < st.length; i++) {
    if (st[i] === 0) { dx.push(0); continue; }
    lp = 100 * sp[i] / st[i]; lm = 100 * sm[i] / st[i];
    dx.push((lp + lm) === 0 ? 0 : 100 * Math.abs(lp - lm) / (lp + lm));
  }
  const as = wilderSeries(dx, n);
  return { adx: as.length ? as[as.length - 1] : null, pdi: lp, mdi: lm };
}
function volRatio(cs) {
  if (cs.length < 12) return 1;
  const recent = cs.slice(-6).map(c => c.v);
  const base = cs.length >= 72 ? cs.slice(-72, -6).map(c => c.v) : cs.slice(0, -6).map(c => c.v);
  const mR = recent.reduce((a,b)=>a+b,0)/recent.length;
  const mB = base.reduce((a,b)=>a+b,0)/Math.max(base.length, 1);
  return mB > 0 ? mR / mB : 1;
}

// ===================== CANDLE FETCHING =====================
const candleCache = new Map();
async function fetchCandles(coin, interval, lookback = 320, dex = "", retries = 3) {
  const step = IV_MS[interval];
  const end = Date.now();
  const start = end - step * (lookback + 2);
  const payload = { type: "candleSnapshot", req: { coin, interval, startTime: start, endTime: end } };
  if (dex) payload.dex = dex;
  let lastErr = null;
  for (let i = 0; i < retries; i++) {
    try {
      const r = await fetch(API, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(payload) });
      if (r.status === 429) { await new Promise(x => setTimeout(x, 2000 * (i + 1))); lastErr = "429"; continue; }
      if (!r.ok) throw new Error("HTTP " + r.status);
      const data = await r.json();
      return data.map(c => ({ t: c.t, T: c.T, o: +c.o, h: +c.h, l: +c.l, c: +c.c, v: +c.v }));
    } catch (e) {
      lastErr = e.message || String(e);
      if (i < retries - 1) await new Promise(x => setTimeout(x, 1500 * (i + 1)));
    }
  }
  throw new Error("candles failed: " + lastErr);
}
async function getCandles(coin, interval, lookback = 320, dex = "") {
  const key = `${coin}|${interval}|${dex}`;
  const hit = candleCache.get(key);
  if (hit && Date.now() - hit.ts < CANDLE_CACHE_MS) return hit.data;
  try {
    const data = await fetchCandles(coin, interval, lookback, dex);
    candleCache.set(key, { ts: Date.now(), data });
    return data;
  } catch (e) {
    if (hit) return hit.data;
    throw e;
  }
}

// ===================== UNIVERSE =====================
async function fetchMeta(dex = "") {
  const payload = { type: "metaAndAssetCtxs" };
  if (dex) payload.dex = dex;
  const r = await fetch(API, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(payload) });
  if (!r.ok) throw new Error("meta HTTP " + r.status);
  const data = await r.json();
  const universe = data[0].universe, ctxs = data[1];
  const out = [];
  for (let i = 0; i < universe.length; i++) {
    const m = universe[i], c = ctxs[i];
    if (!m || m.isDelisted) continue;
    out.push({
      raw: m.name,
      coin: dex ? `${dex}:${m.name}` : m.name,
      dex,
      maxLev: parseInt(m.maxLeverage || 3),
      vol: parseFloat(c.dayNtlVlm || 0),
      funding: parseFloat(c.funding || 0),
      markPx: parseFloat(c.markPx || 0),
    });
  }
  return out;
}

// ===================== SIGNAL ENGINE =====================
function tf(candles, livePrice) {
  if (!candles || candles.length < 10) return null;
  const cs = candles.map(c => ({ ...c }));
  const last = cs[cs.length - 1];
  if (livePrice > 0) { last.c = livePrice; last.h = Math.max(last.h, livePrice); last.l = Math.min(last.l, livePrice); }
  const closes = cs.map(c => c.c);
  return {
    candles: cs, closes,
    e20: ema(closes, 20), e50: ema(closes, 50), e200: ema(closes, 200),
    e20s: emaSeries(closes, 20), e50s: emaSeries(closes, 50),
    rsi: rsi(closes), atr: atr(cs), adx: adx(cs).adx, price: livePrice || closes[closes.length - 1],
  };
}

function trendOf(t) {
  if (!t || t.e20 == null || t.e50 == null) return "FLAT";
  const up = t.e20 > t.e50 && (t.e200 == null || t.e50 > t.e200) && t.price > t.e50;
  const dn = t.e20 < t.e50 && (t.e200 == null || t.e50 < t.e200) && t.price < t.e50;
  // 5-bar sustain: check last 5 completed bars
  if (t.e20s.length >= 6 && t.e50s.length >= 6) {
    let allUp = true, allDn = true;
    for (let i = t.e20s.length - 6; i < t.e20s.length - 1; i++) {
      const c = t.closes[i + (t.closes.length - t.e20s.length)];
      if (!(t.e20s[i] > t.e50s[i] && c > t.e50s[i])) allUp = false;
      if (!(t.e20s[i] < t.e50s[i] && c < t.e50s[i])) allDn = false;
    }
    // fresh cross check
    let freshCross = false;
    for (let i = Math.max(1, t.e20s.length - 6); i < t.e20s.length; i++) {
      const prev = t.e20s[i-1] - t.e50s[i-1];
      const cur = t.e20s[i] - t.e50s[i];
      if (prev * cur < 0) { freshCross = true; break; }
    }
    if (freshCross) return "FLAT";
    if (up && allUp) return "UP";
    if (dn && allDn) return "DOWN";
  }
  return "FLAT";
}

function computeBullScore(T, price, adx5, volR, setupQualified, momentumOk) {
  let s = 0;
  if (T["4h"] && T["4h"].trend === "UP") s += 20;
  if (T["1h"] && T["1h"].trend === "UP") s += 20;
  if (T["15m"] && T["15m"].trend === "UP") s += 10;
  if (adx5 >= 35) s += 15; else if (adx5 >= 30) s += 10; else if (adx5 >= 25) s += 5;
  if (volR >= 1.8) s += 15; else if (volR >= 1.5) s += 10; else if (volR >= 1.2) s += 5;
  if (setupQualified) s += 10;
  if (momentumOk) s += 10;
  if (T["1d"] && T["1d"].trend === "UP") s += 10;
  return Math.min(100, s);
}

function computeBearScore(T, price, atr5, adx5, volR, rsi5, rsi1h) {
  let s = 0;
  const t1 = T["1h"], t4 = T["4h"], t5 = T["5m"];
  if (t1 && t1.trend === "DOWN") s += 25;
  else if (t1 && t1.e50 && price < t1.e50) s += 15;
  if (t4 && t4.trend === "DOWN") s += 20;
  if (t5 && t5.trend === "DOWN") s += 8;
  if (adx5 >= 30) s += 22; else if (adx5 >= 25) s += 18; else if (adx5 < 15) s -= 8;
  if (volR >= 1.5) s += 12; else if (volR >= 1.2) s += 7;
  if (rsi5 < 30) s += 12; else if (rsi5 < 40) s += 8; else if (rsi5 < 45) s += 4; else if (rsi5 > 55) s -= 8;
  if (t1 && t1.e50 && atr5 > 0) {
    const d = (price - t1.e50) / atr5;
    if (d < -2) s += 10; else if (d < -1) s += 5;
  }
  return Math.max(0, Math.min(100, s));
}

function signalFrom(candlesByTf, livePrice) {
  if (!candlesByTf["5m"] || !candlesByTf["1h"] || !candlesByTf["4h"]) return null;
  const T = {};
  for (const iv of ["5m","15m","1h","4h","1d"]) {
    if (!candlesByTf[iv]) continue;
    const t = tf(candlesByTf[iv], livePrice);
    if (t) { t.trend = trendOf(t); T[iv] = t; }
  }
  if (!T["5m"] || !T["1h"] || !T["4h"]) return null;
  const price = T["5m"].price;
  if (!price || price <= 0) return null;
  const a5 = T["5m"].atr || 0;
  if (a5 <= 0) return null;
  const rsi5 = T["5m"].rsi, rsi1 = T["1h"].rsi;
  const adx5 = T["5m"].adx, adx15 = T["15m"] ? T["15m"].adx : null, adx1 = T["1h"].adx;
  const volR = volRatio(T["5m"].candles);

  // ============ SELL branch ============
  const anyUptrend = T["4h"].trend === "UP" && T["1h"].trend === "UP";
  if (!anyUptrend) {
    const bear = computeBearScore(T, price, a5, adx5 || 0, volR, rsi5 || 50, rsi1 || 50);
    const sellGates = [
      { name: "1h DOWN or price<1h EMA50", pass: T["1h"].trend === "DOWN" || (T["1h"].e50 && price < T["1h"].e50) },
      { name: "4h EMA20<EMA50 or price<4h EMA50", pass: (T["4h"].e20 && T["4h"].e20 < T["4h"].e50) || (T["4h"].e50 && price < T["4h"].e50) },
      { name: "ADX(5m) ≥ 28", pass: adx5 != null && adx5 >= 28 },
      { name: "Bear score ≥ 65", pass: bear >= 65 },
      { name: "Volume ratio ≥ 1.2", pass: volR >= 1.2 },
      { name: "Momentum: last 3 5m closes not ascending", pass: (() => {
          const closes = T["5m"].closes;
          if (closes.length < 4) return false;
          return !(closes[closes.length-2] > closes[closes.length-3] && closes[closes.length-3] > closes[closes.length-4]);
        })() },
      { name: "RSI(1h) > 28", pass: rsi1 != null && rsi1 > 28 },
    ];
    const gatesPassed = sellGates.filter(g => g.pass).length;
    const allPass = gatesPassed === sellGates.length;
    const conflicts = [];
    if (allPass && rsi1 != null && rsi1 < 25) conflicts.push("RSI(1h) < 25");
    if (allPass && T["1h"].e50 && a5 > 0 && price < T["1h"].e50 - 6 * a5) conflicts.push("price >6 ATR below 1h EMA50");
    if (allPass && adx1 != null && adx1 < 15) conflicts.push("ADX(1h) < 15");
    const tfT = [T["1d"]?.trend, T["4h"].trend, T["1h"].trend].filter(x => x && x !== "FLAT");
    if (tfT.length >= 2 && new Set(tfT).size >= 2) conflicts.push("higher timeframes disagree");

    // Soft confirmations for SELL
    const soft = [
      T["1d"]?.trend === "DOWN",
      adx5 != null && adx5 >= 35,
      adx1 != null && adx1 >= 25,
      volR >= 1.7,
      rsi5 != null && rsi5 >= 55 && rsi5 <= 65,
      T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 < 2,
      rsi1 != null && rsi1 >= 45 && rsi1 <= 65,
      T["1d"]?.e50 && T["4h"].e50 && T["1h"].e50 && T["15m"]?.e50 && T["5m"].e50 &&
        price < T["1d"].e50 && price < T["4h"].e50 && price < T["1h"].e50 && price < T["15m"].e50 && price < T["5m"].e50,
    ].filter(Boolean).length;

    if (allPass && conflicts.length === 0 && soft >= 4) {
      const tier = soft >= 6 ? "CERTAIN" : "CONFIDENT";
      const stop = price * 1.03, tp2 = price * 0.97;
      const why = `Why SELL: ${sellGates.map(g => g.name).join("; ")}. Bear score ${bear}. Vol ${volR.toFixed(1)}x. RSI(1h) ${rsi1?.toFixed(0)}. ADX(1h) ${adx1?.toFixed(0)}.`;
      return { signal: "SELL", confidence: tier, score: bear, price, stop, tp2, why,
               gatesPassed, gatesTotal: sellGates.length, soft, trend: T };
    }
    const failed = sellGates.filter(g => !g.pass).map(g => g.name);
    const why = `Why NEUTRAL: ${failed.length ? "gates failed: " + failed.join("; ") : "insufficient soft confirmations"}. ` +
                `Soft ${soft}/8. ` + (conflicts.length ? "Conflicts: " + conflicts.join("; ") + ". " : "") +
                `Not enough evidence for a signal.`;
    return { signal: "NEUTRAL", confidence: "LOW", score: bear, price, why, gatesPassed, gatesTotal: sellGates.length, soft, trend: T };
  }

  // ============ BUY branch ============
  const t5c = T["5m"].candles;
  const e20_5 = T["5m"].e20;
  const distEma = e20_5 ? (price - e20_5) / a5 : 0;
  const recentHigh = t5c.length >= 21 ? Math.max(...t5c.slice(-21, -1).map(c => c.h)) : price;

  // 5m setup pullback: bounce off EMA20 within last 3 completed 5m candles
  const bounced = (() => {
    if (!e20_5 || t5c.length < 4) return false;
    for (let i = t5c.length - 4; i < t5c.length - 1; i++) {
      const c = t5c[i];
      if (c.l <= e20_5 * 1.002 && c.c > e20_5) return true;
    }
    return false;
  })();
  const pullbackOk = distEma >= -0.4 && distEma <= 0.15 && rsi5 != null && rsi5 >= 52 && rsi5 <= 62 && bounced;

  // 5m breakout: completed candle above 20-bar high within last 3 bars with volume >= 1.5
  const breakoutOk = (() => {
    if (t5c.length < 24) return false;
    for (let i = t5c.length - 4; i < t5c.length - 1; i++) {
      const high20 = Math.max(...t5c.slice(i - 20, i).map(c => c.h));
      const barVol = t5c[i].v;
      const base = t5c.slice(Math.max(0, i - 72), Math.max(1, i - 6));
      const baseAvg = base.length ? base.reduce((s, c) => s + c.v, 0) / base.length : barVol;
      if (t5c[i].c > high20 && baseAvg > 0 && barVol / baseAvg >= 1.5) return true;
    }
    return false;
  })();
  const setupOk = pullbackOk || breakoutOk;

  const momentumOk = (() => {
    const cs = T["5m"].closes;
    if (cs.length < 4) return false;
    return !(cs[cs.length-2] < cs[cs.length-3] && cs[cs.length-3] < cs[cs.length-4]);
  })();

  const gates = [
    { name: "1d UP or near 1d EMA50", pass: T["1d"] ? (T["1d"].trend === "UP" || (T["1d"].e50 && a5 > 0 && Math.abs(price - T["1d"].e50) / a5 < 3)) : true },
    { name: "4h UP", pass: T["4h"].trend === "UP" },
    { name: "1h UP", pass: T["1h"].trend === "UP" },
    { name: "15m UP", pass: T["15m"] ? T["15m"].trend === "UP" : false },
    { name: "price>4h & 1h EMA50", pass: T["4h"].e50 && T["1h"].e50 && price > T["4h"].e50 && price > T["1h"].e50 },
    { name: "5m setup (pullback or breakout)", pass: setupOk },
    { name: "ADX(5m) ≥ 30", pass: adx5 != null && adx5 >= 30 },
    { name: "ADX(15m) ≥ 22", pass: adx15 != null && adx15 >= 22 },
    { name: "Volume ratio ≥ 1.4", pass: volR >= 1.4 },
    { name: "Momentum confirmation", pass: momentumOk },
    { name: "RSI(1h) < 72", pass: rsi1 != null && rsi1 < 72 },
    { name: "Distance from 1h EMA50 ≤ 4 ATR", pass: T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 <= 4 },
  ];
  const gatesPassed = gates.filter(g => g.pass).length;
  const bullScore = computeBullScore(T, price, adx5 || 0, volR, setupOk, momentumOk);
  const scoreGate = bullScore >= 92;
  if (scoreGate) gates.push({ name: "Composite score ≥ 92", pass: true });

  const soft = [
    T["1d"]?.trend === "UP",
    adx5 != null && adx5 >= 35,
    adx1 != null && adx1 >= 25,
    volR >= 1.7,
    rsi5 != null && rsi5 >= 55 && rsi5 <= 65,
    T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 < 2,
    rsi1 != null && rsi1 >= 45 && rsi1 <= 65,
    T["1d"]?.e50 && T["4h"].e50 && T["1h"].e50 && T["15m"]?.e50 && T["5m"].e50 &&
      price > T["1d"].e50 && price > T["4h"].e50 && price > T["1h"].e50 && price > T["15m"].e50 && price > T["5m"].e50,
  ].filter(Boolean).length;

  const conflicts = [];
  if (rsi1 != null && rsi1 > 75) conflicts.push("RSI(1h) > 75");
  if (T["1h"].e50 && a5 > 0 && price > T["1h"].e50 + 6 * a5) conflicts.push("chasing: price >6 ATR above 1h EMA50");
  if (adx1 != null && adx1 < 15) conflicts.push("ADX(1h) < 15");
  const tfT = [T["1d"]?.trend, T["4h"].trend, T["1h"].trend].filter(x => x && x !== "FLAT");
  if (tfT.length >= 2 && new Set(tfT).size >= 2) conflicts.push("higher timeframes disagree");

  const allPass = gatesPassed === gates.length;

  if (allPass && conflicts.length === 0 && soft >= 4) {
    const swingLow = Math.min(...t5c.slice(-12).map(c => c.l));
    let stop = Math.min(swingLow - 0.2 * a5, price - 1.5 * a5);
    stop = Math.max(stop, price - 3 * a5);
    const risk = price - stop;
    const tp1 = price + 2 * risk, tp2 = price + 3 * risk;
    const tier = soft >= 6 ? "CERTAIN" : "CONFIDENT";
    const setupName = pullbackOk ? "pullback to EMA20 support" : "breakout above 20-bar high";
    const why = `Why BUY: All ${gates.length} gates passed. ${setupName} on 5m. ` +
                `1d${T["1d"]?.trend || "?"} 4hUP 1hUP 15mUP. ADX(5m) ${adx5?.toFixed(0)}. Vol ${volR.toFixed(1)}x. ` +
                `RSI(5m) ${rsi5?.toFixed(0)} RSI(1h) ${rsi1?.toFixed(0)}. Stop ${fmt(stop)} TP2 ${fmt(tp2)}. Soft ${soft}/8.`;
    return { signal: "BUY", confidence: tier, score: bullScore, price, entry: price, stop, tp1, tp2,
             why, gatesPassed, gatesTotal: gates.length, soft, trend: T };
  }

  if (bullScore >= 65 && gatesPassed >= gates.length - 3 && conflicts.length === 0) {
    const failed = gates.filter(g => !g.pass).map(g => g.name);
    const why = `Why WAIT: uptrends confirmed but entry not triggered. Missing: ${failed.join("; ")}. Soft ${soft}/8.`;
    const entryZone = e20_5 ? e20_5 - 0.25 * a5 : price;
    return { signal: "WAIT", confidence: "MED", score: bullScore, price, entryZone,
             why, gatesPassed, gatesTotal: gates.length, soft, trend: T };
  }

  const failed = gates.filter(g => !g.pass).map(g => g.name);
  const why = `Why NEUTRAL: ${failed.length ? "gates failed: " + failed.slice(0,3).join("; ") : "low confidence"}. ` +
              `Score ${bullScore}, soft ${soft}/8. ` + (conflicts.length ? "Conflicts: " + conflicts.join("; ") + ". " : "") +
              `Not enough evidence.`;
  return { signal: "NEUTRAL", confidence: "LOW", score: bullScore, price, why, gatesPassed, gatesTotal: gates.length, soft, trend: T };
}

// ===================== SCAN LOOP =====================
async function buildUniverse() {
  const list = [];
  try {
    const crypto = await fetchMeta("");
    crypto.sort((a, b) => b.vol - a.vol);
    const top = crypto.filter(m => m.vol > MIN_CRYPTO_VOL).slice(0, TOP_N_CRYPTO);
    for (const m of top) list.push({ ...m, assetClass: "CRYPTO" });
  } catch (e) { console.error("crypto universe:", e); }
  try {
    const hip = await fetchMeta(HIP3_DEX);
    for (const m of hip) {
      if (STOCKS.includes(m.raw)) list.push({ ...m, assetClass: "STOCK" });
      else if (COMMODITIES.includes(m.raw)) list.push({ ...m, assetClass: "COMMODITY" });
    }
  } catch (e) { console.error("hip3 universe:", e); }
  return list;
}

let scanRunning = false;
async function runScan() {
  if (scanRunning) return;
  scanRunning = true;
  STATE.status = "scanning";
  render();
  try {
    const universe = await buildUniverse();
    const results = {};
    // concurrency 10
    const queue = [...universe];
    const total = queue.length;
    let done = 0;
    async function worker() {
      while (queue.length) {
        const m = queue.shift();
        try {
          const candles = {};
          await Promise.all(["5m","15m","1h","4h","1d"].map(async iv => {
            try { candles[iv] = await getCandles(m.raw, iv, 320, m.dex); } catch(e) {}
          }));
          const live = parseFloat(STATE.mids[m.coin] || 0) || m.markPx;
          const sig = signalFrom(candles, live);
          if (sig) {
            sig.coin = m.coin;
            sig.assetClass = m.assetClass;
            sig.dex = m.dex;
            results[m.coin] = sig;
          }
        } catch(e) { console.error("scan " + m.coin, e); }
        done++;
        STATE.status = `scanning ${done}/${total}`;
      }
    }
    await Promise.all(Array(10).fill(0).map(() => worker()));
    const order = { BUY:0, WAIT:1, SELL:2, NEUTRAL:3 };
    const sorted = Object.values(results).sort((a,b) =>
      (order[a.signal]||9) - (order[b.signal]||9) || (b.score||0) - (a.score||0));
    STATE.coins = results;
    STATE.watchlist = sorted.map(c => c.coin);
    STATE.lastScan = Date.now();
    STATE.status = "live";
    STATE.error = null;
    checkSignalTransitions(sorted);
  } catch (e) {
    STATE.error = String(e); STATE.status = "error";
    console.error("scan error:", e);
  }
  scanRunning = false;
  render();
}

// ===================== WEBSOCKET =====================
let ws, wsRetry = null;
function connectWS() {
  try {
    ws = new WebSocket(WS_URL);
    ws.onopen = () => ws.send(JSON.stringify({ method: "subscribe", subscription: { type: "allMids" } }));
    ws.onmessage = (ev) => {
      try {
        const m = JSON.parse(ev.data);
        if (m.channel === "allMids") STATE.mids = m.data.mids || {};
      } catch(e) {}
    };
    ws.onclose = () => { wsRetry = setTimeout(connectWS, 3000); };
    ws.onerror = () => {};
  } catch(e) { wsRetry = setTimeout(connectWS, 5000); }
}

// ===================== CHART =====================
function initChart() {
  const el = $("chart");
  el.innerHTML = "";
  chart = LightweightCharts.createChart(el, {
    layout: { background: { color: "#171b24" }, textColor: "#e8ebf2", fontSize: 11 },
    grid: { vertLines: { color: "#262c38" }, horzLines: { color: "#262c38" } },
    timeScale: { timeVisible: true, secondsVisible: false, borderColor: "#262c38" },
    rightPriceScale: { borderColor: "#262c38" },
    crosshair: { mode: 0 },
    handleScroll: true, handleScale: true,
  });
  candleSeries = chart.addCandlestickSeries({
    upColor: "#2ecc83", downColor: "#ff5d68", borderVisible: false,
    wickUpColor: "#2ecc83", wickDownColor: "#ff5d68",
  });
  ema20S = chart.addLineSeries({ color: "#4ea8ff", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  ema50S = chart.addLineSeries({ color: "#f0b429", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  ema200S = chart.addLineSeries({ color: "#8b93a1", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  new ResizeObserver(() => {
    if (chart) chart.applyOptions({ width: el.clientWidth, height: el.clientHeight });
  }).observe(el);
  attachDragHandlers(el);
}

function toBars(cs) { return cs.map(c => ({ time: Math.floor(c.t/1000), open: c.o, high: c.h, low: c.l, close: c.c })); }
function buildEmaSeries(arr, offset, stepMs) {
  const bars = lastBars;
  if (!bars.length || !arr.length) return [];
  const t0 = bars[0].time;
  return arr.map((v, i) => ({ time: t0 + Math.round((offset + i) * (stepMs/1000)), value: v }));
}

async function loadCandles(coin, iv) {
  if (!coin || !chart) return;
  try {
    const meta = STATE.coins[coin] || {};
    const raw = coin.includes(":") ? coin.split(":")[1] : coin;
    const dex = meta.dex || "";
    const data = await getCandles(raw, iv, 320, dex);
    if (!data.length) return;
    lastBars = toBars(data);
    lastBarTime = lastBars[lastBars.length-1].time;
    candleSeries.setData(lastBars);
    const closes = data.map(c => c.c);
    const e20 = emaSeries(closes, 20), e50 = emaSeries(closes, 50), e200 = emaSeries(closes, 200);
    const stepMs = IV_MS[iv];
    ema20S.setData(buildEmaSeries(e20, 19, stepMs));
    ema50S.setData(buildEmaSeries(e50, 49, stepMs));
    ema200S.setData(buildEmaSeries(e200, 199, stepMs));
    chart.timeScale().fitContent();
    drawPriceLines(coin);
  } catch(e) { console.error("loadCandles:", e); }
}

function updateFormingBar(live) {
  if (!lastBars.length || !live || !chart) return;
  const step = IV_MS[currentIv];
  const expected = Math.floor(Date.now() / step) * step / 1000;
  if (expected > lastBarTime) { loadCandles(currentCoin, currentIv); return; }
  const last = lastBars[lastBars.length-1];
  last.close = live;
  last.high = Math.max(last.high, live);
  last.low = Math.min(last.low, live);
  candleSeries.update(last);
}

// ===================== DRAGGABLE PRICE LINES =====================
function drawPriceLines(coin) {
  priceLines.forEach(p => { try { candleSeries.removePriceLine(p.line); } catch(e) {} });
  priceLines = [];
  if (!coin || !candleSeries) return;
  const open = store.getTrades().filter(t => !t.closed_at && t.coin === coin);
  for (const t of open) {
    try {
      const entryLine = candleSeries.createPriceLine({
        price: t.entry, color: "#4ea8ff", lineWidth: 1,
        lineStyle: LightweightCharts.LineStyle.Solid,
        axisLabelVisible: true, title: (t.side || "LONG") + " entry",
      });
      const stopLine = candleSeries.createPriceLine({
        price: t.stop, color: "#ff5d68", lineWidth: 2,
        lineStyle: LightweightCharts.LineStyle.Dashed,
        axisLabelVisible: true, title: "Stop (drag)",
      });
      const tpLine = candleSeries.createPriceLine({
        price: t.tp2, color: "#2ecc83", lineWidth: 2,
        lineStyle: LightweightCharts.LineStyle.Dashed,
        axisLabelVisible: true, title: "TP2 (drag)",
      });
      priceLines.push({ line: entryLine, trade: t, field: null });
      priceLines.push({ line: stopLine, trade: t, field: "stop" });
      priceLines.push({ line: tpLine, trade: t, field: "tp2" });
    } catch(e) {}
  }
}

function attachDragHandlers(el) {
  const getXY = (ev) => {
    if (ev.touches && ev.touches.length) return { x: ev.touches[0].clientX, y: ev.touches[0].clientY };
    return { x: ev.clientX, y: ev.clientY };
  };
  const onDown = (ev) => {
    if (!chart || !candleSeries) return;
    const { y } = getXY(ev);
    const rect = el.getBoundingClientRect();
    const yRel = y - rect.top;
    const threshold = 12;
    let hit = null, bestDist = Infinity;
    for (const pl of priceLines) {
      if (!pl.field) continue;
      const py = candleSeries.priceToCoordinate(pl.line.options().price);
      if (py == null) continue;
      const d = Math.abs(py - yRel);
      if (d < threshold && d < bestDist) { hit = pl; bestDist = d; }
    }
    if (hit) {
      dragState = { active: true, line: hit.line, trade: hit.trade, field: hit.field };
      ev.preventDefault();
    }
  };
  const onMove = (ev) => {
    if (!dragState.active) return;
    const { y } = getXY(ev);
    const rect = el.getBoundingClientRect();
    const yRel = y - rect.top;
    const price = candleSeries.coordinateToPrice(yRel);
    if (price == null) return;
    const t = dragState.trade;
    const side = t.side || "LONG";
    // validate
    if (dragState.field === "stop") {
      if (side === "LONG" && price >= t.entry) return;
      if (side === "SHORT" && price <= t.entry) return;
    } else if (dragState.field === "tp2") {
      if (side === "LONG" && price <= t.entry) return;
      if (side === "SHORT" && price >= t.entry) return;
    }
    // tick snap: 3-4 sig figs
    const mag = Math.pow(10, Math.floor(Math.log10(price)) - 3);
    const snapped = Math.round(price / mag) * mag;
    try { dragState.line.applyOptions({ price: snapped }); } catch(e) {}
    t[dragState.field] = snapped;
    ev.preventDefault();
  };
  const onUp = () => {
    if (!dragState.active) return;
    const trades = store.getTrades();
    const idx = trades.findIndex(x => x.id === dragState.trade.id);
    if (idx >= 0) {
      const oldVal = trades[idx][dragState.field];
      const newVal = dragState.trade[dragState.field];
      if (oldVal !== newVal) {
        trades[idx][dragState.field] = newVal;
        trades[idx].adjustments = trades[idx].adjustments || [];
        trades[idx].adjustments.push({ at: Date.now(), field: dragState.field, from: oldVal, to: newVal });
        store.setTrades(trades);
        toast("BUY", `${dragState.trade.coin} ${dragState.field.toUpperCase()} → ${fmt(newVal)}`);
      }
    }
    dragState = { active: false, line: null, trade: null, field: null };
    render();
  };
  el.addEventListener("mousedown", onDown);
  el.addEventListener("mousemove", onMove);
  window.addEventListener("mouseup", onUp);
  el.addEventListener("touchstart", onDown, { passive: false });
  el.addEventListener("touchmove", onMove, { passive: false });
  window.addEventListener("touchend", onUp);
}

// ===================== TRADING =====================
function calcLiq(entry, lev, side) {
  const f = MAINT_FRAC / lev;
  return side === "LONG" ? entry * (1 - f) : entry * (1 + f);
}
function tradePnl(t, live) {
  const n = t.notional_usd, e = t.entry;
  return (t.side || "LONG") === "LONG" ? (live - e) / e * n : (e - live) / e * n;
}
function tradeMargin(t) { return t.margin_usd || (t.notional_usd / t.leverage); }

function executeTrade(side) {
  const coin = $("execCoin").value;
  if (!coin) return toast("ERR", "pick a coin");
  const meta = STATE.coins[coin];
  const live = parseFloat(STATE.mids[coin] || 0) || (meta ? meta.price : 0);
  if (!live) return toast("ERR", "no live price for " + coin);
  const margin = parseFloat($("execSize").value);
  const lev = Math.min(20, Math.max(1, parseFloat($("execLev").value) || 1));
  if (!margin || margin <= 0) return toast("ERR", "enter margin");
  const notional = margin * lev;
  const stopIn = parseFloat($("execStop").value);
  const tpIn = parseFloat($("execTP").value);
  let stop, tp2;
  if (side === "LONG") {
    stop = stopIn || (meta && meta.signal === "BUY" && meta.stop) || live * 0.97;
    tp2 = tpIn || (meta && meta.signal === "BUY" && meta.tp2) || live * 1.03;
    if (stop >= live) return toast("ERR", "LONG stop must be < price");
    if (tp2 <= live) return toast("ERR", "LONG TP must be > price");
  } else {
    stop = stopIn || live * 1.03;
    tp2 = tpIn || live * 0.97;
    if (stop <= live) return toast("ERR", "SHORT stop must be > price");
    if (tp2 >= live) return toast("ERR", "SHORT TP must be < price");
  }
  const trades = store.getTrades();
  trades.push({
    id: Date.now() + "-" + Math.random().toString(36).slice(2, 6),
    coin, side, entry: live, stop, tp1: (live + tp2) / 2, tp2,
    margin_usd: margin, notional_usd: notional, leverage: lev,
    opened_at: Date.now(), closed_at: null, close_price: null, close_reason: null,
    signal_at_open: meta ? meta.signal : null,
    confidence_at_open: meta ? meta.confidence : null,
    score_at_open: meta ? meta.score : null,
    why_at_open: meta ? meta.why : null,
    adjustments: [],
  });
  store.setTrades(trades);
  let warn = "";
  if (side === "LONG" && meta && meta.signal === "SELL") warn = " (against signal)";
  if (side === "SHORT" && meta && meta.signal === "BUY") warn = " (against signal)";
  toast(side === "LONG" ? "BUY" : "SELL", `${coin} ${side} $${notional.toFixed(0)} (margin $${margin.toFixed(0)} ${lev}x) @ ${fmt(live)}${warn}`);
  render();
}

function closeTrade(id, price, reason) {
  const trades = store.getTrades();
  const t = trades.find(x => x.id === id);
  if (!t || t.closed_at) return;
  t.closed_at = Date.now(); t.close_price = price; t.close_reason = reason;
  store.setTrades(trades);
  toast("SELL", `${t.coin} ${t.side} closed ${reason} @ ${fmt(price)}`);
}
function closeManual(id) {
  const trades = store.getTrades();
  const t = trades.find(x => x.id === id);
  if (!t) return;
  const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
  closeTrade(id, live, "manual");
  render();
}
function checkAutoClose() {
  const trades = store.getTrades();
  let changed = false;
  for (const t of trades) {
    if (t.closed_at) continue;
    const live = parseFloat(STATE.mids[t.coin] || 0);
    if (!live) continue;
    const side = t.side || "LONG";
    if (side === "LONG") {
      if (live <= t.stop) { closeTrade(t.id, t.stop, "stop"); changed = true; }
      else if (t.tp2 && live >= t.tp2) { closeTrade(t.id, t.tp2, "tp2"); changed = true; }
    } else {
      if (live >= t.stop) { closeTrade(t.id, t.stop, "stop"); changed = true; }
      else if (t.tp2 && live <= t.tp2) { closeTrade(t.id, t.tp2, "tp2"); changed = true; }
    }
  }
  if (changed) setTimeout(render, 50);
}
function clearAllTrades() {
  if (!confirm("Clear all paper trades and stats?")) return;
  store.setTrades([]);
  toast("ERR", "All trades cleared");
  render();
}

// ===================== MODAL =====================
function showTradeDetail(id) {
  const t = store.getTrades().find(x => x.id === id);
  if (!t) return;
  const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
  const side = t.side || "LONG";
  const margin = tradeMargin(t), notional = t.notional_usd;
  const pnl = tradePnl(t, live);
  const roe = margin > 0 ? (pnl / margin * 100) : 0;
  const liq = calcLiq(t.entry, t.leverage, side);
  const distLiq = Math.abs(live - liq) / live * 100;
  const stopDist = Math.abs(t.stop - t.entry) / t.entry * 100;
  const tp2Dist = Math.abs(t.tp2 - t.entry) / t.entry * 100;
  const openMs = t.opened_at ? (Date.now() - t.opened_at) : 0;
  const openH = openMs / 3600000;
  const openStr = openH < 1 ? `${(openH*60).toFixed(0)}m` : `${openH.toFixed(1)}h`;
  const riskUsd = side === "LONG" ? (t.entry - t.stop) / t.entry * notional : (t.stop - t.entry) / t.entry * notional;
  const rewardUsd = side === "LONG" ? (t.tp2 - t.entry) / t.entry * notional : (t.entry - t.tp2) / t.entry * notional;
  const rr = riskUsd > 0 ? rewardUsd / riskUsd : 0;
  const c = STATE.coins[t.coin];
  let html = `<h3 style="margin:0 0 6px">${esc(t.coin)} <span class="badge ${side}">${side}</span></h3>
    <div class="mu" style="margin-bottom:8px">${t.leverage}x leverage · ${openStr} open</div>
    <div class="detail-grid">
      <div><span class="k">Margin</span><span>$${margin.toFixed(2)}</span></div>
      <div><span class="k">Notional</span><span>$${notional.toFixed(2)}</span></div>
      <div><span class="k">Entry</span><span>${fmt(t.entry)}</span></div>
      <div><span class="k">Current</span><span>${fmt(live)}</span></div>
      <div><span class="k">Liquidation</span><span class="dn">${fmt(liq)}</span></div>
      <div><span class="k">Dist to liq</span><span>${distLiq.toFixed(2)}%</span></div>
      <div><span class="k">Risk at stop</span><span class="dn">$${riskUsd.toFixed(2)}</span></div>
      <div><span class="k">Reward at TP2</span><span class="up">$${rewardUsd.toFixed(2)}</span></div>
      <div><span class="k">R:R</span><span>1 : ${rr.toFixed(2)}</span></div>
      <div><span class="k">P/L</span><span class="${pnl>=0?'up':'dn'}">$${pnl.toFixed(2)}</span></div>
      <div><span class="k">ROE</span><span class="${pnl>=0?'up':'dn'}">${roe.toFixed(1)}%</span></div>
      <div><span class="k">Current signal</span><span>${c ? c.signal + " " + (c.confidence||"") : "—"}</span></div>
    </div>
    <div style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px;letter-spacing:.06em">Edit levels</div>
      <div class="exec-row">
        <label>Stop</label>
        <input id="editStop" type="number" step="any" value="${t.stop}" style="flex:1">
      </div>
      <div class="exec-row">
        <label>TP2</label>
        <input id="editTP2" type="number" step="any" value="${t.tp2}" style="flex:1">
      </div>
      <button class="btn-ghost" style="width:100%;margin-top:6px" onclick="applyEdits('${t.id}')">Apply changes</button>
    </div>`;
  if (t.signal_at_open) {
    html += `<div style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Signal at open</div>
      <div style="margin-bottom:6px"><span class="badge ${t.signal_at_open}">${t.signal_at_open}</span>
        <span class="badge ${t.confidence_at_open||'LOW'}">${t.confidence_at_open||'—'}</span>
        <span class="mu"> score ${t.score_at_open||0}</span></div>
      <div class="mu" style="line-height:1.55">${esc(t.why_at_open||"")}</div>
    </div>`;
  }
  if (t.adjustments && t.adjustments.length) {
    html += `<div class="mu" style="margin-top:10px;font-size:11px">Adjustments: ${t.adjustments.map(a => `${a.field} ${fmt(a.from)}→${fmt(a.to)}`).join(", ")}</div>`;
  }
  html += `<div style="display:flex;gap:8px;margin-top:14px">
    <button style="flex:1;padding:12px;background:var(--sell);color:#fff;border:0;border-radius:8px;font-weight:700;font-family:inherit;cursor:pointer" onclick="closeManual('${t.id}');closeModal()">Close trade</button>
    <button style="flex:1;padding:12px;background:var(--bd);color:var(--tx);border:0;border-radius:8px;font-weight:700;font-family:inherit;cursor:pointer" onclick="closeModal()">Dismiss</button>
  </div>`;
  $("modalContent").innerHTML = html;
  $("modal").classList.add("open");
}
function applyEdits(id) {
  const trades = store.getTrades();
  const t = trades.find(x => x.id === id);
  if (!t) return;
  const newStop = parseFloat($("editStop").value);
  const newTp = parseFloat($("editTP2").value);
  const side = t.side || "LONG";
  const errs = [];
  if (!newStop || (side === "LONG" && newStop >= t.entry) || (side === "SHORT" && newStop <= t.entry)) errs.push("invalid stop");
  if (!newTp || (side === "LONG" && newTp <= t.entry) || (side === "SHORT" && newTp >= t.entry)) errs.push("invalid TP2");
  if (errs.length) { toast("ERR", errs.join(", ")); return; }
  if (newStop !== t.stop) { t.adjustments = t.adjustments || []; t.adjustments.push({at: Date.now(), field:"stop", from: t.stop, to: newStop}); t.stop = newStop; }
  if (newTp !== t.tp2) { t.adjustments = t.adjustments || []; t.adjustments.push({at: Date.now(), field:"tp2", from: t.tp2, to: newTp}); t.tp2 = newTp; }
  store.setTrades(trades);
  closeModal();
  toast("BUY", `${t.coin} levels updated`);
  render();
}
function closeModal() { $("modal").classList.remove("open"); }

// ===================== STATS =====================
function computeStats(trades) {
  if (!trades.length) return null;
  const enriched = trades.map(t => {
    const side = t.side || "LONG";
    const margin = tradeMargin(t), notional = t.notional_usd;
    const pnl = side === "LONG" ? (t.close_price - t.entry) / t.entry * notional : (t.entry - t.close_price) / t.entry * notional;
    const roe = margin > 0 ? pnl / margin * 100 : 0;
    const holdMs = (t.closed_at || 0) - (t.opened_at || 0);
    return { ...t, side, pnl, roe, holdMs, margin, notional };
  });
  const wins = enriched.filter(t => t.pnl > 0), losses = enriched.filter(t => t.pnl <= 0);
  const grossWin = wins.reduce((s, t) => s + t.pnl, 0);
  const grossLoss = losses.reduce((s, t) => s + Math.abs(t.pnl), 0);
  const net = grossWin - grossLoss;
  const pf = grossLoss > 0 ? grossWin / grossLoss : (grossWin > 0 ? Infinity : 0);
  const winRate = enriched.length > 0 ? wins.length / enriched.length * 100 : 0;
  const avgWin = wins.length ? grossWin / wins.length : 0;
  const avgLoss = losses.length ? grossLoss / losses.length : 0;
  const best = Math.max(...enriched.map(t => t.pnl));
  const worst = Math.min(...enriched.map(t => t.pnl));
  const avgHoldMs = enriched.reduce((s, t) => s + t.holdMs, 0) / enriched.length;
  const sorted = [...enriched].sort((a, b) => a.closed_at - b.closed_at);
  let cum = 0;
  const curve = sorted.map(t => { cum += t.pnl; return { t: t.closed_at, v: cum }; });
  let peak = 0, maxDD = 0;
  for (const p of curve) { if (p.v > peak) peak = p.v; const dd = peak - p.v; if (dd > maxDD) maxDD = dd; }
  const reversed = [...sorted].reverse();
  let streak = 0, streakType = null;
  for (const t of reversed) {
    const type = t.pnl > 0 ? "win" : "loss";
    if (streakType === null) { streakType = type; streak = 1; }
    else if (streakType === type) streak++;
    else break;
  }
  const longs = enriched.filter(t => t.side === "LONG"), shorts = enriched.filter(t => t.side === "SHORT");
  const longWins = longs.filter(t => t.pnl > 0).length, shortWins = shorts.filter(t => t.pnl > 0).length;
  const longNet = longs.reduce((s, t) => s + t.pnl, 0), shortNet = shorts.reduce((s, t) => s + t.pnl, 0);
  const certain = enriched.filter(t => t.confidence_at_open === "CERTAIN");
  const confident = enriched.filter(t => t.confidence_at_open === "CONFIDENT");
  const tierStat = arr => ({
    count: arr.length,
    wins: arr.filter(t => t.pnl > 0).length,
    winRate: arr.length ? arr.filter(t => t.pnl > 0).length / arr.length * 100 : 0,
    net: arr.reduce((s, t) => s + t.pnl, 0),
  });
  let vClass = "ok", vTitle = "TOO FEW TRADES", vMsg = "";
  if (enriched.length < 10) {
    vTitle = "TOO FEW TRADES"; vMsg = `Only ${enriched.length} closed trade${enriched.length===1?"":"s"}. Need 10+ for meaningful statistics.`;
  } else if (pf >= 1.5 && winRate >= 45 && net > 0) {
    vClass = "good"; vTitle = "GOOD"; vMsg = "Profitable with a clear edge.";
  } else if (pf >= 1.0 && net > 0) {
    vTitle = "OK"; vMsg = "Slightly profitable. Consider only CERTAIN signals.";
  } else {
    vClass = "bad"; vTitle = "NEEDS WORK"; vMsg = "Losing money or no edge.";
  }
  return {
    trades: enriched.length, wins: wins.length, losses: losses.length,
    winRate, grossWin, grossLoss, net, pf, avgWin, avgLoss, best, worst, maxDD,
    streak, streakType, curve, avgHoldMs,
    longCount: longs.length, shortCount: shorts.length, longWins, shortWins, longNet, shortNet,
    certain: tierStat(certain), confident: tierStat(confident),
    vClass, vTitle, vMsg,
  };
}

function svgCurve(curve, width, height) {
  if (!curve || curve.length < 2) return "";
  const vals = curve.map(p => p.v);
  const min = Math.min(...vals, 0), max = Math.max(...vals, 0);
  const range = max - min || 1;
  const pad = 4, innerW = width - pad * 2, innerH = height - pad * 2;
  const xStep = innerW / (vals.length - 1);
  const pts = vals.map((v, i) => {
    const x = pad + i * xStep, y = pad + innerH - ((v - min) / range) * innerH;
    return x + "," + y;
  }).join(" ");
  const lastX = pad + (vals.length - 1) * xStep;
  const lastY = pad + innerH - ((vals[vals.length - 1] - min) / range) * innerH;
  const color = vals[vals.length - 1] >= 0 ? "#2ecc83" : "#ff5d68";
  const zeroY = pad + innerH - ((0 - min) / range) * innerH;
  return `<svg viewBox="0 0 ${width} ${height}" preserveAspectRatio="none">
    <line x1="${pad}" y1="${zeroY}" x2="${width-pad}" y2="${zeroY}" stroke="#262c38" stroke-width="1" stroke-dasharray="2,3"/>
    <polyline points="${pts}" fill="none" stroke="${color}" stroke-width="2" vector-effect="non-scaling-stroke"/>
    <circle cx="${lastX}" cy="${lastY}" r="3.5" fill="${color}"/>
  </svg>`;
}

// ===================== BACKTEST =====================
const btCache = new Map();
let btRunning = false, btAbort = false;

async function runBacktestOne(coin, windowDays, margin, leverage) {
  const meta = STATE.coins[coin] || {};
  const raw = coin.includes(":") ? coin.split(":")[1] : coin;
  const dex = meta.dex || "";
  const key = `${coin}|${windowDays}|${margin}|${leverage}`;
  if (btCache.has(key) && Date.now() - btCache.get(key).ts < 600_000) return btCache.get(key).result;
  const warmBars = 320;
  const barsWindow = Math.floor(windowDays * 24 * 60 / 5); // 5m bars
  const total5m = warmBars + barsWindow;
  const c5m = await fetchCandles(raw, "5m", total5m, dex);
  const c1h = await fetchCandles(raw, "1h", Math.ceil(total5m/12) + 50, dex);
  const c4h = await fetchCandles(raw, "4h", Math.ceil(total5m/48) + 50, dex);
  const c1d = await fetchCandles(raw, "1d", Math.ceil(total5m/288) + 50, dex);
  if (c5m.length < warmBars + 10) throw new Error("not enough 5m history");

  const trades = [];
  let openTrade = null;
  for (let i = warmBars; i < c5m.length - 1; i++) {
    const bar = c5m[i];
    const t = bar.t + IV_MS["5m"]; // close time
    const slice5 = c5m.slice(0, i + 1);
    const slice1h = c1h.filter(x => x.T <= t);
    const slice4h = c4h.filter(x => x.T <= t);
    const slice1d = c1d.filter(x => x.T <= t);
    if (!slice1h.length || !slice4h.length) continue;
    const candles = { "5m": slice5, "1h": slice1h, "4h": slice4h, "1d": slice1d };
    // add 15m approximation from 5m by merging 3 bars
    if (slice5.length >= 30) {
      const m15 = [];
      for (let j = 0; j + 2 < slice5.length; j += 3) {
        m15.push({ t: slice5[j].t, T: slice5[j+2].T, o: slice5[j].o, h: Math.max(slice5[j].h,slice5[j+1].h,slice5[j+2].h), l: Math.min(slice5[j].l,slice5[j+1].l,slice5[j+2].l), c: slice5[j+2].c, v: slice5[j].v+slice5[j+1].v+slice5[j+2].v });
      }
      candles["15m"] = m15;
    }
    const sig = signalFrom(candles, bar.c);
    if (sig && (sig.signal === "BUY" || sig.signal === "SELL") && (sig.confidence === "CERTAIN" || sig.confidence === "CONFIDENT")) {
      if (!openTrade) {
        const nextBar = c5m[i + 1];
        if (!nextBar) break;
        const side = sig.signal === "BUY" ? "LONG" : "SHORT";
        const entry = nextBar.o;
        let stop, tp2;
        if (side === "LONG") {
          stop = sig.stop || entry * 0.97;
          tp2 = sig.tp2 || entry * 1.03;
        } else {
          stop = sig.stop || entry * 1.03;
          tp2 = sig.tp2 || entry * 0.97;
        }
        openTrade = { id: i, coin, side, entry, stop, tp2, opened_at: nextBar.t,
          margin_usd: margin, notional_usd: margin * leverage, leverage,
          confidence_at_open: sig.confidence, score_at_open: sig.score, why_at_open: sig.why,
          closed_at: null, close_price: null, close_reason: null };
      }
    }
    if (openTrade) {
      const side = openTrade.side;
      const stopHit = side === "LONG" ? bar.l <= openTrade.stop : bar.h >= openTrade.stop;
      const tpHit = side === "LONG" ? bar.h >= openTrade.tp2 : bar.l <= openTrade.tp2;
      if (stopHit && tpHit) {
        // pessimistic: stop first
        openTrade.closed_at = bar.t; openTrade.close_price = openTrade.stop; openTrade.close_reason = "stop";
        trades.push(openTrade); openTrade = null;
      } else if (stopHit) {
        openTrade.closed_at = bar.t; openTrade.close_price = openTrade.stop; openTrade.close_reason = "stop";
        trades.push(openTrade); openTrade = null;
      } else if (tpHit) {
        openTrade.closed_at = bar.t; openTrade.close_price = openTrade.tp2; openTrade.close_reason = "tp2";
        trades.push(openTrade); openTrade = null;
      }
    }
    if (btAbort) throw new Error("aborted");
  }
  if (openTrade) {
    openTrade.closed_at = c5m[c5m.length-1].T; openTrade.close_price = c5m[c5m.length-1].c; openTrade.close_reason = "end_of_window";
    trades.push(openTrade);
  }
  const stats = computeStats(trades);
  const result = { coin, windowDays, margin, leverage, stats, trades, ts: Date.now() };
  btCache.set(key, { ts: Date.now(), result });
  return result;
}

function renderBacktestResult(r) {
  const el = $("btResults");
  if (!r) { el.innerHTML = ""; return; }
  const s = r.stats;
  if (!s) {
    el.innerHTML = `<div class="mu">No signals fired in the ${r.windowDays}-day window. That's the strict gates working — the bot stayed silent.</div>`;
    return;
  }
  const holdH = (s.avgHoldMs / 3600000).toFixed(1);
  const pfStr = isFinite(s.pf) ? s.pf.toFixed(2) : "∞";
  let warn = "";
  if (s.trades < 20) warn = `<div class="mu" style="color:var(--wait);font-weight:700;margin-bottom:8px">⚠ TOO FEW TRADES — results not statistically meaningful</div>`;
  if (s.trades >= 20 && s.winRate > 90) warn = `<div class="mu" style="color:var(--wait);font-weight:700;margin-bottom:8px">⚠ Unusually high win rate — check for overfitting</div>`;
  el.innerHTML = `
    ${warn}
    <div class="mu" style="font-size:11px;padding:8px;background:var(--card2);border-radius:6px;margin-bottom:10px;line-height:1.5">
      <b>Not modeled:</b> slippage, fees, funding, liquidity, or the historical universe. Past performance does not predict future results.
    </div>
    <div class="stat-grid">
      <div class="stat-box"><div class="k">Trades</div><div class="v">${s.trades}</div></div>
      <div class="stat-box"><div class="k">Win rate</div><div class="v ${s.winRate>=50?'up':'dn'}">${s.winRate.toFixed(1)}%</div></div>
      <div class="stat-box"><div class="k">Net P/L</div><div class="v ${s.net>=0?'up':'dn'}">$${fmt2(s.net)}</div></div>
      <div class="stat-box"><div class="k">Profit factor</div><div class="v ${s.pf>=1?'up':'dn'}">${pfStr}</div></div>
      <div class="stat-box"><div class="k">Avg win</div><div class="v up">$${fmt2(s.avgWin)}</div></div>
      <div class="stat-box"><div class="k">Avg loss</div><div class="v dn">$${fmt2(s.avgLoss)}</div></div>
      <div class="stat-box"><div class="k">Best</div><div class="v up">$${fmt2(s.best)}</div></div>
      <div class="stat-box"><div class="k">Worst</div><div class="v dn">$${fmt2(s.worst)}</div></div>
      <div class="stat-box"><div class="k">Max DD</div><div class="v dn">$${fmt2(s.maxDD)}</div></div>
      <div class="stat-box"><div class="k">Streak</div><div class="v">${s.streak} ${s.streakType||""}</div></div>
      <div class="stat-box"><div class="k">Avg hold</div><div class="v">${holdH}h</div></div>
      <div class="stat-box"><div class="k">W / L</div><div class="v">${s.wins} / ${s.losses}</div></div>
    </div>
    <div id="equityChart" style="margin-top:10px">${svgCurve(s.curve, 600, 100)}</div>
    <div class="side-row">
      <div class="side-box"><b>CERTAIN</b><br>${s.certain.count} trades · ${s.certain.winRate.toFixed(0)}% win<br><span class="${s.certain.net>=0?'up':'dn'}">$${fmt2(s.certain.net)}</span></div>
      <div class="side-box"><b>CONFIDENT</b><br>${s.confident.count} trades · ${s.confident.winRate.toFixed(0)}% win<br><span class="${s.confident.net>=0?'up':'dn'}">$${fmt2(s.confident.net)}</span></div>
    </div>
    <div class="side-row">
      <div class="side-box"><b>LONG</b><br>${s.longCount} · ${s.longCount?(s.longWins/s.longCount*100).toFixed(0):0}% win<br><span class="${s.longNet>=0?'up':'dn'}">$${fmt2(s.longNet)}</span></div>
      <div class="side-box"><b>SHORT</b><br>${s.shortCount} · ${s.shortCount?(s.shortWins/s.shortCount*100).toFixed(0):0}% win<br><span class="${s.shortNet>=0?'up':'dn'}">$${fmt2(s.shortNet)}</span></div>
    </div>`;
}

async function runBacktest() {
  if (btRunning) return;
  const coin = $("btCoin").value;
  if (!coin) return toast("ERR", "pick an asset");
  const win = parseInt($("btWindow").value);
  const margin = parseFloat($("btMargin").value);
  const leverage = Math.min(20, Math.max(1, parseFloat($("btLev").value) || 3));
  if (!margin || margin <= 0) return toast("ERR", "enter margin");
  btRunning = true; btAbort = false;
  $("btProgress").style.display = "block";
  $("btProgressText").textContent = `Running ${coin} (${win}d)...`;
  $("btResults").innerHTML = "";
  try {
    const r = await runBacktestOne(coin, win, margin, leverage);
    store.setBtLast(r);
    renderBacktestResult(r);
    toast("BUY", `Backtest done: ${coin} ${r.stats ? r.stats.trades + " trades" : "no signals"}`);
  } catch(e) {
    toast("ERR", "Backtest failed: " + e.message);
  } finally {
    btRunning = false;
    $("btProgress").style.display = "none";
  }
}

async function runBatch(assetClass) {
  if (btRunning) return;
  const coins = STATE.watchlist.filter(c => STATE.coins[c].assetClass === assetClass);
  if (!coins.length) return toast("ERR", "no coins in this class");
  const win = parseInt($("btWindow").value);
  const margin = parseFloat($("btMargin").value);
  const leverage = Math.min(20, Math.max(1, parseFloat($("btLev").value) || 3));
  if (!margin || margin <= 0) return toast("ERR", "enter margin");
  btRunning = true; btAbort = false;
  $("btProgress").style.display = "block";
  const results = [];
  for (let i = 0; i < coins.length; i++) {
    if (btAbort) break;
    $("btProgressText").textContent = `Running ${coins[i]} (${i+1}/${coins.length})...`;
    try {
      const r = await runBacktestOne(coins[i], win, margin, leverage);
      results.push(r);
    } catch(e) { console.error(e); }
  }
  store.setBtBatch(results);
  // aggregate
  let aggTrades = 0, aggWins = 0, aggNet = 0, aggGrossWin = 0, aggGrossLoss = 0;
  for (const r of results) {
    if (!r.stats) continue;
    aggTrades += r.stats.trades;
    aggWins += r.stats.wins;
    aggNet += r.stats.net;
    aggGrossWin += r.stats.grossWin;
    aggGrossLoss += r.stats.grossLoss;
  }
  const pf = aggGrossLoss > 0 ? aggGrossWin / aggGrossLoss : 0;
  const wr = aggTrades > 0 ? aggWins / aggTrades * 100 : 0;
  let html = `<div class="mu" style="font-size:11px;padding:8px;background:var(--card2);border-radius:6px;margin-bottom:10px">Portfolio simulation (independent trades, no correlation). Not modeled: slippage, fees, funding.</div>`;
  html += `<div class="stat-grid">
    <div class="stat-box"><div class="k">Assets</div><div class="v">${results.length}</div></div>
    <div class="stat-box"><div class="k">Total trades</div><div class="v">${aggTrades}</div></div>
    <div class="stat-box"><div class="k">Agg win rate</div><div class="v ${wr>=50?'up':'dn'}">${wr.toFixed(1)}%</div></div>
    <div class="stat-box"><div class="k">Agg net P/L</div><div class="v ${aggNet>=0?'up':'dn'}">$${fmt2(aggNet)}</div></div>
    <div class="stat-box"><div class="k">Agg PF</div><div class="v">${pf.toFixed(2)}</div></div>
  </div>`;
  html += `<div class="table-wrap" style="margin-top:10px"><table><thead><tr><th>Asset</th><th class="n">Trades</th><th class="n">Win %</th><th class="n">Net</th></tr></thead><tbody>`;
  for (const r of results) {
    const s = r.stats;
    html += `<tr><td>${esc(r.coin)}</td><td class="n">${s ? s.trades : 0}</td><td class="n">${s ? s.winRate.toFixed(0) : "—"}</td><td class="n ${s && s.net>=0?'up':'dn'}">${s ? "$"+fmt2(s.net) : "—"}</td></tr>`;
  }
  html += `</tbody></table></div>`;
  $("btResults").innerHTML = html;
  $("btProgress").style.display = "none";
  btRunning = false;
}

function toggleBacktest() {
  const body = $("backtestBody");
  const tog = $("backtestToggle");
  const isHidden = body.style.display === "none";
  body.style.display = isHidden ? "block" : "none";
  tog.textContent = isHidden ? "▲" : "▼";
}

// ===================== NOTIFICATIONS =====================
let swReg = null;
if ("serviceWorker" in navigator) {
  navigator.serviceWorker.register("sw.js").then(() => {
    navigator.serviceWorker.ready.then(r => { swReg = r; });
  }).catch(() => {});
}
function requestNotifPerm() {
  if (!("Notification" in window)) return toast("ERR", "Notifications not supported");
  Notification.requestPermission().then(p => {
    if (p === "granted") { toast("BUY", "Alerts enabled"); $("notifBtn").style.display = "none"; }
    else toast("ERR", "Permission denied");
  });
}
if ("Notification" in window) {
  if (Notification.permission === "granted") $("notifBtn").style.display = "none";
} else { $("notifBtn").style.display = "none"; }

function fireNotification(title, opts) {
  try {
    if (swReg && swReg.showNotification) swReg.showNotification(title, opts);
    else if ("Notification" in window && Notification.permission === "granted") new Notification(title, opts);
  } catch(e) {}
}

let signalsInitialized = false;
function checkSignalTransitions(coins) {
  const last = store.getLastSignals();
  const lastC = store.getLastConf();
  if (!signalsInitialized) {
    for (const c of coins) { last[c.coin] = c.signal; lastC[c.coin] = c.confidence; }
    store.setLastSignals(last); store.setLastConf(lastC);
    signalsInitialized = true;
    return;
  }
  const canNotify = ("Notification" in window) && Notification.permission === "granted";
  for (const c of coins) {
    const prev = last[c.coin];
    const prevC = lastC[c.coin];
    if (prev && prev !== c.signal) {
      if (canNotify && c.signal === "BUY") {
        fireNotification(`🟢 BUY ${c.coin}`, {
          body: `${c.confidence} · Entry ${fmt(c.entry)} · Stop ${fmt(c.stop)} · TP2 ${fmt(c.tp2)} · score ${c.score}`,
          tag: `buy-${c.coin}`, requireInteraction: true,
        });
      } else if (canNotify && c.signal === "SELL") {
        fireNotification(`🔴 SELL ${c.coin}`, {
          body: `${c.confidence} · score ${c.score}. ${(c.why||"").slice(0,120)}`,
          tag: `sell-${c.coin}`, requireInteraction: true,
        });
      }
    } else if (prev === "BUY" && prevC === "CONFIDENT" && c.confidence === "CERTAIN" && canNotify) {
      fireNotification(`⬆️ ${c.coin} now CERTAIN`, { body: `Upgraded confidence on BUY.`, tag: `upg-${c.coin}` });
    }
    last[c.coin] = c.signal; lastC[c.coin] = c.confidence;
  }
  store.setLastSignals(last); store.setLastConf(lastC);
}

// ===================== RENDER =====================
function toast(kind, msg) {
  const d = document.createElement("div");
  d.className = "t " + kind;
  d.innerHTML = "<b>" + esc(kind) + "</b> " + esc(msg);
  $("toast").appendChild(d);
  setTimeout(() => { d.style.opacity = 0; setTimeout(() => d.remove(), 300); }, 5000);
}

function renderTfTabs() {
  $("tfTabs").innerHTML = Object.keys(IV_MS).map(iv =>
    `<button class="${iv===currentIv?"on":""}" onclick="switchIv('${iv}')">${iv}</button>`).join("");
}
function switchIv(iv) { currentIv = iv; renderTfTabs(); loadCandles(currentCoin, currentIv); }

function renderAssetTabs() {
  const counts = { ALL: 0, CRYPTO: 0, STOCK: 0, COMMODITY: 0 };
  for (const c of Object.values(STATE.coins)) {
    counts.ALL++; if (counts[c.assetClass] != null) counts[c.assetClass]++;
  }
  const tabs = [
    { id: "ALL", label: `All (${counts.ALL})` },
    { id: "CRYPTO", label: `Crypto (${counts.CRYPTO})` },
    { id: "STOCK", label: `Stocks (${counts.STOCK})` },
    { id: "COMMODITY", label: `Commodities (${counts.COMMODITY})` },
  ];
  $("assetTabs").innerHTML = tabs.map(t =>
    `<button class="${assetFilter===t.id?'on':''}" onclick="setAssetFilter('${t.id}')">${t.label}</button>`).join("");
}
function setAssetFilter(f) { assetFilter = f; renderAssetTabs(); renderWatchlist(); }

function refreshCoinSelects() {
  const coins = STATE.watchlist.map(c => STATE.coins[c]).filter(Boolean);
  const html = coins.map(c =>
    `<option value="${esc(c.coin)}">${esc(c.coin)} — ${c.signal} (${c.score||0})</option>`).join("");
  const sel = $("execCoin");
  const curVal = sel.value || currentCoin || "";
  if (sel.innerHTML !== html) {
    sel.innerHTML = html;
    if (Array.from(sel.options).some(o => o.value === curVal)) sel.value = curVal;
    else if (coins.length) sel.value = coins[0].coin;
  }
  const btSel = $("btCoin");
  const curBt = btSel.value || currentCoin || "";
  if (btSel.innerHTML !== html) {
    btSel.innerHTML = html;
    if (Array.from(btSel.options).some(o => o.value === curBt)) btSel.value = curBt;
    else if (coins.length) btSel.value = coins[0].coin;
  }
}

function updateExecPreview() {
  const margin = parseFloat($("execSize").value) || 0;
  const lev = Math.min(20, Math.max(1, parseFloat($("execLev").value) || 1));
  $("notionalPreview").textContent = `Notional: $${(margin*lev).toFixed(2)} (${lev}x)`;
  const coin = $("execCoin").value;
  const live = parseFloat(STATE.mids[coin] || 0) || (STATE.coins[coin]?.price || 0);
  if (live > 0) {
    const longLiq = calcLiq(live, lev, "LONG"), shortLiq = calcLiq(live, lev, "SHORT");
    $("liqPreview").textContent = `Liq: LONG ${fmt(longLiq)} · SHORT ${fmt(shortLiq)}`;
  } else $("liqPreview").textContent = "—";
}

function renderSignalCard(c) {
  const el = $("signalCard");
  const rows = [];
  rows.push(`<div class="sig-row">
    <div class="sig-big">${esc(c.coin)} <span class="badge ${c.signal}">${c.signal}</span>
    <span class="badge ${c.confidence||'LOW'}">${c.confidence||'LOW'}</span>
    <span class="mu" style="font-size:13px">score ${c.score||0}</span></div>
    <div class="mu">${c.gatesPassed||0}/${c.gatesTotal||0} gates · ${c.soft||0}/8 soft</div></div>`);
  if (c.entry) rows.push(kv("Entry", fmt(c.entry)));
  if (c.entryZone) rows.push(kv("Entry zone", fmt(c.entryZone)));
  if (c.stop) rows.push(kv("Stop", fmt(c.stop)));
  if (c.tp1) rows.push(kv("TP1 (2R)", fmt(c.tp1)));
  if (c.tp2) rows.push(kv("TP2 (3R)", fmt(c.tp2)));
  if (c.trend) {
    const t = c.trend;
    const parts = [];
    for (const iv of ["1d","4h","1h","15m","5m"]) if (t[iv]) parts.push(`${iv} ${t[iv].trend}`);
    rows.push(kv("Trends", parts.join(" · ")));
  }
  if (c.trend?.["5m"]?.rsi != null) rows.push(kv("RSI(5m)", c.trend["5m"].rsi.toFixed(0)));
  if (c.trend?.["5m"]?.adx != null) rows.push(kv("ADX(5m)", c.trend["5m"].adx.toFixed(0)));
  if (c.why) rows.push(`<div class="why-box ${c.signal}">${esc(c.why)}</div>`);
  el.innerHTML = rows.join("");
}
function kv(k, v) { return `<div class="sig-row"><span class="mu">${k}</span><span>${v}</span></div>`; }

function renderPositions() {
  const open = store.getTrades().filter(t => !t.closed_at);
  const el = $("positions");
  if (!open.length) { el.innerHTML = `<div class="mu">No open positions.</div>`; return; }
  el.innerHTML = open.map(t => {
    const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
    const side = t.side || "LONG";
    const margin = tradeMargin(t), notional = t.notional_usd;
    const pnl = tradePnl(t, live);
    const roe = margin > 0 ? pnl / margin * 100 : 0;
    const liq = calcLiq(t.entry, t.leverage, side);
    const distLiq = Math.abs(live - liq) / live * 100;
    return `<div class="pos-item" onclick="showTradeDetail('${t.id}')">
      <div><b>${esc(t.coin)}</b> <span class="badge ${side}">${side}</span> ${t.leverage}x · <span class="mu">$${notional.toFixed(0)}</span><br>
      <span class="mu">entry ${fmt(t.entry)} · now ${fmt(live)} · stop ${fmt(t.stop)} · TP2 ${fmt(t.tp2)}</span><br>
      <span class="mu">liq ${fmt(liq)} (${distLiq.toFixed(1)}%)</span><br>
      <span class="${pnl>=0?'up':'dn'}" style="font-weight:700">P/L $${pnl.toFixed(2)} (${roe.toFixed(1)}% ROE)</span></div>
      <button class="x" onclick="event.stopPropagation();closeManual('${t.id}')">Close</button></div>`;
  }).join("");
}

function renderStats() {
  const el = $("statsWrap");
  const closed = store.getTrades().filter(t => t.closed_at);
  const s = computeStats(closed);
  if (!s) { el.innerHTML = `<div class="mu">No closed trades yet.</div>`; return; }
  const holdH = (s.avgHoldMs / 3600000).toFixed(1);
  const pfStr = isFinite(s.pf) ? s.pf.toFixed(2) : "∞";
  el.innerHTML = `
    <div id="verdictWrap" class="${s.vClass}">
      <div id="verdictTitle">${esc(s.vTitle)}</div>
      <div id="verdictMsg">${esc(s.vMsg)}</div>
    </div>
    <div class="stat-grid">
      <div class="stat-box"><div class="k">Trades</div><div class="v">${s.trades}</div></div>
      <div class="stat-box"><div class="k">Win rate</div><div class="v ${s.winRate>=50?'up':'dn'}">${s.winRate.toFixed(1)}%</div></div>
      <div class="stat-box"><div class="k">Net P/L</div><div class="v ${s.net>=0?'up':'dn'}">$${fmt2(s.net)}</div></div>
      <div class="stat-box"><div class="k">Profit factor</div><div class="v ${s.pf>=1?'up':'dn'}">${pfStr}</div></div>
      <div class="stat-box"><div class="k">Avg win</div><div class="v up">$${fmt2(s.avgWin)}</div></div>
      <div class="stat-box"><div class="k">Avg loss</div><div class="v dn">$${fmt2(s.avgLoss)}</div></div>
      <div class="stat-box"><div class="k">Best</div><div class="v up">$${fmt2(s.best)}</div></div>
      <div class="stat-box"><div class="k">Worst</div><div class="v dn">$${fmt2(s.worst)}</div></div>
      <div class="stat-box"><div class="k">Max DD</div><div class="v dn">$${fmt2(s.maxDD)}</div></div>
      <div class="stat-box"><div class="k">Streak</div><div class="v ${s.streakType==='win'?'up':'dn'}">${s.streak} ${s.streakType||""}</div></div>
      <div class="stat-box"><div class="k">Avg hold</div><div class="v">${holdH}h</div></div>
      <div class="stat-box"><div class="k">W/L</div><div class="v">${s.wins}/${s.losses}</div></div>
    </div>
    <div id="equityChart" style="margin-top:12px">${svgCurve(s.curve, 600, 100)}</div>
    <div class="side-row">
      <div class="side-box"><b>CERTAIN</b><br>${s.certain.count} · ${s.certain.winRate.toFixed(0)}% win<br><span class="${s.certain.net>=0?'up':'dn'}">$${fmt2(s.certain.net)}</span></div>
      <div class="side-box"><b>CONFIDENT</b><br>${s.confident.count} · ${s.confident.winRate.toFixed(0)}% win<br><span class="${s.confident.net>=0?'up':'dn'}">$${fmt2(s.confident.net)}</span></div>
    </div>
    <div class="side-row">
      <div class="side-box"><b>LONG</b><br>${s.longCount} · ${s.longCount?(s.longWins/s.longCount*100).toFixed(0):0}% win<br><span class="${s.longNet>=0?'up':'dn'}">$${fmt2(s.longNet)}</span></div>
      <div class="side-box"><b>SHORT</b><br>${s.shortCount} · ${s.shortCount?(s.shortWins/s.shortCount*100).toFixed(0):0}% win<br><span class="${s.shortNet>=0?'up':'dn'}">$${fmt2(s.shortNet)}</span></div>
    </div>`;
}

function renderWatchlist() {
  const q = ($("search")?.value || "").toLowerCase();
  const coins = STATE.watchlist.map(c => STATE.coins[c]).filter(Boolean)
    .filter(c => assetFilter === "ALL" || c.assetClass === assetFilter)
    .filter(c => c.coin.toLowerCase().includes(q));
  const rows = coins.map(c =>
    `<tr class="clickable" onclick="selectCoin('${esc(c.coin)}')">
      <td><b>${esc(c.coin)}</b></td>
      <td><span class="badge ${c.signal}">${c.signal}</span> <span class="badge ${c.confidence||'LOW'}">${c.confidence||'LOW'}</span></td>
      <td class="n">${fmt(c.price)}</td>
      <td class="n">${c.score||0}</td>
    </tr>`).join("");
  $("watch").innerHTML = rows
    ? `<div class="table-wrap"><table><thead><tr><th>Coin</th><th>Signal</th><th class="n">Price</th><th class="n">Score</th></tr></thead><tbody>${rows}</tbody></table></div>`
    : `<div class="mu">No matches.</div>`;
}

function selectCoin(coin) {
  currentCoin = coin;
  $("execCoin").value = coin;
  loadCandles(coin, currentIv);
  render();
}

function render() {
  $("statusDot").className = "dot " + (STATE.status === "live" ? "" : STATE.status === "error" ? "err" : "scan");
  if (!currentCoin && STATE.watchlist.length) {
    const buy = STATE.watchlist.find(c => STATE.coins[c].signal === "BUY");
    const btc = STATE.coins["BTC"] ? "BTC" : null;
    currentCoin = buy || btc || STATE.watchlist[0];
    renderTfTabs(); initChart(); loadCandles(currentCoin, currentIv);
  }
  refreshCoinSelects();
  renderAssetTabs();
  const live = parseFloat(STATE.mids[currentCoin] || 0) || (STATE.coins[currentCoin]?.price || null);
  $("livePrice").textContent = live ? "$" + fmt(live) + " " + currentCoin : "—";
  const execLive = parseFloat(STATE.mids[$("execCoin").value] || 0) || (STATE.coins[$("execCoin").value]?.price || null);
  $("execLive").textContent = execLive ? "$" + fmt(execLive) : "—";
  if (live) updateFormingBar(live);
  updateExecPreview();
  const cur = STATE.coins[currentCoin];
  if (cur) {
    const b = $("banner");
    b.className = "banner " + (cur.signal === "BUY" ? "buy" : cur.signal === "SELL" ? "sell" : cur.signal === "WAIT" ? "wait" : "neut");
    b.textContent = `${cur.signal} ${cur.coin} — ${cur.confidence||""} · score ${cur.score||0} · ${cur.gatesPassed||0}/${cur.gatesTotal||0} gates · ${cur.soft||0}/8 soft`;
    renderSignalCard(cur);
    const eh = $("execHint");
    const ec = STATE.coins[$("execCoin").value];
    if (ec) eh.innerHTML = `<b>${esc(ec.coin)}:</b> ${esc(ec.signal)} ${ec.confidence||""} · ${esc((ec.why||"").slice(0,200))}`;
  }
  renderPositions();
  renderStats();
  renderWatchlist();
  checkAutoClose();
  drawPriceLines(currentCoin);
}

// ===================== BOOT =====================
$("execCoin").addEventListener("change", function() {
  currentCoin = this.value;
  loadCandles(currentCoin, currentIv);
  render();
});
$("execSize").addEventListener("input", updateExecPreview);
$("execLev").addEventListener("input", updateExecPreview);
$("capital").addEventListener("change", function() { localStorage.setItem("legend_capital", this.value); });
$("search").addEventListener("input", renderWatchlist);
const savedCap = localStorage.getItem("legend_capital");
if (savedCap) $("capital").value = savedCap;

connectWS();
renderTfTabs();
render();
setTimeout(runScan, 200);
setInterval(runScan, SCAN_INTERVAL);
setInterval(() => { if (!document.hidden) render(); }, STATE_POLL_MS);

// restore last backtest
const lastBt = store.getBtLast();
if (lastBt) renderBacktestResult(lastBt);
