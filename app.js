/* C.A. Creative Bot — created and owned by Charles Amankwah */

const API = "https://api.hyperliquid.xyz/info";
const WS_URL = "wss://api.hyperliquid.xyz/ws";
const IV_MS = { "1m": 60000, "5m": 300000, "15m": 900000, "1h": 3600000, "4h": 14400000, "1d": 86400000 };
const HIP3_DEX = "xyz";
const STOCKS = ["NVDA","TSLA","AAPL","MSFT","GOOGL","AMZN","META","PLTR"];
const COMMODITIES = ["GOLD","SILVER","BRENTOIL","WTI","CL","COPPER","PLATINUM","PALLADIUM","NATGAS","URANIUM","NICKEL"];
const MIN_CRYPTO_VOL = 2_000_000;
const TOP_N_CRYPTO = 40;
const TOP_N_STOCKS = 20;
const TOP_N_COMMODITIES = 10;
const SCAN_INTERVAL = 60_000;
const STATE_POLL_MS = 4_000;
const CANDLE_CACHE_MS = 90_000;
const CACHE_TTL_BY_IV = { "1m": 30_000, "5m": 90_000, "15m": 300_000, "1h": 1_800_000, "4h": 7_200_000, "1d": 14_400_000 };
const MAINT_FRAC = 0.9;
const AUTO_MAX_OPEN = 5;
const AUTO_COOLDOWN_MS = 5 * 60 * 1000;
const AUTO_SCALP_MAX_OPEN = 3;
const AUTO_SCALP_COOLDOWN_MS = 2 * 60 * 1000;
const SCALP_TFS = ["5m", "15m", "1h", "4h"];
const NEWS_REFRESH_MS = 15 * 60 * 1000;
const INDEX_SYMBOLS = new Set(["SP500","XYZ100","NIFTY","KR200","SOX","SOXL","SPCX","SPC"]);
const FX_SYMBOLS = new Set(["EUR","JPY","GBP","KRW"]);
const COMMODITY_SYMBOLS = new Set(["GOLD","SILVER","BRENTOIL","WTI","CL","COPPER","PLATINUM","PALLADIUM","NATGAS","URANIUM","NICKEL"]);
const BULL_WORDS = ["surge","rally","soar","beat","upgrade","record","bullish","breakout","approval","adoption","inflow","buyback","partnership","launch","etf","halving","institutional"];
const BEAR_WORDS = ["crash","plunge","dump","hack","exploit","lawsuit","ban","bearish","downgrade","miss","liquidation","outflow","fraud","bankruptcy","war","sanction","tariff","sec","fine"];

const $ = id => document.getElementById(id);
const fmt = x => x == null ? "—" : (x >= 1000 ? Number(x).toLocaleString(undefined,{maximumFractionDigits:2}) : Number(x).toPrecision(6)).toString();
const fmt2 = x => x == null ? "—" : Number(x).toLocaleString(undefined,{minimumFractionDigits:2,maximumFractionDigits:2});
const esc = s => String(s).replace(/[&<>"']/g, c => ({"&":"&amp;","<":"&lt;",">":"&gt;","\"":"&quot;","'":"&#39;"}[c]));

const store = {
  getTrades: () => { try { return JSON.parse(localStorage.getItem("legend_trades") || "[]"); } catch { return []; } },
  setTrades: t => localStorage.setItem("legend_trades", JSON.stringify(t)),
  getLastSignals: () => { try { return JSON.parse(localStorage.getItem("legend_last_signals") || "{}"); } catch { return {}; } },
  setLastSignals: m => localStorage.setItem("legend_last_signals", JSON.stringify(m)),
  getLastConf: () => { try { return JSON.parse(localStorage.getItem("legend_last_confidence") || "{}"); } catch { return {}; } },
  setLastConf: m => localStorage.setItem("legend_last_confidence", JSON.stringify(m)),
  getBtLast: () => { try { return JSON.parse(localStorage.getItem("legend_backtest_last") || "null"); } catch { return null; } },
  setBtLast: x => localStorage.setItem("legend_backtest_last", JSON.stringify(x)),
  getHistory: () => { try { return JSON.parse(localStorage.getItem("legend_history") || "{}"); } catch { return {}; } },
  setHistory: h => localStorage.setItem("legend_history", JSON.stringify(h)),
};

const STATE = { status: "starting", lastScan: null, error: null, mids: {}, coins: {}, watchlist: [], oiHistory: {}, bookCache: {}, scalp: {}, news: { crypto: [], general: [], perTicker: {}, lastFetch: 0, sentiment: {} } };
let currentCoin = null, currentIv = "5m", assetFilter = "ALL";
let chart, candleSeries, ema20S, ema50S, ema200S;
let lastBars = [], lastBarTime = 0;
let priceLines = [], _lastPriceLineHash = "";
let dragState = { active: false, line: null, trade: null, field: null };

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
  for (let i = 1; i < cs.length; i++) trs.push(Math.max(cs[i].h - cs[i].l, Math.abs(cs[i].h - cs[i-1].c), Math.abs(cs[i].l - cs[i-1].c)));
  return wilderLast(trs, n);
}
function adx(cs, n = 14) {
  if (cs.length < 2 * n + 1) return { adx: null };
  const pdm = [], mdm = [], trs = [];
  for (let i = 1; i < cs.length; i++) {
    const up = cs[i].h - cs[i-1].h, dn = cs[i-1].l - cs[i].l;
    pdm.push(up > dn && up > 0 ? up : 0);
    mdm.push(dn > up && dn > 0 ? dn : 0);
    trs.push(Math.max(cs[i].h - cs[i].l, Math.abs(cs[i].h - cs[i-1].c), Math.abs(cs[i].l - cs[i-1].c)));
  }
  const st = wilderSeries(trs, n), sp = wilderSeries(pdm, n), sm = wilderSeries(mdm, n);
  if (!st.length) return { adx: null };
  const dx = [];
  for (let i = 0; i < st.length; i++) {
    if (st[i] === 0) { dx.push(0); continue; }
    const lp = 100 * sp[i] / st[i], lm = 100 * sm[i] / st[i];
    dx.push((lp + lm) === 0 ? 0 : 100 * Math.abs(lp - lm) / (lp + lm));
  }
  const as = wilderSeries(dx, n);
  return { adx: as.length ? as[as.length - 1] : null };
}
function volRatio(cs) {
  if (cs.length < 12) return 1;
  const recent = cs.slice(-6).map(c => c.v);
  const base = cs.length >= 72 ? cs.slice(-72, -6).map(c => c.v) : cs.slice(0, -6).map(c => c.v);
  const mR = recent.reduce((a,b)=>a+b,0)/recent.length;
  const mB = base.reduce((a,b)=>a+b,0)/Math.max(base.length, 1);
  return mB > 0 ? mR / mB : 1;
}

const candleCache = new Map();
async function fetchCandles(coin, interval, lookback = 320, dex = "", retries = 3) {
  const step = IV_MS[interval];
  const end = Date.now(), start = end - step * (lookback + 2);
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
  const _ttl = CACHE_TTL_BY_IV[interval] || CANDLE_CACHE_MS;
  if (hit && Date.now() - hit.ts < _ttl) return hit.data;
  try {
    const data = await fetchCandles(coin, interval, lookback, dex);
    candleCache.set(key, { ts: Date.now(), data });
    return data;
  } catch (e) { if (hit) return hit.data; throw e; }
}

const metaCache = new Map();
async function fetchMeta(dex = "") {
  const cached = metaCache.get(dex);
  if (cached && Date.now() - cached.ts < 60000) return cached.data;
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
    out.push({ raw: m.name, coin: dex ? `${dex}:${m.name}` : m.name, dex,
      maxLev: parseInt(m.maxLeverage || 3), vol: parseFloat(c.dayNtlVlm || 0),
      funding: parseFloat(c.funding || 0), markPx: parseFloat(c.markPx || 0),
      openInterest: parseFloat(c.openInterest || 0),
      oraclePx: parseFloat(c.oraclePx || 0),
      premium: parseFloat(c.premium || 0) });
  }
  metaCache.set(dex, { ts: Date.now(), data: out });
  return out;
}

async function fetchOrderBook(coin, dex = "") {
  try {
    const payload = { type: "l2Book", coin: coin };
    if (dex) payload.dex = dex;
    const r = await fetch(API, { method: "POST", headers: { "Content-Type": "application/json" }, body: JSON.stringify(payload) });
    if (!r.ok) return null;
    const data = await r.json();
    const bids = data.levels?.[0] || [], asks = data.levels?.[1] || [];
    const bidDepth = bids.slice(0, 20).reduce((s, l) => s + parseFloat(l.sz || 0) * parseFloat(l.px || 0), 0);
    const askDepth = asks.slice(0, 20).reduce((s, l) => s + parseFloat(l.sz || 0) * parseFloat(l.px || 0), 0);
    const total = bidDepth + askDepth;
    const imbalance = total > 0 ? bidDepth / total : 0.5;
    return { bidDepth, askDepth, imbalance };
  } catch (e) { return null; }
}

function scoreHeadline(title) {
  const t = String(title || "").toLowerCase();
  let s = 0;
  for (const w of BULL_WORDS) if (t.includes(w)) s += 1;
  for (const w of BEAR_WORDS) if (t.includes(w)) s -= 1;
  return Math.max(-3, Math.min(3, s));
}

async function fetchCryptoNews() {
  try {
    const r = await fetch("https://cryptocurrency.cv/api/news?limit=40");
    if (!r.ok) return [];
    const data = await r.json();
    const articles = Array.isArray(data.articles) ? data.articles : [];
    return articles.map(a => ({ title: a.title || "", link: a.link || "", source: a.source || "Crypto", pubDate: a.pubDate }));
  } catch (e) { return []; }
}

async function fetchGeneralMarketNews() {
  const feeds = [
    "https://feeds.marketwatch.com/marketwatch/topstories/",
    "https://www.cnbc.com/id/100003114/device/rss/rss.html"
  ];
  const out = [];
  for (const f of feeds) {
    try {
      const r = await fetch(`https://api.rss2json.com/v1/api.json?rss_url=${encodeURIComponent(f)}`);
      if (!r.ok) continue;
      const data = await r.json();
      for (const item of (data.items || []).slice(0, 15)) {
        out.push({ title: item.title || "", link: item.link || "", source: (data.feed && data.feed.title) || "RSS", pubDate: item.pubDate });
      }
    } catch (e) {}
  }
  return out;
}

async function fetchTickerNews(symbols) {
  const key = localStorage.getItem("marketaux_key");
  if (!key || !symbols.length) return {};
  const out = {};
  try {
    const r = await fetch(`https://api.marketaux.com/v1/news/all?symbols=${encodeURIComponent(symbols.join(","))}&filter_entities=true&language=en&limit=50&api_token=${key}`);
    if (!r.ok) return {};
    const data = await r.json();
    for (const a of (data.data || [])) {
      const syms = (a.entities || []).map(e => e.symbol).filter(Boolean);
      for (const s of syms) {
        if (!out[s]) out[s] = [];
        out[s].push({ title: a.title || "", link: a.url || "", source: a.source || "MarketAux", pubDate: a.published_at });
      }
    }
  } catch (e) {}
  return out;
}

async function fetchAllNews() {
  const [crypto, general] = await Promise.all([fetchCryptoNews(), fetchGeneralMarketNews()]);
  const symbols = Object.values(STATE.coins)
    .filter(c => c.assetClass === "STOCK" || c.assetClass === "COMMODITY")
    .map(c => c.coin.includes(":") ? c.coin.split(":")[1] : c.coin);
  const perTicker = await fetchTickerNews(symbols.slice(0, 20));
  STATE.news.crypto = crypto;
  STATE.news.general = general;
  STATE.news.perTicker = perTicker;
  STATE.news.lastFetch = Date.now();
  const sent = {};
  for (const c of Object.values(STATE.coins)) {
    const sym = c.coin.includes(":") ? c.coin.split(":")[1] : c.coin;
    const tickerNews = perTicker[sym] || [];
    const hasTickerNews = tickerNews.length > 0;
    let related, src;
    if (hasTickerNews) { related = tickerNews; src = "ticker"; }
    else if (c.assetClass === "CRYPTO") { related = [...crypto, ...general].slice(0, 15); src = "crypto"; }
    else { related = general.slice(0, 10); src = "macro"; }
    if (!related.length) { sent[c.coin] = { score: 0, src: "none" }; continue; }
    const avg = related.reduce((s, h) => s + scoreHeadline(h.title), 0) / related.length;
    sent[c.coin] = { score: Math.max(-1, Math.min(1, avg / 2)), src };
  }
  STATE.news.sentiment = sent;
}

function tf(candles, livePrice) {
  if (!candles || candles.length < 10) return null;
  const cs = candles.map(c => ({ ...c }));
  const last = cs[cs.length - 1];
  if (livePrice > 0) { last.c = livePrice; last.h = Math.max(last.h, livePrice); last.l = Math.min(last.l, livePrice); }
  const closes = cs.map(c => c.c);
  return { candles: cs, closes, e20: ema(closes, 20), e50: ema(closes, 50), e200: ema(closes, 200),
    e20s: emaSeries(closes, 20), e50s: emaSeries(closes, 50),
    rsi: rsi(closes), atr: atr(cs), adx: adx(cs).adx, price: livePrice || closes[closes.length - 1] };
}

function trendOf(t) {
  if (!t || t.e20 == null || t.e50 == null) return "FLAT";
  const up = t.e20 > t.e50 && (t.e200 == null || t.e50 > t.e200) && t.price > t.e50;
  const dn = t.e20 < t.e50 && (t.e200 == null || t.e50 < t.e200) && t.price < t.e50;
  if (t.e20s.length >= 6 && t.e50s.length >= 6) {
    let upCount = 0, dnCount = 0;
    const off = t.closes.length - t.e20s.length;
    for (let i = t.e20s.length - 6; i < t.e20s.length - 1; i++) {
      const c = t.closes[i + off];
      if (t.e20s[i] > t.e50s[i] && c > t.e50s[i]) upCount++;
      if (t.e20s[i] < t.e50s[i] && c < t.e50s[i]) dnCount++;
    }
    let fresh = false;
    for (let i = Math.max(2, t.e20s.length - 3); i < t.e20s.length; i++) {
      if ((t.e20s[i-1] - t.e50s[i-1]) * (t.e20s[i] - t.e50s[i]) < 0) { fresh = true; break; }
    }
    if (fresh) return "FLAT";
    if (up && upCount >= 4) return "UP";
    if (dn && dnCount >= 4) return "DOWN";
  }
  return "FLAT";
}

function computeBullScore(T, adx5, volR, setupOk, momentumOk) {
  let s = 0;
  if (T["4h"]?.trend === "UP") s += 20;
  if (T["1h"]?.trend === "UP") s += 20;
  if (T["15m"]?.trend === "UP") s += 10;
  if (adx5 >= 35) s += 15; else if (adx5 >= 30) s += 10; else if (adx5 >= 25) s += 5;
  if (volR >= 1.8) s += 15; else if (volR >= 1.5) s += 10; else if (volR >= 1.2) s += 5;
  if (setupOk) s += 10;
  if (momentumOk) s += 10;
  if (T["1d"]?.trend === "UP") s += 10;
  return Math.min(100, s);
}

function computeBearScore(T, price, atr5, adx5, volR, rsi5) {
  let s = 0;
  const t1 = T["1h"], t4 = T["4h"], t5 = T["5m"];
  if (t1?.trend === "DOWN") s += 25; else if (t1?.e50 && price < t1.e50) s += 15;
  if (t4?.trend === "DOWN") s += 20;
  if (t5?.trend === "DOWN") s += 8;
  if (adx5 >= 30) s += 22; else if (adx5 >= 25) s += 18; else if (adx5 < 15) s -= 8;
  if (volR >= 1.5) s += 12; else if (volR >= 1.2) s += 7;
  if (rsi5 < 30) s += 12; else if (rsi5 < 40) s += 8; else if (rsi5 < 45) s += 4; else if (rsi5 > 55) s -= 8;
  if (t1?.e50 && atr5 > 0) {
    const d = (price - t1.e50) / atr5;
    if (d < -2) s += 10; else if (d < -1) s += 5;
  }
  return Math.max(0, Math.min(100, s));
}

function signalFrom(candlesByTf, livePrice, meta = null) {
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

  const isCrypto = meta?.assetClass === "CRYPTO";
  const volPct = a5 / price;
  if (volPct < 0.0002) {
    return { signal: "NEUTRAL", confidence: "LOW", score: 0, price, why: "Market is too quiet — 5m volatility under 0.02%.", gatesPassed: 0, gatesTotal: 13, trend: T };
  }
  if (volPct > 0.03) {
    return { signal: "NEUTRAL", confidence: "LOW", score: 0, price, why: "Market is in chaos — 5m volatility above 3%.", gatesPassed: 0, gatesTotal: 13, trend: T };
  }

  const rsi5 = T["5m"].rsi, rsi1 = T["1h"].rsi;
  const adx5 = T["5m"].adx, adx15 = T["15m"]?.adx, adx1 = T["1h"].adx;
  const volR = volRatio(T["5m"].candles);
  const newsObj = STATE.news.sentiment[meta?.coin];
  const newsScore = (newsObj && typeof newsObj === "object" ? newsObj.score : newsObj) || 0;
  const newsSrc = (newsObj && typeof newsObj === "object" ? newsObj.src : null) || "none";
  const newsApplicable = isCrypto || newsSrc === "ticker";
  const newsBull = newsApplicable && newsScore > 0.4;
  const newsBear = newsApplicable && newsScore < -0.4;
  const funding = isCrypto ? (meta?.funding || 0) : 0;
  const fundingContrarian = isCrypto && funding < -0.00005;
  const fundingCrowdedLong = isCrypto && funding > 0.0003;
  const premium = isCrypto ? (meta?.premium || 0) : 0;
  const premiumHot = isCrypto && premium > 0.005;
  const oiHist = STATE.oiHistory[meta?.coin] || [];
  let oiRising = false;
  if (isCrypto && oiHist.length >= 3) {
    const delta = (oiHist[oiHist.length-1] - oiHist[oiHist.length-3]) / (oiHist[oiHist.length-3] || 1);
    if (delta > 0.01) oiRising = true;
  }

  const anyUptrend = T["4h"].trend !== "DOWN" && T["1h"].trend !== "DOWN";

  if (!anyUptrend) {
    const bear = computeBearScore(T, price, a5, adx5 || 0, volR, rsi5 || 50);
    const sellGates = [
      { name: "1-hour trend is down", pass: T["1h"].trend === "DOWN" || (T["1h"].e50 && price < T["1h"].e50) },
      { name: "4-hour trend is weak", pass: (T["4h"].e20 && T["4h"].e20 < T["4h"].e50) || (T["4h"].e50 && price < T["4h"].e50) },
      { name: "Trend is strong (ADX 22+)", pass: adx5 != null && adx5 >= 22 },
      { name: "Bearish strength is high (60+)", pass: bear >= 60 },
      { name: "Trading volume is high (0.9x+)", pass: volR >= 0.9 },
      { name: "Momentum is negative", pass: (() => {
          const c = T["5m"].closes; if (c.length < 4) return false;
          return !(c[c.length-2] > c[c.length-3] && c[c.length-3] > c[c.length-4]);
        })() },
      { name: "Not already oversold", pass: rsi1 != null && rsi1 > 28 },
    ];
    const passed = sellGates.filter(g => g.pass).length;
    const allPass = passed === sellGates.length;
    const conflicts = [];
    if (newsBull) conflicts.push("positive news tone (" + newsScore.toFixed(2) + ")");
    if (allPass && rsi1 != null && rsi1 < 25) conflicts.push("already deeply oversold");
    if (allPass && T["1h"].e50 && a5 > 0 && price < T["1h"].e50 - 6 * a5) conflicts.push("price way below trend line");
    if (allPass && adx1 != null && adx1 < 15) conflicts.push("bigger trend too weak");
    const tfT = [T["1d"]?.trend, T["4h"].trend, T["1h"].trend].filter(x => x && x !== "FLAT");
    if (tfT.length >= 2 && new Set(tfT).size >= 2) conflicts.push("timeframes disagree");
    const soft = [
      T["1d"]?.trend === "DOWN", adx5 != null && adx5 >= 30, adx1 != null && adx1 >= 20,
      volR >= 1.4, rsi5 != null && rsi5 >= 55 && rsi5 <= 70, newsBear, fundingCrowdedLong,
      T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 < 2,
    ].filter(Boolean).length;
    if (allPass && conflicts.length === 0 && soft >= 3) {
      const tier = soft >= 5 ? "CERTAIN" : "CONFIDENT";
      const why = "1-hour trend broken down; momentum flipped negative." + (newsBear ? " Bearish news." : "") + (fundingCrowdedLong ? " Longs crowded." : "");
      return { signal: "SELL", confidence: tier, score: bear, price, stop: price * 1.03, tp2: price * 0.97, why, gatesPassed: passed, gatesTotal: sellGates.length, soft, trend: T };
    }
    const failed = sellGates.filter(g => !g.pass).map(g => g.name);
    let why = "No clear signal. ";
    if (failed.length) why += "Missing: " + failed.join(", ") + ". ";
    if (conflicts.length) why += "Conflicts: " + conflicts.join("; ") + ". ";
    return { signal: "NEUTRAL", confidence: "LOW", score: bear, price, why, gatesPassed: passed, gatesTotal: sellGates.length, soft, trend: T };
  }

  const t5c = T["5m"].candles, e20_5 = T["5m"].e20;
  const distEma = e20_5 ? (price - e20_5) / a5 : 0;
  const bounced = (() => {
    if (!e20_5 || t5c.length < 4) return false;
    for (let i = t5c.length - 4; i < t5c.length - 1; i++) {
      if (t5c[i].l <= e20_5 * 1.002 && t5c[i].c > e20_5) return true;
    }
    return false;
  })();
  const pullbackOk = distEma >= -0.7 && distEma <= 0.3 && rsi5 != null && rsi5 >= 45 && rsi5 <= 70 && bounced;
  const breakoutOk = (() => {
    if (t5c.length < 24) return false;
    for (let i = t5c.length - 4; i < t5c.length - 1; i++) {
      const hi = Math.max(...t5c.slice(i - 20, i).map(c => c.h));
      const base = t5c.slice(Math.max(0, i - 72), Math.max(1, i - 6));
      const baseAvg = base.length ? base.reduce((s, c) => s + c.v, 0) / base.length : t5c[i].v;
      if (t5c[i].c > hi && baseAvg > 0 && t5c[i].v / baseAvg >= 1.1) return true;
    }
    return false;
  })();
  const setupOk = pullbackOk || breakoutOk;
  const momentumOk = (() => {
    const c = T["5m"].closes; if (c.length < 4) return false;
    return !(c[c.length-2] < c[c.length-3] && c[c.length-3] < c[c.length-4]);
  })();

  const gates = [
    { name: "1-day trend is up", pass: T["1d"] ? (T["1d"].trend === "UP" || (T["1d"].e50 && a5 > 0 && Math.abs(price - T["1d"].e50) / a5 < 3)) : true },
    { name: "4-hour trend is up", pass: T["4h"].trend === "UP" },
    { name: "1-hour trend is up", pass: T["1h"].trend === "UP" || T["1h"].trend === "FLAT" },
    { name: "15-minute trend is up", pass: T["15m"] ? (T["15m"].trend === "UP" || T["15m"].trend === "FLAT") : false },
    { name: "Price above key levels", pass: T["4h"].e50 && T["1h"].e50 && price > T["4h"].e50 && price > T["1h"].e50 },
    { name: "Good entry spot", pass: setupOk },
    { name: "ADX 22+", pass: adx5 != null && adx5 >= 22 },
    { name: "ADX15 12+", pass: adx15 != null && adx15 >= 12 },
    { name: "Volume 0.9x+", pass: volR >= 0.9 },
    { name: "Momentum up", pass: momentumOk },
    { name: "Not overbought", pass: rsi1 != null && rsi1 < 75 },
    { name: "Near trend line", pass: T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 <= 5 },
  ];
  const bullScore = computeBullScore(T, adx5 || 0, volR, setupOk, momentumOk);
  gates.push({ name: "Score 68+", pass: bullScore >= 68 });
  const passed = gates.filter(g => g.pass).length;
  const soft = [
    T["1d"]?.trend === "UP", adx5 != null && adx5 >= 30, adx1 != null && adx1 >= 20,
    volR >= 1.4, rsi5 != null && rsi5 >= 55 && rsi5 <= 70,
    T["1h"].e50 && a5 > 0 && Math.abs(price - T["1h"].e50) / a5 < 2,
    rsi1 != null && rsi1 >= 45 && rsi1 <= 65,
    newsBull, fundingContrarian, oiRising,
    T["1d"]?.e50 && T["4h"].e50 && T["1h"].e50 && T["15m"]?.e50 && T["5m"].e50 &&
      price > T["1d"].e50 && price > T["4h"].e50 && price > T["1h"].e50 && price > T["15m"].e50 && price > T["5m"].e50,
  ].filter(Boolean).length;
  const conflicts = [];
  if (newsBear) conflicts.push("bearish news (" + newsScore.toFixed(2) + ")");
  if (fundingCrowdedLong) conflicts.push("funding crowded longs");
  if (oiRising && !momentumOk) conflicts.push("OI rising but price falling");
  if (premiumHot) conflicts.push("perp >0.5% over oracle");
  if (rsi1 != null && rsi1 > 80) conflicts.push("overbought");
  if (T["1h"].e50 && a5 > 0 && price > T["1h"].e50 + 8 * a5) conflicts.push("chasing");
  if (adx1 != null && adx1 < 12) conflicts.push("bigger trend weak");
  const tfT = [T["1d"]?.trend, T["4h"].trend, T["1h"].trend].filter(x => x && x !== "FLAT");
  if (tfT.length >= 2 && new Set(tfT).size >= 2) conflicts.push("timeframes disagree");
  const allPass = passed === gates.length;
  if (allPass && conflicts.length === 0 && soft >= 4) {
    const swingLow = Math.min(...t5c.slice(-12).map(c => c.l));
    let stop = Math.min(swingLow - 0.2 * a5, price - 1.5 * a5);
    stop = Math.max(stop, price - 3 * a5);
    const risk = price - stop;
    const tp1 = price + 1 * risk, tp2 = price + 2 * risk;
    const tier = soft >= 7 ? "CERTAIN" : "CONFIDENT";
    const setup = pullbackOk ? "PULLBACK" : "BREAKOUT";
    const why = "4h + 1h + 15m up." + (newsBull ? " Bullish news." : "") + (fundingContrarian ? " Shorts crowded." : "") + (oiRising ? " OI rising." : "") + " Pullback to EMA with volume. Buy now.";
    return { signal: "BUY", setup, confidence: tier, score: bullScore, price, entry: price, stop, tp1, tp2, why, gatesPassed: passed, gatesTotal: gates.length, soft, trend: T };
  }
  if (bullScore >= 45 && passed >= gates.length - 7 && conflicts.length === 0) {
    const failed = gates.filter(g => !g.pass).map(g => g.name);
    const why = "Uptrend healthy but not safe entry. Missing: " + failed.join(", ") + ".";
    const entryZone = e20_5 ? e20_5 - 0.25 * a5 : price;
    return { signal: "WAIT", confidence: "MED", score: bullScore, price, entryZone, why, gatesPassed: passed, gatesTotal: gates.length, soft, trend: T };
  }
  const failed = gates.filter(g => !g.pass).map(g => g.name);
  let why = "No clear signal. ";
  if (failed.length) why += "Missing: " + failed.slice(0, 3).join(", ") + ". ";
  if (conflicts.length) why += "Conflicts: " + conflicts.join("; ") + ". ";
  return { signal: "NEUTRAL", confidence: "LOW", score: bullScore, price, why, gatesPassed: passed, gatesTotal: gates.length, soft, trend: T };
}

function scalpSignal(candles, timeframe, livePrice, meta) {
  if (!candles || candles.length < 30) return null;
  const cs = candles.map(c => ({ ...c }));
  const last = cs[cs.length - 1];
  if (livePrice > 0) { last.c = livePrice; last.h = Math.max(last.h, livePrice); last.l = Math.min(last.l, livePrice); }
  const closes = cs.map(c => c.c);
  const e9 = ema(closes, 9);
  const e21 = ema(closes, 21);
  if (e9 == null || e21 == null) return null;
  const atrV = atr(cs, 14);
  if (!atrV || atrV <= 0) return null;
  const rsiV = rsi(closes, 7);
  if (rsiV == null) return null;
  const volR = volRatio(cs);
  const price = livePrice || last.c;
  if (atrV / price < 0.0003) return null;

  const c1 = cs[cs.length-1], c2 = cs[cs.length-2], c3 = cs[cs.length-3];
  const up3 = c1.c > c2.c && c2.c > c3.c && c1.c > c1.o;
  const dn3 = c1.c < c2.c && c2.c < c3.c && c1.c < c1.o;
  const barRange = Math.abs(c1.c - c1.o);
  const spiking = barRange > atrV * 0.6;
  const volSurge = volR >= 1.25;
  const aboveE9 = price > e9;
  const belowE9 = price < e9;
  const e9Rising = cs.length > 3 ? e9 > ema(closes.slice(0, -2), 9) : false;
  const e9Falling = cs.length > 3 ? e9 < ema(closes.slice(0, -2), 9) : false;

  if (up3 && aboveE9 && spiking && volSurge && rsiV > 40 && rsiV < 75 && e9Rising) {
    const stop = Math.min(c2.l, c1.l) - 0.15 * atrV;
    const risk = price - stop;
    if (risk > 0 && risk < atrV * 1.5) {
      const tp1 = price + 1.0 * risk;
      const tp2 = price + 2.0 * risk;
      const tier = (volR >= 1.8 && rsiV < 68) ? "HIGH" : "MED";
      return {
        signal: "BUY", side: "LONG", timeframe, price, entry: price, stop, tp1, tp2,
        confidence: tier, atr: atrV, volR, rsi: rsiV,
        why: `${timeframe} scalp: 3 up-candles, ${volR.toFixed(1)}x volume, price above rising 9-EMA.`
      };
    }
  }

  if (dn3 && belowE9 && spiking && volSurge && rsiV < 60 && rsiV > 25 && e9Falling) {
    const stop = Math.max(c2.h, c1.h) + 0.15 * atrV;
    const risk = stop - price;
    if (risk > 0 && risk < atrV * 1.5) {
      const tp1 = price - 1.0 * risk;
      const tp2 = price - 2.0 * risk;
      const tier = (volR >= 1.8 && rsiV > 32) ? "HIGH" : "MED";
      return {
        signal: "SELL", side: "SHORT", timeframe, price, entry: price, stop, tp1, tp2,
        confidence: tier, atr: atrV, volR, rsi: rsiV,
        why: `${timeframe} scalp: 3 down-candles, ${volR.toFixed(1)}x volume, price below falling 9-EMA.`
      };
    }
  }

  return null;
}

async function buildUniverse() {
  const list = [];
  try {
    const crypto = await fetchMeta("");
    crypto.sort((a, b) => b.vol - a.vol);
    for (const m of crypto.filter(m => m.vol > MIN_CRYPTO_VOL).slice(0, TOP_N_CRYPTO))
      list.push({ ...m, assetClass: "CRYPTO" });
  } catch (e) {}
  try {
    const hip = await fetchMeta(HIP3_DEX);
    const stocks = [], commodities = [];
    for (const m of hip) {
      if (INDEX_SYMBOLS.has(m.raw) || FX_SYMBOLS.has(m.raw)) continue;
      if (COMMODITY_SYMBOLS.has(m.raw)) commodities.push({ ...m, assetClass: "COMMODITY" });
      else stocks.push({ ...m, assetClass: "STOCK" });
    }
    stocks.sort((a, b) => b.vol - a.vol);
    commodities.sort((a, b) => b.vol - a.vol);
    list.push(...stocks.slice(0, TOP_N_STOCKS));
    list.push(...commodities.slice(0, TOP_N_COMMODITIES));
  } catch (e) {}
  return list;
}

let scanRunning = false;
async function runScan() {
  if (scanRunning) return;
  scanRunning = true;
  STATE.status = "scanning"; render();
  try {
    const universe = await buildUniverse();
    const results = {};
    const scalpResults = {};
    const queue = [...universe];
    const total = queue.length;
    let done = 0;
    let lastProgressiveRender = 0;
    const order = { BUY:0, WAIT:1, SELL:2, NEUTRAL:3 };
    async function worker() {
      while (queue.length) {
        const m = queue.shift();
        try {
          const candles = {};
          await Promise.all(["5m","15m","1h","4h","1d"].map(async iv => {
            try { candles[iv] = await getCandles(m.raw, iv, 320, m.dex); } catch(e) {}
          }));
          const live = parseFloat(STATE.mids[m.coin] || 0) || m.markPx;
          if (m.openInterest) {
            if (!STATE.oiHistory[m.coin]) STATE.oiHistory[m.coin] = [];
            STATE.oiHistory[m.coin].push(m.openInterest);
            if (STATE.oiHistory[m.coin].length > 10) STATE.oiHistory[m.coin].shift();
          }
          const sig = signalFrom(candles, live, m);
          if (sig) {
            sig.coin = m.coin; sig.assetClass = m.assetClass; sig.dex = m.dex;
            results[m.coin] = sig;
          }
          const perTf = {};
          for (const tfv of SCALP_TFS) {
            if (candles[tfv]) {
              const ss = scalpSignal(candles[tfv], tfv, live, m);
              if (ss) { ss.coin = m.coin; ss.assetClass = m.assetClass; ss.dex = m.dex; perTf[tfv] = ss; }
            }
          }
          if (Object.keys(perTf).length) scalpResults[m.coin] = perTf;
          const now = Date.now();
          if (now - lastProgressiveRender > 400 || done + 1 === total) {
            STATE.coins = { ...results };
            STATE.scalp = { ...scalpResults };
            STATE.watchlist = Object.values(STATE.coins).sort((a,b) => (order[a.signal]||9) - (order[b.signal]||9) || (b.score||0) - (a.score||0)).map(c => c.coin);
            STATE.status = `scanning ${done + 1}/${total}`;
            render();
            lastProgressiveRender = now;
          }
        } catch(e) {}
        done++;
        STATE.status = `scanning ${done}/${total}`;
      }
    }
    await Promise.all(Array(12).fill(0).map(() => worker()));
    const sorted = Object.values(results).sort((a,b) => (order[a.signal]||9) - (order[b.signal]||9) || (b.score||0) - (a.score||0));
    STATE.coins = results;
    STATE.scalp = scalpResults;
    STATE.watchlist = sorted.map(c => c.coin);
    STATE.lastScan = Date.now();
    STATE.status = "live"; STATE.error = null;
    checkSignalTransitions(sorted);
    if (!STATE.news.lastFetch || Date.now() - STATE.news.lastFetch > NEWS_REFRESH_MS) {
      fetchAllNews().catch(() => {});
    }
  } catch (e) { STATE.error = String(e); STATE.status = "error"; }
  scanRunning = false;
  render();
}

// FIX v6.1: replace entirely (no stale entries) + always include currentCoin
async function refreshAllScalps() {
  if (STATE.status !== "live") return;
  const coinsToRefresh = Object.values(STATE.coins).slice(0, 40);
  const curMeta = currentCoin ? STATE.coins[currentCoin] : null;
  if (curMeta && !coinsToRefresh.some(c => c.coin === currentCoin)) coinsToRefresh.push(curMeta);
  const fresh = {};
  for (const c of coinsToRefresh) {
    try {
      const meta = STATE.coins[c.coin] || {};
      const raw = c.coin.includes(":") ? c.coin.split(":")[1] : c.coin;
      const dex = meta.dex || "";
      const live = parseFloat(STATE.mids[c.coin] || 0) || c.price;
      if (!live) continue;
      const perTf = {};
      for (const tfv of SCALP_TFS) {
        const hit = candleCache.get(`${raw}|${tfv}|${dex}`);
        if (hit && hit.data) {
          const ss = scalpSignal(hit.data, tfv, live, meta);
          if (ss) { ss.coin = c.coin; ss.assetClass = c.assetClass; ss.dex = meta.dex; perTf[tfv] = ss; }
        }
      }
      if (Object.keys(perTf).length) fresh[c.coin] = perTf;
    } catch(e) {}
  }
  STATE.scalp = fresh;
}

let ws;
function connectWS() {
  try {
    ws = new WebSocket(WS_URL);
    ws.onopen = () => ws.send(JSON.stringify({ method: "subscribe", subscription: { type: "allMids" } }));
    ws.onmessage = (ev) => { try { const m = JSON.parse(ev.data); if (m.channel === "allMids") STATE.mids = m.data.mids || {}; } catch(e) {} };
    ws.onclose = () => setTimeout(connectWS, 3000);
    ws.onerror = () => {};
  } catch(e) { setTimeout(connectWS, 5000); }
}

function initChart() {
  const el = $("chart"); el.innerHTML = "";
  chart = LightweightCharts.createChart(el, {
    layout: { background: { color: getComputedStyle(document.documentElement).getPropertyValue("--card").trim() || "#171b24" }, textColor: getComputedStyle(document.documentElement).getPropertyValue("--tx").trim() || "#e8ebf2", fontSize: 11 },
    grid: { vertLines: { color: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" }, horzLines: { color: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" } },
    timeScale: { timeVisible: true, secondsVisible: false, borderColor: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" },
    rightPriceScale: { borderColor: getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38" },
    crosshair: { mode: 0 },
    handleScroll: true, handleScale: true,
  });
  candleSeries = chart.addCandlestickSeries({ upColor: "#2ecc83", downColor: "#ff5d68", borderVisible: false, wickUpColor: "#2ecc83", wickDownColor: "#ff5d68" });
  ema20S = chart.addLineSeries({ color: "#4ea8ff", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  ema50S = chart.addLineSeries({ color: "#f0b429", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  ema200S = chart.addLineSeries({ color: "#8b93a1", lineWidth: 1, priceLineVisible: false, lastValueVisible: false });
  new ResizeObserver(() => { if (chart) chart.applyOptions({ width: el.clientWidth, height: el.clientHeight }); }).observe(el);
  attachDragHandlers(el);
}

function buildEmaSeries(arr, offset, stepMs) {
  if (!lastBars.length || !arr.length) return [];
  const t0 = lastBars[0].time;
  return arr.map((v, i) => ({ time: t0 + Math.round((offset + i) * (stepMs/1000)), value: v }));
}

function prefetchAdjacent(coin, iv) {
  const order = ["1m","5m","15m","1h","4h","1d"];
  const idx = order.indexOf(iv);
  if (idx < 0) return;
  const meta = STATE.coins[coin] || {};
  const raw = coin.includes(":") ? coin.split(":")[1] : coin;
  const dex = meta.dex || "";
  [idx - 1, idx + 1].forEach(i => {
    if (i >= 0 && i < order.length) getCandles(raw, order[i], 320, dex).catch(() => {});
  });
}

async function loadCandles(coin, iv, preserveView = false) {
  if (!coin || !chart) return;
  let savedRange = null, wasAtEnd = false;
  if (preserveView) {
    try {
      savedRange = chart.timeScale().getVisibleRange();
      if (savedRange && lastBarTime > 0) {
        const barSec = IV_MS[iv] / 1000;
        wasAtEnd = Math.abs(savedRange.to - lastBarTime) < barSec * 2;
      }
    } catch(e) {}
  }
  try {
    const meta = STATE.coins[coin] || {};
    const raw = coin.includes(":") ? coin.split(":")[1] : coin;
    const dex = meta.dex || "";
    const _ck = `${raw}|${iv}|${dex}`;
    const _cached = candleCache.get(_ck);
    if (_cached && _cached.data.length && candleSeries && !lastBars.length) {
      try {
        const _bars = _cached.data.map(c => ({ time: Math.floor(c.t/1000), open: c.o, high: c.h, low: c.l, close: c.c }));
        candleSeries.setData(_bars);
      } catch(e) {}
    }
    const data = await getCandles(raw, iv, 320, dex);
    if (!data.length) return;
    lastBars = data.map(c => ({ time: Math.floor(c.t/1000), open: c.o, high: c.h, low: c.l, close: c.c }));
    lastBarTime = lastBars[lastBars.length-1].time;
    candleSeries.setData(lastBars);
    const closes = data.map(c => c.c);
    ema20S.setData(buildEmaSeries(emaSeries(closes, 20), 19, IV_MS[iv]));
    ema50S.setData(buildEmaSeries(emaSeries(closes, 50), 49, IV_MS[iv]));
    ema200S.setData(buildEmaSeries(emaSeries(closes, 200), 199, IV_MS[iv]));
    if (wasAtEnd) chart.timeScale().scrollToRealTime();
    else if (savedRange) { try { chart.timeScale().setVisibleRange(savedRange); } catch(e) { chart.timeScale().fitContent(); } }
    else chart.timeScale().fitContent();
    drawPriceLines(coin, true);
    prefetchAdjacent(coin, iv);
  } catch(e) {}
}

function updateFormingBar(live) {
  if (!lastBars.length || !live || !chart) return;
  const step = IV_MS[currentIv];
  if (Math.floor(Date.now() / step) * step / 1000 > lastBarTime) {
    loadCandles(currentCoin, currentIv, true);
    return;
  }
  const last = lastBars[lastBars.length-1];
  last.close = live; last.high = Math.max(last.high, live); last.low = Math.min(last.low, live);
  candleSeries.update(last);
}

function drawPriceLines(coin, force = false) {
  if (!candleSeries || !coin) return;
  if (dragState.active && !force) return;
  const open = store.getTrades().filter(t => !t.closed_at && t.coin === coin);
  const hash = coin + "|" + open.map(t => `${t.id}:${t.entry}:${t.stop}:${t.tp2}:${t.tp1_hit}`).join(",");
  if (!force && hash === _lastPriceLineHash) return;
  _lastPriceLineHash = hash;
  priceLines.forEach(p => { try { candleSeries.removePriceLine(p.line); } catch(e) {} });
  priceLines = [];
  for (const t of open) {
    try {
      const scalpTag = t.scalp ? `⚡${t.timeframe} ` : "";
      const tp1Tag = t.tp1_hit ? "💰 " : "";
      priceLines.push({ line: candleSeries.createPriceLine({ price: t.entry, color: t.scalp ? "#f0b429" : "#4ea8ff", lineWidth: 1, lineStyle: LightweightCharts.LineStyle.Solid, axisLabelVisible: true, title: scalpTag + tp1Tag + (t.side || "LONG") + " entry" }), trade: t, field: null });
      priceLines.push({ line: candleSeries.createPriceLine({ price: t.stop, color: "#ff5d68", lineWidth: 2, lineStyle: LightweightCharts.LineStyle.Dashed, axisLabelVisible: true, title: t.breakeven_set ? "Trail/BE" : "Stop" }), trade: t, field: "stop" });
      priceLines.push({ line: candleSeries.createPriceLine({ price: t.tp2, color: "#2ecc83", lineWidth: 2, lineStyle: LightweightCharts.LineStyle.Dashed, axisLabelVisible: true, title: "TP2" }), trade: t, field: "tp2" });
    } catch(e) {}
  }
}

function attachDragHandlers(el) {
  const getXY = (ev) => ev.touches?.length ? { x: ev.touches[0].clientX, y: ev.touches[0].clientY } : { x: ev.clientX, y: ev.clientY };
  const tryStart = (ev) => {
    if (!chart || !candleSeries) return;
    const yRel = getXY(ev).y - el.getBoundingClientRect().top;
    let hit = null, best = 12;
    for (const pl of priceLines) {
      if (!pl.field) continue;
      const py = candleSeries.priceToCoordinate(pl.line.options().price);
      if (py == null) continue;
      const d = Math.abs(py - yRel);
      if (d < best) { hit = pl; best = d; }
    }
    if (hit) { dragState = { active: true, line: hit.line, trade: hit.trade, field: hit.field }; ev.preventDefault(); }
  };
  const doMove = (ev) => {
    if (!dragState.active) return;
    const price = candleSeries.coordinateToPrice(getXY(ev).y - el.getBoundingClientRect().top);
    if (price == null) return;
    const t = dragState.trade, side = t.side || "LONG";
    if (dragState.field === "stop" && ((side === "LONG" && price >= t.entry) || (side === "SHORT" && price <= t.entry))) return;
    if (dragState.field === "tp2" && ((side === "LONG" && price <= t.entry) || (side === "SHORT" && price >= t.entry))) return;
    const mag = Math.pow(10, Math.floor(Math.log10(price)) - 3);
    const snapped = Math.round(price / mag) * mag;
    try { dragState.line.applyOptions({ price: snapped }); } catch(e) {}
    t[dragState.field] = snapped;
    ev.preventDefault();
  };
  const doEnd = () => {
    if (!dragState.active) return;
    try {
      const trades = store.getTrades();
      const idx = trades.findIndex(x => x.id === dragState.trade.id);
      if (idx >= 0) {
        const oldV = trades[idx][dragState.field], newV = dragState.trade[dragState.field];
        if (oldV !== newV) {
          trades[idx][dragState.field] = newV;
          trades[idx].adjustments = trades[idx].adjustments || [];
          trades[idx].adjustments.push({ at: Date.now(), field: dragState.field, from: oldV, to: newV });
          store.setTrades(trades);
          toast("BUY", `${dragState.trade.coin} ${dragState.field.toUpperCase()} → ${fmt(newV)}`);
        }
      }
    } catch(e) {}
    dragState = { active: false, line: null, trade: null, field: null };
    render();
  };
  el.addEventListener("mousedown", tryStart);
  el.addEventListener("mousemove", doMove);
  window.addEventListener("mouseup", doEnd);
  el.addEventListener("touchstart", tryStart, { passive: false });
  el.addEventListener("touchmove", doMove, { passive: false });
  window.addEventListener("touchend", doEnd);
}

function calcLiq(entry, lev, side) { const f = MAINT_FRAC / lev; return side === "LONG" ? entry * (1 - f) : entry * (1 + f); }
function tradePnl(t, live) { const n = t.notional_usd, e = t.entry; return (t.side || "LONG") === "LONG" ? (live - e) / e * n : (e - live) / e * n; }

// FIX v6.1: prefer original margin so ROE is computed against the same base after TP1 halves margin_usd
function tradeMargin(t) {
  return t.original_margin_usd || t.margin_usd || (t.notional_usd / t.leverage);
}

function executeTrade(side, scalpInfo = null) {
  const coin = scalpInfo?.coin || $("execCoin").value;
  if (!coin) return toast("ERR", "pick a coin");
  const meta = STATE.coins[coin];
  const live = parseFloat(STATE.mids[coin] || 0) || (meta ? meta.price : 0);
  if (!live) return toast("ERR", "no live price");
  const margin = scalpInfo?.margin || parseFloat($("execSize").value);
  const lev = scalpInfo?.leverage || Math.min(20, Math.max(1, parseFloat($("execLev").value) || 1));
  if (!margin || margin <= 0) return toast("ERR", "enter margin");
  let stop, tp2, tp1;
  if (scalpInfo) {
    stop = scalpInfo.stop; tp1 = scalpInfo.tp1; tp2 = scalpInfo.tp2;
    // FIX v6.1: sanity + slippage guard for scalp entries
    if (side === "LONG" && (stop >= live || tp2 <= live)) return toast("ERR", "Scalp levels invalid at current price");
    if (side === "SHORT" && (stop <= live || tp2 >= live)) return toast("ERR", "Scalp levels invalid at current price");
    const drift = Math.abs(live - scalpInfo.entry) / scalpInfo.entry;
    if (drift > 0.005) return toast("ERR", "Price moved >0.5% from scalp entry — wait for next signal");
  } else {
    const stopIn = parseFloat($("execStop").value), tpIn = parseFloat($("execTP").value);
    if (side === "LONG") {
      stop = stopIn || (meta && meta.signal === "BUY" && meta.stop) || live * 0.97;
      tp2 = tpIn || (meta && meta.signal === "BUY" && meta.tp2) || live * 1.03;
      if (stop >= live || tp2 <= live) return toast("ERR", "invalid LONG levels");
    } else {
      stop = stopIn || live * 1.03; tp2 = tpIn || live * 0.97;
      if (stop <= live || tp2 >= live) return toast("ERR", "invalid SHORT levels");
    }
    tp1 = (live + tp2) / 2;
  }
  const trades = store.getTrades();
  trades.push({
    id: Date.now() + "-" + Math.random().toString(36).slice(2, 6),
    coin, side, entry: live, stop, tp1, tp2,
    initial_risk: Math.abs(live - stop),
    margin_usd: margin, notional_usd: margin * lev, leverage: lev,
    original_margin_usd: margin, original_notional_usd: margin * lev,
    opened_at: Date.now(), closed_at: null, close_price: null, close_reason: null,
    breakeven_set: false, tp1_hit: false, partial_pnl: 0,
    scalp: !!scalpInfo, timeframe: scalpInfo?.timeframe || null,
    signal_at_open: meta?.signal, confidence_at_open: meta?.confidence, score_at_open: meta?.score, why_at_open: meta?.why, setup_at_open: meta?.setup, adjustments: []
  });
  store.setTrades(trades);
  const tag = scalpInfo ? `⚡Scalp ${scalpInfo.timeframe} ` : "";
  toast(side === "LONG" ? "BUY" : "SELL", `${tag}${coin} ${side} $${(margin*lev).toFixed(0)} @ ${fmt(live)}`);
  render();
}

function closeTradeInternal(t, price, reason) {
  t.closed_at = Date.now();
  t.close_price = price;
  t.close_reason = reason;
  const finalPnl = tradePnl(t, price);
  t.final_pnl = finalPnl;
  t.total_pnl = (t.partial_pnl || 0) + finalPnl;
  if (t.auto || t.scalp) {
    const cooldownKey = t.scalp ? "auto_scalp_last_close_" : "auto_last_close_";
    localStorage.setItem(cooldownKey + t.coin + (t.timeframe ? "_" + t.timeframe : ""), Date.now().toString());
  }
  if (t.auto) {
    const pnl = t.total_pnl;
    if (pnl < 0) {
      const streak = parseInt(localStorage.getItem("auto_loss_streak") || "0") + 1;
      localStorage.setItem("auto_loss_streak", streak.toString());
    } else {
      localStorage.setItem("auto_loss_streak", "0");
    }
    const today = new Date().toISOString().slice(0, 10);
    const dailyKey = "auto_daily_pl_" + today;
    const prev = parseFloat(localStorage.getItem(dailyKey) || "0");
    localStorage.setItem(dailyKey, (prev + pnl).toString());
  }
}

function closeTrade(id, price, reason) {
  const trades = store.getTrades();
  const t = trades.find(x => x.id === id);
  if (!t || t.closed_at) return;
  closeTradeInternal(t, price, reason);
  store.setTrades(trades);
  const tag = t.scalp ? `⚡Scalp ${t.timeframe} ` : "";
  toast("SELL", `${tag}${t.coin} closed ${reason} @ ${fmt(price)}`);
}

function closeManual(id) {
  const t = store.getTrades().find(x => x.id === id);
  if (!t) return;
  closeTrade(id, parseFloat(STATE.mids[t.coin] || 0) || t.entry, "manual");
  render();
}

// FIX v6.1: use two fully CLOSED candles (not the forming one) + reject stale cache
function checkMomentumFlip(t) {
  const meta = STATE.coins[t.coin] || {};
  const raw = t.coin.includes(":") ? t.coin.split(":")[1] : t.coin;
  const dex = meta.dex || "";
  const cached = candleCache.get(`${raw}|5m|${dex}`);
  if (!cached || !cached.data || cached.data.length < 20) return false;
  // Reject cache older than 2 minutes — too stale to trust for reversal detection
  if (Date.now() - cached.ts > 2 * 60 * 1000) return false;
  const cs = cached.data;
  // Two most-recent CLOSED candles (the last one, cs[cs.length-1], is currently forming)
  const c1 = cs[cs.length - 2];
  const c2 = cs[cs.length - 3];
  if (!c1 || !c2) return false;
  const baseline = cs.slice(-20, -2);
  const baselineVol = baseline.reduce((s, c) => s + c.v, 0) / baseline.length;
  if (baselineVol <= 0) return false;
  const flipVolOk = (c1.v + c2.v) / 2 > baselineVol * 1.2;
  if (!flipVolOk) return false;
  if (t.side === "LONG") return c1.c < c1.o && c2.c < c2.o && c1.c < c2.c;
  return c1.c > c1.o && c2.c > c2.o && c1.c > c2.c;
}

// v6.1 — REORDERED: stop & TP2 checked BEFORE momentum flip; 10-min grace; per-TF stale timeout
function checkAutoClose() {
  const trades = store.getTrades();
  let changed = false;
  for (const t of trades) {
    if (t.closed_at) continue;
    const live = parseFloat(STATE.mids[t.coin] || 0);
    if (!live) continue;
    const side = t.side || "LONG";
    const entry = t.entry;

    // Ensure initial_risk is set (for v5 trades carried into v6.1)
    if (!t.initial_risk) {
      const fallback = Math.abs(entry - t.stop);
      if (fallback > 0) { t.initial_risk = fallback; changed = true; }
    }
    const initialRisk = t.initial_risk || 0;
    const profitR = initialRisk > 0
      ? (side === "LONG" ? (live - entry) / initialRisk : (entry - live) / initialRisk)
      : 0;

    // ── R-BASED PROGRESSION (only if initial risk is known) ──
    if (initialRisk > 0) {
      // 1. Breakeven at 0.5R (only if not yet hit TP1)
      if (!t.tp1_hit && !t.breakeven_set && profitR >= 0.5) {
        const newStop = entry;
        if ((side === "LONG" && newStop > t.stop) || (side === "SHORT" && newStop < t.stop)) {
          t.stop = newStop;
          t.breakeven_set = true;
          changed = true;
          toast("BUY", `🔒 ${t.coin} stop → breakeven at 0.5R`);
        }
      }

      // 2. Partial TP at 1R — close 50% and lock in profit
      if (!t.tp1_hit && profitR >= 1.0) {
        const tp1Price = side === "LONG" ? entry + initialRisk : entry - initialRisk;
        const halfNotional = t.notional_usd * 0.5;
        const partialPnl = side === "LONG"
          ? (tp1Price - entry) / entry * halfNotional
          : (entry - tp1Price) / entry * halfNotional;
        t.partial_pnl = (t.partial_pnl || 0) + partialPnl;
        t.tp1_hit = true;
        t.tp1_close_price = tp1Price;
        t.notional_usd = t.notional_usd * 0.5;
        t.margin_usd = t.margin_usd * 0.5;
        const trailStop = side === "LONG" ? tp1Price - initialRisk * 0.5 : tp1Price + initialRisk * 0.5;
        if ((side === "LONG" && trailStop > t.stop) || (side === "SHORT" && trailStop < t.stop)) t.stop = trailStop;
        changed = true;
        toast("BUY", `💰 ${t.coin} 50% closed at TP1 (+$${partialPnl.toFixed(2)}) · trailing active`);
      }

      // 3. After TP1, trail stop 0.5R behind price
      if (t.tp1_hit) {
        const trailStop = side === "LONG" ? live - initialRisk * 0.5 : live + initialRisk * 0.5;
        if ((side === "LONG" && trailStop > t.stop) || (side === "SHORT" && trailStop < t.stop)) {
          t.stop = trailStop;
          changed = true;
        }
      }
    }

    // ── DEFINITIVE EXITS FIRST (stop and TP2 before momentum flip) ──
    // 4. STOP HIT — close at t.stop, not live (protects against gaps)
    if (side === "LONG" && live <= t.stop) {
      const reason = t.tp1_hit ? "trail_stop" : (t.breakeven_set ? "breakeven" : "stop");
      closeTradeInternal(t, t.stop, reason);
      const tag = t.scalp ? `⚡Scalp ${t.timeframe} ` : "";
      toast("SELL", `${tag}${t.coin} closed ${reason} @ ${fmt(t.stop)}`);
      changed = true;
      continue;
    }
    if (side === "SHORT" && live >= t.stop) {
      const reason = t.tp1_hit ? "trail_stop" : (t.breakeven_set ? "breakeven" : "stop");
      closeTradeInternal(t, t.stop, reason);
      const tag = t.scalp ? `⚡Scalp ${t.timeframe} ` : "";
      toast("SELL", `${tag}${t.coin} closed ${reason} @ ${fmt(t.stop)}`);
      changed = true;
      continue;
    }

    // 5. TP2 HIT
    if (side === "LONG" && t.tp2 && live >= t.tp2) {
      closeTradeInternal(t, t.tp2, "tp2");
      const tag = t.scalp ? `⚡Scalp ${t.timeframe} ` : "";
      toast("SELL", `${tag}${t.coin} closed tp2 @ ${fmt(t.tp2)}`);
      changed = true;
      continue;
    }
    if (side === "SHORT" && t.tp2 && live <= t.tp2) {
      closeTradeInternal(t, t.tp2, "tp2");
      const tag = t.scalp ? `⚡Scalp ${t.timeframe} ` : "";
      toast("SELL", `${tag}${t.coin} closed tp2 @ ${fmt(t.tp2)}`);
      changed = true;
      continue;
    }

    // ── "SOFT" EXITS (only if trade hasn't hit TP1 yet) ──
    if (t.tp1_hit) continue;
    const openMinutes = (Date.now() - t.opened_at) / 60000;
    const openHours = openMinutes / 60;

    // 6. MOMENTUM FLIP — requires 10-min grace period
    if (openMinutes >= 10 && checkMomentumFlip(t)) {
      closeTradeInternal(t, live, "momentum_flip");
      const tag = t.scalp ? `⚡Scalp ${t.timeframe} ` : "";
      toast("SELL", `${tag}${t.coin} closed momentum_flip @ ${fmt(live)}`);
      changed = true;
      continue;
    }

    // 7. STALE TIMEOUT — per-timeframe threshold
    const scalpStaleHours = t.scalp
      ? ({ "5m": 0.5, "15m": 1, "1h": 3, "4h": 8 }[t.timeframe] || 1)
      : 4;
    if (openHours >= scalpStaleHours && profitR < 0.3) {
      closeTradeInternal(t, live, "stale_timeout");
      const tag = t.scalp ? `⚡Scalp ${t.timeframe} ` : "";
      toast("SELL", `${tag}${t.coin} closed stale_timeout (${scalpStaleHours}h, <0.3R)`);
      changed = true;
      continue;
    }
  }
  if (changed) {
    store.setTrades(trades);
    setTimeout(render, 50);
  }
}

function startAuto() {
  const m = parseFloat($("autoMargin").value);
  const l = Math.min(20, Math.max(1, parseFloat($("autoLev").value) || 3));
  if (!m || m <= 0) return toast("ERR", "enter a margin amount");
  localStorage.setItem("auto_margin", m.toString());
  localStorage.setItem("auto_lev", l.toString());
  localStorage.setItem("auto_enabled", "1");
  localStorage.setItem("auto_loss_streak", "0");
  renderAutoPanel();
  toast("BUY", `🤖 Auto-trading ON · $${m} margin · ${l}x leverage`);
  playBeep();
}
function stopAuto() {
  localStorage.setItem("auto_enabled", "0");
  renderAutoPanel();
  toast("ERR", "Auto-trading OFF — open auto positions remain");
}
function toggleAutoFromHeader() {
  if (localStorage.getItem("auto_enabled") === "1") stopAuto();
  else {
    const panel = $("autoPanel");
    if (panel) panel.scrollIntoView({ behavior: "smooth", block: "start" });
    toast("BUY", "Configure margin/leverage below, then tap Start");
  }
}
function circuitBreakerReason() {
  const streak = parseInt(localStorage.getItem("auto_loss_streak") || "0");
  if (streak >= 3) return `3 consecutive losses`;
  const dailyCapPct = parseFloat(localStorage.getItem("auto_daily_cap_pct") || "10");
  if (dailyCapPct > 0) {
    const today = new Date().toISOString().slice(0, 10);
    const dailyPL = parseFloat(localStorage.getItem("auto_daily_pl_" + today) || "0");
    const cap = parseFloat($("capital")?.value || "10000") * (dailyCapPct / 100);
    if (dailyPL <= -cap) return `Daily loss cap $${cap.toFixed(0)} hit`;
  }
  return null;
}
function correlationBlocks(coin, side) {
  const meta = STATE.coins[coin];
  if (!meta || meta.assetClass !== "CRYPTO") return false;
  const open = store.getTrades().filter(t => !t.closed_at && t.auto && !t.scalp);
  const sameSideCrypto = open.filter(t => {
    const m = STATE.coins[t.coin];
    return m && m.assetClass === "CRYPTO" && t.side === side;
  });
  return sameSideCrypto.length >= 2;
}

function checkAutoTrade() {
  if (localStorage.getItem("auto_enabled") !== "1") return;
  if (STATE.status !== "live") return;
  const cbReason = circuitBreakerReason();
  if (cbReason) {
    localStorage.setItem("auto_enabled", "0");
    renderAutoPanel();
    toast("ERR", `🛑 Auto-trading STOPPED: ${cbReason}`);
    fireNotification("🛑 Auto-trading stopped", { body: cbReason, tag: "cb-stop" });
    return;
  }
  const margin = parseFloat(localStorage.getItem("auto_margin") || "50");
  const leverage = Math.min(20, Math.max(1, parseFloat(localStorage.getItem("auto_lev") || "3")));
  if (!margin || margin <= 0) return;
  let trades = store.getTrades();

  // Close-on-flip (swing trades only)
  for (const t of [...trades]) {
    if (t.closed_at || !t.auto || t.scalp) continue;
    const cur = STATE.coins[t.coin];
    if (!cur) continue;
    const confident = cur.confidence === "CERTAIN" || cur.confidence === "CONFIDENT";
    const flip = confident && ((t.side === "LONG" && cur.signal === "SELL") || (t.side === "SHORT" && cur.signal === "BUY"));
    if (flip) {
      const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
      closeTrade(t.id, live, "auto_flip");
      toast(cur.signal === "SELL" ? "SELL" : "BUY", `🤖 Auto closed ${t.coin} ${t.side} (flipped)`);
    }
  }
  trades = store.getTrades();

  // SWING AUTO
  let autoOpenCount = trades.filter(t => !t.closed_at && t.auto && !t.scalp).length;
  if (autoOpenCount < AUTO_MAX_OPEN) {
    const toOpen = [];
    for (const c of Object.values(STATE.coins)) {
      if (autoOpenCount >= AUTO_MAX_OPEN) break;
      if (!((c.signal === "BUY" || c.signal === "SELL") && (c.confidence === "CERTAIN" || c.confidence === "CONFIDENT"))) continue;
      const already = trades.find(t => !t.closed_at && t.coin === c.coin && !t.scalp);
      if (already) continue;
      const side = c.signal === "BUY" ? "LONG" : "SHORT";
      if (correlationBlocks(c.coin, side)) continue;
      const lastClose = parseInt(localStorage.getItem("auto_last_close_" + c.coin) || "0");
      if (Date.now() - lastClose < AUTO_COOLDOWN_MS) continue;
      const live = parseFloat(STATE.mids[c.coin] || 0) || c.price;
      if (!live) continue;
      let stop, tp2;
      if (side === "LONG") {
        stop = c.stop || live * 0.97; tp2 = c.tp2 || live * 1.03;
        if (stop >= live || tp2 <= live) continue;
      } else {
        stop = c.stop || live * 1.03; tp2 = c.tp2 || live * 0.97;
        if (stop <= live || tp2 >= live) continue;
      }
      toOpen.push({
        id: Date.now() + "-auto-" + Math.random().toString(36).slice(2, 6),
        coin: c.coin, side, entry: live, stop, tp1: (live + tp2) / 2, tp2,
        initial_risk: Math.abs(live - stop),
        margin_usd: margin, notional_usd: margin * leverage, leverage,
        original_margin_usd: margin, original_notional_usd: margin * leverage,
        opened_at: Date.now(), closed_at: null, close_price: null, close_reason: null,
        breakeven_set: false, tp1_hit: false, partial_pnl: 0,
        scalp: false, timeframe: null,
        signal_at_open: c.signal, confidence_at_open: c.confidence, score_at_open: c.score,
        why_at_open: c.why, setup_at_open: c.setup, auto: true, adjustments: []
      });
      autoOpenCount++;
    }
    if (toOpen.length) {
      trades.push(...toOpen);
      store.setTrades(trades);
      for (const t of toOpen) {
        toast(t.side === "LONG" ? "BUY" : "SELL", `🤖 Auto ${t.side} ${t.coin} $${(margin * leverage).toFixed(0)} @ ${fmt(t.entry)}`);
      }
      playBeep();
      if (("Notification" in window) && Notification.permission === "granted") {
        for (const t of toOpen) fireNotification(`🤖 Auto ${t.side} ${t.coin}`, { body: `${t.confidence_at_open} · entry ${fmt(t.entry)}`, tag: `auto-${t.coin}` });
      }
    }
  }

  // AUTO-SCALP
  const scalpMargin = parseFloat(localStorage.getItem("auto_scalp_margin") || localStorage.getItem("auto_margin") || "50");
  const scalpLev = Math.min(20, Math.max(1, parseFloat(localStorage.getItem("auto_scalp_lev") || localStorage.getItem("auto_lev") || "3")));
  let scalpOpenCount = trades.filter(t => !t.closed_at && t.auto && t.scalp).length;
  if (scalpOpenCount < AUTO_SCALP_MAX_OPEN) {
    const candidates = [];
    for (const [coin, perTf] of Object.entries(STATE.scalp)) {
      for (const [tfv, ss] of Object.entries(perTf)) {
        if (ss.confidence !== "HIGH") continue;
        candidates.push(ss);
      }
    }
    candidates.sort((a, b) => {
      const aR = Math.abs(a.entry - a.stop) / a.entry;
      const bR = Math.abs(b.entry - b.stop) / b.entry;
      if (Math.abs(aR - bR) > 0.001) return aR - bR;
      return (b.volR || 0) - (a.volR || 0);
    });
    const toOpen = [];
    for (const ss of candidates) {
      if (scalpOpenCount >= AUTO_SCALP_MAX_OPEN) break;
      const already = trades.find(t => !t.closed_at && t.coin === ss.coin && t.scalp && t.timeframe === ss.timeframe);
      if (already) continue;
      const cooldownKey = "auto_scalp_last_close_" + ss.coin + "_" + ss.timeframe;
      const lastClose = parseInt(localStorage.getItem(cooldownKey) || "0");
      if (Date.now() - lastClose < AUTO_SCALP_COOLDOWN_MS) continue;
      const live = parseFloat(STATE.mids[ss.coin] || 0) || ss.price;
      if (!live) continue;
      if (Math.abs(live - ss.entry) > ss.atr * 0.8) continue;
      const isLong = ss.side === "LONG";
      if (isLong && (ss.stop >= live || ss.tp2 <= live)) continue;
      if (!isLong && (ss.stop <= live || ss.tp2 >= live)) continue;
      toOpen.push({
        id: Date.now() + "-scalp-" + Math.random().toString(36).slice(2, 6),
        coin: ss.coin, side: ss.side, entry: live, stop: ss.stop, tp1: ss.tp1, tp2: ss.tp2,
        initial_risk: Math.abs(live - ss.stop),
        margin_usd: scalpMargin, notional_usd: scalpMargin * scalpLev, leverage: scalpLev,
        original_margin_usd: scalpMargin, original_notional_usd: scalpMargin * scalpLev,
        opened_at: Date.now(), closed_at: null, close_price: null, close_reason: null,
        breakeven_set: false, tp1_hit: false, partial_pnl: 0,
        scalp: true, timeframe: ss.timeframe,
        signal_at_open: ss.signal, confidence_at_open: "HIGH", score_at_open: 100,
        why_at_open: ss.why, setup_at_open: "SCALP", auto: true, adjustments: []
      });
      scalpOpenCount++;
    }
    if (toOpen.length) {
      trades = store.getTrades();
      trades.push(...toOpen);
      store.setTrades(trades);
      for (const t of toOpen) {
        toast(t.side === "LONG" ? "BUY" : "SELL", `⚡ Auto-scalp ${t.timeframe} ${t.coin} ${t.side} @ ${fmt(t.entry)}`);
      }
      playBeep();
      if (("Notification" in window) && Notification.permission === "granted") {
        for (const t of toOpen) fireNotification(`⚡ Scalp ${t.side} ${t.coin} ${t.timeframe}`, { body: `entry ${fmt(t.entry)} · stop ${fmt(t.stop)} · TP2 ${fmt(t.tp2)}`, tag: `scalp-${t.coin}` });
      }
    }
  }
}

function renderAutoPanel() {
  const enabled = localStorage.getItem("auto_enabled") === "1";
  const cfg = $("autoConfig"), run = $("autoRunning"), hdr = $("autoBtn");
  if (!cfg || !run) return;
  if (!$("autoDailyCap")) {
    const capRow = document.createElement("div");
    capRow.className = "exec-row";
    capRow.style.marginTop = "8px";
    capRow.innerHTML = `<label style="min-width:auto">Daily loss cap %</label><input id="autoDailyCap" type="number" value="${localStorage.getItem("auto_daily_cap_pct") || "10"}" min="0" max="100" step="1" inputmode="numeric"><span class="mu" style="font-size:11px;flex:1 1 100%">Auto-pauses if daily realized loss exceeds this % of capital.</span>`;
    const startBtn = cfg.querySelector("button");
    if (startBtn && startBtn.parentNode) startBtn.parentNode.insertBefore(capRow, startBtn);
    else cfg.appendChild(capRow);
    $("autoDailyCap").addEventListener("change", function() {
      localStorage.setItem("auto_daily_cap_pct", this.value);
      toast("BUY", `Daily loss cap: ${this.value || 0}%`);
    });
  }
  let cbStatus = cfg.querySelector(".cb-status");
  if (!cbStatus) {
    cbStatus = document.createElement("div");
    cbStatus.className = "cb-status mu";
    cbStatus.style.cssText = "font-size:11px;margin-top:6px;padding:6px 8px;background:var(--card2);border-radius:6px";
    cfg.appendChild(cbStatus);
  }
  const streak = parseInt(localStorage.getItem("auto_loss_streak") || "0");
  const today = new Date().toISOString().slice(0, 10);
  const dailyPL = parseFloat(localStorage.getItem("auto_daily_pl_" + today) || "0");
  cbStatus.innerHTML = `Loss streak: <b class="${streak >= 2 ? 'dn' : ''}">${streak}/3</b> · Today P/L: <b class="${dailyPL >= 0 ? 'up' : 'dn'}">$${dailyPL.toFixed(2)}</b>`;

  if (enabled) {
    cfg.style.display = "none";
    run.style.display = "block";
    if (hdr) { hdr.textContent = "🤖 ON"; hdr.style.background = "var(--buy)"; hdr.style.color = "#fff"; hdr.style.borderColor = "var(--buy)"; }
    const autoTrades = store.getTrades().filter(t => t.auto);
    const autoOpen = autoTrades.filter(t => !t.closed_at);
    const autoClosed = autoTrades.filter(t => t.closed_at);
    const swingOpen = autoOpen.filter(t => !t.scalp);
    const scalpOpen = autoOpen.filter(t => t.scalp);
    if (autoOpen.length) {
      $("autoLivePositions").innerHTML = `<div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Open auto positions (swing ${swingOpen.length}/${AUTO_MAX_OPEN} · scalp ${scalpOpen.length}/${AUTO_SCALP_MAX_OPEN})</div>` +
        autoOpen.map(t => {
          const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
          const pnl = tradePnl(t, live) + (t.partial_pnl || 0);
          // FIX v6.1: ROE uses total P/L, not just remaining position's P/L
          const roe = tradeMargin(t) > 0 ? pnl / tradeMargin(t) * 100 : 0;
          const beTag = t.breakeven_set ? ' <span class="badge" style="background:#4ea8ff;font-size:10px">🔒 BE</span>' : '';
          const tp1Tag = t.tp1_hit ? ' <span class="badge" style="background:var(--buy);font-size:10px">💰 TP1</span>' : '';
          const scalpTag = t.scalp ? ` <span class="badge" style="background:#f0b429;color:#000;font-size:10px">⚡${t.timeframe}</span>` : '';
          return `<div style="padding:8px 0;border-bottom:1px solid var(--bd);font-size:12px">
            <b>${esc(t.coin)}</b> <span class="badge ${t.side}">${t.side}</span> ${t.leverage}x${beTag}${tp1Tag}${scalpTag}<br>
            <span class="mu">entry ${fmt(t.entry)} · now ${fmt(live)} · stop ${fmt(t.stop)} · TP2 ${fmt(t.tp2)}</span><br>
            <span class="${pnl>=0?'up':'dn'}" style="font-weight:700">Total P/L $${pnl.toFixed(2)} (${roe.toFixed(1)}% ROE)</span>
          </div>`;
        }).join("");
    } else {
      $("autoLivePositions").innerHTML = `<div class="mu">No open auto positions.</div>`;
    }
    if (autoClosed.length) {
      const stats = computeStats(autoClosed);
      if (stats) {
        $("autoStatsBox").innerHTML = `<div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Auto-trade performance (${autoClosed.length} closed)</div>
          <div class="stat-grid">
            <div class="stat-box"><div class="k">Trades</div><div class="v">${stats.trades}</div></div>
            <div class="stat-box"><div class="k">Win rate</div><div class="v ${stats.winRate>=50?'up':'dn'}">${stats.winRate.toFixed(1)}%</div></div>
            <div class="stat-box"><div class="k">Net P/L</div><div class="v ${stats.net>=0?'up':'dn'}">$${fmt2(stats.net)}</div></div>
            <div class="stat-box"><div class="k">Profit factor</div><div class="v ${stats.pf>=1?'up':'dn'}">${isFinite(stats.pf)?stats.pf.toFixed(2):"∞"}</div></div>
            <div class="stat-box"><div class="k">W/L</div><div class="v">${stats.wins}/${stats.losses}</div></div>
            <div class="stat-box"><div class="k">Avg hold</div><div class="v">${(stats.avgHoldMs/3600000).toFixed(1)}h</div></div>
          </div>`;
      }
    } else {
      $("autoStatsBox").innerHTML = `<div class="mu">No closed auto trades yet.</div>`;
    }
  } else {
    cfg.style.display = "block";
    run.style.display = "none";
    if (hdr) { hdr.textContent = "🤖 OFF"; hdr.style.background = ""; hdr.style.color = ""; hdr.style.borderColor = ""; }
    if (!$("autoMargin").value) $("autoMargin").value = localStorage.getItem("auto_margin") || "50";
    if (!$("autoLev").value) $("autoLev").value = localStorage.getItem("auto_lev") || "3";
    if ($("autoDailyCap") && !$("autoDailyCap").value) $("autoDailyCap").value = localStorage.getItem("auto_daily_cap_pct") || "10";
  }
}

function clearAllTrades() {
  if (!confirm("Clear all paper trades?")) return;
  store.setTrades([]);
  localStorage.removeItem("auto_loss_streak");
  const today = new Date().toISOString().slice(0, 10);
  localStorage.removeItem("auto_daily_pl_" + today);
  Object.keys(localStorage).forEach(k => {
    if (k.startsWith("auto_scalp_last_close_")) localStorage.removeItem(k);
    if (k.startsWith("auto_last_close_")) localStorage.removeItem(k);
  });
  STATE.scalp = {};
  toast("ERR", "Cleared");
  render();
}

function showTradeDetail(id) {
  const t = store.getTrades().find(x => x.id === id); if (!t) return;
  const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
  const side = t.side || "LONG";
  const originalMargin = t.original_margin_usd || t.margin_usd || (t.notional_usd / t.leverage);
  const currentMargin = tradeMargin(t);
  const currentNotional = t.notional_usd;
  const currentPnl = tradePnl(t, live);
  const totalPnl = currentPnl + (t.partial_pnl || 0);
  const roe = originalMargin > 0 ? totalPnl / originalMargin * 100 : 0;
  const liq = calcLiq(t.entry, t.leverage, side), distLiq = Math.abs(live - liq) / live * 100;
  const openH = (Date.now() - t.opened_at) / 3600000;
  const riskUsd = side === "LONG" ? (t.entry - t.stop) / t.entry * currentNotional : (t.stop - t.entry) / t.entry * currentNotional;
  const rewardUsd = side === "LONG" ? (t.tp2 - t.entry) / t.entry * currentNotional : (t.entry - t.tp2) / t.entry * currentNotional;
  const beTag = t.breakeven_set ? ' <span class="badge" style="background:#4ea8ff">🔒 BE</span>' : '';
  const tp1Tag = t.tp1_hit ? ' <span class="badge" style="background:var(--buy)">💰 TP1</span>' : '';
  const scalpTag = t.scalp ? ` <span class="badge" style="background:#f0b429;color:#000">⚡${t.timeframe} SCALP</span>` : '';
  let html = `<h3 style="margin:0 0 6px">${esc(t.coin)} <span class="badge ${side}">${side}</span>${t.auto ? ' <span class="badge" style="background:#8b93a1">🤖 AUTO</span>' : ''}${beTag}${tp1Tag}${scalpTag}</h3>
    <div class="mu" style="margin-bottom:8px">${t.leverage}x · ${openH < 1 ? (openH*60).toFixed(0)+"m" : openH.toFixed(1)+"h"} ${t.closed_at ? 'closed' : 'open'}</div>
    <div class="detail-grid">
      <div><span class="k">Original margin</span><span>$${originalMargin.toFixed(2)}</span></div>
      <div><span class="k">${t.tp1_hit ? "Remaining" : "Size"}</span><span>$${currentNotional.toFixed(2)}${t.tp1_hit ? ' <span class="mu" style="font-size:10px">(50%)</span>' : ''}</span></div>
      <div><span class="k">Entry</span><span>${fmt(t.entry)}</span></div>
      <div><span class="k">${t.closed_at ? "Exit" : "Now"}</span><span>${fmt(t.closed_at ? t.close_price : live)}</span></div>
      <div><span class="k">Stop</span><span>${fmt(t.stop)}${t.breakeven_set ? ' 🔒' : ''}</span></div>
      <div><span class="k">TP2</span><span>${fmt(t.tp2)}</span></div>
      <div><span class="k">Liquidation</span><span class="dn">${fmt(liq)}</span></div>
      <div><span class="k">From liq</span><span>${distLiq.toFixed(2)}%</span></div>
      <div><span class="k">Risk $</span><span class="dn">$${riskUsd.toFixed(2)}</span></div>
      <div><span class="k">Reward $</span><span class="up">$${rewardUsd.toFixed(2)}</span></div>
      ${t.tp1_hit ? `<div><span class="k">💰 TP1 partial</span><span class="up">+$${(t.partial_pnl||0).toFixed(2)}</span></div><div><span class="k">Remaining P/L</span><span class="${currentPnl>=0?'up':'dn'}">$${currentPnl.toFixed(2)}</span></div>` : ''}
      <div><span class="k">${t.tp1_hit ? "Total P/L" : "P/L"}</span><span class="${totalPnl>=0?'up':'dn'}">$${totalPnl.toFixed(2)}</span></div>
      <div><span class="k">ROE (on original)</span><span class="${totalPnl>=0?'up':'dn'}">${roe.toFixed(1)}%</span></div>
    </div>`;
  if (t.closed_at && t.close_reason) {
    html += `<div style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Close reason</div>
      <div style="font-size:13px;font-weight:700">${esc(t.close_reason.replace(/_/g, " "))}</div>
    </div>`;
  }
  if (!t.closed_at) {
    html += `<div style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Adjust stop / TP</div>
      <div class="exec-row"><label>Stop</label><input id="editStop" type="number" step="any" value="${t.stop}" style="flex:1"></div>
      <div class="exec-row"><label>TP2</label><input id="editTP2" type="number" step="any" value="${t.tp2}" style="flex:1"></div>
      <button class="btn-ghost" style="width:100%;margin-top:6px" onclick="applyEdits('${t.id}')">Apply</button>
    </div>`;
  }
  if (t.signal_at_open) {
    html += `<div style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Signal when opened</div>
      <div style="margin-bottom:6px"><span class="badge ${t.signal_at_open}">${t.signal_at_open}</span>
        <span class="badge ${t.confidence_at_open||'LOW'}">${t.confidence_at_open||'—'}</span></div>
      <div class="mu" style="line-height:1.55">${esc(t.why_at_open||"")}</div>
    </div>`;
  }
  html += `<div style="display:flex;gap:8px;margin-top:14px">
    ${!t.closed_at ? `<button style="flex:1;padding:12px;background:var(--sell);color:#fff;border:0;border-radius:8px;font-weight:700;font-family:inherit;cursor:pointer" onclick="closeManual('${t.id}');closeModal()">Close</button>` : ''}
    <button style="flex:1;padding:12px;background:var(--bd);color:var(--tx);border:0;border-radius:8px;font-weight:700;font-family:inherit;cursor:pointer" onclick="closeModal()">Dismiss</button>
  </div>`;
  $("modalContent").innerHTML = html;
  $("modal").classList.add("open");
}
function applyEdits(id) {
  const trades = store.getTrades(), t = trades.find(x => x.id === id); if (!t) return;
  const ns = parseFloat($("editStop").value), nt = parseFloat($("editTP2").value);
  const side = t.side || "LONG", errs = [];
  if (!ns || (side === "LONG" && ns >= t.entry) || (side === "SHORT" && ns <= t.entry)) errs.push("bad stop");
  if (!nt || (side === "LONG" && nt <= t.entry) || (side === "SHORT" && nt >= t.entry)) errs.push("bad TP");
  if (errs.length) return toast("ERR", errs.join(", "));
  if (ns !== t.stop) { t.adjustments = t.adjustments || []; t.adjustments.push({at:Date.now(),field:"stop",from:t.stop,to:ns}); t.stop = ns; }
  if (nt !== t.tp2) { t.adjustments = t.adjustments || []; t.adjustments.push({at:Date.now(),field:"tp2",from:t.tp2,to:nt}); t.tp2 = nt; }
  store.setTrades(trades); closeModal(); toast("BUY", `${t.coin} updated`); render();
}
function closeModal() { $("modal").classList.remove("open"); }

// v6.1: uses total_pnl; falls back gracefully for old v5 trades
function computeStats(trades) {
  if (!trades.length) return null;
  const e = trades.map(t => {
    const side = t.side || "LONG";
    const m = tradeMargin(t);
    const n = t.notional_usd;
    let pnl;
    if (t.closed_at && typeof t.total_pnl === "number") {
      pnl = t.total_pnl;
    } else if (t.closed_at) {
      const basePnl = side === "LONG" ? (t.close_price - t.entry) / t.entry * n : (t.entry - t.close_price) / t.entry * n;
      pnl = basePnl + (t.partial_pnl || 0);
    } else {
      pnl = (t.partial_pnl || 0);
    }
    return { ...t, side, pnl, margin: m, notional: n, holdMs: (t.closed_at || 0) - (t.opened_at || 0) };
  });
  const wins = e.filter(t => t.pnl > 0), losses = e.filter(t => t.pnl <= 0);
  const gw = wins.reduce((s, t) => s + t.pnl, 0), gl = losses.reduce((s, t) => s + Math.abs(t.pnl), 0);
  const net = gw - gl;
  const pf = gl > 0 ? gw / gl : (gw > 0 ? Infinity : 0);
  const wr = e.length > 0 ? wins.length / e.length * 100 : 0;
  const sorted = [...e].sort((a, b) => a.closed_at - b.closed_at);
  let cum = 0;
  const curve = sorted.map(t => { cum += t.pnl; return { t: t.closed_at, v: cum }; });
  let peak = 0, dd = 0;
  for (const p of curve) { if (p.v > peak) peak = p.v; const d = peak - p.v; if (d > dd) dd = d; }
  const rev = [...sorted].reverse();
  let streak = 0, st = null;
  for (const t of rev) { const ty = t.pnl > 0 ? "win" : "loss"; if (st === null) { st = ty; streak = 1; } else if (st === ty) streak++; else break; }
  const longs = e.filter(t => t.side === "LONG"), shorts = e.filter(t => t.side === "SHORT");
  const cert = e.filter(t => t.confidence_at_open === "CERTAIN"), conf = e.filter(t => t.confidence_at_open === "CONFIDENT");
  const pulls = e.filter(t => t.setup_at_open === "PULLBACK"), brks = e.filter(t => t.setup_at_open === "BREAKOUT");
  const scalps = e.filter(t => t.scalp);
  const tp1HitCount = e.filter(t => t.tp1_hit).length;
  const reasonBreakdown = {};
  for (const t of e) {
    const r = t.close_reason || "unknown";
    if (!reasonBreakdown[r]) reasonBreakdown[r] = { count: 0, pnl: 0, wins: 0 };
    reasonBreakdown[r].count++;
    reasonBreakdown[r].pnl += t.pnl;
    if (t.pnl > 0) reasonBreakdown[r].wins++;
  }
  const tier = a => ({ count: a.length, winRate: a.length ? a.filter(t => t.pnl > 0).length / a.length * 100 : 0, net: a.reduce((s, t) => s + t.pnl, 0) });
  let vClass = "ok", vTitle = "TOO FEW TRADES", vMsg = "";
  if (e.length < 10) { vMsg = `Only ${e.length} closed trade${e.length===1?"":"s"}. Need 10+ for meaningful stats.`; }
  else if (pf >= 1.5 && wr >= 45 && net > 0) { vClass = "good"; vTitle = "GOOD"; vMsg = "Profitable. The rules are working."; }
  else if (pf >= 1.0 && net > 0) { vTitle = "OK"; vMsg = "Slightly profitable. Consider only CERTAIN signals."; }
  else { vClass = "bad"; vTitle = "NEEDS WORK"; vMsg = "Losing money. Review entries."; }
  return { trades: e.length, wins: wins.length, losses: losses.length, winRate: wr, net, pf,
    avgWin: wins.length ? gw / wins.length : 0, avgLoss: losses.length ? gl / losses.length : 0,
    best: Math.max(...e.map(t => t.pnl)), worst: Math.min(...e.map(t => t.pnl)),
    maxDD: dd, streak, streakType: st, curve, avgHoldMs: e.reduce((s, t) => s + t.holdMs, 0) / e.length,
    longCount: longs.length, shortCount: shorts.length,
    longWins: longs.filter(t => t.pnl > 0).length, shortWins: shorts.filter(t => t.pnl > 0).length,
    longNet: longs.reduce((s, t) => s + t.pnl, 0), shortNet: shorts.reduce((s, t) => s + t.pnl, 0),
    certain: tier(cert), confident: tier(conf), pullback: tier(pulls), breakout: tier(brks), scalp: tier(scalps),
    tp1HitCount, reasonBreakdown,
    vClass, vTitle, vMsg };
}

function svgCurve(curve, w, h) {
  if (!curve || curve.length < 2) return "";
  const vals = curve.map(p => p.v);
  const min = Math.min(...vals, 0), max = Math.max(...vals, 0), range = max - min || 1;
  const pad = 4, iw = w - pad * 2, ih = h - pad * 2, xs = iw / (vals.length - 1);
  const pts = vals.map((v, i) => `${pad + i * xs},${pad + ih - ((v - min) / range) * ih}`).join(" ");
  const color = vals[vals.length-1] >= 0 ? "#2ecc83" : "#ff5d68";
  const zy = pad + ih - ((0 - min) / range) * ih;
  return `<svg viewBox="0 0 ${w} ${h}" preserveAspectRatio="none"><line x1="${pad}" y1="${zy}" x2="${w-pad}" y2="${zy}" stroke="#262c38" stroke-width="1" stroke-dasharray="2,3"/><polyline points="${pts}" fill="none" stroke="${color}" stroke-width="2" vector-effect="non-scaling-stroke"/><circle cx="${pad+(vals.length-1)*xs}" cy="${pad+ih-((vals[vals.length-1]-min)/range)*ih}" r="3.5" fill="${color}"/></svg>`;
}

function exportTradesCSV() {
  const trades = store.getTrades();
  if (!trades.length) return toast("ERR", "No trades to export");
  const headers = ["id","coin","side","auto","scalp","timeframe","entry","stop","tp1","tp2","tp1_hit","tp1_close_price","breakeven_set","original_margin_usd","original_notional_usd","remaining_margin_usd","remaining_notional_usd","leverage","opened_at","closed_at","close_price","close_reason","partial_pnl","final_pnl","total_pnl","signal_at_open","confidence_at_open","score_at_open","setup_at_open"];
  const rows = trades.map(t => {
    return [t.id, t.coin, t.side || "LONG", t.auto ? "yes" : "no", t.scalp ? "yes" : "no", t.timeframe || "",
      t.entry, t.stop, t.tp1 || "", t.tp2, t.tp1_hit ? "yes" : "no", t.tp1_close_price || "",
      t.breakeven_set ? "yes" : "no",
      t.original_margin_usd || t.margin_usd, t.original_notional_usd || t.notional_usd,
      t.margin_usd, t.notional_usd, t.leverage,
      t.opened_at ? new Date(t.opened_at).toISOString() : "",
      t.closed_at ? new Date(t.closed_at).toISOString() : "",
      t.close_price || "", t.close_reason || "",
      t.partial_pnl || 0, t.final_pnl || "", t.total_pnl || "",
      t.signal_at_open || "", t.confidence_at_open || "", t.score_at_open || "", t.setup_at_open || ""
    ].map(v => `"${String(v).replace(/"/g, '""')}"`).join(",");
  });
  const csv = [headers.join(","), ...rows].join("\n");
  const blob = new Blob([csv], { type: "text/csv" });
  const url = URL.createObjectURL(blob);
  const a = document.createElement("a");
  a.href = url;
  a.download = `ca-creative-bot-trades-${new Date().toISOString().slice(0,10)}.csv`;
  document.body.appendChild(a); a.click(); document.body.removeChild(a);
  URL.revokeObjectURL(url);
  toast("BUY", `Exported ${trades.length} trades to CSV`);
}

async function runBacktestOne(coin, days, margin, leverage) {
  const meta = STATE.coins[coin] || {};
  const raw = coin.includes(":") ? coin.split(":")[1] : coin;
  const dex = meta.dex || "";
  const warm = 320, bars = Math.floor(days * 24 * 60 / 5), total = warm + bars;
  const c5 = await fetchCandles(raw, "5m", total, dex);
  const c1h = await fetchCandles(raw, "1h", Math.ceil(total/12) + 50, dex);
  const c4h = await fetchCandles(raw, "4h", Math.ceil(total/48) + 50, dex);
  const c1d = await fetchCandles(raw, "1d", Math.ceil(total/288) + 50, dex);
  if (c5.length < warm + 10) throw new Error("not enough history");
  const trades = []; let open = null;
  for (let i = warm; i < c5.length - 1; i++) {
    const bar = c5[i], tClose = bar.t + IV_MS["5m"];
    const s5 = c5.slice(0, i + 1), s1h = c1h.filter(x => x.T <= tClose), s4h = c4h.filter(x => x.T <= tClose), s1d = c1d.filter(x => x.T <= tClose);
    if (!s1h.length || !s4h.length) continue;
    const cbt = { "5m": s5, "1h": s1h, "4h": s4h, "1d": s1d };
    if (s5.length >= 30) {
      const m15 = [];
      for (let j = 0; j + 2 < s5.length; j += 3) m15.push({ t: s5[j].t, T: s5[j+2].T, o: s5[j].o, h: Math.max(s5[j].h,s5[j+1].h,s5[j+2].h), l: Math.min(s5[j].l,s5[j+1].l,s5[j+2].l), c: s5[j+2].c, v: s5[j].v+s5[j+1].v+s5[j+2].v });
      cbt["15m"] = m15;
    }
    const sig = signalFrom(cbt, bar.c, null);
    if (sig && (sig.signal === "BUY" || sig.signal === "SELL") && (sig.confidence === "CERTAIN" || sig.confidence === "CONFIDENT") && !open) {
      const nb = c5[i + 1]; if (!nb) break;
      const side = sig.signal === "BUY" ? "LONG" : "SHORT";
      open = { id: i, coin, side, entry: nb.o, stop: sig.stop || nb.o * (side === "LONG" ? 0.97 : 1.03), tp2: sig.tp2 || nb.o * (side === "LONG" ? 1.03 : 0.97), opened_at: nb.t,
        margin_usd: margin, notional_usd: margin * leverage, leverage, confidence_at_open: sig.confidence, setup_at_open: sig.setup, closed_at: null, close_price: null, close_reason: null };
    }
    if (open) {
      const sHit = open.side === "LONG" ? bar.l <= open.stop : bar.h >= open.stop;
      const tHit = open.side === "LONG" ? bar.h >= open.tp2 : bar.l <= open.tp2;
      if (sHit) { open.closed_at = bar.t; open.close_price = open.stop; open.close_reason = "stop"; trades.push(open); open = null; }
      else if (tHit) { open.closed_at = bar.t; open.close_price = open.tp2; open.close_reason = "tp2"; trades.push(open); open = null; }
    }
  }
  if (open) { open.closed_at = c5[c5.length-1].T; open.close_price = c5[c5.length-1].c; open.close_reason = "end"; trades.push(open); }
  return { coin, windowDays: days, stats: computeStats(trades), trades };
}

function renderBacktestResult(r) {
  const el = $("btResults");
  if (!r) { el.innerHTML = ""; return; }
  const s = r.stats;
  if (!s) { el.innerHTML = `<div class="mu">No signals in the ${r.windowDays}-day window.</div>`; return; }
  let warn = "";
  if (s.trades < 20) warn = `<div class="mu" style="color:var(--wait);font-weight:700;margin-bottom:8px">⚠ Too few trades — not statistically meaningful yet</div>`;
  el.innerHTML = `${warn}
    <div class="mu" style="font-size:11px;padding:8px;background:var(--card2);border-radius:6px;margin-bottom:10px;line-height:1.5">
      <b>Backtest is conservative:</b> only models stop-loss and TP2 hit-or-miss. Live trade engine adds partial TP1 (50% at 1R), breakeven at 0.5R, trailing stop after TP1, momentum-flip exit, and stale timeout — none of which are modeled here. Actual live results should be equal or better than this backtest if the engine is working. Slippage, fees, funding not modeled. Past ≠ future.
    </div>
    <div class="stat-grid">
      <div class="stat-box"><div class="k">Trades</div><div class="v">${s.trades}</div></div>
      <div class="stat-box"><div class="k">Win rate</div><div class="v ${s.winRate>=50?'up':'dn'}">${s.winRate.toFixed(1)}%</div></div>
      <div class="stat-box"><div class="k">Net P/L</div><div class="v ${s.net>=0?'up':'dn'}">$${fmt2(s.net)}</div></div>
      <div class="stat-box"><div class="k">Profit factor</div><div class="v ${s.pf>=1?'up':'dn'}">${isFinite(s.pf)?s.pf.toFixed(2):"∞"}</div></div>
      <div class="stat-box"><div class="k">Best</div><div class="v up">$${fmt2(s.best)}</div></div>
      <div class="stat-box"><div class="k">Worst</div><div class="v dn">$${fmt2(s.worst)}</div></div>
      <div class="stat-box"><div class="k">Max DD</div><div class="v dn">$${fmt2(s.maxDD)}</div></div>
      <div class="stat-box"><div class="k">W/L</div><div class="v">${s.wins}/${s.losses}</div></div>
    </div>
    <div style="margin-top:10px">${svgCurve(s.curve, 600, 100)}</div>
    <div class="side-row">
      <div class="side-box"><b>CERTAIN</b><br>${s.certain.count} · ${s.certain.winRate.toFixed(0)}% win<br><span class="${s.certain.net>=0?'up':'dn'}">$${fmt2(s.certain.net)}</span></div>
      <div class="side-box"><b>CONFIDENT</b><br>${s.confident.count} · ${s.confident.winRate.toFixed(0)}% win<br><span class="${s.confident.net>=0?'up':'dn'}">$${fmt2(s.confident.net)}</span></div>
    </div>`;
}

async function runBacktest() {
  const coin = $("btCoin").value;
  if (!coin) return toast("ERR", "pick an asset");
  const days = parseInt($("btWindow").value), margin = parseFloat($("btMargin").value), leverage = Math.min(20, Math.max(1, parseFloat($("btLev").value) || 3));
  $("btProgress").style.display = "block"; $("btProgressText").textContent = `Running ${coin}...`; $("btResults").innerHTML = "";
  try {
    const r = await runBacktestOne(coin, days, margin, leverage);
    store.setBtLast(r); renderBacktestResult(r);
    toast("BUY", `Backtest done: ${r.stats ? r.stats.trades + " trades" : "no signals"}`);
  } catch(e) { toast("ERR", e.message); }
  finally { $("btProgress").style.display = "none"; }
}

function toggleBacktest() {
  const b = $("backtestBody"), t = $("backtestToggle");
  const hidden = b.style.display === "none";
  b.style.display = hidden ? "block" : "none";
  t.textContent = hidden ? "▲" : "▼";
}

function renderScalpPanel() {
  let el = document.getElementById("scalpPanel");
  if (!el) {
    el = document.createElement("section");
    el.id = "scalpPanel";
    el.className = "card";
    const newsAnchor = document.getElementById("newsPanel") || $("signalCard");
    if (newsAnchor && newsAnchor.parentNode) newsAnchor.parentNode.insertBefore(el, newsAnchor.nextSibling);
    else document.body.appendChild(el);
  }
  if (!currentCoin) {
    el.innerHTML = `<h2>⚡ Scalp signals</h2><div class="mu">Select a coin to see per-timeframe scalp setups.</div>`;
    return;
  }
  const perTf = STATE.scalp[currentCoin] || {};
  const coinsWithScalp = Object.keys(STATE.scalp).length;
  let rows = "";
  for (const tfv of SCALP_TFS) {
    const ss = perTf[tfv];
    if (!ss) {
      rows += `<div class="pos-item" style="cursor:default;padding:8px 0">
        <div><b style="color:var(--mu)">${tfv}</b> <span class="mu">— no setup right now</span></div>
      </div>`;
      continue;
    }
    const side = ss.side;
    const badge = `<span class="badge ${side === "LONG" ? "BUY" : "SELL"}">${ss.signal}</span>`;
    const tierBadge = ss.confidence === "HIGH"
      ? `<span class="badge" style="background:var(--buy)">HIGH</span>`
      : `<span class="badge" style="background:#4ea8ff">MED</span>`;
    const entry = ss.entry, stop = ss.stop, tp1 = ss.tp1, tp2 = ss.tp2;
    const pct = (t) => ((t - entry) / entry * 100).toFixed(2);
    const riskPct = Math.abs(((stop - entry) / entry) * 100).toFixed(2);
    const rr = (Math.abs(tp2 - entry) / Math.abs(stop - entry)).toFixed(1);
    rows += `<div style="padding:10px 0;border-bottom:1px solid var(--bd)">
      <div style="display:flex;align-items:center;gap:6px;flex-wrap:wrap;margin-bottom:6px">
        <b>${tfv}</b> ${badge} ${tierBadge}
        <span class="mu">${ss.volR.toFixed(1)}x vol · RSI ${ss.rsi.toFixed(0)} · R:R ${rr}</span>
      </div>
      <div style="font-size:12px;color:var(--mu);line-height:1.5;margin-bottom:6px">${esc(ss.why)}</div>
      <div style="display:grid;grid-template-columns:repeat(4,1fr);gap:6px;font-size:12px">
        <div><div class="mu" style="font-size:10px;text-transform:uppercase">Entry</div><b>$${fmt(entry)}</b></div>
        <div><div class="mu" style="font-size:10px;text-transform:uppercase">Stop</div><b class="dn">$${fmt(stop)}</b><div class="mu" style="font-size:10px">${riskPct}%</div></div>
        <div><div class="mu" style="font-size:10px;text-transform:uppercase">TP1 (50%)</div><b class="up">$${fmt(tp1)}</b><div class="mu" style="font-size:10px">${pct(tp1)}%</div></div>
        <div><div class="mu" style="font-size:10px;text-transform:uppercase">TP2</div><b class="up">$${fmt(tp2)}</b><div class="mu" style="font-size:10px">${pct(tp2)}%</div></div>
      </div>
      <button class="btn-ghost" style="width:100%;margin-top:8px;background:${side === "LONG" ? "var(--buy)" : "var(--sell)"};color:#fff;font-weight:700;border:0" onclick="executeScalpFromPanel('${esc(currentCoin)}','${tfv}')">⚡ Take this scalp (${side})</button>
    </div>`;
  }
  el.innerHTML = `<h2>⚡ Scalp signals — ${esc(currentCoin)} <span class="mu" style="font-size:11px;text-transform:none;letter-spacing:0">· ${coinsWithScalp} coins active</span></h2>${rows}`;
}

function executeScalpFromPanel(coin, tfv) {
  const ss = (STATE.scalp[coin] || {})[tfv];
  if (!ss) return toast("ERR", "Scalp expired — wait for next refresh");
  const live = parseFloat(STATE.mids[coin] || 0) || ss.price;
  if (!live) return toast("ERR", "No live price");
  const margin = parseFloat($("execSize").value) || 100;
  const lev = Math.min(20, Math.max(1, parseFloat($("execLev").value) || 3));
  executeTrade(ss.side, {
    coin, timeframe: tfv, side: ss.side, entry: ss.entry, stop: ss.stop, tp1: ss.tp1, tp2: ss.tp2,
    margin, leverage: lev
  });
}

function getSeenNewsHash() {
  try { return JSON.parse(localStorage.getItem("news_seen_hash") || "[]"); } catch { return []; }
}
function setSeenNewsHash(arr) {
  localStorage.setItem("news_seen_hash", JSON.stringify(arr.slice(-100)));
}
function newsHashOf(h) { return String(h.link || h.title || "").slice(0, 80); }

function renderNewsPanel() {
  let el = document.getElementById("newsPanel");
  if (!el) {
    el = document.createElement("section");
    el.id = "newsPanel";
    el.className = "card";
    const anchor = $("signalCard");
    if (anchor && anchor.parentNode) anchor.parentNode.insertBefore(el, anchor.nextSibling);
  }
  const c = currentCoin ? STATE.coins[currentCoin] : null;
  const sym = c ? (c.coin.includes(":") ? c.coin.split(":")[1] : c.coin) : "";
  const related = (STATE.news.perTicker[sym] || []).slice(0, 4);
  const pool = related.length ? related : [...STATE.news.crypto.slice(0, 4), ...STATE.news.general.slice(0, 3)];
  const seen = new Set(), top = [];
  for (const h of pool) { if (!seen.has(h.title)) { seen.add(h.title); top.push(h); if (top.length >= 6) break; } }

  const folded = localStorage.getItem("news_folded") === "1";
  const seenHash = getSeenNewsHash();
  const seenSet = new Set(seenHash);
  const unseenCount = top.filter(h => !seenSet.has(newsHashOf(h))).length;

  if (!top.length) {
    el.innerHTML = `<h2 onclick="toggleNewsFold()" style="cursor:pointer;display:flex;justify-content:space-between;align-items:center;margin:0">
      <span>News pulse</span><span id="newsToggle">${folded ? "▶" : "▼"}</span></h2>
      <div id="newsBody" style="margin-top:10px;${folded ? 'display:none;' : ''}"><div class="mu">No headlines yet — refreshing every 15 min.</div></div>`;
    return;
  }
  const avg = top.reduce((s, h) => s + scoreHeadline(h.title), 0) / top.length;
  const tone = avg > 0.3 ? "up" : avg < -0.3 ? "dn" : "mu";
  const label = avg > 0.3 ? "Bullish" : avg < -0.3 ? "Bearish" : "Mixed";
  const srcLabel = related.length ? "per-ticker" : (c && c.assetClass === "CRYPTO" ? "crypto feed" : "macro feed");
  const newBadge = unseenCount > 0
    ? ` <span style="background:var(--sell);color:#fff;font-size:10px;padding:1px 6px;border-radius:8px;margin-left:6px;font-weight:700">🔴 ${unseenCount} NEW</span>`
    : "";
  el.innerHTML = `<h2 onclick="toggleNewsFold()" style="cursor:pointer;display:flex;justify-content:space-between;align-items:center;margin:0">
      <span>News pulse${newBadge} <span class="${tone}" style="font-size:11px;text-transform:none;letter-spacing:0;font-weight:400">${label} · ${srcLabel}</span></span>
      <span id="newsToggle">${folded ? "▶" : "▼"}</span>
    </h2>
    <div id="newsBody" style="margin-top:10px;${folded ? 'display:none;' : ''}">
      ${top.map(h => {
        const isNew = !seenSet.has(newsHashOf(h));
        const newDot = isNew ? ' <span style="display:inline-block;width:6px;height:6px;border-radius:50%;background:var(--sell);margin-left:4px"></span>' : '';
        return `<div style="padding:6px 0;border-bottom:1px solid var(--bd);font-size:12px;line-height:1.45">
          <a href="${esc(h.link || "#")}" target="_blank" rel="noopener" style="color:var(--tx);text-decoration:none">${esc(h.title)}${newDot}</a>
          <div class="mu" style="font-size:10px;margin-top:2px">${esc(h.source || "")}${h.pubDate ? " · " + new Date(h.pubDate).toLocaleString() : ""}</div>
        </div>`;
      }).join("")}
    </div>`;
}

function toggleNewsFold() {
  const body = document.getElementById("newsBody");
  const tog = document.getElementById("newsToggle");
  if (!body || !tog) return;
  const hidden = body.style.display === "none";
  body.style.display = hidden ? "block" : "none";
  tog.textContent = hidden ? "▼" : "▶";
  localStorage.setItem("news_folded", hidden ? "0" : "1");
  if (hidden) {
    const c = currentCoin ? STATE.coins[currentCoin] : null;
    const sym = c ? (c.coin.includes(":") ? c.coin.split(":")[1] : c.coin) : "";
    const related = (STATE.news.perTicker[sym] || []).slice(0, 4);
    const pool = related.length ? related : [...STATE.news.crypto.slice(0, 4), ...STATE.news.general.slice(0, 3)];
    const hashes = pool.map(newsHashOf);
    const seenHash = getSeenNewsHash();
    setSeenNewsHash([...seenHash, ...hashes]);
    renderNewsPanel();
  }
}

function renderOrderBookBar() {
  if (currentCoin && STATE.coins[currentCoin]) renderSignalCard(STATE.coins[currentCoin]);
}

let swReg = null;
if ("serviceWorker" in navigator) navigator.serviceWorker.register("sw.js").then(() => navigator.serviceWorker.ready.then(r => { swReg = r; })).catch(() => {});
function requestNotifPerm() {
  if (!("Notification" in window)) return toast("ERR", "not supported");
  Notification.requestPermission().then(p => {
    if (p === "granted") { toast("BUY", "Alerts on"); $("notifBtn").textContent = "🔔 On"; }
    else toast("ERR", "Denied — enable in browser settings");
  });
}
if ("Notification" in window) {
  if (Notification.permission === "granted") { $("notifBtn").textContent = "🔔 On"; }
  else if (Notification.permission === "denied") { $("notifBtn").textContent = "🔕 Blocked"; }
  else { $("notifBtn").textContent = "🔔 Alerts"; }
} else { $("notifBtn").textContent = "🔕 N/A"; $("notifBtn").disabled = true; }

function fireNotification(title, opts) {
  try { if (swReg?.showNotification) swReg.showNotification(title, opts); else if (Notification.permission === "granted") new Notification(title, opts); } catch(e) {}
}

let audioCtx = null;
function toggleSound() {
  const on = localStorage.getItem("sound_on") === "1";
  localStorage.setItem("sound_on", on ? "0" : "1");
  updateSoundBtn();
  toast(on ? "ERR" : "BUY", on ? "Sound alerts OFF" : "Sound alerts ON");
}
function updateSoundBtn() {
  const on = localStorage.getItem("sound_on") === "1";
  const b = $("soundBtn");
  if (b) b.textContent = on ? "🔊" : "🔇";
}
function playBeep() {
  if (localStorage.getItem("sound_on") !== "1") return;
  try {
    if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
    if (audioCtx.state === "suspended") audioCtx.resume();
    const osc = audioCtx.createOscillator();
    const gain = audioCtx.createGain();
    osc.connect(gain); gain.connect(audioCtx.destination);
    osc.frequency.value = 880;
    gain.gain.setValueAtTime(0.15, audioCtx.currentTime);
    gain.gain.exponentialRampToValueAtTime(0.001, audioCtx.currentTime + 0.3);
    osc.start(); osc.stop(audioCtx.currentTime + 0.35);
  } catch(e) {}
}

function applyTheme() {
  const pref = localStorage.getItem("theme_pref") || "auto";
  let theme = pref;
  if (pref === "auto") theme = window.matchMedia("(prefers-color-scheme: dark)").matches ? "dark" : "light";
  document.documentElement.setAttribute("data-theme", theme);
  const btn = $("themeBtn");
  if (btn) {
    btn.textContent = pref === "auto" ? "⚙️" : (pref === "light" ? "☀️" : "🌙");
    btn.title = `Theme: ${pref === "auto" ? "follows device" : pref}`;
  }
  if (chart) {
    const card = getComputedStyle(document.documentElement).getPropertyValue("--card").trim() || "#171b24";
    const tx = getComputedStyle(document.documentElement).getPropertyValue("--tx").trim() || "#e8ebf2";
    const bd = getComputedStyle(document.documentElement).getPropertyValue("--bd").trim() || "#262c38";
    chart.applyOptions({
      layout: { background: { color: card }, textColor: tx },
      grid: { vertLines: { color: bd }, horzLines: { color: bd } },
      timeScale: { borderColor: bd },
      rightPriceScale: { borderColor: bd }
    });
  }
}
function cycleTheme() {
  const cur = localStorage.getItem("theme_pref") || "auto";
  const next = cur === "auto" ? "light" : (cur === "light" ? "dark" : "auto");
  localStorage.setItem("theme_pref", next);
  applyTheme();
  toast("BUY", `Theme: ${next === "auto" ? "auto (device)" : next}`);
}
window.matchMedia("(prefers-color-scheme: dark)").addEventListener("change", () => {
  if ((localStorage.getItem("theme_pref") || "auto") === "auto") applyTheme();
});

function toggleStats() {
  const b = $("statsBody"), t = $("statsToggle");
  const hidden = b.style.display === "none";
  b.style.display = hidden ? "block" : "none";
  t.textContent = hidden ? "▼" : "▲";
  localStorage.setItem("stats_folded", hidden ? "0" : "1");
}

function copyTradeDetails(coin) {
  const c = STATE.coins[coin];
  if (!c || c.signal !== "BUY") return toast("ERR", "No BUY signal to copy");
  const text = `${coin} LONG\nEntry: $${fmt(c.entry)}\nStop: $${fmt(c.stop)}\nTP1 (50%): $${fmt(c.tp1)}\nTP2: $${fmt(c.tp2)}\nConfidence: ${c.confidence}\nScore: ${c.score}\nExit plan: 50% close at TP1 → stop to breakeven → trail remaining 50%`;
  if (navigator.clipboard && navigator.clipboard.writeText) {
    navigator.clipboard.writeText(text).then(() => toast("BUY", "Trade details copied to clipboard"));
  } else {
    const ta = document.createElement("textarea");
    ta.value = text;
    document.body.appendChild(ta);
    ta.select();
    document.execCommand("copy");
    document.body.removeChild(ta);
    toast("BUY", "Trade details copied to clipboard");
  }
}

let signalsInit = false;
function checkSignalTransitions(coins) {
  const last = store.getLastSignals(), lastC = store.getLastConf();
  if (!signalsInit) { for (const c of coins) { last[c.coin] = c.signal; lastC[c.coin] = c.confidence; } store.setLastSignals(last); store.setLastConf(lastC); signalsInit = true; return; }
  const can = ("Notification" in window) && Notification.permission === "granted";
  const hist = store.getHistory();
  for (const c of coins) {
    const p = last[c.coin], pc = lastC[c.coin];
    if (p && p !== c.signal) {
      if (!hist[c.coin]) hist[c.coin] = [];
      hist[c.coin].unshift({ ts: Date.now(), from: p, to: c.signal, price: c.price, conf: c.confidence });
      if (hist[c.coin].length > 10) hist[c.coin].length = 10;
      if (can && c.signal === "BUY") {
        fireNotification(`🟢 BUY ${c.coin}`, { body: `${c.confidence} · entry ${fmt(c.entry)}`, tag: `b-${c.coin}` });
        playBeep();
      } else if (can && c.signal === "SELL") {
        fireNotification(`🔴 SELL ${c.coin}`, { body: `${c.confidence} · score ${c.score}`, tag: `s-${c.coin}` });
        playBeep();
      }
    } else if (can && p === "BUY" && pc === "CONFIDENT" && c.confidence === "CERTAIN") {
      fireNotification(`⬆️ ${c.coin} now CERTAIN`, { body: "Confidence upgraded", tag: `u-${c.coin}` });
      playBeep();
    }
    last[c.coin] = c.signal; lastC[c.coin] = c.confidence;
  }
  store.setLastSignals(last); store.setLastConf(lastC); store.setHistory(hist);
}

function toast(kind, msg) {
  const d = document.createElement("div"); d.className = "t " + kind;
  d.innerHTML = "<b>" + esc(kind) + "</b> " + esc(msg);
  $("toast").appendChild(d);
  setTimeout(() => { d.style.opacity = 0; setTimeout(() => d.remove(), 300); }, 5000);
}

function renderTfTabs() { $("tfTabs").innerHTML = Object.keys(IV_MS).map(iv => `<button class="${iv===currentIv?"on":""}" onclick="switchIv('${iv}')">${iv}</button>`).join(""); }
function switchIv(iv) { currentIv = iv; renderTfTabs(); loadCandles(currentCoin, currentIv); renderScalpPanel(); }

function renderAssetTabs() {
  const c = { ALL: 0, CRYPTO: 0, STOCK: 0, COMMODITY: 0 };
  for (const x of Object.values(STATE.coins)) { c.ALL++; if (c[x.assetClass] != null) c[x.assetClass]++; }
  $("assetTabs").innerHTML = [
    { id: "ALL", label: `All (${c.ALL})` },
    { id: "CRYPTO", label: `Crypto (${c.CRYPTO})` },
    { id: "STOCK", label: `Stocks (${c.STOCK})` },
    { id: "COMMODITY", label: `Commodities (${c.COMMODITY})` }
  ].map(t => `<button class="${assetFilter===t.id?'on':''}" onclick="setAssetFilter('${t.id}')">${t.label}</button>`).join("");
}
function setAssetFilter(f) { assetFilter = f; renderAssetTabs(); renderWatchlist(); }

function refreshCoinSelects() {
  const coins = STATE.watchlist.map(c => STATE.coins[c]).filter(Boolean);
  const html = coins.map(c => `<option value="${esc(c.coin)}">${esc(c.coin)} — ${c.signal} (${c.score||0})</option>`).join("");
  const sel = $("execCoin"), cur = sel.value || currentCoin || "";
  if (sel.innerHTML !== html) { sel.innerHTML = html; if (Array.from(sel.options).some(o => o.value === cur)) sel.value = cur; else if (coins.length) sel.value = coins[0].coin; }
  const bt = $("btCoin"), curB = bt.value || currentCoin || "";
  if (bt.innerHTML !== html) { bt.innerHTML = html; if (Array.from(bt.options).some(o => o.value === curB)) bt.value = curB; else if (coins.length) bt.value = coins[0].coin; }
}

function updateExecPreview() {
  const m = parseFloat($("execSize").value) || 0;
  const l = Math.min(20, Math.max(1, parseFloat($("execLev").value) || 1));
  $("notionalPreview").textContent = `Notional: $${(m*l).toFixed(2)} (${l}x)`;
  const coin = $("execCoin").value;
  const live = parseFloat(STATE.mids[coin] || 0) || (STATE.coins[coin]?.price || 0);
  if (live > 0) $("liqPreview").textContent = `Liq: LONG ${fmt(calcLiq(live, l, "LONG"))} · SHORT ${fmt(calcLiq(live, l, "SHORT"))}`;
  else $("liqPreview").textContent = "—";
}

function renderSignalCard(c) {
  const el = $("signalCard");
  const live = parseFloat(STATE.mids[c.coin] || 0) || c.price;
  const sig = c.signal;
  let actClass, icon, headline;
  if (sig === "BUY") { actClass = "act-buy"; icon = "🟢"; headline = "BUY NOW"; }
  else if (sig === "SELL") { actClass = "act-sell"; icon = "🔴"; headline = "SELL NOW / STAY OUT"; }
  else if (sig === "WAIT") { actClass = "act-wait"; icon = "🟡"; headline = "DON'T BUY YET — WAIT"; }
  else { actClass = "act-neutral"; icon = "⚪"; headline = "NO ACTION — WAIT"; }
  let priceBlock = "";
  const pct = (t) => ((t - live) / live * 100).toFixed(2);
  if (sig === "BUY" && c.entry) {
    priceBlock = `<div class="action-price">Buy at $${fmt(c.entry)}</div>
      <div class="action-levels">
        <div><div class="lbl">Stop loss</div><div class="val dn">$${fmt(c.stop)} (${pct(c.stop)}%)</div></div>
        <div><div class="lbl">TP1 · 50% exit</div><div class="val up">$${fmt(c.tp1)} (+${pct(c.tp1)}%)</div></div>
        <div><div class="lbl">TP2</div><div class="val up">$${fmt(c.tp2)} (+${pct(c.tp2)}%)</div></div>
        <div><div class="lbl">Current price</div><div class="val">$${fmt(live)}</div></div>
      </div>
      <div class="action-instruction">Exit plan: 50% closes at TP1 (+1R) → stop moves to breakeven → remaining 50% trails 0.5R behind price until TP2 or stop. Breakeven auto-triggers at 0.5R.</div>`;
  } else if (sig === "SELL") {
    priceBlock = `<div class="action-price">$${fmt(live)}</div>
      <div class="action-levels">
        <div><div class="lbl">Action</div><div class="val dn">Sell / stay out</div></div>
        <div><div class="lbl">Do not buy above</div><div class="val">$${fmt(live * 1.01)}</div></div>
      </div>`;
  } else if (sig === "WAIT" && c.entryZone) {
    const dist = ((c.entryZone - live) / live * 100).toFixed(2);
    const dir = dist < 0 ? "lower" : "higher";
    priceBlock = `<div class="action-price">Wait for $${fmt(c.entryZone)}</div>
      <div class="action-levels">
        <div><div class="lbl">Current price</div><div class="val">$${fmt(live)}</div></div>
        <div><div class="lbl">Wait for</div><div class="val">$${fmt(c.entryZone)} (${Math.abs(dist)}% ${dir})</div></div>
      </div>`;
  } else {
    priceBlock = `<div class="action-price">$${fmt(live)}</div>
      <div class="action-levels">
        <div><div class="lbl">Position</div><div class="val">No trade</div></div>
        <div><div class="lbl">Wait for</div><div class="val">Clear signal</div></div>
      </div>`;
  }
  let obBlock = "";
  const book = STATE.bookCache[c.coin];
  if (book && book.imbalance) {
    const imb = book.imbalance;
    const pctv = (imb * 100).toFixed(1);
    const side = imb > 0.55 ? "BUYERS in control" : imb < 0.45 ? "SELLERS in control" : "balanced";
    const color = imb > 0.55 ? "var(--buy)" : imb < 0.45 ? "var(--sell)" : "var(--mu)";
    const barW = Math.abs(imb - 0.5) * 200;
    obBlock = `<div class="action-instruction" style="margin-top:14px;padding:10px;background:var(--card2);border-radius:8px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;margin-bottom:6px">Live order flow (top 20 levels)</div>
      <div style="display:flex;align-items:center;gap:8px">
        <span style="color:${color};font-weight:700">${pctv}% bids</span>
        <span class="mu">· ${side}</span>
      </div>
      <div style="height:6px;background:var(--bd);border-radius:3px;margin-top:6px;position:relative;overflow:hidden">
        <div style="position:absolute;left:50%;top:0;bottom:0;width:${barW}%;background:${color};transform:translateX(${imb > 0.5 ? '0' : '-100%'})"></div>
        <div style="position:absolute;left:50%;top:0;bottom:0;width:1px;background:var(--tx)"></div>
      </div>
      <div class="mu" style="font-size:10px;margin-top:6px">Bid depth $${(book.bidDepth/1e6).toFixed(2)}M · Ask depth $${(book.askDepth/1e6).toFixed(2)}M</div>
    </div>`;
  }
  let newsBlock = "";
  const newsObj = STATE.news.sentiment[c.coin];
  if (newsObj) {
    const nScore = typeof newsObj === "object" ? newsObj.score : 0;
    const nSrc = typeof newsObj === "object" ? newsObj.src : "none";
    if (nSrc !== "none" && Math.abs(nScore) > 0.2) {
      const tone = nScore > 0.4 ? "Bullish" : nScore < -0.4 ? "Bearish" : "Mixed";
      const cls = nScore > 0.4 ? "up" : nScore < -0.4 ? "dn" : "mu";
      const srcLabel = nSrc === "ticker" ? "per-ticker" : nSrc === "crypto" ? "crypto feed" : "macro feed";
      const vetos = nSrc === "ticker" || c.assetClass === "CRYPTO";
      newsBlock = `<div class="action-instruction" style="margin-top:10px;padding:8px 10px;background:var(--card2);border-radius:8px;font-size:12px">
        <b>News:</b> <span class="${cls}">${tone}</span> (${nScore.toFixed(2)}) · <span class="mu">${srcLabel}${vetos ? "" : " (informational)"}</span>
      </div>`;
    }
  }
  let reasonsBlock = "";
  if (c.why) {
    reasonsBlock = `<div class="action-instruction" style="margin-top:14px;padding-top:12px;border-top:1px solid var(--bd)"><b style="color:var(--tx)">Why the bot thinks this:</b><br>${esc(c.why)}</div>`;
  }
  let copyBtn = "";
  if (sig === "BUY") {
    copyBtn = `<button class="action-copy" onclick="copyTradeDetails('${esc(c.coin)}')">📋 Copy trade details</button>`;
  }
  const openPos = store.getTrades().find(t => !t.closed_at && t.coin === c.coin);
  let closeBtn = "";
  if (openPos) {
    const side = openPos.side || "LONG";
    closeBtn = `<button class="action-copy" style="margin-top:8px;background:var(--sell);color:#fff;border-color:var(--sell)" onclick="closeManual('${openPos.id}')">Close my ${side} position</button>`;
  }
  let historyBlock = "";
  const hist = store.getHistory()[c.coin] || [];
  if (hist.length) {
    historyBlock = `<div style="margin-top:14px;padding-top:12px;border-top:1px solid var(--bd)">
      <div class="mu" style="font-size:11px;text-transform:uppercase;letter-spacing:.04em;margin-bottom:6px">Recent signal changes</div>
      ${hist.slice(0,5).map(h => {
        const ago = Math.round((Date.now() - h.ts) / 60000);
        const agoStr = ago < 1 ? "just now" : (ago < 60 ? ago + "m ago" : Math.round(ago/60) + "h ago");
        return `<div style="font-size:12px;padding:3px 0;color:var(--mu)">${agoStr}: ${h.from} → <b style="color:var(--tx)">${h.to}</b> @ $${fmt(h.price)}</div>`;
      }).join("")}
    </div>`;
  }
  el.className = `card action-card ${actClass}`;
  el.innerHTML = `<div class="action-title">${icon} ${headline}</div>${priceBlock}${obBlock}${newsBlock}${reasonsBlock}${copyBtn}${closeBtn}${historyBlock}`;
}

function renderPositions() {
  const open = store.getTrades().filter(t => !t.closed_at);
  const el = $("positions");
  if (!open.length) { el.innerHTML = `<div class="mu">No open positions.</div>`; return; }
  el.innerHTML = open.map(t => {
    const live = parseFloat(STATE.mids[t.coin] || 0) || t.entry;
    const side = t.side || "LONG";
    const m = tradeMargin(t); // original margin
    const n = t.notional_usd; // remaining notional
    const originalNotional = t.original_notional_usd || t.notional_usd;
    const currentPnl = tradePnl(t, live);
    const totalPnl = currentPnl + (t.partial_pnl || 0);
    const roe = m > 0 ? totalPnl / m * 100 : 0;
    const liq = calcLiq(t.entry, t.leverage, side), dl = Math.abs(live - liq) / live * 100;
    const beTag = t.breakeven_set ? ' <span class="badge" style="background:#4ea8ff;font-size:10px">🔒 BE</span>' : '';
    const tp1Tag = t.tp1_hit ? ' <span class="badge" style="background:var(--buy);font-size:10px">💰 TP1</span>' : '';
    const scalpTag = t.scalp ? ` <span class="badge" style="background:#f0b429;color:#000;font-size:10px">⚡${t.timeframe}</span>` : '';
    const sizeLabel = t.tp1_hit ? `$${n.toFixed(0)} <span class="mu" style="font-size:10px">of $${originalNotional.toFixed(0)}</span>` : `$${n.toFixed(0)}`;
    return `<div class="pos-item" onclick="showTradeDetail('${t.id}')"><div><b>${esc(t.coin)}${t.auto ? ' 🤖' : ''}</b> <span class="badge ${side}">${side}</span> ${t.leverage}x${beTag}${tp1Tag}${scalpTag} · <span class="mu">${sizeLabel}</span><br><span class="mu">entry ${fmt(t.entry)} · now ${fmt(live)} · stop ${fmt(t.stop)} · TP2 ${fmt(t.tp2)}</span><br><span class="mu">liq ${fmt(liq)} (${dl.toFixed(1)}%)</span><br><span class="${totalPnl>=0?'up':'dn'}" style="font-weight:700">P/L $${totalPnl.toFixed(2)} (${roe.toFixed(1)}% ROE)${t.tp1_hit ? ` · 💰 +$${(t.partial_pnl||0).toFixed(2)}` : ''}</span></div><button class="x" onclick="event.stopPropagation();closeManual('${t.id}')">Close</button></div>`;
  }).join("");
}

function renderStats() {
  const closed = store.getTrades().filter(t => t.closed_at);
  const s = computeStats(closed);
  const el = $("statsWrap");
  if (!s) { el.innerHTML = `<div class="mu">No closed trades yet.</div>`; return; }
  let reasonRows = "";
  const reasonOrder = ["tp2", "trail_stop", "breakeven", "stop", "momentum_flip", "stale_timeout", "auto_flip", "manual", "end"];
  for (const r of reasonOrder) {
    const d = s.reasonBreakdown[r];
    if (!d) continue;
    const wr = d.count > 0 ? (d.wins / d.count * 100).toFixed(0) : 0;
    reasonRows += `<div style="display:flex;justify-content:space-between;padding:4px 0;border-bottom:1px solid var(--bd);font-size:12px">
      <span>${r.replace(/_/g, " ")}</span>
      <span>${d.count}× · ${wr}% win · <b class="${d.pnl>=0?'up':'dn'}">$${fmt2(d.pnl)}</b></span>
    </div>`;
  }
  el.innerHTML = `<div id="verdictWrap" class="${s.vClass}"><div id="verdictTitle">${esc(s.vTitle)}</div><div id="verdictMsg">${esc(s.vMsg)}</div></div>
    <div class="stat-grid">
      <div class="stat-box"><div class="k">Trades</div><div class="v">${s.trades}</div></div>
      <div class="stat-box"><div class="k">Win rate</div><div class="v ${s.winRate>=50?'up':'dn'}">${s.winRate.toFixed(1)}%</div></div>
      <div class="stat-box"><div class="k">Net P/L</div><div class="v ${s.net>=0?'up':'dn'}">$${fmt2(s.net)}</div></div>
      <div class="stat-box"><div class="k">Profit factor</div><div class="v ${s.pf>=1?'up':'dn'}">${isFinite(s.pf)?s.pf.toFixed(2):"∞"}</div></div>
      <div class="stat-box"><div class="k">Avg win</div><div class="v up">$${fmt2(s.avgWin)}</div></div>
      <div class="stat-box"><div class="k">Avg loss</div><div class="v dn">$${fmt2(s.avgLoss)}</div></div>
      <div class="stat-box"><div class="k">Best</div><div class="v up">$${fmt2(s.best)}</div></div>
      <div class="stat-box"><div class="k">Worst</div><div class="v dn">$${fmt2(s.worst)}</div></div>
      <div class="stat-box"><div class="k">Max DD</div><div class="v dn">$${fmt2(s.maxDD)}</div></div>
      <div class="stat-box"><div class="k">💰 TP1 hits</div><div class="v">${s.tp1HitCount}/${s.trades}</div></div>
      <div class="stat-box"><div class="k">Avg hold</div><div class="v">${(s.avgHoldMs/3600000).toFixed(1)}h</div></div>
      <div class="stat-box"><div class="k">W/L</div><div class="v">${s.wins}/${s.losses}</div></div>
    </div>
    <div style="margin-top:12px">${svgCurve(s.curve, 600, 100)}</div>
    <div class="side-row">
      <div class="side-box"><b>CERTAIN</b><br>${s.certain.count} · ${s.certain.winRate.toFixed(0)}% win<br><span class="${s.certain.net>=0?'up':'dn'}">$${fmt2(s.certain.net)}</span></div>
      <div class="side-box"><b>CONFIDENT</b><br>${s.confident.count} · ${s.confident.winRate.toFixed(0)}% win<br><span class="${s.confident.net>=0?'up':'dn'}">$${fmt2(s.confident.net)}</span></div>
    </div>
    <div class="side-row">
      <div class="side-box"><b>LONG</b><br>${s.longCount} · ${s.longCount?(s.longWins/s.longCount*100).toFixed(0):0}% win<br><span class="${s.longNet>=0?'up':'dn'}">$${fmt2(s.longNet)}</span></div>
      <div class="side-box"><b>SHORT</b><br>${s.shortCount} · ${s.shortCount?(s.shortWins/s.shortCount*100).toFixed(0):0}% win<br><span class="${s.shortNet>=0?'up':'dn'}">$${fmt2(s.shortNet)}</span></div>
    </div>
    <div class="side-row">
      <div class="side-box"><b>PULLBACK</b><br>${s.pullback.count} · ${s.pullback.winRate.toFixed(0)}% win<br><span class="${s.pullback.net>=0?'up':'dn'}">$${fmt2(s.pullback.net)}</span></div>
      <div class="side-box"><b>BREAKOUT</b><br>${s.breakout.count} · ${s.breakout.winRate.toFixed(0)}% win<br><span class="${s.breakout.net>=0?'up':'dn'}">$${fmt2(s.breakout.net)}</span></div>
    </div>
    <div class="side-row">
      <div class="side-box"><b>⚡ SCALP</b><br>${s.scalp.count} · ${s.scalp.winRate.toFixed(0)}% win<br><span class="${s.scalp.net>=0?'up':'dn'}">$${fmt2(s.scalp.net)}</span></div>
      <div class="side-box" style="visibility:hidden"></div>
    </div>
    ${reasonRows ? `<div style="margin-top:12px">
      <div class="mu" style="font-size:11px;text-transform:uppercase;letter-spacing:.04em;margin-bottom:6px">Exit reason breakdown</div>
      ${reasonRows}
    </div>` : ''}`;
}

function renderWatchlist() {
  const q = ($("search")?.value || "").toLowerCase();
  const rows = STATE.watchlist.map(c => STATE.coins[c]).filter(Boolean)
    .filter(c => assetFilter === "ALL" || c.assetClass === assetFilter)
    .filter(c => c.coin.toLowerCase().includes(q))
    .map(c => {
      const hasScalp = STATE.scalp[c.coin] && Object.keys(STATE.scalp[c.coin]).length > 0;
      const scalpTag = hasScalp ? ' <span style="background:#f0b429;color:#000;font-size:9px;padding:1px 5px;border-radius:6px;font-weight:700">⚡</span>' : '';
      return `<tr class="clickable" onclick="selectCoin('${esc(c.coin)}')"><td><b>${esc(c.coin)}</b>${scalpTag}</td><td><span class="badge ${c.signal}">${c.signal}</span> <span class="badge ${c.confidence||'LOW'}">${c.confidence||'LOW'}</span></td><td class="n">${fmt(c.price)}</td><td class="n">${c.score||0}</td></tr>`;
    }).join("");
  $("watch").innerHTML = rows ? `<div class="table-wrap"><table><thead><tr><th>Coin</th><th>Signal</th><th class="n">Price</th><th class="n">Score</th></tr></thead><tbody>${rows}</tbody></table></div>` : `<div class="mu">No matches.</div>`;
}

function selectCoin(coin) { currentCoin = coin; $("execCoin").value = coin; loadCandles(coin, currentIv); render(); }

function render() {
  $("statusDot").className = "dot " + (STATE.status === "live" ? "" : STATE.status === "error" ? "err" : "scan");
  if (!currentCoin && STATE.watchlist.length) {
    const buy = STATE.watchlist.find(c => STATE.coins[c].signal === "BUY");
    const btc = STATE.coins["BTC"] ? "BTC" : null;
    currentCoin = buy || btc || STATE.watchlist[0];
    renderTfTabs(); initChart(); loadCandles(currentCoin, currentIv);
  }
  refreshCoinSelects(); renderAssetTabs();
  const live = parseFloat(STATE.mids[currentCoin] || 0) || (STATE.coins[currentCoin]?.price || null);
  $("livePrice").textContent = live ? "$" + fmt(live) + " " + currentCoin : "—";
  const execLive = parseFloat(STATE.mids[$("execCoin").value] || 0) || (STATE.coins[$("execCoin").value]?.price || null);
  $("execLive").textContent = execLive ? "$" + fmt(execLive) : "—";
  if (live) updateFormingBar(live);
  updateExecPreview();
  const cur = STATE.coins[currentCoin];
  if (cur) {
    $("banner").className = "banner " + (cur.signal === "BUY" ? "buy" : cur.signal === "SELL" ? "sell" : cur.signal === "WAIT" ? "wait" : "neut");
    $("banner").textContent = `${cur.signal} ${cur.coin} — ${cur.confidence||""} · ${cur.gatesPassed||0}/${cur.gatesTotal||0} checks · score ${cur.score||0}`;
    renderSignalCard(cur);
    const ec = STATE.coins[$("execCoin").value];
    if (ec) $("execHint").innerHTML = `<b>${esc(ec.coin)}:</b> ${esc(ec.signal)} ${ec.confidence||""} · ${esc((ec.why||"").slice(0,200))}`;
  }
  renderPositions(); renderStats(); renderWatchlist(); renderAutoPanel(); renderScalpPanel(); renderNewsPanel(); checkAutoClose(); drawPriceLines(currentCoin);

  const _now = Date.now();
  if (currentCoin && (!STATE.bookCache[currentCoin] || _now - STATE.bookCache[currentCoin].ts > 2000)) {
    const _dex = (STATE.coins[currentCoin]?.dex) || "";
    const _raw = currentCoin.includes(":") ? currentCoin.split(":")[1] : currentCoin;
    fetchOrderBook(_raw, _dex).then(book => {
      if (book) { STATE.bookCache[currentCoin] = { ts: Date.now(), ...book }; renderOrderBookBar(); }
    }).catch(() => {});
  }
}

$("execCoin").addEventListener("change", function() { currentCoin = this.value; loadCandles(currentCoin, currentIv); render(); });
$("execSize").addEventListener("input", updateExecPreview);
$("execLev").addEventListener("input", updateExecPreview);
$("capital").addEventListener("change", function() { localStorage.setItem("legend_capital", this.value); });
$("search").addEventListener("input", renderWatchlist);
const savedCap = localStorage.getItem("legend_capital");
if (savedCap) $("capital").value = savedCap;

(function injectCSVButton() {
  const body = $("statsBody");
  if (!body || $("csvExportBtn")) return;
  const btn = document.createElement("button");
  btn.id = "csvExportBtn";
  btn.className = "btn-ghost";
  btn.style.cssText = "width:100%;margin-bottom:8px;font-size:12px";
  btn.textContent = "📥 Export trades CSV";
  btn.addEventListener("click", exportTradesCSV);
  body.insertBefore(btn, body.firstChild);
})();

connectWS();
applyTheme();
updateSoundBtn();
fetchAllNews().catch(() => {});
setInterval(fetchAllNews, NEWS_REFRESH_MS);
if (localStorage.getItem("stats_folded") === "1") { $("statsBody").style.display = "none"; $("statsToggle").textContent = "▲"; }
renderTfTabs();
render();
setTimeout(runScan, 200);
setInterval(runScan, SCAN_INTERVAL);
setInterval(() => {
  if (!document.hidden) {
    checkAutoTrade();
    refreshAllScalps().then(() => render());
  }
}, STATE_POLL_MS);

const lastBt = store.getBtLast();
if (lastBt) renderBacktestResult(lastBt); /* C.A. Creative Bot — created and owned by Charles Amankwah */

