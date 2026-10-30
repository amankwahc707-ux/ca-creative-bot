# C.A. Creative Bot

**Created and owned by Charles Amankwah.**

Read-only, browser-only trading signal dashboard for Hyperliquid perpetual markets. No backend, no server, no wallet, no keys.

## Deploy to GitHub Pages (5 minutes)

1. Go to github.com and create a new repository (private or public — your choice).
2. Upload these five files to the repository root:
   - `index.html`
   - `app.js`
   - `style.css`
   - `sw.js`
   - `manifest.json`
3. In the repo, go to **Settings → Pages**.
4. Under "Build and deployment", set **Source** to `Deploy from a branch`, **Branch** to `main`, folder to `/ (root)`.
5. Click **Save**. Wait 30 seconds.
6. Open `https://YOUR-USERNAME.github.io/YOUR-REPO-NAME/` in your browser.

## First use

- Tap the **🔔 Alerts** button once to grant notification permission.
- On phones, use your browser's "Add to Home Screen" so it opens fullscreen like an app.
- No API keys, no wallet connection, no login.

## What it does

- Streams live prices from Hyperliquid's public WebSocket.
- Scans crypto (top 20 by volume), stocks (NVDA, TSLA, AAPL, MSFT, GOOGL, AMZN, META, PLTR), and commodities (GOLD, SILVER, BRENTOIL) every 90 seconds.
- Computes strict, multi-timeframe signals across 5m / 15m / 1h / 4h / 1d.
- Emits BUY or SELL **only** when all hard gates pass, no conflicts exist, and confidence is CERTAIN or CONFIDENT. Otherwise emits NEUTRAL with the exact reason.
- Lets you paper-trade with custom margin, 1–20x leverage, and both LONG and SHORT.
- Auto-sets stop loss and take profit at open. You can drag them on the chart or edit them in the trade detail modal.
- Tracks full performance stats and shows the win rate per confidence tier.
- Includes a backtest that replays the same signal logic on 30/60/90 days of history, with no look-ahead bias and pessimistic fills.

## What it does NOT do

- No order placement, no wallet, no API keys.
- No guarantee of profit or accuracy. Win rate is measured, never promised.
- Alerts fire only while a tab is open (browser tab or PWA in background). True push when the phone is locked requires a paid push service and is not included.

## Files

| File | Purpose |
|---|---|
| `index.html` | Page structure |
| `app.js` | All logic: indicators, signals, trading, backtest |
| `style.css` | Styling |
| `sw.js` | Service worker (notifications only) |
| `manifest.json` | PWA manifest |

## Honest disclaimer

Not financial advice. Signals are rules, not predictions. Trade only what you can afford to lose.
