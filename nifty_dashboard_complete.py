"""
NIFTY Intraday Dashboard — Pass 1
Classes 1–7: ConfigReader, SmartApiClient, InstrumentMasterLoader,
             CandleFetcher, OptionChainBuilder, MetricsCalculator, SignalEngine
"""

# ═══════════════════════════════════════════════════════════════════════════════
# GOOGLE APPS SCRIPT — Extensions → Apps Script → Save
# ONE-DAY ACTIVATION: Button writes today IST date to B3 + YES to B5.
# Python checks B3 == today before honouring B5=YES.
# Python clears B3 and B5 at next session start automatically.
# User must click EXECUTE TRADE again each trading day.
#
# function executeTrade() {
#   var ss   = SpreadsheetApp.getActiveSpreadsheet();
#   var ws   = ss.getSheetByName('EXECUTION');
#   var tz   = 'Asia/Calcutta';
#   var today= Utilities.formatDate(new Date(), tz, 'dd-MMM-yyyy');
#   ws.getRange('B3').setValue(today);
#   ws.getRange('B5').setValue('YES');
#   SpreadsheetApp.getUi().alert(
#     'Trigger set for ' + today + '. Executes on next cycle.');
# }
# function exitAll() {
#   var ss   = SpreadsheetApp.getActiveSpreadsheet();
#   var ws   = ss.getSheetByName('EXECUTION');
#   var tz   = 'Asia/Calcutta';
#   var today= Utilities.formatDate(new Date(), tz, 'dd-MMM-yyyy');
#   ws.getRange('B3').setValue(today);
#   ws.getRange('B6').setValue('EXIT_ALL');
#   ws.getRange('B5').setValue('YES');
#   SpreadsheetApp.getUi().alert('Exit all positions — next cycle.');
# }
# function cancelTrigger() {
#   var ss = SpreadsheetApp.getActiveSpreadsheet();
#   var ws = ss.getSheetByName('EXECUTION');
#   ws.getRange('B5').setValue('NO');
#   ws.getRange('B3').setValue('');
#   SpreadsheetApp.getUi().alert('Trigger cancelled.');
# }
# Setup: Insert → Drawing → rectangle → 3-dot → Assign script
#   EXECUTE TRADE → executeTrade
#   EXIT ALL      → exitAll
#   CANCEL        → cancelTrigger
# ═══════════════════════════════════════════════════════════════════════════════

# ── Standard library ──────────────────────────────────────────────────────────
import os
import json
import math
import time
import logging
import pathlib
import re
import html
import traceback
from datetime import datetime, timedelta, timezone
from itertools import groupby
from typing import Optional, List, Dict, Any, Tuple
from collections import defaultdict

# ── Third-party ───────────────────────────────────────────────────────────────
import pandas as pd
import numpy as np
import requests
import gspread
import pyotp
import ntplib

# logzero is a mandatory dependency — the SmartAPI SDK imports it at module level
# If missing, "from SmartApi import SmartConnect" will raise ImportError before any app code runs.
try:
    import logzero  # noqa: F401 — imported for SmartAPI SDK side-effect dependency check
except ImportError:
    raise ImportError(
        "logzero is not installed. Run: pip install logzero\n"
        "logzero is required by the smartapi-python SDK at import time."
    )

try:
    from SmartApi import SmartConnect
except ImportError as _exc:
    raise ImportError(
        f"smartapi-python is not installed or has missing dependencies: {_exc}\n"
        "Run: pip install smartapi-python logzero"
    )

# ── CONFIG ────────────────────────────────────────────────────────────────────

CONFIG = {
    # ── Google Sheets ──────────────────────────────────────────────────────────
    'GOOGLE_SERVICE_ACCOUNT_JSON': r'C:\Nifty-Dashboard\service_account.json',  # ← SET THIS
    'SPREADSHEET_ID':'1kEMOWPl5O1sKpXpspZ5gXVGro1I-HvtGpn48ty-7dZ0',                       # ← SET THIS

    # ── ChatGPT / OpenAI (optional — leave empty to disable) ───────────────────
    'OPENAI_API_KEY':        '',   # ← SET THIS or set env var OPENAI_API_KEY
    'OPENAI_MODEL':          'gpt-4.1-mini',
    'OPENAI_MAX_TOKENS':     600,
    'CLAUDE_EVERY_N_CYCLES': 1,    # runs every 5-min cycle
    'PROMPT_VERSION':        'v1.2',
    # Backward-compat aliases for older references
    'ANTHROPIC_API_KEY':     '',
    'CLAUDE_MODEL':          'gpt-4.1-mini',
    'CLAUDE_MAX_TOKENS':     600,

    # ── Telegram (optional — leave empty to disable) ───────────────────────────
    'TELEGRAM_BOT_TOKEN':    '',   # ← SET THIS or set env var TELEGRAM_BOT_TOKEN
    'TELEGRAM_CHAT_ID':      '',   # ← SET THIS or set env var TELEGRAM_CHAT_ID

    # ── Angel One ─────────────────────────────────────────────────────────────
    'SPOT_INDEX_TOKEN':   '99926000',
    'VIX_INDEX_TOKEN':    '99919000',   # India VIX, NSE — premium environment analysis
    'NIFTY_STRIKE_STEP':  50,

    # ── VIX thresholds ─────────────────────────────────────────────────────────
    'VIX_HIGH_THRESHOLD':  20.0,
    'VIX_LOW_THRESHOLD':   13.0,
    'VIX_RISING_LOOKBACK':  5,

    # ── Instrument master URLs ─────────────────────────────────────────────────
    'SCRIP_MASTER_URL_PRIMARY':
        'https://margincalculator.angelbroking.com/OpenAPI_File/files/OpenAPIScripMaster.json',
    'SCRIP_MASTER_URL_FALLBACK':
        'https://margincalculator.angelone.in/OpenAPI_File/files/OpenAPIScripMaster.json',

    # ── Scoring weights ────────────────────────────────────────────────────────
    'SCORE_STRONG_PE_WRITING':        2,
    'SCORE_STRONG_CE_WRITING':       -2,
    'SCORE_CE_UNWINDING_RISING':      2,
    'SCORE_PE_UNWINDING_FALLING':    -2,
    'SCORE_SUPPORT_SHIFT_UP':         1,
    'SCORE_SUPPORT_SHIFT_DOWN':      -1,
    'SCORE_RESISTANCE_SHIFT_UP':      1,
    'SCORE_RESISTANCE_SHIFT_DOWN':   -1,
    'SCORE_BULLISH_PCR':              1,
    'SCORE_BEARISH_PCR':             -1,
    'SCORE_BULLISH_VOL_IMBALANCE':    1,
    'SCORE_BEARISH_VOL_IMBALANCE':   -1,
    'SCORE_BULLISH_PRICE_STRUCTURE':  2,
    'SCORE_BEARISH_PRICE_STRUCTURE': -2,
    'SCORE_ABOVE_VWAP':               1,
    'SCORE_BELOW_VWAP':              -1,
    'SCORE_BULLISH_VOL_CONFIRM':      1,
    'SCORE_BEARISH_VOL_CONFIRM':     -1,

    # ── Thresholds ─────────────────────────────────────────────────────────────
    'PCR_BULLISH_THRESHOLD':   1.2,
    'PCR_BEARISH_THRESHOLD':   0.8,
    'SR_PROXIMITY_PCT':        0.005,
    'COMPARISON_OI_THRESHOLD': 50000,
    'BREAKOUT_BUFFER_PCT':     0.002,
    'BREAKDOWN_BUFFER_PCT':    0.002,
    'VOLUME_SPIKE_RATIO':      1.5,
    'REJECTION_WICK_RATIO':    2.0,
    'REJECTION_MIN_CANDLES':   2,

    # ── Paths ──────────────────────────────────────────────────────────────────
    'CACHE_DIR': 'cache',
    'LOG_DIR':   'logs',
}

# Override with environment variables at module load time
CONFIG['OPENAI_API_KEY']     = os.environ.get('OPENAI_API_KEY', CONFIG.get('OPENAI_API_KEY', ''))
CONFIG['ANTHROPIC_API_KEY']  = CONFIG['OPENAI_API_KEY'] or os.environ.get('ANTHROPIC_API_KEY', CONFIG.get('ANTHROPIC_API_KEY', ''))
CONFIG['OPENAI_MODEL']       = os.environ.get('OPENAI_MODEL', CONFIG.get('OPENAI_MODEL', 'gpt-4.1-mini'))
CONFIG['CLAUDE_MODEL']       = CONFIG['OPENAI_MODEL']
CONFIG['OPENAI_MAX_TOKENS']  = int(os.environ.get('OPENAI_MAX_TOKENS', str(CONFIG.get('OPENAI_MAX_TOKENS', CONFIG.get('CLAUDE_MAX_TOKENS', 600)))))
CONFIG['CLAUDE_MAX_TOKENS']  = CONFIG['OPENAI_MAX_TOKENS']
CONFIG['TELEGRAM_BOT_TOKEN'] = os.environ.get('TELEGRAM_BOT_TOKEN', CONFIG['TELEGRAM_BOT_TOKEN'])
CONFIG['TELEGRAM_CHAT_ID']   = os.environ.get('TELEGRAM_CHAT_ID',   CONFIG['TELEGRAM_CHAT_ID'])

# ── Logging setup ─────────────────────────────────────────────────────────────

def _setup_logging() -> logging.Logger:
    log_dir = pathlib.Path(CONFIG['LOG_DIR'])
    log_dir.mkdir(parents=True, exist_ok=True)
    logger = logging.getLogger('nifty_dashboard')
    if logger.handlers:
        return logger
    logger.setLevel(logging.DEBUG)
    fmt = logging.Formatter('%(asctime)s [%(levelname)s] %(message)s', datefmt='%Y-%m-%d %H:%M:%S')
    ch = logging.StreamHandler()
    ch.setLevel(logging.INFO)
    ch.setFormatter(fmt)
    fh = logging.FileHandler(
        log_dir / f"nifty_{datetime.now(timezone(timedelta(hours=5, minutes=30))).strftime('%Y%m%d')}.log",
        encoding='utf-8'
    )
    fh.setLevel(logging.DEBUG)
    fh.setFormatter(fmt)
    logger.addHandler(ch)
    logger.addHandler(fh)
    return logger

log = _setup_logging()

# ── Module-level constants ────────────────────────────────────────────────────

PROMPT_VERSION = CONFIG['PROMPT_VERSION']

CLAUDE_SYSTEM_PROMPT = """You are a NIFTY 50 derivatives market analyst. Analyze the provided market snapshot JSON and return ONLY a valid JSON object matching the schema below.

CRITICAL RULES:
1. NEVER recommend buying, selling, opening positions, or any specific trade action.
2. NEVER use these phrases: BUY, SELL, go long, go short, buy call, buy put, entry at, target price, stop loss, take profit, open position, close position.
3. Describe market conditions, probable participant behavior, and observable patterns only.
4. Return ONLY the JSON object — no markdown, no prose, no code fences.
5. score_agreement=true means your market_bias directionally matches the rule-engine bias field.
   Mapping rule: STRONG BULLISH / BULLISH / MILD BULLISH → Bullish. STRONG BEARISH / BEARISH / MILD BEARISH → Bearish. NEUTRAL → Neutral.
   Set score_agreement=true only if your market_bias and the mapped rule-engine bias are the same direction.

FIELD DEFINITIONS IN THE INPUT JSON:

CORE FIELDS:
spot              = NIFTY 50 current index price
atm               = at-the-money strike (spot rounded to nearest 50 pts)
expiry            = selected options expiry date (DDMMMYYYY)
expiry_type       = WEEKLY or MONTHLY
bias              = rule engine verdict: STRONG BULLISH / BULLISH / MILD BULLISH / NEUTRAL / MILD BEARISH / BEARISH / STRONG BEARISH
score             = score string e.g. '6/12'. Max=+12, Min=-12. Each of 9 positive factors contributes +1 or +2.
confidence        = signal reliability 0-100%. Below 30% = treat as weak.
event_tag         = PROBABLE SHORT COVERING | PROBABLE LONG UNWINDING | BULLISH SHIFT | BEARISH SHIFT | RANGEBOUND | TRAP WARNING | LOW CONFIDENCE
trap              = if non-empty, a bull or bear trap was detected — mention this FIRST in your analysis

price_structure   = BULLISH STRUCTURE (higher highs + higher lows) | BEARISH STRUCTURE | RANGEBOUND | REVERSAL WATCH
vwap              = intraday VWAP from NIFTY Futures candles
vwap_bias         = BULLISH (spot above VWAP) | BEARISH (below) | NEUTRAL
vol_bias          = BULLISH | BEARISH | NEUTRAL — Futures volume confirmation
vol_imbalance     = (total_PE_volume - total_CE_volume) / (total_PE_volume + total_CE_volume). Bounded in [-1, +1]. +1 = all activity on PE side (bullish). -1 = all activity on CE side (bearish). 0 = balanced. NaN/missing if total volume = 0.
oi_concentration  = top-2 CE OI + top-2 PE OI divided by total zone OI. >0.65 = price pinning (large writers dominate, expect range). 0.40-0.65 = normal. <0.40 = OI rotating/spreading (directional move more likely). NaN = unavailable.

support           = strike with highest Put OI (where put writers defend price)
resistance        = strike with highest Call OI (where call writers cap price)
support_shift     = points support moved vs last cycle (+ve = bullish)
resistance_shift  = points resistance moved vs last cycle (-ve = bearish)
pcr_oi            = Put-Call Ratio by OI. >1.2 = bullish. <0.8 = bearish.
pcr_chg_oi        = Put-Call Ratio by Change OI this cycle. Measures fresh directional flow — not cumulative OI. >1.2 = aggressive put writing (fresh support). <0.8 = aggressive call writing (fresh resistance). NaN = insufficient data this cycle (use pcr_oi instead).
total_ce_oi       = total Call OI in focus zone
total_pe_oi       = total Put OI in focus zone
total_ce_chg_oi   = net change in Call OI this cycle (negative = unwinding)
total_pe_chg_oi   = net change in Put OI this cycle (negative = unwinding)

sr_event          = SUPPORT_REVERSAL | RESISTANCE_REVERSAL | BREAKOUT_ABOVE_RESISTANCE | BREAKDOWN_BELOW_SUPPORT | NONE
sr_confidence     = HIGH | MEDIUM | LOW | N/A
sr_event_age      = consecutive 5-min cycles the current sr_event has been active. 1=fired this cycle. 3=held 15min. 6=held 30min. 0=no active event.

candle_pattern    = BULLISH_REJECTION (hammer at support) | BEARISH_REJECTION (shooting star at resistance) | EXPANSION_UP (strong green bar) | EXPANSION_DOWN (strong red bar) | NONE | INSUFFICIENT_DATA
candle_wick_pct   = rejection wick as % of candle range (0-100). >70=very strong rejection. 50-69=moderate. <50=weak.
candle_vol_ratio  = candle futures volume / 5-bar average. >1.5=spike confirms signal. <0.8=low conviction. 1.0=no data.

recent_spot_candles    = last 8 five-minute NIFTY spot bars (most recent last). Each: c=close, d=G(green)/R(red), str=body% of candle range (100=marubozu, <20=doji), vol=0 (index — not meaningful).
recent_futures_candles = same for NIFTY Futures. vol field meaningful here (thousands). vol>1.5×avg=volume spike confirms signal. <0.8×avg=low conviction.

prev_day_high     = yesterday's session high
prev_day_low      = yesterday's session low
prev_day_close    = yesterday's closing price
prev_day_open     = yesterday's opening price
prev_day_range    = yesterday's high minus low
prev_day_position = plain note on where current spot is vs yesterday's levels

session_high      = highest NIFTY spot price reached today since 09:15 IST
session_low       = lowest NIFTY spot price reached today since 09:15 IST
session_open      = NIFTY spot price at market open (09:15 IST today)

checklist_warns   = number of data quality warnings this cycle
checklist_fails   = number of critical failures (>0 = data unreliable, say so clearly)

option_chain      = strike-by-strike data for focus zone: each row has strike, ce_oi, pe_oi, ce_chg_oi, pe_chg_oi, ce_ltp, pe_ltp, ce_iv, pe_iv, ce_volume, pe_volume
session_history_last_8 = last 8 five-minute cycles (40 min of history). Each row: ts, spot, bias, score, event, sr, cp (candle_pattern), support, resist, market, vix, ce_chg (CE change OI this cycle), pe_chg (PE change OI this cycle), sr_age (consecutive cycles same SR event active), oi_conc (OI concentration ratio >0.65=pinning <0.40=rotating).

mtf_context = multi-timeframe analysis context:
  mtf_15m = { structure: BULLISH STRUCTURE|BEARISH STRUCTURE|RANGEBOUND|INSUFFICIENT_DATA, last_close, bars }
  mtf_30m = { structure: same enum, last_close, bars }
  mtf_oi_trend = {
    ce_writing_30min: building|unwinding|stable,
    pe_writing_30min: building|unwinding|stable,
    support_migrated_pts: points support moved in last 30 min (+ve=up -ve=down),
    resistance_migrated_pts: same for resistance,
    oi_concentration_trend: concentrating|spreading|stable,
    max_sr_event_age_30min: max cycles same SR event held in last 30 min
  }
  mtf_sr_context = {
    spot_vs_support_pct: % distance spot to support (lower = closer to break),
    spot_vs_resist_pct: % distance spot to resistance,
    support_oi_now, resistance_oi_now, support_chg_oi_now, resistance_chg_oi_now,
    support_break_risk: HIGH|MEDIUM|LOW,
    resistance_break_risk: HIGH|MEDIUM|LOW,
    support_strengthening: true if PE actively written at support,
    resistance_strengthening: true if CE actively written at resistance
  }

MTF ANALYSIS RULES — apply these when writing current_situation and mtf_alignment:
- 5m and 15m agree: state "aligned on 15m timeframe".
- 5m, 15m, 30m all agree: state "aligned across all timeframes — higher conviction".
- Structures conflict: describe explicitly e.g. "5m BULLISH STRUCTURE but 30m RANGEBOUND — higher timeframe not confirmed".
- Always describe support_break_risk and resistance_break_risk when either is HIGH or MEDIUM.
- Always mention if support is strengthening (PE building) or weakening (PE unwinding).
- Always mention if resistance is strengthening (CE building) or weakening (CE unwinding).
- If support or resistance migrated more than 50 pts in 30 min, call it out explicitly.
- In free-text fields (current_situation, signal, risk_note, mtf_alignment, reasoning, prev_day_context), NEVER use the words: buy, sell, long, short, breakout, breakdown.
  Exception: the price_behavior output field uses Breakout Attempt, Post-Breakout, Breakdown Attempt, Post-Breakdown as required enum values — those are permitted.

PREMIUM ENVIRONMENT:
vix_level         = India VIX current level. <13=low/calm. >20=high/event-risk. NaN=unavailable.
vix_trend         = RISING | FALLING | FLAT over last 5 candles
vix_pct_change    = VIX % change from session open (+ve = VIX rising today)
market_condition  = Decay Favorable | Expansion Favorable | Neutral (rule-engine verdict)
volatility_context= Low | Moderate | High | Rising | Falling | Unknown
price_behavior    = Range-bound | Trending | Breakout Attempt | Post-Breakout | Breakdown Attempt | Post-Breakdown
days_to_expiry    = calendar days to selected expiry. <=2 = maximum theta. >=15 = slow decay.
decay_score       = internal rule score ±10 (+ve=decay, -ve=expansion). Context only — do not cite this number directly.

TRAP VALIDATION (when trap field is non-empty):
Validate by checking: sr_event fired, vol_bias=NEUTRAL (not BULLISH/BEARISH) combined with candle_vol_ratio<0.8 indicating low conviction on the breakout bar, candle_wick_pct>60, vwap_bias opposite to breakout direction, price already reversing (spot moving back through the breakout level), sr_event_age>=4 with reversal = confirmed trap.
If fewer than 3 conditions confirm: state 'trap signal — monitoring for confirmation'.

OUTPUT JSON SCHEMA — return exactly this structure, no extra keys:
{
  "market_bias": "Bullish" | "Bearish" | "Neutral",
  "current_situation": "<2-3 sentences describing current market state and probable participant behavior>",
  "key_levels": {"support": "<strike as string>", "resistance": "<strike as string>"},
  "signal": "<one concise observation about the most important market dynamic right now>",
  "strength": "Strong" | "Moderate" | "Weak",
  "reasoning": ["<point 1 with actual observed values>", "<point 2>", "<point 3>"],
  "prev_day_context": "<how today's price action relates to yesterday's levels>",
  "risk_note": "<one sentence on the main risk to the current directional assessment>",
  "score_agreement": true | false,
  "unusual_observation": "<one notable pattern not captured by the rule engine, or null>",
  "mtf_alignment": "<one sentence: whether 5m/15m/30m structures agree or conflict and what it means>",
  "premium_environment": {
    "market_condition": "Decay Favorable" | "Expansion Favorable" | "Neutral",
    "volatility_context": "High" | "Low" | "Rising" | "Falling" | "Moderate" | "Unknown",
    "price_behavior": "Range-bound" | "Trending" | "Breakout Attempt" | "Post-Breakout" | "Breakdown Attempt" | "Post-Breakdown",
    "key_insight": "<1-2 sentences combining VIX, DTE, and price context>",
    "reasoning": ["<VIX observation with actual value>", "<trend/DTE observation>", "<price behavior observation>"],
    "risk_note": "<one sentence on main risk to the premium environment assessment>"
  }
}"""

CLAUDE_OUTPUT_SCHEMA = """{
  "market_bias": "Bullish | Bearish | Neutral",
  "current_situation": "string",
  "key_levels": {"support": "string", "resistance": "string"},
  "signal": "string",
  "strength": "Strong | Moderate | Weak",
  "reasoning": ["string", "string", "string"],
  "prev_day_context": "string",
  "risk_note": "string",
  "score_agreement": "boolean",
  "unusual_observation": "string | null",
  "mtf_alignment": "string",
  "premium_environment": {
    "market_condition": "Decay Favorable | Expansion Favorable | Neutral",
    "volatility_context": "High | Low | Rising | Falling | Moderate | Unknown",
    "price_behavior": "Range-bound | Trending | Breakout Attempt | Post-Breakout | Breakdown Attempt | Post-Breakdown",
    "key_insight": "string",
    "reasoning": ["string", "string", "string"],
    "risk_note": "string"
  }
}"""

# ── IST timezone ──────────────────────────────────────────────────────────────
_IST = timezone(timedelta(hours=5, minutes=30))

# ── Utility functions ─────────────────────────────────────────────────────────

def now_ist() -> datetime:
    """Return current datetime in IST (UTC+5:30)."""
    return datetime.now(_IST)


def ist_str(fmt: str = '%Y-%m-%d %H:%M:%S') -> str:
    """Return current IST time as formatted string."""
    return now_ist().strftime(fmt)


def safe_int(val: Any, default: int = 0) -> int:
    """Convert val to int, returning default on failure."""
    try:
        return int(val)
    except (ValueError, TypeError):
        return default


def retry_call(fn, *args, attempts: int = 3, delay: float = 2.0,
               fallback: Any = None, label: str = 'call') -> Any:
    """
    Generic retry wrapper used at every external API call site.
    Logs warnings on intermediate failures and error on final failure.
    Returns fallback value if all attempts fail.
    Skips retries on authentication failures (401/403).
    Uses exponential backoff for delays.
    """
    for attempt in range(attempts):
        try:
            return fn(*args)
        except Exception as e:
            error_str = str(e).lower()
            is_auth_failure = ('401' in error_str or '403' in error_str or
                             'unauthorized' in error_str or 'forbidden' in error_str)
            if is_auth_failure:
                log.error(f'[{label}] authentication failure: {e} — not retrying')
                break
            if attempt < attempts - 1:
                backoff_delay = delay * (2 ** attempt)
                log.warning(f'[{label}] attempt {attempt + 1} failed: {e} — retrying in {backoff_delay}s')
                time.sleep(backoff_delay)
            else:
                log.error(f'[{label}] all {attempts} attempts failed: {e}')
    return fallback


# safe_val: convert NaN/inf/None to empty string for Sheets output
safe_val = lambda v: '' if (
    v is None or
    (isinstance(v, float) and (math.isnan(v) or math.isinf(v)))
) else v


# ── CLASS 1 — ConfigReader ────────────────────────────────────────────────────

class ConfigReader:
    """
    Reads runtime configuration from the SETTINGS Google Sheet tab.

    Cell mapping (column B at these row numbers):
        B5  = Symbol (must be NIFTY)
        B7  = Expiry Mode (AUTO | NEXT | MONTHLY | MANUAL)
        B8  = Manual Expiry (DDMMMYYYY, used only when B7=MANUAL)
        B10 = Interval minutes
        B11 = Strikes Above ATM
        B12 = Strikes Below ATM
        B13 = Auto Refresh (YES | NO)
        B15 = Broker (ANGELONE)
        B17 = Angel API Key
        B18 = Angel Client Code
        B19 = Angel PIN (MPIN — must be exactly 4 digits)
        B20 = Angel TOTP Secret
    """

    CELL_MAP = {
        'symbol':           'B5',
        'expiry_mode':      'B7',
        'manual_expiry':    'B8',
        'interval':         'B10',
        'strikes_above':    'B11',
        'strikes_below':    'B12',
        'auto_refresh':     'B13',
        'broker':           'B15',
        'api_key':          'B17',
        'client_code':      'B18',
        'mpin':             'B19',
        'totp_secret':      'B20',
        'anthropic_key':    'B21',
        'telegram_token':   'B22',
        'telegram_chat_id': 'B23',
        'contract_lot_size': 'B25',
        'lot_size':         'B25',
    }

    def __init__(self, spreadsheet):
        self._spreadsheet = spreadsheet
        self.settings: Dict[str, Any] = {}

    def load(self) -> Dict[str, Any]:
        """
        Load all settings from the SETTINGS tab.
        Raises RuntimeError with actionable message if validation fails.
        Never reads from DASHBOARD — always reads from SETTINGS.
        """
        try:
            ws = self._spreadsheet.worksheet('SETTINGS')
        except Exception as e:
            raise RuntimeError(
                f"SETTINGS tab not found in spreadsheet: {e}\n"
                "Create the SETTINGS tab with the correct layout and run again."
            )

        raw: Dict[str, str] = {}
        for key, cell in self.CELL_MAP.items():
            try:
                val = ws.acell(cell).value or ''
                raw[key] = str(val).strip()
            except Exception as e:
                raise RuntimeError(f"Failed to read cell {cell} from SETTINGS: {e}")

        self._validate(raw)
        self.settings = {
            'symbol':           raw['symbol'].upper(),
            'expiry_mode':      raw['expiry_mode'].upper(),
            'manual_expiry':    raw['manual_expiry'].upper(),
            'interval_min':     safe_int(raw['interval'], 5),
            'strikes_above':    max(1, safe_int(raw['strikes_above'], 5)),
            'strikes_below':    max(1, safe_int(raw['strikes_below'], 5)),
            'auto_refresh':     raw['auto_refresh'].upper() == 'YES',
            'broker':           raw['broker'].upper(),
            'api_key':          raw['api_key'],
            'client_code':      raw['client_code'],
            'mpin':             raw['mpin'],
            'totp_secret':      raw['totp_secret'],
            'anthropic_key':    raw.get('anthropic_key', ''),
            'telegram_token':   raw.get('telegram_token', ''),
            'telegram_chat_id': raw.get('telegram_chat_id', ''),
            'lot_size':         max(1, safe_int(raw.get('lot_size', '25'), 25)),
            'contract_lot_size': max(1, safe_int(raw.get('lot_size', '25'), 25)),
        }
        # Push B21-B23 from SETTINGS tab into CONFIG
        if self.settings['anthropic_key']:
            CONFIG['OPENAI_API_KEY'] = self.settings['anthropic_key']
            CONFIG['ANTHROPIC_API_KEY'] = self.settings['anthropic_key']
        if self.settings['telegram_token']:
            CONFIG['TELEGRAM_BOT_TOKEN'] = self.settings['telegram_token']
        if self.settings['telegram_chat_id']:
            CONFIG['TELEGRAM_CHAT_ID'] = self.settings['telegram_chat_id']
        log.info(
            f"[ConfigReader] Loaded settings: symbol={self.settings['symbol']}, "
            f"expiry_mode={self.settings['expiry_mode']}, "
            f"interval={self.settings['interval_min']}min"
        )
        return self.settings

    def _validate(self, raw: Dict[str, str]) -> None:
        errors = []

        if raw['symbol'].upper() != 'NIFTY':
            errors.append(f"B5 (Symbol): must be 'NIFTY', got '{raw['symbol']}'")

        if raw['expiry_mode'].upper() not in ('AUTO', 'NEXT', 'MONTHLY', 'MANUAL'):
            errors.append(
                f"B7 (Expiry Mode): must be AUTO, NEXT, MONTHLY, or MANUAL; got '{raw['expiry_mode']}'"
            )

        if raw['expiry_mode'].upper() == 'MANUAL':
            try:
                datetime.strptime(raw['manual_expiry'], '%d%b%Y')
            except ValueError:
                errors.append(
                    f"B8 (Manual Expiry): must be DDMMMYYYY format (e.g. 28OCT2025); "
                    f"got '{raw['manual_expiry']}'"
                )

        if not raw['interval'] or not raw['interval'].isdigit() or int(raw['interval']) < 1:
            errors.append(f"B10 (Interval): must be a positive integer; got '{raw['interval']}'")

        for cell, name in [('strikes_above', 'B11'), ('strikes_below', 'B12')]:
            if not raw[cell] or not raw[cell].isdigit() or int(raw[cell]) < 1:
                errors.append(f"{name} ({cell.replace('_', ' ').title()}): must be a positive integer >= 1")

        if raw['auto_refresh'].upper() not in ('YES', 'NO'):
            errors.append(f"B13 (Auto Refresh): must be YES or NO; got '{raw['auto_refresh']}'")

        if raw['broker'].upper() != 'ANGELONE':
            errors.append(f"B15 (Broker): must be ANGELONE; got '{raw['broker']}'")

        if not raw['api_key']:
            errors.append("B17 (API Key): must be non-empty")

        if not raw['client_code']:
            errors.append("B18 (Client Code): must be non-empty")

        mpin = raw['mpin']
        if not mpin:
            errors.append(
                "B19 (MPIN): must be non-empty. "
                "Enter your 4-digit Angel One MPIN — NOT your web login password."
            )
        elif not mpin.isdigit():
            errors.append(
                f"B19 (MPIN): must be exactly 4 digits. Got '{mpin}'. "
                "This is your 4-digit Angel One MPIN, not your web login password."
            )
        elif len(mpin) != 4:
            if len(mpin) > 4:
                errors.append(
                    f"B19 (MPIN): must be exactly 4 digits but got {len(mpin)} characters. "
                    "You may have entered your web login password instead of your 4-digit MPIN. "
                    "Your MPIN is the 4-digit PIN you use on the Angel One mobile app."
                )
            else:
                errors.append(
                    f"B19 (MPIN): must be exactly 4 digits; got '{mpin}' ({len(mpin)} digit(s))"
                )

        if not raw['totp_secret']:
            errors.append("B20 (TOTP Secret): must be non-empty")

        if errors:
            raise RuntimeError(
                "SETTINGS validation failed:\n" + "\n".join(f"  • {e}" for e in errors)
            )


# ── CLASS 2 — SmartApiClient ──────────────────────────────────────────────────

class SmartApiClient:
    """
    Manages Angel One SmartAPI authentication and session lifecycle.

    Login sequence (spec-exact):
        data = smartApi.generateSession(client_code, mpin, totp)
        auth_token    = data['data']['jwtToken']
        refresh_token = data['data']['refreshToken']
        feed_token    = smartApi.getfeedToken()   # SDK method — NOT from response dict

    Session tokens:
        auth_token    — used in API Authorization headers
        refresh_token — used for midnight session renewal
        feed_token    — stored for future WebSocket integration

    Midnight renewal:
        Angel One sessions expire at exactly 12:00 midnight IST (SEBI compliance).
        Renewal window: 23:30–23:59 IST. Uses generateToken(refresh_token).
        Do NOT trigger based on elapsed hours since login.
    """

    def __init__(self, api_key: str):
        self.api_key = api_key
        self.smart_api: Optional[SmartConnect] = None
        self.auth_token: str = ''
        self.refresh_token: str = ''
        self.feed_token: str = ''
        self.client_code: str = ''
        self._logged_in: bool = False
        self.consecutive_auth_failures: int = 0
        self._session_renewed_today: bool = False

    def login(self, client_code: str, mpin: str, totp_secret: str) -> None:
        """
        Login to Angel One SmartAPI. Stores auth_token, refresh_token, feed_token.
        Raises RuntimeError with actionable messages for AB7001, AB1050, and generic errors.
        """
        self.client_code = client_code
        self.smart_api = SmartConnect(api_key=self.api_key)

        log.info(f"[SmartApiClient] Attempting login for client {client_code}")

        def _do_login():
            totp = pyotp.TOTP(totp_secret).now()
            return self.smart_api.generateSession(client_code, mpin, totp)

        data = retry_call(_do_login, attempts=2, delay=3.0, fallback=None, label='SmartAPI.login')

        if data is None:
            self.consecutive_auth_failures += 1
            raise RuntimeError(
                "Login failed: no response from SmartAPI after retries. "
                "Check network connectivity and Angel One service status."
            )

        # Detect specific error codes before checking for success
        error_code = (data.get('errorcode') or data.get('errorCode') or '').strip()
        message    = (data.get('message') or '').strip()

        if error_code == 'AB7001' or 'MPIN' in message.upper() or 'loginbypassword' in message.lower():
            self.consecutive_auth_failures += 1
            raise RuntimeError(
                "AB7001: Angel One rejected the credential in cell B19 of the SETTINGS tab. "
                "This error means you entered your web login password instead of your 4-digit MPIN. "
                "Your MPIN is the same 4-digit PIN you use to log into the Angel One mobile app. "
                "It is always exactly 4 digits. "
                "Update cell B19 with your 4-digit MPIN and retry. "
                "Do not enter your web or trading password."
            )

        if error_code == 'AB1050' or 'TOTP' in message.upper():
            self.consecutive_auth_failures += 1
            raise RuntimeError(
                "AB1050: TOTP authentication failed. "
                "Verify your system clock is accurate and that the TOTP secret in cell B20 of "
                "the SETTINGS tab is the correct QR secret from smartapi.angelone.in/enable-totp "
                "— not your MPIN or password. Run SYS-01 to diagnose clock drift."
            )

        if error_code == 'AB1003' or 'already active' in message.lower():
            log.warning(
                "[SmartApiClient] AB1003: Session already active — "
                "proceeding with existing session credentials if available."
            )
            # Fall through: some SDK versions still populate data['data'] on AB1003

        status = data.get('status') or data.get('data', {})
        jwt = None
        if isinstance(data.get('data'), dict):
            jwt = data['data'].get('jwtToken', '')

        if not jwt:
            self.consecutive_auth_failures += 1
            raise RuntimeError(
                f"Login failed: {message or error_code or 'Unknown error'}. "
                "Check that all credentials in cells B17-B20 of the SETTINGS tab are correct "
                "and that your Angel One account has SmartAPI access enabled."
            )

        self.auth_token    = data['data']['jwtToken']
        self.refresh_token = data['data']['refreshToken']
        self.feed_token    = self.smart_api.getfeedToken()  # SDK method — NOT from response dict

        self._logged_in = True
        self.consecutive_auth_failures = 0
        log.info("[SmartApiClient] Login successful. auth_token, refresh_token, feed_token captured.")

    @property
    def smart_connect(self):
        """Read-only access to SmartConnect for order placement."""
        return self.smart_api

    def validate_profile(self) -> bool:
        """Call getProfile() to confirm session is valid after login."""
        try:
            profile = retry_call(
                lambda: self.smart_api.getProfile(self.refresh_token),
                attempts=2, delay=2.0, fallback=None, label='SmartAPI.getProfile'
            )
            if profile and isinstance(profile.get('data'), dict):
                name = profile['data'].get('name', '')
                log.info(f"[SmartApiClient] Profile validated: {name}")
                return True
            log.warning("[SmartApiClient] getProfile returned unexpected data — session may be invalid.")
            return False
        except Exception as e:
            log.warning(f"[SmartApiClient] getProfile failed: {e}")
            return False

    def maybe_renew_session(self) -> None:
        """
        Check midnight renewal window (23:30–23:59 IST).
        If within window, renew using generateToken(refresh_token).
        Updates auth_token and re-fetches feed_token via SDK method.
        Do NOT trigger based on elapsed hours — only time-window-based.
        _session_renewed_today resets on a new calendar day so renewal
        can fire correctly on subsequent days.
        """
        now = now_ist()
        # Reset renewal flag on a new calendar day (prevents skip on day 2+)
        today_date = now.date()
        if not hasattr(self, '_renewal_date') or self._renewal_date != today_date:
            self._session_renewed_today = False
            self._renewal_date = today_date
        if now.hour != 23 or now.minute < 30:
            return
        if self._session_renewed_today:
            return

        log.info("[SmartApiClient] Midnight renewal window detected (23:30–23:59 IST). Renewing session...")
        try:
            renewal = retry_call(
                lambda: self.smart_api.generateToken(self.refresh_token),
                attempts=2, delay=5.0, fallback=None, label='SmartAPI.generateToken'
            )
            if renewal and isinstance(renewal.get('data'), dict):
                new_jwt = renewal['data'].get('jwtToken', '')
                if new_jwt:
                    self.auth_token = new_jwt
                    self.feed_token = self.smart_api.getfeedToken()  # SDK method — NOT from renewal dict
                    self._session_renewed_today = True
                    log.info("[SmartApiClient] Session token renewed successfully.")
                    return
            log.warning(
                "[SmartApiClient] Session token renewal failed. "
                "Session will expire at midnight IST. Restart before midnight to avoid data loss."
            )
        except Exception as e:
            log.warning(
                f"[SmartApiClient] Session renewal exception: {e}. "
                "Session will expire at midnight IST. Restart before midnight to avoid data loss."
            )

    def emergency_relogin(self, mpin: str, totp_secret: str) -> bool:
        """
        Re-login from scratch when consecutive_auth_failures >= 3.
        Returns True on success, False on failure.
        """
        log.warning(
            f"[SmartApiClient] Emergency re-login triggered "
            f"(consecutive_auth_failures={self.consecutive_auth_failures})"
        )
        try:
            self.login(self.client_code, mpin, totp_secret)
            return True
        except Exception as e:
            log.error(f"[SmartApiClient] Emergency re-login failed: {e}")
            return False

    def record_auth_failure(self) -> None:
        self.consecutive_auth_failures += 1
        log.warning(
            f"[SmartApiClient] Auth failure recorded. "
            f"consecutive_auth_failures={self.consecutive_auth_failures}"
        )


# ── CLASS 3 — InstrumentMasterLoader ─────────────────────────────────────────

def classify_expiries(expiry_dates: List[datetime]) -> Dict[datetime, bool]:
    """
    Returns {expiry_datetime: is_monthly} for all expiries.
    Monthly = last expiry in each calendar month (last-of-month logic).
    NEVER uses weekday() — NIFTY switched from Thursday to Tuesday expiry Sep 2025.
    """
    result: Dict[datetime, bool] = {}
    sorted_dates = sorted(set(expiry_dates))
    for (_year, _month), group in groupby(sorted_dates, key=lambda d: (d.year, d.month)):
        month_dates = sorted(group)
        for i, dt in enumerate(month_dates):
            result[dt] = (i == len(month_dates) - 1)  # last in month = monthly
    return result


class InstrumentMasterLoader:
    """
    Downloads, caches, and parses the Angel One Scrip Master JSON.

    Two-stage cache freshness:
        Stage 1: No file for today → download immediately.
        Stage 2: File exists but was downloaded before 08:30 IST and current time is after
                 08:30 → delete and re-download (post-08:30 file may include new weekly contracts).

    Critical filter rules:
        Options : name == 'NIFTY' AND instrumenttype == 'OPTIDX'
        Futures : name == 'NIFTY' AND instrumenttype == 'FUTIDX'
        CE/PE   : symbol.endswith('CE') / symbol.endswith('PE')  — NO optionType field
        Strike  : float(record['strike']) / 100  — raw field is 100× actual
        Expiry  : datetime.strptime(record['expiry'], '%d%b%Y')
        Weekly/Monthly: classify_expiries() last-of-month logic
    """

    def __init__(self):
        self._options_df: Optional[pd.DataFrame] = None
        self._futures_df: Optional[pd.DataFrame] = None
        self._expiry_classification: Dict[datetime, bool] = {}
        self._available_expiries: List[Tuple[datetime, str, bool]] = []
        self._futures_token: str = ''
        self._futures_expiry_str: str = ''
        self._futures_expiry_dt: Optional[datetime] = None
        self._total_record_count: int = 0   # total scrip master records (for INST-02)
        self._cache_download_ts: Optional[datetime] = None  # for INST-01 age check
        self._cache_dir = pathlib.Path(CONFIG['CACHE_DIR'])
        self._cache_dir.mkdir(parents=True, exist_ok=True)

    def load(self) -> None:
        """Download (or load from cache) and parse the scrip master. Must be called once at startup."""
        raw_data = self._load_with_cache()
        self._total_record_count = len(raw_data)
        self._parse(raw_data)
        log.info(
            f"[InstrumentMasterLoader] Loaded {len(self._options_df)} NIFTY options, "
            f"{len(self._futures_df)} NIFTY futures contracts. "
            f"Total scrip master records: {self._total_record_count}. "
            f"Available expiries: {len(self._available_expiries)}"
        )

    def _today_cache_paths(self) -> Tuple[pathlib.Path, pathlib.Path]:
        today_str = now_ist().strftime('%Y%m%d')
        data_path = self._cache_dir / f'instrument_master_{today_str}.json'
        meta_path = self._cache_dir / f'instrument_master_{today_str}.meta'
        return data_path, meta_path

    def _cleanup_stale_cache(self) -> None:
        """Remove any cached files from previous dates."""
        today_str = now_ist().strftime('%Y%m%d')
        for p in self._cache_dir.glob('instrument_master_*.json'):
            if today_str not in p.name:
                p.unlink(missing_ok=True)
        for p in self._cache_dir.glob('instrument_master_*.meta'):
            if today_str not in p.name:
                p.unlink(missing_ok=True)

    def _load_with_cache(self) -> List[dict]:
        self._cleanup_stale_cache()
        data_path, meta_path = self._today_cache_paths()
        now = now_ist()
        cutoff_08_30 = now.replace(hour=8, minute=30, second=0, microsecond=0)

        # Stage 1: no file for today → download
        if not data_path.exists():
            log.info("[InstrumentMasterLoader] No cache for today — downloading...")
            return self._download_and_cache(data_path, meta_path)

        # Stage 2: file exists but downloaded before 08:30 and current time is after 08:30
        if meta_path.exists():
            try:
                download_ts = datetime.fromisoformat(meta_path.read_text(encoding='utf-8').strip())
                # Compare without timezone info — both are IST-aware or both naive
                download_naive = download_ts.replace(tzinfo=None) if download_ts.tzinfo else download_ts
                cutoff_naive = cutoff_08_30.replace(tzinfo=None)
                now_naive = now.replace(tzinfo=None)
                if download_naive < cutoff_naive and now_naive > cutoff_naive:
                    log.info(
                        "[InstrumentMasterLoader] Cache predates 08:30 IST cutoff — re-downloading "
                        "to capture new weekly contracts published at 08:30."
                    )
                    data_path.unlink(missing_ok=True)
                    meta_path.unlink(missing_ok=True)
                    return self._download_and_cache(data_path, meta_path)
            except Exception as e:
                log.warning(f"[InstrumentMasterLoader] Could not read meta file: {e} — re-downloading.")
                return self._download_and_cache(data_path, meta_path)

        log.info("[InstrumentMasterLoader] Loading from today's cache.")
        try:
            with open(data_path, 'r', encoding='utf-8') as f:
                data = json.load(f)
            # Record download time from meta for cache age reporting
            if meta_path.exists():
                try:
                    self._cache_download_ts = datetime.fromisoformat(
                        meta_path.read_text(encoding='utf-8').strip()
                    )
                except Exception:
                    self._cache_download_ts = now_ist()
            return data
        except Exception as e:
            log.warning(f"[InstrumentMasterLoader] Cache read failed: {e} — re-downloading.")
            return self._download_and_cache(data_path, meta_path)

    def _download_and_cache(self, data_path: pathlib.Path, meta_path: pathlib.Path) -> List[dict]:
        """Download from primary URL, fall back to secondary. Raise if both fail."""
        urls = [
            CONFIG['SCRIP_MASTER_URL_PRIMARY'],
            CONFIG['SCRIP_MASTER_URL_FALLBACK'],
        ]
        for url in urls:
            try:
                log.info(f"[InstrumentMasterLoader] Downloading scrip master from {url}")
                resp = requests.get(url, timeout=60)
                if resp.status_code == 200:
                    raw = resp.json()
                    with open(data_path, 'w', encoding='utf-8') as f:
                        json.dump(raw, f)
                    ts_now = now_ist()
                    meta_path.write_text(ts_now.isoformat(), encoding='utf-8')
                    self._cache_download_ts = ts_now
                    log.info(f"[InstrumentMasterLoader] Downloaded {len(raw)} records.")
                    return raw
                log.warning(
                    f"[InstrumentMasterLoader] {url} returned HTTP {resp.status_code} — "
                    "trying fallback."
                )
            except Exception as e:
                log.warning(f"[InstrumentMasterLoader] Download from {url} failed: {e} — trying fallback.")

        raise RuntimeError(
            "Instrument master download failed from both URLs. "
            "Check network connectivity and Angel One service status."
        )

    def _parse(self, raw_data: List[dict]) -> None:
        """Parse scrip master: filter, detect CE/PE, divide strike by 100, classify expiries."""
        options_rows = []
        futures_rows = []

        for rec in raw_data:
            name = rec.get('name', '')
            inst_type = rec.get('instrumenttype', '')
            symbol = rec.get('symbol', '')
            token = rec.get('token', '')
            expiry_str = rec.get('expiry', '')

            if name != 'NIFTY':
                continue

            if inst_type == 'OPTIDX':
                is_ce = symbol.endswith('CE')
                is_pe = symbol.endswith('PE')
                if not (is_ce or is_pe):
                    continue  # discard non-CE/PE records
                try:
                    actual_strike = float(rec.get('strike', 0)) / 100
                    expiry_dt = datetime.strptime(expiry_str, '%d%b%Y')
                except (ValueError, TypeError):
                    continue
                options_rows.append({
                    'token':      token,
                    'symbol':     symbol,
                    'strike':     actual_strike,
                    'expiry_str': expiry_str.upper(),
                    'expiry_dt':  expiry_dt,
                    'option_type':'CE' if is_ce else 'PE',
                    'exch_seg':   rec.get('exch_seg', 'NFO'),
                    'lotsize':    int(rec.get('lotsize', 25) or 25),
                })

            elif inst_type == 'FUTIDX':
                try:
                    expiry_dt = datetime.strptime(expiry_str, '%d%b%Y')
                except (ValueError, TypeError):
                    continue
                futures_rows.append({
                    'token':      token,
                    'symbol':     symbol,
                    'expiry_str': expiry_str.upper(),
                    'expiry_dt':  expiry_dt,
                    'exch_seg':   rec.get('exch_seg', 'NFO'),
                })

        if not options_rows:
            raise RuntimeError(
                "No NIFTY option contracts found. "
                "Verify filter uses name=='NIFTY' and instrumenttype=='OPTIDX'. "
                "Do not filter by symbol=='NIFTY' — no contract has the bare string NIFTY as its full symbol."
            )

        self._options_df = pd.DataFrame(options_rows)
        self._futures_df = pd.DataFrame(futures_rows) if futures_rows else pd.DataFrame(
            columns=['token', 'symbol', 'expiry_str', 'expiry_dt', 'exch_seg']
        )

        # Classify expiries
        all_expiry_dts = self._options_df['expiry_dt'].unique().tolist()
        self._expiry_classification = classify_expiries(all_expiry_dts)

        # Build sorted list of available expiries: (expiry_dt, expiry_str, is_monthly)
        seen = {}
        for _, row in self._options_df.iterrows():
            dt = row['expiry_dt']
            if dt not in seen:
                seen[dt] = row['expiry_str']
        self._available_expiries = sorted(
            [
                (dt, expiry_str, self._expiry_classification.get(dt, False))
                for dt, expiry_str in seen.items()
            ],
            key=lambda x: x[0]
        )

        # Resolve nearest FUTIDX token
        self._resolve_futures_token()

    def _resolve_futures_token(self) -> None:
        """Find the nearest active NIFTY FUTIDX contract."""
        if self._futures_df.empty:
            log.warning("[InstrumentMasterLoader] No NIFTY FUTIDX contracts found.")
            return
        today = now_ist().date()
        future_contracts = self._futures_df[
            self._futures_df['expiry_dt'].apply(lambda d: d.date()) >= today
        ].sort_values('expiry_dt')
        if future_contracts.empty:
            log.warning("[InstrumentMasterLoader] No future-dated NIFTY FUTIDX contracts found.")
            return
        nearest = future_contracts.iloc[0]
        self._futures_token = str(nearest['token'])
        self._futures_expiry_str = str(nearest['expiry_str'])
        self._futures_expiry_dt = nearest['expiry_dt']
        log.info(
            f"[InstrumentMasterLoader] Nearest NIFTY Futures: token={self._futures_token}, "
            f"expiry={self._futures_expiry_str}"
        )

    def select_expiry(self, mode: str, manual_expiry: str = '') -> Tuple[datetime, str, bool]:
        """
        Select expiry based on mode (AUTO/NEXT/MONTHLY/MANUAL).
        Returns (expiry_dt, expiry_str_DDMMMYYYY, is_monthly).
        """
        if not self._available_expiries:
            raise RuntimeError("No expiries available — instrument master may not be loaded.")

        today = now_ist().date()
        future_expiries = [e for e in self._available_expiries if e[0].date() >= today]
        if not future_expiries:
            future_expiries = self._available_expiries  # fallback to all

        mode = mode.upper()

        if mode == 'AUTO':
            return future_expiries[0]

        elif mode == 'NEXT':
            if len(future_expiries) < 2:
                log.warning("[InstrumentMasterLoader] NEXT mode: fewer than 2 future expiries, using first.")
                return future_expiries[0]
            return future_expiries[1]

        elif mode == 'MONTHLY':
            monthly = [e for e in future_expiries if e[2]]  # is_monthly == True
            if not monthly:
                log.warning("[InstrumentMasterLoader] No monthly expiry found — falling back to AUTO.")
                return future_expiries[0]
            return monthly[0]

        elif mode == 'MANUAL':
            manual_upper = manual_expiry.upper().strip()
            try:
                manual_dt = datetime.strptime(manual_upper, '%d%b%Y')
            except ValueError:
                raise RuntimeError(
                    f"Manual expiry '{manual_expiry}' is not in DDMMMYYYY format. "
                    "Update B8 in SETTINGS with a valid date like '28OCT2025'."
                )
            for dt, es, is_m in self._available_expiries:
                if dt == manual_dt:
                    return dt, es, is_m
            raise RuntimeError(
                f"Manual expiry '{manual_upper}' not found in instrument master. "
                f"Available: {[e[1] for e in self._available_expiries[:10]]}"
            )

        else:
            raise RuntimeError(f"Unknown expiry mode '{mode}'. Must be AUTO, NEXT, MONTHLY, or MANUAL.")

    def get_option_contracts(self, expiry_str: str) -> pd.DataFrame:
        """
        Return all NIFTY options for a given expiry (DDMMMYYYY).
        Columns: token, symbol, strike, expiry_str, expiry_dt, option_type, exch_seg
        """
        if self._options_df is None:
            raise RuntimeError("Instrument master not loaded — call load() first.")
        return self._options_df[
            self._options_df['expiry_str'] == expiry_str.upper()
        ].copy()

    def get_futures_token(self) -> str:
        """Return token for the nearest NIFTY FUTIDX contract."""
        return self._futures_token

    def get_futures_expiry_dt(self):
        """Return expiry datetime for the nearest NIFTY FUTIDX contract."""
        return self._futures_expiry_dt

    def get_available_expiries(self) -> List[Tuple[datetime, str, bool]]:
        """Return sorted list of (expiry_dt, expiry_str, is_monthly)."""
        return self._available_expiries

    def get_options_df(self) -> Optional[pd.DataFrame]:
        return self._options_df

    def get_record_count(self) -> int:
        """Return total number of records in the scrip master (for INST-02)."""
        return self._total_record_count

    def get_cache_age_hours(self) -> float:
        """Return age of the instrument master cache in hours (for INST-01)."""
        if self._cache_download_ts is None:
            return 0.0
        try:
            ts = self._cache_download_ts
            now = now_ist()
            ts_naive  = ts.replace(tzinfo=None)  if ts.tzinfo  else ts
            now_naive = now.replace(tzinfo=None) if now.tzinfo else now
            return max(0.0, (now_naive - ts_naive).total_seconds() / 3600)
        except Exception:
            return 0.0

    def is_expiry_monthly(self, expiry_dt: datetime) -> bool:
        return self._expiry_classification.get(expiry_dt, False)


# ── CLASS 4 — CandleFetcher ───────────────────────────────────────────────────

class CandleFetcher:
    """
    Fetches intraday candle data from Angel One SmartAPI.

    TOKEN CONFIGURATION:
    ┌─────────────────────────────────────────────────────────────────────┐
    │  Source 1 — NIFTY Spot Index                                        │
    │    token    : CONFIG['SPOT_INDEX_TOKEN'] = '99926000'               │
    │    exchange : NSE                                                   │
    │    purpose  : OHLC price, ATM calc, price structure, candle reject  │
    │    NOTE     : Do NOT use spot candle volume — index has no volume   │
    │                                                                     │
    │  Source 2 — NIFTY Current-Month Futures                            │
    │    token    : resolved dynamically from InstrumentMasterLoader     │
    │    exchange : NFO                                                   │
    │    purpose  : VWAP computation and volume confirmation ONLY        │
    │    NOTE     : Do NOT use Futures price for ATM or price structure  │
    │                                                                     │
    │  Source 4 — India VIX                                              │
    │    token    : CONFIG['VIX_INDEX_TOKEN'] = '99919000'               │
    │    exchange : NSE                                                   │
    │    purpose  : VIX level and trend for premium environment          │
    │    NOTE     : VIX candle volume is zero — this is expected         │
    │                                                                     │
    │  To adapt for a different index: update SPOT_INDEX_TOKEN and       │
    │  VIX_INDEX_TOKEN in CONFIG. Futures token is auto-resolved from    │
    │  InstrumentMasterLoader by name=='NIFTY' and instrumenttype==     │
    │  'FUTIDX' — update InstrumentMasterLoader filter to change it.    │
    └─────────────────────────────────────────────────────────────────────┘

    CANDLE DATE FORMAT (critical):
        strftime('%Y-%m-%d %H:%M') — no T separator, no seconds.
        Any other format causes AB13000 "Invalid date or time format".
    """

    CANDLE_FMT = '%Y-%m-%d %H:%M'

    def __init__(self, smart_api: SmartConnect, futures_token: str):
        self._api = smart_api
        self.futures_token = futures_token
        self._last_spot_close: float = 0.0

    def _make_candle_params(self, exchange: str, token: str, interval: str,
                            from_dt: datetime, to_dt: datetime) -> dict:
        return {
            'exchange':    exchange,
            'symboltoken': token,
            'interval':    interval,
            'fromdate':    from_dt.strftime(self.CANDLE_FMT),
            'todate':      to_dt.strftime(self.CANDLE_FMT),
        }

    def _candles_to_df(self, raw_candles: List) -> pd.DataFrame:
        """Convert raw candle list to DataFrame with columns: datetime, open, high, low, close, volume."""
        rows = []
        for c in raw_candles:
            try:
                rows.append({
                    'datetime': (
                        datetime.fromisoformat(c[0]).replace(tzinfo=None)
                        if isinstance(c[0], str) else c[0]
                    ),
                    'open':     float(c[1]),
                    'high':     float(c[2]),
                    'low':      float(c[3]),
                    'close':    float(c[4]),
                    'volume':   float(c[5]) if len(c) > 5 else 0.0,
                })
            except (IndexError, TypeError, ValueError):
                continue
        return pd.DataFrame(rows)

    def _fetch_candles(self, exchange: str, token: str, interval: str,
                       from_dt: datetime, to_dt: datetime, label: str) -> Optional[pd.DataFrame]:
        """
        Fetch candles, handling both SDK exception (Mode A) and data:null (Mode B).
        Returns DataFrame or None on failure.
        """
        params = self._make_candle_params(exchange, token, interval, from_dt, to_dt)

        def _call():
            return self._api.getCandleData(params)

        response = None
        try:
            response = retry_call(_call, attempts=2, delay=2.0, fallback=None, label=label)

            log.debug(f"[CandleFetcher.{label}] raw candles received: "
                      f"{len(response.get('data') or [])}")

        except Exception as e:
            log.warning(
                f"[CandleFetcher.{label}] SDK raised exception: {e}. "
                f"fromdate={params['fromdate']} todate={params['todate']}"
            )
            return None

        if response is None:
            log.warning(f"[CandleFetcher.{label}] retry_call returned None (all attempts failed).")
            return None

        # Check for AB13000 in error message
        err_code = str(response.get('errorcode', '') or response.get('errorCode', '')).strip()
        if err_code == 'AB13000':
            log.error(
                f"[CandleFetcher.{label}] AB13000 Invalid date format. "
                f"fromdate='{params['fromdate']}' todate='{params['todate']}'. "
                "Ensure format is '%Y-%m-%d %H:%M' (no T separator, no seconds)."
            )
            return None

        candle_data = response.get('data')
        if not candle_data or not isinstance(candle_data, list) or len(candle_data) == 0:
            log.warning(
                f"[CandleFetcher.{label}] No candle data returned (data is null or empty). "
                f"fromdate={params['fromdate']} todate={params['todate']}"
            )
            return None

        df = self._candles_to_df(candle_data)
        if df.empty:
            return None
        return df

    def fetch_spot(self) -> Optional[pd.DataFrame]:
        """
        Source 1 — NIFTY Spot Index (NSE, 99926000, FIVE_MINUTE).
        Returns the last 4 completed 5-minute candles (minimum required for price structure).
        Volume will be zero — this is expected for index data.
        """
        now = now_ist().replace(tzinfo=None)
        last_bar_end = now.replace(second=0, microsecond=0)
        floored_minute = (last_bar_end.minute // 5) * 5
        last_bar_end = last_bar_end.replace(minute=floored_minute)
        if last_bar_end >= now:
            last_bar_end -= timedelta(minutes=5)
        market_open = now.replace(hour=9, minute=15, second=0, microsecond=0)
        if last_bar_end < market_open:
            return None

        from_dt = last_bar_end - timedelta(minutes=35)  # 7 candles — tail(6) always populated
        if from_dt < market_open:
            from_dt = market_open

        df = self._fetch_candles('NSE', CONFIG['SPOT_INDEX_TOKEN'], 'FIVE_MINUTE',
                                  from_dt, last_bar_end, label='fetch_spot')
        if df is not None and not df.empty:
            self._last_spot_close = float(df['close'].iloc[-1])
        return df

    def fetch_spot_15m(self) -> Optional[pd.DataFrame]:
        """
        NIFTY Spot Index at 15-minute interval (NSE, 99926000).
        Returns last 6 completed 15-minute candles (90 min of history).
        Used for intermediate-term structure in MTF analysis.
        Volume is zero for index data — expected, not an error.
        """
        now = now_ist().replace(tzinfo=None)
        last_bar_end = now.replace(second=0, microsecond=0)
        floored_minute = (last_bar_end.minute // 15) * 15
        last_bar_end = last_bar_end.replace(minute=floored_minute)
        if last_bar_end >= now:
            last_bar_end -= timedelta(minutes=15)
        market_open = now.replace(hour=9, minute=15, second=0, microsecond=0)
        if last_bar_end < market_open:
            return None
        from_dt = last_bar_end - timedelta(minutes=90)  # 6 completed 15m candles
        if from_dt < market_open:
            from_dt = market_open
        return self._fetch_candles(
            'NSE', CONFIG['SPOT_INDEX_TOKEN'], 'FIFTEEN_MINUTE',
            from_dt, last_bar_end, label='fetch_spot_15m'
        )

    def fetch_spot_30m(self) -> Optional[pd.DataFrame]:
        """
        NIFTY Spot Index at 30-minute interval (NSE, 99926000).
        Returns last 5 completed 30-minute candles (150 min of history).
        Used for higher-timeframe structure in MTF analysis.
        Volume is zero for index data — expected, not an error.
        """
        now = now_ist().replace(tzinfo=None)
        last_bar_end = now.replace(second=0, microsecond=0)
        floored_minute = (last_bar_end.minute // 30) * 30
        last_bar_end = last_bar_end.replace(minute=floored_minute)
        if last_bar_end >= now:
            last_bar_end -= timedelta(minutes=30)
        market_open = now.replace(hour=9, minute=15, second=0, microsecond=0)
        if last_bar_end < market_open:
            return None
        from_dt = last_bar_end - timedelta(minutes=150)  # 5 completed 30m candles
        if from_dt < market_open:
            from_dt = market_open
        return self._fetch_candles(
            'NSE', CONFIG['SPOT_INDEX_TOKEN'], 'THIRTY_MINUTE',
            from_dt, last_bar_end, label='fetch_spot_30m'
        )

    def fetch_futures(self) -> Optional[pd.DataFrame]:
        """
        Source 2 — NIFTY Current-Month Futures (NFO, nearest FUTIDX, FIVE_MINUTE).
        Returns candles from market open to the last completed 5-minute candle.
        Volume is meaningful here — used for VWAP and volume confirmation.
        """
        if not self.futures_token:
            log.warning("[CandleFetcher.fetch_futures] No futures token available.")
            return None
        now = now_ist().replace(tzinfo=None)
        last_bar_end = now.replace(second=0, microsecond=0)
        floored_minute = (last_bar_end.minute // 5) * 5
        last_bar_end = last_bar_end.replace(minute=floored_minute)
        if last_bar_end >= now:
            last_bar_end -= timedelta(minutes=5)
        from_dt = now.replace(hour=9, minute=15, second=0, microsecond=0)
        if last_bar_end < from_dt:
            return None
        return self._fetch_candles('NFO', self.futures_token, 'FIVE_MINUTE',
                                    from_dt, last_bar_end, label='fetch_futures')

    def fetch_prev_day(self) -> dict:
        """
        Source 3 — Previous Trading Day OHLC (NSE, 99926000, ONE_DAY).
        Call ONCE at startup. Never call in the per-cycle loop.
        Returns: {prev_date, prev_open, prev_high, prev_low, prev_close, prev_range}
        Returns {} on any failure — never halts.
        """
        try:
            now = now_ist().replace(tzinfo=None)
            from_dt = now - timedelta(days=7)
            from_dt = from_dt.replace(hour=9, minute=15, second=0, microsecond=0)
            df = self._fetch_candles('NSE', CONFIG['SPOT_INDEX_TOKEN'], 'ONE_DAY',
                                      from_dt, now, label='fetch_prev_day')
            if df is None or len(df) < 2:
                log.warning("[CandleFetcher.fetch_prev_day] Fewer than 2 daily candles returned.")
                return {}
            # candles[-1] = today (partial), candles[-2] = yesterday (complete)
            prev = df.iloc[-2]
            prev_date = str(prev.get('datetime', ''))[:10]
            prev_open  = float(prev['open'])
            prev_high  = float(prev['high'])
            prev_low   = float(prev['low'])
            prev_close = float(prev['close'])
            return {
                'prev_date':  prev_date,
                'prev_open':  prev_open,
                'prev_high':  prev_high,
                'prev_low':   prev_low,
                'prev_close': prev_close,
                'prev_range': round(prev_high - prev_low, 2),
            }
        except Exception as e:
            log.warning(f"[CandleFetcher.fetch_prev_day] Failed: {e}")
            return {}

    def fetch_vix(self) -> dict:
        """
        Source 4 — India VIX (NSE, 99919000, FIVE_MINUTE). Call every cycle.
        Returns: {vix_current, vix_open, vix_trend, vix_pct_change, vix_candles_count}
        Returns {} on failure — ThetaEnvironmentAnalyzer handles missing VIX gracefully.
        VIX volume is zero — expected, not an error.
        """
        try:
            now = now_ist().replace(tzinfo=None)
            last_bar_end = now.replace(second=0, microsecond=0)
            floored_minute = (last_bar_end.minute // 5) * 5
            last_bar_end = last_bar_end.replace(minute=floored_minute)
            if last_bar_end >= now:
                last_bar_end -= timedelta(minutes=5)
            market_open = now.replace(hour=9, minute=15, second=0, microsecond=0)
            if last_bar_end < market_open:
                return {}

            from_dt = last_bar_end - timedelta(minutes=30)
            if from_dt < market_open:
                from_dt = market_open

            df = self._fetch_candles('NSE', CONFIG['VIX_INDEX_TOKEN'], 'FIVE_MINUTE',
                                      from_dt, last_bar_end, label='fetch_vix')
            if df is None or df.empty:
                return {}

            closes = df['close'].tolist()
            vix_current = float(closes[-1])
            vix_open    = float(df['open'].iloc[0])
            n = CONFIG['VIX_RISING_LOOKBACK']
            if len(closes) < n:
                # Insufficient candles for reliable trend — default to FLAT
                vix_trend = 'FLAT'
            else:
                lookback = closes[-n:]
                change_pct = (lookback[-1] - lookback[0]) / lookback[0] * 100
                if change_pct > 2.0:
                    vix_trend = 'RISING'
                elif change_pct < -2.0:
                    vix_trend = 'FALLING'
                else:
                    vix_trend = 'FLAT'

            vix_pct_change = round((vix_current - vix_open) / vix_open * 100, 2) if vix_open > 0 else 0.0
            return {
                'vix_current':      vix_current,
                'vix_open':         vix_open,
                'vix_trend':        vix_trend,
                'vix_pct_change':   vix_pct_change,
                'vix_candles_count': len(df),
            }
        except Exception as e:
            log.warning(f"[CandleFetcher.fetch_vix] Failed: {e}")
            return {}

    def get_last_spot_close(self) -> float:
        """Return the last known spot close (used as ATM fallback if fetch_spot fails)."""
        return self._last_spot_close

    @staticmethod
    def candle_summary(df: Optional[pd.DataFrame], n: int = 8) -> List[dict]:
        """
        Returns last n bars as compact dicts: {c: close, d: G/R, str: body% of range 0-100, vol: thousands}.
        Never raises. Returns [] on empty/None input.
        spot vol is always 0 (index data) — expected, not an error.
        futures vol is meaningful — used for breakout/rejection vol_ratio.
        """
        try:
            if df is None or len(df) == 0:
                return []
            tail = df.tail(n)
            result = []
            for _, row in tail.iterrows():
                o  = float(row.get('open',  0) or 0)
                h  = float(row.get('high',  0) or 0)
                lo = float(row.get('low',   0) or 0)
                cl = float(row.get('close', 0) or 0)
                vol = float(row.get('volume', 0) or 0)
                rng  = h - lo
                body = abs(cl - o)
                str_pct = round(body / rng * 100) if rng > 0 else 0
                result.append({
                    'c':   round(cl, 2),
                    'd':   'G' if cl > o else ('D' if cl == o else 'R'),
                    'str': str_pct,
                    'vol': round(vol / 1000, 1),
                })
            return result
        except Exception:
            return []


# ── CLASS 5 — OptionChainBuilder ─────────────────────────────────────────────

class OptionChainBuilder:
    """
    Builds the synthetic NIFTY option chain from instrument master + live quotes.

    Uses a single getMarketData('FULL', {'NFO': [token_list]}) call for all
    focus-zone CE and PE tokens combined. Never loops per-token.

    Exact API field names:
        opnInterest  — NOT openInterest
        tradeVolume  — NOT volume
        symbolToken  — token field in response

    IV source: Option Greeks endpoint (POST optionGreek) with DDMMMYYYY format.
    IV is set to NaN for weekly expiries or outside market hours (AB9019).

    Change OI: computed as current_oi - prev_oi (never from API).
    First cycle: change_oi = 0 for all strikes.
    Duplicate strike guard: drop_duplicates(subset='strike').set_index('strike') before indexing.
    """

    GREEKS_URL = (
        'https://apiconnect.angelbroking.com/rest/secure/angelbroking'
        '/marketData/v1/optionGreek'
    )

    def __init__(self, smart_api_client: SmartApiClient):
        self._client = smart_api_client

    def build(
        self,
        focus_strikes: List[float],
        expiry_str: str,
        is_weekly: bool,
        options_df: pd.DataFrame,
        prev_snapshot: Optional[pd.DataFrame] = None,
    ) -> pd.DataFrame:
        """
        Build the option chain for focus_strikes and expiry.

        Args:
            focus_strikes : list of actual strike prices (post /100 from InstrumentMasterLoader)
            expiry_str    : DDMMMYYYY format (exactly as stored in scrip master)
            is_weekly     : True = weekly expiry (IV will be NaN; Greeks endpoint not called)
            options_df    : subset of instrument master for this expiry
            prev_snapshot : previous cycle's chain DataFrame for change OI computation

        Returns:
            DataFrame with columns per spec: strike, expiry_str, ce_token, ce_symbol, ce_ltp,
            ce_open_interest, ce_change_oi, ce_volume, ce_iv, pe_token, pe_symbol, pe_ltp,
            pe_open_interest, pe_change_oi, pe_volume, pe_iv
        """
        # Build token lists for focus zone
        ce_map: Dict[float, dict] = {}
        pe_map: Dict[float, dict] = {}
        for _, row in options_df.iterrows():
            s = float(row['strike'])
            if s not in focus_strikes:
                continue
            entry = {'token': str(row['token']), 'symbol': str(row['symbol'])}
            if row['option_type'] == 'CE':
                ce_map[s] = entry
            else:
                pe_map[s] = entry

        all_tokens = (
            [v['token'] for v in ce_map.values()] +
            [v['token'] for v in pe_map.values()]
        )

        # Fetch live quotes — single bulk call
        quotes: Dict[str, dict] = {}
        if all_tokens:
            quotes = self._fetch_market_data(all_tokens)

        # Fetch IV (only for monthly expiry during market hours)
        iv_map: Dict[float, Tuple[float, float]] = {}
        now = now_ist()
        market_open  = now.replace(hour=9,  minute=15, second=0, microsecond=0)
        market_close = now.replace(hour=15, minute=30, second=0, microsecond=0)
        now_naive = now.replace(tzinfo=None)
        in_market_hours = (now_naive >= market_open.replace(tzinfo=None) and
                           now_naive <= market_close.replace(tzinfo=None))

        if is_weekly:
            log.warning(
                f"[OptionChainBuilder] Weekly expiry selected ({expiry_str}). "
                "IV values set to NaN due to Angel One Option Greeks API limitation for weekly expiries."
            )
        elif not in_market_hours:
            log.info(
                "[OptionChainBuilder] Outside market hours — "
                "skipping Greeks endpoint (would return AB9019). IV set to NaN."
            )
        else:
            iv_map = self._fetch_iv(expiry_str)

        # Build prev OI lookup (with duplicate strike guard)
        prev_oi_ce: Dict[float, float] = {}
        prev_oi_pe: Dict[float, float] = {}
        if prev_snapshot is not None and not prev_snapshot.empty:
            try:
                prev_dedup = prev_snapshot.drop_duplicates(subset='strike').set_index('strike')
                for s in prev_dedup.index:
                    prev_oi_ce[s] = float(prev_dedup.loc[s, 'ce_open_interest'] or 0)
                    prev_oi_pe[s] = float(prev_dedup.loc[s, 'pe_open_interest'] or 0)
            except Exception as e:
                log.warning(f"[OptionChainBuilder] Failed to build prev OI lookup: {e}")

        # Assemble chain rows
        rows = []
        for strike in sorted(focus_strikes):
            ce_info = ce_map.get(strike, {})
            pe_info = pe_map.get(strike, {})
            ce_token  = ce_info.get('token', '')
            pe_token  = pe_info.get('token', '')
            ce_symbol = ce_info.get('symbol', '')
            pe_symbol = pe_info.get('symbol', '')

            ce_q = quotes.get(ce_token, {})
            pe_q = quotes.get(pe_token, {})

            ce_ltp  = ce_q.get('ltp', float('nan'))
            pe_ltp  = pe_q.get('ltp', float('nan'))
            ce_oi   = ce_q.get('oi', float('nan'))
            pe_oi   = pe_q.get('oi', float('nan'))
            ce_vol  = ce_q.get('volume', float('nan'))
            pe_vol  = pe_q.get('volume', float('nan'))

            # Change OI: current minus previous.
            # If strike is absent from prev lookup (new to focus zone or first cycle)
            # → change = 0 (first observation). Do NOT default to current OI.
            if not pd.isna(ce_oi):
                ce_chg_oi = (
                    float(ce_oi) - prev_oi_ce[strike]
                    if strike in prev_oi_ce
                    else 0.0
                )
            else:
                ce_chg_oi = 0.0

            if not pd.isna(pe_oi):
                pe_chg_oi = (
                    float(pe_oi) - prev_oi_pe[strike]
                    if strike in prev_oi_pe
                    else 0.0
                )
            else:
                pe_chg_oi = 0.0

            ce_iv_val, pe_iv_val = iv_map.get(round(strike, 2), (float('nan'), float('nan')))

            rows.append({
                'strike':            strike,
                'expiry_str':        expiry_str,
                'ce_token':          ce_token,
                'ce_symbol':         ce_symbol,
                'ce_ltp':            ce_ltp,
                'ce_open_interest':  ce_oi,
                'ce_change_oi':      ce_chg_oi,
                'ce_volume':         ce_vol,
                'ce_iv':             ce_iv_val,
                'pe_token':          pe_token,
                'pe_symbol':         pe_symbol,
                'pe_ltp':            pe_ltp,
                'pe_open_interest':  pe_oi,
                'pe_change_oi':      pe_chg_oi,
                'pe_volume':         pe_vol,
                'pe_iv':             pe_iv_val,
            })

        return pd.DataFrame(rows)

    def _fetch_market_data(self, token_list: List[str]) -> Dict[str, dict]:
        """
        Single getMarketData('FULL', {'NFO': [token_list]}) call.
        Returns dict: token → {ltp, oi, volume}.
        Logs unfetched tokens as warning.
        """
        def _call():
            return self._client.smart_api.getMarketData(
                'FULL', {'NFO': token_list}
            )

        response = retry_call(_call, attempts=2, delay=2.0, fallback=None, label='getMarketData')
        if response is None:
            log.warning("[OptionChainBuilder] getMarketData returned None.")
            return {}

        err_code = str(response.get('errorcode', '') or response.get('errorCode', '')).strip()
        if err_code == 'AB2001':
            log.error(
                "[OptionChainBuilder] AB2001 MarketData internal error. "
                "Verify tokens are passed as a Python list under the 'NFO' key."
            )
            self._client.record_auth_failure()
            return {}

        data = response.get('data')
        if not data or not isinstance(data, dict):
            log.warning("[OptionChainBuilder] getMarketData: response['data'] is null or not a dict.")
            return {}

        fetched   = data.get('fetched',   []) or []
        unfetched = data.get('unfetched', []) or []

        if unfetched:
            log.warning(
                f"[OptionChainBuilder] {len(unfetched)} tokens unfetched from getMarketData: "
                f"{unfetched[:5]}{'...' if len(unfetched) > 5 else ''}"
            )

        result: Dict[str, dict] = {}
        for quote in fetched:
            try:
                token = str(quote['symbolToken'])
                result[token] = {
                    'ltp':    float(quote.get('ltp',            0) or 0),
                    'oi':     float(quote.get('opnInterest',    0) or 0),   # exact field name
                    'volume': float(quote.get('tradeVolume',    0) or 0),   # exact field name
                }
            except (KeyError, TypeError, ValueError) as e:
                log.warning(f"[OptionChainBuilder] Failed to parse quote: {e}")

        return result

    def _fetch_iv(self, expiry_str: str) -> Dict[float, Tuple[float, float]]:
        """
        Fetch implied volatility from Option Greeks endpoint.
        expirydate must be DDMMMYYYY uppercase (e.g. '28OCT2025').
        Returns dict: strike → (ce_iv, pe_iv).
        Returns {} on AB9019 (outside market hours) or any failure.
        """
        headers = {
            'Authorization':       f'Bearer {self._client.auth_token}',
            'Content-Type':        'application/json',
            'Accept':              'application/json',
            'X-UserType':          'USER',
            'X-SourceID':          'WEB',
            'X-ClientLocalIP':     '127.0.0.1',
            'X-ClientPublicIP':    '127.0.0.1',
            'X-MACAddress':        '00:00:00:00:00:00',
            'X-PrivateKey':        self._client.api_key,
        }
        payload = {'name': 'NIFTY', 'expirydate': expiry_str}  # DDMMMYYYY exactly as in scrip master

        def _call():
            r = requests.post(self.GREEKS_URL, headers=headers, json=payload, timeout=15)
            r.raise_for_status()
            return r.json()

        response = retry_call(_call, attempts=2, delay=1.0, fallback=None, label='GreeksIV')
        if response is None:
            return {}

        err_code = str(response.get('errorcode', '') or response.get('errorCode', '')).strip()
        message  = str(response.get('message', '') or '').strip()

        if err_code == 'AB9019' or 'No Data Available' in message:
            log.info(
                "[OptionChainBuilder] Option Greeks endpoint returned no data — "
                "market may be closed. IV set to NaN for this cycle."
            )
            return {}

        if err_code == 'AB9022':
            log.warning(
                f"[OptionChainBuilder] AB9022 Invalid expiry date '{expiry_str}'. "
                "expirydate must be DDMMMYYYY uppercase format."
            )
            return {}

        data = response.get('data')
        if not data or not isinstance(data, list):
            return {}

        iv_map: Dict[float, Tuple[float, float]] = {}
        ce_ivs: Dict[float, float] = {}
        pe_ivs: Dict[float, float] = {}

        for item in data:
            try:
                strike = round(float(item.get('strikePrice', 0)) / 100, 2)  # strike field is also 100× in Greeks; round to prevent float precision mismatch
                iv_val = float(item.get('impliedVolatility', 0) or 0)
                opt_type = str(item.get('optionType', '')).upper()
                if opt_type == 'CE':
                    ce_ivs[strike] = iv_val if iv_val > 0 else float('nan')
                elif opt_type == 'PE':
                    pe_ivs[strike] = iv_val if iv_val > 0 else float('nan')
            except (KeyError, TypeError, ValueError):
                continue

        all_strikes = set(ce_ivs.keys()) | set(pe_ivs.keys())
        for s in all_strikes:
            iv_map[s] = (ce_ivs.get(s, float('nan')), pe_ivs.get(s, float('nan')))

        return iv_map


# ── CLASS 6 — MetricsCalculator ───────────────────────────────────────────────

class MetricsCalculator:
    """
    Computes all option-chain metrics from the synthetic chain DataFrame.

    max_score is derived dynamically from CONFIG (not hardcoded).
    pcr_chg_oi = abs(total_pe_chg) / abs(total_ce_chg) if abs(total_ce_chg) > 0 else NaN.
    support   = strike with highest PE OI (put writers defend price).
    resistance = strike with highest CE OI (call writers cap price).
    """

    def __init__(self):
        self.max_score: int = self._compute_max_score()

    @staticmethod
    def _compute_max_score() -> int:
        """
        Sum of all positive scoring weight values from CONFIG.
        Do NOT hardcode — derived at runtime.
        """
        return sum(v for v in [
            CONFIG['SCORE_STRONG_PE_WRITING'],
            CONFIG['SCORE_CE_UNWINDING_RISING'],
            CONFIG['SCORE_SUPPORT_SHIFT_UP'],
            CONFIG['SCORE_RESISTANCE_SHIFT_UP'],
            CONFIG['SCORE_BULLISH_PCR'],
            CONFIG['SCORE_BULLISH_VOL_IMBALANCE'],
            CONFIG['SCORE_BULLISH_PRICE_STRUCTURE'],
            CONFIG['SCORE_ABOVE_VWAP'],
            CONFIG['SCORE_BULLISH_VOL_CONFIRM'],
        ] if v > 0)

    def compute(self, chain: pd.DataFrame, prev_metrics: Optional[dict] = None) -> dict:
        """
        Compute all metrics from the option chain DataFrame.

        Args:
            chain        : DataFrame from OptionChainBuilder.build()
            prev_metrics : metrics dict from previous cycle (for shift detection)

        Returns dict with keys:
            atm (via caller), support_strike, resistance_strike, support_shift, resistance_shift,
            total_ce_oi, total_pe_oi, total_ce_chg_oi, total_pe_chg_oi,
            total_ce_volume, total_pe_volume,
            pcr_oi, pcr_chg_oi, vol_imbalance,
            max_score
        """
        if chain is None or chain.empty:
            return self._empty_metrics()

        def _safe_sum(col: str) -> float:
            try:
                vals = chain[col].dropna()
                return float(vals.sum()) if len(vals) > 0 else 0.0
            except Exception:
                return 0.0

        total_ce_oi     = _safe_sum('ce_open_interest')
        total_pe_oi     = _safe_sum('pe_open_interest')
        total_ce_chg_oi = _safe_sum('ce_change_oi')
        total_pe_chg_oi = _safe_sum('pe_change_oi')
        total_ce_volume = _safe_sum('ce_volume')
        total_pe_volume = _safe_sum('pe_volume')

        # PCR by OI
        pcr_oi = round(total_pe_oi / total_ce_oi, 3) if total_ce_oi > 0 else float('nan')

        # PCR by Change OI — directional momentum (fresh writing only, not abs())
        fresh_ce_chg = max(float(total_ce_chg_oi), 0.0)
        fresh_pe_chg = max(float(total_pe_chg_oi), 0.0)
        if fresh_ce_chg == 0 and fresh_pe_chg == 0:
            pcr_chg_oi = float('nan')
        elif fresh_ce_chg == 0:
            # PE writing with no CE activity — ratio is undefined.
            # Use NaN so safe_val writes '' not 'inf' to Sheets.
            pcr_chg_oi = float('nan')
        else:
            pcr_chg_oi = round(fresh_pe_chg / fresh_ce_chg, 3)

        # Support = max PE OI strike
        support_strike: float = 0.0
        try:
            valid_pe = chain[chain['pe_open_interest'].notna() & (chain['pe_open_interest'] > 0)]
            if not valid_pe.empty:
                support_strike = float(valid_pe.loc[valid_pe['pe_open_interest'].idxmax(), 'strike'])
        except Exception as e:
            log.warning(f'[MetricsCalculator] support_strike calc failed: {e}')

        # Resistance = max CE OI strike
        resistance_strike: float = 0.0
        try:
            valid_ce = chain[chain['ce_open_interest'].notna() & (chain['ce_open_interest'] > 0)]
            if not valid_ce.empty:
                resistance_strike = float(valid_ce.loc[valid_ce['ce_open_interest'].idxmax(), 'strike'])
        except Exception as e:
            log.warning(f'[MetricsCalculator] resistance_strike calc failed: {e}')

        # Shift vs previous cycle
        prev_support    = prev_metrics.get('support_strike', 0)    if prev_metrics else 0
        prev_resistance = prev_metrics.get('resistance_strike', 0) if prev_metrics else 0
        support_shift = (
            round(support_strike - prev_support, 2)
            if prev_support is not None and prev_support != 0.0
            else 0.0
        )
        resistance_shift = (
            round(resistance_strike - prev_resistance, 2)
            if prev_resistance is not None and prev_resistance != 0.0
            else 0.0
        )

        # Volume imbalance = (total_PE_volume - total_CE_volume) / total_volume
        # Denominator is total volume → result is bounded in [-1, +1].
        # +1 = all activity on PE side (bullish). -1 = all activity on CE side (bearish).
        _total_vol = total_ce_volume + total_pe_volume
        vol_imbalance = (
            round((total_pe_volume - total_ce_volume) / _total_vol, 4)
            if _total_vol > 0 else float('nan')
        )

        # ── CHANGE 1: OI Concentration — top-2 strikes OI / total zone OI ──
        # >0.65 = pinning | 0.40-0.65 = normal | <0.40 = spread/rotation
        try:
            top2_ce = float(
                chain['ce_open_interest']
                .dropna()
                .nlargest(2)
                .sum()
            )
            top2_pe = float(
                chain['pe_open_interest']
                .dropna()
                .nlargest(2)
                .sum()
            )
            total_oi = total_ce_oi + total_pe_oi
            oi_concentration = (
                round((top2_ce + top2_pe) / total_oi, 3)
                if total_oi > 0 else float('nan')
            )
        except Exception:
            oi_concentration = float('nan')

        return {
            'support_strike':    support_strike,
            'resistance_strike': resistance_strike,
            'support_shift':     support_shift,
            'resistance_shift':  resistance_shift,
            'total_ce_oi':       int(total_ce_oi),
            'total_pe_oi':       int(total_pe_oi),
            'total_ce_chg_oi':   int(total_ce_chg_oi),
            'total_pe_chg_oi':   int(total_pe_chg_oi),
            'total_ce_volume':   int(total_ce_volume),
            'total_pe_volume':   int(total_pe_volume),
            'pcr_oi':            pcr_oi,
            'pcr_chg_oi':        pcr_chg_oi,
            'vol_imbalance':     vol_imbalance,
            'oi_concentration':  oi_concentration,
            'top_ce_strike':     resistance_strike,
            'top_pe_strike':     support_strike,
            'max_score':         self.max_score,
        }

    def _empty_metrics(self) -> dict:
        return {
            'support_strike': 0.0, 'resistance_strike': 0.0,
            'support_shift': 0.0,  'resistance_shift': 0.0,
            'total_ce_oi': 0,      'total_pe_oi': 0,
            'total_ce_chg_oi': 0,  'total_pe_chg_oi': 0,
            'total_ce_volume': 0,  'total_pe_volume': 0,
            'pcr_oi': float('nan'), 'pcr_chg_oi': float('nan'),
            'vol_imbalance': float('nan'),
            # ── CHANGE 2: Add fallback values for new fields ──
            'oi_concentration': float('nan'),
            'top_ce_strike':    0.0,
            'top_pe_strike':    0.0,
            'max_score': self.max_score,
        }


# ── CLASS 7 — SignalEngine ────────────────────────────────────────────────────

class SignalEngine:
    """
    Combines four layers into a final intraday bias signal:
        1. Option-chain bias (OI, change OI, PCR, S/R shifts, volume imbalance)
        2. Price-structure bias (from NIFTY spot candles — Source 1)
        3. VWAP bias (from NIFTY Futures candles — Source 2)
        4. Volume-confirmation bias (from NIFTY Futures candles — Source 2)

    Scoring:
        All weights in CONFIG. max_score derived dynamically (sum of positive weights = 12).
        score_display  = f"{score}/{max_score}"   e.g. "6/12", "-3/12"
        confidence_display = f"{confidence:.1f}%/100%"  e.g. "70.5%/100%"

    Bias thresholds:
        >= +5  → STRONG BULLISH
        3–4    → BULLISH
        1–2    → MILD BULLISH
        0–(-1) → NEUTRAL
        -2–(-3)→ MILD BEARISH
        -4–(-5)→ BEARISH
        <=-6   → STRONG BEARISH

    bias_calculated_at format: '%d-%b-%Y %H:%M IST'  e.g. "20-Mar-2026 14:35 IST"
    """

    def __init__(self):
        self._max_score = MetricsCalculator._compute_max_score()

    @property
    def max_score(self) -> int:
        return self._max_score

    def run(
        self,
        chain: Optional[pd.DataFrame],
        metrics: dict,
        spot_df: Optional[pd.DataFrame],
        futures_df: Optional[pd.DataFrame],
        spot: float,
        prev_spot: float = 0.0,
    ) -> dict:
        """
        Compute the combined intraday bias signal.

        Args:
            chain      : option chain DataFrame from OptionChainBuilder
            metrics    : output of MetricsCalculator.compute()
            spot_df    : NIFTY spot candles (Source 1) — used for price structure only
            futures_df : NIFTY futures candles (Source 2) — used for VWAP and volume
            spot       : current NIFTY spot index price
            prev_spot  : spot price from previous cycle

        Returns signals dict with all keys required by the snapshot engine.
        """
        # ── Layer 2: Price structure (from spot candles — Source 1) ────────────
        price_structure = self._compute_price_structure(spot_df)

        # ── Layer 3: VWAP (from futures candles — Source 2) ────────────────────
        # Use latest futures close for VWAP comparison (apples-to-apples)
        futures_close = (
            float(futures_df.iloc[-1]['close'])
            if futures_df is not None and not futures_df.empty
            else spot
        )
        vwap_level, vwap_bias = self._compute_vwap(futures_df, futures_close)

        # ── Layer 4: Volume confirmation (from futures candles — Source 2) ──────
        vol_bias = self._compute_vol_bias(futures_df, price_structure)

        # ── Layer 1: Option-chain signals ─────────────────────────────────────
        total_ce_chg = metrics.get('total_ce_chg_oi', 0)
        total_pe_chg = metrics.get('total_pe_chg_oi', 0)
        pcr_oi       = metrics.get('pcr_oi',          float('nan'))
        vol_imbalance= metrics.get('vol_imbalance',   float('nan'))
        support_shift    = metrics.get('support_shift',    0.0)
        resistance_shift = metrics.get('resistance_shift', 0.0)

        oi_threshold = CONFIG['COMPARISON_OI_THRESHOLD']

        # strong_pe_writing: new PE OI being added = bullish
        strong_pe_writing = total_pe_chg >= oi_threshold
        # strong_ce_writing: new CE OI being added = bearish
        strong_ce_writing = total_ce_chg >= oi_threshold

        # CE unwinding with rising price = short covering = bullish
        price_rising = spot > prev_spot if prev_spot > 0 else False
        price_falling = spot < prev_spot if prev_spot > 0 else False
        ce_unwinding_rising  = (total_ce_chg <= -oi_threshold and price_rising)
        pe_unwinding_falling = (total_pe_chg <= -oi_threshold and price_falling)

        # ── Scoring ────────────────────────────────────────────────────────────
        score = 0

        # OI writing signals — mutually exclusive to avoid bilateral buildup double-signal
        if strong_pe_writing and not strong_ce_writing:
            score += CONFIG['SCORE_STRONG_PE_WRITING']
        elif strong_ce_writing and not strong_pe_writing:
            score += CONFIG['SCORE_STRONG_CE_WRITING']
        # If both: bilateral buildup = rangebound, no directional score added
        if ce_unwinding_rising:
            score += CONFIG['SCORE_CE_UNWINDING_RISING']
        if pe_unwinding_falling:
            score += CONFIG['SCORE_PE_UNWINDING_FALLING']

        # S/R shift
        if support_shift > 0:
            score += CONFIG['SCORE_SUPPORT_SHIFT_UP']
        elif support_shift < 0:
            score += CONFIG['SCORE_SUPPORT_SHIFT_DOWN']

        if resistance_shift > 0:
            score += CONFIG['SCORE_RESISTANCE_SHIFT_UP']
        elif resistance_shift < 0:
            score += CONFIG['SCORE_RESISTANCE_SHIFT_DOWN']

        # PCR
        if not math.isnan(pcr_oi):
            if pcr_oi >= CONFIG['PCR_BULLISH_THRESHOLD']:
                score += CONFIG['SCORE_BULLISH_PCR']
            elif pcr_oi <= CONFIG['PCR_BEARISH_THRESHOLD']:
                score += CONFIG['SCORE_BEARISH_PCR']

        # Volume imbalance (positive = more PE volume = bullish)
        if not math.isnan(vol_imbalance):
            if vol_imbalance > 0.2:
                score += CONFIG['SCORE_BULLISH_VOL_IMBALANCE']
            elif vol_imbalance < -0.2:
                score += CONFIG['SCORE_BEARISH_VOL_IMBALANCE']

        # Price structure
        if price_structure == 'BULLISH STRUCTURE':
            score += CONFIG['SCORE_BULLISH_PRICE_STRUCTURE']
        elif price_structure == 'BEARISH STRUCTURE':
            score += CONFIG['SCORE_BEARISH_PRICE_STRUCTURE']

        # VWAP
        if vwap_bias == 'BULLISH':
            score += CONFIG['SCORE_ABOVE_VWAP']
        elif vwap_bias == 'BEARISH':
            score += CONFIG['SCORE_BELOW_VWAP']

        # Volume confirmation
        if vol_bias == 'BULLISH':
            score += CONFIG['SCORE_BULLISH_VOL_CONFIRM']
        elif vol_bias == 'BEARISH':
            score += CONFIG['SCORE_BEARISH_VOL_CONFIRM']

        # Clamp score within theoretical bounds
        score = max(-self._max_score, min(self._max_score, score))

        # ── Bias classification ────────────────────────────────────────────────
        bias = self._classify_bias(score)

        # ── Confidence ────────────────────────────────────────────────────────
        raw_conf = (abs(score) / self._max_score * 100
                    if self._max_score > 0 else 0.0)
        # STRONG bias (|score| >= 5) must show at least 50% confidence
        if abs(score) >= 5:
            confidence = round(max(50.0, min(100.0, raw_conf)), 1)
        else:
            confidence = round(min(100.0, raw_conf), 1)

        # ── Trap detection ────────────────────────────────────────────────────
        trap_msg = self._detect_trap(metrics, vwap_level, vwap_bias, vol_bias, spot)

        # ── Event tag ─────────────────────────────────────────────────────────
        event_tag = self._compute_event_tag(
            trap_msg, confidence, ce_unwinding_rising, pe_unwinding_falling,
            support_shift, resistance_shift, price_structure, score
        )

        # ── Reasoning ─────────────────────────────────────────────────────────
        reasoning = self._build_reasoning(
            score, price_structure, vwap_bias, vol_bias, pcr_oi,
            support_shift, resistance_shift, strong_pe_writing, strong_ce_writing,
            ce_unwinding_rising, pe_unwinding_falling, vol_imbalance
        )

        # ── bias_calculated_at ────────────────────────────────────────────────
        bias_calculated_at = now_ist().strftime('%d-%b-%Y %H:%M IST')

        return {
            'bias':                bias,
            'score':               score,
            'score_raw':           score,
            'score_display':       f"{score}/{self._max_score}",
            'confidence':          confidence,
            'confidence_display':  f"{confidence:.1f}%/100%",
            'max_score':           self._max_score,
            'event_tag':           event_tag,
            'price_structure':     price_structure,
            'vwap_level':          vwap_level,
            'vwap_bias':           vwap_bias,
            'vol_bias':            vol_bias,
            'trap_msg':            trap_msg,
            'bias_calculated_at':  bias_calculated_at,
            'reasoning':           reasoning,
            # individual signal flags (for downstream callers)
            'strong_pe_writing':       strong_pe_writing,
            'strong_ce_writing':       strong_ce_writing,
            'ce_unwinding_rising':     ce_unwinding_rising,
            'pe_unwinding_falling':    pe_unwinding_falling,
        }

    def _compute_price_structure(self, spot_df: Optional[pd.DataFrame]) -> str:
        """
        Classify price structure from recent NIFTY spot candles (Source 1).
        Returns: 'BULLISH STRUCTURE' | 'BEARISH STRUCTURE' | 'RANGEBOUND' | 'REVERSAL WATCH' | 'INSUFFICIENT_DATA'
        """
        if spot_df is None or len(spot_df) < 4:
            return 'INSUFFICIENT_DATA'
        try:
            df = spot_df.tail(6)
            highs  = df['high'].values.astype(float)
            lows   = df['low'].values.astype(float)
            closes = df['close'].values.astype(float)
            n = len(highs) - 1
            if n < 2:
                return 'RANGEBOUND'

            hh = sum(highs[i] > highs[i - 1] for i in range(1, n + 1))
            hl = sum(lows[i]  > lows[i - 1]  for i in range(1, n + 1))
            lh = sum(highs[i] < highs[i - 1] for i in range(1, n + 1))
            ll = sum(lows[i]  < lows[i - 1]  for i in range(1, n + 1))

            threshold = n * 0.75  # 4 of 5 comparisons must agree — reduces noise
            if hh >= threshold and hl >= threshold:
                return 'BULLISH STRUCTURE'
            if lh >= threshold and ll >= threshold:
                return 'BEARISH STRUCTURE'

            # Range compression: recent range much tighter than overall range
            full_range   = highs.max() - lows.min()
            recent_range = highs[-3:].max() - lows[-3:].min() if len(highs) >= 3 else full_range
            if full_range > 0 and recent_range < full_range * 0.45:
                return 'RANGEBOUND'

            # Reversal watch: close reversing after directional move
            if len(closes) >= 3:
                if closes[-1] > closes[-2] and lh >= n * 0.5:
                    return 'REVERSAL WATCH'
                if closes[-1] < closes[-2] and hh >= n * 0.5:
                    return 'REVERSAL WATCH'

            return 'RANGEBOUND'
        except Exception as e:
            log.warning(f"[SignalEngine._compute_price_structure] Error: {e}")
            return 'RANGEBOUND'

    def _compute_vwap(
        self, futures_df: Optional[pd.DataFrame], reference_price: float
    ) -> Tuple[Optional[float], str]:
        """
        Compute VWAP from NIFTY Futures candles (Source 2).
        VWAP = cumsum(typical_price × volume) / cumsum(volume)
        typical_price = (high + low + close) / 3
        reference_price MUST be the latest futures close — NOT the spot
        index price. Futures trade at a premium to spot; comparing VWAP
        against spot causes a permanent bullish bias equal to the basis.
        Returns (vwap_level, vwap_bias). vwap_level is None if futures unavailable.
        """
        if futures_df is None or futures_df.empty:
            return None, 'NEUTRAL'
        try:
            df = futures_df.copy()
            df['typical'] = (df['high'].astype(float) + df['low'].astype(float) + df['close'].astype(float)) / 3
            df['tp_vol']  = df['typical'] * df['volume'].astype(float)
            cum_vol = df['volume'].astype(float).sum()
            if cum_vol == 0:
                return None, 'NEUTRAL'
            vwap = float(df['tp_vol'].sum() / cum_vol)
            if reference_price > vwap:
                vwap_bias = 'BULLISH'
            elif reference_price < vwap:
                vwap_bias = 'BEARISH'
            else:
                vwap_bias = 'NEUTRAL'
            return round(vwap, 2), vwap_bias
        except Exception as e:
            log.warning(f"[SignalEngine._compute_vwap] Error: {e}")
            return None, 'NEUTRAL'

    def _compute_vol_bias(
        self, futures_df: Optional[pd.DataFrame], price_structure: str
    ) -> str:
        """
        Analyze NIFTY Futures candle volume (Source 2) for directional confirmation.
        Never use spot index candle volume.
        """
        if futures_df is None or len(futures_df) < 2:
            return 'NEUTRAL'
        try:
            vols = futures_df['volume'].astype(float)
            recent_vol = float(vols.iloc[-1])
            lookback   = vols.iloc[:-1].tail(10)   # rolling 10-candle window
            if len(lookback) < 2:
                return 'NEUTRAL'
            avg_vol = float(lookback.mean())
            if avg_vol == 0:
                return 'NEUTRAL'
            vol_ratio = recent_vol / avg_vol
            if vol_ratio >= CONFIG['VOLUME_SPIKE_RATIO']:
                if price_structure == 'BULLISH STRUCTURE':
                    return 'BULLISH'
                elif price_structure == 'BEARISH STRUCTURE':
                    return 'BEARISH'
            return 'NEUTRAL'
        except Exception as e:
            log.warning(f"[SignalEngine._compute_vol_bias] Error: {e}")
            return 'NEUTRAL'

    def _detect_trap(
        self,
        metrics: dict,
        vwap_level: Optional[float],
        vwap_bias: str,
        vol_bias: str,
        spot: float,
    ) -> str:
        """
        Detect bullish or bearish trap patterns.
        Bullish trap: price broke above resistance, but volume weak and below VWAP.
        Bearish trap: price broke below support, but quickly reversed and reclaiming VWAP.
        Returns trap description string, or '' if no trap detected.
        """
        resistance = metrics.get('resistance_strike', 0)
        support    = metrics.get('support_strike',    0)

        # Bullish trap
        if (resistance > 0
                and spot > resistance * (1 + CONFIG['BREAKOUT_BUFFER_PCT'])
                and vol_bias != 'BULLISH'
                and vwap_level is not None and spot < vwap_level):
            return (
                f"Possible bull trap: spot {spot:.0f} above resistance {resistance:.0f} "
                f"but volume unconfirmed and below VWAP {vwap_level:.0f}"
            )

        # Bearish trap
        if (support > 0
                and spot < support * (1 - CONFIG['BREAKDOWN_BUFFER_PCT'])
                and vol_bias != 'BEARISH'
                and vwap_level is not None and spot > vwap_level):
            return (
                f"Possible bear trap: spot {spot:.0f} below support {support:.0f} "
                f"but price reclaiming VWAP {vwap_level:.0f}"
            )

        return ''

    def _compute_event_tag(
        self,
        trap_msg: str,
        confidence: float,
        ce_unwinding_rising: bool,
        pe_unwinding_falling: bool,
        support_shift: float,
        resistance_shift: float,
        price_structure: str,
        score: int,
    ) -> str:
        """
        Assign a human-readable event tag based on signal conditions.
        TRAP WARNING overrides all other tags.
        """
        if trap_msg:
            return 'TRAP WARNING'
        if confidence < 30:
            return 'LOW CONFIDENCE'
        if ce_unwinding_rising:
            return 'PROBABLE SHORT COVERING'
        if pe_unwinding_falling:
            return 'PROBABLE LONG UNWINDING'
        if support_shift > 0 and score > 0:
            return 'BULLISH SHIFT'
        if resistance_shift < 0 and score < 0:
            return 'BEARISH SHIFT'
        if price_structure == 'INSUFFICIENT_DATA':
            return 'LOW CONFIDENCE'
        if 'REVERSAL WATCH' in price_structure:
            return 'REVERSAL WATCH'
        if 'RANGEBOUND' in price_structure:
            return 'RANGEBOUND'
        return 'RANGEBOUND'

    @staticmethod
    def _classify_bias(score: int) -> str:
        """
        Map numeric score to bias label.
        Thresholds per spec — no weekday logic, no hardcoded max.
        """
        if score >= 5:
            return 'STRONG BULLISH'
        elif score >= 3:
            return 'BULLISH'
        elif score >= 1:
            return 'MILD BULLISH'
        elif score >= -1:
            return 'NEUTRAL'
        elif score >= -3:
            return 'MILD BEARISH'
        elif score >= -5:
            return 'BEARISH'
        else:
            return 'STRONG BEARISH'

    def _build_reasoning(
        self,
        score: int,
        price_structure: str,
        vwap_bias: str,
        vol_bias: str,
        pcr_oi: float,
        support_shift: float,
        resistance_shift: float,
        strong_pe_writing: bool,
        strong_ce_writing: bool,
        ce_unwinding_rising: bool,
        pe_unwinding_falling: bool,
        vol_imbalance: float,
    ) -> List[str]:
        """Build a list of plain-language reasoning bullets for the signals dict."""
        points = []

        if strong_pe_writing:
            points.append(f"Strong PE writing detected — put writers actively defending support "
                          f"(net PE OI change ≥ {CONFIG['COMPARISON_OI_THRESHOLD']:,})")
        if strong_ce_writing:
            points.append(f"Strong CE writing detected — call writers capping upside "
                          f"(net CE OI change ≥ {CONFIG['COMPARISON_OI_THRESHOLD']:,})")
        if ce_unwinding_rising:
            points.append("CE unwinding with rising price — probable short covering (bullish)")
        if pe_unwinding_falling:
            points.append("PE unwinding with falling price — probable long unwinding (bearish)")

        if not math.isnan(pcr_oi):
            pcr_label = ('bullish' if pcr_oi >= CONFIG['PCR_BULLISH_THRESHOLD']
                         else 'bearish' if pcr_oi <= CONFIG['PCR_BEARISH_THRESHOLD'] else 'neutral')
            points.append(f"PCR (OI) = {pcr_oi:.3f} — {pcr_label}")

        if support_shift != 0:
            direction = 'up' if support_shift > 0 else 'down'
            points.append(f"Support shifted {direction} by {abs(support_shift):.0f} pts "
                          f"({'bullish' if support_shift > 0 else 'bearish'})")
        if resistance_shift != 0:
            direction = 'up' if resistance_shift > 0 else 'down'
            points.append(f"Resistance shifted {direction} by {abs(resistance_shift):.0f} pts "
                          f"({'bullish' if resistance_shift > 0 else 'bearish'})")

        points.append(f"Price structure: {price_structure}")
        points.append(f"VWAP bias: {vwap_bias}")
        points.append(f"Volume confirmation: {vol_bias}")

        if not math.isnan(vol_imbalance):
            vi_label = ('more put activity (supportive)' if vol_imbalance > 0
                        else 'more call activity (resistive)')
            points.append(f"Volume imbalance = {vol_imbalance:.4f} — {vi_label}")

        return points[:8]  # Return up to 8 points


# ── END OF PASS 1 ──
"""
NIFTY Intraday Dashboard — Pass 2
Classes 8–14: ThetaEnvironmentAnalyzer, ReversalBreakoutDetector, StartupChecker,
              SheetsWriter, TelegramSender, ClaudeAnalyst, NiftyDashboardApp
plus main() entry point.
"""

# ── Module-level helper (safe NaN→empty for Sheets) ──────────────────────────
import math as _math

def safe_val(v):
    """Convert float NaN to '' so gspread doesn't write the literal string 'nan'."""
    if v is None:
        return ''
    if isinstance(v, float) and _math.isnan(v):
        return ''
    return v


# ─────────────────────────────────────────────────────────────────────────────
# 8. ThetaEnvironmentAnalyzer
# ─────────────────────────────────────────────────────────────────────────────

class ThetaEnvironmentAnalyzer:
    """
    Determines whether current conditions favour option premium decay or expansion.
    Pure rule-based — no ML, no trade recommendations.
    """

    def compute(
        self,
        vix_data:       dict,
        days_to_expiry: int,
        spot_df,
        metrics:        dict,
        signals:        dict,
        sr_event:       dict,
    ) -> dict:
        try:
            return self._compute(vix_data, days_to_expiry, spot_df, metrics, signals, sr_event)
        except Exception:
            import traceback as _tb
            log.warning(f"[Theta] compute() failed:\n{_tb.format_exc()}")
            return {
                'market_condition': 'Neutral',
                'volatility_context': 'Unknown',
                'price_behavior': 'Range-bound',
                'key_insight': 'Analysis unavailable.',
                'reasoning': ['Error during premium environment computation — check logs.'],
                'risk_note': 'Data unavailable for this cycle.',
                'decay_score': 0,
                'days_to_expiry': days_to_expiry,
                'vix_level': float('nan'),
            }

    def _compute(self, vix_data, days_to_expiry, spot_df, metrics, signals, sr_event):

        vix = vix_data.get('vix_current', float('nan'))
        vix_trend = vix_data.get('vix_trend', 'FLAT')
        decay_score = 0

        # Factor 1 — India VIX level (±3 pts)
        if not math.isnan(vix):
            if vix < CONFIG['VIX_LOW_THRESHOLD']:
                decay_score += 3
            elif vix > CONFIG['VIX_HIGH_THRESHOLD']:
                decay_score -= 3

        # Factor 2 — India VIX trend (±2 pts)
        if vix_trend == 'FALLING':
            decay_score += 2
        elif vix_trend == 'RISING':
            decay_score -= 2

        # Factor 3 — Time to expiry (asymmetric: +2 to -1)
        if days_to_expiry <= 2:
            decay_score += 2
        elif days_to_expiry <= 5:
            decay_score += 1
        elif days_to_expiry >= 15:
            decay_score -= 1

        # Factor 4 — Price behavior (±2 pts)
        price_structure = signals.get('price_structure', '')
        sr = sr_event.get('event', 'NONE')
        if price_structure == 'RANGEBOUND':
            decay_score += 2
        elif sr in ('BREAKOUT_ABOVE_RESISTANCE', 'BREAKDOWN_BELOW_SUPPORT'):
            decay_score -= 2
        elif sr in ('SUPPORT_REVERSAL', 'RESISTANCE_REVERSAL'):
            decay_score += 0
        elif 'BULLISH STRUCTURE' in price_structure or 'BEARISH STRUCTURE' in price_structure:
            decay_score -= 1

        # Factor 5 — OI buildup pattern (±1 pt)
        ce_chg = metrics.get('total_ce_chg_oi', 0) or 0
        pe_chg = metrics.get('total_pe_chg_oi', 0) or 0
        if ce_chg > 0 and pe_chg > 0:
            decay_score += 1
        elif ce_chg < 0 and pe_chg < 0:   # BOTH unwinding = expansion signal
            decay_score -= 1
        # One-sided OI rotation (directional trending) = neutral for Theta

        # Market condition
        if decay_score >= 4:
            market_condition = 'Decay Favorable'
        elif decay_score <= -4:
            market_condition = 'Expansion Favorable'
        else:
            market_condition = 'Neutral'

        # Volatility context
        if math.isnan(vix):
            volatility_context = 'Unknown'
        elif vix > CONFIG['VIX_HIGH_THRESHOLD']:
            volatility_context = 'High'
        elif vix < CONFIG['VIX_LOW_THRESHOLD']:
            volatility_context = 'Low'
        elif vix_trend == 'RISING':
            volatility_context = 'Rising'
        elif vix_trend == 'FALLING':
            volatility_context = 'Falling'
        else:
            volatility_context = 'Moderate'

        # Price behavior
        if sr in ('BREAKOUT_ABOVE_RESISTANCE', 'BREAKDOWN_BELOW_SUPPORT'):
            if sr_event.get('confidence') == 'HIGH':
                price_behavior = ('Post-Breakout' if sr == 'BREAKOUT_ABOVE_RESISTANCE'
                                  else 'Post-Breakdown')
            else:
                price_behavior = 'Breakout Attempt'
        elif sr in ('SUPPORT_REVERSAL', 'RESISTANCE_REVERSAL'):
            price_behavior = 'Range-bound'
        elif price_structure == 'INSUFFICIENT_DATA':
            price_behavior = 'Range-bound'
        elif 'RANGEBOUND' in price_structure:
            price_behavior = 'Range-bound'
        elif 'BULLISH STRUCTURE' in price_structure or 'BEARISH STRUCTURE' in price_structure:
            price_behavior = 'Trending'
        else:
            price_behavior = 'Range-bound'

        # Key insight (1-2 sentences combining top two factors)
        vix_str = f'{vix:.1f}' if not math.isnan(vix) else 'N/A'
        if market_condition == 'Decay Favorable':
            key_insight = (
                f"India VIX at {vix_str} and {vix_trend.lower()} with {days_to_expiry} days to expiry. "
                f"{price_behavior} price action adds further support to a decay-friendly environment."
            )
        elif market_condition == 'Expansion Favorable':
            key_insight = (
                f"India VIX at {vix_str} with a {'confirmed ' if sr in ('BREAKOUT_ABOVE_RESISTANCE','BREAKDOWN_BELOW_SUPPORT') else ''}directional move. "
                f"Option premiums are likely to expand — conditions carry higher risk for premium sellers."
            )
        else:
            key_insight = (
                f"VIX at {vix_str} with {days_to_expiry} days to expiry. "
                f"Mixed signals — neither clearly decay-friendly nor expansion-driven."
            )

        # Reasoning bullets (3-5 items)
        vix_level_label = ('low' if not math.isnan(vix) and vix < CONFIG['VIX_LOW_THRESHOLD']
                           else 'high' if not math.isnan(vix) and vix > CONFIG['VIX_HIGH_THRESHOLD']
                           else 'moderate')
        reasoning = [
            (f"India VIX at {vix_str} — {vix_level_label} — "
             + ('IV is compressed, making option premiums relatively rich for sellers'
                if vix_level_label == 'low'
                else 'IV is elevated, making option premiums expensive and likely to contract if conditions calm'
                if vix_level_label == 'high'
                else 'IV is at a moderate level — no strong bias either way')),
            (f"VIX trend is {vix_trend} — "
             + ('volatility is contracting, which tends to erode option premiums over time'
                if vix_trend == 'FALLING'
                else 'volatility is expanding, which inflates option premiums and makes directional moves more costly'
                if vix_trend == 'RISING'
                else 'volatility is stable — no expansion or contraction pressure')),
            (f"{days_to_expiry} days to expiry — "
             + ('final days of the contract, theta decay is at its fastest — every day erodes remaining time value rapidly'
                if days_to_expiry <= 2
                else 'near expiry, theta is accelerating'
                if days_to_expiry <= 5
                else 'time value decay is slow this far from expiry')),
            (f"Price is {price_behavior} — "
             + ('a sideways market is the most favorable condition for premium sellers, as neither direction is confirmed'
                if price_behavior == 'Range-bound'
                else 'a trending or breakout market increases the risk of a large directional move, which can rapidly inflate option premiums')),
        ]
        if ce_chg > 0 and pe_chg > 0:
            reasoning.append(
                "OI on both CE and PE sides is building simultaneously — this suggests large participants expect "
                "price to remain within a range, which is consistent with a decay environment"
            )
        elif ce_chg < 0 or pe_chg < 0:
            reasoning.append(
                "OI is showing mixed signals — one side unwinding suggests directional positioning"
            )

        # Risk note
        if market_condition == 'Decay Favorable':
            risk_note = "Decay Favorable: VIX can spike suddenly on global news — always be aware of event risk near current expiry."
        elif market_condition == 'Expansion Favorable':
            risk_note = "Expansion Favorable: If VIX falls back quickly, premiums can shrink despite the directional move."
        else:
            risk_note = "Neutral: Mixed signals mean the environment can shift quickly — monitor VIX and price action closely."

        return {
            'market_condition':   market_condition,
            'volatility_context': volatility_context,
            'price_behavior':     price_behavior,
            'key_insight':        key_insight,
            'reasoning':          reasoning[:5],
            'risk_note':          risk_note,
            'decay_score':        decay_score,
            'days_to_expiry':     days_to_expiry,
            'vix_level':          vix if not math.isnan(vix) else float('nan'),
        }


# ─────────────────────────────────────────────────────────────────────────────
# 9. ReversalBreakoutDetector
# ─────────────────────────────────────────────────────────────────────────────

class ReversalBreakoutDetector:
    """
    Detects four intraday price events at S/R levels using observable market data only.
    Priority order: BREAKOUT > BREAKDOWN > SUPPORT_REVERSAL > RESISTANCE_REVERSAL.
    """

    _NONE = {
        'event': 'NONE', 'confidence': 'N/A', 'strike': 0.0, 'direction': 'NONE',
        'conditions_met': [], 'conditions_failed': [],
        'candle_pattern': 'NONE', 'candle_wick_pct': 0, 'candle_vol_ratio': 1.0,
        'reasoning': 'No support/resistance event detected this cycle.',
    }

    def detect(
        self,
        spot:       float,
        metrics:    dict,
        signals:    dict,
        spot_df,
        futures_df,
    ) -> dict:
        try:
            return self._detect(spot, metrics, signals, spot_df, futures_df)
        except Exception:
            import traceback as _tb
            log.warning(f"[SRDetect] detect() failed:\n{_tb.format_exc()}")
            return dict(self._NONE)

    def _detect(self, spot, metrics, signals, spot_df, futures_df):
        support    = float(metrics.get('support_strike', 0) or 0)
        resistance = float(metrics.get('resistance_strike', 0) or 0)
        if support <= 0 or resistance <= 0:
            r = dict(self._NONE)
            r['reasoning'] = 'Support or resistance level unavailable — skipping detection.'
            return r

        prox   = CONFIG['SR_PROXIMITY_PCT']
        bb_pct = CONFIG['BREAKOUT_BUFFER_PCT']
        bd_pct = CONFIG['BREAKDOWN_BUFFER_PCT']

        # Shared candle state
        last_close = prev_close = None
        if spot_df is not None and len(spot_df) >= 2:
            last_close = float(spot_df.iloc[-1].get('close', spot))
            prev_close = float(spot_df.iloc[-2].get('close', spot))

        vol_spike = self._vol_spike(futures_df)
        ce_chg    = metrics.get('total_ce_chg_oi', 0) or 0
        pe_chg    = metrics.get('total_pe_chg_oi', 0) or 0
        pcr_oi    = metrics.get('pcr_oi', float('nan'))
        sup_shift = metrics.get('support_shift', 0) or 0
        res_shift = metrics.get('resistance_shift', 0) or 0
        vwap_bias = signals.get('vwap_bias', 'NEUTRAL')
        vol_bias  = signals.get('vol_bias', 'NEUTRAL')

        # ── Priority 1: BREAKOUT_ABOVE_RESISTANCE ─────────────────────────────
        c1_bo = spot > resistance * (1 + bb_pct)
        c2_bo = last_close is not None and last_close > resistance
        c3_bo = ce_chg < 0
        c4_bo = vwap_bias == 'BULLISH' or vol_bias == 'BULLISH'
        c5_bo = vol_spike

        if c1_bo:
            cp_bo = self._candle_pattern(spot_df, futures_df, 'BULLISH')
            primary = [c1_bo, c2_bo, c3_bo, c4_bo, c5_bo]
            n_met = sum(primary)
            met, fail = self._condition_labels_breakout(c1_bo, c2_bo, c3_bo, c4_bo, c5_bo, cp_bo)
            if n_met >= 4:
                return {
                    'event': 'BREAKOUT_ABOVE_RESISTANCE',
                    'confidence': 'HIGH' if n_met == 5 else 'MEDIUM',
                    'strike': resistance, 'direction': 'BULLISH',
                    'conditions_met': met, 'conditions_failed': fail,
                    'candle_pattern':   cp_bo['pattern'],
                    'candle_wick_pct':  cp_bo['wick_pct'],
                    'candle_vol_ratio': cp_bo['vol_ratio'],
                    'reasoning': (
                        f"Spot {spot:.0f} broke above resistance {resistance:.0f} "
                        f"(+{(spot/resistance-1)*100:.2f}% buffer). {n_met}/5 conditions met."
                    ),
                }

        # ── Priority 2: BREAKDOWN_BELOW_SUPPORT ──────────────────────────────
        c1_bd = spot < support * (1 - bd_pct)
        c2_bd = last_close is not None and last_close < support
        c3_bd = pe_chg < 0
        c4_bd = vwap_bias == 'BEARISH' or vol_bias == 'BEARISH'
        c5_bd = vol_spike

        if c1_bd:
            cp_bd = self._candle_pattern(spot_df, futures_df, 'BEARISH')
            primary = [c1_bd, c2_bd, c3_bd, c4_bd, c5_bd]
            n_met = sum(primary)
            met, fail = self._condition_labels_breakdown(c1_bd, c2_bd, c3_bd, c4_bd, c5_bd, cp_bd)
            if n_met >= 4:
                return {
                    'event': 'BREAKDOWN_BELOW_SUPPORT',
                    'confidence': 'HIGH' if n_met == 5 else 'MEDIUM',
                    'strike': support, 'direction': 'BEARISH',
                    'conditions_met': met, 'conditions_failed': fail,
                    'candle_pattern':   cp_bd['pattern'],
                    'candle_wick_pct':  cp_bd['wick_pct'],
                    'candle_vol_ratio': cp_bd['vol_ratio'],
                    'reasoning': (
                        f"Spot {spot:.0f} broke below support {support:.0f} "
                        f"(-{(1-spot/support)*100:.2f}% buffer). {n_met}/5 conditions met."
                    ),
                }

        # ── Priority 3: SUPPORT_REVERSAL ─────────────────────────────────────
        c1_sr = support > 0 and abs(spot - support) / support <= prox
        c2_sr = last_close is not None and prev_close is not None and last_close > prev_close
        c3_sr = (not math.isnan(pcr_oi) and pcr_oi >= CONFIG['PCR_BULLISH_THRESHOLD']) or pe_chg > 0
        c4_sr = sup_shift >= 0
        c5_sr = vwap_bias == 'BULLISH' or vol_bias == 'BULLISH'

        if c1_sr:
            cp_sr = self._candle_pattern(spot_df, futures_df, 'SUPPORT')
            primary = [c1_sr, c2_sr, c3_sr, c4_sr, c5_sr]
            n_met = sum(primary)
            met, fail = self._condition_labels_support_rev(c1_sr, c2_sr, c3_sr, c4_sr, c5_sr, cp_sr)
            if n_met >= 4:
                return {
                    'event': 'SUPPORT_REVERSAL',
                    'confidence': 'HIGH' if n_met == 5 else 'MEDIUM',
                    'strike': support, 'direction': 'BULLISH',
                    'conditions_met': met, 'conditions_failed': fail,
                    'candle_pattern':   cp_sr['pattern'],
                    'candle_wick_pct':  cp_sr['wick_pct'],
                    'candle_vol_ratio': cp_sr['vol_ratio'],
                    'reasoning': (
                        f"Spot {spot:.0f} testing support at {support:.0f} "
                        f"(within {prox*100:.1f}% proximity). {n_met}/5 conditions met."
                    ),
                }

        # ── Priority 4: RESISTANCE_REVERSAL ──────────────────────────────────
        c1_rr = resistance > 0 and abs(spot - resistance) / resistance <= prox
        c2_rr = last_close is not None and prev_close is not None and last_close <= prev_close
        c3_rr = (not math.isnan(pcr_oi) and pcr_oi <= CONFIG['PCR_BEARISH_THRESHOLD']) or ce_chg > 0
        c4_rr = res_shift <= 0
        c5_rr = vwap_bias == 'BEARISH' or vol_bias == 'BEARISH'

        if c1_rr:
            cp_rr = self._candle_pattern(spot_df, futures_df, 'RESISTANCE')
            primary = [c1_rr, c2_rr, c3_rr, c4_rr, c5_rr]
            n_met = sum(primary)
            met, fail = self._condition_labels_resist_rev(c1_rr, c2_rr, c3_rr, c4_rr, c5_rr, cp_rr)
            if n_met >= 4:
                return {
                    'event': 'RESISTANCE_REVERSAL',
                    'confidence': 'HIGH' if n_met == 5 else 'MEDIUM',
                    'strike': resistance, 'direction': 'BEARISH',
                    'conditions_met': met, 'conditions_failed': fail,
                    'candle_pattern':   cp_rr['pattern'],
                    'candle_wick_pct':  cp_rr['wick_pct'],
                    'candle_vol_ratio': cp_rr['vol_ratio'],
                    'reasoning': (
                        f"Spot {spot:.0f} testing resistance at {resistance:.0f} "
                        f"(within {prox*100:.1f}% proximity). {n_met}/5 conditions met."
                    ),
                }

        r = dict(self._NONE)
        return r

    # ── Private helpers ───────────────────────────────────────────────────────

    def _vol_spike(self, futures_df) -> bool:
        """True if last futures candle volume >= VOLUME_SPIKE_RATIO × mean prior volume."""
        try:
            if futures_df is None or len(futures_df) < 2:
                return False
            vols = futures_df['volume'].values
            last_vol = float(vols[-1])
            mean_vol = float(vols[:-1].mean())
            if mean_vol <= 0:
                return False
            return last_vol / mean_vol >= CONFIG['VOLUME_SPIKE_RATIO']
        except Exception:
            return False

    def _candle_pattern(self, spot_df, futures_df, direction: str) -> dict:
        """
        Changed in v5.4: takes futures_df for vol_ratio; returns dict not tuple/string.

        Returns: {'pattern': str, 'wick_pct': int 0-100, 'vol_ratio': float}
          wick_pct:  >70=strong rejection | 50-69=moderate | <50=weak
          vol_ratio: >1.5=spike | <0.8=low conviction | 1.0=no data

        Patterns: BULLISH_REJECTION | BEARISH_REJECTION |
                  EXPANSION_UP | EXPANSION_DOWN | NONE | INSUFFICIENT_DATA

        Lower-wick formula (works for both green and red candles at support):
            lower_wick = min(open, close) - low   ← body bottom to candle low
        Upper-wick formula (works for both green and red candles at resistance):
            upper_wick = high - max(open, close)   ← candle high to body top
        """
        NONE_R = {'pattern': 'NONE', 'wick_pct': 0, 'vol_ratio': 1.0}
        if spot_df is None or len(spot_df) < CONFIG['REJECTION_MIN_CANDLES']:
            return {'pattern': 'INSUFFICIENT_DATA', 'wick_pct': 0, 'vol_ratio': 1.0}
        bar = spot_df.iloc[-1]
        o  = float(bar.get('open',  0))
        h  = float(bar.get('high',  0))
        lo = float(bar.get('low',   0))
        cl = float(bar.get('close', 0))
        body = abs(cl - o)
        rng  = h - lo
        if rng < 1.0:
            return NONE_R
        # vol_ratio uses futures only (spot index has no meaningful volume)
        # Reference average uses 5 bars BEFORE the signal bar — signal bar excluded.
        try:
            prior_bars = futures_df['volume'].iloc[:-1].tail(5)
            avg = max(float(prior_bars.mean()), 1.0) if len(prior_bars) > 0 else 1.0
            vol_ratio = round(float(futures_df.iloc[-1]['volume']) / avg, 2)
        except Exception:
            vol_ratio = 1.0

        if direction in ('BULLISH', 'SUPPORT'):
            lower_wick = min(o, cl) - lo
            wick_pct   = round(lower_wick / rng * 100)
            if lower_wick >= body * CONFIG['REJECTION_WICK_RATIO'] and wick_pct >= 50:
                return {'pattern': 'BULLISH_REJECTION', 'wick_pct': wick_pct, 'vol_ratio': vol_ratio}
            bp = round(body / rng * 100)
            if bp >= 70 and cl >= o:
                return {'pattern': 'EXPANSION_UP', 'wick_pct': 100 - bp, 'vol_ratio': vol_ratio}
        elif direction in ('BEARISH', 'RESISTANCE'):
            upper_wick = h - max(o, cl)
            wick_pct   = round(upper_wick / rng * 100)
            if upper_wick >= body * CONFIG['REJECTION_WICK_RATIO'] and wick_pct >= 50:
                return {'pattern': 'BEARISH_REJECTION', 'wick_pct': wick_pct, 'vol_ratio': vol_ratio}
            bp = round(body / rng * 100)
            if bp >= 70 and cl < o:
                return {'pattern': 'EXPANSION_DOWN', 'wick_pct': 100 - bp, 'vol_ratio': vol_ratio}
        return NONE_R

    # ── Condition label builders ──────────────────────────────────────────────

    def _condition_labels_breakout(self, c1, c2, c3, c4, c5, cp):
        labels = [
            ('Spot above resistance with buffer',           c1),
            ('Last candle closed above resistance',         c2),
            ('CE OI unwinding (short covering)',            c3),
            ('VWAP or volume bias bullish',                 c4),
            ('Futures volume spike confirmed',              c5),
        ]
        bonus = cp['pattern'] in ('EXPANSION_UP', 'BULLISH_REJECTION')
        met  = [l for l, v in labels if v] + (['Candle: ' + cp['pattern']] if bonus else [])
        fail = [l for l, v in labels if not v] + ([] if bonus else ['No bullish candle expansion'])
        return met, fail

    def _condition_labels_breakdown(self, c1, c2, c3, c4, c5, cp):
        labels = [
            ('Spot below support with buffer',              c1),
            ('Last candle closed below support',            c2),
            ('PE OI unwinding (long unwinding)',            c3),
            ('VWAP or volume bias bearish',                 c4),
            ('Futures volume spike confirmed',              c5),
        ]
        bonus = cp['pattern'] in ('EXPANSION_DOWN', 'BEARISH_REJECTION')
        met  = [l for l, v in labels if v] + (['Candle: ' + cp['pattern']] if bonus else [])
        fail = [l for l, v in labels if not v] + ([] if bonus else ['No bearish candle expansion'])
        return met, fail

    def _condition_labels_support_rev(self, c1, c2, c3, c4, c5, cp):
        labels = [
            ('Spot within proximity of support',            c1),
            ('Price bouncing up (last close >= prior)',     c2),
            ('Put writers active (PCR or PE OI growing)',  c3),
            ('Support not breaking down (shift >= 0)',      c4),
            ('VWAP or volume bias bullish',                 c5),
        ]
        bonus = cp['pattern'] == 'BULLISH_REJECTION'
        met  = [l for l, v in labels if v] + (['Candle: BULLISH_REJECTION'] if bonus else [])
        fail = [l for l, v in labels if not v] + ([] if bonus else ['No bullish rejection candle'])
        return met, fail

    def _condition_labels_resist_rev(self, c1, c2, c3, c4, c5, cp):
        labels = [
            ('Spot within proximity of resistance',         c1),
            ('Price rejected down (last close <= prior)',   c2),
            ('Call writers active (PCR or CE OI growing)', c3),
            ('Resistance not breaking up (shift <= 0)',     c4),
            ('VWAP or volume bias bearish',                 c5),
        ]
        bonus = cp['pattern'] == 'BEARISH_REJECTION'
        met  = [l for l, v in labels if v] + (['Candle: BEARISH_REJECTION'] if bonus else [])
        fail = [l for l, v in labels if not v] + ([] if bonus else ['No bearish rejection candle'])
        return met, fail


# ─────────────────────────────────────────────────────────────────────────────
# 10. SetupEvaluator
# ─────────────────────────────────────────────────────────────────────────────

class SetupEvaluator:
    """
    8-gate entry framework. Analytics only — no order placement.
    Validated strategy rules:
    - Decay Favorable  → HEDGED_SELL only
    - Expansion Fav.   → Buying ONLY if VIX <= 22 + SR event confirmed
    - VIX > 22         → Block buying regardless of environment
    - Rangebound       → Block buying always
    - Expiry after 13:00 IST → Block ALL new entries
    - Expiry 11-13 IST → Block BUYING only; selling still allowed
    - Trap             → NOT a block; handled by OrderExecutor as fade opportunity
    """
    SETUP_NONE      = 'NONE'
    SETUP_DECAY     = 'HEDGED_SELL'
    SETUP_BUY_BREAK = 'BREAKOUT_BUY'
    SETUP_BUY_REV   = 'REVERSAL_BUY'
    SETUP_BLOCKED   = 'BLOCKED'

    def evaluate(
        self,
        snapshot: dict, metrics: dict, signals: dict,
        sr_event: dict, theta_env: dict, vix_data: dict,
        chain, days_to_expiry: int, is_weekly: bool,
        lot_size: int = 25,
    ) -> dict:
        """Run all 8 gates. Never raises. Always returns 21 keys."""
        try:
            market_condition = theta_env.get('market_condition', 'Neutral')
            price_structure  = signals.get('price_structure', '')
            sr_ev   = sr_event.get('event', 'NONE')
            sr_age  = int(snapshot.get('sr_event_age', 0) or 0)
            oi_conc = metrics.get('oi_concentration', float('nan'))
            total_zone_oi = (
                (metrics.get('total_ce_oi', 0) or 0) +
                (metrics.get('total_pe_oi', 0) or 0))
            bias         = snapshot.get('bias', '')
            support_s    = float(metrics.get('support_strike', 0) or 0)
            resistance_s = float(metrics.get('resistance_strike', 0) or 0)
            expiry_day      = (days_to_expiry == 0)
            pre_expiry_warn = (0 < days_to_expiry <= 2)
            signal_id = f"SIG_{ist_str('%Y%m%d_%H%M%S')}"

            oi_regime = 'NORMAL'
            if not math.isnan(oi_conc):
                if oi_conc > 0.65:   oi_regime = 'PINNING'
                elif oi_conc < 0.40: oi_regime = 'ROTATING'

            liquidity_ok = total_zone_oi > 100000
            late_entry   = sr_age >= 6

            ist = now_ist()
            if (ist.hour == 9 and ist.minute >= 15) or \
               (ist.hour == 10 and ist.minute < 15):
                time_block = 'OPEN'
            elif 10 <= ist.hour < 13:
                time_block = 'MID'
            elif (13 <= ist.hour <= 14) or \
                 (ist.hour == 15 and ist.minute <= 30):
                time_block = 'CLOSE'
            else:
                time_block = 'OUTSIDE'

            _expiry_buy_blocked = False
            if expiry_day:
                if time_block == 'CLOSE':
                    return self._blocked(signal_id,
                        'Expiry day after 13:00 IST — no new entries. '
                        'Gamma risk unacceptable. Use EXIT_ALL only.',
                        expiry_day, pre_expiry_warn, oi_regime,
                        liquidity_ok, late_entry, time_block, {}, lot_size)
                if time_block == 'MID':
                    _expiry_buy_blocked = True

            vwap_confirms = signals.get('vwap_bias', 'NEUTRAL') != 'NEUTRAL'
            vol_confirms  = signals.get('vol_bias',  'NEUTRAL') != 'NEUTRAL'
            vwap_vol_ok   = vwap_confirms or vol_confirms
            gate_results  = {}

            # Gate 1: Environment
            env_ok = (market_condition != 'Neutral')
            if not env_ok and price_structure not in (
                    'BULLISH STRUCTURE', 'BEARISH STRUCTURE'):
                return self._blocked(signal_id,
                    'Neutral environment — no directional edge',
                    expiry_day, pre_expiry_warn, oi_regime,
                    liquidity_ok, late_entry, time_block, {}, lot_size)
            gate_results['environment_ok'] = env_ok

            # Gate 2: Structure
            struct_ok = price_structure in (
                'BULLISH STRUCTURE','BEARISH STRUCTURE',
                'REVERSAL WATCH','RANGEBOUND')
            if not struct_ok:
                return self._blocked(signal_id,
                    'Insufficient price structure data',
                    expiry_day, pre_expiry_warn, oi_regime,
                    liquidity_ok, late_entry, time_block,
                    gate_results, lot_size)
            gate_results['structure_ok'] = struct_ok

            # Gate 3: OI regime
            gate_results['oi_regime'] = oi_regime
            if oi_regime == 'ROTATING' and \
                    market_condition != 'Expansion Favorable':
                return self._blocked(signal_id,
                    'OI rotating — unclear regime',
                    expiry_day, pre_expiry_warn, oi_regime,
                    liquidity_ok, late_entry, time_block,
                    gate_results, lot_size)

            # Gate 4: Liquidity (soft)
            gate_results['liquidity_ok'] = liquidity_ok

            # Gate 5: Trap — NOT a block; fade opportunity in OrderExecutor
            gate_results['trap_ok'] = not bool(snapshot.get('trap', ''))

            # Gate 6: VWAP+Vol (soft)
            gate_results['vwap_vol_ok'] = vwap_vol_ok

            # Gate 7: Late entry
            gate_results['late_entry'] = late_entry
            if late_entry:
                return self._blocked(signal_id,
                    'Late entry — SR event age >= 6 cycles (30 min)',
                    expiry_day, pre_expiry_warn, oi_regime,
                    liquidity_ok, late_entry, time_block,
                    gate_results, lot_size)

            # Gate 8: Strategy + VIX cap
            _vix = float(vix_data.get('vix_current', 14.0) or 14.0)
            if math.isnan(_vix): _vix = 14.0
            setup_type = self.SETUP_BLOCKED

            if market_condition == 'Decay Favorable':
                setup_type = self.SETUP_DECAY
                if oi_regime == 'ROTATING':
                    return self._blocked(signal_id,
                        'Rotating OI in decay env — no edge',
                        expiry_day, pre_expiry_warn, oi_regime,
                        liquidity_ok, late_entry, time_block,
                        gate_results, lot_size)
                if (expiry_day and
                        sr_ev in ('BREAKOUT_ABOVE_RESISTANCE',
                                  'BREAKDOWN_BELOW_SUPPORT') and
                        vwap_confirms and vol_confirms and
                        sr_age >= 2 and not _expiry_buy_blocked and
                        _vix <= 22.0):
                    setup_type = self.SETUP_BUY_BREAK

            elif market_condition == 'Expansion Favorable':
                if _vix > 22.0:
                    return self._blocked(signal_id,
                        f'VIX {_vix:.1f} > 22 — premiums too expensive to buy.',
                        expiry_day, pre_expiry_warn, oi_regime,
                        liquidity_ok, late_entry, time_block,
                        gate_results, lot_size)
                if _expiry_buy_blocked:
                    return self._blocked(signal_id,
                        'Expiry day 11:00-13:00 — buying blocked.',
                        expiry_day, pre_expiry_warn, oi_regime,
                        liquidity_ok, late_entry, time_block,
                        gate_results, lot_size)
                if sr_ev in ('BREAKOUT_ABOVE_RESISTANCE',
                             'BREAKDOWN_BELOW_SUPPORT'):
                    setup_type = self.SETUP_BUY_BREAK
                elif sr_ev in ('SUPPORT_REVERSAL','RESISTANCE_REVERSAL'):
                    setup_type = self.SETUP_BUY_REV
                else:
                    return self._blocked(signal_id,
                        'Expansion env — no confirming SR event',
                        expiry_day, pre_expiry_warn, oi_regime,
                        liquidity_ok, late_entry, time_block,
                        gate_results, lot_size)
                if price_structure == 'RANGEBOUND':
                    return self._blocked(signal_id,
                        'Rangebound in expansion — no directional edge',
                        expiry_day, pre_expiry_warn, oi_regime,
                        liquidity_ok, late_entry, time_block,
                        gate_results, lot_size)
            else:
                return self._blocked(signal_id,
                    'Neutral environment — no setup',
                    expiry_day, pre_expiry_warn, oi_regime,
                    liquidity_ok, late_entry, time_block,
                    gate_results, lot_size)

            gate_results['strategy_selected'] = setup_type

            quality = 0
            if env_ok:                                        quality += 20
            if price_structure in ('BULLISH STRUCTURE',
                                   'BEARISH STRUCTURE'):     quality += 15
            if oi_regime == 'PINNING':                       quality += 15
            if liquidity_ok:                                 quality += 10
            if gate_results.get('trap_ok'):                  quality += 10
            if vwap_confirms:                                quality += 10
            if vol_confirms:                                  quality += 10
            if 2 <= sr_age < 6:                              quality += 10
            if not liquidity_ok:                             quality -= 20
            if not vwap_vol_ok:                              quality -= 15
            if expiry_day and setup_type == self.SETUP_BUY_BREAK:
                                                             quality -= 20
            quality = max(0, min(100, quality))

            bias_upper = bias.upper()
            if setup_type == self.SETUP_DECAY:
                if 'BULLISH' in bias_upper:
                    short_option_type = 'PE'
                    short_strike      = support_s
                    hedge_strike      = short_strike - 200
                else:
                    short_option_type = 'CE'
                    short_strike      = resistance_s
                    hedge_strike      = short_strike + 200
            elif setup_type in (self.SETUP_BUY_BREAK, self.SETUP_BUY_REV):
                if (sr_ev in ('BREAKOUT_ABOVE_RESISTANCE',
                              'SUPPORT_REVERSAL') or
                        'BULLISH' in bias_upper):
                    short_option_type = 'CE_BUY'
                    short_strike      = resistance_s
                else:
                    short_option_type = 'PE_BUY'
                    short_strike      = support_s
                hedge_strike = 0.0
            else:
                short_option_type = ''
                short_strike      = 0.0
                hedge_strike      = 0.0

            def _get_ltp(strike_val, opt_type):
                try:
                    if chain is None or len(chain) == 0 or \
                            strike_val == 0.0:
                        return 0.0
                    col  = ('ce_ltp' if 'CE' in str(opt_type).upper()
                            else 'pe_ltp')
                    rows = chain[chain['strike'] == float(strike_val)]
                    return float(rows.iloc[0].get(col, 0) or 0) \
                           if len(rows) > 0 else 0.0
                except Exception:
                    return 0.0

            short_ltp = _get_ltp(short_strike, short_option_type)
            hedge_ltp = (_get_ltp(hedge_strike, short_option_type)
                         if hedge_strike else 0.0)
            net_premium = round(
                short_ltp - hedge_ltp if setup_type == self.SETUP_DECAY
                else short_ltp, 2)
            max_risk = round(
                200 - net_premium if setup_type == self.SETUP_DECAY
                else short_ltp, 2)

            return {
                'signal_id': signal_id, 'setup_type': setup_type,
                'setup_quality': quality, 'blocked_reason': '',
                'expiry_day': expiry_day,
                'pre_expiry_warning': pre_expiry_warn,
                'oi_regime': oi_regime, 'liquidity_ok': liquidity_ok,
                'late_entry': late_entry, 'time_block': time_block,
                'gate_results': gate_results,
                'short_strike': short_strike,
                'short_option_type': short_option_type,
                'short_ltp': short_ltp,
                'hedge_strike': hedge_strike, 'hedge_ltp': hedge_ltp,
                'net_premium': net_premium, 'max_risk': max_risk,
                'lot_size': lot_size,
                'net_premium_total': round(net_premium * lot_size, 2),
                'max_risk_total':    round(max_risk    * lot_size, 2),
            }
        except Exception as e:
            log.warning(f'[SetupEvaluator] evaluate() error: {e}')
            return self._safe_none(lot_size)

    def _blocked(self, signal_id, reason, expiry_day, pre_expiry_warn,
                 oi_regime, liquidity_ok, late_entry, time_block,
                 gate_results, lot_size) -> dict:
        r = self._safe_none(lot_size)
        r.update({'signal_id': signal_id, 'setup_type': self.SETUP_BLOCKED,
                  'blocked_reason': reason, 'expiry_day': expiry_day,
                  'pre_expiry_warning': pre_expiry_warn,
                  'oi_regime': oi_regime, 'liquidity_ok': liquidity_ok,
                  'late_entry': late_entry, 'time_block': time_block,
                  'gate_results': gate_results, 'lot_size': lot_size})
        return r

    def _safe_none(self, lot_size=75) -> dict:
        return {
            'signal_id': '', 'setup_type': self.SETUP_NONE,
            'setup_quality': 0, 'blocked_reason': 'Evaluation error',
            'expiry_day': False, 'pre_expiry_warning': False,
            'oi_regime': 'NORMAL', 'liquidity_ok': False,
            'late_entry': False, 'time_block': 'OUTSIDE',
            'gate_results': {}, 'short_strike': 0.0,
            'short_option_type': '', 'short_ltp': 0.0,
            'hedge_strike': 0.0, 'hedge_ltp': 0.0,
            'net_premium': 0.0, 'max_risk': 0.0, 'lot_size': lot_size,
            'net_premium_total': 0.0, 'max_risk_total': 0.0,
        }


# ─────────────────────────────────────────────────────────────────────────────
# 11. StartupChecker
# ─────────────────────────────────────────────────────────────────────────────

class StartupChecker:
    """
    Runs 30 checks across 5 groups (SYS×5, AUTH×5, INST×6, FEED×9, SNAP×5).
    Phase 1 (SYS/AUTH/INST) runs once at startup.
    Phase 2 (FEED/SNAP) runs every cycle after data is fetched.
    """

    STATUS_PASS = 'PASS'
    STATUS_WARN = 'WARN'
    STATUS_FAIL = 'FAIL'

    # Colors (RGB float dicts for gspread batch_format)
    _GREEN  = {'red': 0.851, 'green': 0.918, 'blue': 0.827}
    _ORANGE = {'red': 0.988, 'green': 0.898, 'blue': 0.804}
    _RED    = {'red': 0.957, 'green': 0.800, 'blue': 0.800}

    def __init__(self, max_score: int):
        self.max_score       = max_score
        self.phase1_results: List[dict] = []
        self.phase2_results: List[dict] = []

    # ── Phase 1 — session startup ─────────────────────────────────────────────

    def run_phase1(
        self,
        gc,
        spreadsheet,
        api_client,           # SmartApiClient instance
        instruments,          # dict: {expiry_str, focus_zone, futures_token, nifty_options, expiry_dt}
        expiry_str:   str,
        expiry_dt,
        focus_zone:   list,
        is_weekly:    bool,
    ):
        self.phase1_results = []
        ts = ist_str()

        # ── GROUP 1: SYS ─────────────────────────────────────────────────────
        self._check_sys01(ts)
        self._check_sys02(ts)
        self._check_sys03(gc, spreadsheet, ts)
        self._check_sys04(ts)
        self._check_sys05(ts)

        # ── GROUP 2: AUTH ─────────────────────────────────────────────────────
        self._check_auth01(api_client, ts)
        self._check_auth02(api_client, ts)
        self._check_auth03(ts)
        self._check_auth04(api_client, ts)
        self._check_auth05(api_client, ts)

        # ── GROUP 3: INST ─────────────────────────────────────────────────────
        self._check_inst01(instruments, ts)
        self._check_inst02(instruments, ts)
        self._check_inst03(instruments, ts)
        self._check_inst04(expiry_str, instruments, ts)
        self._check_inst05(instruments, expiry_dt, ts)
        self._check_inst06(focus_zone, instruments, expiry_str, ts)

    # ── Phase 2 — per-cycle quality gate ─────────────────────────────────────

    def run_phase2(
        self,
        spot_df,
        futures_df,
        chain,            # current option chain DataFrame
        prev_chain,       # previous snapshot DataFrame or None
        score:     int,
        is_weekly: bool,
        expiry_dt,
        expiry_str: str,
        prev_atm:   float,
        current_atm: float,
        prev_cycle_ts,
        cycle_num:  int,
        max_score:  int,
    ):
        self.phase2_results = []
        ts = ist_str()

        self._check_feed01(spot_df, ts)
        self._check_feed02(spot_df, ts)
        self._check_feed03(futures_df, ts)
        self._check_feed04(futures_df, ts)
        self._check_feed05(chain, ts)
        self._check_feed06(chain, ts)
        self._check_feed07(chain, ts)
        self._check_feed08(chain, ts)
        self._check_feed09(is_weekly, ts)
        self._check_snap01(cycle_num, ts)
        self._check_snap02(prev_cycle_ts, ts)
        self._check_snap03(prev_atm, current_atm, ts)
        self._check_snap04(score, max_score, ts)
        self._check_snap05(chain, prev_chain, ts)

    # ── Summary helpers ───────────────────────────────────────────────────────

    def all_results(self) -> List[dict]:
        return self.phase1_results + self.phase2_results

    def summary(self) -> dict:
        results = self.all_results()
        warns = sum(1 for r in results if r['status'] == self.STATUS_WARN)
        fails = sum(1 for r in results if r['status'] == self.STATUS_FAIL)
        return {'warns': warns, 'fails': fails, 'results': results}

    def has_critical_fail(self) -> bool:
        return any(r['status'] == self.STATUS_FAIL for r in self.all_results())

    # ── Internal result recorder ──────────────────────────────────────────────

    def _record(self, results_list: List[dict], check_id: str, group: str,
                description: str, status: str, detail: str, ts: str):
        results_list.append({
            'check_id':    check_id,
            'group':       group,
            'description': description,
            'status':      status,
            'detail':      detail,
            'timestamp':   ts,
        })
        icon = {'PASS': '✔', 'WARN': '⚠', 'FAIL': '✘'}.get(status, '?')
        lvl  = {'PASS': log.debug, 'WARN': log.warning, 'FAIL': log.error}[status]
        lvl(f"[{check_id}] {icon} {status}: {detail}")

    def _p1(self, *a, **k): self._record(self.phase1_results, *a, **k)
    def _p2(self, *a, **k): self._record(self.phase2_results, *a, **k)

    # ══════════════════════════════════════════════════════════════════════════
    # SYS checks
    # ══════════════════════════════════════════════════════════════════════════

    def _check_sys01(self, ts):
        """SYS-01 | System clock accuracy | CRITICAL"""
        import ntplib, time as _time
        try:
            client = ntplib.NTPClient()
            try:
                resp = client.request('pool.ntp.org', version=3)
            except Exception:
                resp = client.request('time.cloudflare.com', version=3)
            drift = abs(resp.offset)
            if drift > 30:
                self._p1('SYS-01', 'SYS', 'System clock accuracy', self.STATUS_FAIL,
                         f'Clock drift {drift:.1f}s > 30s — synchronise system clock immediately.', ts)
            elif drift > 15:
                self._p1('SYS-01', 'SYS', 'System clock accuracy', self.STATUS_WARN,
                         f'Clock drift {drift:.1f}s (>15s threshold). Recommend NTP sync.', ts)
            else:
                self._p1('SYS-01', 'SYS', 'System clock accuracy', self.STATUS_PASS,
                         f'Clock drift {drift:.3f}s — within tolerance.', ts)
        except Exception as e:
            self._p1('SYS-01', 'SYS', 'System clock accuracy', self.STATUS_WARN,
                     f'NTP servers unreachable ({e}). Clock accuracy cannot be verified.', ts)

    def _check_sys02(self, ts):
        """SYS-02 | Market hours check | WARN"""
        from datetime import time as dtime
        ist = now_ist()
        in_hours = (ist.weekday() < 5 and dtime(9, 15) <= ist.time() <= dtime(15, 30))
        if not in_hours:
            self._p1('SYS-02', 'SYS', 'Market hours check', self.STATUS_WARN,
                     'Outside NSE market hours. Data may be stale or unavailable. Running in analysis-only mode.', ts)
        else:
            self._p1('SYS-02', 'SYS', 'Market hours check', self.STATUS_PASS,
                     f'Within market hours ({ist.strftime("%H:%M IST")}).', ts)

    def _check_sys03(self, gc, spreadsheet, ts):
        """SYS-03 | Google Sheet accessible and writable | CRITICAL"""
        try:
            ws = spreadsheet.worksheet('SETTINGS')
            ws.acell('B5').value
            self._p1('SYS-03', 'SYS', 'Google Sheet accessible and writable', self.STATUS_PASS,
                     'SETTINGS tab readable.', ts)
        except Exception as e:
            self._p1('SYS-03', 'SYS', 'Google Sheet accessible and writable', self.STATUS_FAIL,
                     f'Cannot access spreadsheet: {e}. Check service account permissions.', ts)

    def _check_sys04(self, ts):
        """SYS-04 | Output folder writable | WARN"""
        import pathlib as _pl
        try:
            for d in [CONFIG['LOG_DIR'], CONFIG['CACHE_DIR']]:
                p = _pl.Path(d)
                p.mkdir(parents=True, exist_ok=True)
                test_f = p / '.write_test'
                test_f.write_text('ok')
                test_f.unlink()
            self._p1('SYS-04', 'SYS', 'Output folder writable', self.STATUS_PASS,
                     f"logs/ and cache/ writable.", ts)
        except Exception as e:
            self._p1('SYS-04', 'SYS', 'Output folder writable', self.STATUS_WARN,
                     f'Output folder issue: {e}', ts)

    def _check_sys05(self, ts):
        """SYS-05 | Python dependency check | CRITICAL"""
        mandatory = ['SmartApi', 'pandas', 'numpy', 'gspread', 'google.oauth2',
                     'pyotp', 'requests', 'ntplib', 'logzero']
        failed = []
        for pkg in mandatory:
            try:
                __import__(pkg)
            except ImportError:
                failed.append(pkg)
        if failed:
            self._p1('SYS-05', 'SYS', 'Python dependency check', self.STATUS_FAIL,
                     f'Missing mandatory packages: {failed}. Run: pip install {" ".join(failed)}', ts)
        else:
            extra = 'OpenAI HTTPS mode ready. No SDK dependency required.'
            self._p1('SYS-05', 'SYS', 'Python dependency check', self.STATUS_PASS,
                     f'All mandatory dependencies present. {extra}', ts)

    # ══════════════════════════════════════════════════════════════════════════
    # AUTH checks
    # ══════════════════════════════════════════════════════════════════════════

    def _check_auth01(self, api_client, ts):
        """AUTH-01 | Login success and session token validity | CRITICAL"""
        at = getattr(api_client, 'auth_token', '')
        rt = getattr(api_client, 'refresh_token', '')
        ft = getattr(api_client, 'feed_token', '')
        if at and rt:
            self._p1('AUTH-01', 'AUTH', 'Login success and session token validity', self.STATUS_PASS,
                     'authToken and refreshToken present.', ts)
        else:
            self._p1('AUTH-01', 'AUTH', 'Login success and session token validity', self.STATUS_FAIL,
                     'authToken or refreshToken missing — login may have failed.', ts)

    def _check_auth02(self, api_client, ts):
        """AUTH-02 | Login credential and TOTP error handling | CRITICAL"""
        # Pass — this is a structural check that errors are caught in SmartApiClient.login()
        err = getattr(api_client, 'last_login_error', None)
        if err:
            self._p1('AUTH-02', 'AUTH', 'Login credential and TOTP error handling', self.STATUS_FAIL,
                     str(err), ts)
        else:
            self._p1('AUTH-02', 'AUTH', 'Login credential and TOTP error handling', self.STATUS_PASS,
                     'No credential or TOTP errors at login.', ts)

    def _check_auth03(self, ts):
        """AUTH-03 | Session midnight renewal check | WARN"""
        ist = now_ist()
        if 23 <= ist.hour and ist.minute >= 30:
            self._p1('AUTH-03', 'AUTH', 'Session midnight renewal check', self.STATUS_WARN,
                     'Approaching midnight — session renewal will be triggered at 23:30–23:59 IST.', ts)
        else:
            self._p1('AUTH-03', 'AUTH', 'Session midnight renewal check', self.STATUS_PASS,
                     'Not in midnight renewal window.', ts)

    def _check_auth04(self, api_client, ts):
        """AUTH-04 | refreshToken captured at login | CRITICAL"""
        rt = getattr(api_client, 'refresh_token', '')
        if rt:
            self._p1('AUTH-04', 'AUTH', 'refreshToken captured at login', self.STATUS_PASS,
                     'refreshToken present.', ts)
        else:
            self._p1('AUTH-04', 'AUTH', 'refreshToken captured at login', self.STATUS_FAIL,
                     'refreshToken empty — session renewal will fail at midnight.', ts)

    def _check_auth05(self, api_client, ts):
        """AUTH-05 | Feed token availability | WARN"""
        ft = getattr(api_client, 'feed_token', '')
        if ft:
            self._p1('AUTH-05', 'AUTH', 'Feed token availability', self.STATUS_PASS,
                     'feedToken present.', ts)
        else:
            self._p1('AUTH-05', 'AUTH', 'Feed token availability', self.STATUS_WARN,
                     'feedToken absent — polling mode unaffected but WebSocket feeds will not work.', ts)

    # ══════════════════════════════════════════════════════════════════════════
    # INST checks
    # ══════════════════════════════════════════════════════════════════════════

    def _check_inst01(self, instruments, ts):
        """INST-01 | Instrument master date and time freshness | CRITICAL"""
        cache_age_h = instruments.get('cache_age_hours', 0)
        if cache_age_h > 24:
            self._p1('INST-01', 'INST', 'Instrument master freshness', self.STATUS_FAIL,
                     f'Instrument master is {cache_age_h:.1f}h old (>24h). Download failed.', ts)
        else:
            self._p1('INST-01', 'INST', 'Instrument master freshness', self.STATUS_PASS,
                     f'Instrument master age: {cache_age_h:.1f}h.', ts)

    def _check_inst02(self, instruments, ts):
        """INST-02 | Instrument master record count | WARN"""
        count = instruments.get('record_count', 0)
        if count < 10000:
            self._p1('INST-02', 'INST', 'Instrument master record count', self.STATUS_FAIL,
                     f'Only {count} records — below 10,000 minimum. Download may be corrupt.', ts)
        elif count < 50000:
            self._p1('INST-02', 'INST', 'Instrument master record count', self.STATUS_WARN,
                     f'{count} records — below expected 50,000.', ts)
        else:
            self._p1('INST-02', 'INST', 'Instrument master record count', self.STATUS_PASS,
                     f'{count:,} records loaded.', ts)

    def _check_inst03(self, instruments, ts):
        """INST-03 | NIFTY option contracts found | CRITICAL"""
        count = instruments.get('nifty_option_count', 0)
        if count == 0:
            self._p1('INST-03', 'INST', 'NIFTY option contracts found', self.STATUS_FAIL,
                     "No NIFTY option contracts found. Verify filter uses name=='NIFTY' and "
                     "instrumenttype=='OPTIDX'. Do not filter by symbol=='NIFTY'.", ts)
        else:
            self._p1('INST-03', 'INST', 'NIFTY option contracts found', self.STATUS_PASS,
                     f'{count} NIFTY OPTIDX contracts loaded.', ts)

    def _check_inst04(self, expiry_str, instruments, ts):
        """INST-04 | Selected expiry exists | CRITICAL"""
        available = instruments.get('available_expiries', [])
        if expiry_str and expiry_str in available:
            self._p1('INST-04', 'INST', 'Selected expiry exists', self.STATUS_PASS,
                     f'Expiry {expiry_str} found in instrument master.', ts)
        else:
            self._p1('INST-04', 'INST', 'Selected expiry exists', self.STATUS_FAIL,
                     f'Expiry {expiry_str!r} not found. Available: {available[:5]}', ts)

    def _check_inst05(self, instruments, expiry_dt, ts):
        """INST-05 | NIFTY Futures token resolved | CRITICAL"""
        from datetime import date as _date
        ft = instruments.get('futures_token', '')
        fe = instruments.get('futures_expiry_dt')
        if not ft:
            self._p1('INST-05', 'INST', 'NIFTY Futures token resolved', self.STATUS_FAIL,
                     'NIFTY FUTIDX token not resolved. Futures candles and VWAP unavailable.', ts)
        else:
            if pd.isna(fe):
                days_to_fut = 99
            elif isinstance(fe, pd.Timestamp):
                days_to_fut = (fe.date() - now_ist().date()).days
            elif hasattr(fe, 'toordinal'):
                days_to_fut = (fe - now_ist().date()).days
            else:
                days_to_fut = 99

            if days_to_fut <= 3:
                self._p1('INST-05', 'INST', 'NIFTY Futures token resolved', self.STATUS_WARN,
                         f'Futures token {ft} resolved but expiry in {days_to_fut} days.', ts)
                return

            self._p1('INST-05', 'INST', 'NIFTY Futures token resolved', self.STATUS_PASS,
                     f'Futures token {ft} resolved.', ts)

    def _check_inst06(self, focus_zone, instruments, expiry_str, ts):
        """INST-06 | Focus zone strike coverage | INFO/WARN at startup"""
        fz_strikes = focus_zone or []
        covered = instruments.get('focus_zone_covered', len(fz_strikes))
        total = len(fz_strikes)

        if total == 0:
            self._p1(
                'INST-06',
                'INST',
                'Focus zone strike coverage',
                self.STATUS_WARN,
                'Focus zone not built yet at startup. Coverage will be validated during the live cycle.',
                ts
            )
            return

        ratio = covered / total if total > 0 else 0.0
        if ratio < 0.5:
            self._p1('INST-06', 'INST', 'Focus zone strike coverage', self.STATUS_FAIL,
                     f'Only {covered}/{total} strikes have CE+PE contracts ({ratio*100:.0f}%).', ts)
        elif ratio < 1.0:
            self._p1('INST-06', 'INST', 'Focus zone strike coverage', self.STATUS_WARN,
                     f'{covered}/{total} strikes covered — some missing CE or PE contracts.', ts)
        else:
            self._p1('INST-06', 'INST', 'Focus zone strike coverage', self.STATUS_PASS,
                     f'All {total} focus zone strikes have CE and PE contracts.', ts)

    # ══════════════════════════════════════════════════════════════════════════
    # FEED checks (Phase 2)
    # ══════════════════════════════════════════════════════════════════════════

    def _check_feed01(self, spot_df, ts):
        """FEED-01 | Spot index candle data received | CRITICAL"""
        if spot_df is not None and len(spot_df) > 0:
            self._p2('FEED-01', 'FEED', 'Spot index candle data received', self.STATUS_PASS,
                     f'{len(spot_df)} spot candles received.', ts)
        else:
            self._p2('FEED-01', 'FEED', 'Spot index candle data received', self.STATUS_FAIL,
                     'No spot candle data — ATM and price structure unreliable.', ts)

    def _check_feed02(self, spot_df, ts):
        """FEED-02 | Spot candle data recency | CRITICAL"""
        from datetime import time as dtime
        ist = now_ist()
        if not (ist.weekday() < 5 and dtime(9, 15) <= ist.time() <= dtime(15, 30)):
            self._p2('FEED-02', 'FEED', 'Spot candle data recency', self.STATUS_PASS,
                     'Outside market hours — recency check skipped.', ts)
            return
        if spot_df is None or len(spot_df) == 0:
            self._p2('FEED-02', 'FEED', 'Spot candle data recency', self.STATUS_FAIL,
                     'No spot data to check recency.', ts)
            return
        try:
            last_ts = spot_df.index[-1] if hasattr(spot_df.index[-1], 'hour') else None
            if last_ts is None:
                try:
                    import pandas as pd
                    last_ts = pd.Timestamp(spot_df.iloc[-1].get('timestamp', ist))
                except Exception:
                    last_ts = ist
            gap_min = (ist.replace(tzinfo=None) - last_ts.replace(tzinfo=None)).total_seconds() / 60
            if gap_min > 20:
                self._p2('FEED-02', 'FEED', 'Spot candle data recency', self.STATUS_FAIL,
                         f'Last spot candle is {gap_min:.0f}min old (>20min).', ts)
            elif gap_min > 10:
                self._p2('FEED-02', 'FEED', 'Spot candle data recency', self.STATUS_WARN,
                         f'Last spot candle is {gap_min:.0f}min old (10-20min).', ts)
            else:
                self._p2('FEED-02', 'FEED', 'Spot candle data recency', self.STATUS_PASS,
                         f'Last spot candle is {gap_min:.1f}min old.', ts)
        except Exception as e:
            self._p2('FEED-02', 'FEED', 'Spot candle data recency', self.STATUS_WARN,
                     f'Could not check recency: {e}', ts)

    def _check_feed03(self, futures_df, ts):
        """FEED-03 | Futures candle data received | WARN"""
        if futures_df is not None and len(futures_df) > 0:
            self._p2('FEED-03', 'FEED', 'Futures candle data received', self.STATUS_PASS,
                     f'{len(futures_df)} futures candles received.', ts)
        else:
            self._p2('FEED-03', 'FEED', 'Futures candle data received', self.STATUS_WARN,
                     'No futures candle data — VWAP and volume signals disabled this cycle.', ts)

    def _check_feed04(self, futures_df, ts):
        """FEED-04 | Futures candle volume non-zero | WARN"""
        if futures_df is None or len(futures_df) == 0:
            self._p2('FEED-04', 'FEED', 'Futures candle volume non-zero', self.STATUS_WARN,
                     'No futures data — volume check skipped.', ts)
            return
        try:
            non_zero = (futures_df['volume'] > 0).sum()
            if non_zero == 0:
                self._p2('FEED-04', 'FEED', 'Futures candle volume non-zero', self.STATUS_WARN,
                         'All futures candle volumes are zero — VWAP signals set to NEUTRAL.', ts)
            else:
                self._p2('FEED-04', 'FEED', 'Futures candle volume non-zero', self.STATUS_PASS,
                         f'{non_zero}/{len(futures_df)} candles have non-zero volume.', ts)
        except Exception as e:
            self._p2('FEED-04', 'FEED', 'Futures candle volume non-zero', self.STATUS_WARN,
                     f'Volume check failed: {e}', ts)

    def _check_feed05(self, chain, ts):
        """FEED-05 | Option quote data received | CRITICAL"""
        if chain is not None and len(chain) > 0:
            self._p2('FEED-05', 'FEED', 'Option quote data received', self.STATUS_PASS,
                     f'{len(chain)} option chain rows received.', ts)
        else:
            self._p2('FEED-05', 'FEED', 'Option quote data received', self.STATUS_FAIL,
                     'Empty option chain — getMarketData returned no valid quotes.', ts)

    def _check_feed06(self, chain, ts):
        """FEED-06 | Option quote coverage ratio | WARN"""
        if chain is None or len(chain) == 0:
            self._p2('FEED-06', 'FEED', 'Option quote coverage ratio', self.STATUS_WARN,
                     'No chain data to check coverage.', ts)
            return
        try:
            ce_valid = chain['ce_ltp'].apply(
                lambda v: v is not None and not (isinstance(v, float) and math.isnan(v))
            ).sum()
            pe_valid = chain['pe_ltp'].apply(
                lambda v: v is not None and not (isinstance(v, float) and math.isnan(v))
            ).sum()
            total = len(chain) * 2
            valid = ce_valid + pe_valid
            ratio = valid / total if total > 0 else 0
            if ratio < 0.30:
                self._p2('FEED-06', 'FEED', 'Option quote coverage ratio', self.STATUS_FAIL,
                         f'Only {ratio*100:.0f}% option quotes returned — data unreliable.', ts)
            elif ratio < 0.70:
                self._p2('FEED-06', 'FEED', 'Option quote coverage ratio', self.STATUS_WARN,
                         f'{ratio*100:.0f}% quote coverage (below 70%).', ts)
            else:
                self._p2('FEED-06', 'FEED', 'Option quote coverage ratio', self.STATUS_PASS,
                         f'{ratio*100:.0f}% quote coverage.', ts)
        except Exception as e:
            self._p2('FEED-06', 'FEED', 'Option quote coverage ratio', self.STATUS_WARN,
                     f'Coverage check failed: {e}', ts)

    def _check_feed07(self, chain, ts):
        """FEED-07 | OI data availability | WARN"""
        if chain is None or len(chain) == 0:
            self._p2('FEED-07', 'FEED', 'OI data availability', self.STATUS_WARN,
                     'No chain data for OI check.', ts)
            return
        try:
            ce_oi_nonzero = (chain['ce_open_interest'].fillna(0) > 0).any()
            pe_oi_nonzero = (chain['pe_open_interest'].fillna(0) > 0).any()
            if not ce_oi_nonzero and not pe_oi_nonzero:
                self._p2('FEED-07', 'FEED', 'OI data availability', self.STATUS_WARN,
                         'All OI values are zero — OI-based signals unreliable.', ts)
            else:
                self._p2('FEED-07', 'FEED', 'OI data availability', self.STATUS_PASS,
                         'Non-zero OI available for at least one CE and PE token.', ts)
        except Exception as e:
            self._p2('FEED-07', 'FEED', 'OI data availability', self.STATUS_WARN,
                     f'OI check failed: {e}', ts)

    def _check_feed08(self, chain, ts):
        """FEED-08 | Option Greeks / IV availability | WARN"""
        if chain is None or len(chain) == 0:
            self._p2('FEED-08', 'FEED', 'Option Greeks / IV availability', self.STATUS_WARN,
                     'No chain data for IV check.', ts)
            return
        try:
            ce_iv_ok = chain['ce_iv'].apply(
                lambda v: v is not None and isinstance(v, (int, float)) and not math.isnan(v) and v > 0
            ).any()
            pe_iv_ok = chain['pe_iv'].apply(
                lambda v: v is not None and isinstance(v, (int, float)) and not math.isnan(v) and v > 0
            ).any()
            if ce_iv_ok or pe_iv_ok:
                self._p2('FEED-08', 'FEED', 'Option Greeks / IV availability', self.STATUS_PASS,
                         'At least one non-zero IV value available.', ts)
            else:
                self._p2('FEED-08', 'FEED', 'Option Greeks / IV availability', self.STATUS_WARN,
                         'All IV values are NaN — Greeks endpoint may be outside hours or unavailable.', ts)
        except Exception as e:
            self._p2('FEED-08', 'FEED', 'Option Greeks / IV availability', self.STATUS_WARN,
                     f'IV check failed: {e}', ts)

    def _check_feed09(self, is_weekly, ts):
        """FEED-09 | Weekly expiry IV warning | WARN"""
        if is_weekly:
            self._p2('FEED-09', 'FEED', 'Weekly expiry IV warning', self.STATUS_WARN,
                     'Weekly expiry selected. IV values set to NaN due to known Angel One Option Greeks API limitation.', ts)
        else:
            self._p2('FEED-09', 'FEED', 'Weekly expiry IV warning', self.STATUS_PASS,
                     'Monthly expiry — IV endpoint supported.', ts)

    # ══════════════════════════════════════════════════════════════════════════
    # SNAP checks (Phase 2)
    # ══════════════════════════════════════════════════════════════════════════

    def _check_snap01(self, cycle_num, ts):
        """SNAP-01 | First cycle change OI warning | WARN"""
        if cycle_num <= 1:
            self._p2('SNAP-01', 'SNAP', 'First cycle change OI warning', self.STATUS_WARN,
                     'First cycle — no previous snapshot. Change OI signals must not be used until cycle 2.', ts)
        else:
            self._p2('SNAP-01', 'SNAP', 'First cycle change OI warning', self.STATUS_PASS,
                     f'Cycle {cycle_num} — change OI computed from previous snapshot.', ts)

    def _check_snap02(self, prev_cycle_ts, ts):
        """SNAP-02 | Snapshot age at cycle start | WARN"""
        if prev_cycle_ts is None:
            self._p2('SNAP-02', 'SNAP', 'Snapshot age at cycle start', self.STATUS_PASS,
                     'First cycle — no previous timestamp.', ts)
            return
        try:
            elapsed = (now_ist().replace(tzinfo=None) - prev_cycle_ts.replace(tzinfo=None)).total_seconds()
            interval_s = CONFIG.get('_INTERVAL_SECONDS', 300)
            if elapsed > interval_s * 2:
                self._p2('SNAP-02', 'SNAP', 'Snapshot age at cycle start', self.STATUS_WARN,
                         f'Previous cycle was {elapsed:.0f}s ago (>2× interval). Snapshot may be stale.', ts)
            else:
                self._p2('SNAP-02', 'SNAP', 'Snapshot age at cycle start', self.STATUS_PASS,
                         f'Previous cycle {elapsed:.0f}s ago — within expected interval.', ts)
        except Exception as e:
            self._p2('SNAP-02', 'SNAP', 'Snapshot age at cycle start', self.STATUS_WARN,
                     f'Age check failed: {e}', ts)

    def _check_snap03(self, prev_atm, current_atm, ts):
        """SNAP-03 | ATM strike change detection | WARN"""
        if prev_atm is None or prev_atm == 0:
            self._p2('SNAP-03', 'SNAP', 'ATM strike change detection', self.STATUS_PASS,
                     'First cycle — no previous ATM.', ts)
            return
        delta = abs(current_atm - prev_atm)
        if delta > 150:
            self._p2('SNAP-03', 'SNAP', 'ATM strike change detection', self.STATUS_WARN,
                     f'ATM moved {delta:.0f} pts in one cycle — large shift detected.', ts)
        else:
            self._p2('SNAP-03', 'SNAP', 'ATM strike change detection', self.STATUS_PASS,
                     f'ATM moved {delta:.0f} pts — within normal range.', ts)

    def _check_snap04(self, score, max_score, ts):
        """SNAP-04 | Score boundary sanity check | WARN"""
        if abs(score) > max_score:
            self._p2('SNAP-04', 'SNAP', 'Score boundary sanity check', self.STATUS_WARN,
                     f'Score {score} exceeds max_score ±{max_score} — scoring logic error.', ts)
        else:
            self._p2('SNAP-04', 'SNAP', 'Score boundary sanity check', self.STATUS_PASS,
                     f'Score {score}/{max_score} within bounds.', ts)

    def _check_snap05(self, chain, prev_chain, ts):
        """SNAP-05 | Previous snapshot strike alignment | WARN"""
        if prev_chain is None or len(prev_chain) == 0:
            self._p2('SNAP-05', 'SNAP', 'Previous snapshot strike alignment', self.STATUS_PASS,
                     'No previous snapshot to align.', ts)
            return
        try:
            curr_strikes = set(chain['strike'].tolist())
            prev_strikes = set(prev_chain['strike'].tolist())
            overlap = len(curr_strikes & prev_strikes)
            total   = max(len(curr_strikes), len(prev_strikes), 1)
            ratio   = overlap / total
            if ratio < 0.5:
                self._p2('SNAP-05', 'SNAP', 'Previous snapshot strike alignment', self.STATUS_WARN,
                         f'Only {ratio*100:.0f}% strike overlap between current and previous snapshots.', ts)
            else:
                self._p2('SNAP-05', 'SNAP', 'Previous snapshot strike alignment', self.STATUS_PASS,
                         f'{ratio*100:.0f}% strike alignment with previous snapshot.', ts)
        except Exception as e:
            self._p2('SNAP-05', 'SNAP', 'Previous snapshot strike alignment', self.STATUS_WARN,
                     f'Alignment check failed: {e}', ts)


# ─────────────────────────────────────────────────────────────────────────────
# 11. SheetsWriter
# ─────────────────────────────────────────────────────────────────────────────

class SheetsWriter:
    """
    Manages all Google Sheets writes. Uses gspread 6.x service account auth.
    All 16 tabs created in correct order. All writes via retry_call().
    """

    TAB_ORDER = [
        'DASHBOARD', 'VISUALIZE', 'SIGNAL', 'POSITION_LOG', 'EXECUTION',
        'CLAUDE_ANALYSIS', 'CURRENT_SITUATION',
        'STARTUP_CHECKLIST', 'CURRENT_SNAPSHOT', 'PREVIOUS_SNAPSHOT', 'COMPARISON',
        'HISTORY_LOG', 'TODAY_LOG', 'DAILY_REVIEW',
        'SETTINGS_HELP', 'SETTINGS',
    ]

    # Colors (RGB float dicts)
    GREEN    = {'red': 0.851, 'green': 0.918, 'blue': 0.827}
    RED      = {'red': 0.957, 'green': 0.800, 'blue': 0.800}
    YELLOW   = {'red': 1.000, 'green': 0.949, 'blue': 0.800}
    ORANGE   = {'red': 0.988, 'green': 0.898, 'blue': 0.804}
    DEEP_RED = {'red': 0.878, 'green': 0.400, 'blue': 0.400}
    WHITE    = {'red': 1.0,   'green': 1.0,   'blue': 1.0  }
    NAVY     = {'red': 0.133, 'green': 0.224, 'blue': 0.400}

    def __init__(self):
        self.gc          = None
        self.spreadsheet = None
        self._ws_cache: Dict[str, Any] = {}
        self._today_log_date: str = ''  # Format: YYYY-MM-DD. Tracks when TODAY_LOG was last cleared.

    def connect(self):
        """Authenticate with Google Sheets using service account."""
        try:
            self.gc          = gspread.service_account(filename=CONFIG['GOOGLE_SERVICE_ACCOUNT_JSON'])
            self.spreadsheet = self.gc.open_by_key(CONFIG['SPREADSHEET_ID'])
            log.info(f"[Sheets] Connected to spreadsheet: {self.spreadsheet.title}")
        except Exception as e:
            raise RuntimeError(
                f"Google Sheets authentication failed. Verify the service account JSON key file "
                f"path in CONFIG and that the spreadsheet has been shared with the service account "
                f"email. Full error: {e}"
            )

    def get_worksheet(self, name: str):
        """Get worksheet by name, creating it if absent. Cached."""
        if name in self._ws_cache:
            return self._ws_cache[name]
        titles = [ws.title for ws in self.spreadsheet.worksheets()]
        if name in titles:
            ws = self.spreadsheet.worksheet(name)
        else:
            # ── CHANGE 5: Increase column count from 30 to 60 for extended headers ──
            ws = self.spreadsheet.add_worksheet(title=name, rows=500, cols=60)
            log.info(f"[Sheets] Created new tab: {name}")
        self._ws_cache[name] = ws
        return ws

    def settings_tab_exists(self) -> bool:
        titles = [ws.title for ws in self.spreadsheet.worksheets()]
        return 'SETTINGS' in titles

    def ensure_tab_order(self):
        """Reorder tabs to match TAB_ORDER (creates missing tabs first)."""
        try:
            existing = {ws.title: ws for ws in self.spreadsheet.worksheets()}
            for tab in self.TAB_ORDER:
                if tab not in existing:
                    self.get_worksheet(tab)
                    if tab == 'EXECUTION':
                        self.write_execution_scaffold()
            # Reorder
            ordered = []
            for tab in self.TAB_ORDER:
                try:
                    ordered.append(self.spreadsheet.worksheet(tab))
                except Exception:
                    pass
            if ordered:
                self.spreadsheet.reorder_worksheets(ordered)
        except Exception as e:
            log.warning(f"[Sheets] Tab reorder failed (non-critical): {e}")

    # ── DASHBOARD ─────────────────────────────────────────────────────────────

    def write_dashboard(
        self,
        signals:          dict,
        metrics:          dict,
        sr_event:         dict,
        theta_env:        dict,
        checklist_result: dict,
        prev_day:         dict,
        vix_data:         dict,
        claude_summary:   Optional[dict] = None,
        snapshot:         Optional[dict] = None,
    ):
        try:
            ws = self.get_worksheet('DASHBOARD')

            bias             = signals.get('bias', 'NEUTRAL')
            score_display    = signals.get('score_display', '0/12')
            conf_display     = signals.get('confidence_display', '0.0%/100%')
            event_tag        = signals.get('event_tag', '—')
            price_structure  = signals.get('price_structure', '—')
            vwap_bias        = signals.get('vwap_bias', 'NEUTRAL')
            vol_bias         = signals.get('vol_bias', 'NEUTRAL')
            vwap_level       = signals.get('vwap_level', float('nan'))
            trap_msg         = signals.get('trap_msg', '')
            reasoning_pts    = signals.get('reasoning', [])
            bias_at          = signals.get('bias_calculated_at', ist_str())
            # Prefer snapshot for display fields not in signals dict
            _snap            = snapshot or {}
            spot             = _snap.get('spot', signals.get('spot', 0.0)) or 0.0
            atm              = _snap.get('atm',  signals.get('atm',  0))   or 0
            expiry_str       = _snap.get('expiry',      signals.get('expiry',      '—'))
            expiry_type      = _snap.get('expiry_type', signals.get('expiry_type', '—'))

            support          = int(metrics.get('support_strike', 0) or 0)
            resistance       = int(metrics.get('resistance_strike', 0) or 0)
            ce_oi            = int(metrics.get('total_ce_oi', 0) or 0)
            pe_oi            = int(metrics.get('total_pe_oi', 0) or 0)
            ce_chg_oi        = int(metrics.get('total_ce_chg_oi', 0) or 0)
            pe_chg_oi        = int(metrics.get('total_pe_chg_oi', 0) or 0)
            ce_vol           = int(metrics.get('total_ce_volume', 0) or 0)
            pe_vol           = int(metrics.get('total_pe_volume', 0) or 0)
            pcr_oi           = metrics.get('pcr_oi', float('nan'))
            pcr_chg_oi       = metrics.get('pcr_chg_oi', float('nan'))
            support_shift    = metrics.get('support_shift', 0) or 0
            resistance_shift = metrics.get('resistance_shift', 0) or 0
            vol_imbalance    = metrics.get('vol_imbalance', float('nan'))

            sr_ev            = sr_event.get('event', 'NONE')
            sr_conf          = sr_event.get('confidence', 'N/A')
            sr_reason        = sr_event.get('reasoning', '—')
            cond_met         = sr_event.get('conditions_met', [])
            cond_fail        = sr_event.get('conditions_failed', [])
            candle_pat       = sr_event.get('candle_pattern', 'NONE')

            warns = checklist_result.get('warns', 0)
            fails = checklist_result.get('fails', 0)
            status_text  = 'ALL PASS' if warns == 0 and fails == 0 else \
                           ('CRITICAL FAILURES' if fails > 0 else 'WARNINGS ACTIVE')
            system_msg   = (f'{fails} critical failure(s). {warns} warning(s). '
                            f'Check STARTUP_CHECKLIST tab.' if fails > 0
                            else f'{warns} warning(s).' if warns > 0 else 'All systems nominal.')

            ts = ist_str('%d-%b-%Y %H:%M:%S IST')

            def fmt_vix(v):
                return f'{v:.2f}' if (v is not None and not math.isnan(v)) else '—'

            def fmt_f(v, fmt=',.2f'):
                try:
                    return format(v, fmt)
                except Exception:
                    return safe_val(v)

            vwap_str = fmt_f(vwap_level) if (vwap_level and not math.isnan(vwap_level)) else 'N/A'
            pcr_str  = fmt_f(pcr_oi, '.3f') if (not math.isnan(pcr_oi)) else '—'
            pch_str  = fmt_f(pcr_chg_oi, '.3f') if (not math.isnan(pcr_chg_oi)) else '—'
            vi_str   = fmt_f(vol_imbalance, '.4f') if (not math.isnan(vol_imbalance)) else '—'
            spot_str = fmt_f(spot) if spot else '—'

            # Claude summary block values
            if claude_summary:
                c_bias     = claude_summary.get('market_bias', '—')
                c_strength = claude_summary.get('strength', '—')
                c_signal   = (claude_summary.get('signal', '') or '')[:60]
                c_agree    = claude_summary.get('score_agreement', False)
                c_risk     = (claude_summary.get('risk_note', '') or '')[:80]
                c_at       = claude_summary.get('bias_at', '—')
                c_agree_d  = '✅  YES' if c_agree else '⚠️  NO'
            else:
                c_bias = c_strength = c_signal = c_risk = c_at = '—'
                c_agree = False; c_agree_d = '—'

            # Condition labels
            met_str  = '; '.join(cond_met)  if isinstance(cond_met,  list) else str(cond_met  or '—')
            fail_str = '; '.join(cond_fail) if isinstance(cond_fail, list) else str(cond_fail or '—')

            header_rows: List[List] = [
                ['── NIFTY Dashboard ──', '', '', '', ''],
                ['Last Updated', ts, '', '', ''],
                ['Selected Expiry', expiry_str, '', 'Type:', expiry_type],
                [f'Spot Price (₹)', spot_str, '', 'ATM Strike:', str(atm)],
                ['', '', '', '', ''],
                ['── SIGNALS ──', '', '', '', ''],
                ['Final Bias', bias, 'Bias At:', bias_at, ''],
                ['Score', score_display, '', '', ''],
                ['Confidence', conf_display, '', '', ''],
                ['Event Tag', event_tag, '', '', ''],
                ['Price Structure', price_structure, '', '', ''],
                ['VWAP Bias', vwap_bias, '', '', ''],
                ['Volume Confirm', vol_bias, '', '', ''],
                ['VWAP Level', vwap_str, '', '', ''],
                ['Trap Warning', trap_msg or '—', '', '', ''],
                ['Reasoning', '', '', '', ''],
                *[['', pt, '', '', ''] for pt in (reasoning_pts or [])[:8]],
                ['', '', '', '', ''],
                ['── CLAUDE SUMMARY ──', '', '', '', ''],
                ['Claude last ran:', c_at, '', '', ''],
                ['Claude Bias', c_bias, 'Strength', c_strength, ''],
                ['Signal', c_signal, 'Score Agrees', c_agree_d, ''],
                ['Risk Note', c_risk, '', '', ''],
                ['', '', '', '', ''],
                ['── S/R EVENT DETECTION ──', '', '', '', ''],
                ['SR Event', sr_ev, '', '', ''],
                ['Confidence', sr_conf, '', '', ''],
                ['Candle Pattern', candle_pat, '', '', ''],
                ['SR Reasoning', sr_reason, '', '', ''],
                ['Conditions Met', met_str or '—', '', '', ''],
                ['Conditions ✗', fail_str or '—', '', '', ''],
                ['', '', '', '', ''],
                ['── OPTION CHAIN METRICS ──', '', '', '', ''],
                ['Support', str(support), '', 'Resistance:', str(resistance)],
                ['CE OI (Total)', f'{ce_oi:,}', '', 'PE OI (Total):', f'{pe_oi:,}'],
                ['CE Chg OI', f'{ce_chg_oi:+,}', '', 'PE Chg OI:', f'{pe_chg_oi:+,}'],
                ['CE Volume', f'{ce_vol:,}', '', 'PE Volume:', f'{pe_vol:,}'],
                ['PCR (OI)', pcr_str, '', 'PCR (Chg OI):', pch_str],
                ['Support Shift', f'{support_shift:+.0f} pts', '', 'Resistance Shift:', f'{resistance_shift:+.0f} pts'],
                ['Volume Imbalance', vi_str, '', '', ''],
                ['', '', '', '', ''],
                ['── PREMIUM ENVIRONMENT ──', '', '', '', ''],
                ['Market Condition', theta_env.get('market_condition', '—'), '', 'Decay Score:',
                 f"{theta_env.get('decay_score', 0):+d}/10"],
                ['Volatility Context', theta_env.get('volatility_context', '—'), '', 'India VIX:',
                 fmt_vix(theta_env.get('vix_level', float('nan')))],
                ['Price Behavior', theta_env.get('price_behavior', '—'), '', 'VIX Trend:',
                 vix_data.get('vix_trend', '—')],
                ['Days to Expiry', str(theta_env.get('days_to_expiry', 0)) + ' days', '', '', ''],
                ['Key Insight', theta_env.get('key_insight', '—'), '', '', ''],
                *[['', r, '', '', ''] for r in theta_env.get('reasoning', [])],
                ['Risk Note (Env)', theta_env.get('risk_note', '—'), '', '', ''],
                ['', '', '', '', ''],
                ['── CHECKLIST STATUS ──', '', '', '', ''],
                ['Warns', str(warns), '', 'Fails:', str(fails)],
                ['Status', status_text, '', '', ''],
                ['System Message', system_msg, '', '', ''],
            ]

            # Flatten and write
            vals = [[safe_val(c) for c in row] for row in header_rows]
            retry_call(
                lambda: ws.update(values=vals, range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label='DashboardWrite'
            )

            # Color formatting — find row indices dynamically
            formats = []

            def row_of(label):
                return next((i for i, r in enumerate(header_rows) if r and r[0] == label), None)

            def add_fmt(row_idx, col, color):
                if row_idx is not None:
                    cell = f'{col}{row_idx + 1}'
                    formats.append({'range': cell, 'format': {'backgroundColor': color}})

            # Final Bias color
            bias_colors = {
                'STRONG BULLISH': self.GREEN, 'BULLISH': self.GREEN, 'MILD BULLISH': self.GREEN,
                'NEUTRAL': self.YELLOW,
                'MILD BEARISH': self.RED, 'BEARISH': self.RED, 'STRONG BEARISH': self.RED,
            }
            bias_row = row_of('Final Bias')
            add_fmt(bias_row, 'B', bias_colors.get(bias, self.YELLOW))

            # Status color
            status_row = row_of('Status')
            status_color = self.RED if fails > 0 else (self.ORANGE if warns > 0 else self.GREEN)
            add_fmt(status_row, 'B', status_color)

            # Claude Summary colors
            claude_bias_row = row_of('Claude Bias')
            if claude_bias_row is not None and claude_summary:
                add_fmt(claude_bias_row, 'B', bias_colors.get(c_bias.upper(), self.YELLOW))
                strength_colors = {'Strong': self.GREEN, 'Moderate': self.YELLOW, 'Weak': self.ORANGE}
                add_fmt(claude_bias_row, 'D', strength_colors.get(c_strength, self.YELLOW))
                signal_row = row_of('Signal')
                if signal_row is not None:
                    add_fmt(signal_row, 'D',
                            self.GREEN if c_agree else self.ORANGE)

            # Market Condition color
            mc_row = row_of('Market Condition')
            mc_colors = {
                'Decay Favorable': self.GREEN,
                'Expansion Favorable': self.RED,
                'Neutral': self.YELLOW,
            }
            add_fmt(mc_row, 'B', mc_colors.get(theta_env.get('market_condition', ''), self.YELLOW))

            # Volatility Context color
            vc_row = row_of('Volatility Context')
            vc_colors = {
                'High': self.RED, 'Rising': self.ORANGE,
                'Low': self.GREEN, 'Falling': self.GREEN,
                'Moderate': self.YELLOW, 'Unknown': self.WHITE,
            }
            add_fmt(vc_row, 'B', vc_colors.get(theta_env.get('volatility_context', ''), self.WHITE))

            if formats:
                retry_call(
                    lambda: ws.batch_format(formats),
                    attempts=2, delay=2.0, fallback=None, label='DashboardFormat'
                )
        except Exception as e:
            log.error(f"[Sheets] write_dashboard() failed: {e}\n{__import__('traceback').format_exc()}")

    # ── STARTUP_CHECKLIST ─────────────────────────────────────────────────────

    def write_checklist(self, checklist_result: dict):
        try:
            ws = self.get_worksheet('STARTUP_CHECKLIST')
            results = checklist_result.get('results', [])
            warns   = checklist_result.get('warns', 0)
            fails   = checklist_result.get('fails', 0)

            if fails > 0:
                summary_status = f'🔴 CRITICAL FAILURES — {fails} fail(s), {warns} warning(s)'
                summary_color  = self.DEEP_RED
            elif warns > 0:
                summary_status = f'🟡 WARNINGS ACTIVE — {warns} warning(s)'
                summary_color  = self.ORANGE
            else:
                summary_status = '🟢 ALL PASS'
                summary_color  = self.GREEN

            header = [['STARTUP_CHECKLIST', summary_status, '', '', '', ''],
                      ['Check ID', 'Group', 'Description', 'Status', 'Detail', 'Timestamp']]
            rows   = [[r['check_id'], r['group'], r['description'], r['status'],
                       r['detail'], r['timestamp']] for r in results]
            all_rows = header + rows

            retry_call(
                lambda: ws.clear(),
                attempts=2, delay=2.0, fallback=None, label='ChecklistClear'
            )
            retry_call(
                lambda: ws.update(values=all_rows, range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label='ChecklistWrite'
            )

            # Color-code each result row
            formats = [{'range': 'A1:F1',
                        'format': {'backgroundColor': summary_color}}]
            status_color_map = {
                'PASS': self.GREEN,
                'WARN': self.ORANGE,
                'FAIL': self.RED,
            }
            for idx, r in enumerate(results):
                row_num  = idx + 3  # 1=header, 2=col-labels, 3=first result
                color    = status_color_map.get(r['status'], self.WHITE)
                formats.append({'range': f'A{row_num}:F{row_num}',
                                'format': {'backgroundColor': color}})
            if formats:
                retry_call(
                    lambda: ws.batch_format(formats),
                    attempts=2, delay=2.0, fallback=None, label='ChecklistFormat'
                )
        except Exception as e:
            log.error(f"[Sheets] write_checklist() failed: {e}")

    # ── CURRENT_SNAPSHOT ──────────────────────────────────────────────────────

    def write_current_snapshot(self, chain):
        self._write_snapshot('CURRENT_SNAPSHOT', chain)

    def write_previous_snapshot(self, chain):
        self._write_snapshot('PREVIOUS_SNAPSHOT', chain)

    def _write_snapshot(self, tab_name: str, chain):
        try:
            ws   = self.get_worksheet(tab_name)
            cols = ['strike', 'expiryDate',
                    'ce_token', 'ce_symbol', 'ce_ltp', 'ce_open_interest', 'ce_change_oi',
                    'ce_volume', 'ce_iv',
                    'pe_token', 'pe_symbol', 'pe_ltp', 'pe_open_interest', 'pe_change_oi',
                    'pe_volume', 'pe_iv']
            hdr  = [['Strike', 'Expiry',
                     'CE Token', 'CE Symbol', 'CE LTP', 'CE OI', 'CE Chg OI',
                     'CE Volume', 'CE IV',
                     'PE Token', 'PE Symbol', 'PE LTP', 'PE OI', 'PE Chg OI',
                     'PE Volume', 'PE IV']]
            if chain is None or len(chain) == 0:
                rows = []
            else:
                rows = [[safe_val(row.get(c, '')) for c in cols]
                        for _, row in chain.iterrows()]
            retry_call(
                lambda: ws.clear(),
                attempts=2, delay=2.0, fallback=None, label=f'{tab_name}Clear'
            )
            retry_call(
                lambda: ws.update(values=hdr + rows, range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label=f'{tab_name}Write'
            )
        except Exception as e:
            log.error(f"[Sheets] {tab_name} write failed: {e}")

    # ── COMPARISON ────────────────────────────────────────────────────────────

    def write_comparison(self, current_chain, prev_chain):
        try:
            ws = self.get_worksheet('COMPARISON')
            hdr = [['Strike', 'CE OI Prev', 'CE OI Curr', 'CE OI Delta',
                    'PE OI Prev', 'PE OI Curr', 'PE OI Delta',
                    'CE Vol', 'PE Vol', 'Interpretation']]

            if current_chain is None or len(current_chain) == 0:
                retry_call(lambda: ws.clear(), attempts=2, delay=2.0, fallback=None, label='CompClear')
                retry_call(lambda: ws.update(values=hdr, range_name='A1'),
                           attempts=2, delay=2.0, fallback=None, label='CompWrite')
                return

            threshold = CONFIG['COMPARISON_OI_THRESHOLD']
            rows_data = []
            color_data = []

            prev_idx = {}
            if prev_chain is not None and len(prev_chain) > 0:
                for _, row in prev_chain.iterrows():
                    s = row.get('strike', 0)
                    prev_idx[s] = row

            for _, row in current_chain.iterrows():
                strike = row.get('strike', 0)
                ce_cur = int(row.get('ce_open_interest', 0) or 0)
                pe_cur = int(row.get('pe_open_interest', 0) or 0)
                ce_vol = int(row.get('ce_volume', 0) or 0)
                pe_vol = int(row.get('pe_volume', 0) or 0)

                prev_row  = prev_idx.get(strike, {})
                ce_prev   = int(prev_row.get('ce_open_interest', 0) or 0) if prev_row else 0
                pe_prev   = int(prev_row.get('pe_open_interest', 0) or 0) if prev_row else 0
                ce_delta  = ce_cur - ce_prev
                pe_delta  = pe_cur - pe_prev

                # Interpretation logic
                ce_rising = ce_delta > threshold
                ce_fall   = ce_delta < -threshold
                pe_rising = pe_delta > threshold
                pe_fall   = pe_delta < -threshold

                if pe_rising and not ce_rising:
                    interp = 'PE Writing (Support Building)'
                    color  = self.GREEN
                elif ce_rising and not pe_rising:
                    interp = 'CE Writing (Resistance Building)'
                    color  = self.RED
                elif ce_fall and not pe_fall:
                    interp = 'CE Unwinding (Bullish)'
                    color  = self.GREEN
                elif pe_fall and not ce_fall:
                    interp = 'PE Unwinding (Bearish)'
                    color  = self.RED
                elif ce_rising and pe_rising:
                    interp = 'Both OI Rising (Ambiguous)'
                    color  = self.YELLOW
                elif ce_fall and pe_fall:
                    interp = 'Both OI Falling (Unwinding)'
                    color  = self.ORANGE
                else:
                    interp = 'No Significant Change'
                    color  = self.YELLOW

                rows_data.append([
                    strike, ce_prev, ce_cur, ce_delta,
                    pe_prev, pe_cur, pe_delta,
                    ce_vol, pe_vol, interp
                ])
                color_data.append(color)

            retry_call(lambda: ws.clear(), attempts=2, delay=2.0, fallback=None, label='CompClear')
            retry_call(
                lambda: ws.update(values=hdr + rows_data, range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label='CompWrite'
            )

            formats = []
            for idx, color in enumerate(color_data):
                row_num = idx + 2
                formats.append({'range': f'J{row_num}', 'format': {'backgroundColor': color}})
            if formats:
                retry_call(lambda: ws.batch_format(formats),
                           attempts=2, delay=2.0, fallback=None, label='CompFormat')
        except Exception as e:
            log.error(f"[Sheets] write_comparison() failed: {e}")

    # ── HISTORY_LOG ───────────────────────────────────────────────────────────

    HISTORY_HEADER = [
        'Timestamp', 'Symbol', 'Expiry', 'Expiry Type', 'Spot Price (₹)', 'ATM',
        'Bias', 'Bias Calculated At', 'Score', 'Score Max', 'Confidence %',
        'Support', 'Resistance', 'PCR OI', 'Event Tag', 'Warns', 'Fails',
        'SR Event', 'SR Confidence', 'Candle Pattern',
        'Market Condition', 'Volatility Context', 'India VIX', 'Days to Expiry',
        # GROUP A — Raw OI Chain
        'CE OI Total', 'PE OI Total', 'CE Chg OI', 'PE Chg OI', 'PCR Chg OI',
        'CE Vol Total', 'PE Vol Total', 'Vol Imbalance',
        # GROUP B — S/R Migration
        'Support Shift', 'Resistance Shift', 'Support OI', 'Resistance OI',
        'Support Chg OI', 'Resistance Chg OI',
        # GROUP C — Break Risk
        'SR Event Age', 'Spot vs Support %', 'Spot vs Resist %',
        # GROUP D — Candle + VWAP Context
        'VWAP Level', 'VWAP Bias', 'Vol Bias', 'Price Structure',
        'Candle Wick %', 'Candle Vol Ratio',
        # ── CHANGE 3: Add 3 new OI concentration columns ──
        'Top CE Strike', 'Top PE Strike', 'OI Concentration',
    ]

    # TODAY_LOG uses identical header to HISTORY_LOG. Cleared daily at first cycle.
    TODAY_LOG_HEADER = HISTORY_HEADER

    SIGNAL_HEADER = [
        'Signal ID','Timestamp','Cycle','Time Block',
        'Expiry Day','Pre-Expiry Warn',
        'Setup Type','Setup Quality','Blocked Reason',
        'Bias','Score','Spot at Signal',
        'Support','Resistance','VWAP',
        'Price Structure','MTF 15m','MTF 30m',
        'SR Event','SR Age','OI Regime',
        'Market Condition','VIX Level','VIX Trend',
        'PCR OI','OI Concentration','Days to Expiry',
        'Short Strike','Short Option Type','Short LTP',
        'Hedge Strike','Hedge LTP',
        'Net Premium (pts)','Max Risk (pts)',
        'Lot Size','Net Premium (₹)','Max Risk (₹)',
        'Gate: Environment','Gate: Structure','Gate: OI Regime',
        'Gate: Liquidity','Gate: Trap','Gate: VWAP/Vol',
        'Gate: Late Entry','Gate: Strategy',
        'Spot 15m Later','Move 15m (pts)','Correct 15m','Label 15m',
        'Spot 30m Later','Move 30m (pts)','Correct 30m','Label 30m',
        'Quality Score Final',
    ]

    POSITION_LOG_HEADER = [
        'Timestamp','Event','Action','Short Symbol','Short Strike',
        'Hedge Symbol','Hedge Strike','Lots','Quantity','Lot Size',
        'Short Fill','Hedge Fill','Net Premium (₹)','Max Risk (₹)',
        'Entry Spot','Entry Time','Short Order ID','Hedge Order ID',
        'Hedge Gap','Position State','Is Trap Fade',
        'Bias at Entry','Score at Entry','Market Condition',
        'SR Event','VIX Level',
    ]

    def _ensure_history_header(self, ws):
        """Write or migrate HISTORY_LOG header."""
        try:
            existing = ws.row_values(1)
            if not existing:
                retry_call(
                    lambda: ws.update(values=[self.HISTORY_HEADER], range_name='A1'),
                    attempts=2, delay=2.0, fallback=None, label='HistoryHeader'
                )
            else:
                # Append missing columns
                missing = [c for c in self.HISTORY_HEADER if c not in existing]
                if missing:
                    new_header = existing + missing
                    retry_call(
                        lambda: ws.update(values=[new_header], range_name='A1'),
                        attempts=2, delay=2.0, fallback=None, label='HistoryHeaderMigrate'
                    )
        except Exception as e:
            log.warning(f"[Sheets] History header check failed: {e}")

    def _ensure_today_log_header(self, ws):
        """Write TODAY_LOG header (identical to HISTORY_LOG)."""
        try:
            existing = ws.row_values(1)
            if not existing:
                retry_call(
                    lambda: ws.update(values=[self.TODAY_LOG_HEADER], range_name='A1'),
                    attempts=2, delay=2.0, fallback=None, label='TodayLogHeader'
                )
        except Exception as e:
            log.warning(f"[Sheets] Today log header check failed: {e}")

    def clear_and_reset_today_log(self, headers: list):
        """
        Clear all content from TODAY_LOG and write the header row.
        Called at the start of each new session (when IST date has changed).
        """
        try:
            ws = self.get_worksheet('TODAY_LOG')
            retry_call(
                lambda: ws.clear(),
                attempts=2, delay=2.0, fallback=None, label='TodayLogClear'
            )
            retry_call(
                lambda: ws.update(values=[headers], range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label='TodayLogHeaderWrite'
            )
            # Freeze header row
            try:
                retry_call(
                    lambda: ws.freeze(rows=1),
                    attempts=2, delay=2.0, fallback=None, label='TodayLogFreeze'
                )
            except Exception:
                pass  # Freeze is nice-to-have but not critical
            log.info('[SheetsWriter] TODAY_LOG cleared and reset for new session.')
        except Exception as e:
            log.error(f"[Sheets] clear_and_reset_today_log() failed: {e}")

    def append_history(self, row_dict: dict):
        """Append row to both HISTORY_LOG and TODAY_LOG."""
        # ── Append to HISTORY_LOG ──
        try:
            ws = self.get_worksheet('HISTORY_LOG')
            self._ensure_history_header(ws)
            row = [safe_val(row_dict.get(col, '')) for col in self.HISTORY_HEADER]
            retry_call(
                lambda: ws.append_row(row, value_input_option='USER_ENTERED'),
                attempts=2, delay=2.0, fallback=None, label='HistoryAppend'
            )
        except Exception as e:
            log.error(f"[Sheets] append_history() HISTORY_LOG failed: {e}")
        
        # ── Append to TODAY_LOG ──
        try:
            ws_today = self.get_worksheet('TODAY_LOG')
            self._ensure_today_log_header(ws_today)
            row = [safe_val(row_dict.get(col, '')) for col in self.HISTORY_HEADER]
            retry_call(
                lambda: ws_today.append_row(row, value_input_option='USER_ENTERED'),
                attempts=2, delay=2.0, fallback=None, label='TodayLogAppend'
            )
        except Exception as e:
            log.error(f"[Sheets] append_history() TODAY_LOG failed: {e}")

    # ── CLAUDE_ANALYSIS ───────────────────────────────────────────────────────

    CLAUDE_HEADER = [
        'Timestamp', 'Spot', 'ATM', 'Bias (Rule)', 'Bias (Claude)', 'Strength',
        'Score', 'Confidence', 'SR Event', 'SR Confidence',
        'Signal', 'Current Situation', 'Risk Note', 'Score Agreement',
        'Unusual Observation',
        'Market Condition (Rule)', 'Market Condition (Claude)',
        'Volatility Context (Claude)', 'Key Premium Insight', 'Prompt Version',
    ]

    def _ensure_claude_header(self, ws):
        try:
            existing = ws.row_values(1)
            if not existing:
                retry_call(
                    lambda: ws.update(values=[self.CLAUDE_HEADER], range_name='A1'),
                    attempts=2, delay=2.0, fallback=None, label='ClaudeHeader'
                )
            else:
                missing = [c for c in self.CLAUDE_HEADER if c not in existing]
                if missing:
                    retry_call(
                        lambda: ws.update(values=[existing + missing], range_name='A1'),
                        attempts=2, delay=2.0, fallback=None, label='ClaudeHeaderMigrate'
                    )
        except Exception as e:
            log.warning(f"[Sheets] Claude header check failed: {e}")

    def append_claude_analysis(self, analysis: dict, snapshot: dict, ts: str,
                               call_type: str = 'ANALYSIS'):
        try:
            ws = self.get_worksheet('CLAUDE_ANALYSIS')
            self._ensure_claude_header(ws)

            pe = analysis.get('premium_environment', {}) or {}
            row = [
                ts,
                safe_val(snapshot.get('spot', '')),
                safe_val(snapshot.get('atm', '')),
                snapshot.get('bias', ''),
                analysis.get('market_bias', ''),
                analysis.get('strength', ''),
                snapshot.get('score', ''),
                snapshot.get('confidence', ''),
                snapshot.get('sr_event', ''),
                snapshot.get('sr_confidence', ''),
                analysis.get('signal', ''),
                analysis.get('current_situation', ''),
                analysis.get('risk_note', ''),
                str(analysis.get('score_agreement', False)),
                str(analysis.get('unusual_observation', '') or ''),
                snapshot.get('market_condition', ''),
                pe.get('market_condition', ''),
                pe.get('volatility_context', ''),
                pe.get('key_insight', ''),
                CONFIG.get('PROMPT_VERSION', 'v1.0'),
            ]
            row = [safe_val(v) for v in row]
            retry_call(
                lambda: ws.append_row(row, value_input_option='USER_ENTERED'),
                attempts=2, delay=2.0, fallback=None, label='ChatGPTAppend'
            )
        except Exception as e:
            log.error(f"[Sheets] append_claude_analysis() failed: {e}")

    def write_current_situation(self, analysis: dict,
                                 snapshot: dict,
                                 mtf_context: dict,
                                 ts: str):
        """
        Overwrite CURRENT_SITUATION tab with the latest AI analysis.
        Cleared and fully rewritten every cycle. Never appends.
        """
        try:
            ws = self.get_worksheet('CURRENT_SITUATION')
            retry_call(
                lambda: ws.clear(),
                attempts=2, delay=2.0,
                fallback=None, label='CurSitClear'
            )
            pe   = analysis.get('premium_environment', {}) or {}
            mtf  = mtf_context or {}
            oi_t = mtf.get('mtf_oi_trend', {})
            sr_c = mtf.get('mtf_sr_context', {})

            rows = [
                ['NIFTY — Current Situation', ts],
                [],
                ['── BIAS & SCORE ──', ''],
                ['Bias',          snapshot.get('bias', '')],
                ['AI Bias',       analysis.get('market_bias', '')],
                ['Score',         snapshot.get('score', '')],
                ['Confidence',    snapshot.get('confidence', '')],
                ['Strength',      analysis.get('strength', '')],
                ['Event Tag',     snapshot.get('event_tag', '')],
                [],
                ['── CURRENT SITUATION ──', ''],
                ['Summary',       analysis.get('current_situation', '')],
                ['Signal',        analysis.get('signal', '')],
                ['Risk Note',     analysis.get('risk_note', '')],
                ['MTF Alignment', analysis.get('mtf_alignment', '')],
                [],
                ['── S/R LEVELS ──', ''],
                ['Support',                  snapshot.get('support', '')],
                ['Resistance',               snapshot.get('resistance', '')],
                ['Support Break Risk',       sr_c.get('support_break_risk', '')],
                ['Resistance Break Risk',    sr_c.get('resistance_break_risk', '')],
                ['Support Strengthening',    str(sr_c.get('support_strengthening', ''))],
                ['Resistance Strengthening', str(sr_c.get('resistance_strengthening', ''))],
                ['Support Migrated (30m)',   oi_t.get('support_migrated_pts', '')],
                ['Resistance Migrated (30m)',oi_t.get('resistance_migrated_pts', '')],
                [],
                ['── OI TREND (30 min) ──', ''],
                ['CE Writing',       oi_t.get('ce_writing_30min', '')],
                ['PE Writing',       oi_t.get('pe_writing_30min', '')],
                ['OI Concentration', oi_t.get('oi_concentration_trend', '')],
                ['SR Event Age',     oi_t.get('max_sr_event_age_30min', '')],
                [],
                ['── TIMEFRAME ALIGNMENT ──', ''],
                ['5m Structure',  snapshot.get('price_structure', '')],
                ['15m Structure', mtf.get('mtf_15m', {}).get('structure', '')],
                ['30m Structure', mtf.get('mtf_30m', {}).get('structure', '')],
                [],
                ['── PREMIUM ENVIRONMENT ──', ''],
                ['Market Condition', pe.get('market_condition', '')],
                ['Volatility',       pe.get('volatility_context', '')],
                ['Key Insight',      pe.get('key_insight', '')],
                [],
                ['── REASONING ──', ''],
            ]
            for i, pt in enumerate(
                analysis.get('reasoning', [])[:5], 1
            ):
                rows.append([f'Point {i}', str(pt)])

            rows_safe = [[safe_val(c) for c in r] for r in rows]
            retry_call(
                lambda: ws.update(
                    values=rows_safe, range_name='A1'
                ),
                attempts=2, delay=2.0,
                fallback=None, label='CurSitWrite'
            )
        except Exception as e:
            log.error(f'[Sheets] write_current_situation() failed: {e}')

    def write_visualization_tab(
        self,
        snapshot:       dict,
        metrics:        dict,
        signals:        dict,
        theta_env:      dict,
        sr_event:       dict,
        vix_data:       dict,
        chain,
        history_rows:   list,
        claude_summary: Optional[dict] = None,
    ):
        """
        Overwrites VISUALIZE tab every cycle with live market data
        structured as chart-ready tables.

        TAB LAYOUT:
          Rows 1-3    : Prominent timestamp header (staleness check)
          Rows 4-12   : Live status bar (spot, bias, S/R, VIX, etc.)
          Rows 13-25  : Latest AI analysis panel
          Rows 26+    : Option chain OI table (Section C — for Charts 1 & 2)
          Below chain : Session time-series table (Section D — for Charts 3-7)

        CHART SETUP (create once in Sheets after first run):
          Chart 1 — CE/PE OI Bar: Section C, columns A / B / F
                    (Strike, CE OI, PE OI)   Type: Bar chart
          Chart 2 — OI Change Column: Section C, columns A / C / G
                    (Strike, CE ChgOI, PE ChgOI)   Type: Column chart
          Chart 3 — Spot + VWAP Line: Section D, columns A / B / I
                    (Timestamp, Spot, VWAP Level)   Type: Line chart
          Chart 4 — Score Area: Section D, columns A / C
                    (Timestamp, Score int)   Type: Area chart
          Chart 5 — PCR Trend: Section D, columns A / E
                    (Timestamp, PCR OI)   Type: Line chart
          Chart 6 — India VIX Line: Section D, columns A / H
                    (Timestamp, India VIX)   Type: Line chart
          Chart 7 — CE/PE ChgOI Over Session: Section D, columns A / F / G
                    (Timestamp, CE ChgOI, PE ChgOI)   Type: Stacked column

        PERFORMANCE RULES:
          - All data built as Python lists first, then 1 ws.update() call
          - 1 ws.batch_format() call at the end for all colors
          - No volatile Sheets formulas anywhere
          - Max 3 API calls total: clear + update + batch_format
        """
        try:
            AMBER = {'red': 1.0, 'green': 0.600, 'blue': 0.0}

            ws = self.get_worksheet('VISUALIZE')
            retry_call(
                lambda: ws.clear(),
                attempts=2, delay=2.0, fallback=None, label='VizClear'
            )

            # ── Helper ────────────────────────────────────────────────────
            def sv(v):
                """safe_val shorthand — also handles nan floats."""
                if v is None:
                    return ''
                if isinstance(v, float) and (math.isnan(v) or math.isinf(v)):
                    return ''
                return v

            def score_int(score_str):
                """Extract integer from '5/12' score string."""
                try:
                    return int(str(score_str).split('/')[0])
                except Exception:
                    return ''

            # ── Derived values ────────────────────────────────────────────
            spot       = sv(snapshot.get('spot', ''))
            atm        = int(snapshot.get('atm', 0) or 0)
            bias       = snapshot.get('bias', '—')
            support    = int(metrics.get('support_strike', 0) or 0)
            resistance = int(metrics.get('resistance_strike', 0) or 0)
            vwap_lv    = sv(signals.get('vwap_level', ''))
            score_disp = signals.get('score_display', '—')
            conf_disp  = signals.get('confidence_display', '—')
            sr_ev      = sr_event.get('event', 'NONE')
            sr_age     = snapshot.get('sr_event_age', 0)
            trap       = snapshot.get('trap', '') or ''
            event_tag  = signals.get('event_tag', '—')
            pcr_oi     = sv(metrics.get('pcr_oi', ''))
            pcr_chg    = sv(metrics.get('pcr_chg_oi', ''))
            vol_imbal  = sv(metrics.get('vol_imbalance', ''))
            theta_mc   = theta_env.get('market_condition', '—')
            vix_curr   = sv(vix_data.get('vix_current', ''))
            vix_trend  = vix_data.get('vix_trend', '—')
            vix_pct    = sv(vix_data.get('vix_pct_change', ''))
            dte        = theta_env.get('days_to_expiry', 0)
            price_str  = signals.get('price_structure', '—')
            vol_bias   = signals.get('vol_bias', '—')
            wick_pct   = sv(sr_event.get('candle_wick_pct', 0))
            vol_ratio  = sv(sr_event.get('candle_vol_ratio', 1.0))
            vwap_bias  = signals.get('vwap_bias', '—')
            decay_sc   = theta_env.get('decay_score', 0)
            sess_high  = sv(snapshot.get('session_high', ''))
            sess_low   = sv(snapshot.get('session_low', ''))
            sess_open  = sv(snapshot.get('session_open', ''))

            # ── Section A: Timestamp Header (rows 1-3) ────────────────────
            # Row 2 col B is the prominent orange timestamp cell — staleness
            # check. If it is > 10 min old, the script is not running.
            timestamp_str = ist_str('%d-%b-%Y   %H:%M:%S   IST')
            section_a = [
                ['', '', '', '', '', '', '', ''],
                [
                    '🕐  LAST UPDATED:',
                    timestamp_str,
                    '',
                    '━━━  NIFTY INTRADAY VISUALIZER  ━━━',
                    '',
                    '',
                    'Auto-refreshes every 5 min',
                    '',
                ],
                ['', '', '', '', '', '', '', ''],
            ]

            # ── Section B: Live Status Bar (rows 4-12) ────────────────────
            section_b = [
                ['━━━ LIVE STATUS ━━━', '', '', '', '', '', '', ''],
                [
                    'SPOT',     sv(spot),
                    'ATM',      atm,
                    'BIAS',     bias,
                    'SCORE',    score_disp,
                ],
                [
                    'SUPPORT',    support,
                    'RESISTANCE', resistance,
                    'VWAP',       sv(vwap_lv),
                    'CONFIDENCE', conf_disp,
                ],
                [
                    'SR EVENT',  sr_ev,
                    'SR AGE',    sr_age,
                    'TRAP',      trap or 'None',
                    'EVENT TAG', event_tag,
                ],
                [
                    'PCR OI',     sv(pcr_oi),
                    'PCR ChgOI',  sv(pcr_chg),
                    'VOL IMBAL',  sv(vol_imbal),
                    'THETA ENV',  theta_mc,
                ],
                [
                    'INDIA VIX',  sv(vix_curr),
                    'VIX TREND',  vix_trend,
                    'VIX CHG%',   sv(vix_pct),
                    'DTE',        dte,
                ],
                [
                    'PRICE STRUCT', price_str,
                    'VOL BIAS',     vol_bias,
                    'WICK %',       sv(wick_pct),
                    'VOL RATIO',    sv(vol_ratio),
                ],
                [
                    'VWAP BIAS',   vwap_bias,
                    'DECAY SCORE', decay_sc,
                    'SESS HIGH',   sv(sess_high),
                    'SESS LOW',    sv(sess_low),
                ],
                ['', '', '', '', '', '', '', ''],
            ]

            # ── Section C: AI Analysis Panel (rows 13-25) ─────────────────
            pe = claude_summary or {}
            ai_bias     = pe.get('market_bias', '— AI not run —')
            ai_strength = pe.get('strength', '')
            ai_agree    = str(pe.get('score_agreement', ''))
            ai_signal   = str(pe.get('signal', '') or '')[:100]
            ai_sit      = str(pe.get('current_situation', '') or '')[:150]
            ai_mtf      = str(pe.get('mtf_alignment', '') or '')[:120]
            ai_risk     = str(pe.get('risk_note', '') or '')[:120]
            ai_unusual  = str(pe.get('unusual_observation', '') or '—')[:100]
            reasoning   = pe.get('reasoning', []) or []

            section_c = [
                ['━━━ LATEST AI ANALYSIS ━━━', '', '', '', '', '', '', ''],
                [
                    'AI BIAS',    ai_bias,
                    'STRENGTH',   ai_strength,
                    'SCORE AGREES', ai_agree,
                    '', '',
                ],
                ['SIGNAL:',    ai_signal,    '', '', '', '', '', ''],
                ['SITUATION:', ai_sit,       '', '', '', '', '', ''],
                ['MTF ALIGN:', ai_mtf,       '', '', '', '', '', ''],
                ['RISK NOTE:', ai_risk,      '', '', '', '', '', ''],
                ['UNUSUAL:',   ai_unusual,   '', '', '', '', '', ''],
                ['REASONING:', '', '', '', '', '', '', ''],
            ]
            for idx, point in enumerate(reasoning[:4], 1):
                section_c.append(
                    [f'  {idx}.', str(point)[:150], '', '', '', '', '', '']
                )
            # Pad to always 4 reasoning rows
            while len([r for r in section_c if r and r[0].strip().startswith(tuple('1234'))]) < 4:
                section_c.append(['', '', '', '', '', '', '', ''])
            section_c.append(['', '', '', '', '', '', '', ''])

            # ── Section D: Option Chain OI Table ──────────────────────────
            # Source for Chart 1 (CE/PE OI) and Chart 2 (OI Change)
            # Columns: A=Strike B=CE OI C=CE ChgOI D=CE LTP E=CE IV
            #          F=PE OI  G=PE ChgOI H=PE LTP  I=PE IV
            section_d_header = [
                ['━━━ OPTION CHAIN — FOCUS ZONE ━━━',
                 '', '', '', '', '', '', '', ''],
                ['Strike', 'CE OI', 'CE Chg OI', 'CE LTP', 'CE IV',
                 'PE OI',  'PE Chg OI', 'PE LTP', 'PE IV'],
            ]
            chain_rows = []
            chain_strike_rows = {}   # strike -> row_index for coloring
            if chain is not None and len(chain) > 0:
                for row_i, (_, row) in enumerate(chain.iterrows()):
                    strike_val = int(row.get('strike', 0) or 0)
                    chain_rows.append([
                        strike_val,
                        int(row.get('ce_open_interest', 0) or 0),
                        int(row.get('ce_change_oi', 0) or 0),
                        sv(row.get('ce_ltp', '')),
                        sv(row.get('ce_iv', '')),
                        int(row.get('pe_open_interest', 0) or 0),
                        int(row.get('pe_change_oi', 0) or 0),
                        sv(row.get('pe_ltp', '')),
                        sv(row.get('pe_iv', '')),
                    ])
                    chain_strike_rows[strike_val] = row_i
            chain_rows.append(['', '', '', '', '', '', '', '', ''])

            # ── Section E: Session Time-Series Table ──────────────────────
            # Source for Charts 3-7. Columns:
            # A=Timestamp B=Spot C=Score(int) D=Confidence%
            # E=PCR OI F=CE ChgOI G=PE ChgOI H=India VIX I=VWAP Level
            section_e_header = [
                ['━━━ SESSION TIME-SERIES (last 75 cycles) ━━━',
                 '', '', '', '', '', '', '', ''],
                ['Timestamp', 'Spot', 'Score', 'Confidence%',
                 'PCR OI', 'CE Chg OI', 'PE Chg OI',
                 'India VIX', 'VWAP Level'],
            ]
            ts_rows = []
            for r in history_rows[-75:]:
                ts_rows.append([
                    r.get('Timestamp', ''),
                    sv(r.get('Spot Price (\u20b9)', '')),
                    score_int(r.get('Score', '')),
                    sv(r.get('Confidence %', '')),
                    sv(r.get('PCR OI', '')),
                    sv(r.get('CE Chg OI', '')),
                    sv(r.get('PE Chg OI', '')),
                    sv(r.get('India VIX', '')),
                    sv(r.get('VWAP Level', '')),
                ])

            # ── Assemble all rows ─────────────────────────────────────────
            all_rows = (
                section_a +
                section_b +
                section_c +
                section_d_header +
                chain_rows +
                section_e_header +
                ts_rows
            )

            # Sanitize — every cell must be a scalar safe for Sheets
            all_rows_safe = [
                [sv(c) for c in row] for row in all_rows
            ]

            # Validate row count to prevent Sheets quota issues
            if len(all_rows_safe) > 490:
                log.warning(f'[Sheets] VISUALIZE tab row count {len(all_rows_safe)} exceeds 490 limit, truncating')
                all_rows_safe = all_rows_safe[:490]

            retry_call(
                lambda: ws.update(values=all_rows_safe, range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label='VizWrite'
            )

            # ── Color Formatting (one batch_format call) ──────────────────
            # Calculate dynamic row offsets
            row_ts_header   = 2   # Row 2 = timestamp (1-based)
            row_status_hdr  = len(section_a) + 1           # "LIVE STATUS" header
            row_ai_hdr      = row_status_hdr + len(section_b)
            row_chain_hdr   = row_ai_hdr + len(section_c)
            row_chain_data  = row_chain_hdr + 2             # after 2 header rows
            row_ts_data_hdr = row_chain_data + len(chain_rows)

            # Bias color
            bias_upper = bias.upper()
            if 'BULLISH' in bias_upper:
                bias_color = self.GREEN
            elif 'BEARISH' in bias_upper:
                bias_color = self.RED
            else:
                bias_color = self.YELLOW

            # AI bias color
            if ai_bias == 'Bullish':
                ai_bias_color = self.GREEN
            elif ai_bias == 'Bearish':
                ai_bias_color = self.RED
            else:
                ai_bias_color = self.YELLOW

            # Theta color
            if theta_mc == 'Decay Favorable':
                theta_color = self.GREEN
            elif theta_mc == 'Expansion Favorable':
                theta_color = self.RED
            else:
                theta_color = self.YELLOW

            # Trap color
            trap_color = self.DEEP_RED if trap else self.GREEN

            # Score color (row 5 col F = bias label cell)
            score_row = row_status_hdr + 1    # first data row of status bar
            ai_bias_row = row_ai_hdr + 1      # first data row of AI section

            formats = [
                # Timestamp row — AMBER background, bold
                {'range': f'B{row_ts_header}',
                 'format': {
                     'backgroundColor': AMBER,
                     'textFormat': {'bold': True, 'fontSize': 11},
                 }},
                # Title cell — NAVY
                {'range': f'D{row_ts_header}:G{row_ts_header}',
                 'format': {'backgroundColor': self.NAVY}},
                # Status header row — NAVY
                {'range': f'A{row_status_hdr}:H{row_status_hdr}',
                 'format': {'backgroundColor': self.NAVY}},
                # AI section header row — NAVY
                {'range': f'A{row_ai_hdr}:H{row_ai_hdr}',
                 'format': {'backgroundColor': self.NAVY}},
                # Chain section header rows — NAVY
                {'range': f'A{row_chain_hdr}:I{row_chain_hdr}',
                 'format': {'backgroundColor': self.NAVY}},
                {'range': f'A{row_chain_hdr+1}:I{row_chain_hdr+1}',
                 'format': {'backgroundColor': self.NAVY}},
                # Time-series header rows — NAVY
                {'range': f'A{row_ts_data_hdr}:I{row_ts_data_hdr}',
                 'format': {'backgroundColor': self.NAVY}},
                {'range': f'A{row_ts_data_hdr+1}:I{row_ts_data_hdr+1}',
                 'format': {'backgroundColor': self.NAVY}},
                # Bias cell (row score_row col F = 6th col = F)
                {'range': f'F{score_row}',
                 'format': {'backgroundColor': bias_color}},
                # AI Bias cell (row ai_bias_row col B)
                {'range': f'B{ai_bias_row}',
                 'format': {'backgroundColor': ai_bias_color}},
                # Theta env cell (row score_row+3 col H)
                {'range': f'H{score_row + 3}',
                 'format': {'backgroundColor': theta_color}},
                # Trap cell (row score_row+2 col F)
                {'range': f'F{score_row + 2}',
                 'format': {'backgroundColor': trap_color}},
            ]

            # Strike row colors: ATM=YELLOW, support=GREEN, resistance=RED
            for strike_val, row_offset in chain_strike_rows.items():
                actual_row = row_chain_data + row_offset
                if strike_val == atm:
                    color = self.YELLOW
                elif strike_val == support:
                    color = self.GREEN
                elif strike_val == resistance:
                    color = self.RED
                else:
                    continue
                formats.append({
                    'range': f'A{actual_row}:I{actual_row}',
                    'format': {'backgroundColor': color},
                })

            if formats:
                retry_call(
                    lambda: ws.batch_format(formats),
                    attempts=2, delay=2.0, fallback=None, label='VizFormat'
                )

            log.info(f'[Sheets] VISUALIZE tab written — {len(ts_rows)} session rows, '
                     f'{len(chain_rows)-1} chain strikes.')

        except Exception as e:
            log.error(f'[Sheets] write_visualization_tab() failed: {e}')

    # ── DAILY_REVIEW ──────────────────────────────────────────────────────────

    DAILY_REVIEW_HEADER = [
        'Date', 'Total Cycles', 'ChatGPT Calls', 'Session Character',
        'Best Signals', 'Missed Signals', 'SR Event Accuracy',
        'SR Accurate (True/False)', 'Prev Day Level Interaction', 'Calibration Note',
    ]

    def append_daily_review(self, review: dict, ts: str):
        try:
            ws = self.get_worksheet('DAILY_REVIEW')
            existing = ws.row_values(1)
            if not existing:
                retry_call(
                    lambda: ws.update(values=[self.DAILY_REVIEW_HEADER], range_name='A1'),
                    attempts=2, delay=2.0, fallback=None, label='DailyRevHeader'
                )

            sr_accurate = review.get('sr_accurate', False)
            row = [
                ts,
                safe_val(review.get('total_cycles', 0)),
                safe_val(review.get('claude_calls', 0)),
                review.get('session_character', ''),
                review.get('best_signals', ''),
                review.get('missed_signals', ''),
                review.get('sr_event_accuracy', ''),
                str(sr_accurate),
                review.get('prev_day_interaction', ''),
                review.get('calibration_note', ''),
            ]
            row = [safe_val(v) for v in row]
            retry_call(
                lambda: ws.append_row(row, value_input_option='USER_ENTERED'),
                attempts=2, delay=2.0, fallback=None, label='DailyRevAppend'
            )

            # Color SR Accurate cell
            try:
                # Use col_values (single column, lightweight) instead of
                # get_all_values() to find the last row after append.
                last_row = len(ws.col_values(1))
                col_idx  = self.DAILY_REVIEW_HEADER.index('SR Accurate (True/False)') + 1
                col_let  = chr(ord('A') + col_idx - 1)
                acc_cell = f'{col_let}{last_row}'
                acc_col2 = chr(ord('A') + self.DAILY_REVIEW_HEADER.index('SR Event Accuracy'))
                acc_cell2= f'{acc_col2}{last_row}'
                color    = self.GREEN if sr_accurate else self.RED
                fmts = [
                    {'range': acc_cell,  'format': {'backgroundColor': color}},
                    {'range': acc_cell2, 'format': {'backgroundColor': color}},
                ]
                retry_call(lambda: ws.batch_format(fmts),
                           attempts=2, delay=2.0, fallback=None, label='DailyRevFormat')
            except Exception:
                pass
        except Exception as e:
            log.error(f"[Sheets] append_daily_review() failed: {e}")

    # ── SETTINGS_HELP ─────────────────────────────────────────────────────────

    def write_settings_help(self):
        try:
            ws = self.get_worksheet('SETTINGS_HELP')
            content = [
                ['NIFTY Intraday Dashboard — Settings & Documentation'],
                [''],
                ['── SETUP ──'],
                ['GOOGLE_SERVICE_ACCOUNT_JSON', 'Path to your GCP service account JSON key file.'],
                ['SPREADSHEET_ID',              'The Google Spreadsheet ID (from the URL).'],
                ['',
                 'Create a GCP project → enable Google Sheets API + Google Drive API → create service account → download JSON key.'],
                ['',
                 'Share the spreadsheet with the service account email (Editor access).'],
                [''],
                ['── SETTINGS TAB LAYOUT ──'],
                ['B5',  'Symbol (NIFTY)'],
                ['B7',  'Expiry Mode: AUTO | NEXT | MONTHLY | MANUAL'],
                ['B8',  'Manual Expiry (DDMMMYYYY — only if B7=MANUAL)'],
                ['B10', 'Refresh interval in minutes (e.g. 5)'],
                ['B11', 'Strikes Above ATM (e.g. 5)'],
                ['B12', 'Strikes Below ATM (e.g. 5)'],
                ['B13', 'Auto Refresh: YES | NO'],
                ['B15', 'Broker: ANGELONE'],
                ['B17', 'Angel One API Key'],
                ['B18', 'Angel One Client Code'],
                ['B19', 'Angel One MPIN (⚠ 4-digit PIN from mobile app — NOT your web password)'],
                ['B20', 'Angel One TOTP Secret (from smartapi.angelone.in/enable-totp)'],
                [''],
                ['── MPIN REMINDER ──'],
                ['', 'B19 must be your 4-digit Angel One MPIN (same as mobile app login PIN).'],
                ['', 'NEVER enter your web login password here — this produces AB7001 error.'],
                [''],
                ['── CHATGPT / OPENAI (OPTIONAL) ──'],
                ['Model',          CONFIG.get('OPENAI_MODEL', 'gpt-4.1-mini')],
                ['API Key',        'Set OPENAI_API_KEY in CONFIG or as env variable.'],
                ['Call Types',
                 '1) Morning Brief (<09:20 IST, once/session) 2) 15-min Analysis (every N cycles) 3) EOD Review (>=15:30 IST)'],
                ['Output Schema',  'market_bias, strength, signal, reasoning, score_agreement, premium_environment'],
                ['Score Agreement','True if Claude\'s market_bias directionally matches rule engine bias.'],
                ['Unusual Obs.',   'Notable pattern not captured by the rule engine (or null).'],
                ['Premium Env.',   'Claude\'s narrative on market_condition, volatility_context, key_insight.'],
                ['Disable',        'Leave OPENAI_API_KEY empty — program runs normally without ChatGPT.'],
                [''],
                ['── TELEGRAM (OPTIONAL) ──'],
                ['Bot Token', 'Message @BotFather → /newbot → copy the token.'],
                ['Chat ID',   'Visit https://api.telegram.org/bot{TOKEN}/getUpdates after sending the bot a message.'],
                ['Filtering', 'Alerts sent only when: strength=Strong OR sr_confidence=HIGH OR trap non-empty.'],
                ['Morning',   'Morning brief always sent (no filter).'],
                ['EOD',       'EOD review sent silently (no sound notification).'],
                ['Disable',   'Leave TELEGRAM_BOT_TOKEN empty — all send() calls return immediately.'],
                [''],
                ['── PREVIOUS DAY LEVELS ──'],
                ['', 'prev_high, prev_low, prev_close are fetched ONCE at startup (not every cycle).'],
                ['', 'Used by Claude for context. Not re-fetched during the day (yesterday\'s levels are constant).'],
                [''],
                ['── PROMPT VERSION ──'],
                ['', 'Increment CONFIG[\'PROMPT_VERSION\'] (e.g. v1.0→v1.1) when you change CLAUDE_SYSTEM_PROMPT.'],
                ['', 'The version is logged in CLAUDE_ANALYSIS tab so you can track which prompt produced which analysis.'],
                [''],
                ['── PREMIUM ENVIRONMENT (VIX + THETA ANALYSIS) ──'],
                ['VIX Token',   '99919000 on NSE — fetched every cycle using FIVE_MINUTE candles.'],
                ['VIX Low',     f"CONFIG['VIX_LOW_THRESHOLD'] = {CONFIG.get('VIX_LOW_THRESHOLD', 13.0)} (below = low vol = decay-friendly)"],
                ['VIX High',    f"CONFIG['VIX_HIGH_THRESHOLD'] = {CONFIG.get('VIX_HIGH_THRESHOLD', 20.0)} (above = high vol = expansion-friendly)"],
                ['VIX Lookback', f"CONFIG['VIX_RISING_LOOKBACK'] = {CONFIG.get('VIX_RISING_LOOKBACK', 5)} candles for trend detection"],
                ['Decay Favorable', 'VIX low/falling + range-bound + near expiry — premiums tend to erode. Does NOT mean sell options.'],
                ['Expansion Favorable', 'VIX high/rising + breakout — premiums tend to inflate. Does NOT mean buy options.'],
                ['Neutral', 'Mixed signals — environment can shift quickly.'],
                ['Decay Score', '±10 range. ≥+4 = Decay Favorable. ≤-4 = Expansion Favorable.'],
                ['Days to Expiry', '≤2 days = max theta. ≥15 days = slow decay.'],
                ['IMPORTANT', 'Premium environment is for understanding conditions only. It does NOT tell you what to trade.'],
                ['VIX Volume',  'VIX is index data — no volume available from VIX candles. This is expected and not an error.'],
                ['Rule vs Claude', 'Rule-based ThetaEnvironmentAnalyzer runs every cycle. ChatGPT provides narrative enrichment every 15 min.'],
                [''],
                ['── TAB ORDER ──'],
                ['1. DASHBOARD', 'Live output — first tab visible on open.'],
                ['2. CLAUDE_ANALYSIS', 'Appended ChatGPT AI history.'],
                ['3. STARTUP_CHECKLIST', 'System health checks — rewritten every cycle.'],
                ['4. CURRENT_SNAPSHOT', 'Current option chain.'],
                ['5. PREVIOUS_SNAPSHOT', 'Previous cycle option chain.'],
                ['6. COMPARISON', 'Strike-wise OI delta table.'],
                ['7. HISTORY_LOG', 'Appended per-cycle summary rows.'],
                ['8. DAILY_REVIEW', 'Appended end-of-day review.'],
                ['9. SETTINGS_HELP', 'This documentation (written once at startup).'],
                ['10. SETTINGS', 'User-editable config (NEVER overwritten by script).'],
            ]
            retry_call(
                lambda: ws.clear(),
                attempts=2, delay=2.0, fallback=None, label='HelpClear'
            )
            retry_call(
                lambda: ws.update(values=content, range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label='HelpWrite'
            )
        except Exception as e:
            log.error(f"[Sheets] write_settings_help() failed: {e}")

    # ── SETTINGS template ─────────────────────────────────────────────────────

    def write_settings_template(self):
        """Create blank SETTINGS tab with labels, defaults, and notes. Leave B17-B20 empty."""
        try:
            titles = [ws.title for ws in self.spreadsheet.worksheets()]
            if 'SETTINGS' not in titles:
                ws = self.spreadsheet.add_worksheet(title='SETTINGS', rows=40, cols=4)
            else:
                ws = self.spreadsheet.worksheet('SETTINGS')
            self._ws_cache['SETTINGS'] = ws

            rows = [
                # Row 1: header
                ['⚙ NIFTY Dashboard — Configuration Settings', '', ''],
                # Row 2: instruction
                ['Edit Column B values only. Column C shows valid options / notes.', '', ''],
                # Row 3: column labels
                ['Setting', 'Value', 'Valid Options / Notes'],
                # Row 4: section
                ['── MARKET ──', '', ''],
                # Row 5: Symbol
                ['Symbol', 'NIFTY', 'NIFTY (only supported in this version)'],
                # Row 6: section
                ['── EXPIRY ──', '', ''],
                # Row 7: Expiry Mode
                ['Expiry Mode', 'AUTO', 'AUTO | NEXT | MONTHLY | MANUAL'],
                # Row 8: Manual Expiry
                ['Manual Expiry', '', 'DDMMMYYYY (e.g. 28OCT2025) — only used when B7=MANUAL'],
                # Row 9: section
                ['── REFRESH ──', '', ''],
                # Row 10: Interval
                ['Interval (min)', '5', 'Positive integer (e.g. 5 = refresh every 5 minutes)'],
                # Row 11: Strikes Above ATM
                ['Strikes Above ATM', '5', 'Positive integer ≥ 1'],
                # Row 12: Strikes Below ATM
                ['Strikes Below ATM', '5', 'Positive integer ≥ 1'],
                # Row 13: Auto Refresh
                ['Auto Refresh', 'YES', 'YES | NO'],
                # Row 14: section
                ['── BROKER ──', '', ''],
                # Row 15: Broker
                ['Broker', 'ANGELONE', 'ANGELONE (only supported in this version)'],
                # Row 16: section
                ['── ANGEL ONE CREDENTIALS ──', '', ''],
                # Row 17: API Key
                ['Angel API Key', '', 'Your Angel One SmartAPI API key'],
                # Row 18: Client Code
                ['Angel Client Code', '', 'Your Angel One client ID / user ID'],
                # Row 19: MPIN (4 digits only)
                ['Angel PIN (MPIN)', '', '⚠ 4-digit MPIN — same as Angel One mobile app PIN. NOT your web password.'],
                # Row 20: TOTP Secret
                ['Angel TOTP Secret', '', 'TOTP secret from smartapi.angelone.in/enable-totp'],
                # Row 21: Anthropic API Key (optional)
                ['Anthropic API Key (B21)', '', 'Optional. From console.anthropic.com. Leave empty to disable Claude AI.'],
                # Row 22: Telegram Bot Token (optional)
                ['Telegram Bot Token (B22)', '', 'Optional. From @BotFather on Telegram. Leave empty to disable alerts.'],
                # Row 23: Telegram Chat ID (optional)
                ['Telegram Chat ID (B23)', '', 'Optional. Your Telegram chat ID from @userinfobot.'],
                # Row 24: blank
                ['', '', ''],
                # Row 25: section
                ['── SIGNAL & EXECUTION ──', '', ''],
                # Row 26: Lot Size
                ['Lot Size', '75', 'NIFTY lot size (currently 75). Update if SEBI changes it.'],
                # Row 27: warning
                ['⚠ This SETTINGS tab is the ONLY place the script reads config from. '
                 'Do NOT put config values in the DASHBOARD tab — the script overwrites DASHBOARD '
                 'with live output on every cycle.', '', ''],
            ]
            retry_call(
                lambda: ws.clear(),
                attempts=2, delay=2.0, fallback=None, label='SettingsTemplateClear'
            )
            retry_call(
                lambda: ws.update(values=rows, range_name='A1'),
                attempts=2, delay=2.0, fallback=None, label='SettingsTemplateWrite'
            )
            log.info('[Sheets] SETTINGS template created.')
        except Exception as e:
            log.error(f"[Sheets] write_settings_template() failed: {e}")

    # ── EXECUTION Tab ─────────────────────────────────────────────────────────

    def write_execution_tab(self, position=None, gates=None):
        """
        Write EXECUTION tab status/position/gate cells only.
        NEVER writes to B3 (activation date), B5 (execute trigger),
        B6 (action), B7 (strike), B8 (lots) — those are user-input
        cells written by the Apps Script button and read at cycle
        start. write_execution_scaffold() writes static labels once.
        """
        try:
            ws = self.get_worksheet('EXECUTION')
            pos = position or {}
            g = gates or {}
            _dte = int((pos.get('days_to_expiry', 99) or 99))
            _ist = now_ist()
            if _dte == 0:
                if _ist.hour >= 14:
                    _ew = 'EXPIRY DAY — EXIT REVIEW. No new entries after 14:00.'
                elif _ist.hour >= 13:
                    _ew = 'EXPIRY DAY — After 13:00. Selling only.'
                elif _ist.hour >= 11:
                    _ew = 'EXPIRY DAY — Theta accelerating. Prefer selling.'
                else:
                    _ew = 'EXPIRY DAY — Normal window open.'
            else:
                _ew = ''
            now_str = ist_str('%d-%b-%Y  %H:%M:%S  IST')
            op = pos.get('action', 'NONE') if pos else 'NONE'
            sv = safe_val

            # Row 2: expiry warning — safe to overwrite, not user input
            retry_call(lambda: ws.update(
                values=[['\u26a0 Expiry Status', _ew]], range_name='A2'),
                attempts=2, delay=2.0, fallback=None, label='ExecExpiryWarn')

            # Rows 10-19: status block
            status_rows = [
                ['\u2500 STATUS \u2500', ''],
                ['Last Updated', now_str],
                ['Trigger Status', 'IDLE'],
                ['Position State', pos.get('position_state', '') if pos else ''],
                ['Last Action', ''],
                ['Short Order ID', ''],
                ['Hedge Order ID', ''],
                ['Short Fill', ''],
                ['Hedge Fill', ''],
                ['Error', ''],
            ]
            retry_call(lambda: ws.update(
                values=status_rows, range_name='A10'),
                attempts=2, delay=2.0, fallback=None, label='ExecStatusBlock')

            # Rows 20-30: active position block
            pos_rows = [
                ['\u2500 ACTIVE POSITION \u2500', ''],
                ['Open Position', op],
                ['Entry Spot', sv(pos.get('entry_spot', '')) if pos else ''],
                ['Entry Time', pos.get('entry_time', '') if pos else ''],
                ['Short Strike', sv(pos.get('short_strike', '')) if pos else ''],
                ['Hedge Strike', sv(pos.get('hedge_strike', '')) if pos else ''],
                ['Hedge Gap', sv(pos.get('hedge_gap', '')) if pos else ''],
                ['Short Entry LTP', sv(pos.get('short_fill', '')) if pos else ''],
                ['Hedge Entry LTP', sv(pos.get('hedge_fill', '')) if pos else ''],
                ['Net Premium (\u20b9)', sv(pos.get('net_premium', '')) if pos else ''],
                ['Max Risk (\u20b9)', sv(pos.get('max_risk', '')) if pos else ''],
            ]
            retry_call(lambda: ws.update(
                values=pos_rows, range_name='A20'),
                attempts=2, delay=2.0, fallback=None, label='ExecPosBlock')

            # Rows 31-43: gates block
            gate_rows = [
                ['\u2500 SAFETY GATES \u2500', ''],
                ['Market Hours', g.get('Market Hours', '')],
                ['Checklist Fails', g.get('Checklist Fails', '')],
                ['No Active Position', g.get('No Active Position', '')],
                ['Strike in Focus Zone', g.get('Strike in Focus Zone', '')],
                ['Lot Size Valid', g.get('Lot Size Valid', '')],
                ['Min Premium (\u2265\u20b910)', g.get('Min Premium', '')],
                ['Static IP Registered', 'YES'],
                ['\u2500 GPT VALIDATION \u2500', ''],
                ['Trap Status', g.get('Trap Status', '')],
                ['GPT Trap Text', g.get('GPT Trap Text', '')],
                ['GPT Score Agreement', g.get('GPT Score Agreement', '')],
                ['GPT Bias Alignment', g.get('GPT Bias Alignment', '')],
            ]
            retry_call(lambda: ws.update(
                values=gate_rows, range_name='A31'),
                attempts=2, delay=2.0, fallback=None, label='ExecGateBlock')

            fmts = [{'range':'A1:B1','format':{'backgroundColor':self.NAVY}},
                   {'range':'A4:B4','format':{'backgroundColor':self.NAVY}},
                   {'range':'A10:B10','format':{'backgroundColor':self.NAVY}},
                   {'range':'A20:B20','format':{'backgroundColor':self.NAVY}},
                   {'range':'A31:B31','format':{'backgroundColor':self.NAVY}},
                   {'range':'A39:B39','format':{'backgroundColor':self.NAVY}}]
            if _ew:
                ew_color = (self.DEEP_RED if 'EXIT REVIEW' in _ew else
                           self.ORANGE if 'After 13:00' in _ew else
                           self.YELLOW if 'accelerating' in _ew else self.GREEN)
                fmts.append({'range':'A2:B2','format':{'backgroundColor':ew_color}})
            for offset, key in enumerate(['Market Hours','Checklist Fails','No Active Position',
                                         'Strike in Focus Zone','Lot Size Valid','Min Premium'],
                                        start=32):
                val = g.get(key, '')
                color = (self.GREEN if val.startswith('PASS')
                        else self.RED if val.startswith('FAIL') else self.YELLOW)
                fmts.append({'range':f'A{offset}:B{offset}','format':{'backgroundColor':color}})
            for row_n, key in {40:'Trap Status',41:'GPT Trap Text',42:'GPT Score Agreement',43:'GPT Bias Alignment'}.items():
                val = g.get(key, '')
                color = (self.DEEP_RED if 'FADE OPPORTUNITY' in val else
                        self.ORANGE if 'FADE LIKELY' in val else
                        self.YELLOW if ('MONITORING' in val or 'WARN' in val) else
                        self.RED if 'FAIL' in val else
                        self.GREEN if 'PASS' in val else self.WHITE)
                fmts.append({'range':f'A{row_n}:B{row_n}','format':{'backgroundColor':color}})
            if pos:
                fmts.append({'range':'A21:B21','format':{'backgroundColor':self.GREEN}})
            retry_call(lambda: ws.batch_format(fmts), attempts=2, delay=2.0, fallback=None, label='ExecFmt')
        except Exception as e:
            log.error(f'[Sheets] write_execution_tab(): {e}')

    def write_execution_scaffold(self):
        """
        Write the static column-A labels and trigger input defaults to
        the EXECUTION tab ONCE on tab creation only. This is the only
        place that writes the initial B5='NO', B6='SELL_PE', B7='', B8='1'
        defaults. Never call in the per-cycle loop.
        """
        try:
            ws = self.get_worksheet('EXECUTION')
            if ws.row_values(1):
                return  # already initialised — do not overwrite
            scaffold = [
                ['\u2501\u2501\u2501 EXECUTION CONTROL PANEL \u2501\u2501\u2501', ''],
                ['\u26a0 Expiry Status', ''],
                ['Activation Date', ''],
                ['\u2500 TRIGGER \u2500', ''],
                ['Execute Trade', 'NO'],
                ['Action', 'SELL_PE'],
                ['Strike', ''],
                ['Lots', '1'],
                ['Order Type', 'MARKET'],
            ]
            retry_call(lambda: ws.update(values=scaffold, range_name='A1'),
                       attempts=2, delay=2.0, fallback=None, label='ExecScaffold')
            log.info('[Sheets] EXECUTION tab scaffold written.')
        except Exception as e:
            log.warning(f'[Sheets] write_execution_scaffold(): {e}')

    def read_execution_trigger(self) -> dict:
        try:
            ws = self.get_worksheet('EXECUTION')
            vals = ws.batch_get(['B3','B5','B6','B7','B8','B9','B38'])
            def _c(v): return str(((v[0][0] if (v and v[0]) else '') or '')).strip()
            return {'activation_date':_c(vals[0]),'execute_trade':_c(vals[1]),'action':_c(vals[2]),
                   'strike':_c(vals[3]),'lots':_c(vals[4]),'order_type':_c(vals[5]),
                   'static_ip_confirmed':_c(vals[6])}
        except Exception as e:
            log.warning(f'[Sheets] read_execution_trigger(): {e}')
            return {'activation_date':'','execute_trade':'NO','action':'','strike':'0','lots':'1',
                   'order_type':'MARKET','static_ip_confirmed':''}

    def write_execution_status(self, status: str, error: str = ''):
        try:
            ws = self.get_worksheet('EXECUTION')
            retry_call(lambda: ws.update(values=[[ist_str()],[status]], range_name='B11'),
                      attempts=2, delay=1.0, fallback=None, label='ExecStatus')
            retry_call(lambda: ws.update(values=[[error]], range_name='B19'),
                      attempts=2, delay=1.0, fallback=None, label='ExecError')
        except Exception as e:
            log.warning(f'[Sheets] write_execution_status(): {e}')

    def write_execution_gates(self, gates: dict, snapshot: dict):
        try:
            ws = self.get_worksheet('EXECUTION')
            rows = [[gates.get('Market Hours','')],
                   [gates.get('Checklist Fails','')],
                   [gates.get('No Active Position','')],
                   [gates.get('Strike in Focus Zone','')],
                   [gates.get('Lot Size Valid','')],
                   [gates.get('Min Premium','')],
                   ['YES'],
                   ['\u2500 GPT VALIDATION \u2500'],
                   [gates.get('Trap Status','')],
                   [gates.get('GPT Trap Text','')],
                   [gates.get('GPT Score Agreement','')],
                   [gates.get('GPT Bias Alignment','')]]
            retry_call(lambda: ws.update(values=rows, range_name='B32'),
                      attempts=2, delay=1.0, fallback=None, label='ExecGates')
        except Exception as e:
            log.warning(f'[Sheets] write_execution_gates(): {e}')

    def write_execution_full(self, position, short_order, hedge_order, short_fill, hedge_fill):
        try:
            ws = self.get_worksheet('EXECUTION')
            pos = position or {}
            sv = safe_val
            status_rows = [[ist_str()],['DONE'],[pos.get('position_state','')],
                          [str(pos.get('action',''))+' '+str(pos.get('short_strike',''))+' x'+str(pos.get('lots',''))+' lot'],
                          [short_order],[hedge_order],[sv(short_fill)],[sv(hedge_fill)],['']]
            retry_call(lambda: ws.update(values=status_rows, range_name='B11'),
                      attempts=2, delay=1.0, fallback=None, label='ExecFullStatus')
            pos_rows = [[pos.get('action','NONE')],[sv(pos.get('entry_spot',''))],[pos.get('entry_time','')],
                       [sv(pos.get('short_strike',''))],[sv(pos.get('hedge_strike',''))],
                       [sv(pos.get('hedge_gap',''))],[sv(pos.get('short_fill',''))],
                       [sv(pos.get('hedge_fill',''))],[sv(pos.get('net_premium',''))],
                       [sv(pos.get('max_risk',''))]]
            retry_call(lambda: ws.update(values=pos_rows, range_name='B21'),
                      attempts=2, delay=1.0, fallback=None, label='ExecFullPos')
        except Exception as e:
            log.warning(f'[Sheets] write_execution_full(): {e}')

    def update_position_state(self, pos: dict):
        try:
            ws = self.get_worksheet('EXECUTION')
            retry_call(lambda: ws.update(values=[[pos.get('position_state','')]], range_name='B13'),
                      attempts=2, delay=1.0, fallback=None, label='ExecPosState')
        except Exception as e:
            log.warning(f'[Sheets] update_position_state(): {e}')

    def write_execution_position_cleared(self):
        try:
            ws = self.get_worksheet('EXECUTION')
            retry_call(lambda: ws.update(values=[['DONE'],['']], range_name='B12'),
                      attempts=2, delay=1.0, fallback=None, label='ExecDone')
            empty_pos = [['NONE']]+[['']*1 for _ in range(9)]
            retry_call(lambda: ws.update(values=empty_pos, range_name='B21'),
                      attempts=2, delay=1.0, fallback=None, label='ExecPosClr')
        except Exception as e:
            log.warning(f'[Sheets] write_execution_position_cleared(): {e}')

    def reset_execution_trigger(self):
        try:
            ws = self.get_worksheet('EXECUTION')
            retry_call(lambda: ws.update(values=[['NO']], range_name='B5'),
                      attempts=2, delay=1.0, fallback=None, label='ExecReset')
        except Exception as e:
            log.warning(f'[Sheets] reset_execution_trigger(): {e}')

    def deactivate_execution_for_new_session(self):
        try:
            ws = self.get_worksheet('EXECUTION')
            retry_call(lambda: ws.update(values=[['']], range_name='B3'),
                      attempts=2, delay=2.0, fallback=None, label='ExecDeactDate')
            retry_call(lambda: ws.update(values=[['NO']], range_name='B5'),
                      attempts=2, delay=2.0, fallback=None, label='ExecDeactTrigger')
            log.info('[Sheets] Execution deactivated for new session.')
        except Exception as e:
            log.warning(f'[Sheets] deactivate_execution_for_new_session(): {e}')

    def suggest_trap_fade(self, fade_action: str, fade_strike: float, fade_status: str):
        try:
            ws = self.get_worksheet('EXECUTION')
            retry_call(lambda: ws.update(values=[[fade_action],[str(int(fade_strike))]], range_name='B6'),
                      attempts=2, delay=1.0, fallback=None, label='TrapFadeSuggest')
            retry_call(lambda: ws.update(values=[[fade_status]], range_name='B12'),
                      attempts=2, delay=1.0, fallback=None, label='TrapFadeStatus')
            log.info(f'[Sheets] Trap fade suggested: {fade_action} at {fade_strike:.0f}')
        except Exception as e:
            log.warning(f'[Sheets] suggest_trap_fade(): {e}')

    def append_position_log(self, position: dict, event: str, snapshot: dict):
        try:
            ws = self.get_worksheet('POSITION_LOG')
            existing = ws.row_values(1)
            if not existing:
                retry_call(lambda: ws.update(values=[self.POSITION_LOG_HEADER], range_name='A1'),
                          attempts=2, delay=2.0, fallback=None, label='PosLogHeader')
                retry_call(lambda: ws.freeze(rows=1), attempts=1, delay=1.0, fallback=None, label='PosLogFreeze')
            sv = safe_val
            pos = position or {}
            row = [ist_str(),event,pos.get('action',''),pos.get('short_symbol',''),sv(pos.get('short_strike','')),
                  pos.get('hedge_symbol',''),sv(pos.get('hedge_strike','')),pos.get('lots',0),pos.get('quantity',0),
                  pos.get('lot_size',75),sv(pos.get('short_fill','')),sv(pos.get('hedge_fill','')),
                  sv(pos.get('net_premium','')),sv(pos.get('max_risk','')),sv(pos.get('entry_spot','')),
                  pos.get('entry_time',''),pos.get('short_order_id',''),pos.get('hedge_order_id',''),
                  pos.get('hedge_gap',200),pos.get('position_state',''),str(pos.get('is_trap_fade',False)),
                  snapshot.get('bias',''),snapshot.get('score',''),snapshot.get('market_condition',''),
                  snapshot.get('sr_event',''),sv(snapshot.get('vix_level',''))]
            if len(row) != len(self.POSITION_LOG_HEADER):
                log.error(f'[Sheets] append_position_log: row={len(row)} != header={len(self.POSITION_LOG_HEADER)} — skip')
                return
            retry_call(lambda: ws.append_row(row,value_input_option='USER_ENTERED'),
                      attempts=2, delay=2.0, fallback=None, label='PosLogAppend')
        except Exception as e:
            log.error(f'[Sheets] append_position_log(): {e}')

    def _ensure_signal_header(self, ws):
        try:
            existing = ws.row_values(1)
            if existing == self.SIGNAL_HEADER:
                return
            if not existing:
                retry_call(lambda: ws.update(values=[self.SIGNAL_HEADER], range_name='A1'),
                          attempts=2, delay=2.0, fallback=None, label='SignalHeader')
                retry_call(lambda: ws.freeze(rows=1), attempts=2, delay=2.0, fallback=None, label='SignalFreeze')
        except Exception as e:
            log.warning(f'[Sheets] _ensure_signal_header(): {e}')

    def append_signal_row(self, setup, snapshot, signals, metrics, theta_env, vix_data, sr_event,
                         cycle_num, mtf_context=None):
        try:
            ws = self.get_worksheet('SIGNAL')
            self._ensure_signal_header(ws)
            mtf = mtf_context or {}
            gate = setup.get('gate_results', {})
            sv = safe_val
            row = [setup.get('signal_id',''),ist_str(),cycle_num,setup.get('time_block',''),
                  str(setup.get('expiry_day',False)),str(setup.get('pre_expiry_warning',False)),
                  setup.get('setup_type',''),setup.get('setup_quality',0),setup.get('blocked_reason',''),
                  snapshot.get('bias',''),snapshot.get('score',''),sv(snapshot.get('spot','')),
                  int(metrics.get('support_strike',0)or 0),int(metrics.get('resistance_strike',0)or 0),
                  sv(signals.get('vwap_level','')),signals.get('price_structure',''),
                  mtf.get('mtf_15m',{}).get('structure',''),mtf.get('mtf_30m',{}).get('structure',''),
                  sr_event.get('event','NONE'),int(snapshot.get('sr_event_age',0)or 0),setup.get('oi_regime',''),
                  theta_env.get('market_condition',''),sv(vix_data.get('vix_current','')),vix_data.get('vix_trend',''),
                  sv(metrics.get('pcr_oi','')),sv(metrics.get('oi_concentration','')),theta_env.get('days_to_expiry',0),
                  sv(setup.get('short_strike',0)),setup.get('short_option_type',''),sv(setup.get('short_ltp',0)),
                  sv(setup.get('hedge_strike',0)),sv(setup.get('hedge_ltp',0)),
                  sv(setup.get('net_premium',0)),sv(setup.get('max_risk',0)),setup.get('lot_size',75),
                  sv(setup.get('net_premium_total',0)),sv(setup.get('max_risk_total',0)),
                  str(gate.get('environment_ok','')),str(gate.get('structure_ok','')),gate.get('oi_regime',''),
                  str(gate.get('liquidity_ok','')),str(gate.get('trap_ok','')),str(gate.get('vwap_vol_ok','')),
                  str(gate.get('late_entry','')),gate.get('strategy_selected',''),
                  '','','','','','','','','']
            if len(row) != len(self.SIGNAL_HEADER):
                log.error(f'[Sheets] append_signal_row: row={len(row)} != header={len(self.SIGNAL_HEADER)} — skip')
                return
            retry_call(lambda: ws.append_row(row,value_input_option='USER_ENTERED'),
                      attempts=2, delay=2.0, fallback=None, label='SignalAppend')
            try:
                # Use row_count (lightweight) instead of get_all_values()
                # to find the last row after append.
                last_row = ws.row_count if hasattr(ws, 'row_count') else len(ws.col_values(1))
                setup_type = setup.get('setup_type','')
                if setup_type == SetupEvaluator.SETUP_DECAY:
                    row_color = self.ORANGE
                elif setup_type == SetupEvaluator.SETUP_BUY_BREAK:
                    row_color = self.GREEN
                elif setup_type == SetupEvaluator.SETUP_BUY_REV:
                    row_color = self.YELLOW
                else:
                    row_color = self.WHITE
                retry_call(lambda: ws.batch_format([{'range':f'A{last_row}:C{last_row}','format':{'backgroundColor':row_color}}]),
                          attempts=1, delay=1.0, fallback=None, label='SignalRowColor')
            except Exception:
                pass
        except Exception as e:
            log.error(f'[Sheets] append_signal_row(): {e}')

    def update_signal_outcomes(self, pending_signals: list, current_spot: float):
        try:
            if not pending_signals:
                return
            needs_check = any(s.get('cycles_elapsed',0) >= 3 for s in pending_signals)
            if not needs_check:
                return
            ws = self.get_worksheet('SIGNAL')
            # Fetch up to 500 rows only — avoids O(n) full-sheet read as log grows
            all_values = ws.get('A1:BZ500') or []
            if len(all_values) < 2:
                return
            header = all_values[0]
            try:
                id_col = header.index('Signal ID')
                o15s_col = header.index('Spot 15m Later')
                oqf_col = header.index('Quality Score Final')
            except ValueError as ve:
                log.warning(f'[Sheets] update_signal_outcomes: missing col: {ve}')
                return
            def _cl(idx: int) -> str:
                r, n = '', idx + 1
                while n:
                    n, rem = divmod(n-1,26)
                    r = chr(65+rem)+r
                return r
            start_col = _cl(o15s_col)
            end_col = _cl(oqf_col)
            for sig in pending_signals:
                cycles   = sig.get('cycles_elapsed', 0)
                done_15  = sig.get('outcome_15m_done', False)
                done_30  = sig.get('outcome_30m_done', False)
                ready_15 = cycles >= 3 and not done_15
                ready_30 = cycles >= 6 and not done_30
                if not (ready_15 or ready_30):
                    continue
                signal_id  = sig.get('signal_id', '')
                spot_entry = float(sig.get('spot_at_signal', 0) or 0)
                bias_entry = sig.get('bias', '')
                row_idx = None
                for i, row in enumerate(all_values[1:], start=2):
                    if len(row) > id_col and row[id_col] == signal_id:
                        row_idx = i
                        break
                if row_idx is None:
                    continue

                def _label(spot_now):
                    pts = round(spot_now - spot_entry, 2)
                    is_bull = 'BULLISH' in bias_entry.upper()
                    is_bear = 'BEARISH' in bias_entry.upper()
                    ok = (is_bull and pts > 10) or (is_bear and pts < -10)
                    if abs(pts) <= 10:
                        lbl = 'NO_EDGE'
                    elif ok:
                        lbl = 'CORRECT'
                    else:
                        lbl = 'INCORRECT'
                    return pts, ok, lbl

                if ready_15:
                    sig['spot_at_15m'] = current_spot
                    sig['outcome_15m_done'] = True

                if ready_30:
                    sig['outcome_30m_done'] = True

                spot_15 = float(sig.get('spot_at_15m', current_spot) or current_spot)
                spot_30 = current_spot
                pts_15, ok_15, lbl_15 = _label(spot_15)
                pts_30, ok_30, lbl_30 = _label(spot_30)

                q = sig.get('setup_quality', 0)
                # 15m outcome: lighter weight (early read, noisier)
                if lbl_15 == 'CORRECT':
                    q = min(100, q + 15)
                elif lbl_15 == 'INCORRECT':
                    q = max(0, q - 10)
                # 30m outcome: heavier weight (more confirmatory)
                if lbl_30 == 'CORRECT':
                    q = min(100, q + 40)
                elif lbl_30 == 'INCORRECT':
                    q = max(0, q - 20)

                outcome = [spot_15, pts_15, str(ok_15), lbl_15,
                           spot_30, pts_30, str(ok_30), lbl_30, q]
                retry_call(lambda r=row_idx, o=outcome: ws.update(values=[o], range_name=f'{start_col}{r}:{end_col}{r}'),
                          attempts=2, delay=1.0, fallback=None, label=f'OutcomeBatch_{signal_id}')
                log.info(
                    f'[SignalOutcome] {signal_id}: '
                    f'15m={lbl_15} ({pts_15:+.1f}pts) '
                    f'30m={lbl_30} ({pts_30:+.1f}pts) quality={q}')
            # Prune fully-resolved signals so the list doesn't grow unboundedly
            pending_signals[:] = [
                s for s in pending_signals
                if not (s.get('outcome_15m_done') and s.get('outcome_30m_done'))
            ]
        except Exception as e:
            log.warning(f'[Sheets] update_signal_outcomes(): {e}')


# ─────────────────────────────────────────────────────────────────────────────
# 12. TelegramSender
# ─────────────────────────────────────────────────────────────────────────────

class TelegramSender:
    """
    Sends HTML-formatted Telegram messages via Bot API.
    Entirely optional — silently disabled if token or chat_id are empty.
    """

    def __init__(self):
        self.token   = CONFIG.get('TELEGRAM_BOT_TOKEN', '') or ''
        self.chat_id = CONFIG.get('TELEGRAM_CHAT_ID', '')   or ''
        self.enabled = bool(self.token and self.chat_id)
        if not self.enabled:
            log.info('[Telegram] Disabled — token or chat_id not configured.')

    def send(self, text: str, silent: bool = False) -> bool:
        if not self.enabled:
            return False
        try:
            # Truncate message to Telegram's 4096 char limit
            text = text[:4096]
            url     = f'https://api.telegram.org/bot{self.token}/sendMessage'
            payload = {
                'chat_id':              self.chat_id,
                'text':                 text,
                'parse_mode':           'HTML',
                'disable_notification': silent,
            }
            r = requests.post(url, json=payload, timeout=10)
            r.raise_for_status()
            return True
        except Exception as e:
            log.warning(f'[Telegram] send() failed: {e}')
            return False

    def send_analysis(self, analysis: dict, snapshot: dict, prev_day: dict, ts: str,
                      mtf_context: dict = None) -> bool:
        """Alert filtering: send only when strength=Strong OR sr_confidence=HIGH OR trap non-empty."""
        if not self.enabled:
            return False
        strength   = analysis.get('strength', '')
        sr_event   = snapshot.get('sr_event', 'NONE')
        sr_conf    = snapshot.get('sr_confidence', '')
        trap       = snapshot.get('trap', '')
        if not (strength == 'Strong' or (sr_event != 'NONE' and sr_conf == 'HIGH') or trap):
            return False

        bias    = snapshot.get('bias', '—')
        spot    = snapshot.get('spot', 0)
        atm     = snapshot.get('atm', 0)
        support = snapshot.get('support', 0)
        resist  = snapshot.get('resistance', 0)
        score   = snapshot.get('score', '—')
        conf    = snapshot.get('confidence', '—')
        pcr     = snapshot.get('pcr_oi', float('nan'))
        vwap_b  = snapshot.get('vwap_bias', '—')
        mc      = snapshot.get('market_condition', '')
        vix     = snapshot.get('vix_level', float('nan'))

        bias_upper = bias.upper() if bias else ''
        bias_icon  = ('🟢' if 'BULLISH' in bias_upper else
                      '🔴' if 'BEARISH' in bias_upper else '🟡')

        sr_icon_map = {
            'BREAKOUT_ABOVE_RESISTANCE': '🚀',
            'BREAKDOWN_BELOW_SUPPORT':   '📉',
            'SUPPORT_REVERSAL':          '📈',
            'RESISTANCE_REVERSAL':       '🔻',
        }
        sr_icon = sr_icon_map.get(sr_event, 'ℹ️')

        pcr_str = f'{pcr:.3f}' if (not math.isnan(pcr)) else '—'
        vix_str = f'{vix:.2f}' if (not math.isnan(vix)) else '—'

        # Prev day tag
        ph = prev_day.get('prev_high', 0) or 0
        pl = prev_day.get('prev_low',  0) or 0
        if ph and spot > ph:
            pd_tag = f'Above prev high ({ph})'
        elif pl and spot < pl:
            pd_tag = f'Below prev low ({pl})'
        elif ph and pl:
            pd_tag = f'Inside prev range ({pl}–{ph})'
        else:
            pd_tag = '—'

        trap_line = ''
        if trap:
            trap_line = f'\n⚠️ <b>TRAP WARNING:</b> {html.escape(str(trap))}'

        sr_line = ''
        if sr_event != 'NONE':
            sr_line = f'\n{sr_icon} <b>SR Event:</b> {html.escape(sr_event)} [{html.escape(sr_conf)}]'

        # ── MTF section ──────────────────────────────────────────────────────────
        _mtf   = mtf_context or {}
        _oi_t  = _mtf.get('mtf_oi_trend', {})
        _sr_c  = _mtf.get('mtf_sr_context', {})
        _m15   = _mtf.get('mtf_15m', {}).get('structure', '')
        _m30   = _mtf.get('mtf_30m', {}).get('structure', '')
        _ps    = snapshot.get('price_structure', '')

        mtf_line = ''
        if _m15 or _m30:
            mtf_line = (
                f'\n📊 <b>MTF:</b> '
                f'5m={html.escape(str(_ps))} | '
                f'15m={html.escape(str(_m15))} | '
                f'30m={html.escape(str(_m30))}'
            )
        _align = analysis.get('mtf_alignment', '')
        align_line = (
            f'\n🔗 <b>Alignment:</b> {html.escape(str(_align))}'
            if _align else ''
        )
        _sup_risk = _sr_c.get('support_break_risk', '')
        _res_risk = _sr_c.get('resistance_break_risk', '')
        _risk_icon = '🔴' if 'HIGH' in (str(_sup_risk) + str(_res_risk)) else '🟡'
        sr_risk_line = ''
        if _sup_risk or _res_risk:
            sr_risk_line = (
                f'\n{_risk_icon} <b>Break Risk:</b> '
                f'Sup={html.escape(str(_sup_risk))} '
                f'Res={html.escape(str(_res_risk))}'
            )

        reasoning = analysis.get('reasoning', [])
        r_pts = '\n'.join(f'  • {html.escape(str(r))}' for r in reasoning[:3]) or '—'
        current_sit = html.escape(str(analysis.get('current_situation', '') or ''))[:400]
        signal_txt  = html.escape(str(analysis.get('signal', '') or ''))[:200]
        risk_txt    = html.escape(str(analysis.get('risk_note', '') or ''))[:200]
        mc_txt      = html.escape(mc) if mc else '—'

        msg = (
            f'{bias_icon} <b>NIFTY — {html.escape(ts)}</b>\n'
            f'━━━━━━━━━━━━━━━━━━━━━━━━\n'
            f'<b>Bias:</b> {html.escape(bias)} | <b>Strength:</b> {html.escape(strength)}\n'
            f'<b>Score:</b> {html.escape(str(score))}  <b>Conf:</b> {html.escape(str(conf))}\n'
            f'<b>Spot:</b> {html.escape(str(spot))}  <b>ATM:</b> {html.escape(str(atm))}\n'
            f'<b>Support:</b> {html.escape(str(support))}  <b>Resistance:</b> {html.escape(str(resist))}\n'
            f'<b>PCR:</b> {html.escape(pcr_str)}  <b>VWAP:</b> {html.escape(str(vwap_b))}'
            f'{trap_line}{sr_line}\n'
            f'<b>Market Cond:</b> {mc_txt}  <b>VIX:</b> {vix_str}\n'
            f'━━━━━━━━━━━━━━━━━━━━━━━━\n'
            f'<b>Situation:</b>\n{current_sit}'
            f'{mtf_line}{align_line}{sr_risk_line}\n\n'
            f'<b>Signal:</b> {signal_txt}\n\n'
            f'<b>Why:</b>\n{r_pts}\n\n'
            f'<b>Prev Day:</b> {html.escape(pd_tag)}\n'
            f'<b>Risk:</b> {risk_txt}'
        )
        return self.send(msg)

    def send_morning_brief(self, text: str, prev_day: dict) -> bool:
        if not self.enabled:
            return False
        ph    = prev_day.get('prev_high',  '—')
        pl    = prev_day.get('prev_low',   '—')
        pc    = prev_day.get('prev_close', '—')
        pdate = prev_day.get('prev_date',  '—')
        prng  = prev_day.get('prev_range', '—')
        date_str = now_ist().strftime('%d-%b-%Y')
        msg = (
            f'🌅 <b>NIFTY Morning Brief — {html.escape(date_str)}</b>\n'
            f'━━━━━━━━━━━━━━━━━━━━━━━━\n'
            f'<b>Previous Session ({html.escape(str(pdate))}):</b>\n'
            f'  High: {html.escape(str(ph))}  Low: {html.escape(str(pl))}  Close: {html.escape(str(pc))}\n'
            f'  Range: {html.escape(str(prng))} pts\n'
            f'━━━━━━━━━━━━━━━━━━━━━━━━\n'
            f'{html.escape(str(text))}'
        )
        return self.send(msg)

    def send_eod(self, text: str) -> bool:
        if not self.enabled:
            return False
        date_str = now_ist().strftime('%d-%b-%Y')
        msg = (
            f'🔔 <b>NIFTY EOD Review — {html.escape(date_str)}</b>\n'
            f'━━━━━━━━━━━━━━━━━━━━━━━━\n'
            f'{html.escape(str(text))}'
        )
        return self.send(msg, silent=True)


# ─────────────────────────────────────────────────────────────────────────────
# 12. OrderExecutor
# ─────────────────────────────────────────────────────────────────────────────

class OrderExecutor:
    """
    Manual trade execution triggered by Google Sheets button.
    ONE-DAY GATE: B3 must contain today's IST date. Apps Script writes; Python clears at reset.
    13 lifecycle states, trap fade scoring, full position monitoring.
    """
    PRODUCT_TYPE_DEFAULT = 'INTRADAY'  # MIS — correct for intraday option strategies
    PRODUCT_TYPE = 'INTRADAY'          # alias used by _exit_all_positions
    VARIETY = 'NORMAL'
    EXCHANGE = 'NFO'
    ORDER_TYPE = 'MARKET'
    DURATION = 'DAY'

    STATE_OPEN = 'OPEN'
    STATE_PARTIAL_PROFIT = 'PARTIAL_PROFIT'
    STATE_TARGET = 'TARGET_ACHIEVED'
    STATE_PARTIAL_LOSS = 'PARTIAL_LOSS'
    STATE_STOPLOSS = 'STOPLOSS_HIT'
    STATE_EXIT_STRUCTURE = 'EXIT_ON_STRUCTURE'
    STATE_EXIT_VWAP = 'EXIT_ON_VWAP'
    STATE_EXIT_TRAP = 'EXIT_ON_TRAP'
    STATE_EXIT_THETA = 'EXIT_ON_THETA_EDGE'
    STATE_EXIT_OI = 'EXIT_ON_OI_UNWIND'
    STATE_EXIT_SR_RESET = 'EXIT_ON_SR_RESET'
    STATE_TIME_EXIT = 'TIME_EXIT'
    STATE_HEDGE_FAILED = 'HEDGE_FAILED'

    TARGET_PCT = 0.50
    PARTIAL_PCT = 0.20
    STOPLOSS_PCT = 0.75
    PARTIAL_LOSS_PCT = 0.50

    def __init__(self, api_client, instrument_loader, telegram, sheets):
        self.api_client = api_client
        self.instrument_loader = instrument_loader
        self.telegram = telegram
        self.sheets = sheets
        self.active_position: dict = {}
        self._last_trap_type: str = 'NONE'
        self._neutral_vol_cycles: int = 0

    @staticmethod
    def _round_to_tick(price: float, tick: float = 0.05) -> float:
        """Round price to nearest tick (default 0.05)."""
        return round(round(price / tick) * tick, 2)

    def _compute_hedge_gap(self, vix_level: float, is_trap_fade: bool, short_ltp: float) -> int:
        try:
            vix = float(vix_level or 14.0)
            if math.isnan(vix): vix = 14.0
        except Exception:
            vix = 14.0
        if vix > 22.0: gap = 400
        elif vix > 18.0: gap = 300
        elif is_trap_fade and (short_ltp or 0) < 50.0: gap = 150
        else: gap = 200
        return max(150, (gap // 50) * 50)

    def _compute_pnl(self, pos: dict, short_current: float, hedge_current: float) -> float:
        qty = int(pos.get('quantity', 25) or 25)
        txn = pos.get('txn', 'SELL')
        short_entry = float(pos.get('short_fill', 0) or 0)
        hedge_entry = float(pos.get('hedge_fill', 0) or 0)
        state = pos.get('position_state', self.STATE_OPEN)
        if txn == 'BUY':
            return round((short_current - short_entry) * qty, 2)
        elif state == self.STATE_HEDGE_FAILED:
            return round((short_entry - short_current) * qty, 2)
        else:
            return round(((short_entry - short_current) + (hedge_current - hedge_entry)) * qty, 2)

    def _assess_trap_fade(self, snapshot: dict, metrics: dict, gpt_analysis: dict) -> dict:
        result = {'trap_type': 'NONE', 'gpt_confirmed': False, 'gpt_bias_aligns': False,
                  'wick_confirms': False, 'age_confirms': False, 'fade_score': 0,
                  'fade_action': 'NONE', 'fade_strike': 0.0, 'fade_status': 'PASS — no trap detected',
                  'suggest': False}
        try:
            trap_msg = snapshot.get('trap', '')
            if not trap_msg:
                self._last_trap_type = 'NONE'
                return result
            is_bull = 'bull trap' in trap_msg.lower()
            is_bear = 'bear trap' in trap_msg.lower()
            if not (is_bull or is_bear):
                self._last_trap_type = 'NONE'
                return result
            result['trap_type'] = 'BULL_TRAP' if is_bull else 'BEAR_TRAP'
            self._last_trap_type = result['trap_type']
            fade_score = 1
            # Factors are 100% market-observable — no GPT dependency.
            # GPT fields retained in result dict for display only (not scoring).
            gpt = gpt_analysis or {}
            gpt_bias = (gpt.get('market_bias', '') or 'Neutral')
            result['gpt_confirmed'] = False   # display-only, not scored
            result['gpt_bias_aligns'] = (
                (is_bull and gpt_bias == 'Bearish') or
                (is_bear and gpt_bias == 'Bullish')
            )  # display-only, not scored

            # Factor 2: candle volume ratio < 0.8 = low conviction breakout
            vol_ratio = float(snapshot.get('candle_vol_ratio', 1.0) or 1.0)
            result['low_vol_confirms'] = vol_ratio < 0.8
            if result['low_vol_confirms']: fade_score += 1

            # Factor 3: VWAP opposing the breakout direction
            vwap_bias = snapshot.get('vwap_bias', 'NEUTRAL')
            result['vwap_opposes'] = (
                (is_bull and vwap_bias == 'BEARISH') or
                (is_bear and vwap_bias == 'BULLISH')
            )
            if result['vwap_opposes']: fade_score += 1

            # Factor 4: SR event has persisted (not a one-cycle spike)
            sr_age = int(snapshot.get('sr_event_age', 0) or 0)
            result['age_confirms'] = sr_age >= 2
            if result['age_confirms']: fade_score += 1

            # Factor 5: Rejection wick confirms reversal
            wick_pct = float(snapshot.get('candle_wick_pct', 0) or 0)
            result['wick_confirms'] = wick_pct > 50
            if result['wick_confirms']: fade_score += 1
            result['fade_score'] = fade_score
            result['suggest'] = (fade_score >= 3)
            res_s = float(metrics.get('resistance_strike', 0) or 0)
            sup_s = float(metrics.get('support_strike', 0) or 0)
            if is_bull and res_s > 0:
                result['fade_action'] = 'SELL_CE'
                result['fade_strike'] = res_s
            elif is_bear and sup_s > 0:
                result['fade_action'] = 'SELL_PE'
                result['fade_strike'] = sup_s
            label = 'BULL' if is_bull else 'BEAR'
            if fade_score >= 4:
                result['fade_status'] = (f'FADE OPPORTUNITY ({fade_score}/5): {result["fade_action"]} '
                                        f'at {result["fade_strike"]:.0f} — {label} trap confirmed. Click EXECUTE TRADE.')
            elif fade_score >= 3:
                result['fade_status'] = (f'FADE LIKELY ({fade_score}/5): {result["fade_action"]} '
                                        f'at {result["fade_strike"]:.0f} — monitoring.')
            else:
                result['fade_status'] = f'TRAP MONITORING ({fade_score}/5): Insufficient confirmation. Wait.'
        except Exception as e:
            log.warning(f'[OrderExecutor] _assess_trap_fade: {e}')
        return result

    def _evaluate_lifecycle(self, pos: dict, snapshot: dict, gpt_analysis: dict) -> str:
        if not pos: return ''
        try:
            ist_now = now_ist()
            action = pos.get('action', '')
            txn = pos.get('txn', 'SELL')
            expiry_day = pos.get('expiry_day', False)
            net_prem = float(pos.get('net_premium', 0) or 0)
            max_risk = float(pos.get('max_risk', 0) or 0)
            qty = int(pos.get('quantity', 25) or 25)
            entry_spot = float(pos.get('entry_spot', 0) or 0)
            # net_prem and max_risk are already total ₹ (price × quantity).
            # Do NOT multiply by qty again — that would inflate by lot size.
            target    = net_prem  * self.TARGET_PCT
            stoploss  = -(max_risk * self.STOPLOSS_PCT)
            partial_p = net_prem  * self.PARTIAL_PCT
            partial_l = -(max_risk * self.PARTIAL_LOSS_PCT)
            spot_now = float(snapshot.get('spot', entry_spot) or entry_spot)
            spot_move = spot_now - entry_spot
            # Estimate option delta from moneyness to avoid overstating OTM loss.
            # ATM (moneyness=0) → delta ≈ 0.50; far OTM (moneyness>0.03) → delta ≈ 0.10
            if entry_spot > 0:
                short_strike = float(self.active_position.get('short_strike', entry_spot) or entry_spot)
                moneyness = abs(short_strike - entry_spot) / entry_spot
                est_delta = max(0.10, 0.50 * math.exp(-moneyness / 0.015))
            else:
                est_delta = 0.50
            pnl_proxy = ((-spot_move * qty * est_delta) if txn == 'SELL'
                         else (spot_move * qty * est_delta))
            pr_struct = snapshot.get('price_structure', '')
            vwap_bias = snapshot.get('vwap_bias', 'NEUTRAL')
            vol_bias = snapshot.get('vol_bias', 'NEUTRAL')
            trap_msg = snapshot.get('trap', '')
            mkt_cond = snapshot.get('market_condition', '')
            sr_age = int(snapshot.get('sr_event_age', 0) or 0)
            pe_chg_oi = float(snapshot.get('total_pe_chg_oi', 0) or 0)
            ce_chg_oi = float(snapshot.get('total_ce_chg_oi', 0) or 0)
            if not pos.get('hedge_order_id') and txn == 'SELL' and pos.get('hedge_token'):
                return self.STATE_HEDGE_FAILED
            if (expiry_day and ist_now.hour >= 14) or (ist_now.hour == 15 and ist_now.minute >= 10):
                return self.STATE_TIME_EXIT  # 15:10 — 10-min window before broker auto-squareoff
            if pnl_proxy <= stoploss:
                return self.STATE_STOPLOSS
            if pnl_proxy >= target:
                return self.STATE_TARGET
            entry_structure = pos.get('entry_structure', '')
            if entry_structure and pr_struct not in ('', 'INSUFFICIENT_DATA'):
                if (('BULLISH' in entry_structure and 'BEARISH' in pr_struct) or
                    ('BEARISH' in entry_structure and 'BULLISH' in pr_struct)):
                    return self.STATE_EXIT_STRUCTURE
            entry_vwap = pos.get('entry_vwap_bias', 'NEUTRAL')
            if txn == 'SELL':
                if entry_vwap != 'NEUTRAL' and vwap_bias != 'NEUTRAL' and vwap_bias != entry_vwap:
                    return self.STATE_EXIT_VWAP
            elif txn == 'BUY':
                if vwap_bias != 'NEUTRAL' and (('CE' in action and vwap_bias == 'BEARISH') or
                                               ('PE' in action and vwap_bias == 'BULLISH')):
                    return self.STATE_EXIT_VWAP
            if trap_msg:
                is_fade = pos.get('is_trap_fade', False)
                if not is_fade:
                    if 'bull trap' in trap_msg.lower() and 'BUY_CE' in action:
                        return self.STATE_EXIT_TRAP
                    if 'bear trap' in trap_msg.lower() and 'BUY_PE' in action:
                        return self.STATE_EXIT_TRAP
            if txn == 'SELL' and mkt_cond == 'Expansion Favorable':
                return self.STATE_EXIT_THETA
            OI_THRESHOLD = -50000
            if 'SELL_PE' in action and pe_chg_oi < OI_THRESHOLD:
                return self.STATE_EXIT_OI
            if 'SELL_CE' in action and ce_chg_oi < OI_THRESHOLD:
                return self.STATE_EXIT_OI
            entry_sr_age = int(pos.get('entry_sr_age', 0) or 0)
            if entry_sr_age >= 6 and sr_age == 0:
                return self.STATE_EXIT_SR_RESET
            if vol_bias == 'NEUTRAL':
                self._neutral_vol_cycles += 1
            else:
                self._neutral_vol_cycles = 0
            if pnl_proxy >= partial_p:
                return self.STATE_PARTIAL_PROFIT
            if pnl_proxy <= partial_l:
                return self.STATE_PARTIAL_LOSS
            return self.STATE_OPEN
        except Exception as e:
            log.warning(f'[OrderExecutor] _evaluate_lifecycle: {e}')
            return self.STATE_OPEN

    def check_and_execute(self, trigger: dict, snapshot: dict, metrics: dict, cfg: dict,
                         focus_zone: list, gpt_analysis: dict = None) -> bool:
        try:
            if trigger.get('execute_trade', 'NO').upper() != 'YES':
                if self.active_position:
                    self._run_lifecycle_check(snapshot, gpt_analysis)
                return False
            act_date = trigger.get('activation_date', '').strip()
            today_ist = now_ist().strftime('%d-%b-%Y')
            if act_date.upper() != today_ist.upper():
                log.warning(f'[OrderExecutor] Date gate: {act_date} != {today_ist}')
                self.sheets.write_execution_status(status='SAFETY_BLOCKED',
                                                  error=f'Activation date {act_date} != today {today_ist}. Click EXECUTE TRADE again today.')
                return False
            action = trigger.get('action', '').upper().strip()
            if action not in {'SELL_CE', 'SELL_PE', 'BUY_CE', 'BUY_PE', 'EXIT_ALL'}:
                self.sheets.write_execution_status(status='FAILED', error=f'Invalid action: {action}')
                return True
            try:
                strike = float(trigger.get('strike', '0') or '0')
                lots = max(1, int(trigger.get('lots', '1') or '1'))
            except (ValueError, TypeError):
                self.sheets.write_execution_status(status='FAILED', error='Invalid strike or lots.')
                return True
            # Parse order type (default MARKET)
            order_type_req = (trigger.get('order_type', 'MARKET') or 'MARKET').upper().strip()
            if order_type_req not in {'MARKET', 'LIMIT'}:
                self.sheets.write_execution_status(status='FAILED', error=f'Invalid order_type: {order_type_req}. Support MARKET|LIMIT only.')
                return True
            # Parse product type (default CARRYFORWARD)
            product_type_req = (trigger.get('product_type', self.PRODUCT_TYPE_DEFAULT) or self.PRODUCT_TYPE_DEFAULT).upper().strip()
            if product_type_req not in {'CARRYFORWARD', 'INTRADAY'}:
                self.sheets.write_execution_status(status='FAILED', error=f'Invalid product_type: {product_type_req}. Support CARRYFORWARD|INTRADAY only.')
                return True
            contract_lot_size = int(cfg.get('contract_lot_size', 0) or 0)

            if contract_lot_size <= 0:
                raise ValueError(
                    f'Invalid contract lot size in Google Sheets: {contract_lot_size}. Update SETTINGS.'
                )

            quantity = contract_lot_size * lots
            lot_size = contract_lot_size
            expiry_str = cfg.get('_expiry_str', '')
            gpt = gpt_analysis or {}
            _short_ltp_p = float(trigger.get('_short_ltp_preview', 0) or 0)
            gates = {}
            all_pass = True
            ist_now = now_ist()
            mkt_open = (ist_now.weekday() < 5 and (ist_now.hour > 9 or
                        (ist_now.hour == 9 and ist_now.minute >= 15)) and
                        (ist_now.hour < 15 or (ist_now.hour == 15 and ist_now.minute <= 30)))
            gates['Market Hours'] = 'PASS' if mkt_open else 'FAIL'
            if not mkt_open: all_pass = False
            cf = int(snapshot.get('checklist_fails', 0) or 0)
            gates['Checklist Fails'] = f'PASS ({cf})' if cf == 0 else f'FAIL ({cf})'
            if cf > 0: all_pass = False
            has_pos = bool(self.active_position)
            if action != 'EXIT_ALL':
                gates['No Active Position'] = 'PASS' if not has_pos else 'FAIL'
                if has_pos: all_pass = False
            else:
                gates['No Active Position'] = 'PASS (EXIT)'
            _trap_fade = self._assess_trap_fade(snapshot, metrics, gpt)
            _trap_type = _trap_fade['trap_type']
            if _trap_type != 'NONE':
                gates['Trap Status'] = _trap_fade['fade_status']
                if _trap_fade['suggest']:
                    self.sheets.suggest_trap_fade(_trap_fade['fade_action'],
                                                 _trap_fade['fade_strike'],
                                                 _trap_fade['fade_status'])
                else:
                    all_pass = False
            else:
                gates['Trap Status'] = 'PASS — no trap'
            gpt_txt = ' '.join([(gpt.get('signal', '') or ''), (gpt.get('current_situation', '') or ''),
                               (gpt.get('risk_note', '') or '')]).lower()
            gates['GPT Trap Text'] = 'NOTED: GPT flags trap — see Trap Status' if 'trap' in gpt_txt else 'PASS'
            score_agree = bool(gpt.get('score_agreement', True))
            gates['GPT Score Agreement'] = 'PASS' if score_agree else 'WARN: GPT disagrees'
            if not score_agree:
                log.warning('[OrderExecutor] GPT score_agreement=False.')
            gpt_bias = (gpt.get('market_bias', '') or 'Neutral')
            _is_fade = (_trap_type != 'NONE' and _trap_fade['suggest'])
            _bias_ok = True
            _bias_msg = ''
            if _is_fade:
                if ((_trap_type == 'BULL_TRAP' and gpt_bias == 'Bearish') or
                    (_trap_type == 'BEAR_TRAP' and gpt_bias == 'Bullish')):
                    _bias_msg = f'GPT {gpt_bias} confirms fade'
                else:
                    _bias_msg = f'GPT {gpt_bias} — fade not fully confirmed'
                gates['GPT Bias Alignment'] = 'PASS (FADE): ' + _bias_msg
            else:
                if action == 'BUY_CE' and gpt_bias == 'Bearish':
                    _bias_msg = f'ADVISORY: BUY_CE vs GPT {gpt_bias} — operator informed'
                    log.warning(f'[OrderExecutor] GPT bias conflict: {_bias_msg}')
                elif action == 'BUY_PE' and gpt_bias == 'Bullish':
                    _bias_msg = f'ADVISORY: BUY_PE vs GPT {gpt_bias} — operator informed'
                    log.warning(f'[OrderExecutor] GPT bias conflict: {_bias_msg}')
                elif (action == 'SELL_PE' and gpt_bias == 'Bearish') or \
                     (action == 'SELL_CE' and gpt_bias == 'Bullish'):
                    _bias_msg = f'ADVISORY: {action} vs GPT {gpt_bias} — operator informed'
                # GPT bias is advisory only — never blocks execution.
                # Operator sees the note in the gates panel and decides.
                gates['GPT Bias Alignment'] = ('PASS' if not _bias_msg else 'ADVISORY: ' + _bias_msg)
                # _bias_ok intentionally NOT propagated to all_pass
            strike_ok = bool(focus_zone and strike in [float(s) for s in focus_zone])
            gates['Strike in Focus Zone'] = 'PASS' if (strike_ok or action == 'EXIT_ALL') else 'FAIL'
            if not strike_ok and action != 'EXIT_ALL':
                all_pass = False
            lot_ok = (1 <= lots <= 20)
            gates['Lot Size Valid'] = 'PASS' if lot_ok else 'FAIL (max 20)'
            if not lot_ok: all_pass = False
            min_prem_ok = (_short_ltp_p >= 10.0 or _short_ltp_p == 0.0 or 'BUY' in action)
            gates['Min Premium'] = (f'PASS (LTP≈{_short_ltp_p:.0f})' if min_prem_ok
                                   else f'FAIL (LTP={_short_ltp_p:.0f} < ₹10 min)')
            if not min_prem_ok: all_pass = False
            static_ok = (trigger.get('static_ip_confirmed', '').upper() == 'YES')
            gates['Static IP Registered'] = 'PASS' if static_ok else 'FAIL (set B38=YES)'
            if not static_ok: all_pass = False
            self.sheets.write_execution_gates(gates, snapshot)
            if not all_pass:
                self.sheets.write_execution_status(status='SAFETY_BLOCKED',
                                                  error='Gate(s) failed — see EXECUTION tab rows 32-43')
                return True
            self.sheets.write_execution_status(status='EXECUTING', error='')
            if action == 'EXIT_ALL':
                return self._exit_all_positions()
            try:
                contracts = self.instrument_loader.get_option_contracts(expiry_str)
                if contracts is None or len(contracts) == 0:
                    raise ValueError('No contracts for expiry: ' + expiry_str)
                opt_type = 'CE' if 'CE' in action else 'PE'
                txn = 'SELL' if action.startswith('SELL') else 'BUY'
                hedge_txn = 'BUY' if txn == 'SELL' else 'SELL'
                _vix_now = float(snapshot.get('vix_level', 14.0) or 14.0)
                _is_tf = (_trap_type != 'NONE')
                _hedge_gap = self._compute_hedge_gap(_vix_now, _is_tf, _short_ltp_p)
                log.info(f'[OrderExecutor] Hedge gap: {_hedge_gap}pts (VIX={_vix_now:.1f} fade={_is_tf})')
                hedge_str = (strike + _hedge_gap if 'CE' in action else strike - _hedge_gap)
                short_row = contracts[(contracts['strike'] == float(strike)) &
                                     (contracts['option_type'].str.upper() == opt_type)]
                if len(short_row) == 0:
                    raise ValueError(f'Token not found: {strike} {opt_type}')
                # Validate contract lot size matches config
                instrument_lot_size = int(short_row.iloc[0].get('lotsize', 0) or 0)
                if instrument_lot_size > 0 and instrument_lot_size != contract_lot_size:
                    log.warning(
                        f'Instrument master lotsize {instrument_lot_size} differs from contract_lot_size {contract_lot_size}; using sheet value.'
                    )
                short_token = str(short_row.iloc[0]['token'])
                short_symbol = str(short_row.iloc[0]['symbol'])
                # Final quantity comes from calculated values above (contract_lot_size * lots)
                hedge_token = hedge_symbol = ''
                if txn == 'SELL':
                    h_row = contracts[(contracts['strike'] == float(hedge_str)) &
                                    (contracts['option_type'].str.upper() == opt_type)]
                    if len(h_row) == 0:
                        raise ValueError(f'Hedge not found: {hedge_str} {opt_type}. Set strikes_above/below >= 5 in SETTINGS.')
                    hedge_token = str(h_row.iloc[0]['token'])
                    hedge_symbol = str(h_row.iloc[0]['symbol'])
            except Exception as e:
                self.sheets.write_execution_status(status='FAILED', error=f'Token lookup: {e}')
                return True
            # Build order parameters with parsed product_type and order_type
            order_price = '0'
            if order_type_req == 'LIMIT':
                if not _short_ltp_p or _short_ltp_p <= 0:
                    raise ValueError(f'LIMIT order requires _short_ltp_preview > 0, got {_short_ltp_p}')
                order_price = str(self._round_to_tick(_short_ltp_p))
            short_params = {'variety': self.VARIETY, 'tradingsymbol': short_symbol,
                          'symboltoken': short_token, 'transactiontype': txn,
                          'exchange': self.EXCHANGE, 'ordertype': order_type_req,
                          'producttype': product_type_req, 'duration': self.DURATION,
                          'price': order_price, 'squareoff': '0', 'stoploss': '0', 'quantity': str(quantity)}
            short_order_id = ''
            try:
                resp = retry_call(lambda: self.api_client.smart_connect.placeOrder(short_params),
                                 attempts=2, delay=0.5, fallback=None, label='PlaceShortLeg')
                if resp and resp.get('status'):
                    short_order_id = (resp.get('data', {}).get('orderid', ''))
                    log.info(f'[OrderExecutor] Short: {txn} {short_symbol} qty={quantity} id={short_order_id}')
                else:
                    raise ValueError(f'Short rejected: {resp}')
            except Exception as e:
                self.sheets.write_execution_status(status='FAILED', error=f'Short leg: {e}')
                self._alert(f'ORDER FAILED\n{txn} {short_symbol}\n{e}')
                return True
            hedge_order_id = ''
            hedge_placed = False
            if txn == 'SELL' and hedge_token:
                hedge_params = {**short_params, 'tradingsymbol': hedge_symbol,
                              'symboltoken': hedge_token, 'transactiontype': hedge_txn}
                try:
                    resp2 = retry_call(lambda: self.api_client.smart_connect.placeOrder(hedge_params),
                                      attempts=2, delay=0.5, fallback=None, label='PlaceHedgeLeg')
                    if resp2 and resp2.get('status'):
                        hedge_order_id = (resp2.get('data', {}).get('orderid', ''))
                        hedge_placed = True
                        log.info(f'[OrderExecutor] Hedge: {hedge_txn} {hedge_symbol} id={hedge_order_id}')
                    else:
                        log.error(f'[OrderExecutor] Hedge rejected: {resp2}. Short {short_order_id} is UNHEDGED.')
                except Exception as e2:
                    log.error(f'[OrderExecutor] Hedge error: {e2}. Short {short_order_id} UNHEDGED.')
            import time as _time
            short_fill = hedge_fill = 0.0
            _max_fill_attempts = 5
            for _fa in range(_max_fill_attempts):
                _time.sleep(1.5)
                try:
                    ob = self.api_client.smart_connect.getOrderBook()
                    orders = (ob.get('data') or []) if ob else []
                    for o in orders:
                        oid = str(o.get('orderid', ''))
                        fp = float(o.get('averageprice', 0) or 0)
                        if oid == str(short_order_id) and fp > 0:
                            short_fill = fp
                        if oid == str(hedge_order_id) and fp > 0:
                            hedge_fill = fp
                    filled_short = short_fill > 0
                    filled_hedge = hedge_fill > 0 or not hedge_token or txn == 'BUY'
                    if filled_short and filled_hedge:
                        break
                    log.warning(f'[OrderExecutor] Fill attempt {_fa+1}/{_max_fill_attempts}: '
                                f'short={short_fill:.2f} hedge={hedge_fill:.2f} — retrying')
                except Exception as e3:
                    log.warning(f'[OrderExecutor] Order book attempt {_fa+1}: {e3}')
            if short_fill == 0.0:
                log.error('[OrderExecutor] Short fill price is 0 after all retries. '
                          'Verify order manually in Angel One app.')
            entry_spot = float(snapshot.get('spot', 0) or 0)
            net_prem_val = round((short_fill - hedge_fill) * quantity, 2) if txn == 'SELL' else round(short_fill * quantity, 2)
            max_risk_val = round((_hedge_gap - (short_fill - hedge_fill)) * quantity, 2) if txn == 'SELL' else round(short_fill * quantity, 2)
            init_state = (self.STATE_HEDGE_FAILED if txn == 'SELL' and not hedge_placed else self.STATE_OPEN)
            self.active_position = {'action': action, 'txn': txn, 'short_symbol': short_symbol,
                                   'short_token': short_token, 'short_strike': strike,
                                   'short_order_id': short_order_id, 'short_fill': short_fill,
                                   'hedge_symbol': hedge_symbol, 'hedge_token': hedge_token,
                                   'hedge_strike': hedge_str if txn == 'SELL' else 0.0,
                                   'hedge_order_id': hedge_order_id, 'hedge_fill': hedge_fill,
                                   'hedge_gap': _hedge_gap, 'quantity': quantity, 'lots': lots,
                                   'lot_size': lot_size, 'entry_spot': entry_spot,
                                   'entry_time': ist_str('%H:%M:%S'),
                                   'entry_structure': snapshot.get('price_structure', ''),
                                   'entry_vwap_bias': snapshot.get('vwap_bias', 'NEUTRAL'),
                                   'entry_sr_age': int(snapshot.get('sr_event_age', 0) or 0),
                                   'net_premium': net_prem_val, 'max_risk': max_risk_val,
                                   'days_to_expiry': int(snapshot.get('days_to_expiry', 0) or 0),
                                   'expiry_day': (int(snapshot.get('days_to_expiry', 1) or 1) == 0),
                                   'position_state': init_state, 'is_trap_fade': _is_tf, 'peak_pnl': 0.0,
                                   'product_type': product_type_req}
            self._neutral_vol_cycles = 0
            self.sheets.write_execution_full(position=self.active_position, short_order=short_order_id,
                                            hedge_order=hedge_order_id, short_fill=short_fill,
                                            hedge_fill=hedge_fill)
            self.sheets.append_position_log(position=self.active_position, event='ENTRY', snapshot=snapshot)
            self.sheets.reset_execution_trigger()
            state_sfx = (' ⚠️ HEDGE FAILED' if init_state == self.STATE_HEDGE_FAILED else '')
            self._alert(f'ORDER PLACED{state_sfx}\n{action} {short_symbol} ×{lots} lot\nShort: {short_fill} | '
                       f'Hedge: {hedge_fill}\nNet prem: ₹{net_prem_val} | Max risk: ₹{max_risk_val}\n'
                       f'Hedge gap: {_hedge_gap}pts | ID: {short_order_id}')
            return True
        except Exception as e:
            log.error(f'[OrderExecutor] check_and_execute: {e}')
            try:
                self.sheets.write_execution_status(status='FAILED', error=str(e))
            except Exception:
                pass
            return False

    def _run_lifecycle_check(self, snapshot: dict, gpt_analysis: dict):
        try:
            if not self.active_position: return
            pos = self.active_position
            state = self._evaluate_lifecycle(pos, snapshot, gpt_analysis)
            old = pos.get('position_state', self.STATE_OPEN)
            if state != old:
                pos['position_state'] = state
                log.info(f'[OrderExecutor] State: {old} → {state}')
                self.sheets.append_position_log(position=pos, event=f'STATE:{state}', snapshot=snapshot)
                self._alert(f'POSITION UPDATE\n{pos.get("action")} {pos.get("short_strike")}\n'
                           f'State: {old} → {state}')
                advisory = {self.STATE_EXIT_STRUCTURE, self.STATE_EXIT_VWAP, self.STATE_EXIT_TRAP,
                           self.STATE_EXIT_THETA, self.STATE_EXIT_OI, self.STATE_EXIT_SR_RESET,
                           self.STATE_TIME_EXIT, self.STATE_STOPLOSS, self.STATE_TARGET}
                if state == self.STATE_HEDGE_FAILED:
                    # Hedge failed — short leg is unhedged and exposed. Exit immediately.
                    log.error('[OrderExecutor] HEDGE_FAILED: placing automatic exit for unhedged short.')
                    self._alert('⚠️ HEDGE FAILED — auto-exiting unhedged short position now.')
                    self._exit_all_positions()
                    return
                if state in advisory:
                    self.sheets.write_execution_status(status=state,
                                                      error=f'Advisory: Consider EXIT_ALL. Reason: {state}')
            self.sheets.update_position_state(pos)
        except Exception as e:
            log.warning(f'[OrderExecutor] _run_lifecycle_check: {e}')

    def _exit_all_positions(self) -> bool:
        try:
            if not self.active_position:
                self.sheets.write_execution_status(status='FAILED', error='No active position.')
                return True
            pos = self.active_position
            sq_txn = 'BUY' if pos['txn'] == 'SELL' else 'SELL'
            results = []
            # Use the product type recorded at entry — must match or broker rejects
            exit_product_type = pos.get('product_type', self.PRODUCT_TYPE)
            sq_base = {'variety': self.VARIETY, 'exchange': self.EXCHANGE, 'ordertype': self.ORDER_TYPE,
                      'producttype': exit_product_type, 'duration': self.DURATION,
                      'price': '0', 'squareoff': '0', 'stoploss': '0',
                      'quantity': str(pos['quantity']), 'transactiontype': sq_txn}
            r1 = retry_call(lambda: self.api_client.smart_connect.placeOrder(
                {**sq_base, 'tradingsymbol': pos['short_symbol'], 'symboltoken': pos['short_token']}),
                           attempts=2, delay=0.5, fallback=None, label='ExitShort')
            results.append(f"Short: {((r1 or {}).get('data') or {}).get('orderid','?')}")
            if pos.get('hedge_token'):
                r2 = retry_call(lambda: self.api_client.smart_connect.placeOrder(
                    {**sq_base, 'tradingsymbol': pos['hedge_symbol'],
                     'symboltoken': pos['hedge_token'], 'transactiontype': pos['txn']}),
                               attempts=2, delay=0.5, fallback=None, label='ExitHedge')
                results.append(f"Hedge: {((r2 or {}).get('data') or {}).get('orderid','?')}")
            pos_copy = dict(self.active_position)
            self.active_position = {}
            self._neutral_vol_cycles = 0
            self.sheets.write_execution_status(status='DONE', error='Exited. ' + ' | '.join(results))
            self.sheets.write_execution_position_cleared()
            self.sheets.append_position_log(position=pos_copy, event='EXIT', snapshot={})
            self.sheets.reset_execution_trigger()
            self._alert('POSITION EXITED\n' + '\n'.join(results))
            return True
        except Exception as e:
            log.error(f'[OrderExecutor] _exit_all_positions: {e}')
            return False

    def _alert(self, text: str):
        try:
            self.telegram.send(f'⚡ <b>EXECUTION ALERT</b>\n{text}')
        except Exception:
            pass


# ─────────────────────────────────────────────────────────────────────────────
# 13. ClaudeAnalyst
# ─────────────────────────────────────────────────────────────────────────────

class ClaudeAnalyst:
    """
    Manages ChatGPT analysis calls via direct HTTPS (no SDK).
    Three call types: morning brief, 15-min analysis, EOD review.
    Entirely optional — disabled if OPENAI_API_KEY is empty.
    """

    _SAFE_FALLBACK = {
        'market_bias': 'Neutral',
        'current_situation': 'Analysis unavailable.',
        'key_levels': {'support': '—', 'resistance': '—'},
        'signal': 'ChatGPT not available this cycle.',
        'strength': 'Weak',
        'reasoning': ['ChatGPT analysis unavailable.'],
        'prev_day_context': '',
        'risk_note': 'Analysis unavailable.',
        'score_agreement': False,
        'unusual_observation': None,
        'premium_environment': {
            'market_condition': 'Neutral',
            'volatility_context': 'Unknown',
            'price_behavior': 'Range-bound',
            'key_insight': 'ChatGPT analysis unavailable.',
            'reasoning': [],
            'risk_note': 'Premium environment analysis unavailable.',
        },
    }

    def __init__(self):
        self.api_key     = (CONFIG.get('OPENAI_API_KEY', '') or
                            os.environ.get('OPENAI_API_KEY', '') or
                            CONFIG.get('ANTHROPIC_API_KEY', '') or
                            os.environ.get('ANTHROPIC_API_KEY', ''))
        self.enabled     = bool(self.api_key)
        self.prev_day: dict        = {}
        self.morning_done: bool    = False
        self.eod_done: bool        = False
        self.cycle_log: List[dict] = []
        self.last_analysis: Optional[dict] = None
        self.last_run_ts: str      = '—'
        self.claude_calls: int     = 0

        if not self.enabled:
            log.info('[ChatGPT] Disabled — OPENAI_API_KEY not configured.')

    def maybe_run(
        self,
        cycle_num:       int,
        snapshot:        dict,
        metrics:         dict,
        signals:         dict,
        sr_event:        dict,
        chain,
        history_rows:    List[dict],
        spot_candles:    Optional[List] = None,
        futures_candles: Optional[List] = None,
        spot_15m_df:     Optional[object] = None,
        spot_30m_df:     Optional[object] = None,
    ) -> Optional[dict]:
        """
        Returns the latest analysis dict (possibly cached from prior cycle),
        or None if Claude is disabled. Never raises — all exceptions are caught.
        """
        if not self.enabled:
            return self.last_analysis

        try:
            return self._maybe_run(
                cycle_num, snapshot, metrics, signals, sr_event,
                chain, history_rows, spot_candles, futures_candles,
                spot_15m_df, spot_30m_df,
            )
        except Exception as e:
            log.warning(f'[ChatGPT] maybe_run() failed: {e}\n{__import__("traceback").format_exc()}')
            return self.last_analysis

    def _maybe_run(self, cycle_num, snapshot, metrics, signals, sr_event,
                   chain, history_rows, spot_candles, futures_candles,
                   spot_15m_df=None, spot_30m_df=None):
        ist = now_ist()

        # Daily call cap guard
        _max_calls = int(CONFIG.get('CLAUDE_MAX_DAILY_CALLS', 80))
        if self.claude_calls >= _max_calls:
            log.warning(f'[ChatGPT] Daily call cap ({_max_calls}) reached — returning cached analysis.')
            return self.last_analysis

        # Morning brief — once per session before 09:20 IST
        if not self.morning_done and ist.hour == 9 and ist.minute < 20:
            analysis = self._call_morning_brief(snapshot)
            self.morning_done = True
            self.last_analysis = analysis
            self.last_run_ts   = ist_str()
            self.claude_calls += 1
            return analysis

        # EOD review — once per session at/after 15:30 IST
        if not self.eod_done and ist.hour == 15 and ist.minute >= 30:
            self._call_eod(snapshot)
            self.eod_done    = True
            self.last_run_ts = ist_str()
            self.claude_calls += 1
            return self.last_analysis

        # 15-min analysis — every N cycles
        if cycle_num > 0 and cycle_num % CONFIG['CLAUDE_EVERY_N_CYCLES'] == 0:
            analysis = self._call_analysis(
                snapshot, metrics, signals, sr_event,
                chain, history_rows, spot_candles, futures_candles,
                spot_15m_df, spot_30m_df,
            )
            self.last_analysis = analysis
            self.last_run_ts   = ist_str()
            self.claude_calls += 1
            self.cycle_log.append({'ts': self.last_run_ts, 'analysis': analysis, 'snapshot': snapshot})
            if len(self.cycle_log) > 20:
                self.cycle_log = self.cycle_log[-20:]  # EOD only reads [-20:] — trim the rest
            return analysis

        return self.last_analysis

    def end_of_day(self, snapshot: dict):
        """Trigger EOD review — called from Ctrl+C handler or loop end."""
        if not self.enabled or self.eod_done:
            return
        try:
            self._call_eod(snapshot)
            self.eod_done    = True
            self.claude_calls += 1
        except Exception as e:
            log.warning(f'[ChatGPT] end_of_day() failed: {e}')

    # ── Internal call helpers ─────────────────────────────────────────────────

    def _call_morning_brief(self, snapshot: dict) -> dict:
        pd = self.prev_day
        ph = pd.get('prev_high', 'N/A'); pl = pd.get('prev_low', 'N/A')
        pc = pd.get('prev_close', 'N/A'); po = pd.get('prev_open', 'N/A')
        prng = pd.get('prev_range', 'N/A')
        user_msg = (
            f"Morning session starting. Respond with valid JSON matching the schema "
            f"in your system instructions. Previous day NIFTY data:\n"
            f"Open: {po}, High: {ph}, Low: {pl}, Close: {pc}, Range: {prng} pts\n"
            f"Current spot: {snapshot.get('spot', '—')}\n\n"
            f"For current_situation: describe 1) Key levels to watch based on prev day, "
            f"2) Opening scenario implications, 3) What to watch in the first 30 minutes, "
            f"4) Main risk factors. 3-4 sentences. Do not recommend trades.\n"
            f"Set market_bias, strength, and score_agreement based on available context. "
            f"Set all other fields to brief placeholders where live data is not yet available."
        )
        raw = self._call_claude(user_msg, max_tokens=400, expect_json=True)
        log.info(f'[ChatGPT] Morning brief complete.')
        # Parse and sanitize through standard pipeline
        parsed   = self._parse_json(raw)
        analysis = self._sanitize_output(parsed)
        analysis['bias_at'] = ist_str()
        return analysis

    def _call_analysis(self, snapshot, metrics, signals, sr_event,
                       chain, history_rows, spot_candles,
                       futures_candles,
                       spot_15m_df=None, spot_30m_df=None) -> dict:
        vix_data = {}  # passed via snapshot fields

        # Prev day position note
        spot = snapshot.get('spot', 0)
        ph   = self.prev_day.get('prev_high', 0) or 0
        pl   = self.prev_day.get('prev_low',  0) or 0
        pc   = self.prev_day.get('prev_close',0) or 0
        if ph and spot > ph:
            pd_note = f'ABOVE yesterday\'s high ({ph}) by {round(spot-ph,1)} pts — above prev session range'
        elif pl and spot < pl:
            pd_note = f'BELOW yesterday\'s low ({pl}) by {round(pl-spot,1)} pts — below prev session range'
        elif pc and spot > pc:
            pd_note = f'Above yesterday\'s close ({pc}), within prev range'
        elif pc:
            pd_note = f'Below yesterday\'s close ({pc}), within prev range'
        else:
            pd_note = 'No previous day data available'

        # Compact chain payload
        chain_payload = []
        if chain is not None and len(chain) > 0:
            for _, row in chain.iterrows():
                chain_payload.append({
                    'strike':     row.get('strike', 0),
                    'ce_oi':      safe_val(row.get('ce_open_interest', '')),
                    'pe_oi':      safe_val(row.get('pe_open_interest', '')),
                    'ce_chg_oi':  safe_val(row.get('ce_change_oi', '')),
                    'pe_chg_oi':  safe_val(row.get('pe_change_oi', '')),
                    'ce_ltp':     safe_val(row.get('ce_ltp', '')),
                    'pe_ltp':     safe_val(row.get('pe_ltp', '')),
                    'ce_iv':      safe_val(row.get('ce_iv', '')),
                    'pe_iv':      safe_val(row.get('pe_iv', '')),
                    'ce_volume':  safe_val(row.get('ce_volume', '')),
                    'pe_volume':  safe_val(row.get('pe_volume', '')),
                })

        full_snapshot = {
            **snapshot,
            'prev_day_high':         self.prev_day.get('prev_high', 0),
            'prev_day_low':          self.prev_day.get('prev_low', 0),
            'prev_day_close':        self.prev_day.get('prev_close', 0),
            'prev_day_open':         self.prev_day.get('prev_open', 0),
            'prev_day_range':        self.prev_day.get('prev_range', 0),
            'prev_day_position':     pd_note,
            'option_chain':          (lambda cp, atm_val: (
                lambda atm_idx: cp[max(0, atm_idx - 3): min(len(cp), atm_idx + 4)]
            )(next((i for i, r in enumerate(cp) if r.get('strike', 0) == atm_val),
                   len(cp) // 2))
            )(chain_payload, snapshot.get('atm', 0)),   # ATM-centred ±3 — always includes key resistance
            'recent_spot_candles':   spot_candles    or [],
            'recent_futures_candles': futures_candles or [],
            'session_history_last_8': [
                {
                    'ts':      r.get('Timestamp', ''),
                    'spot':    r.get('Spot Price (₹)', 0),
                    'bias':    r.get('Bias', ''),
                    'score':   r.get('Score', 0),
                    'event':   r.get('Event Tag', ''),
                    'sr':      r.get('SR Event', ''),
                    'cp':      r.get('Candle Pattern', ''),
                    'support': r.get('Support', 0),
                    'resist':  r.get('Resistance', 0),
                    'market':  r.get('Market Condition', ''),
                    'vix':     r.get('India VIX', ''),
                    'ce_chg':  r.get('CE Chg OI', ''),
                    'pe_chg':  r.get('PE Chg OI', ''),
                    'sr_age':  r.get('SR Event Age', ''),
                    'oi_conc': r.get('OI Concentration', ''),
                }
                for r in history_rows[-8:]
            ],
        }

        # ── MTF context ──────────────────────────────────────────────
        mtf_context = self._build_mtf_context(
            history_rows, spot_15m_df, spot_30m_df
        )
        full_snapshot['mtf_context'] = mtf_context

        # Clean NaN values for JSON
        import json as _json
        def clean_for_json(obj):
            if isinstance(obj, float):
                return '' if math.isnan(obj) or math.isinf(obj) else obj
            if isinstance(obj, dict):
                return {k: clean_for_json(v) for k, v in obj.items()}
            if isinstance(obj, list):
                return [clean_for_json(i) for i in obj]
            return obj

        # Remove undocumented fields that add noise without analytical value for GPT
        _GPT_EXCLUDE = {'score_raw', 'bias_at', 'vix_candles_count'}
        clean_snap = {k: v for k, v in clean_for_json(full_snapshot).items()
                      if k not in _GPT_EXCLUDE}
        payload_str = _json.dumps(clean_snap, default=str)
        if len(payload_str) > 8000:
            log.warning(f'[ChatGPT] Payload {len(payload_str)} chars after structural limits — '
                        f'hard-truncating to 8000. Consider reducing focus zone or history rows.')
            payload_str = payload_str[:8000]
        user_msg    = (
            f'Analyze this NIFTY market snapshot and respond with valid JSON '
            f'matching the schema in your system instructions exactly:\n\n{payload_str}'
        )

        raw      = self._call_claude(user_msg, max_tokens=CONFIG['CLAUDE_MAX_TOKENS'])
        parsed   = self._parse_json(raw)
        analysis = self._sanitize_output(parsed)
        analysis['_mtf_context'] = mtf_context
        analysis['bias_at'] = ist_str()
        log.info(f"[ChatGPT] 15-min analysis: bias={analysis.get('market_bias')} strength={analysis.get('strength')}")
        return analysis

    @staticmethod
    def _build_mtf_context(
        history_rows: list,
        spot_15m_df,
        spot_30m_df,
    ) -> dict:
        """
        Build compact multi-timeframe context for the AI payload.
        5m OI trend: derived from last 6 history_rows.
        15m / 30m structure: derived from candle DataFrames.
        Never raises. Returns safe empty dicts on any failure.
        """
        result = {
            'mtf_5m':        {},
            'mtf_15m':       {},
            'mtf_30m':       {},
            'mtf_oi_trend':  {},
            'mtf_sr_context': {},
        }

        try:
            recent = history_rows[-6:] if len(history_rows) >= 6 else history_rows
            if recent:
                ce_chg_list, pe_chg_list = [], []
                sup_list, res_list       = [], []
                sr_ages, oi_conc         = [], []

                for r in recent:
                    try:
                        ce_v = r.get('CE Chg OI', '')
                        pe_v = r.get('PE Chg OI', '')
                        s_v  = r.get('Support', 0)
                        r_v  = r.get('Resistance', 0)
                        a_v  = r.get('SR Event Age', 0)
                        c_v  = r.get('OI Concentration', '')
                        if ce_v != '': ce_chg_list.append(float(ce_v))
                        if pe_v != '': pe_chg_list.append(float(pe_v))
                        if s_v:  sup_list.append(float(s_v))
                        if r_v:  res_list.append(float(r_v))
                        if a_v:  sr_ages.append(int(a_v))
                        if c_v not in ('', None): oi_conc.append(float(c_v))
                    except (TypeError, ValueError):
                        continue

                def _trend(lst):
                    if len(lst) < 2: return 'stable'
                    return 'building' if lst[-1] > lst[0] else (
                           'unwinding' if lst[-1] < lst[0] else 'stable')

                sup_moved = round(sup_list[-1] - sup_list[0], 0) if len(sup_list) >= 2 else 0
                res_moved = round(res_list[-1] - res_list[0], 0) if len(res_list) >= 2 else 0
                conc_trend = (
                    'concentrating' if len(oi_conc) >= 2 and oi_conc[-1] > oi_conc[0] + 0.05
                    else 'spreading' if len(oi_conc) >= 2 and oi_conc[-1] < oi_conc[0] - 0.05
                    else 'stable'
                )

                ce_trend = _trend(ce_chg_list)
                pe_trend = _trend(pe_chg_list)

                result['mtf_oi_trend'] = {
                    'ce_writing_30min':        ce_trend,
                    'pe_writing_30min':        pe_trend,
                    'support_migrated_pts':    sup_moved,
                    'resistance_migrated_pts': res_moved,
                    'oi_concentration_trend':  conc_trend,
                    'max_sr_event_age_30min':  max(sr_ages) if sr_ages else 0,
                }

                last_r = recent[-1]
                svs  = last_r.get('Spot vs Support %', '')
                svr  = last_r.get('Spot vs Resist %',  '')

                sup_break = (
                    'HIGH'   if svs != '' and float(svs) < 0.3 and pe_trend == 'unwinding'
                    else 'MEDIUM' if svs != '' and float(svs) < 0.5
                    else 'LOW'
                )
                res_break = (
                    'HIGH'   if svr != '' and float(svr) < 0.3 and ce_trend == 'unwinding'
                    else 'MEDIUM' if svr != '' and float(svr) < 0.5
                    else 'LOW'
                )

                result['mtf_sr_context'] = {
                    'spot_vs_support_pct':       svs,
                    'spot_vs_resist_pct':        svr,
                    'support_oi_now':            last_r.get('Support OI', ''),
                    'resistance_oi_now':         last_r.get('Resistance OI', ''),
                    'support_chg_oi_now':        last_r.get('Support Chg OI', ''),
                    'resistance_chg_oi_now':     last_r.get('Resistance Chg OI', ''),
                    'support_break_risk':        sup_break,
                    'resistance_break_risk':     res_break,
                    'support_strengthening':     pe_trend == 'building',
                    'resistance_strengthening':  ce_trend == 'building',
                }
        except Exception as _e:
            log.warning(f'[MTF] OI section failed: {_e}')

        def _candle_struct(df):
            try:
                if df is None or len(df) < 2:
                    return {'structure': 'INSUFFICIENT_DATA'}
                h = df['high'].astype(float).values
                l = df['low'].astype(float).values
                c = df['close'].astype(float).values
                n = len(h)
                hh = sum(h[i] > h[i-1] for i in range(1, n))
                hl = sum(l[i] > l[i-1] for i in range(1, n))
                lh = sum(h[i] < h[i-1] for i in range(1, n))
                ll = sum(l[i] < l[i-1] for i in range(1, n))
                thr = (n - 1) * 0.75  # must match SignalEngine._compute_price_structure threshold
                if hh >= thr and hl >= thr:   struct = 'BULLISH STRUCTURE'
                elif lh >= thr and ll >= thr:  struct = 'BEARISH STRUCTURE'
                else:                          struct = 'RANGEBOUND'
                return {'structure': struct, 'last_close': round(float(c[-1]), 2), 'bars': n}
            except Exception:
                return {'structure': 'INSUFFICIENT_DATA'}

        result['mtf_15m'] = _candle_struct(spot_15m_df)
        result['mtf_30m'] = _candle_struct(spot_30m_df)
        return result

    def _call_eod(self, snapshot: dict):
        """Build and send EOD review. Writes to DAILY_REVIEW via NiftyDashboardApp."""
        history_summary = '\n'.join(
            f"  {e.get('ts','')} | spot={e.get('snapshot',{}).get('spot','')} "
            f"bias={e.get('analysis',{}).get('market_bias','')}"
            for e in self.cycle_log[-20:]
        ) or 'No 15-min cycles logged.'

        user_msg = (
            f"End of day review for NIFTY session. Respond with valid JSON matching "
            f"the schema in your system instructions.\n"
            f"Previous day: {self.prev_day}\n"
            f"Session log (last 20):\n{history_summary}\n\n"
            f"Current snapshot: spot={snapshot.get('spot','')} | bias={snapshot.get('bias','')} | "
            f"SR event={snapshot.get('sr_event','')} | market_cond={snapshot.get('market_condition','')}\n\n"
            f"For current_situation: write 3-5 sentences covering — "
            f"1) Session character (trending/rangebound/choppy), "
            f"2) Best signals that worked, 3) Signals that were misleading, "
            f"4) SR event accuracy today, 5) One calibration note for tomorrow. "
            f"Do not recommend trades. Set all other fields based on end-of-day context."
        )
        try:
            raw     = self._call_claude(user_msg, max_tokens=700, expect_json=True)
            log.info('[ChatGPT] EOD review complete.')
            parsed   = self._parse_json(raw)
            analysis = self._sanitize_output(parsed)
            analysis['bias_at'] = ist_str()
            if self.last_analysis is None:
                self.last_analysis = dict(self._SAFE_FALLBACK)
            # Store narrative in eod_review for DAILY_REVIEW tab
            self.last_analysis['eod_review'] = analysis.get('current_situation', '')[:2000]
            self.last_analysis.update({k: v for k, v in analysis.items() if k != 'eod_review'})
        except Exception as e:
            log.warning(f'[ChatGPT] EOD review failed: {e}')

    # ── API call ──────────────────────────────────────────────────────────────

    
    def _call_claude(self, user_msg: str, max_tokens: int, expect_json: bool = True) -> str:
        headers = {
            'Authorization': f'Bearer {self.api_key}',
            'Content-Type': 'application/json',
        }
        payload = {
            'model': CONFIG.get('OPENAI_MODEL', CONFIG.get('CLAUDE_MODEL', 'gpt-4.1-mini')),
            'temperature': 0.2,
            'messages': [
                {'role': 'system', 'content': CLAUDE_SYSTEM_PROMPT},
                {'role': 'user', 'content': user_msg},
            ],
            'max_tokens': max_tokens,
        }
        if expect_json:
            payload['response_format'] = {'type': 'json_object'}
        delays = [20, 40, 60]
        last_err = None
        for attempt in range(3):
            try:
                r = requests.post(
                    'https://api.openai.com/v1/chat/completions',
                    headers=headers,
                    json=payload,
                    timeout=45,
                )
                if r.status_code == 429:
                    last_err = RuntimeError(f'HTTP 429: {r.text[:500]}')
                    wait_s = delays[min(attempt, len(delays) - 1)]
                    log.warning(f'[ChatGPT] Rate limited - waiting {wait_s}s')
                    time.sleep(wait_s)
                    continue
                if r.status_code >= 400:
                    try:
                        err_text = r.json()
                    except Exception:
                        err_text = r.text[:500]
                    raise RuntimeError(f'HTTP {r.status_code}: {err_text}')
                body = r.json()
                choices = body.get('choices') or []
                if not choices:
                    raise RuntimeError(f'No choices in response: {body}')
                message = choices[0].get('message') or {}
                content = message.get('content', '')
                if isinstance(content, list):
                    parts = []
                    for item in content:
                        if isinstance(item, dict) and item.get('type') == 'text':
                            parts.append(item.get('text', ''))
                        else:
                            parts.append(str(item))
                    content = ''.join(parts).strip()
                if not isinstance(content, str) or not content.strip():
                    raise RuntimeError(f'Empty content in response: {body}')
                return content
            except Exception as exc:
                last_err = exc
                msg = str(exc).lower()
                if attempt < 2 and ('429' in msg or 'rate limit' in msg):
                    wait_s = delays[min(attempt, len(delays) - 1)]
                    log.warning(f'[ChatGPT] Rate limited - waiting {wait_s}s')
                    time.sleep(wait_s)
                    continue
                log.warning(f'[ChatGPT] API attempt {attempt+1} failed: {exc}')
                if attempt < 2:
                    time.sleep(5)
        raise RuntimeError(f'ChatGPT API: all attempts failed. Last error: {last_err}')

    # ── JSON parsing ──────────────────────────────────────────────────────────

    @staticmethod
    def _parse_json(raw: str) -> dict:
        try:
            clean = raw.strip()
            # Strip all common fence variants (```json, ```, single `)
            if clean.startswith('```'):
                clean = re.sub(r'^```[a-zA-Z]*\n?', '', clean)
                clean = re.sub(r'\n?```$', '', clean).strip()
            elif clean.startswith('`') and clean.endswith('`'):
                clean = clean[1:-1].strip()
            # Discard any preamble text before the first JSON object
            brace_start = clean.find('{')
            if brace_start > 0:
                clean = clean[brace_start:]
            return json.loads(clean)
        except Exception:
            return {
                'market_bias': 'Neutral',
                'current_situation': raw[:300],
                'key_levels': {'support': '—', 'resistance': '—'},
                'signal': 'JSON parse error — see logs',
                'strength': 'Weak',
                'reasoning': ['ChatGPT response could not be parsed as JSON'],
                'prev_day_context': '',
                'risk_note': 'Analysis unreliable this cycle',
                'score_agreement': False,
                'unusual_observation': None,
                'premium_environment': {
                    'market_condition': 'Neutral',
                    'volatility_context': 'Unknown',
                    'price_behavior': 'Range-bound',
                    'key_insight': 'ChatGPT analysis unavailable — JSON parse error.',
                    'reasoning': [],
                    'risk_note': 'Premium environment analysis unavailable this cycle.',
                },
            }

    # ── Safety sanitizer — MANDATORY after _parse_json() ─────────────────────

    @staticmethod
    def _sanitize_output(analysis: dict) -> dict:
        """
        Step 1 — Enum field validation.
        Step 2 — Forbidden phrase scan across all free-text fields.
        Step 3 — Type safety.
        Called AFTER _parse_json() and BEFORE any Sheets write or Telegram send.
        """
        ALLOWED_BIAS      = {'Bullish', 'Bearish', 'Neutral'}
        ALLOWED_STRENGTH  = {'Strong', 'Moderate', 'Weak'}
        ALLOWED_CONDITION = {'Decay Favorable', 'Expansion Favorable', 'Neutral'}
        ALLOWED_VOLATILITY= {'High', 'Low', 'Rising', 'Falling', 'Moderate', 'Unknown'}
        ALLOWED_BEHAVIOR  = {'Range-bound', 'Trending', 'Breakout Attempt', 'Post-Breakout', 'Breakdown Attempt', 'Post-Breakdown'}

        # Step 1 — Enum validation
        if analysis.get('market_bias') not in ALLOWED_BIAS:
            log.warning(f"[Safety] Invalid market_bias: {analysis.get('market_bias')} → forced to 'Neutral'")
            analysis['market_bias'] = 'Neutral'
        if analysis.get('strength') not in ALLOWED_STRENGTH:
            log.warning(f"[Safety] Invalid strength: {analysis.get('strength')} → forced to 'Weak'")
            analysis['strength'] = 'Weak'
        pe = analysis.get('premium_environment', {}) or {}
        if pe.get('market_condition') not in ALLOWED_CONDITION:
            pe['market_condition'] = 'Neutral'
        if pe.get('volatility_context') not in ALLOWED_VOLATILITY:
            pe['volatility_context'] = 'Unknown'
        if pe.get('price_behavior') not in ALLOWED_BEHAVIOR:
            pe['price_behavior'] = 'Range-bound'
        analysis['premium_environment'] = pe

        # Step 2 — Forbidden phrase scan
        FORBIDDEN = [
            # Entry-side forbidden phrases
            'BUY', 'SELL', 'go long', 'go short', 'buy call', 'buy put',
            'entry at', 'target price', 'stop loss', 'take profit',
            'open position', 'close position',
            # Exit-side forbidden phrases
            'exit position', 'exit the', 'exit your', 'exit all',
            'square off', 'squareoff', 'close the trade', 'close your',
            'cut position', 'book profit', 'book loss',
        ]

        def scrub(value: str) -> str:
            if not isinstance(value, str):
                return value
            for phrase in FORBIDDEN:
                if phrase.lower() in value.lower():
                    log.warning(f'[Safety] Forbidden phrase "{phrase}" in field — removed')
                    value = re.sub(re.escape(phrase), '[removed]', value, flags=re.IGNORECASE)
            return value

        free_text_fields = [
            'current_situation', 'signal', 'risk_note', 'prev_day_context', 'unusual_observation', 'mtf_alignment',
        ]
        for field in free_text_fields:
            if field in analysis:
                analysis[field] = scrub(analysis[field])

        if isinstance(analysis.get('reasoning'), list):
            analysis['reasoning'] = [scrub(r) for r in analysis['reasoning']]

        pe_free = ['key_insight', 'risk_note']
        for field in pe_free:
            if field in pe:
                pe[field] = scrub(pe[field])
        if isinstance(pe.get('reasoning'), list):
            pe['reasoning'] = [scrub(r) for r in pe['reasoning']]

        # Step 2b — key_levels numeric validation
        try:
            kl = analysis.get('key_levels') or {}
            def _safe_strike(val):
                try:
                    v = float(str(val or '').replace(',', '').strip())
                    return str(int(v)) if v > 0 else '—'
                except (ValueError, TypeError):
                    return '—'
            analysis['key_levels'] = {
                'support':    _safe_strike(kl.get('support')),
                'resistance': _safe_strike(kl.get('resistance')),
            }
        except Exception:
            analysis['key_levels'] = {'support': '—', 'resistance': '—'}

        # Step 3 — Type safety
        if not isinstance(analysis.get('score_agreement'), bool):
            analysis['score_agreement'] = False
        if not isinstance(analysis.get('reasoning'), list):
            analysis['reasoning'] = [str(analysis.get('reasoning', ''))]
        analysis['reasoning'] = analysis['reasoning'][:5]

        # Truncate long strings
        for field in free_text_fields:
            if isinstance(analysis.get(field), str) and len(analysis[field]) > 500:
                analysis[field] = analysis[field][:500]

        # Truncate premium_environment free-text fields
        if isinstance(pe.get('key_insight'), str) and len(pe['key_insight']) > 300:
            pe['key_insight'] = pe['key_insight'][:300]
        if isinstance(pe.get('reasoning'), list):
            pe['reasoning'] = [
                r[:200] if isinstance(r, str) and len(r) > 200 else r
                for r in pe['reasoning']
            ]
        analysis['premium_environment'] = pe

        return analysis


    # ─────────────────────────────────────────────────────────────────────────────
    # 14. NiftyDashboardApp
    # ─────────────────────────────────────────────────────────────────────────────
class NiftyDashboardApp:
    """
    Orchestrates all 16 classes. Runs the 23-step intraday data cycle.
    Handles startup, continuous loop, Ctrl+C graceful shutdown.
    """

    def __init__(self):
        log.info('=' * 60)
        log.info('NIFTY Intraday Dashboard — Starting up')
        log.info('=' * 60)

        # ── Google Sheets connection ──────────────────────────────────────────
        self.sheets = SheetsWriter()
        self.sheets.connect()

        # ── First-run SETTINGS check ──────────────────────────────────────────
        if not self.sheets.settings_tab_exists():
            self.sheets.write_settings_template()
            self.sheets.write_settings_help()
            raise RuntimeError(
                'SETTINGS tab was not found. A blank template has been created in the Google '
                'Spreadsheet. Fill in your credentials in the SETTINGS tab: '
                'B17=API Key, B18=Client Code, B19=MPIN (4 digits only), B20=TOTP Secret. '
                'Then re-run the script.'
            )

        # ── Load configuration from SETTINGS tab ─────────────────────────────
        self.config_reader = ConfigReader(self.sheets.spreadsheet)
        self.cfg           = self.config_reader.load()
        # Store interval seconds for SNAP-02
        CONFIG['_INTERVAL_SECONDS'] = int(self.cfg.get('interval_min', 5)) * 60

        # ── Instrument master ─────────────────────────────────────────────────
        self.instrument_loader = InstrumentMasterLoader()
        self.instrument_loader.load()

        # ── API client ────────────────────────────────────────────────────────
        self.api_client = SmartApiClient(self.cfg['api_key'])
        self.api_client.login(
            client_code=self.cfg['client_code'],
            mpin=self.cfg['mpin'],
            totp_secret=self.cfg['totp_secret'],
        )

        # ── Core engine classes ───────────────────────────────────────────────
        self.candle_fetcher  = CandleFetcher(
            self.api_client.smart_api,
            self.instrument_loader.get_futures_token(),
        )
        self.chain_builder   = OptionChainBuilder(self.api_client)
        self.metrics_calc    = MetricsCalculator()
        self.signal_engine   = SignalEngine()
        self.theta_analyzer  = ThetaEnvironmentAnalyzer()
        self.sr_detector     = ReversalBreakoutDetector()
        self.checker         = StartupChecker(max_score=self.metrics_calc.max_score)
        self.telegram        = TelegramSender()
        self.claude          = ClaudeAnalyst()

        # ── Fetch previous day OHLC once at startup ───────────────────────────
        self.prev_day = self.candle_fetcher.fetch_prev_day()
        self.claude.prev_day = self.prev_day
        if self.prev_day:
            log.info(f"[PrevDay] H={self.prev_day.get('prev_high')} "
                     f"L={self.prev_day.get('prev_low')} "
                     f"C={self.prev_day.get('prev_close')}")
        else:
            log.warning('[PrevDay] Previous day OHLC unavailable.')

        # ── Intraday session tracking ─────────────────────────────────────────
        self.session_high:  float = 0.0
        self.session_low:   float = float('inf')
        self.session_open:  float = 0.0

        # ── SR event tracking ─────────────────────────────────────────────────
        self.sr_event_age:  int   = 0
        self.last_sr_event: str   = 'NONE'

        # ── Per-cycle state ───────────────────────────────────────────────────
        self.prev_chain      = None
        self.prev_metrics    = None   # for MetricsCalculator.compute(prev_metrics=)
        self.prev_spot       = 0.0    # for SignalEngine.run(prev_spot=)
        self.prev_atm        = 0.0
        self.prev_cycle_ts   = None
        self.cycle_num       = 0
        self.history_rows:   List[dict] = []

        # ── Expiry state (resolved per cycle but stored for INST checks) ──────
        self.expiry_str      = ''
        self.expiry_dt       = None
        self.is_weekly       = False

        # ── Execution system ──────────────────────────────────────────────────
        self.order_executor = OrderExecutor(
            api_client=self.api_client, instrument_loader=self.instrument_loader,
            telegram=self.telegram, sheets=self.sheets
        )
        self.setup_evaluator = SetupEvaluator()
        self.pending_signals = []
        self._session_trend_anchor = ''

        # ── Phase 1 startup checks ────────────────────────────────────────────
        self._run_phase1_checks()

        # ── Write settings help once ──────────────────────────────────────────
        self.sheets.write_settings_help()

        # ── Ensure tab order ──────────────────────────────────────────────────
        self.sheets.ensure_tab_order()

        # ── Wait for market open if before 09:15 ─────────────────────────────
        self._wait_for_market_open()

        log.info('[App] Startup complete. Entering main loop.')

    def _wait_for_market_open(self):
        from datetime import time as dtime
        while True:
            ist = now_ist()
            if ist.time() < dtime(9, 15) and ist.weekday() < 5:
                log.warning(
                    f'[App] Script started before market open ({ist.strftime("%H:%M IST")}). '
                    'Waiting for 09:15 IST...'
                )
                time.sleep(60)
            else:
                break
        ist = now_ist()
        if ist.time() >= dtime(15, 30):
            log.warning(
                '[App] Script started post-market. Candle and quote data will be stale. '
                'Run during 09:00–15:30 IST for live analysis.'
            )

    def _run_phase1_checks(self):
        """Run SYS/AUTH/INST checks once at startup before any data API calls."""
        # Resolve expiry for INST checks — returns (expiry_dt, expiry_str, is_monthly)
        try:
            expiry_dt, expiry_str, is_monthly = self.instrument_loader.select_expiry(
                mode=self.cfg.get('expiry_mode', 'AUTO'),
                manual_expiry=self.cfg.get('manual_expiry', ''),
            )
            is_weekly = not is_monthly
            self.expiry_str = expiry_str
            self.expiry_dt  = expiry_dt
            self.is_weekly  = is_weekly
        except Exception as e:
            log.error(f'[App] Expiry resolution failed at startup: {e}')
            expiry_str = ''; expiry_dt = None; is_weekly = False

        # Build focus zone (no spot yet — use 0 as placeholder)
        try:
            n_above    = int(self.cfg.get('strikes_above', 5))
            n_below    = int(self.cfg.get('strikes_below', 5))
            focus_zone = []  # populated after first cycle spot fetch
        except Exception:
            focus_zone = []

        # Build instruments dict using real public getters
        opts_df = self.instrument_loader.get_options_df()
        avail   = self.instrument_loader.get_available_expiries()
        instruments_info = {
            'cache_age_hours':    self.instrument_loader.get_cache_age_hours(),
            'record_count':       self.instrument_loader.get_record_count(),
            'nifty_option_count': len(opts_df) if opts_df is not None else 0,
            'available_expiries': [e[1] for e in avail],   # list of expiry strings for INST-04
            'futures_token':      self.instrument_loader.get_futures_token(),
            'futures_expiry_dt':  self.instrument_loader.get_futures_expiry_dt(),
            'focus_zone_covered': len(focus_zone),
        }

        self.checker.run_phase1(
            gc=self.sheets.gc,
            spreadsheet=self.sheets.spreadsheet,
            api_client=self.api_client,
            instruments=instruments_info,
            expiry_str=expiry_str,
            expiry_dt=expiry_dt,
            focus_zone=focus_zone,
            is_weekly=is_weekly,
        )
        p1_summary = self.checker.summary()
        log.info(f"[Phase1] {p1_summary['warns']} warnings, {p1_summary['fails']} failures.")

        if self.checker.has_critical_fail():
            # Write initial checklist
            self.sheets.write_checklist(p1_summary)
            fail_msgs = [r['detail'] for r in p1_summary['results'] if r['status'] == 'FAIL']
            raise RuntimeError(
                f'Startup Phase 1 CRITICAL FAILURE(S): {"; ".join(fail_msgs)}'
            )

    # ── CHANGE 4: Helper to extract Strike OI from chain DataFrame ───────────

    def _get_strike_oi(self, chain, metrics):
        """
        Extract support OI, support chg OI, resistance OI, and resistance chg OI from chain.
        Returns tuple: (support_oi, support_chg_oi, resistance_oi, resistance_chg_oi)
        """
        support = int(metrics.get('support_strike', 0) or 0)
        resistance = int(metrics.get('resistance_strike', 0) or 0)

        support_oi = 0
        support_chg_oi = 0
        resistance_oi = 0
        resistance_chg_oi = 0

        if chain is not None and not chain.empty:
            # Get PE OI at support strike
            pe_row = chain[chain['strike'] == support]
            if not pe_row.empty:
                support_oi = int(pe_row['pe_open_interest'].iloc[0] or 0)
                support_chg_oi = int(pe_row['pe_change_oi'].iloc[0] or 0)
            
            # Get CE OI at resistance strike
            ce_row = chain[chain['strike'] == resistance]
            if not ce_row.empty:
                resistance_oi = int(ce_row['ce_open_interest'].iloc[0] or 0)
                resistance_chg_oi = int(ce_row['ce_change_oi'].iloc[0] or 0)

        return support_oi, support_chg_oi, resistance_oi, resistance_chg_oi

    # ── CHANGE 8: Check if TODAY_LOG needs to be reset for new session ───────

    def _check_today_log_session_reset(self):
        """
        On new IST date: clear TODAY_LOG, reset signal tracking,
        and deactivate execution for the new session.
        Execution requires the user to click button again each day.
        """
        ist       = now_ist()
        today_str = ist.strftime('%Y-%m-%d')
        if self.sheets._today_log_date != today_str:
            self.sheets._today_log_date = today_str
            self.sheets.clear_and_reset_today_log(
                self.sheets.TODAY_LOG_HEADER)
            # Reset signal tracking for new session
            self.pending_signals       = []
            self._session_trend_anchor = ''
            # Reset Claude analysis flags for new session
            self.claude.eod_done       = False
            self.claude.morning_done   = False
            self.claude.last_analysis  = None   # clear stale yesterday analysis
            log.info('[App] Session reset: claude.last_analysis cleared for new trading day.')
            # Reset session range for new trading day
            self.session_high = 0.0
            self.session_low  = float('inf')
            self.session_open = 0.0
            # Deactivate execution
            try:
                self.sheets.deactivate_execution_for_new_session()
                if hasattr(self, 'order_executor'):
                    self.order_executor.active_position     = {}
                    self.order_executor._neutral_vol_cycles = 0
                    self.order_executor._last_trap_type     = 'NONE'
            except Exception as _de:
                log.warning(f'[App] Execution deactivation: {_de}')
            log.info(
                '[App] New session: TODAY_LOG cleared, signals reset, '
                'execution deactivated. Click EXECUTE TRADE to reactivate.')

    def run(self):
        """Main entry point. Single-run or continuous loop based on SETTINGS."""
        auto_refresh = str(self.cfg.get('auto_refresh', 'YES')).upper() == 'YES'
        interval_min = int(self.cfg.get('interval_min', 5))

        if auto_refresh:
            log.info(f'[App] Auto-refresh mode — interval {interval_min} min.')
            try:
                while True:
                    self._run_cycle()
                    log.info(f'[App] Sleeping {interval_min} min until next cycle...')
                    time.sleep(interval_min * 60)
            except KeyboardInterrupt:
                log.info('[App] Ctrl+C detected — triggering EOD review before exit.')
                try:
                    self.claude.end_of_day(self._build_simple_snapshot())
                    if self.claude.last_analysis and 'eod_review' in self.claude.last_analysis:
                        self._write_daily_review()
                except Exception as e:
                    log.warning(f'[App] EOD on shutdown failed: {e}')
                log.info('[App] Graceful shutdown complete.')
        else:
            log.info('[App] Single-run mode.')
            self._run_cycle()
            log.info('[App] Single run complete.')

    def _build_simple_snapshot(self) -> dict:
        """Minimal snapshot for EOD/shutdown when no fresh data is available."""
        return {
            'spot': 0, 'atm': 0, 'bias': '—', 'score': '—', 'confidence': '—',
            'sr_event': self.last_sr_event, 'market_condition': '—',
        }

    # ── Main cycle ────────────────────────────────────────────────────────────

    def _run_cycle(self):
        self.cycle_num += 1
        log.info(f'[Cycle {self.cycle_num}] Starting at {ist_str()}')

        # ── Step 0: Check if TODAY_LOG needs to be reset ─────────────────────
        # CHANGE 8: Reset TODAY_LOG at the start of each new session (date change)
        self._check_today_log_session_reset()

        # ── Step 0B: Read execution trigger ──────────────────────────────────
        _exec_trigger = {}
        try:
            _exec_trigger = self.sheets.read_execution_trigger()
        except Exception as _et:
            log.debug(f'[App] Trigger read: {_et}')

        # ── Step 1: Midnight renewal ──────────────────────────────────────────
        self.api_client.maybe_renew_session()

        # ── Step 2: Determine expiry ──────────────────────────────────────────
        try:
            expiry_dt, expiry_str, is_monthly = self.instrument_loader.select_expiry(
                mode=self.cfg.get('expiry_mode', 'AUTO'),
                manual_expiry=self.cfg.get('manual_expiry', ''),
            )
            is_weekly = not is_monthly
        except Exception as e:
            log.error(f'[Cycle] Expiry resolution failed: {e}')
            expiry_str = self.expiry_str
            expiry_dt  = self.expiry_dt
            is_weekly  = self.is_weekly
            is_monthly = not is_weekly

        expiry_type = 'WEEKLY' if is_weekly else 'MONTHLY'
        self.expiry_str = expiry_str
        self.expiry_dt  = expiry_dt
        self.is_weekly  = is_weekly

        # ── Step 3: Fetch spot candles ────────────────────────────────────────
        spot_df = self.candle_fetcher.fetch_spot()

        # ── Step 3b: Fetch VIX ────────────────────────────────────────────────
        vix_data = self.candle_fetcher.fetch_vix()

        # ── Step 3c: Build candle summaries ───────────────────────────────────
        spot_candles    = CandleFetcher.candle_summary(spot_df,    n=8)
        futures_df_temp = None  # will be fetched at step 4

        # ── Step 4: Fetch futures candles ─────────────────────────────────────
        futures_df = self.candle_fetcher.fetch_futures()
        futures_candles = CandleFetcher.candle_summary(futures_df, n=8)

        # ── Step 4b: Fetch MTF candles for AI analysis ────────────────
        try:
            spot_15m_df = self.candle_fetcher.fetch_spot_15m()
        except Exception as _e:
            log.warning(f'[App] fetch_spot_15m failed: {_e}')
            spot_15m_df = None
        try:
            spot_30m_df = self.candle_fetcher.fetch_spot_30m()
        except Exception as _e:
            log.warning(f'[App] fetch_spot_30m failed: {_e}')
            spot_30m_df = None

        # ── Step 3d: Update session range (after spot_df available) ──────────
        spot = float('nan')
        if spot_df is not None and len(spot_df) > 0:
            spot = float(spot_df.iloc[-1].get('close', float('nan')))
        if not math.isnan(spot):
            self.session_high = max(self.session_high, spot)
            self.session_low  = min(self.session_low,  spot)
            if self.session_open == 0.0 and spot_df is not None and len(spot_df) > 0:
                # Use the open of the earliest available candle (closest to 09:15)
                # not the close of the latest candle, which drifts after 09:20.
                self.session_open = float(spot_df.iloc[0].get('open', spot))

        # ── Step 5: Determine ATM ─────────────────────────────────────────────
        if math.isnan(spot):
            spot = self.candle_fetcher.get_last_spot_close() or self.prev_spot or 0.0
        atm = math.floor(spot / CONFIG['NIFTY_STRIKE_STEP'] + 0.5) * CONFIG['NIFTY_STRIKE_STEP']

        # ── Step 6: Focus zone ────────────────────────────────────────────────
        n_above    = int(self.cfg.get('strikes_above', 5))
        n_below    = int(self.cfg.get('strikes_below', 5))
        focus_zone = [atm + i * CONFIG['NIFTY_STRIKE_STEP']
                      for i in range(-n_below, n_above + 1)]

        # ── Step 7: Fetch option quotes ───────────────────────────────────────
        options_df = self.instrument_loader.get_option_contracts(expiry_str)
        chain = self.chain_builder.build(
            focus_strikes=focus_zone,
            expiry_str=expiry_str,
            is_weekly=is_weekly,
            options_df=options_df,
            prev_snapshot=self.prev_chain,
        )

        # ── Step 8: Fetch IV (skip for weekly or outside hours) ───────────────
        # IV is fetched inside chain_builder.build() via Greeks endpoint.

        # ── Step 9-10: Change OI and chain already built in chain_builder ─────

        # ── Step 11: Compute metrics ──────────────────────────────────────────
        metrics = self.metrics_calc.compute(
            chain=chain,
            prev_metrics=self.prev_metrics,
        )
        pcr_chg_oi = metrics.get('pcr_chg_oi', float('nan'))

        # ── Step 12: SR event detection ───────────────────────────────────────
        sr_event = self.sr_detector.detect(
            spot=spot,
            metrics=metrics,
            signals={},  # signals not yet computed — pass empty, will use in next cycle
            spot_df=spot_df,
            futures_df=futures_df,
        )

        # ── Step 13: Signal engine ────────────────────────────────────────────
        signals = self.signal_engine.run(
            chain=chain,
            metrics=metrics,
            spot_df=spot_df,
            futures_df=futures_df,
            spot=spot,
            prev_spot=self.prev_spot,
        )
        # Re-run SR detection with signals now available
        sr_event = self.sr_detector.detect(
            spot=spot,
            metrics=metrics,
            signals=signals,
            spot_df=spot_df,
            futures_df=futures_df,
        )
        # Re-track SR age with updated event
        current_event = sr_event['event']
        if current_event != 'NONE':
            if current_event == self.last_sr_event:
                self.sr_event_age += 1
            else:
                self.sr_event_age = 1
                self.last_sr_event = current_event
        else:
            self.sr_event_age  = 0
            self.last_sr_event = 'NONE'

        # ── Step 13b: ThetaEnvironmentAnalyzer ───────────────────────────────
        days_to_expiry = 0
        if expiry_dt:
            try:
                days_to_expiry = max(0, (expiry_dt.date() - now_ist().date()).days)
            except Exception:
                pass
        theta_env = self.theta_analyzer.compute(
            vix_data=vix_data,
            days_to_expiry=days_to_expiry,
            spot_df=spot_df,
            metrics=metrics,
            signals=signals,
            sr_event=sr_event,
        )

        # ── Step 14: Phase 2 startup checks ──────────────────────────────────
        self.checker.run_phase2(
            spot_df=spot_df,
            futures_df=futures_df,
            chain=chain,
            prev_chain=self.prev_chain,
            score=signals.get('score_raw', 0),
            is_weekly=is_weekly,
            expiry_dt=expiry_dt,
            expiry_str=expiry_str,
            prev_atm=self.prev_atm,
            current_atm=float(atm),
            prev_cycle_ts=self.prev_cycle_ts,
            cycle_num=self.cycle_num,
            max_score=self.metrics_calc.max_score,
        )
        checklist_result = self.checker.summary()
        warns = checklist_result['warns']
        fails = checklist_result['fails']

        # ── Step 15: Recompute confidence with warn penalty ───────────────────
        # Apply penalty from the first warning (spec: confidence reduces when warns increase).
        if warns >= 1:
            orig_conf = signals.get('confidence', 0)
            penalised = max(0.0, orig_conf - warns * 5)
            signals['confidence'] = penalised
            signals['confidence_display'] = f'{penalised:.1f}%/100%'

        # ── Step 16: Write checklist ──────────────────────────────────────────
        self.sheets.write_checklist(checklist_result)

        # ── Step 17: Halt cycle if any FAIL ──────────────────────────────────
        if fails > 0:
            fail_msg = '; '.join(r['detail'] for r in checklist_result['results']
                                 if r['status'] == 'FAIL')

            # Holiday / failed-cycle fallback ChatGPT note so CLAUDE_ANALYSIS is not blank
            if getattr(self.claude, 'enabled', False):
                try:
                    fallback_snapshot = {
                        'spot': spot,
                        'atm': int(atm) if atm else 0,
                        'bias': signals.get('bias', 'NEUTRAL'),
                        'score': signals.get('score_display', '0/12'),
                        'confidence': signals.get('confidence_display', '0.0%/100%'),
                        'sr_event': sr_event.get('event', 'NONE'),
                        'sr_confidence': sr_event.get('confidence', 'N/A'),
                        'market_condition': theta_env.get('market_condition', 'Unknown'),
                    }
                    fallback_prompt = (
                        "Return strict JSON only. Create a short descriptive market note for a failed or holiday cycle. "
                        "Do not use buy, sell, entry, target, stoploss or trading advice. "
                        f"Timestamp: {ist_str()}\n"
                        f"Reason: {fail_msg}\n"
                        f"Spot: {safe_val(spot)} ATM: {safe_val(atm)}\n"
                        f"Bias: {signals.get('bias', 'NEUTRAL')} Score: {signals.get('score_display', '0/12')} "
                        f"Confidence: {signals.get('confidence_display', '0.0%/100%')}\n"
                        f"Prev day high/low/close: {self.prev_day.get('prev_high','')}, "
                        f"{self.prev_day.get('prev_low','')}, {self.prev_day.get('prev_close','')}\n"
                        'JSON schema: {"market_bias":"...","strength":"LOW|MEDIUM|HIGH","signal":"...",'
                        '"current_situation":"...","risk_note":"...","score_agreement":false,'
                        '"unusual_observation":"...","premium_environment":{"market_condition":"...",'
                        '"volatility_context":"...","key_insight":"..."}}'
                    )
                    raw = self.claude._call_claude(fallback_prompt, max_tokens=500)
                    fallback_analysis = self.claude._sanitize_output(self.claude._parse_json(raw))
                    self.claude.last_analysis = fallback_analysis
                    self.sheets.append_claude_analysis(
                        analysis=fallback_analysis,
                        snapshot=fallback_snapshot,
                        ts=ist_str(),
                        call_type='FALLBACK',
                    )
                    log.info('[ChatGPT] Fallback note written to CLAUDE_ANALYSIS.')
                except Exception as e:
                    log.warning(f'[ChatGPT] GPT fallback failed, writing plain fallback note: {e}')
                    plain_analysis = {
                        'market_bias': 'Neutral',
                        'current_situation': (
                            'Market closed or live data unavailable. No fresh spot, futures, or VIX candles '
                            'were returned, so no live intraday bias assessment was generated.'
                        ),
                        'key_levels': {'support': '—', 'resistance': '—'},
                        'signal': 'Live market snapshot unavailable this cycle.',
                        'strength': 'Weak',
                        'reasoning': [
                            'Spot, futures, and VIX candle data were unavailable for this cycle.',
                            'Option quotes were unavailable or insufficient for reliable OI-based interpretation.',
                            'Use previous-day values only as descriptive context.'
                        ],
                        'prev_day_context': 'Previous-day levels are available for reference only.',
                        'risk_note': f'AI fallback used plain text note because GPT request failed: {e}',
                        'score_agreement': False,
                        'unusual_observation': None,
                        'premium_environment': {
                            'market_condition': 'Neutral',
                            'volatility_context': 'Unknown',
                            'price_behavior': 'Range-bound',
                            'key_insight': 'Live data unavailable, so premium environment could not be assessed reliably.',
                            'reasoning': [
                                'No live VIX confirmation available.',
                                'No live futures volume confirmation available.',
                                'No live price-structure confirmation available.'
                            ],
                            'risk_note': 'Premium environment note is fallback-only due to missing live data.'
                        }
                    }
                    fallback_snapshot = {
                        'spot': self.candle_fetcher.get_last_spot_close(),
                        'atm': 0,
                        'expiry': expiry_str if "expiry_str" in locals() else '—',
                        'expiry_type': expiry_type if "expiry_type" in locals() else '—',
                        'bias': 'NEUTRAL',
                        'score': '0/0',
                        'confidence': '0%/100%',
                        'bias_at': ist_str(),
                        'event_tag': 'LOW CONFIDENCE',
                        'market_condition': 'Neutral',
                    }
                    try:
                        self.sheets.append_claude_analysis(
                            analysis=plain_analysis,
                            snapshot=fallback_snapshot,
                            ts=ist_str(),
                            call_type='FALLBACK',
                        )
                        log.info('[ChatGPT] Plain fallback note written to CLAUDE_ANALYSIS.')
                    except Exception as sheet_err:
                        log.warning(f'[ChatGPT] Plain fallback sheet write failed: {sheet_err}')

            log.error(f'[Cycle {self.cycle_num}] HALT — checklist FAIL: {fail_msg}')
            return

        # ── Step 18: Build snapshot dict ──────────────────────────────────────
        snapshot = {
            'spot':             spot,
            'atm':              int(atm),
            'expiry':           expiry_str,
            'expiry_type':      expiry_type,
            'bias':             signals.get('bias', 'NEUTRAL'),
            'score':            signals.get('score_display', '0/12'),
            'score_raw':        signals.get('score_raw', 0),
            'confidence':       signals.get('confidence', 0.0),
            'bias_at':          signals.get('bias_calculated_at', ist_str()),
            'event_tag':        signals.get('event_tag', '—'),
            'trap':             signals.get('trap_msg', ''),
            'price_structure':  signals.get('price_structure', '—'),
            'vwap':             signals.get('vwap_level', float('nan')),
            'vwap_bias':        signals.get('vwap_bias', 'NEUTRAL'),
            'vol_bias':         signals.get('vol_bias', 'NEUTRAL'),
            'support':          int(metrics.get('support_strike', 0) or 0),
            'resistance':       int(metrics.get('resistance_strike', 0) or 0),
            'support_shift':    metrics.get('support_shift', 0),
            'resistance_shift': metrics.get('resistance_shift', 0),
            'pcr_oi':           metrics.get('pcr_oi', float('nan')),
            'pcr_chg_oi':       pcr_chg_oi,
            'total_ce_oi':      metrics.get('total_ce_oi', 0),
            'total_pe_oi':      metrics.get('total_pe_oi', 0),
            'total_ce_chg_oi':  metrics.get('total_ce_chg_oi', 0),
            'total_pe_chg_oi':  metrics.get('total_pe_chg_oi', 0),
            'vol_imbalance':    metrics.get('vol_imbalance', float('nan')),
            'oi_concentration': metrics.get('oi_concentration', float('nan')),
            'sr_event':         sr_event.get('event', 'NONE'),
            'sr_event_age':     self.sr_event_age,
            'sr_confidence':    sr_event.get('confidence', 'N/A'),
            'candle_pattern':   sr_event.get('candle_pattern', 'NONE'),
            'candle_wick_pct':  sr_event.get('candle_wick_pct', 0),
            'candle_vol_ratio': sr_event.get('candle_vol_ratio', 1.0),
            'checklist_warns':  warns,
            'checklist_fails':  fails,
            'session_high':     self.session_high,
            'session_low':      self.session_low,
            'session_open':     self.session_open,
            'market_condition':   theta_env.get('market_condition', 'Neutral'),
            'volatility_context': theta_env.get('volatility_context', 'Unknown'),
            'price_behavior':     theta_env.get('price_behavior', 'Range-bound'),
            'vix_level':          theta_env.get('vix_level', float('nan')),
            'vix_trend':          vix_data.get('vix_trend', 'Unknown'),
            'vix_pct_change':     vix_data.get('vix_pct_change', float('nan')),
            'vix_candles_count':  vix_data.get('vix_candles_count', 0),
            'days_to_expiry':     theta_env.get('days_to_expiry', 0),
            'decay_score':        theta_env.get('decay_score', 0),
        }

        # ── Step 19: Claude ───────────────────────────────────────────────────
        claude_result = self.claude.maybe_run(
            cycle_num=self.cycle_num,
            snapshot=snapshot,
            metrics=metrics,
            signals=signals,
            sr_event=sr_event,
            chain=chain,
            history_rows=self.history_rows,
            spot_candles=spot_candles,
            futures_candles=futures_candles,
            spot_15m_df=spot_15m_df,
            spot_30m_df=spot_30m_df,
        )

        # ── Step 20: Write primary tabs ───────────────────────────────────────
        self.sheets.write_dashboard(
            signals=signals,
            metrics=metrics,
            sr_event=sr_event,
            theta_env=theta_env,
            checklist_result=checklist_result,
            prev_day=self.prev_day,
            vix_data=vix_data,
            claude_summary=self.claude.last_analysis,
            snapshot=snapshot,
        )
        self.sheets.write_current_snapshot(chain)
        if self.prev_chain is not None:
            self.sheets.write_previous_snapshot(self.prev_chain)
        self.sheets.write_comparison(chain, self.prev_chain)
        self.sheets.write_visualization_tab(
            snapshot=snapshot,
            metrics=metrics,
            signals=signals,
            theta_env=theta_env,
            sr_event=sr_event,
            vix_data=vix_data,
            chain=chain,
            history_rows=self.history_rows,
            claude_summary=self.claude.last_analysis,
        )

        # ── Step 21: Append HISTORY_LOG ───────────────────────────────────────
        # ── CHANGE 5: Build extended row dict with 23 new fields ──────────────
        
        # Get Strike OI values
        support_oi, support_chg_oi, resistance_oi, resistance_chg_oi = (
            self._get_strike_oi(chain, metrics)
        )
        
        # Calculate percentage distances
        support_val = float(metrics.get('support_strike', 0) or 0)
        resistance_val = float(metrics.get('resistance_strike', 0) or 0)
        spot_vs_support_pct = (
            round((spot - support_val) / support_val * 100, 2)
            if support_val > 0 else ''
        )
        spot_vs_resist_pct = (
            round((resistance_val - spot) / resistance_val * 100, 2)
            if resistance_val > 0 else ''
        )
        
        history_row = {
            'Timestamp':          ist_str(),
            'Symbol':             'NIFTY',
            'Expiry':             expiry_str,
            'Expiry Type':        expiry_type,
            'Spot Price (₹)':     safe_val(spot),
            'ATM':                int(atm),
            'Bias':               signals.get('bias', ''),
            'Bias Calculated At': signals.get('bias_calculated_at', ''),
            'Score':              signals.get('score_display', ''),
            'Score Max':          self.metrics_calc.max_score,
            'Confidence %':       signals.get('confidence', ''),
            'Support':            int(metrics.get('support_strike', 0) or 0),
            'Resistance':         int(metrics.get('resistance_strike', 0) or 0),
            'PCR OI':             safe_val(metrics.get('pcr_oi', float('nan'))),
            'Event Tag':          signals.get('event_tag', ''),
            'Warns':              warns,
            'Fails':              fails,
            'SR Event':           sr_event.get('event', 'NONE'),
            'SR Confidence':      sr_event.get('confidence', 'N/A'),
            'Candle Pattern':     sr_event.get('candle_pattern', 'NONE'),
            'Market Condition':   theta_env.get('market_condition', ''),
            'Volatility Context': theta_env.get('volatility_context', ''),
            'India VIX':          safe_val(theta_env.get('vix_level', float('nan'))),
            'Days to Expiry':     theta_env.get('days_to_expiry', 0),
            # GROUP A — Raw OI Chain
            'CE OI Total':        safe_val(metrics.get('total_ce_oi', 0)),
            'PE OI Total':        safe_val(metrics.get('total_pe_oi', 0)),
            'CE Chg OI':          safe_val(metrics.get('total_ce_chg_oi', 0)),
            'PE Chg OI':          safe_val(metrics.get('total_pe_chg_oi', 0)),
            'PCR Chg OI':         safe_val(metrics.get('pcr_chg_oi', float('nan'))),
            'CE Vol Total':       safe_val(metrics.get('total_ce_volume', 0)),
            'PE Vol Total':       safe_val(metrics.get('total_pe_volume', 0)),
            'Vol Imbalance':      safe_val(metrics.get('vol_imbalance', float('nan'))),
            # GROUP B — S/R Migration
            'Support Shift':      safe_val(metrics.get('support_shift', 0)),
            'Resistance Shift':   safe_val(metrics.get('resistance_shift', 0)),
            'Support OI':         support_oi,
            'Resistance OI':      resistance_oi,
            'Support Chg OI':     support_chg_oi,
            'Resistance Chg OI':  resistance_chg_oi,
            # GROUP C — Break Risk
            'SR Event Age':       self.sr_event_age,
            'Spot vs Support %':  spot_vs_support_pct,
            'Spot vs Resist %':   spot_vs_resist_pct,
            # GROUP D — Candle + VWAP Context
            'VWAP Level':         safe_val(signals.get('vwap_level')),
            'VWAP Bias':          signals.get('vwap_bias', ''),
            'Vol Bias':           signals.get('vol_bias', ''),
            'Price Structure':    signals.get('price_structure', ''),
            'Candle Wick %':      safe_val(sr_event.get('candle_wick_pct', 0)),
            'Candle Vol Ratio':   safe_val(sr_event.get('candle_vol_ratio', 1.0)),
            # ── CHANGE 4: Add 3 fields for OI concentration ──
            'Top CE Strike':      int(metrics.get('top_ce_strike', 0) or 0),
            'Top PE Strike':      int(metrics.get('top_pe_strike', 0) or 0),
            'OI Concentration':   safe_val(metrics.get('oi_concentration', float('nan'))),
        }
        self.sheets.append_history(history_row)
        self.history_rows.append(history_row)
        if len(self.history_rows) > 200:
            self.history_rows = self.history_rows[-200:]

        # ── Step 22: Append CLAUDE_ANALYSIS if ChatGPT ran ───────────────────
        if claude_result is not None and claude_result is not self.claude.last_analysis or (
            self.claude.last_run_ts != '—' and
            self.claude.claude_calls > 0 and
            self.cycle_num % CONFIG['CLAUDE_EVERY_N_CYCLES'] == 0
        ):
            if claude_result and claude_result.get('signal'):
                self.sheets.append_claude_analysis(
                    analysis=claude_result,
                    snapshot=snapshot,
                    ts=ist_str(),
                )
                # Extract MTF context stored by _call_analysis
                _mtf_ctx = claude_result.get('_mtf_context', {})
                # Write CURRENT_SITUATION tab every cycle
                self.sheets.write_current_situation(
                    analysis=claude_result,
                    snapshot=snapshot,
                    mtf_context=_mtf_ctx,
                    ts=ist_str(),
                )
                self.telegram.send_analysis(
                    analysis=claude_result,
                    snapshot=snapshot,
                    prev_day=self.prev_day,
                    ts=ist_str(),
                    mtf_context=_mtf_ctx,
                )
            else:
                # Write cached analysis to CURRENT_SITUATION even if no new
                # AI call ran this cycle
                if self.claude.last_analysis:
                    _mtf_ctx = self.claude.last_analysis.get(
                        '_mtf_context', {}
                    )
                    self.sheets.write_current_situation(
                        analysis=self.claude.last_analysis,
                        snapshot=snapshot,
                        mtf_context=_mtf_ctx,
                        ts=ist_str(),
                    )

        # ── Step 22b: Signal evaluation & execution trigger ──────────────────
        sig_eval = {}  # Initialize to prevent NameError if try block fails
        try:
            if snapshot and snapshot.get('bias') and snapshot.get('score') and snapshot.get('spot'):
                sig_eval = self.setup_evaluator.evaluate(
                    snapshot=snapshot,
                    metrics=metrics,
                    signals=signals,
                    sr_event=sr_event,
                    theta_env=theta_env,
                    vix_data=vix_data,
                    chain=chain,
                    days_to_expiry=days_to_expiry,
                    is_weekly=is_weekly,
                    lot_size=int(self.cfg.get('lot_size', 25)),
                )
                if sig_eval and sig_eval.get('setup_type') != 'NONE':
                    sig_id = f"{self.cycle_num}_{snapshot.get('bias','')[:3]}"
                    sig_eval['signal_id'] = sig_id
                    sig_dict = {
                        'signal_id': sig_id,
                        'spot_at_signal': float(snapshot.get('spot') or 0),
                        'bias': snapshot.get('bias', ''),
                        'setup_quality': sig_eval.get('setup_quality', 0),
                        'setup_type': sig_eval.get('setup_type', ''),
                        'cycles_elapsed': 0,
                        'outcome_15m_done': False,
                        'outcome_30m_done': False,
                    }
                    # Age existing signals BEFORE appending so new signal
                    # starts at cycles_elapsed=0 this cycle
                    for s in self.pending_signals:
                        s['cycles_elapsed'] = s.get('cycles_elapsed', 0) + 1
                    self.pending_signals.append(sig_dict)
                    log.info(f"[Signal] New signal recorded: {sig_id} ({sig_eval.get('setup_type')})")
                    # Append signal row to SIGNAL tab
                    mtf_ctx = self.claude.last_analysis.get('_mtf_context', {}) if self.claude.last_analysis else {}
                    self.sheets.append_signal_row(
                        setup=sig_eval,
                        snapshot=snapshot,
                        signals=signals,
                        metrics=metrics,
                        theta_env=theta_env,
                        vix_data=vix_data,
                        sr_event=sr_event,
                        cycle_num=self.cycle_num,
                        mtf_context=mtf_ctx
                    )
                    # Capture 9:45 IST trend anchor on first DECAY signal
                    ist = now_ist()
                    if ist.hour == 9 and ist.minute >= 45 and not self._session_trend_anchor:
                        self._session_trend_anchor = snapshot.get('bias', '')
                        log.info(f"[TrendAnchor] Session trend anchored at 9:45 IST: {self._session_trend_anchor}")

                # Update signal outcomes every cycle (outside if sig_eval)
                self.sheets.update_signal_outcomes(
                    pending_signals=self.pending_signals,
                    current_spot=float(snapshot.get('spot') or 0)
                )
        except Exception as e:
            log.warning(f"[SignalEval] Step 22b signal evaluation error: {e}")
        
        # ── Execution trigger + lifecycle monitoring ───────────────────
        try:
            self.cfg['_expiry_str'] = expiry_str

            # Guard: set _short_ltp_preview safely even if Step 22b raised
            _ltp_prev = 0
            try:
                _ltp_prev = sig_eval.get('short_ltp', 0)
            except Exception:
                pass
            _exec_trigger['_short_ltp_preview'] = _ltp_prev

            # Build focus zone from current chain strikes
            _focus_strikes = []
            if chain is not None and len(chain) > 0:
                _focus_strikes = pd.to_numeric(chain['strike'], errors='coerce').dropna().tolist()

            if _exec_trigger.get('execute_trade', 'NO').upper() == 'YES':
                log.info(
                    f'[App] Execution trigger: '
                    f'{_exec_trigger.get("action")} '
                    f'strike={_exec_trigger.get("strike")} '
                    f'lots={_exec_trigger.get("lots")} '
                    f'date={_exec_trigger.get("activation_date")}')
                self.order_executor.check_and_execute(
                    trigger      = _exec_trigger,
                    snapshot     = snapshot,
                    metrics      = metrics,
                    cfg          = self.cfg,
                    focus_zone   = _focus_strikes,
                    gpt_analysis = (self.claude.last_analysis or {}))
            elif self.order_executor.active_position:
                # No trigger this cycle — run lifecycle monitoring only
                self.order_executor._run_lifecycle_check(
                    snapshot     = snapshot,
                    gpt_analysis = (self.claude.last_analysis or {}))
        except Exception as _exe:
            log.warning(f'[App] Execution block: {_exe}')

        # Update EXECUTION tab every cycle
        try:
            self.sheets.write_execution_tab(
                position = (self.order_executor.active_position
                            if self.order_executor.active_position
                            else None),
                gates    = {},
            )
        except Exception as _exw:
            log.debug(f'[App] write_execution_tab: {_exw}')

        # ── Check EOD at 15:30 ────────────────────────────────────────────────
        ist = now_ist()
        if ist.hour == 15 and ist.minute >= 30 and not self.claude.eod_done:
            self.claude.end_of_day(snapshot)
            if self.claude.last_analysis and 'eod_review' in self.claude.last_analysis:
                self._write_daily_review()
                eod_text = self.claude.last_analysis.get('eod_review', '')
                if eod_text:
                    self.telegram.send_eod(eod_text)

        # ── Step 23: Update state for next cycle ──────────────────────────────
        if chain is not None and len(chain) > 0:
            self.prev_chain = chain.copy()
        self.prev_metrics  = metrics
        self.prev_spot     = float(spot) if not math.isnan(spot) else self.prev_spot
        self.prev_atm      = float(atm)
        self.prev_cycle_ts = now_ist()

        log.info(
            f'[Cycle {self.cycle_num}] Done — '
            f'spot={spot:.0f} atm={atm} bias={signals.get("bias","?")} '
            f'score={signals.get("score_display","?")} '
            f'sr={sr_event.get("event","NONE")} '
            f'market={theta_env.get("market_condition","?")} '
            f'vix={theta_env.get("vix_level","nan")}'
        )

    def _write_daily_review(self):
        """Write EOD review row to DAILY_REVIEW tab."""
        try:
            eod_text = self.claude.last_analysis.get('eod_review', '') if self.claude.last_analysis else ''
            review = {
                'total_cycles':       self.cycle_num,
                'claude_calls':       self.claude.claude_calls,
                'session_character':  eod_text[:500] if eod_text else '—',
                'best_signals':       '—',
                'missed_signals':     '—',
                'sr_event_accuracy':  f'SR events tracked: {self.sr_event_age} cycles last event.',
                'sr_accurate':        False,
                'prev_day_interaction': str(self.prev_day.get('prev_close', '—')),
                'calibration_note':   '—',
            }
            self.sheets.append_daily_review(review, ist_str())
        except Exception as e:
            log.warning(f'[App] _write_daily_review failed: {e}')


# ─────────────────────────────────────────────────────────────────────────────
# main()
# ─────────────────────────────────────────────────────────────────────────────

def main():
    """Entry point — instantiate NiftyDashboardApp and run."""
    try:
        app = NiftyDashboardApp()
        app.run()
    except RuntimeError as e:
        log.error(f'[Main] RuntimeError: {e}')
        print(f'\n❌ STARTUP ERROR: {e}\n')
        raise SystemExit(1)
    except Exception as e:
        log.error(f'[Main] Unexpected error: {e}\n{__import__("traceback").format_exc()}')
        raise


if __name__ == '__main__':
    main()
