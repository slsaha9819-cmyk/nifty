#!/usr/bin/env python3
"""
nifty_dashboard.py
NIFTY Intraday Market Analysis Dashboard — Angel One SmartAPI
Single-file, production-ready implementation.
"""

import json
import math
import time
import logging
import pathlib
from datetime import datetime, timedelta
from typing import Optional, Dict, List, Tuple, Any
from itertools import groupby

import pandas as pd
import numpy as np
import requests
import pyotp
import ntplib
import gspread
from gspread.exceptions import APIError, WorksheetNotFound

try:
    from SmartApi import SmartConnect
except ImportError as _e:
    raise ImportError(
        "smartapi-python is not installed. "
        "Run: pip install smartapi-python\n"
        f"Original error: {_e}"
    )

# ─────────────────────────────────────────────────────────────────────────────
# CONFIGURATION — all tunable thresholds in one place
# ─────────────────────────────────────────────────────────────────────────────
CONFIG: Dict[str, Any] = {
    # ── Google Sheets ──────────────────────────────────────────────────────
    'GOOGLE_SERVICE_ACCOUNT_JSON': 'service_account.json',
    'SPREADSHEET_ID':              '1ZYsVNrazNa4ATNKAGHfLdzkV60_9zhgFS2PIlIfH_yM',

    # ── Local paths ────────────────────────────────────────────────────────
    'LOG_FILE':              'logs/nifty_dashboard.log',
    'INSTRUMENT_CACHE_DIR':  'cache/',

    # ── Instrument master URLs ─────────────────────────────────────────────
    'INSTRUMENT_MASTER_URL_PRIMARY':
        'https://margincalculator.angelbroking.com/OpenAPI_File/files/OpenAPIScripMaster.json',
    'INSTRUMENT_MASTER_URL_FALLBACK':
        'https://margincalculator.angelone.in/OpenAPI_File/files/OpenAPIScripMaster.json',

    # ── Market data ────────────────────────────────────────────────────────
    'NIFTY_STRIKE_INTERVAL': 50,
    'SPOT_INDEX_TOKEN':      '99926000',   # NIFTY 50 index, NSE
    'SPOT_INDEX_EXCHANGE':   'NSE',
    'CANDLE_INTERVAL':       'FIVE_MINUTE',

    # ── NTP (use response.offset — not tx_time subtraction) ────────────────
    'NTP_PRIMARY':            'pool.ntp.org',
    'NTP_FALLBACK':           'time.cloudflare.com',
    'NTP_DRIFT_WARN_SECONDS': 15,
    'NTP_DRIFT_FAIL_SECONDS': 30,

    # ── Market hours IST ───────────────────────────────────────────────────
    'MARKET_OPEN_HOUR':    9,   'MARKET_OPEN_MINUTE':   15,
    'MARKET_CLOSE_HOUR':  15,   'MARKET_CLOSE_MINUTE':  30,

    # ── Feed quality ───────────────────────────────────────────────────────
    'CANDLE_RECENCY_WARN_MINUTES':  10,
    'CANDLE_RECENCY_FAIL_MINUTES':  20,
    'MIN_QUOTE_COVERAGE_WARN':       0.70,
    'MIN_QUOTE_COVERAGE_FAIL':       0.30,
    'MIN_INSTRUMENT_RECORDS':       50000,
    'MIN_INSTRUMENT_RECORDS_FAIL':  10000,
    'ATM_CHANGE_WARN_POINTS':        150,

    # ── Session renewal ────────────────────────────────────────────────────
    'RENEWAL_WINDOW_START_HOUR':   23,
    'RENEWAL_WINDOW_START_MINUTE': 30,

    # ── Rate limits ────────────────────────────────────────────────────────
    'RATE_LIMIT_RETRY_WAIT':        2,    # base back-off seconds for AB1019 retry
    'RATE_LIMIT_MAX_RETRIES':       3,    # max retry attempts on AB1019
    'RATE_LIMIT_INTER_CALL_SLEEP':  1.0,  # seconds to sleep between spot and futures calls
    'SHEETS_429_BACKOFF':          60,

    # ── Scoring weights ────────────────────────────────────────────────────
    'SCORE_STRONG_PE_WRITING':         2,
    'SCORE_STRONG_CE_WRITING':        -2,
    'SCORE_CE_UNWINDING_RISING':       2,
    'SCORE_PE_UNWINDING_FALLING':     -2,
    'SCORE_SUPPORT_SHIFT_UP':          1,
    'SCORE_SUPPORT_SHIFT_DOWN':       -1,
    'SCORE_RESISTANCE_SHIFT_UP':       1,
    'SCORE_RESISTANCE_SHIFT_DOWN':    -1,
    'SCORE_BULLISH_PCR':               1,
    'SCORE_BEARISH_PCR':              -1,
    'SCORE_BULLISH_VOL_IMBALANCE':     1,
    'SCORE_BEARISH_VOL_IMBALANCE':    -1,
    'SCORE_BULLISH_PRICE_STRUCTURE':   2,
    'SCORE_BEARISH_PRICE_STRUCTURE':  -2,
    'SCORE_ABOVE_VWAP':                1,
    'SCORE_BELOW_VWAP':               -1,
    'SCORE_BULLISH_VOL_CONFIRM':       1,
    'SCORE_BEARISH_VOL_CONFIRM':      -1,

    # ── Bias classification thresholds ─────────────────────────────────────
    'BIAS_STRONG_BULLISH':   5,
    'BIAS_BULLISH':          3,
    'BIAS_MILD_BULLISH':     1,
    'BIAS_MILD_BEARISH':    -1,
    'BIAS_BEARISH':         -4,
    'BIAS_STRONG_BEARISH':  -6,
}

# ─────────────────────────────────────────────────────────────────────────────
# LOGGING
# ─────────────────────────────────────────────────────────────────────────────
for _d in ['logs', 'cache']:
    pathlib.Path(_d).mkdir(exist_ok=True)

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s [%(levelname)s] %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler(CONFIG['LOG_FILE'], encoding='utf-8'),
    ],
)
log = logging.getLogger(__name__)

# ─────────────────────────────────────────────────────────────────────────────
# UTILITIES
# ─────────────────────────────────────────────────────────────────────────────
IST_OFFSET = timedelta(hours=5, minutes=30)

def now_ist() -> datetime:
    from datetime import timezone
    return datetime.now(timezone.utc).replace(tzinfo=None) + IST_OFFSET

def rgb_color(r: float, g: float, b: float) -> dict:
    return {"red": r, "green": g, "blue": b}

COLOR_GREEN   = rgb_color(0.851, 0.918, 0.827)
COLOR_RED     = rgb_color(0.957, 0.800, 0.800)
COLOR_YELLOW  = rgb_color(1.000, 0.949, 0.800)
COLOR_ORANGE  = rgb_color(0.988, 0.898, 0.804)
COLOR_DEEPRED = rgb_color(0.878, 0.400, 0.400)

STATUS_COLOR = {'PASS': COLOR_GREEN, 'WARN': COLOR_ORANGE, 'FAIL': COLOR_DEEPRED}

def bias_color(bias: str) -> dict:
    if 'BULLISH' in bias: return COLOR_GREEN
    if 'BEARISH' in bias: return COLOR_RED
    return COLOR_YELLOW

def safe_float(v, default: float = float('nan')) -> float:
    try:    return float(v)
    except: return default

def ss(v) -> str:
    """Sheets-safe string conversion."""
    if v is None:                          return ''
    if isinstance(v, float) and math.isnan(v): return 'N/A'
    return str(v)

def _sheets_append(ws: gspread.Worksheet, row: list):
    # RAW prevents Google Sheets from auto-parsing values like '24MAR2026' as dates
    ws.append_row(row, value_input_option='RAW')


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 1 — ConfigReader
# ═════════════════════════════════════════════════════════════════════════════
class ConfigReader:
    """
    Reads and validates all runtime settings from the SETTINGS Google Sheet tab.

    The SETTINGS tab is separate from the DASHBOARD tab so that write_dashboard()
    can freely write output to DASHBOARD (A1 onward) without overwriting config cells.

    SETTINGS tab layout (col A = label, col B = value):
        B2  Symbol               e.g. NIFTY
        B3  Expiry Mode          AUTO | NEXT | MONTHLY | MANUAL
        B4  Manual Expiry        DDMMMYYYY (only when B3=MANUAL)
        B5  Interval Minutes     e.g. 5
        B6  Strikes Above ATM    e.g. 5
        B7  Strikes Below ATM    e.g. 5
        B8  Auto Refresh         YES | NO
        B9  Broker               ANGELONE
        B10 Angel API Key
        B11 Angel Client Code
        B12 Angel PIN (MPIN)     4-digit mobile app PIN
        B13 Angel TOTP Secret
    """

    def __init__(self, spreadsheet: gspread.Spreadsheet):
        self.spreadsheet = spreadsheet
        self._ws: Optional[gspread.Worksheet] = None

    def _get_ws(self) -> gspread.Worksheet:
        if self._ws is None:
            try:
                self._ws = self.spreadsheet.worksheet('SETTINGS')
            except WorksheetNotFound:
                # Fall back to DASHBOARD for backwards compatibility,
                # but warn the user to create a SETTINGS tab.
                log.warning(
                    "CONFIG-01: 'SETTINGS' tab not found — falling back to 'DASHBOARD' tab. "
                    "IMPORTANT: Create a 'SETTINGS' tab with config in B2–B13 to prevent "
                    "write_dashboard() from overwriting your config cells on every cycle."
                )
                try:
                    self._ws = self.spreadsheet.worksheet('DASHBOARD')
                except WorksheetNotFound:
                    self._ws = self.spreadsheet.add_worksheet(title='SETTINGS', rows=50, cols=10)
        return self._ws

    def _read(self, cell: str) -> str:
        try:
            val = self._get_ws().acell(cell).value
            return val.strip() if val else ''
        except Exception as e:
            log.error(f"Error reading cell {cell}: {e}")
            return ''

    def load(self) -> dict:
        def _safe_int(raw: str, default: int) -> int:
            try:
                return int(raw)
            except (ValueError, TypeError):
                log.warning(f"ConfigReader: expected integer, got '{raw}'. Using default {default}.")
                return default

        # Row mapping matches the SETTINGS tab template layout:
        # Row 5=Symbol, 7=Expiry Mode, 8=Manual Expiry, 10=Interval,
        # 11=Strikes Above, 12=Strikes Below, 13=Auto Refresh, 15=Broker,
        # 17=API Key, 18=Client Code, 19=MPIN, 20=TOTP Secret
        cfg = {
            'symbol':           self._read('B5') or 'NIFTY',
            'expiry_mode':      (self._read('B7') or 'AUTO').upper(),
            'manual_expiry':    self._read('B8'),
            'interval_minutes': _safe_int(self._read('B10') or '5', 5),
            'strikes_above':    _safe_int(self._read('B11') or '5', 5),
            'strikes_below':    _safe_int(self._read('B12') or '5', 5),
            'auto_refresh':     (self._read('B13') or 'NO').upper(),
            'broker':           (self._read('B15') or 'ANGELONE').upper(),
            'api_key':          self._read('B17'),
            'client_code':      self._read('B18'),
            'mpin':             self._read('B19'),
            'totp_secret':      self._read('B20'),
        }
        self._validate(cfg)
        log.info(f"Config loaded — symbol={cfg['symbol']}, expiry_mode={cfg['expiry_mode']}, "
                 f"auto_refresh={cfg['auto_refresh']}, interval={cfg['interval_minutes']}m")
        return cfg

    def _validate(self, cfg: dict):
        missing = [k for k in ('api_key', 'client_code', 'mpin', 'totp_secret') if not cfg.get(k)]
        if missing:
            raise ValueError(f"Missing required values in SETTINGS cells: {missing}. "
                             "Check B17=API Key, B18=Client Code, B19=MPIN, B20=TOTP Secret.")
        if len(cfg['mpin']) != 4 or not cfg['mpin'].isdigit():
            raise ValueError(
                f"Cell B19 (MPIN) must be exactly 4 digits. Got: '{cfg['mpin']}'. "
                "Do NOT enter your web login password — enter your 4-digit Angel One MPIN "
                "(the same PIN you use in the Angel One mobile app)."
            )
        if cfg['expiry_mode'] not in ('AUTO', 'NEXT', 'MONTHLY', 'MANUAL'):
            raise ValueError(f"Invalid expiry mode '{cfg['expiry_mode']}'. Use AUTO/NEXT/MONTHLY/MANUAL.")
        if cfg['expiry_mode'] == 'MANUAL' and not cfg['manual_expiry']:
            raise ValueError("Expiry mode is MANUAL but cell B4 is empty.")
        if cfg['strikes_above'] < 1 or cfg['strikes_below'] < 1:
            raise ValueError(
                f"Cells B6 (strikes above={cfg['strikes_above']}) and B7 (strikes below={cfg['strikes_below']}) "
                "must each be a positive integer >= 1."
            )


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 2 — SmartApiClient
# ═════════════════════════════════════════════════════════════════════════════
class SmartApiClient:
    """
    Handles Angel One SmartAPI login, token capture, and midnight session renewal.
    Captures authToken, refreshToken, and feedToken — none are discarded.
    """

    def __init__(self, api_key: str, client_code: str, mpin: str, totp_secret: str):
        self.api_key      = api_key
        self.client_code  = client_code
        self.mpin         = mpin
        self.totp_secret  = totp_secret
        self.smart_api:    Optional[SmartConnect] = None
        self.auth_token:   str = ''
        self.refresh_token: str = ''
        self.feed_token:   str = ''

    def login(self):
        try:
            totp = pyotp.TOTP(self.totp_secret).now()
        except Exception as e:
            raise RuntimeError(
                f"TOTP generation failed. Verify the secret in cell B13 is the QR secret "
                f"from smartapi.angelone.in/enable-totp. Error: {e}"
            )

        self.smart_api = SmartConnect(api_key=self.api_key)
        try:
            data = self.smart_api.generateSession(self.client_code, self.mpin, totp)
        except Exception as e:
            self._handle_login_error(str(e), {})

        if not data or data.get('status') is False:
            self._handle_login_error('', data or {})

        try:
            self.auth_token    = data['data']['jwtToken']
            self.refresh_token = data['data']['refreshToken']
        except (KeyError, TypeError) as e:
            raise RuntimeError(
                f"Login response received but token extraction failed: {e}. "
                f"Full response: {data}"
            )

        if not self.auth_token:
            raise RuntimeError(f"AUTH-01 FAIL: authToken is empty. Response: {data}")
        if not self.refresh_token:
            raise RuntimeError("AUTH-04 FAIL: refreshToken is empty after login.")

        # feedToken must be fetched via SDK method — never read from response dict
        self.feed_token = self.smart_api.getfeedToken()
        if not self.feed_token:
            log.warning("AUTH-05 WARN: feedToken is empty. WebSocket will not be available.")

        log.info("Login successful. authToken, refreshToken, feedToken all captured.")

    def _handle_login_error(self, err_str: str, data: dict):
        error_code = str(data.get('errorcode', ''))
        message    = str(data.get('message', ''))
        combined   = err_str + error_code + message

        if 'AB7001' in combined or 'LoginbyPassword' in combined:
            raise RuntimeError(
                "AB7001: Angel One rejected the credential in cell B12. "
                "This error means you entered your web login password instead of your 4-digit MPIN. "
                "Your MPIN is the same 4-digit PIN you use to log into the Angel One mobile app. "
                "It is always exactly 4 digits. Update cell B12 with your 4-digit MPIN and retry. "
                "Do not enter your web or trading password."
            )
        if 'AB1050' in combined or ('totp' in combined.lower() and 'fail' in combined.lower()):
            raise RuntimeError(
                "AB1050: TOTP authentication failed. Verify your system clock is accurate (SYS-01) "
                "and that the TOTP secret in cell B13 is the correct QR secret from "
                "smartapi.angelone.in/enable-totp — not your MPIN or password."
            )
        raise RuntimeError(
            f"Login failed. API message: '{message or err_str}'. "
            "Check that all credentials in cells B10–B13 are correct and that your "
            "Angel One account has SmartAPI access enabled."
        )

    def check_and_renew_session(self):
        """Renew session token if IST time is between 23:30 and 23:59. Never use hour-based thresholds."""
        ist = now_ist()
        if ist.hour == CONFIG['RENEWAL_WINDOW_START_HOUR'] and ist.minute >= CONFIG['RENEWAL_WINDOW_START_MINUTE']:
            log.info("AUTH-03: Midnight renewal window (23:30–23:59 IST). Renewing session token...")
            try:
                resp = self.smart_api.generateToken(self.refresh_token)
                self.auth_token    = resp['data']['jwtToken']
                new_refresh        = resp['data'].get('refreshToken')
                if new_refresh:
                    self.refresh_token = new_refresh
                # Ensure the SDK uses the renewed token for subsequent API calls
                self.smart_api.access_token = self.auth_token
                self.feed_token = self.smart_api.getfeedToken()
                log.info("Session token renewed successfully.")
            except Exception as e:
                log.warning(
                    f"Session token renewal failed: {e}. "
                    "Session will expire at midnight IST. Restart before midnight to avoid data loss."
                )

    def get_api(self) -> SmartConnect:
        return self.smart_api


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 3 — InstrumentMasterLoader
# ═════════════════════════════════════════════════════════════════════════════
class InstrumentMasterLoader:
    """
    Downloads, caches, and parses the Angel One scrip master.
    CRITICAL implementation notes:
    - Filter NIFTY options by: name=='NIFTY' AND instrumenttype=='OPTIDX'  (never symbol=='NIFTY')
    - CE/PE via symbol.endswith('CE'/'PE')  (no standalone optionType field exists)
    - Strike = float(record['strike']) / 100  (scrip master stores 100x actual strike)
    - Expiry = datetime.strptime(expiry_str, "%d%b%Y")
    - Weekly/monthly classification: last-of-month grouping  (never weekday-based)
    - Retains original DDMMMYYYY string for Greeks API calls
    """

    def __init__(self):
        self.cache_dir   = pathlib.Path(CONFIG['INSTRUMENT_CACHE_DIR'])
        self.cache_dir.mkdir(exist_ok=True)
        self.options_df:            Optional[pd.DataFrame] = None
        self.futures_df:            Optional[pd.DataFrame] = None
        self.expiry_classification: Dict[datetime, bool]   = {}   # True = monthly
        self.nifty_futures_token:   str = ''
        self.nifty_futures_expiry:  str = ''
        self._raw_record_count:     int = 0

    # ── Cache helpers ──────────────────────────────────────────────────────
    def _cache_file(self, ds: str)  -> pathlib.Path: return self.cache_dir / f"instrument_master_{ds}.json"
    def _meta_file(self, ds: str)   -> pathlib.Path: return self.cache_dir / f"instrument_master_{ds}.meta"

    def _download(self) -> list:
        for url in [CONFIG['INSTRUMENT_MASTER_URL_PRIMARY'], CONFIG['INSTRUMENT_MASTER_URL_FALLBACK']]:
            try:
                log.info(f"Downloading instrument master from {url}")
                r = requests.get(url, timeout=60)
                if r.status_code == 200:
                    return r.json()
                log.warning(f"HTTP {r.status_code} from {url}")
            except Exception as e:
                log.warning(f"Download failed from {url}: {e}")
        raise RuntimeError(
            "Instrument master download failed from both URLs. "
            "Check network connectivity and Angel One service status."
        )

    def load(self) -> None:
        ist      = now_ist()
        date_str = ist.strftime('%Y%m%d')
        cf       = self._cache_file(date_str)
        mf       = self._meta_file(date_str)

        # Purge stale cache from other dates
        for f in self.cache_dir.glob('instrument_master_*.json'):
            if f.name != cf.name:
                f.unlink(missing_ok=True)
                log.info(f"Purged old cache file: {f.name}")
        for f in self.cache_dir.glob('instrument_master_*.meta'):
            if f.name != mf.name:
                f.unlink(missing_ok=True)

        cutoff       = ist.replace(hour=8, minute=30, second=0, microsecond=0)
        needs_dl     = True

        # Two-stage freshness check
        if cf.exists() and mf.exists():
            try:
                meta          = json.loads(mf.read_text())
                dl_time       = datetime.fromisoformat(meta['downloaded_at'])
                post_cutoff   = ist >= cutoff
                pre_cutoff_dl = dl_time < cutoff
                if pre_cutoff_dl and post_cutoff:
                    log.info("INST-01 Stage 2: Cache pre-dates 08:30 IST and clock is now past 08:30. Re-downloading.")
                    cf.unlink(missing_ok=True)
                    mf.unlink(missing_ok=True)
                else:
                    needs_dl = False
                    log.info(f"INST-01: Using cached instrument master (downloaded {dl_time.isoformat()}).")
            except Exception:
                needs_dl = True

        if needs_dl:
            records = self._download()
            cf.write_text(json.dumps(records))
            mf.write_text(json.dumps({'downloaded_at': ist.isoformat()}))
            log.info(f"Instrument master saved: {len(records)} records.")
        else:
            records = json.loads(cf.read_text())

        self._raw_record_count = len(records)
        self._parse(records)

    def _parse(self, records: list):
        options: List[dict] = []
        futures: List[dict] = []

        for rec in records:
            name      = rec.get('name', '')
            inst_type = rec.get('instrumenttype', '')
            exch      = rec.get('exch_seg', '')
            symbol    = rec.get('symbol', '')
            token     = str(rec.get('token', ''))
            expiry_s  = rec.get('expiry', '')

            if name != 'NIFTY':
                continue
            try:
                expiry_dt = datetime.strptime(expiry_s, "%d%b%Y")
            except ValueError:
                continue

            if inst_type == 'OPTIDX' and exch == 'NFO':
                is_ce = symbol.endswith('CE')
                is_pe = symbol.endswith('PE')
                if not is_ce and not is_pe:
                    continue
                try:
                    strike = round(float(rec.get('strike', 0)) / 100, 2)  # divide by 100; round to avoid float drift
                except (TypeError, ValueError):
                    continue
                options.append({
                    'symbol':      symbol,
                    'token':       token,
                    'strike':      strike,
                    'expiry_str':  expiry_s,            # retain DDMMMYYYY for Greeks API
                    'expiry_dt':   expiry_dt,
                    'option_type': 'CE' if is_ce else 'PE',
                    'exch_seg':    exch,
                })

            elif inst_type == 'FUTIDX' and exch == 'NFO':
                futures.append({
                    'symbol':     symbol,
                    'token':      token,
                    'expiry_str': expiry_s,
                    'expiry_dt':  expiry_dt,
                    'exch_seg':   exch,
                })

        self.options_df = pd.DataFrame(options)
        self.futures_df = pd.DataFrame(futures)
        log.info(f"Parsed {len(self.options_df)} NIFTY OPTIDX, {len(self.futures_df)} NIFTY FUTIDX records.")

        if not self.options_df.empty:
            all_exp = self.options_df['expiry_dt'].unique().tolist()
            self.expiry_classification = self._classify_expiries(all_exp)

        # Resolve nearest NIFTY Futures token
        if not self.futures_df.empty:
            today = now_ist().replace(hour=0, minute=0, second=0, microsecond=0, tzinfo=None)
            fut   = self.futures_df[self.futures_df['expiry_dt'] >= today].sort_values('expiry_dt')
            if not fut.empty:
                row = fut.iloc[0]
                self.nifty_futures_token  = row['token']
                self.nifty_futures_expiry = row['expiry_str']
                log.info(f"NIFTY Futures: token={self.nifty_futures_token}, expiry={self.nifty_futures_expiry}")

    @staticmethod
    def _classify_expiries(expiry_dates: list) -> Dict[datetime, bool]:
        """
        Returns {expiry_dt: is_monthly}.
        Monthly = last expiry in each calendar month.
        NEVER uses weekday — NIFTY weekly expiry moved from Thursday to Tuesday in Sep 2025.
        """
        result: Dict[datetime, bool] = {}
        sorted_dates = sorted(set(expiry_dates))
        for (_y, _m), grp in groupby(sorted_dates, key=lambda d: (d.year, d.month)):
            month_dates = sorted(grp)
            for i, dt in enumerate(month_dates):
                result[dt] = (i == len(month_dates) - 1)   # last in month = monthly
        return result

    def get_available_expiries(self) -> List[datetime]:
        if self.options_df is None or self.options_df.empty:
            return []
        today = now_ist().replace(hour=0, minute=0, second=0, microsecond=0, tzinfo=None)
        return sorted({d for d in self.options_df['expiry_dt'].unique() if d >= today})

    def select_expiry(self, mode: str, manual_str: str = '') -> Tuple[datetime, str, bool]:
        """Returns (expiry_datetime, 'DDMMMYYYY', is_monthly)."""
        expiries = self.get_available_expiries()
        if not expiries:
            raise RuntimeError("INST-04 FAIL: No active expiries found.")

        if mode == 'AUTO':
            selected = expiries[0]
        elif mode == 'NEXT':
            selected = expiries[1] if len(expiries) > 1 else expiries[0]
        elif mode == 'MONTHLY':
            monthly = [e for e in expiries if self.expiry_classification.get(e, False)]
            if not monthly:
                raise RuntimeError("INST-04 FAIL: No monthly expiry available.")
            selected = monthly[0]
        elif mode == 'MANUAL':
            try:
                target = datetime.strptime(manual_str.strip().upper(), "%d%b%Y")
            except ValueError:
                raise RuntimeError(
                    f"INST-04 FAIL: Cannot parse manual expiry '{manual_str}'. "
                    "Use DDMMMYYYY format, e.g. 28OCT2025."
                )
            matches = [e for e in expiries if e.date() == target.date()]
            if not matches:
                raise RuntimeError(
                    f"INST-04 FAIL: Manual expiry '{manual_str}' not found. "
                    f"Available: {[e.strftime('%d%b%Y').upper() for e in expiries[:5]]}"
                )
            selected = matches[0]
        else:
            raise ValueError(f"Unknown expiry mode: {mode}")

        expiry_str = selected.strftime("%d%b%Y").upper()
        is_monthly = self.expiry_classification.get(selected, False)
        log.info(f"Selected expiry: {expiry_str} ({'MONTHLY' if is_monthly else 'WEEKLY'})")
        return selected, expiry_str, is_monthly

    def get_contracts_for_expiry(self, expiry_dt: datetime) -> pd.DataFrame:
        if self.options_df is None or self.options_df.empty:
            return pd.DataFrame()
        mask = self.options_df['expiry_dt'].apply(lambda d: d.date()) == expiry_dt.date()
        return self.options_df[mask].copy()


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 4 — CandleFetcher
# ═════════════════════════════════════════════════════════════════════════════
class CandleFetcher:
    """
    Fetches intraday candle data from exactly two sources.

    SOURCE 1 — NIFTY Spot Index
        Variable: self.spot_token = CONFIG['SPOT_INDEX_TOKEN'] (default '99926000')
        Exchange: CONFIG['SPOT_INDEX_EXCHANGE'] (default 'NSE')
        Use for: OHLC price structure and ATM determination ONLY.
        Do NOT use for VWAP or volume signals — index has no traded volume.

    SOURCE 2 — NIFTY Current-Month Futures
        Variable: self.futures_token  (resolved by InstrumentMasterLoader at startup)
        Exchange: 'NFO'
        Use for: VWAP computation and volume confirmation signals ONLY.
        Do NOT use futures price for ATM or price-structure classification.

    To adapt for BANKNIFTY/FINNIFTY: update CONFIG['SPOT_INDEX_TOKEN'] and pass
    the appropriate InstrumentMasterLoader futures token.

    Date format for getCandleData: YYYY-MM-DD HH:MM  (no seconds, no T separator).
    Any other format produces AB13000 "Invalid date or time format".
    """

    def __init__(self, smart_api: SmartConnect, futures_token: str):
        self.smart_api        = smart_api
        self.spot_token       = CONFIG['SPOT_INDEX_TOKEN']
        self.spot_exchange    = CONFIG['SPOT_INDEX_EXCHANGE']
        self.futures_token    = futures_token
        self.futures_exchange = 'NFO'
        # Last-known-good cache — returned on AB1019 / null response so the
        # cycle can continue using stale data rather than skipping entirely.
        self._last_spot_df:    Optional[pd.DataFrame] = None
        self._last_futures_df: Optional[pd.DataFrame] = None

    @staticmethod
    def _fmt(dt: datetime) -> str:
        """Candle API requires YYYY-MM-DD HH:MM — no seconds, no T separator."""
        return dt.strftime('%Y-%m-%d %H:%M')

    def _fetch(self, exchange: str, token: str, from_dt: datetime, to_dt: datetime) -> Optional[pd.DataFrame]:
        from_str = self._fmt(from_dt)
        to_str   = self._fmt(to_dt)
        params   = {
            "exchange":    exchange,
            "symboltoken": token,
            "interval":    CONFIG['CANDLE_INTERVAL'],
            "fromdate":    from_str,
            "todate":      to_str,
        }

        max_retries = CONFIG['RATE_LIMIT_MAX_RETRIES']
        base_wait   = CONFIG['RATE_LIMIT_RETRY_WAIT']

        for attempt in range(1, max_retries + 1):
            # ── API call ───────────────────────────────────────────────────
            try:
                response = self.smart_api.getCandleData(params)
            except Exception as e:
                err = str(e)
                if 'AB1019' in err:
                    wait = base_wait * (2 ** (attempt - 1))   # 2s, 4s, 8s
                    log.warning(
                        f"getCandleData AB1019 (Too many requests) for token={token} "
                        f"({exchange}). Attempt {attempt}/{max_retries}. "
                        f"Retrying in {wait}s..."
                    )
                    time.sleep(wait)
                    continue
                if 'AB13000' in err:
                    log.error(
                        f"getCandleData AB13000: Invalid date format. "
                        f"fromdate='{from_str}' todate='{to_str}'. "
                        "Ensure format is YYYY-MM-DD HH:MM with no seconds."
                    )
                elif 'AB1004' in err:
                    log.warning(
                        f"getCandleData AB1004: Something went wrong for token={token}. "
                        "Market may be closed or holiday."
                    )
                else:
                    log.warning(f"getCandleData exception for token={token} ({exchange}): {e}")
                return None

            # ── AB1019 surfaced inside the response body (not as exception) ──
            if response and response.get('errorcode') == 'AB1019':
                wait = base_wait * (2 ** (attempt - 1))
                log.warning(
                    f"getCandleData AB1019 (Too many requests) in response for token={token} "
                    f"({exchange}). Attempt {attempt}/{max_retries}. "
                    f"Retrying in {wait}s..."
                )
                time.sleep(wait)
                continue

            # ── Null / empty data ──────────────────────────────────────────
            if not response or response.get('data') is None:
                log.warning(f"getCandleData returned null data for token={token} ({exchange}).")
                return None

            data = response['data']
            if not isinstance(data, list) or len(data) == 0:
                log.warning(f"getCandleData returned empty list for token={token}.")
                return None

            # ── Success: parse and return DataFrame ────────────────────────
            df = pd.DataFrame(data, columns=['timestamp', 'open', 'high', 'low', 'close', 'volume'])
            df['timestamp'] = pd.to_datetime(df['timestamp'])
            for col in ['open', 'high', 'low', 'close', 'volume']:
                df[col] = pd.to_numeric(df[col], errors='coerce')
            return df

        # All retries exhausted for this token
        log.error(
            f"getCandleData AB1019: All {max_retries} retries exhausted for token={token} "
            f"({exchange}). Returning None — caller will use last-known-good data."
        )
        return None

    def _intraday_window(self) -> Tuple[datetime, datetime]:
        ist     = now_ist()
        from_dt = ist.replace(hour=9, minute=15, second=0, microsecond=0)
        return from_dt, ist

    def fetch_spot_candles(self) -> Optional[pd.DataFrame]:
        from_dt, to_dt = self._intraday_window()
        df = self._fetch(self.spot_exchange, self.spot_token, from_dt, to_dt)
        if df is not None:
            self._last_spot_df = df          # update last-known-good cache
        else:
            if self._last_spot_df is not None:
                log.warning(
                    "FEED-01: Spot candle fetch failed (AB1019 or null). "
                    "Using last-known-good spot data from previous cycle."
                )
                df = self._last_spot_df
            else:
                log.warning(
                    "FEED-01: Spot index candle data unavailable. "
                    "Will fallback to last known close for ATM."
                )
        # Sleep between spot and futures calls to avoid back-to-back AB1019
        time.sleep(CONFIG['RATE_LIMIT_INTER_CALL_SLEEP'])
        return df

    def fetch_futures_candles(self) -> Optional[pd.DataFrame]:
        if not self.futures_token:
            log.warning("FEED-03: Futures token not resolved. VWAP and volume signals disabled.")
            return None
        from_dt, to_dt = self._intraday_window()
        df = self._fetch(self.futures_exchange, self.futures_token, from_dt, to_dt)
        if df is not None:
            self._last_futures_df = df       # update last-known-good cache
        else:
            if self._last_futures_df is not None:
                log.warning(
                    "FEED-03: Futures candle fetch failed (AB1019 or null). "
                    "Using last-known-good futures data from previous cycle."
                )
                df = self._last_futures_df
            else:
                log.warning(
                    "FEED-03: Futures candle data unavailable. "
                    "VWAP and volume signals set to NEUTRAL."
                )
        return df


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 5 — OptionChainBuilder
# ═════════════════════════════════════════════════════════════════════════════
class OptionChainBuilder:
    """
    Reconstructs a synthetic strike-wise NIFTY option chain from:
      - instrument master (token mapping + filtered contracts)
      - live getMarketData bulk quote (single NFO call)
      - Option Greeks endpoint (IV, DDMMMYYYY format)
    Change OI is computed internally from snapshot delta — never fetched from API.
    """

    def __init__(self, smart_api: SmartConnect, loader: InstrumentMasterLoader):
        self.smart_api = smart_api
        self.loader    = loader

    @staticmethod
    def determine_atm(spot_price: float) -> float:
        iv = CONFIG['NIFTY_STRIKE_INTERVAL']
        return round(round(spot_price / iv) * iv, 2)

    @staticmethod
    def focus_zone_strikes(atm: float, above: int, below: int) -> List[float]:
        iv = CONFIG['NIFTY_STRIKE_INTERVAL']
        return sorted([atm + i * iv for i in range(-below, above + 1)])

    def _bulk_quotes(self, tokens: List[str]) -> dict:
        """
        Single getMarketData('FULL', {'NFO': [list]}) call.
        CRITICAL: tokens must be a Python list under 'NFO' — not a string, not nested.
        Returns {token: {'ltp', 'oi', 'volume'}}.
        """
        quotes: Dict[str, dict] = {}
        if not tokens:
            return quotes
        try:
            response = self.smart_api.getMarketData('FULL', {'NFO': tokens})
        except Exception as e:
            log.error(f"getMarketData exception: {e}. "
                      "Verify token list format is {{'NFO': [list_of_strings]}}.")
            return quotes

        if not response or not response.get('data'):
            log.error(f"getMarketData returned null/AB2001. Response: {response}")
            return quotes

        fetched   = response['data'].get('fetched',   []) or []
        unfetched = response['data'].get('unfetched', []) or []

        if unfetched:
            log.warning(f"FEED-06: {len(unfetched)} unfetched tokens: {unfetched}. "
                        "Their LTP/OI/volume will be NaN this cycle.")

        for q in fetched:
            token = str(q.get('symbolToken', ''))
            if not token:
                continue
            oi     = q.get('opnInterest',  0)    # exact field name
            volume = q.get('tradeVolume',  0)    # exact field name
            ltp    = q.get('ltp', float('nan'))
            if oi     is None: oi     = 0
            if volume is None: volume = 0
            quotes[token] = {'ltp': ltp, 'oi': oi, 'volume': volume}

        log.info(f"getMarketData: {len(fetched)} fetched, {len(unfetched)} unfetched "
                 f"from {len(tokens)} requested tokens.")
        return quotes

    def _fetch_iv(self, expiry_str: str, is_weekly: bool) -> Dict[Tuple[float, str], float]:
        """Returns {(strike, 'CE'/'PE'): iv_value}. Sets NaN for weekly or on AB9019."""
        iv_map: Dict[Tuple[float, str], float] = {}
        if is_weekly:
            log.warning("FEED-09: Weekly expiry selected. IV set to NaN (Angel One Greeks API "
                        "limitation for weekly expiries).")
            return iv_map
        try:
            payload = {"name": "NIFTY", "expirydate": expiry_str}   # must be DDMMMYYYY
            resp    = self.smart_api.optionGreek(payload)
        except Exception as e:
            err = str(e)
            if 'AB9019' in err:
                log.info("FEED-08: Option Greeks AB9019 — market closed. IV set to NaN.")
            elif 'AB9022' in err:
                log.error(f"FEED-08: Option Greeks AB9022 — invalid expiry format. "
                          f"Sent: '{expiry_str}'. Must be DDMMMYYYY uppercase.")
            else:
                log.warning(f"FEED-08: Option Greeks exception: {e}")
            return iv_map

        if not resp or not resp.get('data'):
            code = resp.get('errorcode', '') if resp else ''
            if code == 'AB9019':
                log.info("FEED-08: Option Greeks returned no data (AB9019) — market may be closed. IV set to NaN.")
            elif code == 'AB9022':
                log.error(f"FEED-08: Option Greeks AB9022 for expiry '{expiry_str}'. Expects DDMMMYYYY uppercase.")
            else:
                log.warning(f"FEED-08: Option Greeks returned null. Code: {code}")
            return iv_map

        for item in resp['data']:
            try:
                strike   = float(item.get('strikePrice', 0))
                opt_type = str(item.get('optionType', '')).upper()
                iv_val   = safe_float(item.get('impliedVolatility', float('nan')))
                if opt_type in ('CE', 'PE'):
                    iv_map[(strike, opt_type)] = iv_val
            except Exception:
                continue
        return iv_map

    def build(self, expiry_dt: datetime, expiry_str: str, is_weekly: bool,
              atm: float, strikes_above: int, strikes_below: int,
              prev_snapshot: Optional[pd.DataFrame]) -> pd.DataFrame:

        contracts = self.loader.get_contracts_for_expiry(expiry_dt)
        if contracts.empty:
            raise RuntimeError(f"INST-04 FAIL: No contracts found for expiry {expiry_str}.")

        focus   = self.focus_zone_strikes(atm, strikes_above, strikes_below)
        subset  = contracts[contracts['strike'].isin(focus)]
        ce_df   = subset[subset['option_type'] == 'CE']
        pe_df   = subset[subset['option_type'] == 'PE']

        all_tokens = list(ce_df['token'].values) + list(pe_df['token'].values)
        if not all_tokens:
            raise RuntimeError("INST-06 FAIL: No tokens in focus zone.")

        quotes = self._bulk_quotes(all_tokens)
        iv_map = self._fetch_iv(expiry_str, is_weekly)

        rows: List[dict] = []
        for strike in focus:
            row = {'strike': strike, 'expiry_str': expiry_str}
            ce  = ce_df[ce_df['strike'] == strike]
            pe  = pe_df[pe_df['strike'] == strike]

            if not ce.empty:
                ct = ce.iloc[0]['token']
                q  = quotes.get(ct, {})
                row.update({
                    'ce_token': ct, 'ce_symbol': ce.iloc[0]['symbol'],
                    'ce_ltp': safe_float(q.get('ltp')),
                    'ce_open_interest': q.get('oi', 0),
                    'ce_volume': q.get('volume', 0),
                    'ce_iv': iv_map.get((strike, 'CE'), float('nan')),
                })
            else:
                row.update({'ce_token': '', 'ce_symbol': '', 'ce_ltp': float('nan'),
                            'ce_open_interest': 0, 'ce_volume': 0, 'ce_iv': float('nan')})

            if not pe.empty:
                pt = pe.iloc[0]['token']
                q  = quotes.get(pt, {})
                row.update({
                    'pe_token': pt, 'pe_symbol': pe.iloc[0]['symbol'],
                    'pe_ltp': safe_float(q.get('ltp')),
                    'pe_open_interest': q.get('oi', 0),
                    'pe_volume': q.get('volume', 0),
                    'pe_iv': iv_map.get((strike, 'PE'), float('nan')),
                })
            else:
                row.update({'pe_token': '', 'pe_symbol': '', 'pe_ltp': float('nan'),
                            'pe_open_interest': 0, 'pe_volume': 0, 'pe_iv': float('nan')})

            rows.append(row)

        df = pd.DataFrame(rows)

        # Change OI = current - previous snapshot OI (never fetched from API)
        if prev_snapshot is not None and not prev_snapshot.empty and 'strike' in prev_snapshot.columns:
            prev = prev_snapshot.set_index('strike')
            def _prev_oi(strike, col):
                if strike not in prev.index:
                    return 0
                val = prev.loc[strike, col]
                # guard against duplicate strikes returning a Series
                return float(val.iloc[0]) if hasattr(val, 'iloc') else float(val)
            df['ce_change_oi'] = df.apply(
                lambda r: r['ce_open_interest'] - _prev_oi(r['strike'], 'ce_open_interest'), axis=1)
            df['pe_change_oi'] = df.apply(
                lambda r: r['pe_open_interest'] - _prev_oi(r['strike'], 'pe_open_interest'), axis=1)
        else:
            df['ce_change_oi'] = 0
            df['pe_change_oi'] = 0
            log.warning("SNAP-01: First cycle — change OI = 0. Do not use change OI signals until cycle 2.")

        return df


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 6 — MetricsCalculator
# ═════════════════════════════════════════════════════════════════════════════
class MetricsCalculator:
    """Computes all option-chain metrics from the synthetic chain DataFrame."""

    def compute(self, chain: pd.DataFrame, prev_chain: Optional[pd.DataFrame]) -> dict:
        m: Dict[str, Any] = {}
        if chain.empty:
            return m

        ce_oi   = chain['ce_open_interest'].fillna(0)
        pe_oi   = chain['pe_open_interest'].fillna(0)
        ce_chg  = chain['ce_change_oi'].fillna(0)
        pe_chg  = chain['pe_change_oi'].fillna(0)
        ce_vol  = chain['ce_volume'].fillna(0)
        pe_vol  = chain['pe_volume'].fillna(0)

        m['total_ce_oi']        = float(ce_oi.sum())
        m['total_pe_oi']        = float(pe_oi.sum())
        m['total_ce_change_oi'] = float(ce_chg.sum())
        m['total_pe_change_oi'] = float(pe_chg.sum())
        m['total_ce_volume']    = float(ce_vol.sum())
        m['total_pe_volume']    = float(pe_vol.sum())

        m['pcr_oi']        = round(m['total_pe_oi']        / m['total_ce_oi'],        3) if m['total_ce_oi'] > 0         else float('nan')
        m['pcr_change_oi'] = round(m['total_pe_change_oi'] / m['total_ce_change_oi'], 3) if m['total_ce_change_oi'] != 0 else float('nan')

        # Support = max PE OI strike; Resistance = max CE OI strike
        pe_max_i = pe_oi.idxmax() if pe_oi.sum() > 0 else None
        ce_max_i = ce_oi.idxmax() if ce_oi.sum() > 0 else None
        m['support_strike']    = float(chain.loc[pe_max_i, 'strike']) if pe_max_i is not None else float('nan')
        m['resistance_strike'] = float(chain.loc[ce_max_i, 'strike']) if ce_max_i is not None else float('nan')

        # Shifts vs previous snapshot
        if prev_chain is not None and not prev_chain.empty:
            p_ce_oi = prev_chain['ce_open_interest'].fillna(0)
            p_pe_oi = prev_chain['pe_open_interest'].fillna(0)
            prev_support    = float(prev_chain.loc[p_pe_oi.idxmax(), 'strike']) if p_pe_oi.sum() > 0 else m['support_strike']
            prev_resistance = float(prev_chain.loc[p_ce_oi.idxmax(), 'strike']) if p_ce_oi.sum() > 0 else m['resistance_strike']
            m['support_shift']    = m['support_strike']    - prev_support    if not math.isnan(m['support_strike'])    else 0.0
            m['resistance_shift'] = m['resistance_strike'] - prev_resistance if not math.isnan(m['resistance_strike']) else 0.0
        else:
            m['support_shift']    = 0.0
            m['resistance_shift'] = 0.0

        # net_oi_momentum: positive = PE building faster than CE (bullish pressure)
        m['net_oi_momentum'] = m['total_pe_change_oi'] - m['total_ce_change_oi']

        total_vol = m['total_ce_volume'] + m['total_pe_volume']
        m['volume_imbalance_ratio'] = round(
            (m['total_pe_volume'] - m['total_ce_volume']) / total_vol, 3) if total_vol > 0 else 0.0

        m['probable_bullish_buildup'] = bool(
            pe_chg[pe_chg > 0].count() > ce_chg[ce_chg > 0].count() and
            not math.isnan(m['pcr_oi']) and m['pcr_oi'] > 1.0)
        m['probable_bearish_buildup'] = bool(
            ce_chg[ce_chg > 0].count() > pe_chg[pe_chg > 0].count() and
            not math.isnan(m['pcr_oi']) and m['pcr_oi'] < 1.0)
        m['probable_short_covering'] = bool(ce_chg[ce_chg < 0].count() > 0 and m['total_ce_change_oi'] < 0)
        m['probable_long_unwinding'] = bool(pe_chg[pe_chg < 0].count() > 0 and m['total_pe_change_oi'] < 0)
        m['upward_pe_base_shift']    = bool(m['support_shift']    > 0)
        m['downward_ce_cap_shift']   = bool(m['resistance_shift'] < 0)

        # Distance of spot from support/resistance (populated by caller)
        m['spot_distance_to_support']    = float('nan')
        m['spot_distance_to_resistance'] = float('nan')
        return m

    def add_spot_distances(self, m: dict, spot: float):
        if not math.isnan(m.get('support_strike', float('nan'))):
            m['spot_distance_to_support']    = round(spot - m['support_strike'],    1)
        if not math.isnan(m.get('resistance_strike', float('nan'))):
            m['spot_distance_to_resistance'] = round(m['resistance_strike'] - spot, 1)


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 7 — SignalEngine
# ═════════════════════════════════════════════════════════════════════════════
class SignalEngine:
    """
    Combines four analysis layers into a final intraday bias.
    VWAP and volume signals use Futures candle data exclusively (Source 2).
    Price structure uses spot index candle data (Source 1).
    All position inferences are rule-based heuristics — NOT actual institutional positions.
    """

    # ── Price structure ────────────────────────────────────────────────────
    def compute_price_structure(self, spot_df: Optional[pd.DataFrame]) -> Tuple[str, str]:
        if spot_df is None or len(spot_df) < 4:
            return 'RANGEBOUND', 'Insufficient candle data for price structure analysis.'
        h  = spot_df['high'].values
        lo = spot_df['low'].values
        n  = len(h)
        tail = slice(max(0, n - 4), n)
        prev = slice(max(0, n - 8), max(0, n - 4))

        hh = all(h[i]  > h[i-1]  for i in range(max(1, n-3), n))
        hl = all(lo[i] > lo[i-1] for i in range(max(1, n-3), n))
        lh = all(h[i]  < h[i-1]  for i in range(max(1, n-3), n))
        ll = all(lo[i] < lo[i-1] for i in range(max(1, n-3), n))

        recent_range = h[tail].max() - lo[tail].min() if n >= 4 else 0
        prior_range  = h[prev].max() - lo[prev].min() if n >= 8 else recent_range
        compressed   = prior_range > 0 and recent_range < prior_range * 0.6

        if hh and hl:
            return 'BULLISH STRUCTURE',  'Higher highs and higher lows — uptrend forming.'
        if lh and ll:
            return 'BEARISH STRUCTURE',  'Lower highs and lower lows — downtrend forming.'
        if compressed:
            return 'RANGEBOUND',         'Range compression detected — potential breakout setup.'
        last_close = spot_df['close'].iloc[-1]
        first_open = spot_df['open'].iloc[0]
        if last_close > first_open * 1.003:
            return 'BULLISH STRUCTURE',  'Mild upward bias intraday.'
        if last_close < first_open * 0.997:
            return 'BEARISH STRUCTURE',  'Mild downward bias intraday.'
        return 'RANGEBOUND', 'No clear directional structure.'

    # ── VWAP (Futures data only) ───────────────────────────────────────────
    def compute_vwap(self, futures_df: Optional[pd.DataFrame]) -> Tuple[float, str, str]:
        if futures_df is None or futures_df.empty:
            return float('nan'), 'NEUTRAL', 'Futures data unavailable — VWAP disabled.'
        df = futures_df.copy()
        if df['volume'].fillna(0).sum() == 0:
            return float('nan'), 'NEUTRAL', 'Zero Futures volume — VWAP disabled.'
        df['typical']  = (df['high'] + df['low'] + df['close']) / 3
        df['cum_tpv']  = (df['typical'] * df['volume']).cumsum()
        df['cum_vol']  = df['volume'].cumsum()
        # Guard: replace 0 cumulative volume with NaN to avoid inf in vwap
        df['vwap']     = df['cum_tpv'] / df['cum_vol'].replace(0, float('nan'))
        vwap           = float(df['vwap'].iloc[-1])
        close          = float(df['close'].iloc[-1])
        if   close > vwap * 1.001: return vwap, 'BULLISH', f'Price {close:.0f} above VWAP {vwap:.0f}.'
        elif close < vwap * 0.999: return vwap, 'BEARISH', f'Price {close:.0f} below VWAP {vwap:.0f}.'
        else:                      return vwap, 'NEUTRAL',  f'Price near VWAP {vwap:.0f}.'

    # ── Volume confirmation (Futures data only) ────────────────────────────
    def compute_volume_confirmation(self, futures_df: Optional[pd.DataFrame], ps: str) -> Tuple[str, str]:
        if futures_df is None or futures_df.empty or futures_df['volume'].fillna(0).sum() == 0:
            return 'NEUTRAL', 'No Futures volume data available.'
        vols     = futures_df['volume'].fillna(0).values
        avg_vol  = float(np.mean(vols[:-1])) if len(vols) > 1 else float(vols[0]) if len(vols) > 0 else 1
        last_vol = float(vols[-1])
        closes   = futures_df['close'].values
        up_move  = closes[-1] > closes[-2] if len(closes) >= 2 else True
        expanding   = last_vol > avg_vol * 1.5
        contracting = last_vol < avg_vol * 0.5
        if expanding and up_move and 'BULLISH' in ps:    return 'BULLISH', 'Breakout volume expansion confirmed.'
        if expanding and not up_move and 'BEARISH' in ps: return 'BEARISH', 'Breakdown volume expansion confirmed.'
        if expanding and up_move and 'BEARISH' in ps:    return 'BEARISH', 'High-volume rejection on up move.'
        if contracting and 'BULLISH' in ps:               return 'NEUTRAL', 'Weak breakout — volume not confirming.'
        if contracting and 'BEARISH' in ps:               return 'NEUTRAL', 'Weak breakdown — volume not confirming.'
        return 'NEUTRAL', 'Volume inconclusive.'

    # ── Trap detection ─────────────────────────────────────────────────────
    def detect_trap(self, ps: str, vwap_bias: str, vol_bias: str,
                    metrics: dict, spot_close: float, vwap: float) -> Tuple[bool, str]:
        if math.isnan(vwap) or math.isnan(spot_close):
            return False, ''
        bullish_trap = (
            'BULLISH' in ps and
            vol_bias in ('NEUTRAL', 'BEARISH') and
            spot_close < vwap and
            metrics.get('resistance_shift', 0) > 0
        )
        bearish_trap = (
            'BEARISH' in ps and
            vol_bias in ('NEUTRAL', 'BULLISH') and
            spot_close > vwap and
            metrics.get('support_shift', 0) <= 0
        )
        if bullish_trap:
            return True, 'BULLISH TRAP: Price broke up but volume weak; now below VWAP with CE resistance intact.'
        if bearish_trap:
            return True, 'BEARISH TRAP: Price broke down but reversed above VWAP with PE support intact.'
        return False, ''

    # ── Score ──────────────────────────────────────────────────────────────
    def compute_score(self, m: dict, ps: str, vwap_bias: str, vol_bias: str) -> int:
        C = CONFIG
        score = 0
        pe_chg = m.get('total_pe_change_oi', 0)
        ce_chg = m.get('total_ce_change_oi', 0)
        if pe_chg > 0 and ce_chg <= 0:          score += C['SCORE_STRONG_PE_WRITING']
        if ce_chg > 0 and pe_chg <= 0:          score += C['SCORE_STRONG_CE_WRITING']
        if m.get('probable_short_covering'):     score += C['SCORE_CE_UNWINDING_RISING']
        if m.get('probable_long_unwinding'):     score += C['SCORE_PE_UNWINDING_FALLING']
        ss_ = m.get('support_shift', 0)
        rs_ = m.get('resistance_shift', 0)
        if ss_ > 0: score += C['SCORE_SUPPORT_SHIFT_UP']
        if ss_ < 0: score += C['SCORE_SUPPORT_SHIFT_DOWN']
        if rs_ > 0: score += C['SCORE_RESISTANCE_SHIFT_UP']
        if rs_ < 0: score += C['SCORE_RESISTANCE_SHIFT_DOWN']
        pcr = m.get('pcr_oi', float('nan'))
        if not math.isnan(pcr):
            if pcr > 1.2: score += C['SCORE_BULLISH_PCR']
            elif pcr < 0.8: score += C['SCORE_BEARISH_PCR']
        vi = m.get('volume_imbalance_ratio', 0)
        if vi >  0.2: score += C['SCORE_BULLISH_VOL_IMBALANCE']
        if vi < -0.2: score += C['SCORE_BEARISH_VOL_IMBALANCE']
        if 'BULLISH' in ps:    score += C['SCORE_BULLISH_PRICE_STRUCTURE']
        elif 'BEARISH' in ps:  score += C['SCORE_BEARISH_PRICE_STRUCTURE']
        if 'BULLISH' in vwap_bias: score += C['SCORE_ABOVE_VWAP']
        elif 'BEARISH' in vwap_bias: score += C['SCORE_BELOW_VWAP']
        if 'BULLISH' in vol_bias: score += C['SCORE_BULLISH_VOL_CONFIRM']
        elif 'BEARISH' in vol_bias: score += C['SCORE_BEARISH_VOL_CONFIRM']
        return score

    def classify_bias(self, score: int) -> str:
        C = CONFIG
        if   score >=  C['BIAS_STRONG_BULLISH']:  return 'STRONG BULLISH'
        elif score >=  C['BIAS_BULLISH']:          return 'BULLISH'
        elif score >=  C['BIAS_MILD_BULLISH']:     return 'MILD BULLISH'
        elif score >   C['BIAS_MILD_BEARISH']:     return 'NEUTRAL'
        elif score >   C['BIAS_BEARISH']:          return 'MILD BEARISH'      # -3, -2, -1  (> -4)
        elif score >   C['BIAS_STRONG_BEARISH']:   return 'BEARISH'           # -5, -4      (> -6)
        else:                                      return 'STRONG BEARISH'    # -6 and below

    def compute_confidence(self, score: int, trap: bool, warn_count: int) -> float:
        base = min(abs(score) / 12.0, 1.0) * 100   # 12 = theoretical max ±score
        if trap: base *= 0.5
        base -= warn_count * 2
        return round(max(base, 0.0), 1)

    def detect_event_tag(self, m: dict, bias: str, trap: bool, confidence: float) -> str:
        if trap:                                        return 'TRAP WARNING'
        if confidence < 35:                             return 'LOW CONFIDENCE'
        if m.get('probable_short_covering'):            return 'PROBABLE SHORT COVERING'
        if m.get('probable_long_unwinding'):            return 'PROBABLE LONG UNWINDING'
        if m.get('upward_pe_base_shift') and 'BULLISH' in bias:  return 'BULLISH SHIFT'
        if m.get('downward_ce_cap_shift') and 'BEARISH' in bias: return 'BEARISH SHIFT'
        if bias == 'NEUTRAL':                           return 'RANGEBOUND'
        return bias

    def build_reasoning(self, m: dict, ps: str, vwap_bias: str, vol_bias: str,
                        bias: str, score: int, trap_msg: str) -> str:
        parts = []
        pcr = m.get('pcr_oi', float('nan'))
        if not math.isnan(pcr): parts.append(f"PCR OI={pcr:.2f}")
        sup = m.get('support_strike', float('nan'))
        res = m.get('resistance_strike', float('nan'))
        if not math.isnan(sup): parts.append(f"Sup={sup:.0f}")
        if not math.isnan(res): parts.append(f"Res={res:.0f}")
        parts += [f"PS={ps}", f"VWAP={vwap_bias}", f"Vol={vol_bias}", f"Score={score}→{bias}"]
        if trap_msg: parts.append(f"TRAP: {trap_msg}")
        return ' | '.join(parts)

    def run(self, metrics: dict,
            spot_df: Optional[pd.DataFrame], futures_df: Optional[pd.DataFrame],
            warn_count: int) -> dict:
        ps, ps_reason           = self.compute_price_structure(spot_df)
        vwap, vwap_bias, vr     = self.compute_vwap(futures_df)
        vol_bias, vol_reason    = self.compute_volume_confirmation(futures_df, ps)
        spot_close              = float(spot_df['close'].iloc[-1]) if spot_df is not None and not spot_df.empty else float('nan')
        trap, trap_msg          = self.detect_trap(ps, vwap_bias, vol_bias, metrics, spot_close, vwap)
        score                   = self.compute_score(metrics, ps, vwap_bias, vol_bias)
        bias                    = self.classify_bias(score)
        confidence              = self.compute_confidence(score, trap, warn_count)
        event_tag               = self.detect_event_tag(metrics, bias, trap, confidence)
        reasoning               = self.build_reasoning(metrics, ps, vwap_bias, vol_bias, bias, score, trap_msg)
        return {
            'price_structure': ps,    'ps_reason':    ps_reason,
            'vwap':            vwap,  'vwap_bias':    vwap_bias,  'vwap_reason': vr,
            'vol_bias':        vol_bias, 'vol_reason': vol_reason,
            'trap':            trap,  'trap_msg':     trap_msg,
            'score':           score, 'bias':         bias,
            'confidence':      confidence, 'event_tag': event_tag,
            'reasoning':       reasoning,
        }


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 8 — StartupChecker
# ═════════════════════════════════════════════════════════════════════════════
class StartupChecker:
    """
    Runs all 30 startup checks across 5 groups.
    FAIL on any critical check halts the program.
    WARN continues with a persistent indicator.
    Results are written to STARTUP_CHECKLIST tab.
    """

    def __init__(self, smart_api_client: 'SmartApiClient',
                 loader: 'InstrumentMasterLoader',
                 spreadsheet: gspread.Spreadsheet,
                 cfg: dict,
                 expiry_dt: Optional[datetime],
                 expiry_str: str,
                 is_weekly: bool,
                 spot_df: Optional[pd.DataFrame],
                 futures_df: Optional[pd.DataFrame],
                 chain: Optional[pd.DataFrame],
                 prev_chain: Optional[pd.DataFrame],
                 score: Optional[int],
                 prev_atm: Optional[float],
                 current_atm: Optional[float],
                 prev_cycle_ts: Optional[datetime],
                 cycle_num: int):
        self.sac          = smart_api_client
        self.loader       = loader
        self.spreadsheet  = spreadsheet
        self.cfg          = cfg
        self.expiry_dt    = expiry_dt
        self.expiry_str   = expiry_str
        self.is_weekly    = is_weekly
        self.spot_df      = spot_df
        self.futures_df   = futures_df
        self.chain        = chain
        self.prev_chain   = prev_chain
        self.score        = score
        self.prev_atm     = prev_atm
        self.current_atm  = current_atm
        self.prev_cycle_ts = prev_cycle_ts
        self.cycle_num    = cycle_num
        self.results: List[dict] = []

    def _add(self, check_id: str, group: str, desc: str, status: str, detail: str):
        ts = now_ist().strftime('%Y-%m-%d %H:%M:%S')
        self.results.append({
            'id': check_id, 'group': group, 'desc': desc,
            'status': status, 'detail': detail, 'ts': ts
        })
        log.info(f"[{status}] {check_id}: {detail}")

    # ── GROUP 1: System ────────────────────────────────────────────────────
    def _sys01_ntp(self):
        drift = None
        for server in [CONFIG['NTP_PRIMARY'], CONFIG['NTP_FALLBACK']]:
            try:
                client   = ntplib.NTPClient()
                response = client.request(server, version=3)
                drift    = abs(response.offset)   # pre-calculated offset — correct method
                break
            except Exception:
                continue
        if drift is None:
            self._add('SYS-01', 'System', 'System clock accuracy', 'WARN',
                      'NTP servers unreachable. Clock accuracy cannot be verified. Ensure system time is synchronized.')
        elif drift > CONFIG['NTP_DRIFT_FAIL_SECONDS']:
            self._add('SYS-01', 'System', 'System clock accuracy', 'FAIL',
                      f'Clock drift {drift:.1f}s exceeds {CONFIG["NTP_DRIFT_FAIL_SECONDS"]}s threshold. Sync system clock.')
        elif drift > CONFIG['NTP_DRIFT_WARN_SECONDS']:
            self._add('SYS-01', 'System', 'System clock accuracy', 'WARN',
                      f'Clock drift {drift:.1f}s exceeds {CONFIG["NTP_DRIFT_WARN_SECONDS"]}s warn threshold.')
        else:
            self._add('SYS-01', 'System', 'System clock accuracy', 'PASS', f'Clock drift {drift:.3f}s — within tolerance.')

    def _sys02_market_hours(self):
        ist  = now_ist()
        open_t  = ist.replace(hour=CONFIG['MARKET_OPEN_HOUR'],  minute=CONFIG['MARKET_OPEN_MINUTE'],  second=0)
        close_t = ist.replace(hour=CONFIG['MARKET_CLOSE_HOUR'], minute=CONFIG['MARKET_CLOSE_MINUTE'], second=0)
        if ist.weekday() >= 5 or not (open_t <= ist <= close_t):
            self._add('SYS-02', 'System', 'Market hours check', 'WARN',
                      f'Outside NSE market hours ({ist.strftime("%H:%M")} IST). Data may be stale.')
        else:
            self._add('SYS-02', 'System', 'Market hours check', 'PASS',
                      f'Within market hours ({ist.strftime("%H:%M")} IST).')

    def _sys03_sheets_accessible(self):
        try:
            ws = self.spreadsheet.worksheet('DASHBOARD')
            ws.acell('A1')
            self._add('SYS-03', 'System', 'Google Sheet accessible and writable', 'PASS',
                      'DASHBOARD tab read successfully.')
        except Exception as e:
            self._add('SYS-03', 'System', 'Google Sheet accessible and writable', 'FAIL',
                      f'Sheet access error: {e}. Check service account permissions and sharing.')

    def _sys04_output_folders(self):
        try:
            for d in ['logs', 'cache']:
                p = pathlib.Path(d)
                p.mkdir(exist_ok=True)
                test = p / '.write_test'
                test.write_text('ok')
                test.unlink()
            self._add('SYS-04', 'System', 'Output folder writable', 'PASS', 'logs/, cache/ are writable.')
        except Exception as e:
            self._add('SYS-04', 'System', 'Output folder writable', 'WARN', f'Folder write test failed: {e}')

    def _sys05_dependencies(self):
        import importlib
        pkgs = {
            'SmartApi':                     'smartapi-python',
            'pandas':                       'pandas',
            'numpy':                        'numpy',
            'gspread':                      'gspread',
            'google.oauth2.service_account':'google-auth',
            'pyotp':                        'pyotp',
            'requests':                     'requests',
            'ntplib':                       'ntplib',
        }
        failed = []
        for mod, pkg in pkgs.items():
            try:
                importlib.import_module(mod)
            except ImportError:
                failed.append(pkg)
        if failed:
            self._add('SYS-05', 'System', 'Python dependency check', 'FAIL',
                      f"Missing packages: {failed}. Run: pip install {' '.join(failed)}")
        else:
            self._add('SYS-05', 'System', 'Python dependency check', 'PASS', 'All required packages importable.')

    # ── GROUP 2: Auth ──────────────────────────────────────────────────────
    def _auth01_tokens(self):
        if self.sac.auth_token and self.sac.refresh_token:
            self._add('AUTH-01', 'Auth', 'Login success and session token validity', 'PASS',
                      'authToken and refreshToken are non-empty.')
        else:
            missing = [k for k, v in [('authToken', self.sac.auth_token), ('refreshToken', self.sac.refresh_token)] if not v]
            self._add('AUTH-01', 'Auth', 'Login success and session token validity', 'FAIL',
                      f"Missing tokens: {missing}. Re-run login.")

    def _auth02_credential_errors(self):
        # This check documents what was caught at login; passes if login succeeded
        if self.sac.auth_token:
            self._add('AUTH-02', 'Auth', 'Login credential and TOTP error handling', 'PASS',
                      'Login completed without credential errors.')
        else:
            self._add('AUTH-02', 'Auth', 'Login credential and TOTP error handling', 'FAIL',
                      'Login failed. Check AB7001 (MPIN) and AB1050 (TOTP) in log.')

    def _auth03_renewal(self):
        ist = now_ist()
        in_window = (ist.hour == CONFIG['RENEWAL_WINDOW_START_HOUR'] and
                     ist.minute >= CONFIG['RENEWAL_WINDOW_START_MINUTE'])
        if in_window:
            self._add('AUTH-03', 'Auth', 'Session midnight renewal check', 'WARN',
                      'Within 23:30–23:59 renewal window. Session renewal triggered.')
            self.sac.check_and_renew_session()
        else:
            self._add('AUTH-03', 'Auth', 'Session midnight renewal check', 'PASS',
                      f'Outside renewal window ({ist.strftime("%H:%M")} IST).')

    def _auth04_refresh_token(self):
        if self.sac.refresh_token:
            self._add('AUTH-04', 'Auth', 'refreshToken captured at login', 'PASS', 'refreshToken is non-empty.')
        else:
            self._add('AUTH-04', 'Auth', 'refreshToken captured at login', 'FAIL',
                      'refreshToken is empty. Session midnight renewal will fail. Re-run login.')

    def _auth05_feed_token(self):
        if self.sac.feed_token:
            self._add('AUTH-05', 'Auth', 'Feed token availability', 'PASS', 'feedToken is non-empty.')
        else:
            self._add('AUTH-05', 'Auth', 'Feed token availability', 'WARN',
                      'feedToken is empty. Polling mode unaffected; WebSocket integration will not be available.')

    # ── GROUP 3: Instrument ────────────────────────────────────────────────
    def _inst01_freshness(self):
        ist      = now_ist()
        date_str = ist.strftime('%Y%m%d')
        mf       = self.loader._meta_file(date_str)
        if not mf.exists():
            self._add('INST-01', 'Instrument', 'Instrument master freshness', 'FAIL',
                      'No cache meta file found for today. Instrument master not loaded.')
            return
        try:
            meta    = json.loads(mf.read_text())
            dl_time = datetime.fromisoformat(meta['downloaded_at'])
            self._add('INST-01', 'Instrument', 'Instrument master freshness', 'PASS',
                      f'Downloaded at {dl_time.strftime("%H:%M:%S")} IST today.')
        except Exception as e:
            self._add('INST-01', 'Instrument', 'Instrument master freshness', 'WARN', f'Meta read error: {e}')

    def _inst02_record_count(self):
        n = self.loader._raw_record_count
        if n < CONFIG['MIN_INSTRUMENT_RECORDS_FAIL']:
            self._add('INST-02', 'Instrument', 'Instrument master record count', 'FAIL',
                      f'Only {n} records (< {CONFIG["MIN_INSTRUMENT_RECORDS_FAIL"]}). Data likely corrupt.')
        elif n < CONFIG['MIN_INSTRUMENT_RECORDS']:
            self._add('INST-02', 'Instrument', 'Instrument master record count', 'WARN',
                      f'{n} records (< {CONFIG["MIN_INSTRUMENT_RECORDS"]} expected). Some contracts may be missing.')
        else:
            self._add('INST-02', 'Instrument', 'Instrument master record count', 'PASS', f'{n} records.')

    def _inst03_nifty_options(self):
        if self.loader.options_df is None or self.loader.options_df.empty:
            self._add('INST-03', 'Instrument', 'NIFTY option contracts found', 'FAIL',
                      'No NIFTY option contracts found. Verify filter uses name=="NIFTY" and '
                      'instrumenttype=="OPTIDX". Do NOT filter by symbol=="NIFTY" — no contract '
                      'has the bare string NIFTY as its full symbol.')
        else:
            self._add('INST-03', 'Instrument', 'NIFTY option contracts found', 'PASS',
                      f'{len(self.loader.options_df)} NIFTY OPTIDX records found.')

    def _inst04_expiry(self):
        if not self.expiry_dt:
            self._add('INST-04', 'Instrument', 'Selected expiry exists', 'FAIL',
                      'Selected expiry is None. Expiry selection failed.')
        else:
            contracts = self.loader.get_contracts_for_expiry(self.expiry_dt)
            if contracts.empty:
                self._add('INST-04', 'Instrument', 'Selected expiry exists', 'FAIL',
                          f'Expiry {self.expiry_str} not found or has no contracts.')
            else:
                self._add('INST-04', 'Instrument', 'Selected expiry exists', 'PASS',
                          f'{len(contracts)} contracts for expiry {self.expiry_str}.')

    def _inst05_futures_token(self):
        token = self.loader.nifty_futures_token
        if not token:
            self._add('INST-05', 'Instrument', 'NIFTY Futures token resolved', 'FAIL',
                      'No NIFTY FUTIDX contract found. VWAP and volume signals unavailable.')
            return
        expiry = self.loader.nifty_futures_expiry
        try:
            exp_dt    = datetime.strptime(expiry, "%d%b%Y")
            days_left = (exp_dt - now_ist().replace(tzinfo=None)).days
        except Exception:
            days_left = 99
        if days_left < 0:
            self._add('INST-05', 'Instrument', 'NIFTY Futures token resolved', 'FAIL',
                      f'Futures contract {expiry} has already expired ({abs(days_left)} days ago). '
                      'Reload instrument master to pick up the next contract.')
        elif days_left <= 3:
            self._add('INST-05', 'Instrument', 'NIFTY Futures token resolved', 'WARN',
                      f'Futures expiry {expiry} is within {days_left} days. Consider rollover.')
        else:
            self._add('INST-05', 'Instrument', 'NIFTY Futures token resolved', 'PASS',
                      f'Token={token}, expiry={expiry}, {days_left} days remaining.')

    def _inst06_focus_zone(self):
        if self.chain is None or self.chain.empty or not self.current_atm:
            self._add('INST-06', 'Instrument', 'Focus zone strike coverage', 'WARN',
                      'Chain not yet built — cannot verify coverage.')
            return
        above = self.cfg.get('strikes_above', 5)
        below = self.cfg.get('strikes_below', 5)
        total = above + below + 1
        ce_ok = self.chain['ce_token'].apply(bool).sum()
        pe_ok = self.chain['pe_token'].apply(bool).sum()
        ratio = min(ce_ok, pe_ok) / total if total > 0 else 0
        if ratio < CONFIG['MIN_QUOTE_COVERAGE_FAIL']:
            self._add('INST-06', 'Instrument', 'Focus zone strike coverage', 'FAIL',
                      f'Only {ratio:.0%} of focus-zone strikes have both CE and PE.')
        elif ratio < CONFIG['MIN_QUOTE_COVERAGE_WARN']:
            self._add('INST-06', 'Instrument', 'Focus zone strike coverage', 'WARN',
                      f'{ratio:.0%} of focus-zone strikes covered.')
        else:
            self._add('INST-06', 'Instrument', 'Focus zone strike coverage', 'PASS',
                      f'{ratio:.0%} coverage ({ce_ok} CE, {pe_ok} PE out of {total} strikes).')

    # ── GROUP 4: Feed ──────────────────────────────────────────────────────
    def _feed01_spot_candle(self):
        if self.spot_df is None or self.spot_df.empty:
            self._add('FEED-01', 'Feed', 'Spot index candle data received', 'FAIL',
                      'No spot candle data. ATM will use last known close.')
        else:
            self._add('FEED-01', 'Feed', 'Spot index candle data received', 'PASS',
                      f'{len(self.spot_df)} candles returned.')

    def _feed02_spot_recency(self):
        if self.spot_df is None or self.spot_df.empty:
            self._add('FEED-02', 'Feed', 'Spot candle data recency', 'FAIL', 'No spot data.')
            return
        last_ts = self.spot_df['timestamp'].iloc[-1]
        ist     = now_ist()
        if hasattr(last_ts, 'to_pydatetime'):
            last_ts = last_ts.to_pydatetime().replace(tzinfo=None)
        gap_min = abs((ist - last_ts).total_seconds() / 60)
        if gap_min > CONFIG['CANDLE_RECENCY_FAIL_MINUTES']:
            self._add('FEED-02', 'Feed', 'Spot candle data recency', 'FAIL',
                      f'Last candle is {gap_min:.1f} min old (>{CONFIG["CANDLE_RECENCY_FAIL_MINUTES"]}m).')
        elif gap_min > CONFIG['CANDLE_RECENCY_WARN_MINUTES']:
            self._add('FEED-02', 'Feed', 'Spot candle data recency', 'WARN',
                      f'Last candle is {gap_min:.1f} min old.')
        else:
            self._add('FEED-02', 'Feed', 'Spot candle data recency', 'PASS',
                      f'Last candle {gap_min:.1f} min ago.')

    def _feed03_futures_candle(self):
        if self.futures_df is None or self.futures_df.empty:
            self._add('FEED-03', 'Feed', 'Futures candle data received', 'WARN',
                      'No Futures candle data. VWAP and volume signals disabled.')
        else:
            self._add('FEED-03', 'Feed', 'Futures candle data received', 'PASS',
                      f'{len(self.futures_df)} candles returned.')

    def _feed04_futures_volume(self):
        if self.futures_df is None or self.futures_df.empty:
            self._add('FEED-04', 'Feed', 'Futures candle volume non-zero', 'WARN', 'No Futures data.')
            return
        if self.futures_df['volume'].fillna(0).sum() == 0:
            self._add('FEED-04', 'Feed', 'Futures candle volume non-zero', 'WARN',
                      'All Futures candles have zero volume. VWAP signals set to NEUTRAL.')
        else:
            self._add('FEED-04', 'Feed', 'Futures candle volume non-zero', 'PASS',
                      f'Total Futures volume: {int(self.futures_df["volume"].sum()):,}')

    def _feed05_option_quotes(self):
        if self.chain is None or self.chain.empty:
            self._add('FEED-05', 'Feed', 'Option quote data received', 'FAIL',
                      'Chain not built. getMarketData may have returned AB2001 or null.')
            return
        valid = self.chain['ce_ltp'].notna().sum() + self.chain['pe_ltp'].notna().sum()
        if valid == 0:
            self._add('FEED-05', 'Feed', 'Option quote data received', 'FAIL',
                      'Zero valid LTP values. Check getMarketData token list format.')
        else:
            self._add('FEED-05', 'Feed', 'Option quote data received', 'PASS',
                      f'{valid} valid LTP values received.')

    def _feed06_coverage(self):
        if self.chain is None or self.chain.empty:
            self._add('FEED-06', 'Feed', 'Option quote coverage ratio', 'WARN', 'Chain unavailable.')
            return
        n       = len(self.chain)
        ce_ok   = self.chain['ce_ltp'].notna().sum()
        pe_ok   = self.chain['pe_ltp'].notna().sum()
        ratio   = (ce_ok + pe_ok) / (2 * n) if n > 0 else 0
        if ratio < CONFIG['MIN_QUOTE_COVERAGE_FAIL']:
            self._add('FEED-06', 'Feed', 'Option quote coverage ratio', 'FAIL',
                      f'Only {ratio:.0%} quote coverage ({ce_ok} CE + {pe_ok} PE out of {n*2}).')
        elif ratio < CONFIG['MIN_QUOTE_COVERAGE_WARN']:
            self._add('FEED-06', 'Feed', 'Option quote coverage ratio', 'WARN',
                      f'{ratio:.0%} coverage.')
        else:
            self._add('FEED-06', 'Feed', 'Option quote coverage ratio', 'PASS',
                      f'{ratio:.0%} coverage ({ce_ok} CE + {pe_ok} PE).')

    def _feed07_oi(self):
        if self.chain is None or self.chain.empty:
            self._add('FEED-07', 'Feed', 'OI data availability', 'WARN', 'Chain unavailable.')
            return
        ce_oi = self.chain['ce_open_interest'].sum()
        pe_oi = self.chain['pe_open_interest'].sum()
        if ce_oi == 0 and pe_oi == 0:
            self._add('FEED-07', 'Feed', 'OI data availability', 'WARN',
                      'All opnInterest values are zero. OI signals will be unreliable.')
        else:
            self._add('FEED-07', 'Feed', 'OI data availability', 'PASS',
                      f'CE OI={ce_oi:,.0f}, PE OI={pe_oi:,.0f}')

    def _feed08_iv(self):
        if self.chain is None or self.chain.empty:
            self._add('FEED-08', 'Feed', 'Option Greeks / IV availability', 'WARN', 'Chain unavailable.')
            return
        valid_iv = self.chain[['ce_iv', 'pe_iv']].stack().dropna()
        valid_iv = valid_iv[valid_iv > 0]
        if valid_iv.empty:
            self._add('FEED-08', 'Feed', 'Option Greeks / IV availability', 'WARN',
                      'All IV values are NaN or zero. Greeks endpoint may be unavailable.')
        else:
            self._add('FEED-08', 'Feed', 'Option Greeks / IV availability', 'PASS',
                      f'{len(valid_iv)} non-zero IV values received.')

    def _feed09_weekly_iv(self):
        if self.is_weekly:
            self._add('FEED-09', 'Feed', 'Weekly expiry IV warning', 'WARN',
                      f'Weekly expiry {self.expiry_str} selected. IV values set to NaN due to '
                      'known Angel One Option Greeks API limitation for weekly expiries.')
        else:
            self._add('FEED-09', 'Feed', 'Weekly expiry IV warning', 'PASS',
                      f'Monthly expiry {self.expiry_str} — IV expected to be available.')

    # ── GROUP 5: Snapshot ──────────────────────────────────────────────────
    def _snap01_first_cycle(self):
        if self.cycle_num <= 1:
            self._add('SNAP-01', 'Snapshot', 'First cycle change OI warning', 'WARN',
                      'First cycle — no previous snapshot. Change OI = 0. Do not use change OI signals.')
        else:
            self._add('SNAP-01', 'Snapshot', 'First cycle change OI warning', 'PASS',
                      f'Cycle {self.cycle_num} — change OI computed from previous snapshot.')

    def _snap02_snapshot_age(self):
        if self.prev_cycle_ts is None:
            self._add('SNAP-02', 'Snapshot', 'Snapshot age at cycle start', 'PASS', 'First run.')
            return
        elapsed = (now_ist() - self.prev_cycle_ts).total_seconds() / 60
        threshold = self.cfg.get('interval_minutes', 5) * 2
        if elapsed > threshold:
            self._add('SNAP-02', 'Snapshot', 'Snapshot age at cycle start', 'WARN',
                      f'Last cycle was {elapsed:.1f} min ago (> 2× configured {self.cfg["interval_minutes"]}m interval).')
        else:
            self._add('SNAP-02', 'Snapshot', 'Snapshot age at cycle start', 'PASS',
                      f'Last cycle {elapsed:.1f} min ago.')

    def _snap03_atm_change(self):
        if self.prev_atm is None or self.current_atm is None:
            self._add('SNAP-03', 'Snapshot', 'ATM strike change detection', 'PASS', 'No previous ATM to compare.')
            return
        delta = abs(self.current_atm - self.prev_atm)
        if delta > CONFIG['ATM_CHANGE_WARN_POINTS']:
            self._add('SNAP-03', 'Snapshot', 'ATM strike change detection', 'WARN',
                      f'ATM shifted {delta:.0f} pts in one cycle (>{CONFIG["ATM_CHANGE_WARN_POINTS"]}). '
                      'Spot may have gapped or data spike detected.')
        else:
            self._add('SNAP-03', 'Snapshot', 'ATM strike change detection', 'PASS',
                      f'ATM delta {delta:.0f} pts.')

    def _snap04_score_boundary(self):
        if self.score is None:
            self._add('SNAP-04', 'Snapshot', 'Score boundary sanity check', 'PASS', 'Score not yet computed.')
            return
        max_possible = 12   # theoretical max: ±(2+2+1+1+1+1+2+1+1) = ±12
        if abs(self.score) > max_possible:
            self._add('SNAP-04', 'Snapshot', 'Score boundary sanity check', 'WARN',
                      f'Score {self.score} outside expected range ±{max_possible}. Possible data anomaly.')
        else:
            self._add('SNAP-04', 'Snapshot', 'Score boundary sanity check', 'PASS',
                      f'Score {self.score} within ±{max_possible}.')

    def _snap05_strike_alignment(self):
        if self.chain is None or self.prev_chain is None or self.prev_chain.empty:
            self._add('SNAP-05', 'Snapshot', 'Previous snapshot strike alignment', 'PASS',
                      'No previous snapshot to compare.')
            return
        cur_strikes  = set(self.chain['strike'].tolist())
        prev_strikes = set(self.prev_chain['strike'].tolist())
        if not cur_strikes:
            self._add('SNAP-05', 'Snapshot', 'Previous snapshot strike alignment', 'WARN', 'Empty current chain.')
            return
        overlap = len(cur_strikes & prev_strikes) / len(cur_strikes)
        if overlap < 0.5:
            self._add('SNAP-05', 'Snapshot', 'Previous snapshot strike alignment', 'WARN',
                      f'Only {overlap:.0%} strike overlap with previous snapshot. ATM may have shifted significantly.')
        else:
            self._add('SNAP-05', 'Snapshot', 'Previous snapshot strike alignment', 'PASS',
                      f'{overlap:.0%} strike alignment with previous snapshot.')

    # ── Orchestrator ───────────────────────────────────────────────────────
    def run_all(self) -> Tuple[int, int, List[dict]]:
        self.results = []
        # GROUP 1
        self._sys01_ntp()
        self._sys02_market_hours()
        self._sys03_sheets_accessible()
        self._sys04_output_folders()
        self._sys05_dependencies()
        # GROUP 2
        self._auth01_tokens()
        self._auth02_credential_errors()
        self._auth03_renewal()
        self._auth04_refresh_token()
        self._auth05_feed_token()
        # GROUP 3
        self._inst01_freshness()
        self._inst02_record_count()
        self._inst03_nifty_options()
        self._inst04_expiry()
        self._inst05_futures_token()
        self._inst06_focus_zone()
        # GROUP 4
        self._feed01_spot_candle()
        self._feed02_spot_recency()
        self._feed03_futures_candle()
        self._feed04_futures_volume()
        self._feed05_option_quotes()
        self._feed06_coverage()
        self._feed07_oi()
        self._feed08_iv()
        self._feed09_weekly_iv()
        # GROUP 5
        self._snap01_first_cycle()
        self._snap02_snapshot_age()
        self._snap03_atm_change()
        self._snap04_score_boundary()
        self._snap05_strike_alignment()

        warns = sum(1 for r in self.results if r['status'] == 'WARN')
        fails = sum(1 for r in self.results if r['status'] == 'FAIL')
        log.info(f"Checklist complete: {len(self.results)} checks, {warns} WARN, {fails} FAIL.")
        return warns, fails, self.results


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 9 — SheetsWriter
# ═════════════════════════════════════════════════════════════════════════════
class SheetsWriter:
    """
    Writes all 7 output tabs to Google Sheets using gspread service account auth.

    Setup steps (document these to the user):
    1. Create a Google Cloud project and enable Google Sheets API + Google Drive API.
    2. Create a service account and download the JSON key file.
    3. Share the spreadsheet with the service account email (Editor access).
    4. Set CONFIG['GOOGLE_SERVICE_ACCOUNT_JSON'] to the JSON key file path.
    5. Set CONFIG['SPREADSHEET_ID'] to the spreadsheet ID from its URL.

    Auth: gspread.service_account() — idiomatic gspread 6.x pattern.
    HTTP 429 handling: manual 60s backoff (BackOffHTTPClient omitted due to known 403 bug).
    gspread 6.x update(): always use named arguments — values= and range_name=.
    """

    def __init__(self):
        self.gc:                Optional[gspread.Client]      = None
        self.spreadsheet:       Optional[gspread.Spreadsheet] = None
        self._ws_cache:         Dict[str, gspread.Worksheet]  = {}
        self._history_header_written: bool = False   # avoids acell() call every cycle

    def connect(self) -> gspread.Spreadsheet:
        try:
            self.gc          = gspread.service_account(filename=CONFIG['GOOGLE_SERVICE_ACCOUNT_JSON'])
            self.spreadsheet = self.gc.open_by_key(CONFIG['SPREADSHEET_ID'])
            log.info("Google Sheets connected successfully.")
            return self.spreadsheet
        except FileNotFoundError:
            raise RuntimeError(
                f"Service account JSON not found: {CONFIG['GOOGLE_SERVICE_ACCOUNT_JSON']}. "
                "Set CONFIG['GOOGLE_SERVICE_ACCOUNT_JSON'] to the correct path."
            )
        except Exception as e:
            raise RuntimeError(
                f"Google Sheets authentication failed. Verify the service account JSON key file path "
                f"in CONFIG and that the spreadsheet has been shared with the service account email. "
                f"Full error: {e}"
            )

    def _ws(self, name: str) -> gspread.Worksheet:
        if name not in self._ws_cache:
            try:
                self._ws_cache[name] = self.spreadsheet.worksheet(name)
            except WorksheetNotFound:
                self._ws_cache[name] = self.spreadsheet.add_worksheet(title=name, rows=2000, cols=30)
                log.info(f"Created worksheet: {name}")
        return self._ws_cache[name]

    def _safe_update(self, ws: gspread.Worksheet, values: list, range_name: str):
        """Update with HTTP 429 backoff — up to 3 attempts."""
        for attempt in range(3):
            try:
                ws.update(values=values, range_name=range_name)
                return
            except WorksheetNotFound as e:
                log.error(f"Worksheet no longer exists for range {range_name}: {e}. "
                          "Tab may have been deleted mid-run. Invalidating ws cache.")
                self._ws_cache = {k: v for k, v in self._ws_cache.items() if v != ws}
                return
            except APIError as e:
                if '429' in str(e):
                    log.warning(f"HTTP 429 on update (attempt {attempt+1}/3). "
                                f"Backing off {CONFIG['SHEETS_429_BACKOFF']}s...")
                    time.sleep(CONFIG['SHEETS_429_BACKOFF'])
                else:
                    log.error(f"Sheets API error on update to {range_name}: {e}")
                    return
        log.error(f"Update to {range_name} failed after 3 attempts.")

    def _fmt_cells(self, ws: gspread.Worksheet, formats: List[dict]):
        """Apply background colors. Format: [{'range': 'A1:B2', 'color': {...}}]"""
        try:
            ws.batch_format([
                {"range": f["range"], "format": {"backgroundColor": f["color"]}}
                for f in formats
            ])
        except Exception as e:
            log.warning(f"batch_format error on {ws.title}: {e}")

    # ── Tab 1: DASHBOARD ───────────────────────────────────────────────────
    def write_dashboard(self, snap: dict, signals: dict, metrics: dict,
                        cfg: dict, checklist_warns: int, checklist_fails: int,
                        expiry_str: str, expiry_type: str,
                        available_expiries: List[str], status_msg: str = ''):
        ws  = self._ws('DASHBOARD')
        ts  = now_ist().strftime('%Y-%m-%d %H:%M:%S')
        bias = signals.get('bias', 'NEUTRAL')
        score = signals.get('score', 0)
        vwap  = signals.get('vwap', float('nan'))

        header_rows = [
            ['NIFTY Intraday Dashboard', '', '', 'Last Updated:', ts],
            ['Symbol',          cfg.get('symbol', 'NIFTY'), '', 'Expiry Mode:', cfg.get('expiry_mode', '')],
            ['Selected Expiry', expiry_str, '', 'Expiry Type:', expiry_type],
            ['Spot Price',      ss(snap.get('spot')),      '', 'ATM Strike:', ss(snap.get('atm'))],
            ['Available Expiries', ', '.join(available_expiries[:8]), '', '', ''],
            ['', '', '', '', ''],
            ['── SIGNALS ──', '', '', '', ''],
            ['Final Bias',       bias,                        '', 'Score:',       ss(score)],
            ['Confidence',       f"{signals.get('confidence', 0):.1f}%",
                                                             '', 'Event Tag:',   signals.get('event_tag', '')],
            ['Price Structure',  signals.get('price_structure', ''), '', 'VWAP Bias:',  signals.get('vwap_bias', '')],
            ['Volume Confirm',   signals.get('vol_bias', ''), '', 'VWAP Level:',  ss(round(vwap, 1) if not math.isnan(vwap) else float('nan'))],
            ['Trap Warning',     ss(signals.get('trap_msg', '')), '', '', ''],
            ['Reasoning',        signals.get('reasoning', ''), '', '', ''],
            ['', '', '', '', ''],
            ['── OPTION CHAIN METRICS ──', '', '', '', ''],
            ['Support Strike',   ss(metrics.get('support_strike')),    '', 'Resistance Strike:', ss(metrics.get('resistance_strike'))],
            ['CE OI Total',      ss(metrics.get('total_ce_oi')),       '', 'PE OI Total:',       ss(metrics.get('total_pe_oi'))],
            ['CE Chg OI',        ss(metrics.get('total_ce_change_oi')), '', 'PE Chg OI:',        ss(metrics.get('total_pe_change_oi'))],
            ['CE Volume',        ss(metrics.get('total_ce_volume')),   '', 'PE Volume:',         ss(metrics.get('total_pe_volume'))],
            ['PCR (OI)',         ss(metrics.get('pcr_oi')),            '', 'PCR (Chg OI):',      ss(metrics.get('pcr_change_oi'))],
            ['Support Shift',    ss(metrics.get('support_shift')),     '', 'Resistance Shift:',  ss(metrics.get('resistance_shift'))],
            ['Vol Imbalance',    ss(metrics.get('volume_imbalance_ratio')), '', '', ''],
            ['', '', '', '', ''],
            ['── CHECKLIST STATUS ──', '', '', '', ''],
            ['Checklist Warns',  ss(checklist_warns), '', 'Checklist Fails:', ss(checklist_fails)],
            ['Status',
             'ALL PASS' if checklist_fails == 0 and checklist_warns == 0
             else ('WARNINGS ACTIVE' if checklist_fails == 0 else 'CRITICAL FAILURES'),
             '', '', ''],
            ['System Message',   status_msg, '', '', ''],
        ]

        self._safe_update(ws, header_rows, 'A1')

        # Color the bias cell
        bc = bias_color(bias)
        self._fmt_cells(ws, [
            {'range': 'B8', 'color': bc},
            {'range': 'B26',
             'color': COLOR_GREEN if checklist_fails == 0 and checklist_warns == 0
                      else (COLOR_ORANGE if checklist_fails == 0 else COLOR_DEEPRED)},
        ])

    # ── Tab 2: STARTUP_CHECKLIST ───────────────────────────────────────────
    def write_checklist(self, results: List[dict], warns: int, fails: int):
        ws = self._ws('STARTUP_CHECKLIST')
        ts = now_ist().strftime('%Y-%m-%d %H:%M:%S')

        summary_status = ('ALL PASS' if fails == 0 and warns == 0
                          else ('WARNINGS ACTIVE' if fails == 0 else 'CRITICAL FAILURES'))
        summary_color  = (COLOR_GREEN if fails == 0 and warns == 0
                          else (COLOR_ORANGE if fails == 0 else COLOR_DEEPRED))

        rows = [
            [f'Checklist Summary: {summary_status}  |  {warns} WARN  {fails} FAIL  |  {ts}'],
            ['Check ID', 'Group', 'Description', 'Status', 'Detail', 'Timestamp'],
        ]
        for r in results:
            rows.append([r['id'], r['group'], r['desc'], r['status'], r['detail'], r['ts']])

        try:
            ws.clear()
            self._safe_update(ws, rows, 'A1')
        except Exception as e:
            log.error(f"write_checklist clear/update failed: {e}. "
                      "Attempting update without clear to preserve prior data.")
            try:
                self._safe_update(ws, rows, 'A1')
            except Exception as e2:
                log.error(f"write_checklist fallback update also failed: {e2}")

        # Row-level color formatting
        fmt_list = [{'range': 'A1:F1', 'color': summary_color}]
        for i, r in enumerate(results):
            row_num = i + 3   # rows start at row 3 (1=summary, 2=header)
            fmt_list.append({'range': f'A{row_num}:F{row_num}', 'color': STATUS_COLOR[r['status']]})
        self._fmt_cells(ws, fmt_list)

    # ── Tab 3 & 4: CURRENT_SNAPSHOT / PREVIOUS_SNAPSHOT ───────────────────
    def write_snapshot(self, chain: pd.DataFrame, tab_name: str, atm: float,
                       spot: float, expiry_str: str, expiry_type: str):
        ws = self._ws(tab_name)
        ts = now_ist().strftime('%Y-%m-%d %H:%M:%S')
        header = [
            [f'{tab_name}  |  {ts}  |  Symbol: NIFTY  |  Expiry: {expiry_str} ({expiry_type})  |  Spot: {spot:.0f}  |  ATM: {atm:.0f}']
        ]
        col_header = [[
            'Strike', 'Expiry',
            'CE Token', 'CE Symbol', 'CE LTP', 'CE OI (opnInterest)', 'CE Chg OI', 'CE Volume (tradeVolume)', 'CE IV',
            'PE Token', 'PE Symbol', 'PE LTP', 'PE OI (opnInterest)', 'PE Chg OI', 'PE Volume (tradeVolume)', 'PE IV',
        ]]
        data_rows = []
        for _, row in chain.iterrows():
            data_rows.append([
                ss(row.get('strike')),     ss(row.get('expiry_str')),
                ss(row.get('ce_token')),   ss(row.get('ce_symbol')),   ss(row.get('ce_ltp')),
                ss(row.get('ce_open_interest')), ss(row.get('ce_change_oi')), ss(row.get('ce_volume')), ss(row.get('ce_iv')),
                ss(row.get('pe_token')),   ss(row.get('pe_symbol')),   ss(row.get('pe_ltp')),
                ss(row.get('pe_open_interest')), ss(row.get('pe_change_oi')), ss(row.get('pe_volume')), ss(row.get('pe_iv')),
            ])
        try:
            ws.clear()
            self._safe_update(ws, header + col_header + data_rows, 'A1')
        except Exception as e:
            log.error(f"write_snapshot ({tab_name}) clear/update failed: {e}. "
                      "Attempting update without clear to preserve prior data.")
            try:
                self._safe_update(ws, header + col_header + data_rows, 'A1')
            except Exception as e2:
                log.error(f"write_snapshot ({tab_name}) fallback update failed: {e2}")

        # Highlight ATM row
        if not chain.empty:
            chain_reset = chain.reset_index(drop=True)
            atm_rows = chain_reset[chain_reset['strike'] == atm]
            if not atm_rows.empty:
                atm_row_num = chain_reset.index.get_loc(atm_rows.index[0]) + 3
                self._fmt_cells(ws, [{'range': f'A{atm_row_num}:P{atm_row_num}', 'color': COLOR_YELLOW}])

    # ── Tab 5: COMPARISON ─────────────────────────────────────────────────
    def write_comparison(self, current: pd.DataFrame, previous: Optional[pd.DataFrame]):
        ws = self._ws('COMPARISON')
        ts = now_ist().strftime('%Y-%m-%d %H:%M:%S')
        rows = [[f'COMPARISON  |  {ts}'], [
            'Strike',
            'CE OI Prev', 'CE OI Curr', 'CE OI Delta',
            'PE OI Prev', 'PE OI Curr', 'PE OI Delta',
            'CE Vol',     'PE Vol',
            'Interpretation',
        ]]
        prev_idx = previous.set_index('strike') if previous is not None and not previous.empty else pd.DataFrame()
        fmt_list = []
        for row_i, (_, row) in enumerate(current.iterrows(), start=3):
            strike  = row.get('strike')
            try:
                ce_prev = float(prev_idx.loc[strike, 'ce_open_interest']) if strike in prev_idx.index else 0.0
            except (ValueError, TypeError):
                ce_prev = 0.0
            try:
                pe_prev = float(prev_idx.loc[strike, 'pe_open_interest']) if strike in prev_idx.index else 0.0
            except (ValueError, TypeError):
                pe_prev = 0.0
            ce_curr = safe_float(row.get('ce_open_interest'), 0)
            pe_curr = safe_float(row.get('pe_open_interest'), 0)
            ce_del  = ce_curr - ce_prev
            pe_del  = pe_curr - pe_prev
            ce_vol  = safe_float(row.get('ce_volume'), 0)
            pe_vol  = safe_float(row.get('pe_volume'), 0)

            if   pe_del > 0 and ce_del <= 0:   interp, color = 'Probable PE Writing (Bearish Support)',    COLOR_GREEN
            elif ce_del > 0 and pe_del <= 0:   interp, color = 'Probable CE Writing (Bullish Resistance)', COLOR_RED
            elif ce_del < 0 and pe_del >= 0:   interp, color = 'Probable CE Unwinding (Bullish)',          COLOR_GREEN
            elif pe_del < 0 and ce_del >= 0:   interp, color = 'Probable PE Unwinding (Bearish)',          COLOR_RED
            elif ce_del > 0 and pe_del > 0:    interp, color = 'Both OI Rising (Ambiguous)',               COLOR_YELLOW
            elif ce_del < 0 and pe_del < 0:    interp, color = 'Both OI Falling (Unwinding/Exit)',        COLOR_ORANGE
            else:                              interp, color = 'No Significant Change',                    COLOR_YELLOW

            rows.append([
                ss(strike),
                ss(int(safe_float(ce_prev, 0))), ss(int(safe_float(ce_curr, 0))), ss(int(safe_float(ce_del, 0))),
                ss(int(safe_float(pe_prev, 0))), ss(int(safe_float(pe_curr, 0))), ss(int(safe_float(pe_del, 0))),
                ss(int(safe_float(ce_vol,  0))), ss(int(safe_float(pe_vol,  0))),
                interp,
            ])
            fmt_list.append({'range': f'J{row_i}', 'color': color})

        try:
            ws.clear()
            self._safe_update(ws, rows, 'A1')
        except Exception as e:
            log.error(f"write_comparison clear/update failed: {e}. "
                      "Attempting update without clear to preserve prior data.")
            try:
                self._safe_update(ws, rows, 'A1')
            except Exception as e2:
                log.error(f"write_comparison fallback update failed: {e2}")
        if fmt_list:
            self._fmt_cells(ws, fmt_list)

    # ── Tab 6: HISTORY_LOG ────────────────────────────────────────────────
    def append_history(self, snap: dict, signals: dict, metrics: dict,
                       expiry_str: str, expiry_type: str, warns: int, fails: int):
        ws = self._ws('HISTORY_LOG')
        if not self._history_header_written:
            hdr = [['Timestamp', 'Symbol', 'Expiry', 'Expiry Type', 'Spot', 'ATM',
                    'Bias', 'Score', 'Confidence%', 'Support', 'Resistance',
                    'PCR OI', 'Event Tag', 'Checklist Warns', 'Checklist Fails']]
            self._safe_update(ws, hdr, 'A1')
            self._history_header_written = True
        row = [
            now_ist().strftime('%Y-%m-%d %H:%M:%S'),
            snap.get('symbol', 'NIFTY'),
            expiry_str, expiry_type,
            ss(snap.get('spot')),
            ss(snap.get('atm')),
            signals.get('bias', ''),
            ss(signals.get('score', '')),
            ss(signals.get('confidence', '')),
            ss(metrics.get('support_strike', '')),
            ss(metrics.get('resistance_strike', '')),
            ss(metrics.get('pcr_oi', '')),
            signals.get('event_tag', ''),
            ss(warns), ss(fails),
        ]
        try:
            _sheets_append(ws, row)
        except Exception as e:
            log.error(f"History log append failed: {e}")

    # ── Tab 7: SETTINGS_HELP ──────────────────────────────────────────────
    def write_settings_help(self):
        ws   = self._ws('SETTINGS_HELP')
        rows = [
            ['NIFTY Dashboard — Settings Help & Documentation'],
            [''],
            ['DASHBOARD INPUT CELLS'],
            ['Cell', 'Field',           'Valid Values / Notes'],
            ['B2',  'Symbol',           'NIFTY (currently only NIFTY supported)'],
            ['B3',  'Expiry Mode',      'AUTO | NEXT | MONTHLY | MANUAL'],
            ['B4',  'Manual Expiry',    'DDMMMYYYY format e.g. 28OCT2025 (only used when B3=MANUAL)'],
            ['B5',  'Interval Minutes', 'Positive integer e.g. 5. Polling interval in loop mode.'],
            ['B6',  'Strikes Above ATM','Positive integer e.g. 5. Number of strikes above ATM in focus zone.'],
            ['B7',  'Strikes Below ATM','Positive integer e.g. 5. Number of strikes below ATM in focus zone.'],
            ['B8',  'Auto Refresh',     'YES = continuous loop mode. NO = single run mode.'],
            ['B9',  'Broker Name',      'ANGELONE'],
            ['B10', 'Angel API Key',    'From smartapi.angelone.in — your API key string.'],
            ['B11', 'Angel Client Code','Your Angel One client/user ID.'],
            ['B12', 'Angel PIN (MPIN)',
             'CRITICAL: This must be your 4-digit MPIN — NOT your web login password. '
             'Your MPIN is the same 4-digit PIN you use in the Angel One mobile app. '
             'It is always exactly 4 digits. Entering your web password produces error AB7001 '
             'and the program will halt with a clear instruction to fix it.'],
            ['B13', 'Angel TOTP Secret','QR secret from smartapi.angelone.in/enable-totp. Not your MPIN or password.'],
            [''],
            ['EXPIRY MODES'],
            ['Mode',    'Description'],
            ['AUTO',    'Nearest expiry (weekly or monthly, whichever comes first).'],
            ['NEXT',    'Second nearest expiry.'],
            ['MONTHLY', 'Nearest monthly expiry. Monthly = last expiry in a calendar month (last-of-month logic).'],
            ['MANUAL',  'Exact expiry from cell B4 in DDMMMYYYY format.'],
            ['',        'NOTE: Weekly vs monthly is determined by last-of-month grouping — never by weekday. '
                        'NIFTY weekly expiry moved from Thursday to Tuesday in September 2025.'],
            [''],
            ['DATA SOURCES AND IMPORTANT NOTES'],
            ['Topic',                    'Note'],
            ['VWAP & Volume Signals',
             'Sourced exclusively from NIFTY Futures candles (NFO, FUTIDX). '
             'NIFTY index (NSE, 99926000) has no traded volume — using index volume for VWAP would produce wrong results.'],
            ['ATM & Price Structure',
             'Sourced from NIFTY Spot Index candles (NSE, token 99926000) only. '
             'Futures price is not used for ATM determination.'],
            ['IV (Implied Volatility)',
             'Fetched from Angel One Option Greeks endpoint (POST /optionGreek) using DDMMMYYYY expiry format. '
             'Set to NaN for weekly expiries (known API limitation). '
             'Set to NaN outside market hours (endpoint returns AB9019).'],
            ['Change OI',
             'Computed internally as: current_oi - previous_snapshot_oi. '
             'Not fetched from any Angel One API. Zero on first cycle.'],
            ['Strike Prices',
             'Scrip master stores strikes at 100× actual value. Divided by 100 at parse time. '
             'e.g. stored as 2440000.0 → actual 24400.'],
            ['NIFTY Option Filter',
             'Filter: name=="NIFTY" AND instrumenttype=="OPTIDX". '
             'Never use symbol=="NIFTY" — no contract has the bare string NIFTY as its full symbol.'],
            ['CE/PE Detection',
             'Determined by symbol.endswith("CE") / symbol.endswith("PE"). '
             'There is no standalone optionType field in the scrip master.'],
            ['Expiry Date Format',
             'Greeks API requires DDMMMYYYY uppercase (e.g. 28OCT2025). '
             'ISO format returns AB9022.'],
            ['Candle Date Format',
             'getCandleData requires YYYY-MM-DD HH:MM (no seconds, no T separator). '
             'Any other format returns AB13000.'],
            ['getMarketData Response',
             'Quotes are in response["data"]["fetched"] (list). '
             'OI field: opnInterest. Volume field: tradeVolume. '
             'Unfetched tokens in response["data"]["unfetched"].'],
            ['Scrip Master Refresh',
             'Downloaded fresh after 08:30 IST daily to capture new weekly contracts. '
             'Pre-08:30 cache is replaced after the cutoff.'],
            [''],
            ['CHECKLIST ITEM REFERENCE'],
            ['Check ID', 'What It Checks', 'Action on WARN', 'Action on FAIL'],
            ['SYS-01', 'System clock drift vs NTP pool.ntp.org',
             'Sync system clock; note TOTP may fail with high drift.',
             'Sync system clock immediately — TOTP authentication will fail.'],
            ['SYS-02', 'NSE market hours (09:15–15:30 Mon–Fri)',
             'Data may be stale outside hours; analysis-only mode.',
             'N/A (non-critical — no FAIL).'],
            ['SYS-03', 'Google Sheet accessible and writable',
             'N/A (critical — no WARN).',
             'Check service account JSON path, spreadsheet ID, and sharing settings.'],
            ['SYS-04', 'Output folders (logs/, cache/) writable',
             'Check disk space and folder permissions.',
             'N/A (non-critical).'],
            ['SYS-05', 'All required Python packages importable',
             'N/A (critical — no WARN).',
             'Run: pip install <missing_package>.'],
            ['AUTH-01', 'authToken and refreshToken non-empty',
             'N/A (critical).', 'Re-run login. Check credentials in B10–B13.'],
            ['AUTH-02', 'Login credential/TOTP error codes',
             'N/A (critical).', 'AB7001=MPIN error; AB1050=TOTP error. See B12 note above.'],
            ['AUTH-03', 'Midnight renewal window (23:30–23:59 IST)',
             'Renewal window active — token renewal attempted.', 'N/A.'],
            ['AUTH-04', 'refreshToken captured', 'N/A (critical).', 'Re-login.'],
            ['AUTH-05', 'feedToken available', 'Polling mode unaffected.', 'N/A (non-critical).'],
            ['INST-01', 'Scrip master freshness (two-stage: date + 08:30 cutoff)',
             'N/A (critical).', 'Network issue or Angel One server down. Retry later.'],
            ['INST-02', 'Scrip master record count (>50k expected)',
             'Some contracts may be missing.', 'Data likely corrupt — re-download.'],
            ['INST-03', 'NIFTY option contracts found',
             'N/A (critical).', 'Verify filter. Never use symbol=="NIFTY".'],
            ['INST-04', 'Selected expiry exists in master',
             'N/A (critical).', 'Change expiry mode or check B4 manual expiry.'],
            ['INST-05', 'NIFTY Futures token resolved',
             'Expiry within 3 days — plan rollover.', 'No FUTIDX found — VWAP disabled.'],
            ['INST-06', 'Focus zone strike coverage',
             '<70% coverage — some signals unreliable.', '<30% coverage — chain unusable.'],
            ['FEED-01', 'Spot candle data received',
             'N/A (critical).', 'Check NSE token 99926000. Market may be closed.'],
            ['FEED-02', 'Spot candle recency (<20 min)',
             '10–20 min lag — data may be delayed.', '>20 min lag — data likely stale.'],
            ['FEED-03', 'Futures candle received', 'VWAP disabled.', 'N/A (non-critical).'],
            ['FEED-04', 'Futures candle volume non-zero', 'VWAP signals set NEUTRAL.', 'N/A.'],
            ['FEED-05', 'Option quote data received',
             'N/A (critical).', 'Check getMarketData format: {"NFO": [list]}.'],
            ['FEED-06', 'Quote coverage ratio (>70% expected)',
             '<70% — some strikes missing LTP.', '<30% — chain unreliable.'],
            ['FEED-07', 'OI data non-zero', 'OI signals unreliable.', 'N/A.'],
            ['FEED-08', 'Option Greeks/IV available', 'IV set NaN — may be outside hours.', 'N/A.'],
            ['FEED-09', 'Weekly expiry IV warning', 'IV set NaN for weekly expiry.', 'N/A.'],
            ['SNAP-01', 'First cycle change OI', 'Do not use chg OI signals this cycle.', 'N/A.'],
            ['SNAP-02', 'Snapshot age vs interval', 'Gap > 2× interval — possible missed cycle.', 'N/A.'],
            ['SNAP-03', 'ATM strike shift per cycle', 'ATM jumped >150 pts — verify spot data.', 'N/A.'],
            ['SNAP-04', 'Score within ±12', 'Score anomaly — check data quality.', 'N/A.'],
            ['SNAP-05', 'Strike alignment with prev snapshot', '<50% overlap — ATM shifted significantly.', 'N/A.'],
            [''],
            ['RATE LIMITS'],
            ['API',                'Limit',         'Dashboard Usage'],
            ['getMarketData',      '10/sec, 500/min', '1 call per cycle — well within limit.'],
            ['getCandleData',      '3/sec, 180/min',
             '2 calls per cycle (spot + futures). A 1s inter-call sleep is applied between '
             'the two calls to prevent AB1019 (Too Many Requests). On AB1019, the script '
             'retries up to 3 times with exponential back-off (2s, 4s, 8s) and falls back '
             'to last-known-good candle data if all retries fail.'],
            ['Option Greeks',      'Unspecified',     '1 call per cycle.'],
            [''],
            ['SEBI COMPLIANCE NOTICE (effective April 1, 2026)'],
            ['Angel One requires a registered static IP address for all order placement and modification APIs. '
             'This dashboard is a read-only analytics tool and places no orders — the static IP requirement '
             'does not affect its operation. For APIs other than Orders and GTT, using a static IP is not mandatory. '
             'However, if you also use your SmartAPI key for order execution from a separate application, '
             'you must register a static IP address with Angel One via the SmartAPI developer portal '
             'before April 1, 2026.'],
            [''],
            ['ANALYTICAL LIMITATION NOTICE'],
            ['This system does NOT detect actual institutional positions. All signals are rule-based '
             'heuristics inferred from observable market data (OI, volume, price structure, VWAP). '
             'Inferences about probable participant behavior are probabilistic estimates only, not '
             'confirmed facts. Do not treat any output as financial advice.'],
        ]
        try:
            ws.clear()
            self._safe_update(ws, rows, 'A1')
        except Exception as e:
            log.error(f"write_settings_help clear/update failed: {e}. "
                      "Attempting update without clear.")
            try:
                self._safe_update(ws, rows, 'A1')
            except Exception as e2:
                log.error(f"write_settings_help fallback update failed: {e2}")


# ═════════════════════════════════════════════════════════════════════════════
# CLASS 10 — NiftyDashboardApp
# ═════════════════════════════════════════════════════════════════════════════
class NiftyDashboardApp:
    """
    Orchestrates all classes.
    Supports single-run (B8=NO) and continuous loop (B8=YES) modes.
    Handles Ctrl+C gracefully.
    """

    def __init__(self):
        self.writer        = SheetsWriter()
        self.spreadsheet:  Optional[gspread.Spreadsheet] = None
        self.cfg:          dict = {}
        self.sac:          Optional[SmartApiClient] = None
        self.loader:       Optional[InstrumentMasterLoader] = None
        self.candle:       Optional[CandleFetcher] = None
        self.builder:      Optional[OptionChainBuilder] = None
        self.metrics_calc  = MetricsCalculator()
        self.signal_engine = SignalEngine()
        self.prev_chain:   Optional[pd.DataFrame] = None
        self.prev_atm:     Optional[float] = None
        self.prev_cycle_ts: Optional[datetime] = None
        self.last_spot:    float = 0.0
        self.cycle_num:    int   = 0

    def _write_status(self, msg: str):
        try:
            ws = self.spreadsheet.worksheet('DASHBOARD')
            ws.update(values=[[msg]], range_name='B27')
        except Exception:
            pass
        log.error(msg)

    def _init(self):
        """Connect to Sheets, load config, login, load instrument master."""
        self.spreadsheet = self.writer.connect()
        reader           = ConfigReader(self.spreadsheet)
        self.cfg         = reader.load()

        self.sac = SmartApiClient(
            self.cfg['api_key'], self.cfg['client_code'],
            self.cfg['mpin'],    self.cfg['totp_secret']
        )
        self.sac.login()

        self.loader = InstrumentMasterLoader()
        self.loader.load()

        self.candle  = CandleFetcher(self.sac.get_api(), self.loader.nifty_futures_token)
        self.builder = OptionChainBuilder(self.sac.get_api(), self.loader)

        # Write static SETTINGS_HELP once at startup
        try:
            self.writer.write_settings_help()
        except Exception as e:
            log.warning(f"SETTINGS_HELP write failed: {e}")

    def _run_cycle(self) -> bool:
        """Execute one full snapshot cycle. Returns False if a FAIL halts execution."""
        self.cycle_num += 1
        ist = now_ist()
        log.info(f"═══ Cycle {self.cycle_num} at {ist.strftime('%H:%M:%S')} IST ═══")

        # Expiry selection
        try:
            expiry_dt, expiry_str, is_monthly = self.loader.select_expiry(
                self.cfg['expiry_mode'], self.cfg.get('manual_expiry', ''))
            is_weekly = not is_monthly   # build() and StartupChecker use is_weekly convention
        except RuntimeError as e:
            self._write_status(str(e))
            return False

        # Fetch candles
        spot_df    = self.candle.fetch_spot_candles()
        futures_df = self.candle.fetch_futures_candles()

        # Determine spot price and ATM
        if spot_df is not None and not spot_df.empty:
            self.last_spot = float(spot_df['close'].iloc[-1])
        elif self.last_spot == 0:
            log.warning("No spot price available. Cannot determine ATM. Skipping cycle.")
            return True
        atm = self.builder.determine_atm(self.last_spot)

        # Build option chain
        chain = None
        try:
            chain = self.builder.build(
                expiry_dt, expiry_str, is_weekly,
                atm, self.cfg['strikes_above'], self.cfg['strikes_below'],
                self.prev_chain
            )
        except RuntimeError as e:
            log.error(f"Chain build failed: {e}")
            chain = pd.DataFrame()

        # Compute metrics and signals
        metrics = self.metrics_calc.compute(chain, self.prev_chain) if chain is not None and not chain.empty else {}
        self.metrics_calc.add_spot_distances(metrics, self.last_spot)
        signals = self.signal_engine.run(metrics, spot_df, futures_df, 0)

        # Run startup checklist
        checker = StartupChecker(
            smart_api_client=self.sac, loader=self.loader,
            spreadsheet=self.spreadsheet, cfg=self.cfg,
            expiry_dt=expiry_dt, expiry_str=expiry_str, is_weekly=is_weekly,
            spot_df=spot_df, futures_df=futures_df,
            chain=chain, prev_chain=self.prev_chain,
            score=signals.get('score'), prev_atm=self.prev_atm,
            current_atm=atm, prev_cycle_ts=self.prev_cycle_ts,
            cycle_num=self.cycle_num,
        )
        warns, fails, results = checker.run_all()

        # Recompute confidence with actual warn count
        signals['confidence'] = self.signal_engine.compute_confidence(
            signals.get('score', 0), signals.get('trap', False), warns)

        # Write checklist to Sheets
        try:
            self.writer.write_checklist(results, warns, fails)
        except Exception as e:
            log.error(f"Checklist write failed: {e}")

        # Halt on critical failure
        if fails > 0:
            fail_msgs = [r['detail'] for r in results if r['status'] == 'FAIL']
            msg = f"CRITICAL FAILURES ({fails}): " + " | ".join(fail_msgs[:3])
            self._write_status(msg)
            log.error(f"Halting due to {fails} FAIL(s) in checklist.")
            return False

        # Available expiries for dashboard
        available = [e.strftime('%d%b%Y').upper() for e in self.loader.get_available_expiries()[:8]]
        expiry_type = 'MONTHLY' if is_monthly else 'WEEKLY'
        snap = {
            'symbol': self.cfg.get('symbol', 'NIFTY'),
            'spot':   round(self.last_spot, 2),
            'atm':    atm,
        }

        # Write all output tabs
        try:
            self.writer.write_dashboard(
                snap, signals, metrics, self.cfg, warns, fails,
                expiry_str, expiry_type, available,
                status_msg=f'Cycle {self.cycle_num} OK | {warns}W {fails}F'
            )
            if chain is not None and not chain.empty:
                if self.prev_chain is not None and not self.prev_chain.empty:
                    self.writer.write_snapshot(self.prev_chain, 'PREVIOUS_SNAPSHOT',
                                               self.prev_atm or atm, self.last_spot,
                                               expiry_str, expiry_type)
                self.writer.write_snapshot(chain, 'CURRENT_SNAPSHOT', atm,
                                           self.last_spot, expiry_str, expiry_type)
                self.writer.write_comparison(chain, self.prev_chain)
            self.writer.append_history(snap, signals, metrics, expiry_str, expiry_type, warns, fails)
        except APIError as e:
            if '429' in str(e):
                log.warning(f"HTTP 429 writing outputs. Backing off {CONFIG['SHEETS_429_BACKOFF']}s.")
                time.sleep(CONFIG['SHEETS_429_BACKOFF'])
            else:
                log.error(f"Sheets API error writing outputs: {e}")
        except Exception as e:
            log.error(f"Output write failed: {e}", exc_info=True)

        # Update state for next cycle
        self.prev_chain    = chain.copy() if chain is not None and not chain.empty else self.prev_chain
        self.prev_atm      = atm
        self.prev_cycle_ts = ist

        log.info(f"Cycle {self.cycle_num} complete. Bias={signals.get('bias')} "
                 f"Score={signals.get('score')} Confidence={signals.get('confidence')}% "
                 f"Warns={warns}")
        return True

    def run(self):
        try:
            self._init()
        except Exception as e:
            log.critical(f"Initialization failed: {e}", exc_info=True)
            try:
                self._write_status(f"INIT FAILED: {e}")
            except Exception:
                pass
            return

        loop_mode = self.cfg.get('auto_refresh', 'NO') == 'YES'
        interval  = max(1, self.cfg.get('interval_minutes', 5)) * 60

        if not loop_mode:
            log.info("Single-run mode (B8=NO).")
            self._run_cycle()
            log.info("Single-run complete.")
            return

        log.info(f"Continuous loop mode (B8=YES). Interval={self.cfg['interval_minutes']}m. Ctrl+C to stop.")
        try:
            while True:
                should_continue = self._run_cycle()
                if not should_continue:
                    log.error("Loop halted due to critical checklist failure.")
                    break
                log.info(f"Sleeping {self.cfg['interval_minutes']}m until next cycle...")
                time.sleep(interval)
        except KeyboardInterrupt:
            log.info("Ctrl+C received. Dashboard stopped gracefully.")


# ─────────────────────────────────────────────────────────────────────────────
# ENTRY POINT
# ─────────────────────────────────────────────────────────────────────────────
if __name__ == '__main__':
    log.info("NIFTY Dashboard starting...")
    log.info("MPIN REMINDER: Cell B12 must be your 4-digit Angel One MPIN — NOT your web login password.")
    app = NiftyDashboardApp()
    app.run()
