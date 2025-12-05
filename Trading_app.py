# Trading_app.py
# ----------------------------------------------------
# Trading Frictions (Mainnet market data via ccxt REST) + Testnet paper orders
# ----------------------------------------------------
import time, random, math, traceback
from typing import Dict, Optional, List, Tuple

import tkinter as tk
from tkinter import ttk, messagebox

from trading_utils import *  # expects API_KEY, API_SECRET (may be empty)

import ccxt
import numpy as np

# ---------- Palette ----------
BLOOM_BLUE   = "#2a6df4"
BLOOM_GREEN  = "#2bb673"
BLOOM_GREEN_H= "#31c27f"
BLOOM_RED    = "#f05454"
BLOOM_RED_H  = "#ff6a6a"
BLOOM_AMBER  = "#f4a62a"
FG_MAIN      = "#e9edf3"
FG_MUTED     = "#aeb7c7"
BG_DARK      = "#0b0f17"
BG_PANEL     = "#161b26"
SEP          = "#444a60"

# ---------- Universe ----------
BASES_TOP10  = ["BTC","ETH","BNB","SOL","XRP","ADA","DOGE","TRX","LTC","BCH"]
ALL_BASES    = BASES_TOP10
QUOTE        = "USDT"
DEFAULT_SYMBOLS = [f"{b}/{QUOTE}" for b in ALL_BASES]

# ---------- Formatting ----------
def _trim(x, fmt):
    s = fmt.format(x)
    if "." in s:
        s = s.rstrip("0").rstrip(".")
    return s

def fmt_qty(x):
    if x is None or not np.isfinite(x): return "—"
    # compact (fewer useless zeros)
    return _trim(x, "{:,.6f}")
# ADD — more precise % and a basis-points helper (1% = 100 bp)
def fmt_pct2_signed(x):
    if x is None or not np.isfinite(x): return "—"
    return _trim(x, "{:+.2f}%")

def fmt_bp_from_pct(x):
    if x is None or not np.isfinite(x): return "—"
    val = _trim(x * 100.0, "{:+.2f}")   # 2 decimal bp
    return f"{val} bp"

def fmt_pct_or_bp(pct_value):
    if pct_value is None or not np.isfinite(pct_value):
        return "—"
    return fmt_pct2_signed(pct_value) if abs(pct_value) >= 1.0 else fmt_bp_from_pct(pct_value)


def fmt_usd(x):
    if x is None or not np.isfinite(x): return "—"
    return _trim(x, "{:,.2f}")

def fmt_px(x):
    if x is None or not np.isfinite(x): return "—"
    return _trim(x, "{:,.2f}")

def fmt_pct_signed(x):
    if x is None or not np.isfinite(x): return "—"
    return _trim(x, "{:+.4f}%")

FEE_BPS = 0.00075  # 7.5 bps fixed
LIQ_FACTOR_K = 1000

# ---------- App ----------
class FrictionApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Trading Frictions — Mainnet data (ccxt REST) + Testnet paper")
        self.configure(bg=BG_DARK)
        self.minsize(1280, 800)

        # Session state
        self.session_start_value_usdt: Optional[float] = None
        self.session_friction_usdt: float = 0.0
        self.session_open_mid: Dict[str, float] = {}
        self._last_total_usdt: float = 0.0
        self._ui_last_mid: Dict[str, Tuple[float, int]] = {}

        # Clients
        self.ex_pub: Optional[ccxt.binance] = None   # MAINNET, no keys (market data)
        self.ex_priv: Optional[ccxt.binance] = None  # TESTNET, with keys (balances & orders)

        # REST cache for quick mid polling
        self._rest_cache: Dict[str, Dict[str, float]] = {}  # sym -> {ts, bid, ask, mid}
        self.symbols: List[str] = DEFAULT_SYMBOLS[:]

        self._style()
        self._build_layout()

        if not self._connect_clients():
            self._fatal_disable()
            return

        # Initial refresh
        self.after(50, self.refresh_balance)

        # Heartbeats: price chip (poll ticker) and 10s PnL refresh
        self.after(400, self._tick_selected_price)   # ~2.5 Hz (REST)
        self.after(10_000, self._heartbeat_10s)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

    def _pad_levels_to_quote(self, levels: List[Tuple[float, float]], side: str, quote_target: float) -> List[Tuple[float, float]]:
        """
        Extend levels until the target quote notional is covered by *sampling*
        both price gaps and volumes from the empirical distribution of the side.
        """
        if not levels or quote_target <= 0:
            return levels

        # Current covered quote
        def _covered(ls):
            c = 0.0
            for p, q in ls:
                if p and q and q > 0:
                    c += p * q
            return c

        covered = _covered(levels)
        if covered >= quote_target:
            return levels

        # Empirical gap and volume stats
        prices = np.array([float(p) for p, _ in levels if np.isfinite(p)])
        vols = np.array([float(v) for _, v in levels if np.isfinite(v) and v > 0])

        if len(prices) >= 2:
            gaps = np.abs(np.diff(prices))
            gap_mu = float(np.mean(gaps)) if np.isfinite(np.mean(gaps)) else max(prices[-1] * 1e-4, 1e-8)
            gap_sd = float(np.std(gaps)) if np.isfinite(np.std(gaps)) else gap_mu * 0.5
        else:
            gap_mu = max(float(prices[-1]) * 1e-4, 1e-8) if len(prices) else 1e-4
            gap_sd = gap_mu * 0.5

        if len(vols) >= 1:
            vol_mu = float(np.mean(vols))
            vol_sd = float(np.std(vols)) if len(vols) > 1 else max(vol_mu * 0.5, 1e-12)
        else:
            vol_mu = 1e-6
            vol_sd = vol_mu * 0.5

        last_px = float(levels[-1][0]) if levels else 0.0

        rng = np.random.default_rng()

        # Keep adding sampled synthetic levels until covered
        while covered < quote_target and len(levels) < 5000:
            # Sample a strictly positive gap
            gap = abs(float(rng.normal(gap_mu, gap_sd)))
            gap = max(gap, max(abs(last_px) * 1e-6, 1e-10))

            # Move price in the correct direction
            px = last_px + gap if side == "buy" else max(last_px - gap, 1e-12)

            # Sample a volume; clip to be non-negative and small epsilon minimum
            q = float(rng.normal(vol_mu, vol_sd))
            if not np.isfinite(q) or q <= 0:
                q = max(vol_mu * 0.3, 1e-9)

            levels.append((px, q))
            covered += px * q
            last_px = px

        return levels

    # ---------- Styles ----------
    def _style(self):
        s = ttk.Style(self); s.theme_use("clam")
        s.configure(".", background=BG_DARK, foreground=FG_MAIN)
        s.configure("Bloom.TSeparator", background=SEP)

        s.configure("StatName.TLabel", background=BG_DARK, foreground=FG_MUTED, font=("Menlo", 12, "bold"))
        s.configure("SectionTitle.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 14, "bold"))
        s.configure("StatValue.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 13, "bold"))
        s.configure("StatValueGreen.TLabel", background=BG_DARK, foreground=BLOOM_GREEN_H, font=("Menlo", 13, "bold"))
        s.configure("StatValueRed.TLabel",   background=BG_DARK, foreground=BLOOM_RED_H,   font=("Menlo", 13, "bold"))
        s.configure("PNL.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 15, "bold"))

        s.configure("LivePrice.TLabel", background=BG_PANEL, foreground=BLOOM_AMBER,
                    font=("Menlo", 16, "bold"), padding=(10,6))
        s.configure("Bloom.Green.TButton", padding=(12,8), background=BLOOM_GREEN,
                    foreground=BG_DARK, font=("Helvetica", 12, "bold"), borderwidth=0)
        s.map("Bloom.Green.TButton", background=[("active", BLOOM_GREEN_H)])
        s.configure("Bloom.Red.TButton", padding=(12,8), background=BLOOM_RED,
                    foreground="#ffffff", font=("Helvetica", 12, "bold"), borderwidth=0)
        s.map("Bloom.Red.TButton", background=[("active", BLOOM_RED_H)])
        s.configure("Bloom.Amber.TButton", padding=(10,6), background=BLOOM_AMBER,
                    foreground=BG_DARK, font=("Helvetica", 11, "bold"), borderwidth=0)

        s.configure("Dark.TCombobox", fieldbackground=BG_PANEL, background=BG_PANEL, foreground=FG_MAIN)
        s.map("Dark.TCombobox",
              fieldbackground=[("readonly", BG_PANEL)],
              background=[("readonly", BG_PANEL)],
              foreground=[("readonly", FG_MAIN)])

        s.configure("Dark.TEntry", fieldbackground=BG_PANEL, foreground=FG_MAIN, insertcolor=FG_MAIN, padding=4)
        s.configure("Balances.Treeview", background=BG_PANEL, fieldbackground=BG_PANEL,
                    foreground=FG_MAIN, rowheight=22, borderwidth=0)
        s.configure("Balances.Treeview.Heading", background=BG_DARK, foreground=FG_MAIN,
                    relief="flat", font=("Menlo", 11, "bold"))

    # ---------- Layout ----------
    def _build_layout(self):
        top = ttk.Frame(self, padding=(10,10))
        top.pack(side="top", fill="both", expand=True)
        top.grid_columnconfigure(0, weight=7)
        top.grid_columnconfigure(1, weight=5)
        top.grid_rowconfigure(0, weight=1)

        self.left  = ttk.Frame(top, padding=(6,6))
        self.right = ttk.Frame(top, padding=(6,6))
        self.left.grid(row=0, column=0, sticky="nsew")
        ttk.Separator(top, orient="vertical", style="Bloom.TSeparator").grid(row=0, column=1, sticky="ns", padx=6)
        self.right.grid(row=0, column=2, sticky="nsew")

        # LEFT — Balances
        ttk.Label(self.left, text="Balances (USDT-valued)", style="StatName.TLabel").pack(anchor="w", pady=(0,6))

        cols = ("asset", "qty", "qty_usdt")
        self.tree = ttk.Treeview(self.left, columns=cols, show="headings",
                                 style="Balances.Treeview", selectmode="none")
        self.tree.heading("asset", text="ASSET")
        self.tree.heading("qty", text="QTY")
        self.tree.heading("qty_usdt", text="QTY IN USDT (±% vs session OPEN)")
        self.tree.column("asset", width=100, anchor="center")
        self.tree.column("qty", width=160, anchor="center")
        self.tree.column("qty_usdt", width=300, anchor="center")
        self.tree.pack(fill="both", expand=True)

        self.total_lbl = ttk.Label(self.left, text="Total: — USDT", style="StatValue.TLabel")
        self.total_lbl.pack(anchor="w", pady=(6,0))
        self.pnl_lbl = ttk.Label(self.left, text="PnL: — (—%)  |  market: —  |  friction: —", style="PNL.TLabel")
        self.pnl_lbl.pack(anchor="w", pady=(2,6))
        self.reset_btn = ttk.Button(self.left, text="Reset PnL Baseline", style="Bloom.Amber.TButton",
                                    command=self._reset_pnl_baseline)
        self.reset_btn.pack(anchor="w")

        # RIGHT — Last Execution — Stats
        ttk.Label(self.right, text="Last Execution — Stats", style="SectionTitle.TLabel") \
            .pack(anchor="w", pady=(0, 6))

        spec = [
            ("t_first", "Last exec (local time)"),
            ("way", "Way"),
            ("exec_base", "Executed qty (BASE)"),
            ("exec_quote", "Executed qty (QUOTE)"),
            ("slip_ms", "Slippage (ms: click → first fill)"),
            ("arrival", "Arrival price (mid)"),
            ("first_px", "First exec price  |  vs Arrival"),
            ("last_px", "Last exec price   |  vs First"),
            ("vwap", "VWAP              |  vs First"),
            ("mkt_total", "Total market friction"),
            ("fees", "  Fees"),
            ("impact", "  Impact cost"),
            ("spread", "  Spread"),
            ("slippage", "  Slippage cost"),
        ]

        self.stats: Dict[str, ttk.Label] = {}
        for key, label in spec:
            row = ttk.Frame(self.right, padding=(1,1)); row.pack(anchor="w", pady=1, fill="x")
            ttk.Label(row, text=label, style="StatName.TLabel").pack(side="left")
            val = ttk.Label(row, text="—", style="StatValue.TLabel"); val.pack(side="right")
            self.stats[key] = val

        # BOTTOM — Inputs & Buttons + price chip
        bottom = ttk.Frame(self, padding=(8,8)); bottom.pack(side="bottom", fill="x")
        ttk.Label(bottom, text="Base:", style="StatName.TLabel").grid(row=0, column=0, sticky="e", padx=(0,6))
        self.base_var = tk.StringVar(value="BNB")
        self.base_cb = ttk.Combobox(bottom, values=ALL_BASES,
                                    textvariable=self.base_var, width=10, state="readonly",
                                    style="Dark.TCombobox")
        self.base_cb.grid(row=0, column=1, sticky="w")
        self.base_cb.bind("<<ComboboxSelected>>", lambda _e: self._tick_selected_price())

        ttk.Label(bottom, text="Quote:", style="StatName.TLabel").grid(row=0, column=2, sticky="e", padx=(12,6))
        ttk.Label(bottom, text=QUOTE, style="StatValue.TLabel").grid(row=0, column=3, sticky="w", padx=(0,12))

        ttk.Label(bottom, text="Quote Qty (K USDT):", style="StatName.TLabel").grid(row=0, column=4, sticky="e", padx=(0, 6))
        self.quote_qty_var = tk.IntVar(value=1000)  # integer K (1 K USDT = 1000 USDT)
        self.quote_entry = ttk.Entry(bottom, textvariable=self.quote_qty_var, width=12, style="Dark.TEntry")
        self.quote_entry.grid(row=0, column=5, sticky="w", padx=(0, 18))

        self.buy_btn  = ttk.Button(bottom, text="Buy",  style="Bloom.Green.TButton", command=lambda: self._place("buy"))
        self.sell_btn = ttk.Button(bottom, text="Sell", style="Bloom.Red.TButton",  command=lambda: self._place("sell"))
        self.buy_btn.grid(row=0, column=6, padx=(0,8))
        self.sell_btn.grid(row=0, column=7, padx=(0,18))

        self.price_chip = ttk.Label(bottom, text="—", style="LivePrice.TLabel")
        self.price_chip.grid(row=0, column=8, sticky="w")

    # ---------- Clients ----------
    def _connect_clients(self) -> bool:
        try:
            # MAINNET (public, no keys) — market data
            self.ex_pub = ccxt.binance({
                "enableRateLimit": True,
                "options": {"defaultType": "spot"},
            })
            self.ex_pub.load_markets()
            self.symbols = [s for s in DEFAULT_SYMBOLS if s in self.ex_pub.markets]
            if not self.symbols:
                raise ccxt.ExchangeError("None of the requested symbols exist on Binance mainnet.")

            # TESTNET (private, optional) — balances & orders
            self.ex_priv = None
            try:
                if API_KEY and API_SECRET:
                    ex = ccxt.binance({
                        "apiKey": API_KEY,
                        "secret": API_SECRET,
                        "enableRateLimit": True,
                        "options": {"defaultType": "spot"},
                    })
                    ex.set_sandbox_mode(True)   # paper trading
                    ex.load_markets()
                    self.ex_priv = ex
            except Exception as e_priv:
                print("Testnet keys invalid or missing:", e_priv)
                self.ex_priv = None

            # Enable/disable trading buttons depending on private client
            for w in (self.buy_btn, self.sell_btn):
                try: w.configure(state=("normal" if self.ex_priv else "disabled"))
                except Exception: pass

            return True
        except Exception as e:
            messagebox.showerror("Startup", f"{type(e).__name__}: {e}")
            return False

    def _fatal_disable(self):
        for w in (self.base_cb, self.quote_entry, self.buy_btn, self.sell_btn):
            try: w.configure(state="disabled")
            except Exception: pass

    # ---------- REST helpers (public client) ----------
    def _rest_ticker_cached(self, sym: str) -> Tuple[Optional[float], Optional[float], Optional[float]]:
        """
        Light cache (~300 ms) to avoid hammering REST.
        """
        now = int(time.time() * 1000)
        rec = self._rest_cache.get(sym)
        if rec and (now - rec.get("ts", 0) < 300):
            b = rec.get("bid"); a = rec.get("ask"); m = rec.get("mid")
            return (b if np.isfinite(b) else None,
                    a if np.isfinite(a) else None,
                    m if np.isfinite(m) else None)
        try:
            t = self.ex_pub.fetch_ticker(sym)
            bid = float(t.get("bid") or np.nan)
            ask = float(t.get("ask") or np.nan)
            mid = (bid + ask) / 2.0 if np.isfinite(bid) and np.isfinite(ask) and bid>0 and ask>0 else np.nan
            self._rest_cache[sym] = {"ts": now, "bid": bid, "ask": ask, "mid": mid}
            return (bid if np.isfinite(bid) else None,
                    ask if np.isfinite(ask) else None,
                    mid if np.isfinite(mid) else None)
        except Exception:
            return (None, None, None)

    def _mid_now(self, sym: str) -> Optional[float]:
        _, _, mid = self._rest_ticker_cached(sym)
        return float(mid) if (mid and np.isfinite(mid) and mid > 0) else None

    # ---------- Heartbeats ----------
    def _tick_selected_price(self):
        try:
            sym = f"{self.base_var.get()}/{QUOTE}"
            m = self._mid_now(sym)  # REST
            self.price_chip.configure(text=f"{sym}  {fmt_px(m) if m else '—'}")
            if m and np.isfinite(m) and m > 0:
                self._ui_last_mid[sym] = (float(m), int(time.time() * 1000))
        except Exception:
            traceback.print_exc()
        self.after(400, self._tick_selected_price)

    def _heartbeat_10s(self):
        try:
            self.refresh_balance()
        except Exception:
            traceback.print_exc()
        self.after(10_000, self._heartbeat_10s)

    # ---------- Balance & PnL (private client if available) ----------
    def refresh_balance(self):
        if not self.ex_priv:
            # No keys: show zeros but keep totals consistent
            for row in self.tree.get_children():
                self.tree.delete(row)
            self.tree.insert("", "end", values=("USDT", "0", "0"))
            for b in ALL_BASES:
                self.tree.insert("", "end", values=(b, "0", "0"))
            total_usdt = 0.0
        else:
            bal = self.ex_priv.fetch_balance()

            # Clear
            for row in self.tree.get_children():
                self.tree.delete(row)

            total_usdt = 0.0

            # USDT cash
            usdt_qty = float(bal.get("total", {}).get("USDT") or 0.0) * LIQ_FACTOR_K
            self.tree.insert("", "end", values=("USDT", fmt_qty(usdt_qty), fmt_usd(usdt_qty)))
            total_usdt += usdt_qty

            # Other assets
            for b in ALL_BASES:
                qty = float(bal.get("total", {}).get(b) or 0.0) * LIQ_FACTOR_K
                if qty == 0:
                    # still show a compact zero row so the table is dense
                    self.tree.insert("", "end", values=(b, fmt_qty(0.0), fmt_usd(0.0)))
                    continue
                sym = f"{b}/{QUOTE}"
                mid = self._mid_now(sym)
                if mid is None or not np.isfinite(mid):
                    usd_val, pct_str = 0.0, "—"
                else:
                    usd_val = qty * mid
                    if sym not in self.session_open_mid:
                        self.session_open_mid[sym] = float(mid)
                    open_mid = self.session_open_mid.get(sym)
                    pct_str = fmt_pct_signed((mid/open_mid - 1.0)*100.0) if (open_mid and open_mid>0) else "—"

                self.tree.insert("", "end", values=(b, fmt_qty(qty), f"{fmt_usd(usd_val)} ({pct_str})"))
                total_usdt += usd_val

        # Store last total for instant reset
        self._last_total_usdt = total_usdt

        if self.session_start_value_usdt is None:
            self.session_start_value_usdt = float(total_usdt)

        self.total_lbl.configure(text=f"Total: {fmt_usd(total_usdt)} USDT")

        session_pnl = total_usdt - (self.session_start_value_usdt or 0.0)
        session_pnl_pct = (
            (session_pnl / self.session_start_value_usdt * 100.0)
            if (self.session_start_value_usdt and self.session_start_value_usdt > 0) else np.nan
        )

        market_part = session_pnl - float(self.session_friction_usdt or 0.0)
        style = "StatValueGreen.TLabel" if session_pnl > 0 else ("StatValueRed.TLabel" if session_pnl < 0 else "PNL.TLabel")

        def _pct(x, denom):
            return (x / denom * 100.0) if (np.isfinite(x) and np.isfinite(denom) and denom > 0) else np.nan

        mkt_pct = _pct(market_part, (self.session_start_value_usdt or np.nan))
        fric_pct = _pct(self.session_friction_usdt, (self.session_start_value_usdt or np.nan))

        self.pnl_lbl.configure(
            text=(f"PnL: {fmt_usd(session_pnl)} USDT ({fmt_bp_from_pct(session_pnl_pct)})"
                  f"  |  market: {fmt_usd(market_part)} USDT ({fmt_bp_from_pct(mkt_pct)})"
                  f"  |  friction: {fmt_usd(self.session_friction_usdt)} USDT ({fmt_bp_from_pct(fric_pct)})"),
            style=style
        )

    def _reset_pnl_baseline(self):
        """Instantly reset PnL, market, and friction to 0 using last totals."""
        self.session_start_value_usdt = float(self._last_total_usdt or 0.0)
        self.session_friction_usdt = 0.0
        self._last_total_usdt = self.session_start_value_usdt
        self.pnl_lbl.configure(text="PnL: 0.00 USDT (0%)  |  market: 0.00 USDT 0%  |  friction: 0.00 USDT 0%")

    # ---------- OB simulation ----------
    @staticmethod
    def _simulate_by_quote(levels: List[Tuple[float, float]], quote_target: float) -> Tuple[float, float, float]:
        """
        Walk levels (price, size) and fill until quote_target is reached.
        Returns (filled_base, vwap, last_px). first_px is levels[0][0] if any.
        """
        remaining_quote = quote_target
        filled_base = 0.0
        cost_quote = 0.0
        last_px = np.nan
        for px, qty in levels:
            if px is None or qty is None or qty <= 0: continue
            take_base = min(qty, remaining_quote / px)
            if take_base <= 0: break
            filled_base += take_base
            cost_quote += take_base * px
            last_px = px
            remaining_quote -= take_base * px
            if remaining_quote <= 1e-12:
                break
        vwap = (cost_quote / filled_base) if filled_base > 0 else np.nan
        return filled_base, vwap, last_px

    # ---------- Orders (private client) ----------
    def _quote_qty_param(self, sym: str, quote_cost: float) -> str:
        try:
            return self.ex_priv.cost_to_precision(sym, quote_cost)
        except Exception:
            try:
                return self.ex_priv.number_to_string(float(quote_cost))
            except Exception:
                return str(quote_cost)

    def _show_wait(self, text: str):
        win = tk.Toplevel(self)
        win.title("Please wait")
        win.configure(bg=BG_PANEL)
        win.transient(self)
        win.grab_set()
        ttk.Label(win, text=text, style="StatName.TLabel").pack(padx=18, pady=14)
        win.update_idletasks()
        try:
            x = self.winfo_rootx() + (self.winfo_width() - win.winfo_reqwidth()) // 2
            y = self.winfo_rooty() + (self.winfo_height() - win.winfo_reqheight()) // 2
            win.geometry(f"+{max(x, 0)}+{max(y, 0)}")
        except Exception:
            pass
        return win

    def _close_wait(self, win):
        try:
            if win and win.winfo_exists():
                win.grab_release()
                win.destroy()
        except Exception:
            pass

    def _place(self, side: str):
        if not self.ex_priv:
            messagebox.showwarning("Trading disabled", "No valid testnet API keys. Market data works without keys.")
            return

        base = self.base_var.get()
        sym = f"{base}/{QUOTE}"

        # Start timer AT CLICK (includes UI wait + sleep + snapshot)
        t_click = int(time.time() * 1000)

        # Parse input
        try:
            q_quote_real = float(self.quote_qty_var.get())  # real USDT notional for Binance
            q_quote_stat = q_quote_real * LIQ_FACTOR_K  # internal ×1000 accounting
        except Exception:
            messagebox.showwarning("Input", "Quote quantity must be numeric.")
            return
        if not np.isfinite(q_quote_real) or q_quote_real <= 0:
            messagebox.showwarning("Input", "Quote quantity must be positive.")
            return

        # -------- Arrival = last price the USER SAW on the price chip ----------
        rec = getattr(self, "_ui_last_mid", {}).get(sym)
        if not rec:
            messagebox.showwarning("Price",
                                   "No recent displayed price yet. Wait until the price chip shows a number, then click.")
            return
        arrival, ts_seen = rec
        if not (np.isfinite(arrival) and arrival > 0):
            messagebox.showwarning("Price", "Displayed price is invalid. Please wait for the next update.")
            return

        # Optional staleness guard (2 seconds)
        now_ms = int(time.time() * 1000)
        STALE_MS = 2000

        # Wait popup
        wait = self._show_wait("Submitting order…")
        try:
            # Random latency BEFORE OB snapshot (included in slippage measurement)
            d = max(0.0, min(1.0, random.gauss(0.5, 0.2)))
            time.sleep(d)

            # OB snapshot (public mainnet)
            ob = self.ex_pub.fetch_order_book(sym, limit=50)
            top_bid = ob["bids"][0][0] if ob.get("bids") else np.nan
            top_ask = ob["asks"][0][0] if ob.get("asks") else np.nan

            if side == "buy":
                levels = [(float(px), float(sz)) for px, sz in ob.get("asks", [])]  # keep OB as-is
            else:
                levels = [(float(px), float(sz)) for px, sz in ob.get("bids", [])]

            # simulate on inflated notional (qty * 1000 in USDT)
            quote_target = q_quote_stat

            # interpolate synthetic levels if current OB quote sum is insufficient
            levels = self._pad_levels_to_quote(levels, side, quote_target)

            # walk the book to fill the inflated quote notional
            filled_base_sim, vwap_sim, last_px_sim = self._simulate_by_quote(levels, quote_target)
            first_px_sim = levels[0][0] if levels else np.nan
            fees_usdt = -abs(q_quote_stat * FEE_BPS)  # 7.5 bps on inflated notional (×1000)

            # Spread cost = relative spread × inflated notional (negative)
            spread_usd = np.nan
            if np.isfinite(top_bid) and np.isfinite(top_ask):
                mid = (top_ask + top_bid) / 2.0
                rel_spread = ((top_ask - top_bid) / mid) if (mid and mid > 0) else np.nan
                spread_usd = (-rel_spread * q_quote_stat) if np.isfinite(rel_spread) else np.nan

            # Slippage cost = slipp_rel × inflated notional (negative)
            slippage_usd = np.nan
            if np.isfinite(first_px_sim) and np.isfinite(arrival):
                slipp_rel = ((first_px_sim - arrival) / arrival) if side == "buy" else ((arrival - first_px_sim) / arrival)
                slippage_usd = (-slipp_rel * q_quote_stat) if np.isfinite(slipp_rel) else np.nan

            # Impact cost = (vwap vs first) relative × inflated notional (negative, adverse)
            impact_usd = np.nan
            if np.isfinite(vwap_sim) and np.isfinite(first_px_sim):
                imp_rel_raw = (vwap_sim - first_px_sim) / first_px_sim
                imp_rel = imp_rel_raw if side == "buy" else (-imp_rel_raw)
                impact_usd = (-imp_rel * q_quote_stat) if np.isfinite(imp_rel) else np.nan

            # Total
            mkt_total_usd = np.nan
            if all(np.isfinite(x) for x in (fees_usdt, impact_usd, spread_usd, slippage_usd)):
                mkt_total_usd = fees_usdt + impact_usd + spread_usd + slippage_usd

            # Percent/bp denominators use the inflated notional directly
            net_quote = q_quote_stat

            def pct_of_notional(x):
                return (x / net_quote * 100.0) if (np.isfinite(x) and np.isfinite(net_quote) and net_quote > 0) else np.nan

            mkt_total_pct = pct_of_notional(mkt_total_usd)
            fees_pct_net = pct_of_notional(fees_usdt)
            impact_pct_net = pct_of_notional(impact_usd)
            spread_pct_net = pct_of_notional(spread_usd)
            slip_pct_net = pct_of_notional(slippage_usd)

            # -------- Send REAL testnet order (private client) --------
            cost_str = self._quote_qty_param(sym, q_quote_real)
            if side == "sell":
                # place *real* order (not inflated): approximate base from real quote / arrival
                amt_real = q_quote_real / (arrival or 1.0)
                amt_real = float(self.ex_priv.amount_to_precision(sym, amt_real))
                order = self.ex_priv.create_order(sym, "market", "sell", amt_real)
            else:
                order = self.ex_priv.create_order(sym, "market", "buy", None, None, {"quoteOrderQty": cost_str})

            oid = order.get("id")
            full = order
            for _ in range(20):
                try:
                    if oid:
                        full = self.ex_priv.fetch_order(oid, sym)
                except Exception:
                    pass
                status = (full.get("status") or "").lower()
                filled = float(full.get("filled") or full.get("amount") or 0.0)
                if status in ("closed", "canceled") or filled > 0:
                    break
                time.sleep(0.10)

        except Exception as e:
            traceback.print_exc()
            self._close_wait(wait)
            messagebox.showerror("Order", f"{type(e).__name__}: {e}")
            return
        finally:
            self._close_wait(wait)

        # ---------- First fill timestamp detection ----------
        def _extract_first_fill_ms(payload: dict) -> Optional[int]:
            if not isinstance(payload, dict):
                return None
            t = payload.get("transactTime")
            if isinstance(t, (int, float)):
                return int(t)
            fills = payload.get("fills") or []
            if fills:
                try:
                    tf = fills[0].get("time")
                    if isinstance(tf, (int, float)):
                        return int(tf)
                except Exception:
                    pass
            return None

        info_full = full.get("info") or {}
        info_order = order.get("info") if isinstance(order, dict) else {}

        t_first = _extract_first_fill_ms(info_full)
        if t_first is None:
            t_first = _extract_first_fill_ms(info_order)
        if t_first is None:
            t_first = full.get("timestamp") if isinstance(full.get("timestamp"), (int, float)) else None

        slip_ms = (int(t_first) - t_click) if (t_first is not None) else None

        # Human-readable first-fill timestamp (local time)
        if t_first is not None:
            try:
                ts_human = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(int(t_first) / 1000))
            except Exception:
                ts_human = "—"
        else:
            ts_human = "—"

        # Execution summary popup
        # Report simulated (inflated ×1000) quantities only
        messagebox.showinfo(
            "Execution",
            f"{side.upper()} executed on {sym}\n"
            f"Base exchanged (×1000):  {fmt_qty(filled_base_sim)} {base}\n"
            f"Quote exchanged (×1000): {fmt_usd(q_quote_stat)} {QUOTE}"
        )

        # Accumulate session friction
        if np.isfinite(mkt_total_usd):
            self.session_friction_usdt += float(mkt_total_usd)

        # --- Header stats (these must update every trade) ---
        self._set_stat("t_first", ts_human)  # NEW
        self._set_stat("way", side.upper())
        self._set_stat("exec_base", f"{fmt_qty(filled_base_sim)} {base}  (×1000)")
        self._set_stat("exec_quote", f"{fmt_usd(q_quote_stat)} {QUOTE} (×1000)")
        self._set_stat("slip_ms", f"{int(slip_ms)} ms" if slip_ms is not None else "—")
        self._set_stat("arrival", f"{fmt_px(arrival)} USDT")

        # pct helpers
        def pct(a, b):
            return ((a / b - 1.0) * 100.0) if (np.isfinite(a) and np.isfinite(b) and b != 0) else np.nan

        f_vs_arr = pct(first_px_sim, arrival)
        l_vs_first = pct(last_px_sim, first_px_sim)
        v_vs_first = pct(vwap_sim, first_px_sim)

        self._set_stat("first_px", f"{fmt_px(first_px_sim)} USDT  |  {fmt_pct_or_bp(f_vs_arr)}")
        self._set_stat("last_px", f"{fmt_px(last_px_sim)} USDT   |  {fmt_pct_or_bp(l_vs_first)}")
        self._set_stat("vwap", f"{fmt_px(vwap_sim)} USDT  |  {fmt_pct_or_bp(v_vs_first)}")

        # components & total — single measure after USDT (no parentheses)
        self._set_stat_signed("mkt_total",
                              f"{fmt_usd(mkt_total_usd)} USDT  |  {fmt_pct_or_bp(mkt_total_pct)}",
                              positive_green=(np.isfinite(mkt_total_usd) and mkt_total_usd >= 0))
        self._set_stat_signed("fees",
                              f"{fmt_usd(fees_usdt)} USDT  |  {fmt_pct_or_bp(fees_pct_net)}",
                              positive_green=False)
        self._set_stat_signed("impact",
                              f"{fmt_usd(impact_usd)} USDT  |  {fmt_pct_or_bp(impact_pct_net)}",
                              positive_green=False)
        self._set_stat_signed("spread",
                              f"{fmt_usd(spread_usd)} USDT  |  {fmt_pct_or_bp(spread_pct_net)}",
                              positive_green=False)
        self._set_stat_signed("slippage",
                              f"{fmt_usd(slippage_usd)} USDT  |  {fmt_pct_or_bp(slip_pct_net)}",
                              positive_green=(np.isfinite(slippage_usd) and slippage_usd >= 0))

    # ---------- Utilities ----------
    def _set_stat(self, key: str, text: str):
        self.stats[key].configure(text=text, style="StatValue.TLabel")

    def _set_stat_signed(self, key: str, text: str, positive_green: bool):
        self.stats[key].configure(
            text=text,
            style=("StatValueGreen.TLabel" if positive_green else "StatValueRed.TLabel")
        )

    def _on_close(self):
        self.destroy()

# ---------- Main ----------
if __name__ == "__main__":
    app = FrictionApp()
    app.mainloop()
