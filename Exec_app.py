# Trading_app.py
# ----------------------------------------------------
# Trading Frictions (Mainnet market data via ccxt REST) + Testnet paper orders
# ----------------------------------------------------
import asyncio
import math
import sys
import time
import tkinter as tk
import traceback
from tkinter import ttk, messagebox
from typing import Dict, Optional, List, Tuple

import ccxt
import numpy as np
from ccxt.base.errors import RequestTimeout, NetworkError, ExchangeError
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure

from trading_utils import (
    API_KEY,
    API_SECRET,
    twap_next_child,
    vwap_next_child,
    is_next_child,
)

# ---------- Palette ----------
BLOOM_BLUE = "#2a6df4"
BLOOM_GREEN = "#2bb673"
BLOOM_GREEN_H = "#31c27f"
BLOOM_RED = "#f05454"
BLOOM_RED_H = "#ff6a6a"
BLOOM_AMBER = "#f4a62a"
FG_MAIN = "#e9edf3"
FG_MUTED = "#aeb7c7"
BG_DARK = "#0b0f17"
BG_PANEL = "#161b26"
SEP = "#444a60"

# ---------- Universe ----------
BASES_TOP10 = ["BTC", "ETH", "BNB", "SOL", "XRP", "ADA", "DOGE", "TRX", "LTC", "BCH"]
ALL_BASES = BASES_TOP10
QUOTE = "USDT"
DEFAULT_SYMBOLS = [f"{b}/{QUOTE}" for b in ALL_BASES]
VENUES = ["binance", "bybit", "kucoin", "gateio"]


# ---------- Formatting ----------
def _trim(x, fmt):
    s = fmt.format(x)
    if "." in s: s = s.rstrip("0").rstrip(".")
    return s


def fmt_qty2(x):
    if x is None or not np.isfinite(x): return "—"
    return _trim(x, "{:,.2f}")


def fmt_qty(x): return "—" if (x is None or not np.isfinite(x)) else _trim(x, "{:,.6f}")


def fmt_usd(x): return "—" if (x is None or not np.isfinite(x)) else _trim(x, "{:,.2f}")


def fmt_px(x):  return "—" if (x is None or not np.isfinite(x)) else _trim(x, "{:,.2f}")


def fmt_pct_signed(x): return "—" if (x is None or not np.isfinite(x)) else _trim(x, "{:+.4f}%")


def fmt_pct2_signed(x): return "—" if (x is None or not np.isfinite(x)) else _trim(x, "{:+.2f}%")


def fmt_bp_from_pct(x):
    if x is None or not np.isfinite(x): return "—"
    val = _trim(x * 100.0, "{:+.2f}")
    return f"{val} bp"


def fmt_pct_or_bp(pct_value):
    if pct_value is None or not np.isfinite(pct_value): return "—"
    return fmt_pct2_signed(pct_value) if abs(pct_value) >= 1.0 else fmt_bp_from_pct(pct_value)


FEE_BPS = 0.00075  # 7.5 bps
LIQ_FACTOR_K = 1000
TARGET_START_USDT = 100_000.0

# ---------- VWAP helper ----------
def calculate_VWAP(levels: List[Tuple[float, float]], quote_target: float):
    remaining = float(quote_target)
    if not levels or remaining <= 0.0:
        return 0.0, float("nan"), float("nan")

    filled_base, spent_quote, last_px = 0.0, 0.0, float("nan")
    for px, qty in levels:
        if px <= 0.0 or qty <= 0.0:
            continue
        take_base = min(qty, remaining / px)
        filled_base += take_base
        spent_quote += take_base * px
        last_px = px
        remaining -= take_base * px
        if remaining <= 1e-12:
            break
    vwap = spent_quote / filled_base if filled_base > 0.0 else float("nan")
    return filled_base, vwap, last_px

# ---------- Main App ----------
class FrictionApp(tk.Tk):
    def __init__(self):
        super().__init__()

        # GUI setup
        self.title("Exec Dashboard")
        self.configure(bg=BG_DARK)
        self.minsize(1280, 820)
        if sys.platform.startswith("win"):
            self.state("zoomed")
        self.minsize(1280, 700)

        # Call style
        self._style()

        # ------------------ Strategy runtime state ------------------
        self.current_strat = None
        self._strat_execs: List[Tuple[float, float]] = []
        self._strat_child_execs: List[dict] = []
        self._strat_venue_stats: Dict[str, dict] = {}
        self._strat_mkt_samples: List[Tuple[float, float]] = []
        self._strat_price_times: List[float] = []
        self._strat_price_values: List[float] = []
        self._strat_exec_times: List[float] = []
        self._strat_exec_prices: List[float] = []
        self._strat_exec_unit_vol: List[float] = []
        self._strat_exec_cum_vol: List[float] = []
        self._strat_exec_cum_notional: float = 0.0
        self._strat_chart_fig: Optional[Figure] = None
        self._strat_chart_canvas: Optional[FigureCanvasTkAgg] = None
        self._strat_ax_price = None
        self._strat_ax_vol = None

        # Build UI / layout
        self._build_layout()
        if not self._connect_clients():
            self._fatal_disable()

    def _style(self):
        style = ttk.Style(self)
        style.theme_use('clam')
        style.configure('TButton', font=('Helvetica', 12), foreground='white', background='#007acc')
        style.map('TButton',
                  background=[('active', '#005f99')],
                  foreground=[('disabled', '#999999')])
        style.configure('TLabel', font=('Helvetica', 12))


        # Initial refresh
        self.after(50, self.refresh_balance)
        # Heartbeats
        self.after(400, self._tick_selected_price)  # ~2.5 Hz (REST)
        self.after(10_000, self._heartbeat_10s)
        self.protocol("WM_DELETE_WINDOW", self._on_close)

        # Auto-liquidate at launch (after UI + clients settle)
        self.after(800, self._auto_liquidate_on_launch)



# ---------- Styles ----------
def _style(self):
    s = ttk.Style(self)
    s.theme_use("clam")

    # -------- Global colors --------
    s.configure(".", background=BG_DARK, foreground=FG_MAIN)

    # -------- Notebook / Tabs (INVERTED) --------
    # Notebook frame (no border, dark background)
    s.configure(
        "Bloom.TNotebook",
        background=BG_DARK,
        borderwidth=0,
        tabmargins=(8, 4, 8, 0)  # a bit tighter vertically
    )

    # Unselected tabs: DARK tile + AMBER text (so unselected looks like your old "Trading")
    s.configure(
        "Bloom.TNotebook.Tab",
        background="#232936",
        foreground=BLOOM_AMBER,  # << amber on unselected
        padding=(16, 8, 16, 8),  # slightly smaller than before
        font=("Menlo", 12, "bold"),
        borderwidth=0
    )

    # Selected tab: LIGHTER panel + LIGHT text (so selected looks like your old "Exec")
    s.map(
        "Bloom.TNotebook.Tab",
        background=[("selected", BG_PANEL), ("active", "#2a3142")],
        foreground=[("selected", "#e1e7f5"), ("active", "#ffffff")]
    )

    # -------- Separators / Labels --------
    s.configure("Bloom.TSeparator", background=SEP)
    s.configure("H1.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 15, "bold"))
    # --- excerpt from _style() ---
    s.configure("SectionTitle.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 15, "bold"))
    s.configure("StatName.TLabel", background=BG_DARK, foreground=FG_MUTED, font=("Menlo", 12, "bold"))
    s.configure("StatValue.TLabel", background=BG_DARK, foreground="#e9edf3", font=("Menlo", 13, "bold"))
    s.configure("StatAmber.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 13, "bold"))  # NEW
    s.configure("StatValueGreen.TLabel", background=BG_DARK, foreground=BLOOM_GREEN_H, font=("Menlo", 13, "bold"))
    s.configure("StatValueRed.TLabel", background=BG_DARK, foreground=BLOOM_RED_H, font=("Menlo", 13, "bold"))
    s.configure("PNL.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 12, "bold"))

    s.configure("LivePrice.TLabel", background=BG_PANEL, foreground=BLOOM_AMBER, font=("Menlo", 16, "bold"),
                padding=(10, 6))

    # -------- Panels / inputs (tighter vertical padding) --------
    s.configure("Panel.TFrame", background=BG_PANEL, relief="flat", padding=(10, 6))  # was (10,10)
    s.configure("Dark.TEntry", fieldbackground=BG_PANEL, foreground=FG_MAIN, insertcolor=FG_MAIN, padding=3)
    s.configure("Dark.TCombobox", fieldbackground=BG_PANEL, background=BG_PANEL, foreground=FG_MAIN)
    s.map("Dark.TCombobox",
          fieldbackground=[("readonly", BG_PANEL)],
          background=[("readonly", BG_PANEL)],
          foreground=[("readonly", FG_MAIN)])

    # -------- Buttons (tighter paddings) --------
    s.configure("Bloom.Green.TButton", padding=(10, 6), background=BLOOM_GREEN, foreground=BG_DARK,
                font=("Helvetica", 12, "bold"), borderwidth=0)  # was (12,8)
    s.map("Bloom.Green.TButton", background=[("active", BLOOM_GREEN_H)])
    s.configure("Bloom.Red.TButton", padding=(10, 6), background=BLOOM_RED, foreground="#ffffff",
                font=("Helvetica", 12, "bold"), borderwidth=0)  # was (12,8)
    s.map("Bloom.Red.TButton", background=[("active", BLOOM_RED_H)])
    s.configure("Bloom.Amber.TButton", padding=(8, 5), background=BLOOM_AMBER, foreground=BG_DARK,
                font=("Helvetica", 11, "bold"), borderwidth=0)  # was (10,6)
    s.configure("Bloom.Blue.TButton", padding=(8, 5), background=BLOOM_BLUE, foreground="#ffffff",
                font=("Helvetica", 11, "bold"), borderwidth=0)

    # -------- Strat progress bar (thin, green, horizontal) --------
    s.configure(
        "Strat.Green.Horizontal.TProgressbar",
        troughcolor=BG_DARK,
        background=BLOOM_GREEN,
        thickness=3,
        borderwidth=0,
    )

    # -------- Tables --------
    s.configure("Balances.Treeview", background=BG_PANEL, fieldbackground=BG_PANEL, foreground=FG_MAIN, rowheight=22,
                borderwidth=0)
    s.configure("Balances.Treeview.Heading", background=BG_DARK, foreground=FG_MAIN, relief="flat",
                font=("Menlo", 11, "bold"))
    s.configure("StatTable.Treeview", background=BG_PANEL, fieldbackground=BG_PANEL, foreground=FG_MAIN, rowheight=22,
                borderwidth=0)
    s.configure("StatTable.Treeview.Heading", background=BG_DARK, foreground=FG_MAIN, relief="flat",
                font=("Menlo", 11, "bold"))
    s.configure("StatTableAmber.Treeview", background=BG_PANEL, fieldbackground=BG_PANEL, foreground=BLOOM_AMBER,
                rowheight=22, borderwidth=0)
    s.configure("StatTableAmber.Treeview.Heading", background=BG_DARK, foreground=FG_MAIN, relief="flat",
                font=("Menlo", 11, "bold"))

    # -------- Spacers --------
    s.configure("Spacer.TFrame", background=BG_DARK)


# ---------- Layout (Left: Balance + Controls | Right: Stats + Placeholder) ----------
def _build_layout(self):
    # ===== NOTEBOOK (Tabs) =====
    self.tabs = ttk.Notebook(self, style="Bloom.TNotebook")
    self.tabs.pack(fill="both", expand=True, padx=10, pady=10)

    # ---------- TAB 1: Trading + Exec details ----------
    tab1 = ttk.Frame(self.tabs)
    self.tabs.add(tab1, text="Trading + Exec details")

    # ----- Paned window (left/right) inside Tab 1 -----
    root = ttk.Panedwindow(tab1, orient="horizontal")
    root.pack(fill="both", expand=True)

    # ===== LEFT PANE =====
    left_pane = ttk.Frame(root, padding=(6, 6))
    left_pane.grid_columnconfigure(0, weight=1)
    left_pane.grid_rowconfigure(0, weight=0)  # balances fixed height
    left_pane.grid_rowconfigure(1, weight=1)  # controls expand vertically

    # -- Top-left: Balance & PnL --
    left_top = ttk.Frame(left_pane)
    left_top.grid(row=0, column=0, sticky="ew", pady=(0, 6))
    ttk.Label(left_top, text="Balance & PnL", style="SectionTitle.TLabel").pack(anchor="w", pady=(0, 6))

    cols = ("asset", "qty", "mid_px", "qty_usdt", "theo_qty_arr")
    self.tree = ttk.Treeview(left_top, columns=cols, show="headings",
                             style="Balances.Treeview", selectmode="none", height=11)
    self.tree.heading("asset", text="ASSET")
    self.tree.heading("qty", text="QTY")
    self.tree.heading("mid_px", text="MID PX")
    self.tree.heading("qty_usdt", text="QTY IN USDT (±% vs session OPEN)")
    self.tree.heading("theo_qty_arr", text="Theo QTY at Arrival")
    self.tree.column("asset", width=110, anchor="center")
    self.tree.column("qty", width=140, anchor="center")
    self.tree.column("mid_px", width=120, anchor="center")
    self.tree.column("qty_usdt", width=280, anchor="center")
    self.tree.column("theo_qty_arr", width=220, anchor="center")
    self.tree.pack(fill="x", expand=False)

    bal_footer = ttk.Frame(left_top, padding=(0, 6))
    bal_footer.pack(fill="x")

    self.total_lbl = ttk.Label(bal_footer, text="Total: — USDT", style="StatValue.TLabel")
    self.total_lbl.grid(row=0, column=0, sticky="w")

    self.pnl_lbl = ttk.Label(
        bal_footer,
        text="PnL vs Arrival Ptf: —  |  market: —  |  friction: —",
        style="PNL.TLabel"
    )

    self.pnl_lbl.grid(row=1, column=0, sticky="w", pady=(2, 4))

    bal_toolbar = ttk.Frame(left_top, style="Panel.TFrame")
    bal_toolbar.pack(fill="x")
    bal_toolbar.grid_columnconfigure(0, weight=1, uniform="axes3")
    bal_toolbar.grid_columnconfigure(1, weight=1, uniform="axes3")
    bal_toolbar.grid_columnconfigure(2, weight=1, uniform="axes3")

    self.reset_btn = ttk.Button(
        bal_toolbar, text="Reset PnL Baseline",
        style="Bloom.Amber.TButton",
        command=self._reset_pnl_baseline
    )
    self.reset_btn.grid(row=0, column=0, sticky="e", padx=12, pady=(0, 8))

    self.liquidate_btn = ttk.Button(
        bal_toolbar, text="Liquidate All",
        style="Bloom.Blue.TButton",
        command=self._liquidate_all,
        state="normal"
    )
    self.liquidate_btn.grid(row=0, column=2, sticky="w", padx=12, pady=(0, 8))

    # -- Bottom-left: Controls container (Selection / Exec / SOR / Strat) --
    left_bottom = ttk.Frame(left_pane, padding=(6, 6), style="Panel.TFrame")
    left_bottom.grid(row=1, column=0, sticky="nsew")
    left_bottom.grid_columnconfigure(0, weight=1)

    # ===== PART 2: Selection =====
    p2 = ttk.Frame(left_bottom, style="Panel.TFrame")
    p2.grid(row=0, column=0, sticky="ew", pady=(0, 8))
    for c in range(7):
        p2.grid_columnconfigure(c, weight=1)

    ttk.Label(p2, text="Selection", style="SectionTitle.TLabel").grid(
        row=0, column=0, columnspan=8, sticky="w", pady=(0, 6)
    )

    ttk.Label(p2, text="Base:", style="StatName.TLabel").grid(row=1, column=0, sticky="e", padx=(0, 6))
    self.base_cb = ttk.Combobox(
        p2, values=ALL_BASES, textvariable=self.base_var, width=10,
        state="readonly", style="Dark.TCombobox"
    )
    self.base_cb.grid(row=1, column=1, sticky="w")
    self.base_cb.bind("<<ComboboxSelected>>", lambda _e: self._tick_selected_price())

    ttk.Label(p2, text="Quote:", style="StatName.TLabel").grid(row=1, column=2, sticky="e", padx=(12, 6))
    ttk.Label(p2, text=QUOTE, style="StatValue.TLabel").grid(row=1, column=3, sticky="w")

    ttk.Label(p2, text="Quote Qty (K USDT):", style="StatName.TLabel").grid(row=1, column=4, sticky="e", padx=(12, 6))
    self.quote_entry = ttk.Entry(p2, textvariable=self.quote_qty_var, width=12, style="Dark.TEntry")
    self.quote_entry.grid(row=1, column=5, sticky="w")

    self.sel_price_chip = ttk.Label(p2, text="—", style="LivePrice.TLabel")
    self.sel_price_chip.grid(row=1, column=6, sticky="e", padx=(12, 0))

    ttk.Frame(left_bottom, height=10, style="Spacer.TFrame").grid(row=1, column=0, sticky="ew")

    # ===== PART 3: Exec at Market =====
    p3 = ttk.Frame(left_bottom, style="Panel.TFrame")
    p3.grid(row=2, column=0, sticky="ew", pady=(0, 8))

    ttk.Label(p3, text="Exec at Market", style="SectionTitle.TLabel").grid(
        row=0, column=0, columnspan=3, sticky="w", pady=(0, 6)
    )
    p3.grid_columnconfigure(0, weight=1)
    p3.grid_columnconfigure(1, weight=1)
    p3.grid_columnconfigure(2, weight=1)

    self.buy_btn = ttk.Button(p3, text="Buy", style="Bloom.Green.TButton",
                              command=lambda: self._place("buy"))
    self.sell_btn = ttk.Button(p3, text="Sell", style="Bloom.Red.TButton",
                               command=lambda: self._place("sell"))
    self.buy_btn.grid(row=1, column=0, padx=12, pady=4, sticky="e")
    self.sell_btn.grid(row=1, column=2, padx=12, pady=4, sticky="w")

    ttk.Frame(left_bottom, height=10, style="Spacer.TFrame").grid(row=3, column=0, sticky="ew")

    # ===== PART 4: SOR Exec =====
    p4 = ttk.Frame(left_bottom, style="Panel.TFrame")
    p4.grid(row=4, column=0, sticky="ew", pady=(0, 8))

    ttk.Label(p4, text="SOR Exec", style="SectionTitle.TLabel").grid(
        row=0, column=0, columnspan=3, sticky="w", pady=(0, 4)
    )

    # Centered grid of venue checkboxes (no extra headline line)
    venues_frame = ttk.Frame(p4, style="Panel.TFrame")
    venues_frame.grid(row=1, column=0, columnspan=3, pady=(0, 4))
    for i in range(5):
        venues_frame.grid_columnconfigure(i, weight=1)

    r, c = 0, 0
    for v in VENUES:
        cb = ttk.Checkbutton(venues_frame, text=v, variable=self.venue_vars[v])
        cb.grid(row=r, column=c, padx=12, pady=4, sticky="")
        c += 1
        if c >= 5:
            c = 0
            r += 1

    p4.grid_columnconfigure(0, weight=1)
    p4.grid_columnconfigure(1, weight=1)
    p4.grid_columnconfigure(2, weight=1)

    btn_buy_sor = ttk.Button(p4, text="Buy (SOR)", style="Bloom.Green.TButton",
                             command=self._placeholder_sor_buy)
    btn_sell_sor = ttk.Button(p4, text="Sell (SOR)", style="Bloom.Red.TButton",
                              command=self._placeholder_sor_sell)
    btn_buy_sor.grid(row=3, column=0, padx=12, pady=6, sticky="e")
    btn_sell_sor.grid(row=3, column=2, padx=12, pady=6, sticky="w")

    ttk.Frame(left_bottom, height=10, style="Spacer.TFrame").grid(row=5, column=0, sticky="ew")

    # ===== PART 5: Strat Exec (two lines) =====
    p5 = ttk.Frame(left_bottom, style="Panel.TFrame")
    p5.grid(row=6, column=0, sticky="ew", pady=(0, 8))

    p5.grid_columnconfigure(0, weight=1)
    p5.grid_columnconfigure(1, weight=1)
    p5.grid_columnconfigure(2, weight=1)

    ttk.Label(p5, text="Strat Exec", style="SectionTitle.TLabel").grid(
        row=0, column=0, columnspan=3, sticky="w", pady=(0, 6)
    )

    controls = ttk.Frame(p5, style="Panel.TFrame")
    controls.grid(row=1, column=0, columnspan=3, sticky="ew")
    # side spacers
    for col in (0, 7):
        controls.grid_columnconfigure(col, weight=1)
    # content columns: fixed
    for col in (1, 2, 3, 4, 5, 6):
        controls.grid_columnconfigure(col, weight=0)

    ttk.Label(controls, text="Strategy:", style="StatName.TLabel").grid(row=0, column=1, sticky="e", padx=(0, 6))
    ttk.Combobox(
        controls,
        values=["TWAP", "VWAP", "IS"],
        textvariable=self.strategy_var,
        width=15,  # smaller to make room for Sub-Orders/min
        state="readonly",
        style="Dark.TCombobox"
    ).grid(row=0, column=2, sticky="w")

    ttk.Label(controls, text="Duration (min):", style="StatName.TLabel").grid(row=0, column=3, sticky="e", padx=(24, 6))
    ttk.Entry(controls, textvariable=self.duration_var, width=8, style="Dark.TEntry").grid(row=0, column=4, sticky="w")

    ttk.Label(controls, text="Sub-Orders/min:", style="StatName.TLabel").grid(row=0, column=5, sticky="e", padx=(24, 6))
    ttk.Entry(controls, textvariable=self.suborders_per_min_var, width=6, style="Dark.TEntry").grid(row=0, column=6,
                                                                                                    sticky="w")

    ttk.Checkbutton(controls, text="Use SOR", variable=self.use_sor_var).grid(row=0, column=7, sticky="w", padx=(24, 0))

    self.strat_buy_btn = ttk.Button(
        p5,
        text="Buy (Strat)",
        style="Bloom.Green.TButton",
        command=lambda: self._start_strat("buy"),  # NEW
    )
    self.strat_cancel_btn = ttk.Button(
        p5,
        text="Cancel",
        style="Bloom.Amber.TButton",
        command=self._cancel_strat,  # NEW
    )
    self.strat_sell_btn = ttk.Button(
        p5,
        text="Sell (Strat)",
        style="Bloom.Red.TButton",
        command=lambda: self._start_strat("sell"),  # NEW
    )

    self.strat_buy_btn.grid(row=2, column=0, padx=12, pady=6, sticky="e")
    self.strat_cancel_btn.grid(row=2, column=1, padx=12, pady=6, sticky="n")
    self.strat_sell_btn.grid(row=2, column=2, padx=12, pady=6, sticky="w")

    self.strat_progress = ttk.Progressbar(
        p5,
        mode="determinate",
        maximum=100,
        value=0,  # start empty on app launch
        style="Strat.Green.Horizontal.TProgressbar"
    )
    self.strat_progress.grid(row=3, column=0, columnspan=3, sticky="ew", padx=12, pady=(4, 2))

    # ===== RIGHT PANE =====
    right_pane = ttk.Frame(root, padding=(6, 6))
    right_pane.grid_columnconfigure(0, weight=1)
    right_pane.grid_rowconfigure(0, weight=1)
    right_pane.grid_rowconfigure(1, weight=0)

    right_top = ttk.Frame(right_pane)
    right_top.grid(row=0, column=0, sticky="nsew", pady=(0, 6))

    stats_title_frame = ttk.Frame(right_top, style="Panel.TFrame")
    stats_title_frame.pack(anchor="w", fill="x", pady=(0, 6))

    ttk.Label(
        stats_title_frame,
        text="Last Order — Stats",
        style="SectionTitle.TLabel"
    ).pack(side="left", padx=(0, 8))

    self.stats_side_lbl = ttk.Label(
        stats_title_frame,
        text="",
        style="StatValue.TLabel"
    )
    self.stats_side_lbl.pack(side="left")

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
    self.stats = {}
    for key, label in spec:
        row = ttk.Frame(right_top, padding=(1, 1))
        row.pack(anchor="w", pady=1, fill="x")
        ttk.Label(row, text=label, style="StatName.TLabel").pack(side="left")
        # default style; we’ll recolor selectively via _set_stat
        val = ttk.Label(row, text="—", style="StatValue.TLabel")
        val.pack(side="right")
        self.stats[key] = val

    # keys that must always render in BLOOM_AMBER
    self._amber_stat_keys = {
        "t_first", "way", "exec_base", "exec_quote",
        "slip_ms", "arrival", "first_px", "last_px", "vwap"
    }

    right_bottom = ttk.Frame(right_pane, style="Panel.TFrame")
    right_bottom.grid(row=1, column=0, sticky="nsew")
    right_pane.grid_rowconfigure(1, weight=1)

    ttk.Label(right_bottom, text="Last — SOR Per-Venue", style="SectionTitle.TLabel").pack(anchor="w", pady=(0, 6))

    table_frame = ttk.Frame(right_bottom, style="Panel.TFrame")
    table_frame.pack(fill="both", expand=True)

    # Dark style; no horizontal scrollbar (we auto-fit columns)
    self.sor_table = ttk.Treeview(
        table_frame,
        show="headings",
        height=10,
        style="StatTable.Treeview",
        selectmode="none"
    )
    self.sor_table.pack(fill="both", expand=True)

    self._sor_stats_order = [
        "vol_pct",  # << first
        "slippage_ms",
        "first_vs_arrival",
        "last_vs_first",
        "vwap_vs_first",
        "fees_usdt",
        "impact_usdt",
        "spread_usdt",
        "slippage_usdt",
        "total_mkt_usdt",
    ]
    self._sor_stat_labels = {
        "vol_pct": "% of Volume",
        "slippage_ms": "Slippage (ms: click→snapshot)",
        "first_vs_arrival": "First px | vs Arrival",
        "last_vs_first": "Last px  | vs First",
        "vwap_vs_first": "VWAP     | vs First",
        "fees_usdt": "Fees (USDT)",
        "impact_usdt": "Impact (USDT)",
        "spread_usdt": "Spread (USDT)",
        "slippage_usdt": "Slippage (USDT)",
        "total_mkt_usdt": "Total market friction (USDT)",
    }

    self.sor_table["columns"] = ["Stat"]
    self.sor_table.heading("Stat", text="Stat", anchor="w")
    self.sor_table.column("Stat", width=320, stretch=True, anchor="w")
    for stat in self._sor_stats_order:
        self.sor_table.insert("", "end", iid=stat, values=(self._sor_stat_labels[stat],))

    root.add(left_pane)
    root.add(right_pane)
    root.pane(left_pane, weight=58)
    root.pane(right_pane, weight=42)

    def _set_initial_split():
        try:
            root.sashpos(0, int(self.winfo_width() * 0.58))
        except Exception:
            pass

    self.after(0, _set_initial_split)

    def _sync_sel_price():
        try:
            sym = f"{self.base_var.get()}/{QUOTE}"
            _, _, mid = self._rest_ticker_cached(sym)
            txt = f"{sym}  {fmt_px(mid) if (mid and np.isfinite(mid) and mid > 0) else '—'}"
            self.sel_price_chip.configure(text=txt)
        except Exception:
            pass
        self.after(400, _sync_sel_price)

    self.after(200, _sync_sel_price)

    # ---------- TAB 2: Exec Strat ----------
    tab2 = ttk.Frame(self.tabs)
    self.tabs.add(tab2, text="Exec Strat")

    # Grid: 2 rows (top, bottom) × 2 cols (left, right); bottom spans both cols.
    tab2.grid_rowconfigure(0, weight=1)  # top half
    tab2.grid_rowconfigure(1, weight=1)  # bottom half
    tab2.grid_columnconfigure(0, weight=1)  # left
    tab2.grid_columnconfigure(1, weight=1)  # right

    # Part 1 (top-left): Strat Stats
    strat_top_left = ttk.Frame(tab2, style="Panel.TFrame", padding=(10, 10))
    strat_top_left.grid(row=0, column=0, sticky="nsew", padx=(0, 6), pady=(0, 6))

    ttk.Label(strat_top_left, text="Strat Stats", style="SectionTitle.TLabel").pack(anchor="w", pady=(0, 6))
    self.strat_stats = {}
    for key, label in [
        ("s_name", "Strategy"),
        ("s_status", "Status"),
        ("s_launch", "Launch time"),
        ("s_way", "Way"),
        ("s_total_quote", "Order quote qty (USDT)"),
        ("s_remaining_quote", "Remaining quote (USDT)"),
        ("s_remaining_time", "Remaining time"),
        ("s_perf_arrival", "Perf vs arrival"),
        ("s_perf_twap", "Perf vs mkt TWAP"),
        ("s_mkt_total", "Total market friction"),
        ("s_fees", "  Fees"),
        ("s_impact", "  Impact"),
        ("s_spread", "  Spread"),
        ("s_slippage", "  Slippage"),
    ]:
        row = ttk.Frame(strat_top_left, padding=(1, 1))
        row.pack(anchor="w", pady=1, fill="x")
        ttk.Label(row, text=label, style="StatName.TLabel").pack(side="left")
        val = ttk.Label(row, text="—", style="StatValue.TLabel")
        val.pack(side="right")
        self.strat_stats[key] = val

    # Part 2 (top-right): Strat — Per-Venue table
    strat_top_right = ttk.Frame(tab2, style="Panel.TFrame", padding=(10, 10))
    strat_top_right.grid(row=0, column=1, sticky="nsew", padx=(6, 0), pady=(0, 6))

    ttk.Label(strat_top_right, text="Strat — Per-Venue", style="SectionTitle.TLabel").pack(anchor="w", pady=(0, 6))
    s_table_frame = ttk.Frame(strat_top_right, style="Panel.TFrame")
    s_table_frame.pack(fill="both", expand=True)

    self.strat_sor_table = ttk.Treeview(
        s_table_frame,
        show="headings",
        height=10,
        style="StatTable.Treeview",
        selectmode="none"
    )
    # No horizontal scrollbar: let columns auto-fit within the panel width
    self.strat_sor_table.pack(side="left", fill="both", expand=True)

    # Structure: "Stat" column + per-venue columns set dynamically
    self._strat_venue_stat_order = [
        "vol_pct",
        "perf_arrival",
        "twap_order",
        "twap_mkt",
        "vwap_order",
        "fees",
        "impact",
        "slippage",
        "total_mkt",
    ]
    self._strat_venue_stat_labels = {
        "vol_pct": "% of Volume",
        "perf_arrival": "Perf vs arrival",
        "twap_order": "TWAP Order",
        "twap_mkt": "TWAP Market",
        "vwap_order": "VWAP Order",
        "fees": "Fees (USDT)",
        "impact": "Impact (USDT)",
        "slippage": "Slippage (USDT)",
        "total_mkt": "Total market friction (USDT)",
    }
    self.strat_sor_table["columns"] = ["Stat"]
    self.strat_sor_table.heading("Stat", text="Stat", anchor="w")
    self.strat_sor_table.column("Stat", width=280, stretch=True, anchor="w")
    for stat in self._strat_venue_stat_order:
        self.strat_sor_table.insert("", "end", iid=stat, values=(self._strat_venue_stat_labels[stat],))

    # Part 3 (bottom): Price & Volume chart
    strat_bottom = ttk.Frame(tab2, style="Panel.TFrame", padding=(10, 10))
    strat_bottom.grid(row=1, column=0, columnspan=2, sticky="nsew", pady=(6, 0))
    ttk.Label(strat_bottom, text="Strat — Price & Volume", style="SectionTitle.TLabel").pack(anchor="w", pady=(0, 4))

    # Initialize matplotlib chart for price + executions + volume
    self._init_strat_chart(strat_bottom)


# ---------- Strat Chart Helpers ----------
def _init_strat_chart(self, parent):
    """Create the price+volume chart in Tab 2 bottom panel."""
    try:
        self._strat_chart_fig = Figure(figsize=(6, 3))
        self._strat_ax_price = self._strat_chart_fig.add_subplot(2, 1, 1)
        self._strat_ax_vol = self._strat_chart_fig.add_subplot(2, 1, 2, sharex=self._strat_ax_price)

        # Figure / axes background (Bloomberg-ish dark)
        self._strat_chart_fig.patch.set_facecolor(BG_DARK)
        self._strat_ax_price.set_facecolor(BG_PANEL)
        self._strat_ax_vol.set_facecolor(BG_PANEL)

        # Labels
        self._strat_ax_price.set_ylabel("Price", color=FG_MAIN)
        self._strat_ax_vol.set_ylabel("Volume (USDT)", color=FG_MAIN)
        self._strat_ax_vol.set_xlabel("Time since start (s)", color=FG_MAIN)

        # Grid
        for ax in (self._strat_ax_price, self._strat_ax_vol):
            ax.grid(True, linestyle="--", linewidth=0.5, alpha=0.4, color=SEP)
            ax.tick_params(colors=FG_MAIN)

        self._strat_chart_canvas = FigureCanvasTkAgg(self._strat_chart_fig, master=parent)
        self._strat_chart_canvas.get_tk_widget().pack(fill="both", expand=True)
        self._strat_chart_fig.tight_layout()
    except Exception as e:
        print("[Strat Chart] init error:", e)
        self._strat_chart_fig = None
        self._strat_chart_canvas = None
        self._strat_ax_price = None
        self._strat_ax_vol = None


def _update_strat_chart(self):
    """Redraw price, exec VWAP, market TWAP and execution volume on the chart."""
    if not (self._strat_chart_fig and self._strat_chart_canvas and self._strat_ax_price and self._strat_ax_vol):
        return
    try:
        ax_price = self._strat_ax_price
        ax_vol = self._strat_ax_vol
        ax_price.cla()
        ax_vol.cla()

        # Restore backgrounds
        ax_price.set_facecolor(BG_PANEL)
        ax_vol.set_facecolor(BG_PANEL)

        # Labels
        ax_price.set_ylabel("Price", color=FG_MAIN)
        ax_vol.set_ylabel("Volume (USDT)", color=FG_MAIN)
        ax_vol.set_xlabel("Time since start (s)", color=FG_MAIN)

        # Grid
        for ax in (ax_price, ax_vol):
            ax.grid(True, linestyle="--", linewidth=0.5, alpha=0.4, color=SEP)
            ax.tick_params(colors=FG_MAIN)

        # ----- Time axis range -----
        all_times = []
        all_times.extend(self._strat_price_times or [])
        all_times.extend(self._strat_exec_times or [])
        t_min, t_max = 0.0, 0.0
        if all_times:
            t_min = 0.0
            t_max = max(all_times)
            if t_max <= 0:
                t_max = 1.0

        # ----- Price path: mid price -----
        legend_handles_price = []

        if self._strat_price_times and self._strat_price_values:
            lp_mid, = ax_price.plot(
                self._strat_price_times,
                self._strat_price_values,
                linewidth=1.3,
                color=BLOOM_AMBER,
            )
            lp_mid.set_label("Mid price")
            legend_handles_price.append(lp_mid)

        # ----- Exec VWAP *time series* -----
        if self._strat_exec_times and self._strat_execs:
            n = min(len(self._strat_exec_times), len(self._strat_execs))
            sum_K = 0.0
            sum_Kpx = 0.0
            vwap_times = []
            vwap_vals = []
            for i in range(n):
                K_i, px_i = self._strat_execs[i]
                t_i = float(self._strat_exec_times[i])
                if not (np.isfinite(K_i) and K_i > 0 and np.isfinite(px_i) and px_i > 0):
                    continue
                sum_K += K_i
                sum_Kpx += K_i * px_i
                if sum_K <= 0 or not np.isfinite(sum_Kpx):
                    continue
                vwap_times.append(t_i)
                vwap_vals.append(sum_Kpx / sum_K)
            if vwap_times:
                lp_vwap, = ax_price.plot(
                    vwap_times,
                    vwap_vals,
                    linestyle="--",
                    linewidth=1.2,
                    color=BLOOM_GREEN,
                )
                lp_vwap.set_label("Exec VWAP")
                legend_handles_price.append(lp_vwap)

        # ----- Market TWAP *time series* -----
        mkt_samples = self._strat_mkt_samples or []
        start_ts = None
        if self.current_strat:
            try:
                start_ts = float(self.current_strat.get("start_ts", None) or 0.0)
            except Exception:
                start_ts = None
        if start_ts is None and mkt_samples:
            start_ts = float(mkt_samples[0][0])

        if len(mkt_samples) >= 2 and start_ts is not None:
            twap_num = 0.0
            twap_den = 0.0
            twap_times = []
            twap_vals = []
            for i in range(len(mkt_samples) - 1):
                t_i, mid_i = mkt_samples[i]
                t_j, _ = mkt_samples[i + 1]
                dt = float(t_j - t_i)
                if dt <= 0:
                    continue
                if not (np.isfinite(mid_i) and mid_i > 0):
                    continue
                twap_num += mid_i * dt
                twap_den += dt
                if twap_den <= 0 or not np.isfinite(twap_num):
                    continue
                t_rel = max(0.0, float(t_j) - start_ts)
                twap_times.append(t_rel)
                twap_vals.append(twap_num / twap_den)
            if twap_times:
                lp_twap, = ax_price.plot(
                    twap_times,
                    twap_vals,
                    linestyle=":",
                    linewidth=1.2,
                    color=BLOOM_BLUE,
                )
                lp_twap.set_label("Mkt TWAP")
                legend_handles_price.append(lp_twap)

        # ----- Buy / Sell markers (triangles) -----
        if getattr(self, "_strat_buy_times", None) and getattr(self, "_strat_buy_prices", None):
            sc_buy = ax_price.scatter(
                self._strat_buy_times,
                self._strat_buy_prices,
                marker="^",
                s=40,
                color=BLOOM_GREEN,
                label="Buys",
            )
            legend_handles_price.append(sc_buy)

        if getattr(self, "_strat_sell_times", None) and getattr(self, "_strat_sell_prices", None):
            sc_sell = ax_price.scatter(
                self._strat_sell_times,
                self._strat_sell_prices,
                marker="v",
                s=40,
                color=BLOOM_RED,
                label="Sells",
            )
            legend_handles_price.append(sc_sell)

        # ----- Volume: unit bars + cumulative line -----
        legend_handles_vol = []

        if self._strat_exec_times and self._strat_exec_unit_vol:
            bars = ax_vol.bar(
                self._strat_exec_times,
                self._strat_exec_unit_vol,
                align="center",
            )
            if len(bars) > 0:
                bars[0].set_label("Child volume")
                legend_handles_vol.append(bars[0])

        if self._strat_exec_times and self._strat_exec_cum_vol:
            lv, = ax_vol.plot(
                self._strat_exec_times,
                self._strat_exec_cum_vol,
                linewidth=1.1,
            )
            lv.set_label("Cum. volume")
            legend_handles_vol.append(lv)

        # ----- Legends (white text) -----
        if legend_handles_price:
            leg_p = ax_price.legend(handles=legend_handles_price, loc="upper left", frameon=False)
            if leg_p:
                for txt in leg_p.get_texts():
                    txt.set_color(FG_MAIN)

        if legend_handles_vol:
            leg_v = ax_vol.legend(handles=legend_handles_vol, loc="upper left", frameon=False)
            if leg_v:
                for txt in leg_v.get_texts():
                    txt.set_color(FG_MAIN)

        self._strat_chart_fig.tight_layout()
        self._strat_chart_canvas.draw_idle()
    except Exception as e:
        print("[Strat Chart] update error:", e)


# ---------- Strat per-venue helper ----------
def _strat_update_venue_table(self):
    """Update 'Strat — Per-Venue' table from self._strat_venue_stats."""
    venues = sorted(self._strat_venue_stats.keys())
    if not venues:
        # Just keep Stat column and labels
        self.strat_sor_table["columns"] = ["Stat"]
        self.strat_sor_table.heading("Stat", text="Stat", anchor="w")
        self.strat_sor_table.column("Stat", width=280, stretch=True, anchor="w")
        for stat in self._strat_venue_stat_order:
            if not self.strat_sor_table.exists(stat):
                self.strat_sor_table.insert("", "end", iid=stat,
                                            values=(self._strat_venue_stat_labels[stat],))
            else:
                self.strat_sor_table.set(stat, "Stat", self._strat_venue_stat_labels[stat])
        return

    cols = ["Stat"] + venues
    self.strat_sor_table["columns"] = cols

    self.strat_sor_table.heading("Stat", text="Stat", anchor="w")
    self.strat_sor_table.column("Stat", width=280, stretch=True, anchor="w")

    for v in venues:
        self.strat_sor_table.heading(v, text=v, anchor="center")
        self.strat_sor_table.column(v, width=120, anchor="center", stretch=True)

    for stat in self._strat_venue_stat_order:
        if not self.strat_sor_table.exists(stat):
            self.strat_sor_table.insert("", "end", iid=stat,
                                        values=(self._strat_venue_stat_labels[stat],))
        else:
            self.strat_sor_table.set(stat, "Stat", self._strat_venue_stat_labels[stat])

    total_notional = sum(d.get("notional", 0.0) for d in self._strat_venue_stats.values())

    for stat in self._strat_venue_stat_order:
        for v in venues:
            d = self._strat_venue_stats.get(v, {})
            txt = "—"
            if stat == "vol_pct":
                used = float(d.get("notional", 0.0))
                pct = (used / total_notional * 100.0) if (total_notional > 0 and np.isfinite(used)) else np.nan
                txt = "—" if not np.isfinite(pct) else f"{_trim(pct, '{:.2f}')}%"
            elif stat == "perf_arrival":
                perf = d.get("perf_arrival_pct", np.nan)
                txt = fmt_pct_or_bp(perf) if (perf is not None and np.isfinite(perf)) else "—"
            elif stat == "twap_order":
                px = d.get("twap_order_px", np.nan)
                txt = fmt_px(px) if np.isfinite(px) else "—"
            elif stat == "twap_mkt":
                px = d.get("twap_mkt_px", np.nan)
                txt = fmt_px(px) if np.isfinite(px) else "—"
            elif stat == "vwap_order":
                px = d.get("vwap_order_px", np.nan)
                txt = fmt_px(px) if np.isfinite(px) else "—"
            elif stat in ("fees", "impact", "slippage", "total_mkt"):
                key_map = {
                    "fees": "fees_usdt",
                    "impact": "impact_usdt",
                    "slippage": "slippage_usdt",
                    "total_mkt": "total_mkt_usdt",
                }
                val = d.get(key_map[stat], np.nan)
                txt = fmt_usd(val) if (val is not None and np.isfinite(val)) else "—"
            try:
                self.strat_sor_table.set(stat, v, txt)
            except Exception:
                pass


def _strat_record_child(
        self,
        venue: str,
        side_or_K,
        price: float | None = None,
        qty_base_or_side: float | str | None = None,
        notional_usdt: float | None = None,
        fees_usdt: float = 0.0,
        impact_usdt: float = 0.0,
        spread_usdt: float = 0.0,
        slippage_usdt: float = 0.0,
        ts: float | None = None,
) -> None:
    """
    Record a single child execution for the running strategy, including
    the full cost decomposition.

    This supports two call styles:

    1) NEW (recommended):
        _strat_record_child(
            venue="binance",
            side="buy" / "sell",
            price=exec_price,
            qty_base=filled_base_qty,
            notional_usdt=filled_notional_usdt,
            fees_usdt=...,
            impact_usdt=...,
            spread_usdt=...,
            slippage_usdt=...,
            ts=...
        )

    2) LEGACY (used by _strat_tick currently):
        _strat_record_child(venue_label, child_K, exec_px, side)

       where:
         - child_K is the child notional in K-USDT (e.g. 5 means 5,000 USDT)
         - we infer:
             notional_usdt = child_K * 1000
             qty_base      = notional_usdt / price
         - all cost terms default to 0.0, and we approximate them here.
    """
    import time

    if ts is None:
        ts = time.time()

    # ----- Normalize arguments depending on call style -----
    if isinstance(side_or_K, str):
        # NEW SIGNATURE:
        #   venue, side, price, qty_base, notional_usdt, ...
        side = side_or_K.lower()
        child_price = float(price or 0.0)
        qty_base = float(qty_base_or_side or 0.0)
        if notional_usdt is None:
            notional_usdt = qty_base * child_price if child_price > 0 else 0.0
        K_child = float(notional_usdt) / 1000.0 if np.isfinite(notional_usdt) else 0.0
    else:
        # LEGACY SIGNATURE:
        #   _strat_record_child(venue_label, child_K, exec_px, side)
        child_K = float(side_or_K or 0.0)
        child_price = float(price or 0.0)
        side = (qty_base_or_side or "buy").lower()
        if notional_usdt is None:
            notional_usdt = child_K * 1000.0
        qty_base = notional_usdt / child_price if child_price > 0 else 0.0
        K_child = float(notional_usdt) / 1000.0 if np.isfinite(notional_usdt) else 0.0

    s = self.current_strat or {}
    start_ts = float(s.get("start_ts", ts))
    t_rel = max(0.0, ts - start_ts)  # time since start (s) – axis for charts

    # ----- If no explicit costs were passed, approximate them -----
    notional = float(notional_usdt or 0.0)
    arrival = getattr(self, "_strat_arrival_mid", None)

    if (fees_usdt == 0.0 and impact_usdt == 0.0 and
            spread_usdt == 0.0 and slippage_usdt == 0.0 and
            notional > 0.0):

        # Fees ≈ 7.5 bps of notional (negative)
        if np.isfinite(notional):
            fees_usdt = -abs(notional * FEE_BPS)
        else:
            fees_usdt = 0.0

        # Slippage vs arrival, with sign convention matching the app
        slippage_usdt = 0.0
        if (arrival and np.isfinite(arrival) and arrival > 0 and
                np.isfinite(child_price) and child_price > 0):
            if side == "buy":
                slipp_rel = (child_price - arrival) / arrival
            else:
                slipp_rel = (arrival - child_price) / arrival
            slippage_usdt = -(slipp_rel * notional)

        # For now we keep impact / spread at 0.0 at the child level
        impact_usdt = 0.0
        spread_usdt = 0.0

    # --- Ensure lists exist -------------------------------------------------
    if not hasattr(self, "_strat_child_execs"):
        self._strat_child_execs: list[dict] = []
    if not hasattr(self, "_strat_execs"):
        # list of (K, price) for VWAP; here K = notional / 1000
        self._strat_execs: list[tuple[float, float]] = []
    if not hasattr(self, "_strat_exec_times"):
        self._strat_exec_times: list[float] = []
    if not hasattr(self, "_strat_exec_prices"):
        self._strat_exec_prices: list[float] = []
    if not hasattr(self, "_strat_exec_unit_vol"):
        # per-child notional in USDT
        self._strat_exec_unit_vol: list[float] = []
    if not hasattr(self, "_strat_exec_cum_vol"):
        # cumulative notional in USDT
        self._strat_exec_cum_vol: list[float] = []
    if not hasattr(self, "_strat_buy_times"):
        self._strat_buy_times: list[float] = []
    if not hasattr(self, "_strat_buy_prices"):
        self._strat_buy_prices: list[float] = []
    if not hasattr(self, "_strat_sell_times"):
        self._strat_sell_times: list[float] = []
    if not hasattr(self, "_strat_sell_prices"):
        self._strat_sell_prices: list[float] = []

    # --- Store detailed record for stats aggregation ------------------------
    rec = {
        "venue": venue,
        "side": side,
        "price": float(child_price),
        "qty_base": float(qty_base),
        "notional_usdt": float(notional_usdt),
        "fees_usdt": float(fees_usdt),
        "impact_usdt": float(impact_usdt),
        "spread_usdt": float(spread_usdt),
        "slippage_usdt": float(slippage_usdt),
        "t_rel": float(t_rel),
    }
    self._strat_child_execs.append(rec)

    # --- Series for VWAP / chart -------------------------------------------
    # Use K = notional / 1000 as "size" for VWAP, consistent with stats.
    K_child = float(notional_usdt) / 1000.0 if np.isfinite(notional_usdt) else 0.0
    if K_child > 0.0 and np.isfinite(child_price) and child_price > 0.0:
        self._strat_execs.append((K_child, float(child_price)))

    self._strat_exec_times.append(t_rel)
    self._strat_exec_prices.append(float(child_price))
    self._strat_exec_unit_vol.append(float(notional_usdt))

    if self._strat_exec_cum_vol:
        self._strat_exec_cum_vol.append(self._strat_exec_cum_vol[-1] + float(notional_usdt))
    else:
        self._strat_exec_cum_vol.append(float(notional_usdt))

    # Buy / sell markers for the price panel
    if side == "buy":
        self._strat_buy_times.append(t_rel)
        self._strat_buy_prices.append(float(child_price))
    else:  # treat anything non-buy as sell
        self._strat_sell_times.append(t_rel)
        self._strat_sell_prices.append(float(child_price))

    # --- Per-venue aggregation for the "Strat — Per-Venue" table -----------
    if not hasattr(self, "_strat_venue_stats"):
        self._strat_venue_stats = {}

    d = self._strat_venue_stats.get(venue)
    if d is None:
        d = {
            "notional": 0.0,
            "vwap_order_num": 0.0,
            "vwap_order_den": 0.0,
            "fees_usdt": 0.0,
            "impact_usdt": 0.0,
            "spread_usdt": 0.0,
            "slippage_usdt": 0.0,
            "total_mkt_usdt": 0.0,
            "perf_arrival_pct": np.nan,
            "twap_order_px": np.nan,
            "twap_mkt_px": np.nan,
            "vwap_order_px": np.nan,
        }
        self._strat_venue_stats[venue] = d

    d["notional"] += float(notional_usdt or 0.0)
    d["vwap_order_num"] += float(notional_usdt or 0.0) * float(child_price)
    d["vwap_order_den"] += float(notional_usdt or 0.0)
    d["fees_usdt"] += float(fees_usdt)
    d["impact_usdt"] += float(impact_usdt)
    d["spread_usdt"] += float(spread_usdt)
    d["slippage_usdt"] += float(slippage_usdt)
    # total_mkt_usdt will be recomputed once we know the full decomposition


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
                    "options": {"defaultType": "spot", "recvWindow": 20000},
                    "timeout": 30000,
                })
                ex.set_sandbox_mode(True)  # paper trading
                ex.retries = 1
                ex.load_markets()
                self.ex_priv = ex
        except Exception as e_priv:
            print("Testnet keys invalid or missing:", e_priv)
            self.ex_priv = None
        # Enable/disable trading buttons depending on private client
        for w in (self.buy_btn, self.sell_btn):
            try:
                w.configure(state=("normal" if self.ex_priv else "disabled"))
            except Exception:
                pass
        return True
    except Exception as e:
        messagebox.showerror("Startup", f"{type(e).__name__}: {e}")
        return False


def _fatal_disable(self):
    for w in (self.base_cb, self.quote_entry, self.buy_btn, self.sell_btn):
        try:
            w.configure(state="disabled")
        except Exception:
            pass


# ---------- REST helpers (public client) ----------
def _rest_ticker_cached(self, sym: str) -> Tuple[Optional[float], Optional[float], Optional[float]]:
    now = int(time.time() * 1000)
    rec = self._rest_cache.get(sym)
    if rec and (now - rec.get("ts", 0) < 300):
        b = rec.get("bid");
        a = rec.get("ask");
        m = rec.get("mid")
        return (b if np.isfinite(b) else None,
                a if np.isfinite(a) else None,
                m if np.isfinite(m) else None)
    try:
        t = self.ex_pub.fetch_ticker(sym)
        bid = float(t.get("bid") or np.nan)
        ask = float(t.get("ask") or np.nan)
        mid = (bid + ask) / 2.0 if np.isfinite(bid) and np.isfinite(ask) and bid > 0 and ask > 0 else np.nan
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
        m = self._mid_now(sym)
        txt = f"{sym}  {fmt_px(m) if (m and np.isfinite(m)) else '—'}"
        # update only the selection chip
        if hasattr(self, "sel_price_chip"):
            self.sel_price_chip.configure(text=txt)
        if m and np.isfinite(m) and m > 0:
            now = time.time()
            self._ui_last_mid[sym] = (float(m), int(now * 1000))
            # If a strategy is running on this symbol, collect samples for mkt TWAP & chart
            if self.current_strat and self.current_strat.get("status") == "Ongoing":
                if self.current_strat.get("sym") == sym:
                    self._strat_mkt_samples.append((now, float(m)))
                    # time axis relative to strat start
                    t0 = float(self.current_strat.get("start_ts", now))
                    self._strat_price_times.append(max(0.0, now - t0))
                    self._strat_price_values.append(float(m))
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
    # Benchmark notional in *inflated* units (100k real → 100M inflated)
    benchmark_notional_usdt = TARGET_START_USDT * LIQ_FACTOR_K

    # This will hold the current value of the theoretical arrival ptf,
    # valued at *current* prices, in inflated units.
    theo_ptf_value = 0.0

    if not self.ex_priv:
        # No private client: dummy display with zeros and static theo column
        for row in self.tree.get_children():
            self.tree.delete(row)

        # USDT row
        self.tree.insert(
            "",
            "end",
            values=("USDT", fmt_qty2(0.0), "1.00", fmt_usd(0.0), fmt_qty2(0.0)),
        )
        # Crypto rows
        for b in ALL_BASES:
            self.tree.insert(
                "",
                "end",
                values=(b, fmt_qty2(0.0), "—", fmt_usd(0.0), "—"),
            )
        total_usdt = 0.0

    else:
        try:
            bal = self.ex_priv.fetch_balance()
        except (RequestTimeout, NetworkError) as e:
            print(f"[WARN] Testnet balance fetch timed out: {e}")
            return  # skip this cycle, keep previous values
        except ExchangeError as e:
            print(f"[WARN] Testnet exchange error: {e}")
            return

        # Clear current rows
        for row in self.tree.get_children():
            self.tree.delete(row)

        total_usdt = 0.0

        # --- Theoretical per-asset notional at arrival (real units) ---------
        # Example: TARGET_START_USDT = 100_000 and len(ALL_BASES) = 10
        # => 10_000 real USDT per asset, i.e. 10M in inflated units.
        num_assets = max(1, len(ALL_BASES))
        per_asset_real = TARGET_START_USDT / float(num_assets)

        # --- USDT row --------------------------------------------------------
        usdt_qty_real = float(bal.get("total", {}).get("USDT") or 0.0)
        usdt_qty_disp = usdt_qty_real * LIQ_FACTOR_K  # inflated qty
        theo_usdt_arrival_disp = 0.0  # in the arrival ptf, all 100k is deployed in the 10 cryptos

        self.tree.insert(
            "",
            "end",
            values=(
                "USDT",
                fmt_qty2(usdt_qty_disp),
                "1.00",
                fmt_usd(usdt_qty_disp),
                fmt_qty2(theo_usdt_arrival_disp),
            ),
        )
        total_usdt += usdt_qty_disp
        # Theo ptf has 0 USDT position, so no contribution to theo_ptf_value from USDT.

        # --- Crypto rows (BTC, ETH, ...) ------------------------------------
        for b in ALL_BASES:
            sym = f"{b}/{QUOTE}"

            # Current real & displayed qty
            qty_real = float(bal.get("total", {}).get(b) or 0.0)
            qty_disp = qty_real * LIQ_FACTOR_K  # inflated qty

            # Current mid
            mid = self._mid_now(sym)

            # Freeze "arrival" mid at first observation and never change it
            if sym not in self.session_open_mid:
                if mid is not None and np.isfinite(mid) and mid > 0.0:
                    self.session_open_mid[sym] = float(mid)

            open_mid = self.session_open_mid.get(sym)

            # PnL vs session OPEN (for the old column text; still useful info)
            if mid is None or not np.isfinite(mid):
                usd_val = 0.0
                pct_str = "—"
            else:
                usd_val = qty_disp * mid  # inflated value
                if open_mid and np.isfinite(open_mid) and open_mid > 0.0:
                    pct_str = fmt_pct_signed((mid / open_mid - 1.0) * 100.0)
                else:
                    pct_str = "—"

            px_str = fmt_px(mid) if (mid is not None and np.isfinite(mid)) else "—"

            # Theo QTY at Arrival (in inflated units), based on frozen arrival mid
            # Real per-asset notional = per_asset_real (e.g. 10,000 USDT)
            # Real theo base qty      = per_asset_real / open_mid
            # Displayed qty           = real theo qty * LIQ_FACTOR_K
            theo_qty_disp_val = 0.0
            if open_mid and np.isfinite(open_mid) and open_mid > 0.0:
                theo_qty_real = per_asset_real / open_mid
                theo_qty_disp_val = theo_qty_real * LIQ_FACTOR_K
                theo_q_display = fmt_qty2(theo_qty_disp_val)
            else:
                theo_q_display = "—"

            # Theo ptf valued at *current* mid
            if (
                    mid is not None
                    and np.isfinite(mid)
                    and mid > 0.0
                    and theo_qty_disp_val > 0.0
            ):
                theo_ptf_value += theo_qty_disp_val * mid

            self.tree.insert(
                "",
                "end",
                values=(
                    b,
                    fmt_qty2(qty_disp),
                    px_str,
                    f"{fmt_usd(usd_val)} ({pct_str})",
                    theo_q_display,
                ),
            )
            total_usdt += usd_val

    # ====== PnL vs Arrival Ptf calculation =================================

    # Store last total for instant reset if needed elsewhere
    self._last_total_usdt = total_usdt
    if self.session_start_value_usdt is None:
        # Kept for compatibility, but no longer used as PnL denominator
        self.session_start_value_usdt = float(total_usdt)

    # Show raw total (still useful as "current mark-to-market" in inflated units)
    self.total_lbl.configure(text=f"Total: {fmt_usd(total_usdt)} USDT")

    # Friction is the cumulative sum of all frictions (negative cost)
    friction = float(self.session_friction_usdt or 0.0)

    # Current ptf value as per your definition:
    #   current_ptf_value = sum(qty * price) - cumulated_friction
    # with friction negative → this is total_usdt - (negative) = total_usdt + |friction|
    current_ptf_value = total_usdt - friction

    # PnL vs Arrival Ptf:
    #   theo_ptf_value is value of the theoretical arrival ptf at *current* prices
    pnl_vs_arrival = current_ptf_value - theo_ptf_value

    # Market component:
    #   market = PnL vs Arrival - friction
    market_part = pnl_vs_arrival - friction

    # All bps are vs the fixed 100k real (100M inflated)
    def _pct_of_benchmark(x: float) -> float:
        return (
            (x / benchmark_notional_usdt * 100.0)
            if (
                    np.isfinite(x)
                    and np.isfinite(benchmark_notional_usdt)
                    and benchmark_notional_usdt > 0.0
            )
            else np.nan
        )

    pnl_pct = _pct_of_benchmark(pnl_vs_arrival)
    mkt_pct = _pct_of_benchmark(market_part)
    fric_pct = _pct_of_benchmark(friction)

    # Color by sign of PnL vs arrival ptf
    style = (
        "StatValueGreen.TLabel"
        if pnl_vs_arrival > 0
        else ("StatValueRed.TLabel" if pnl_vs_arrival < 0 else "PNL.TLabel")
    )

    self.pnl_lbl.configure(
        text=(
            f"PnL vs Arrival Ptf: {fmt_usd(pnl_vs_arrival)} USDT ({fmt_bp_from_pct(pnl_pct)})"
            f"  |  market: {fmt_usd(market_part)} USDT ({fmt_bp_from_pct(mkt_pct)})"
            f"  |  friction: {fmt_usd(friction)} USDT ({fmt_bp_from_pct(fric_pct)})"
        ),
        style=style,
    )


def _reset_pnl_baseline(self):
    """
    Reset the PnL baseline for execution statistics.

    Under the new PnL vs Arrival Ptf logic:
      - The theoretical arrival portfolio is fixed at launch (10k real USDT per asset),
        based on the frozen arrival mid prices (session_open_mid).
      - The only "baseline" we reset here is the cumulative friction, so that from this
        moment onward we start counting transaction costs from zero.

    Effect:
      - self.session_friction_usdt is set to 0.0
      - refresh_balance() is called to recompute:
          * current_ptf_value
          * PnL vs Arrival Ptf
          * market component
          * friction (now 0)
        and to update the PnL label accordingly.
    """
    # Legacy field kept for compatibility, but no longer used in PnL vs Arrival.
    self.session_start_value_usdt = float(self._last_total_usdt or 0.0)

    # Reset cumulative friction (negative cost in inflated USDT)
    self.session_friction_usdt = 0.0

    # Recompute balances and PnL vs Arrival immediately
    try:
        self.refresh_balance()
    except Exception:
        # Soft-fail: in worst case, next heartbeat will recompute it.
        traceback.print_exc()


# ---------- OB helpers ----------
def _pad_levels_to_quote(self, levels: List[Tuple[float, float]], side: str, quote_target: float) -> List[
    Tuple[float, float]]:
    if not levels or quote_target <= 0:
        return levels

    def _covered(ls):
        c = 0.0
        for p, q in ls:
            if p and q and q > 0:
                c += p * q
        return c

    covered = _covered(levels)
    if covered >= quote_target:
        return levels
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
    while covered < quote_target and len(levels) < 5000:
        gap = abs(float(rng.normal(gap_mu, gap_sd)))
        gap = max(gap, max(abs(last_px) * 1e-6, 1e-10))
        px = last_px + gap if side == "buy" else max(last_px - gap, 1e-12)
        q = float(rng.normal(vol_mu, vol_sd))
        if not np.isfinite(q) or q <= 0:
            q = max(vol_mu * 0.3, 1e-9)
        levels.append((px, q))
        covered += px * q
        last_px = px
    return levels


@staticmethod
def _simulate_by_quote(levels: List[Tuple[float, float]], quote_target: float) -> Tuple[float, float, float]:
    return calculate_VWAP(levels, quote_target)


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


# ---------- Exec at Market (kept working) ----------
# ---------- Exec at Market (kept working) ----------
def _place(self, side: str):
    if not self.ex_priv:
        messagebox.showwarning("Trading disabled", "No valid testnet API keys. Market data works without keys.")
        return None

    base = self.base_var.get()
    sym = f"{base}/{QUOTE}"
    t_click = int(time.time() * 1000)
    # Parse input (Entry is K USDT)
    try:
        K = float(self.quote_qty_var.get())  # e.g., 5
        q_quote_display = 1000.0 * K  # what the student *thinks* in USDT (5,000)
        q_quote_real = K  # what we actually send to testnet in USDT (5)
        q_quote_stat = q_quote_display  # internal illusion ×1000 for OB/PNL/etc.
    except Exception:
        messagebox.showwarning("Input", "Quote quantity must be numeric.")
        return None
    if not np.isfinite(q_quote_real) or q_quote_real <= 0:
        messagebox.showwarning("Input", "Quote quantity must be positive.")
        return None

    # Arrival = last price the user saw (from price chip)
    rec = getattr(self, "_ui_last_mid", {}).get(sym)
    if not rec:
        messagebox.showwarning("Price", "No recent displayed price yet.")
        return None
    arrival, _ts_seen = rec
    if not (np.isfinite(arrival) and arrival > 0):
        messagebox.showwarning("Price", "Displayed price is invalid.")
        return None

    wait = self._show_wait("Submitting order…")
    try:
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
        # Slippage cost = (first vs arrival) × inflated notional (negative)
        slippage_usd = np.nan
        if np.isfinite(first_px_sim) and np.isfinite(arrival):
            slipp_rel = ((first_px_sim - arrival) / arrival) if side == "buy" else ((arrival - first_px_sim) / arrival)
            slippage_usd = (-slipp_rel * q_quote_stat) if np.isfinite(slipp_rel) else np.nan
        # Impact cost = (vwap vs first) × inflated notional (negative, adverse)
        impact_usd = np.nan
        if np.isfinite(vwap_sim) and np.isfinite(first_px_sim):
            imp_rel_raw = (vwap_sim - first_px_sim) / first_px_sim
            imp_rel = imp_rel_raw if side == "buy" else (-imp_rel_raw)
            impact_usd = (-imp_rel * q_quote_stat) if np.isfinite(imp_rel) else np.nan
        # Total
        parts = [fees_usdt, impact_usd, spread_usd, slippage_usd]
        mkt_total_usd = float(sum(x for x in parts if (x is not None and np.isfinite(x))))
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
        # q_quote_real is now *x* (not x*1000). We keep using it for the real testnet order.
        cost_str = self._quote_qty_param(sym, q_quote_real)
        if side == "sell":
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
        if status not in ("closed", "canceled") and filled <= 0:
            # no visible fill, but we still keep the simulated costs
            pass

    except Exception as e:
        traceback.print_exc()
        self._close_wait(wait)
        messagebox.showerror("Order", f"{type(e).__name__}: {e}")
        return None
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
    messagebox.showinfo(
        "Execution",
        f"{side.upper()} executed on {sym}\n"
        f"Base exchanged (×1000):  {fmt_qty(filled_base_sim)} {base}\n"
        f"Quote exchanged (×1000): {fmt_usd(q_quote_display)} {QUOTE}"
    )

    # Accumulate session friction
    if np.isfinite(mkt_total_usd):
        self.session_friction_usdt += float(mkt_total_usd)

    # --- Update Stats (right) ---
    self._set_stat("t_first", ts_human)
    self._set_stat("way", side.upper())
    self._update_stats_title(side, mode="Market")
    self._set_stat("exec_base", f"{fmt_qty(filled_base_sim)} {base}  (×1000)")
    self._set_stat("exec_quote", f"{fmt_usd(q_quote_stat)} {QUOTE} (×1000)")
    self._set_stat("slip_ms", f"{int(slip_ms)} ms" if slip_ms is not None else "—")
    self._set_stat("arrival", f"{fmt_px(arrival)} USDT")

    def pct(a, b):
        return ((a / b - 1.0) * 100.0) if (np.isfinite(a) and np.isfinite(b) and b != 0) else np.nan

    f_vs_arr = pct(first_px_sim, arrival)
    l_vs_first = pct(last_px_sim, first_px_sim)
    v_vs_first = pct(vwap_sim, first_px_sim)

    self._set_stat("first_px", f"{fmt_px(first_px_sim)} USDT  |  {fmt_pct_or_bp(f_vs_arr)}")
    self._set_stat("last_px", f"{fmt_px(last_px_sim)} USDT   |  {fmt_pct_or_bp(l_vs_first)}")
    self._set_stat("vwap", f"{fmt_px(vwap_sim)} USDT  |  {fmt_pct_or_bp(v_vs_first)}")

    # components & total
    def pct_of_notional2(x, denom):
        return (x / denom * 100.0) if (np.isfinite(x) and np.isfinite(denom) and denom > 0) else np.nan

    net_quote2 = q_quote_stat
    mkt_total_pct2 = pct_of_notional2(mkt_total_usd, net_quote2)
    fees_pct_net2 = pct_of_notional2(fees_usdt, net_quote2)
    impact_pct_net2 = pct_of_notional2(impact_usd, net_quote2)
    spread_pct_net2 = pct_of_notional2(spread_usd, net_quote2)
    slip_pct_net2 = pct_of_notional2(slippage_usd, net_quote2)

    self._set_stat_signed("mkt_total", f"{fmt_usd(mkt_total_usd)} USDT  |  {fmt_pct_or_bp(mkt_total_pct2)}",
                          positive_green=(np.isfinite(mkt_total_usd) and mkt_total_usd >= 0))
    self._set_stat_signed("fees", f"{fmt_usd(fees_usdt)} USDT  |  {fmt_pct_or_bp(fees_pct_net2)}", positive_green=False)
    self._set_stat_signed("impact", f"{fmt_usd(impact_usd)} USDT  |  {fmt_pct_or_bp(impact_pct_net2)}",
                          positive_green=False)
    self._set_stat_signed("spread", f"{fmt_usd(spread_usd)} USDT  |  {fmt_pct_or_bp(spread_pct_net2)}",
                          positive_green=False)
    self._set_stat_signed("slippage", f"{fmt_usd(slippage_usd)} USDT  |  {fmt_pct_or_bp(slip_pct_net2)}",
                          positive_green=(np.isfinite(slippage_usd) and slippage_usd >= 0))

    # ---- RETURN child stats for strat aggregation (×1000 illusion) ----
    child_stats = {
        "notional_usdt": float(q_quote_stat),
        "fees_usdt": float(fees_usdt) if np.isfinite(fees_usdt) else 0.0,
        "impact_usdt": float(impact_usd) if np.isfinite(impact_usd) else 0.0,
        "spread_usdt": float(spread_usd) if np.isfinite(spread_usd) else 0.0,
        "slippage_usdt": float(slippage_usd) if np.isfinite(slippage_usd) else 0.0,
        "mkt_total_usd": float(mkt_total_usd) if np.isfinite(mkt_total_usd) else 0.0,
    }
    return child_stats


# ---------- Auto-liquidate on startup ----------
# ---------- Auto-liquidate on startup ----------
def _auto_liquidate_on_launch(self):
    try:
        if not self.ex_priv:
            return
        bal = self.ex_priv.fetch_balance()
        totals = bal.get("total", {}) if isinstance(bal, dict) else {}
        # any positive non-USDT balance?
        has_nonusdt = any(
            (k != "USDT") and (float(totals.get(k) or 0.0) > 0.0)
            for k in totals.keys()
        )
        if not has_nonusdt:
            # even if nothing to liquidate, we STILL want to align baseline
            # to a clean TARGET_START_USDT via init_ptf_adjust.
            wait = self._show_wait("Adjusting initial portfolio…")

            def _runner_adjust_only():
                try:
                    async def _do_adjust():
                        await self._init_ptf_adjust_async()

                    asyncio.run(_do_adjust())
                finally:
                    self.after(0, self.refresh_balance)
                    self.after(0, self._reset_pnl_baseline)
                    self.after(0, lambda: self._close_wait(wait))

            import threading
            threading.Thread(target=_runner_adjust_only, daemon=True).start()
            return

        # There ARE non-USDT balances → first liquidate them to USDT, then adjust.
        wait = self._show_wait("Submitting liquidation…")

        def _runner():
            try:
                async def _do_all():
                    # 1) Liquidate TOP10 assets to USDT
                    await self._liquidate_all_async()
                    # 2) Adjust real USDT balance to TARGET_START_USDT
                    await self._init_ptf_adjust_async()

                asyncio.run(_do_all())
            finally:
                # All UI updates must be back on Tk main thread
                self.after(0, self.refresh_balance)
                self.after(0, self._reset_pnl_baseline)
                self.after(0, lambda: self._close_wait(wait))

        import threading
        threading.Thread(target=_runner, daemon=True).start()

    except Exception:
        # Soft-fail; don't block UI if testnet is unavailable
        pass


# ---------- Liquidation ----------
async def _sell_asset_async(self, base: str):
    try:
        if base == "USDT":
            return
        sym = f"{base}/{QUOTE}"
        bal = self.ex_priv.fetch_balance()
        amt = float(bal.get("total", {}).get(base) or 0.0)
        if amt <= 0:
            return
        amt = float(self.ex_priv.amount_to_precision(sym, amt))
        await asyncio.to_thread(self.ex_priv.create_order, sym, "market", "sell", amt)
    except Exception as e:
        print(f"[Liquidate] {base}: {e}")


def _liquidate_all(self):
    if not self.ex_priv:
        messagebox.showwarning("Trading disabled", "No valid testnet API keys.")
        return

    wait = self._show_wait("Submitting liquidation…")

    def _runner():
        try:
            # Pure async logic (no Tk calls inside)
            asyncio.run(self._liquidate_all_async())
            # Once done, schedule UI updates on the main Tk thread
            self.after(0, self.refresh_balance)
            self.after(
                0,
                lambda: messagebox.showinfo(
                    "Liquidation",
                    "All positions liquidated to USDT (async parallel).",
                ),
            )
        finally:
            # Close the wait dialog on the main thread
            self.after(0, lambda: self._close_wait(wait))

    import threading
    threading.Thread(target=_runner, daemon=True).start()


async def _liquidate_all_async(self):
    bases_to_sell = [b for b in ALL_BASES if b != "USDT"]
    tasks = [self._sell_asset_async(b) for b in bases_to_sell]
    await asyncio.gather(*tasks)


async def _init_ptf_adjust_async(self):
    """
    After auto-liquidation, nudge the *real* testnet USDT balance so that:

        USDT_real ≈ TARGET_START_USDT

    With LIQ_FACTOR_K = 1000, this corresponds to 100M in the inflated UI.
    - If USDT_real > TARGET_START_USDT: buy a 'parking' asset (not in ALL_BASES)
      with the excess USDT.
    - If USDT_real < TARGET_START_USDT: sell that parking asset (if held)
      to bring USDT closer to the target.
    """
    if not self.ex_priv:
        return

    try:
        bal = self.ex_priv.fetch_balance()
        totals = bal.get("total", {}) if isinstance(bal, dict) else {}
        cur_usdt = float(totals.get(QUOTE) or 0.0)
    except Exception as e:
        print("[init_ptf_adjust] balance error:", e)
        return

    target = float(TARGET_START_USDT)
    if not np.isfinite(cur_usdt) or not np.isfinite(target) or target <= 0:
        return

    diff = cur_usdt - target

    # If we are already within 1 USDT of the target, don't bother.
    if abs(diff) < 1.0:
        return

    # --- Helper: pick a "parking" asset BASE where BASE/USDT exists
    #     and BASE is not in ALL_BASES (so it won't appear in your balance table).
    def _pick_parking_asset() -> Optional[str]:
        try:
            markets = getattr(self.ex_priv, "markets", None) or {}
            for symbol in markets.keys():
                if not isinstance(symbol, str):
                    continue
                if not symbol.endswith(f"/{QUOTE}"):
                    continue
                base_sym = symbol.split("/")[0]
                if base_sym in ALL_BASES or base_sym == QUOTE:
                    continue
                return base_sym
        except Exception:
            pass
        return None

    parking_base = _pick_parking_asset()
    if not parking_base:
        print("[init_ptf_adjust] no parking asset found")
        return

    sym = f"{parking_base}/{QUOTE}"
    px = self._mid_now(sym)
    if not (px and np.isfinite(px) and px > 0):
        print(f"[init_ptf_adjust] no usable mid price for {sym}")
        return

    try:
        if diff > 0:
            # We have MORE USDT than target → spend the excess on parking_base.
            spend = diff  # in real USDT units
            try:
                spend_prec = float(self.ex_priv.cost_to_precision(sym, spend))
            except Exception:
                spend_prec = float(spend)
            if spend_prec <= 0:
                return
            await asyncio.to_thread(
                self.ex_priv.create_order,
                sym,
                "market",
                "buy",
                None,
                None,
                {"quoteOrderQty": spend_prec},
            )
        else:
            # We have LESS USDT than target → sell parking_base to raise USDT.
            need = -diff  # how many USDT we want to add
            amt_have = float(totals.get(parking_base) or 0.0)
            if amt_have <= 0:
                # Nothing to sell, nothing more we can do.
                return

            base_to_sell = min(amt_have, need / px)
            try:
                base_prec = float(self.ex_priv.amount_to_precision(sym, base_to_sell))
            except Exception:
                base_prec = float(base_to_sell)
            if base_prec <= 0:
                return

            await asyncio.to_thread(
                self.ex_priv.create_order,
                sym,
                "market",
                "sell",
                base_prec,
            )
    except Exception as e:
        print("[init_ptf_adjust] order error:", e)
        return


# ---------- Placeholders for Parts 4 & 5 ----------
# ---------- SOR execution ----------
def _get_pub_client(self, venue: str) -> Optional[ccxt.Exchange]:
    try:
        if venue in self._pub_clients:
            return self._pub_clients[venue]
        cls = getattr(ccxt, venue, None)
        if cls is None:
            return None
        ex = cls({"enableRateLimit": True, "options": {"defaultType": "spot"}, "timeout": 20000})
        ex.load_markets()
        self._pub_clients[venue] = ex
        return ex
    except Exception:
        return None


async def _fetch_ob_once(self, venue: str, symbol: str, limit: int = 100):
    """Fetch OB for a venue with a hard ~2s cap; return dict with error on timeout."""
    start = int(time.time() * 1000)
    ex = self._get_pub_client(venue)
    if ex is None or symbol not in getattr(ex, "markets", {}):
        return {"venue": venue, "error": "symbol/venue unavailable"}
    try:
        # HARD CAP SHORTENED: 10.0 -> 2.0 seconds
        ob = await asyncio.wait_for(
            asyncio.to_thread(ex.fetch_order_book, symbol, limit),
            timeout=2.0
        )
        end = int(time.time() * 1000)
        return {
            "venue": venue,
            "bids": [(float(p), float(q)) for p, q in ob.get("bids", [])],
            "asks": [(float(p), float(q)) for p, q in ob.get("asks", [])],
            "bestBid": float(ob["bids"][0][0]) if ob.get("bids") else np.nan,
            "bestAsk": float(ob["asks"][0][0]) if ob.get("asks") else np.nan,
            "snapshot_ms": end - start,
        }
    except asyncio.TimeoutError:
        return {"venue": venue, "error": "timeout>2s"}
    except Exception as e:
        return {"venue": venue, "error": str(e)}


def _sor_clear_table(self):
    """Clear all venue columns, keep the left 'Stat' labels intact."""
    # Reset to only the Stat column
    self.sor_table["columns"] = ["Stat"]
    self.sor_table.heading("Stat", text="Stat", anchor="w")
    self.sor_table.column("Stat", width=320, stretch=True, anchor="w")
    # Ensure each row shows its left label
    for stat in self._sor_stats_order:
        if not self.sor_table.exists(stat):
            self.sor_table.insert("", "end", iid=stat, values=(self._sor_stat_labels[stat],))
        else:
            self.sor_table.set(stat, "Stat", self._sor_stat_labels[stat])


def _sor_set_table_columns(self, venues: List[str]):
    # Build column list
    cols = ["Stat"] + venues
    self.sor_table["columns"] = cols

    # Reset 'Stat' heading/column
    self.sor_table.heading("Stat", text="Stat", anchor="w")
    self.sor_table.column("Stat", width=320, stretch=True, anchor="w")

    # Headings for venues
    for v in venues:
        self.sor_table.heading(v, text=v)
        # start with a sane min; will auto-grow below
        self.sor_table.column(v, width=120, anchor="center", stretch=True)

    # Ensure each row has label in first cell
    for stat in self._sor_stats_order:
        if not self.sor_table.exists(stat):
            self.sor_table.insert("", "end", iid=stat, values=(self._sor_stat_labels[stat],))
        else:
            self.sor_table.set(stat, "Stat", self._sor_stat_labels[stat])

    # Auto-fit: compute simple width from the longest displayed string per column
    try:
        import tkinter.font as tkfont
        f = tkfont.nametofont("TkDefaultFont")
        char_w = max(f.measure("0"), 6)  # fallback
        # include header text
        longest = {c: len(c) for c in cols}
        for stat in self._sor_stats_order:
            for v in venues:
                txt = self.sor_table.set(stat, v)
                longest[v] = max(longest.get(v, 0), len(str(txt)))
        # apply width with padding
        for v in venues:
            px = int(longest.get(v, 12) * (char_w * 0.85)) + 28
            self.sor_table.column(v, width=max(120, min(px, 260)), stretch=True)
    except Exception:
        # keep the defaults if measuring fails
        pass


def _sor_fill_table(self, venues: List[str], per_venue: Dict[str, Dict[str, float]]):
    self._sor_set_table_columns(venues)
    for stat in self._sor_stats_order:
        for v in venues:
            val = per_venue.get(v, {}).get(stat)
            if stat.endswith("_ms"):
                s = "—" if val is None or not np.isfinite(val) else f"{int(val)} ms"
            elif stat.endswith("_usdt"):
                s = fmt_usd(val) if (val is not None and np.isfinite(val)) else "—"
            elif stat == "vol_pct":
                s = "—" if val is None or not np.isfinite(val) else f"{_trim(float(val), '{:.2f}')}%"
            else:
                # relative percentages/bp for first/last/vwap vs ref
                s = fmt_pct_or_bp(val) if (val is not None and np.isfinite(val)) else "—"
            try:
                self.sor_table.set(stat, v, s)
            except Exception:
                pass


def _sor_execute(self, side: str):
    base = self.base_var.get()
    sym = f"{base}/{QUOTE}"
    chosen = [v for v, var in self.venue_vars.items() if var.get()]
    if not chosen:
        messagebox.showwarning("SOR", "Select at least one venue.")
        self._sor_clear_table()
        return

    # Arrival = last mid shown on selection chip
    rec = getattr(self, "_ui_last_mid", {}).get(sym)
    if not rec:
        messagebox.showwarning("SOR", "No recent displayed price yet.")
        self._sor_clear_table()
        return
    arrival, _ = rec
    if not (np.isfinite(arrival) and arrival > 0):
        messagebox.showwarning("SOR", "Displayed price is invalid.")
        self._sor_clear_table()
        return

    # Parse K -> real paper order in USDT, simulation uses ×1000
    try:
        K = float(self.quote_qty_var.get())
    except Exception:
        messagebox.showwarning("Input", "Quote quantity must be numeric.")
        self._sor_clear_table()
        return
    if not np.isfinite(K) or K <= 0:
        messagebox.showwarning("Input", "Quote quantity must be positive.")
        self._sor_clear_table()
        return
    q_quote_real = K
    q_quote_sim = 1000.0 * K

    # Private client required for the eventual paper order
    if not self.ex_priv:
        messagebox.showwarning("Trading disabled", "No valid testnet API keys.")
        self._sor_clear_table()
        return

    # Quick balance checks up front
    try:
        bal = self.ex_priv.fetch_balance()
    except Exception as e:
        messagebox.showerror("SOR", f"Balance error: {e}")
        self._sor_clear_table()
        return
    usdt_tot = float(bal.get("total", {}).get(QUOTE) or 0.0)
    base_tot = float(bal.get("total", {}).get(base) or 0.0)
    if side == "buy" and usdt_tot < q_quote_real:
        messagebox.showwarning("SOR", "Insufficient USDT to buy.")
        self._sor_clear_table()
        return
    if side == "sell" and base_tot <= 0.0:
        messagebox.showwarning("SOR", f"Insufficient {base} to sell.")
        self._sor_clear_table()
        return

    # === SOR flow: take snapshots FIRST, then decide whether to place order ===
    wait = self._show_wait("Taking venue snapshots…")
    t_click = int(time.time() * 1000)

    async def _snapshot_then_maybe_order():
        try:
            snaps = await asyncio.gather(*[self._fetch_ob_once(v, sym, limit=100) for v in chosen])
        except Exception:
            snaps = []

        ok_venues = [s.get("venue") for s in snaps if (s and not s.get("error"))]

        if not ok_venues:
            # No snapshot within 10s → executed volume = 0, NO ORDER SENT
            self._sor_clear_table()
            self._update_stats_title(side, mode="SOR")
            self._set_stat("t_first", "—")
            self._set_stat("way", f"{side.upper()} (SOR)")
            self._set_stat("exec_base", f"{fmt_qty(0.0)} {base}  (×1000)")
            self._set_stat("exec_quote", f"{fmt_usd(0.0)} {QUOTE} (×1000)")
            self._set_stat("slip_ms", "—")
            self._set_stat("arrival", f"{fmt_px(arrival)} USDT")
            self._set_stat("first_px", "—")
            self._set_stat("last_px", "—")
            self._set_stat("vwap", "—")
            self._set_stat_signed("mkt_total", "0 USDT  |  +0.00%", positive_green=True)
            self._set_stat_signed("fees", "0 USDT  |  +0.00%", positive_green=True)
            self._set_stat_signed("impact", "0 USDT  |  +0.00%", positive_green=True)
            self._set_stat_signed("spread", "0 USDT  |  +0.00%", positive_green=True)
            self._set_stat_signed("slippage", "0 USDT  |  +0.00%", positive_green=True)
            self._close_wait(wait)
            messagebox.showwarning("SOR", "No venue responded within 10s — no order sent.")
            return

        # -------- Build aggregated book + per-venue first-vs-arrival --------
        agg = []  # ("ask"/"bid", px, qty, venue)
        per_venue = {v: {} for v in chosen}

        for s in snaps:
            v = s.get("venue")
            if s.get("error"):
                per_venue[v]["slippage_ms"] = np.nan
                continue

            per_venue[v]["slippage_ms"] = float(s.get("snapshot_ms") or np.nan)
            bids = s.get("bids") or []
            asks = s.get("asks") or []

            if side == "buy":
                touch = (asks[0][0] if asks else np.nan)
                rel_first = (((touch / arrival) - 1.0) * 100.0) if (
                            np.isfinite(touch) and np.isfinite(arrival) and arrival > 0) else np.nan
                per_venue[v]["first_vs_arrival"] = rel_first
                for p, q in asks:
                    agg.append(("ask", float(p), float(q), v))
            else:
                touch = (bids[0][0] if bids else np.nan)
                rel_first = (((arrival / touch) - 1.0) * 100.0) if (
                            np.isfinite(touch) and np.isfinite(arrival) and touch > 0) else np.nan
                per_venue[v]["first_vs_arrival"] = rel_first
                for p, q in bids:
                    agg.append(("bid", float(p), float(q), v))

        agg.sort(key=(lambda x: x[1]) if side == "buy" else (lambda x: -x[1]))

        # -------- Walk aggregated book; attribute fills per venue --------
        remaining = q_quote_sim
        venue_fills_quote = {v: 0.0 for v in chosen}
        venue_first_px = {v: None for v in chosen}
        venue_last_px = {v: None for v in chosen}
        venue_vwap_num = {v: 0.0 for v in chosen}
        venue_vwap_den = {v: 0.0 for v in chosen}

        global_first_px = None
        global_last_px = None
        global_vwap_num = 0.0
        global_vwap_den = 0.0

        i = 0
        while i < len(agg) and remaining > 0:
            _kind, px, qty, v = agg[i];
            i += 1
            if px <= 0 or qty <= 0:
                continue
            quote_cap = qty * px
            take_quote = min(remaining, quote_cap)
            if take_quote <= 0:
                continue
            take_base = take_quote / px

            if global_first_px is None:
                global_first_px = px
            global_last_px = px
            global_vwap_num += take_base * px
            global_vwap_den += take_base

            venue_fills_quote[v] += take_quote
            venue_vwap_num[v] += take_base * px
            venue_vwap_den[v] += take_base
            if venue_first_px[v] is None:
                venue_first_px[v] = px
            venue_last_px[v] = px

            remaining -= take_quote

        # If not enough depth, pad synthetically (not visible, no costs)
        venues_all = chosen[:]
        if remaining > 0:
            pad_start = global_last_px if (global_last_px is not None and np.isfinite(global_last_px)) else arrival
            step = max(abs(pad_start) * 1e-4, 1e-4)
            px = pad_start
            synthetic_used_quote = 0.0
            while remaining > 0 and synthetic_used_quote < q_quote_sim and len(agg) < 4000:
                px = px + step if side == "buy" else max(px - step, 1e-12)
                q_base = max(remaining / px, 1.0)
                take_quote = min(remaining, q_base * px)
                take_base = take_quote / px

                if global_first_px is None:
                    global_first_px = px
                global_last_px = px
                global_vwap_num += take_base * px
                global_vwap_den += take_base

                synthetic_used_quote += take_quote
                remaining -= take_quote
            SYN = "(synthetic)"
            if SYN not in per_venue:
                per_venue[SYN] = {}
            venue_fills_quote[SYN] = synthetic_used_quote
            venues_all.append(SYN)

        # -------- Per-venue stats + totals (exclude synthetic from costs) --------
        sum_fees = sum_impact = sum_spread = sum_slippage = 0.0
        for v in venues_all:
            used_q = float(venue_fills_quote.get(v, 0.0))
            if v == "(synthetic)" or used_q <= 0.0:
                per_venue[v].update({
                    "last_vs_first": np.nan,
                    "vwap_vs_first": np.nan,
                    "fees_usdt": 0.0,
                    "impact_usdt": 0.0,
                    "spread_usdt": np.nan,
                    "slippage_usdt": 0.0 if v == "(synthetic)" else np.nan,
                    "total_mkt_usdt": 0.0,
                })
                continue

            fpx = float(venue_first_px.get(v) or np.nan)
            lpx = float(venue_last_px.get(v) or np.nan)
            vden = float(venue_vwap_den.get(v, 0.0) or 0.0)
            vnum = float(venue_vwap_num.get(v, 0.0) or 0.0)
            vwap = (vnum / vden) if vden > 0.0 else np.nan

            last_vs_first = ((lpx / fpx) - 1.0) * 100.0 if (
                        np.isfinite(lpx) and np.isfinite(fpx) and fpx > 0.0) else np.nan
            vwap_vs_first = ((vwap / fpx) - 1.0) * 100.0 if (
                        np.isfinite(vwap) and np.isfinite(fpx) and fpx > 0.0) else np.nan

            fees_usdt = -abs(used_q * FEE_BPS)

            sx = next((sx for sx in snaps if sx.get("venue") == v and not sx.get("error")), None)
            if sx and np.isfinite(sx.get("bestBid")) and np.isfinite(sx.get("bestAsk")) and sx["bestBid"] > 0 and sx[
                "bestAsk"] > 0:
                mid = (sx["bestAsk"] + sx["bestBid"]) / 2.0
                rel_spread = (sx["bestAsk"] - sx["bestBid"]) / mid
                spread_usdt = -(rel_spread * used_q)
            else:
                spread_usdt = np.nan

            if np.isfinite(fpx) and np.isfinite(arrival) and arrival > 0:
                slipp_rel = ((fpx - arrival) / arrival) if side == "buy" else ((arrival - fpx) / arrival)
                slippage_usdt = -(slipp_rel * used_q)
            else:
                slippage_usdt = np.nan

            if np.isfinite(vwap) and np.isfinite(fpx) and fpx > 0:
                imp_raw = (vwap - fpx) / fpx
                imp_rel = imp_raw if side == "buy" else (-imp_raw)
                impact_usdt = -(imp_rel * used_q)
            else:
                impact_usdt = np.nan

            parts = [fees_usdt, impact_usdt, spread_usdt, slippage_usdt]
            total_mkt = float(sum(x for x in parts if (x is not None and np.isfinite(x))))

            per_venue[v].update({
                "last_vs_first": last_vs_first,
                "vwap_vs_first": vwap_vs_first,
                "fees_usdt": fees_usdt,
                "impact_usdt": impact_usdt,
                "spread_usdt": spread_usdt,
                "slippage_usdt": slippage_usdt,
                "total_mkt_usdt": total_mkt,
            })

            if np.isfinite(fees_usdt):     sum_fees += fees_usdt
            if np.isfinite(impact_usdt):   sum_impact += impact_usdt
            if np.isfinite(spread_usdt):   sum_spread += spread_usdt
            if np.isfinite(slippage_usdt): sum_slippage += slippage_usdt

        sum_total = float(sum(x for x in (sum_fees, sum_impact, sum_spread, sum_slippage) if np.isfinite(x)))

        display_venues = [v for v in venues_all if v != "(synthetic)"]
        display_total_quote = sum(float(venue_fills_quote.get(v, 0.0)) for v in display_venues)
        for v in display_venues:
            used_q = float(venue_fills_quote.get(v, 0.0))
            vol_pct = (used_q / display_total_quote * 100.0) if (np.isfinite(used_q) and np.isfinite(
                display_total_quote) and display_total_quote > 0) else np.nan
            per_venue[v]["vol_pct"] = vol_pct

        # Fill the bottom table with the snapshot-based simulation
        self._sor_fill_table(display_venues, per_venue)

        # ---------- Now place the REAL paper order ----------
        cost_str = self._quote_qty_param(sym, q_quote_real)
        try:
            if side == "sell":
                amt_real = q_quote_real / (arrival or 1.0)
                amt_real = float(self.ex_priv.amount_to_precision(sym, amt_real))
                order = self.ex_priv.create_order(sym, "market", "sell", amt_real)
            else:
                order = self.ex_priv.create_order(sym, "market", "buy", None, None, {"quoteOrderQty": cost_str})
        except Exception as e:
            # If the order fails, we keep the snapshot results but mark timing as "—"
            self._close_wait(wait)
            messagebox.showerror("SOR", f"Order failed after snapshots: {e}")
            return

        # First fill time for slippage (ms)
        def _extract_first_fill_ms(payload: dict):
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

        info_full = order.get("info") if isinstance(order, dict) else {}
        t_first_ms = _extract_first_fill_ms(info_full)
        if t_first_ms is None:
            t_first_ms = order.get("timestamp") if isinstance(order.get("timestamp"), (int, float)) else None
        slip_ms = (int(t_first_ms) - t_click) if (t_first_ms is not None) else None
        ts_human = (time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(int(t_first_ms) / 1000))
                    if t_first_ms is not None else "—")

        # Global deltas & right panel
        global_vwap = (global_vwap_num / global_vwap_den) if global_vwap_den > 0 else np.nan

        def rel(a, b):
            try:
                fa = float(a);
                fb = float(b)
                if not (np.isfinite(fa) and np.isfinite(fb) and fb > 0.0): return np.nan
                return (fa / fb - 1.0) * 100.0
            except Exception:
                return np.nan

        first_vs_arr = rel(global_first_px, arrival)
        last_vs_first = rel(global_last_px, global_first_px)
        vwap_vs_first = rel(global_vwap, global_first_px)

        self._update_stats_title(side, mode="SOR")
        self._set_stat("t_first", ts_human)
        self._set_stat("way", f"{side.upper()} (SOR)")
        self._set_stat("exec_base", f"{fmt_qty(global_vwap_den)} {base}  (×1000)")
        self._set_stat("exec_quote", f"{fmt_usd(q_quote_sim)} {QUOTE} (×1000)")
        self._set_stat("slip_ms", f"{int(slip_ms)} ms" if slip_ms is not None else "—")
        self._set_stat("arrival", f"{fmt_px(arrival)} USDT")
        self._set_stat("first_px", f"{fmt_px(global_first_px)} USDT  |  {fmt_pct_or_bp(first_vs_arr)}")
        self._set_stat("last_px", f"{fmt_px(global_last_px)} USDT   |  {fmt_pct_or_bp(last_vs_first)}")
        self._set_stat("vwap", f"{fmt_px(global_vwap)} USDT     |  {fmt_pct_or_bp(vwap_vs_first)}")

        def pct_of_notional(x, denom):
            return (x / denom * 100.0) if (np.isfinite(x) and np.isfinite(denom) and denom > 0) else np.nan

        mkt_total = float(sum(x for x in (sum_fees, sum_impact, sum_spread, sum_slippage) if np.isfinite(x)))
        self._set_stat_signed("mkt_total",
                              f"{fmt_usd(mkt_total)} USDT  |  {fmt_pct_or_bp(pct_of_notional(mkt_total, q_quote_sim))}",
                              positive_green=(np.isfinite(mkt_total) and mkt_total >= 0))
        self._set_stat_signed("fees",
                              f"{fmt_usd(sum_fees)} USDT   |  {fmt_pct_or_bp(pct_of_notional(sum_fees, q_quote_sim))}",
                              positive_green=False)
        self._set_stat_signed("impact",
                              f"{fmt_usd(sum_impact)} USDT |  {fmt_pct_or_bp(pct_of_notional(sum_impact, q_quote_sim))}",
                              positive_green=False)
        self._set_stat_signed("spread",
                              f"{fmt_usd(sum_spread)} USDT |  {fmt_pct_or_bp(pct_of_notional(sum_spread, q_quote_sim))}",
                              positive_green=False)
        self._set_stat_signed("slippage",
                              f"{fmt_usd(sum_slippage)} USDT | {fmt_pct_or_bp(pct_of_notional(sum_slippage, q_quote_sim))}",
                              positive_green=(np.isfinite(sum_slippage) and sum_slippage >= 0))

        if np.isfinite(mkt_total):
            self.session_friction_usdt += float(mkt_total)

        self.refresh_balance()
        self._close_wait(wait)

    import threading
    threading.Thread(target=lambda: asyncio.run(_snapshot_then_maybe_order()), daemon=True).start()


def _placeholder_sor_buy(self):
    self._sor_execute("buy")


def _strat_build_schedule(self, name: str, total_K: float, num_buckets: int) -> List[float]:
    """
    Build a simple schedule in *K units* for the chosen strategy.

    total_K      : total order size in K USDT (same units as quote_qty_var)
    num_buckets  : number of time buckets

    TWAP:        equal size per bucket
    VWAP:        U-shaped weights (more at start & end as a toy "volume curve")
    IS:          choose best among {front-loaded, TWAP, back-loaded}
                  using toy impact + risk cost:
                    Impact ~ sum q_i^2
                    Risk   ~ sum Inventory_i^2 (remaining inv before bucket i)
    """
    num_buckets = max(1, int(num_buckets))
    if total_K <= 0 or num_buckets <= 0:
        return [0.0] * max(1, num_buckets)

    def _normalize(weights):
        s = sum(weights)
        if s <= 0:
            return [total_K / num_buckets] * num_buckets
        return [total_K * w / s for w in weights]

    name = (name or "").lower()

    # ---- TWAP baseline ----
    if name == "twap":
        return [total_K / num_buckets] * num_buckets

    # ---- Simple VWAP (U-shaped toy volume curve) ----
    if name == "vwap":
        # More volume at start/end, less in the middle
        mid = (num_buckets - 1) / 2.0
        weights = []
        for i in range(num_buckets):
            d = abs(i - mid)
            # Higher weight near extremes, minimum in the centre
            weights.append(1.0 + 0.5 * d)
        return _normalize(weights)

    # ---- Implementation Shortfall: choose best among 3 candidate shapes ----
    # Candidates in *weights* (still in arbitrary units; we scale later):
    #   front-loaded: bigger at start
    #   twap:        flat
    #   back-loaded: bigger at end
    weights_twap = [1.0] * num_buckets
    weights_front = [float(num_buckets - i) for i in range(num_buckets)]
    weights_back = [float(i + 1) for i in range(num_buckets)]

    candidates = {
        "front": _normalize(weights_front),
        "twap": _normalize(weights_twap),
        "back": _normalize(weights_back),
    }

    # Toy parameters for costs (impact & risk); only ranking matters
    lam = 1.0  # impact weight
    gam = 1.0  # risk weight

    def _cost(schedule: List[float]) -> float:
        # Impact ~ sum q_i^2
        impact = sum(q * q for q in schedule)
        # Risk  ~ sum Inv_i^2, where Inv_i is remaining inventory before bucket i
        inv = total_K
        risk = 0.0
        for q in schedule:
            risk += inv * inv
            inv -= q
        return lam * impact + gam * risk

    best_name = None
    best_sched = None
    best_cost = None
    for cand_name, sched in candidates.items():
        c = _cost(sched)
        if best_cost is None or c < best_cost:
            best_cost = c
            best_name = cand_name
            best_sched = sched

    # For transparency: you could store best_name into self.current_strat if needed.
    return best_sched or ([total_K / num_buckets] * num_buckets)


def _start_strat(self, side: str):
    """
    Launch TWAP / VWAP / IS strategy.

    - Uses current Base, Quote Qty (K USDT), Duration, Sub-Orders/min, Use SOR
    - The *shape* of the child volumes is delegated to the lab functions:
        twap_next_child, vwap_next_child, is_next_child
    - Each bucket:
        * compute child_K via the chosen strategy function
        * set quote_qty_var to child_K
        * call _place (Market) or _sor_execute (SOR)
    """
    side = (side or "").lower()
    if side not in ("buy", "sell"):
        messagebox.showwarning("Strat", "Invalid side for strategy.")
        return

    if self.current_strat and self.current_strat.get("status") == "Ongoing":
        messagebox.showwarning("Strat", "A strategy is already running. Cancel it first.")
        return

    # Parse user inputs
    try:
        total_K = float(self.quote_qty_var.get())
    except Exception:
        messagebox.showwarning("Strat", "Quote quantity (K USDT) must be numeric.")
        return
    if not np.isfinite(total_K) or total_K <= 0:
        messagebox.showwarning("Strat", "Quote quantity (K USDT) must be positive.")
        return

    try:
        duration_min = float(self.duration_var.get())
    except Exception:
        messagebox.showwarning("Strat", "Duration (min) must be numeric.")
        return
    if not np.isfinite(duration_min) or duration_min <= 0:
        messagebox.showwarning("Strat", "Duration (min) must be positive.")
        return

    try:
        sub_per_min = int(self.suborders_per_min_var.get())
    except Exception:
        messagebox.showwarning("Strat", "Sub-Orders/min must be integer.")
        return
    sub_per_min = max(1, sub_per_min)

    base = self.base_var.get()
    sym = f"{base}/{QUOTE}"

    # Arrival mid for perf vs arrival
    arrival = self._mid_now(sym)
    if not (arrival and np.isfinite(arrival) and arrival > 0):
        messagebox.showwarning("Strat", "No valid mid price for current symbol.")
        return

    # Timing
    bucket_seconds = max(1.0, 60.0 / float(sub_per_min))
    total_seconds = duration_min * 60.0

    strat_name = self.strategy_var.get()

    # Reset exec history, per-venue stats, market samples, chart series
    self._strat_execs = []
    self._strat_child_execs = []
    self._strat_venue_stats = {}
    self._strat_mkt_samples = []
    self._strat_price_times = []
    self._strat_price_values = []
    self._strat_exec_times = []
    self._strat_exec_prices = []
    self._strat_exec_unit_vol = []
    self._strat_exec_cum_vol = []
    self._strat_exec_cum_notional = 0.0

    # Strategy state
    now = time.time()
    self.current_strat = {
        "name": strat_name,
        "side": side,
        "base": base,
        "sym": sym,
        "use_sor": bool(self.use_sor_var.get()),
        "total_K": total_K,
        "remaining_K": total_K,
        "bucket_seconds": bucket_seconds,
        "duration_sec": total_seconds,
        "start_ts": now,
        "next_idx": 0,
        "status": "Ongoing",
    }
    self._strat_arrival_mid = float(arrival)

    # Reset progress bar & stats
    self.strat_progress.configure(value=0)
    self._strat_update_stats()
    self._strat_update_venue_table()
    self._update_strat_chart()

    # Kick the first bucket
    self.after(0, self._strat_tick)


def _cancel_strat(self):
    """User cancels the running strategy."""
    # Only react if a strategy is actually running
    if not self.current_strat:
        return
    if self.current_strat.get("status") != "Ongoing":
        return

    # Mark as cancelled and zero out remaining volume
    self.current_strat["status"] = "Cancelled"
    self.current_strat["remaining_K"] = 0.0

    # Empty progress bar
    try:
        self.strat_progress.configure(value=0)
    except Exception:
        pass

    # Refresh stats panel
    self._strat_update_stats()

    # Inform the user
    messagebox.showinfo(
        "Strategy cancelled",
        "The execution strategy has been cancelled.\n\n"
        "No further child orders will be sent."
    )


def _strat_tick(self):
    """
    One bucket of the strategy:
      - ask the relevant strategy function (TWAP/VWAP/IS) for the child volume
        + a 'finished' flag
      - send child order (Market or SOR)
      - update remaining K / progress bar
      - if finished=True or no remaining, stop and show a summary popup
      - otherwise reschedule next bucket
    """
    if not self.current_strat:
        return
    if self.current_strat.get("status") != "Ongoing":
        return

    s = self.current_strat
    idx = int(s.get("next_idx", 0))

    remaining_K = float(s.get("remaining_K", 0.0))
    if remaining_K <= 0.0:
        self.current_strat["status"] = "Completed"
        self._strat_update_stats()
        self._strat_update_venue_table()
        self._update_strat_chart()
        return

    # --- Choose strategy-specific child volume (in K) + finished flag ---
    strat_name = (s.get("name") or "").lower()
    if strat_name == "twap":
        child_K, finished_flag = self._twap_next_child()
    elif strat_name == "vwap":
        child_K, finished_flag = self._vwap_next_child()
    else:
        # default: Implementation Shortfall
        child_K, finished_flag = self._is_next_child()

    # Numerical safety: child_K cannot exceed remaining_K
    if child_K > remaining_K:
        child_K = remaining_K

    # If this bucket is effectively zero and not finished, skip to next
    if child_K <= 0.0 and not finished_flag:
        self.current_strat["next_idx"] = idx + 1
        self._strat_update_stats()
        self._strat_update_venue_table()
        self._update_strat_chart()
        delay_ms = int(self.current_strat["bucket_seconds"] * 1000)
        self.after(delay_ms, self._strat_tick)
        return

    # Temporarily override the quote_qty_var with the child K
    old_K = self.quote_qty_var.get()
    self.quote_qty_var.set(child_K)

    sym = s["sym"]
    base = s["base"]
    side = s["side"]
    use_sor = bool(s.get("use_sor", False))

    # Approximate execution price by current mid at send time
    exec_px = self._mid_now(sym) or self._strat_arrival_mid or 0.0

    child_stats = None
    try:
        if use_sor:
            # For now, aggregate all SOR child executions into a virtual venue "SOR"
            venue_label = "SOR"
            self._sor_execute(side)
        else:
            # Market flow (Binance testnet) — returns child friction decomposition
            venue_label = "binance"
            child_stats = self._place(side)
    except Exception:
        # If anything blows up, treat this child as unexecuted in this toy version.
        exec_px = 0.0
        venue_label = "Unknown"
    finally:
        # Restore original K in UI entry
        try:
            self.quote_qty_var.set(old_K)
        except Exception:
            pass

    # Record child exec in K units for perf & friction calculations
    if exec_px and math.isfinite(exec_px) and exec_px > 0 and child_K > 0:
        if (not use_sor) and isinstance(child_stats, dict):
            # Use *actual* child costs from _place (Market strategy)
            self._strat_record_child(
                venue_label,
                side,  # NEW-style signature
                price=exec_px,
                qty_base_or_side=None,
                notional_usdt=child_stats.get("notional_usdt"),
                fees_usdt=child_stats.get("fees_usdt", 0.0),
                impact_usdt=child_stats.get("impact_usdt", 0.0),
                spread_usdt=child_stats.get("spread_usdt", 0.0),
                slippage_usdt=child_stats.get("slippage_usdt", 0.0),
            )
        else:
            # Fallback: legacy approximation (SOR or error case)
            self._strat_record_child(venue_label, child_K, exec_px, side)

    # Update remaining / progress
    remaining_K = max(0.0, remaining_K - child_K)
    self.current_strat["remaining_K"] = remaining_K
    self.current_strat["next_idx"] = idx + 1

    total_K = float(self.current_strat["total_K"])
    executed_K = max(0.0, total_K - remaining_K)
    progress = (executed_K / total_K * 100.0) if (total_K > 0) else 0.0
    self.strat_progress.configure(value=progress)

    # --- If finished_flag is True, show summary and stop here ----
    if finished_flag:
        self.current_strat["status"] = "Completed"

        # Executed quote in USDT (inflated: 1 K = 1000 USDT)
        executed_quote_usdt = executed_K * 1000.0
        remaining_quote_usdt = remaining_K * 1000.0

        # Executed base volume from child records (inflated base units)
        try:
            executed_base = sum(
                float(rec.get("qty_base", 0.0) or 0.0)
                for rec in (self._strat_child_execs or [])
            )
        except Exception:
            executed_base = 0.0

        # Reason: remaining < 5K vs time horizon
        now = time.time()
        start_ts = float(s.get("start_ts", now))
        duration_sec = float(s.get("duration_sec", 0.0) or 0.0)
        if remaining_K > 0.0 and remaining_K < 5.0:
            reason = "Remaining slice below 5 K-USDT minimum."
        elif duration_sec > 0.0 and (now - start_ts) >= duration_sec - 1e-6:
            reason = "Time horizon reached."
        else:
            reason = "Target schedule completed."

        strat_label = (s.get("name") or "Strategy").upper()
        side_label = (side or "").upper()

        messagebox.showinfo(
            "Strategy finished",
            f"{strat_label} {side_label} finished.\n\n"
            f"Executed quote: {fmt_usd(executed_quote_usdt)} {QUOTE}\n"
            f"Executed base:  {fmt_qty(executed_base)} {base}\n"
            f"Remaining quote not executed: {fmt_usd(remaining_quote_usdt)} {QUOTE}\n\n"
            f"Reason: {reason}"
        )

        self._strat_update_stats()
        self._strat_update_venue_table()
        self._update_strat_chart()
        return

    # Refresh stats panel, per-venue table, and chart
    self._strat_update_stats()
    self._strat_update_venue_table()
    self._update_strat_chart()

    # Schedule next bucket if still ongoing and there is remaining volume
    if self.current_strat["status"] == "Ongoing" and remaining_K > 0:
        delay_ms = int(self.current_strat["bucket_seconds"] * 1000)
        self.after(delay_ms, self._strat_tick)
    else:
        self.current_strat["status"] = "Completed"
        self._strat_update_stats()
        self._strat_update_venue_table()
        self._update_strat_chart()


def _strat_update_stats(self):
    """
    Update the Strat Stats panel from self.current_strat & child execs.

    Fields:
      - Strategy, Status, Launch time, Way
      - Order quote qty, Remaining quote, Remaining time
      - Perf vs arrival (VWAP of execs vs arrival mid)
      - Perf vs mkt TWAP (VWAP of execs vs market TWAP since launch)
      - Friction: total market friction and its components (sum over child orders)
      - Per-venue aggregate stats for the 'Strat — Per-Venue' table.
    """
    # If no strategy, reset everything
    if not self.current_strat:
        for k, lbl in self.strat_stats.items():
            lbl.configure(text="—", style="StatValue.TLabel")
        self.strat_progress.configure(value=0)
        return

    s = self.current_strat
    now = time.time()

    total_K = float(s.get("total_K", 0.0))
    remaining_K = float(s.get("remaining_K", 0.0))
    executed_K = max(0.0, total_K - remaining_K)

    # In this app, 1 K = 1000 USDT
    total_usdt = total_K * 1000.0
    remaining_usdt = remaining_K * 1000.0

    # Remaining time
    start_ts = float(s.get("start_ts", now))
    duration_sec = float(s.get("duration_sec", 0.0))
    elapsed = max(0.0, now - start_ts)
    remaining_t = max(0.0, duration_sec - elapsed)

    def _fmt_mmss(seconds: float) -> str:
        seconds = max(0, int(round(seconds)))
        m, sec = divmod(seconds, 60)
        return f"{m:02d}:{sec:02d}"

    # ----- Basic fields (amber style) -----
    launch_str = time.strftime("%Y-%m-%d %H:%M:%S", time.localtime(start_ts))
    self.strat_stats["s_name"].configure(text=str(s.get("name", "—")), style="StatAmber.TLabel")
    self.strat_stats["s_status"].configure(text=s.get("status", "—"), style="StatAmber.TLabel")
    self.strat_stats["s_launch"].configure(text=launch_str, style="StatAmber.TLabel")
    self.strat_stats["s_way"].configure(text=(s.get("side", "") or "—").upper(), style="StatAmber.TLabel")
    self.strat_stats["s_total_quote"].configure(text=fmt_usd(total_usdt), style="StatValue.TLabel")
    self.strat_stats["s_remaining_quote"].configure(text=fmt_usd(remaining_usdt), style="StatValue.TLabel")
    self.strat_stats["s_remaining_time"].configure(
        text=_fmt_mmss(0.0 if s.get("status") == "Completed" else remaining_t),
        style="StatValue.TLabel",
    )

    # ----- Realized VWAP of executions -----
    arrival = self._strat_arrival_mid or float("nan")
    vwap_exec_px = float("nan")
    if self._strat_execs and arrival and np.isfinite(arrival) and arrival > 0:
        sum_K = sum(k for k, _ in self._strat_execs)
        sum_Kpx = sum(k * px for k, px in self._strat_execs)
        if sum_K > 0 and np.isfinite(sum_Kpx):
            vwap_exec_px = sum_Kpx / sum_K

    # ----- Perf vs arrival -----
    perf_arrival_pct = float("nan")
    if np.isfinite(vwap_exec_px) and np.isfinite(arrival) and arrival > 0:
        if s.get("side") == "buy":
            # For a buy, lower exec price is better → positive perf if vwap_exec < arrival
            perf_arrival_pct = (arrival / vwap_exec_px - 1.0) * 100.0
        else:
            # For a sell, higher exec price is better → positive perf if vwap_exec > arrival
            perf_arrival_pct = (vwap_exec_px / arrival - 1.0) * 100.0

    if np.isfinite(perf_arrival_pct):
        style = "StatValueGreen.TLabel" if perf_arrival_pct >= 0 else "StatValueRed.TLabel"
        self.strat_stats["s_perf_arrival"].configure(
            text=fmt_pct_or_bp(perf_arrival_pct),
            style=style,
        )
    else:
        self.strat_stats["s_perf_arrival"].configure(text="—", style="StatValue.TLabel")

    # ----- Perf vs mkt TWAP (mid TWAP since launch) -----
    mkt_twap_px = float("nan")
    if len(self._strat_mkt_samples) >= 2:
        # time-weighted TWAP
        times = [t for t, _ in self._strat_mkt_samples]
        mids = [m for _, m in self._strat_mkt_samples]
        twap_num = 0.0
        twap_den = 0.0
        for i in range(len(times) - 1):
            dt = times[i + 1] - times[i]
            if dt <= 0:
                continue
            mid_i = mids[i]
            if not (np.isfinite(mid_i) and mid_i > 0):
                continue
            twap_num += mid_i * dt
            twap_den += dt
        if twap_den > 0:
            mkt_twap_px = twap_num / twap_den

    perf_twap_pct = float("nan")
    if np.isfinite(vwap_exec_px) and np.isfinite(mkt_twap_px) and mkt_twap_px > 0:
        side = (s.get("side") or "").lower()
        if side == "buy":
            perf_twap_pct = (mkt_twap_px / vwap_exec_px - 1.0) * 100.0
        else:
            perf_twap_pct = (vwap_exec_px / mkt_twap_px - 1.0) * 100.0

    if np.isfinite(perf_twap_pct):
        style = "StatValueGreen.TLabel" if perf_twap_pct >= 0 else "StatValueRed.TLabel"
        self.strat_stats["s_perf_twap"].configure(
            text=fmt_pct_or_bp(perf_twap_pct),
            style=style,
        )
    else:
        self.strat_stats["s_perf_twap"].configure(text="—", style="StatValue.TLabel")

    # ----- Friction: sum over child orders -----
    fees = impact = spread = slipp = 0.0
    mkt_total = 0.0
    if self._strat_child_execs and total_usdt > 0:
        for rec in self._strat_child_execs:
            f = rec.get("fees_usdt")
            if np.isfinite(f):
                fees += f
            i = rec.get("impact_usdt")
            if np.isfinite(i):
                impact += i
            sp = rec.get("spread_usdt")
            if np.isfinite(sp):
                spread += sp
            sl = rec.get("slippage_usdt")
            if np.isfinite(sl):
                slipp += sl
        parts = [fees, impact, spread, slipp]
        mkt_total = float(sum(x for x in parts if np.isfinite(x)))

        def _pct_of_notional(x: float) -> float:
            return (x / total_usdt * 100.0) if (
                    np.isfinite(x) and np.isfinite(total_usdt) and total_usdt > 0
            ) else float("nan")

        mkt_total_pct = _pct_of_notional(mkt_total)
        fees_pct = _pct_of_notional(fees)
        impact_pct = _pct_of_notional(impact)
        spread_pct = _pct_of_notional(spread)
        slipp_pct = _pct_of_notional(slipp)

        # Total friction
        style_tot = "StatValueGreen.TLabel" if mkt_total >= 0 else "StatValueRed.TLabel"
        self.strat_stats["s_mkt_total"].configure(
            text=f"{fmt_usd(mkt_total)} USDT  |  {fmt_pct_or_bp(mkt_total_pct)}",
            style=style_tot,
        )
        # Components (fees, impact, spread, slippage)
        self.strat_stats["s_fees"].configure(
            text=f"{fmt_usd(fees)} USDT  |  {fmt_pct_or_bp(fees_pct)}",
            style=("StatValueGreen.TLabel" if fees >= 0 else "StatValueRed.TLabel"),
        )
        self.strat_stats["s_impact"].configure(
            text=f"{fmt_usd(impact)} USDT  |  {fmt_pct_or_bp(impact_pct)}",
            style=("StatValueGreen.TLabel" if impact >= 0 else "StatValueRed.TLabel"),
        )
        self.strat_stats["s_spread"].configure(
            text=f"{fmt_usd(spread)} USDT  |  {fmt_pct_or_bp(spread_pct)}",
            style=("StatValueGreen.TLabel" if spread >= 0 else "StatValueRed.TLabel"),
        )
        self.strat_stats["s_slippage"].configure(
            text=f"{fmt_usd(slipp)} USDT  |  {fmt_pct_or_bp(slipp_pct)}",
            style=("StatValueGreen.TLabel" if slipp >= 0 else "StatValueRed.TLabel"),
        )
    else:
        # No executions yet → neutral / 0
        self.strat_stats["s_mkt_total"].configure(text="0.00 USDT  |  +0.00%", style="StatValue.TLabel")
        self.strat_stats["s_fees"].configure(text="0.00 USDT  |  +0.00%", style="StatValue.TLabel")
        self.strat_stats["s_impact"].configure(text="0.00 USDT  |  +0.00%", style="StatValue.TLabel")
        self.strat_stats["s_spread"].configure(text="0.00 USDT  |  +0.00%", style="StatValue.TLabel")
        self.strat_stats["s_slippage"].configure(text="0.00 USDT  |  +0.00%", style="StatValue.TLabel")

    # ----- Push per-venue stats (for Strat — Per-Venue table) ---------------
    # We already accumulated notional and costs per venue in _strat_record_child.
    if hasattr(self, "_strat_venue_stats"):
        for v, d in self._strat_venue_stats.items():
            notional_v = float(d.get("notional", 0.0) or 0.0)
            num = float(d.get("vwap_order_num", 0.0) or 0.0)
            den = float(d.get("vwap_order_den", 0.0) or 0.0)
            vwap_order_px = (num / den) if (den > 0 and np.isfinite(num)) else np.nan
            d["vwap_order_px"] = vwap_order_px
            d["twap_order_px"] = vwap_order_px  # toy: TWAP order ≈ VWAP of child fills
            d["twap_mkt_px"] = mkt_twap_px

            # Per-venue perf vs arrival
            perf_v = float("nan")
            if np.isfinite(vwap_order_px) and np.isfinite(arrival) and arrival > 0:
                if s.get("side") == "buy":
                    perf_v = (arrival / vwap_order_px - 1.0) * 100.0
                else:
                    perf_v = (vwap_order_px / arrival - 1.0) * 100.0
            d["perf_arrival_pct"] = perf_v

            # Per-venue total friction = sum of components
            f_v = float(d.get("fees_usdt", 0.0) or 0.0)
            i_v = float(d.get("impact_usdt", 0.0) or 0.0)
            sp_v = float(d.get("spread_usdt", 0.0) or 0.0)
            sl_v = float(d.get("slippage_usdt", 0.0) or 0.0)
            parts_v = [f_v, i_v, sp_v, sl_v]
            d["total_mkt_usdt"] = float(sum(x for x in parts_v if np.isfinite(x)))

        # For pure market strats, this automatically yields one venue "binance"
        # with 100% of notional; SOR strats will aggregate under "SOR" for now.

    # Push market TWAP into per-venue stats (TWAP Market same for all venues)
    if np.isfinite(mkt_twap_px) and hasattr(self, "_strat_venue_stats"):
        for v, d in self._strat_venue_stats.items():
            d["twap_mkt_px"] = mkt_twap_px


# ---------- Strategy roadmap wrappers (TWAP / VWAP / IS) ----------
def _twap_next_child(self) -> tuple[float, bool]:
    """
    Wrapper around trading_utils.twap_next_child.

    Returns
    -------
    (child_K, finished)
      child_K : float (integer K units)
      finished : bool
    """
    if not self.current_strat:
        return 0.0, True
    s = self.current_strat
    total_K = float(s.get("total_K", 0.0))
    remaining_K = float(s.get("remaining_K", 0.0))
    executed_K = max(0.0, total_K - remaining_K)
    duration_sec = float(s.get("duration_sec", 0.0) or 0.0)
    start_ts = float(s.get("start_ts", time.time()))
    elapsed_sec = max(0.0, time.time() - start_ts)
    return twap_next_child(total_K, executed_K, duration_sec, elapsed_sec)


def _vwap_next_child(self) -> tuple[float, bool]:
    """
    Wrapper around trading_utils.vwap_next_child.
    """
    if not self.current_strat:
        return 0.0, True
    s = self.current_strat
    total_K = float(s.get("total_K", 0.0))
    remaining_K = float(s.get("remaining_K", 0.0))
    executed_K = max(0.0, total_K - remaining_K)
    duration_sec = float(s.get("duration_sec", 0.0) or 0.0)
    start_ts = float(s.get("start_ts", time.time()))
    elapsed_sec = max(0.0, time.time() - start_ts)
    return vwap_next_child(total_K, executed_K, duration_sec, elapsed_sec)


def _is_next_child(self) -> tuple[float, bool]:
    """
    Wrapper around trading_utils.is_next_child.
    """
    if not self.current_strat:
        return 0.0, True
    s = self.current_strat
    total_K = float(s.get("total_K", 0.0))
    remaining_K = float(s.get("remaining_K", 0.0))
    executed_K = max(0.0, total_K - remaining_K)
    duration_sec = float(s.get("duration_sec", 0.0) or 0.0)
    start_ts = float(s.get("start_ts", time.time()))
    elapsed_sec = max(0.0, time.time() - start_ts)
    return is_next_child(total_K, executed_K, duration_sec, elapsed_sec)


def _placeholder_sor_sell(self):
    self._sor_execute("sell")


def _placeholder_strat_buy(self):
    messagebox.showinfo("Strat Exec (Buy)",
                        f"Placeholder\nStrat={self.strategy_var.get()} | Duration={self.duration_var.get()} min | Use SOR={self.use_sor_var.get()}")


def _placeholder_strat_sell(self):
    messagebox.showinfo("Strat Exec (Sell)",
                        f"Placeholder\nStrat={self.strategy_var.get()} | Duration={self.duration_var.get()} min | Use SOR={self.use_sor_var.get()}")


# ---------- Utilities ----------
def _set_stat(self, key: str, text: str):
    if key in getattr(self, "_amber_stat_keys", set()):
        self.stats[key].configure(text=text, style="StatAmber.TLabel")
    else:
        self.stats[key].configure(text=text, style="StatValue.TLabel")


def _set_stat_signed(self, key: str, text: str, positive_green: bool):
    self.stats[key].configure(
        text=text,
        style=("StatValueGreen.TLabel" if positive_green else "StatValueRed.TLabel")
    )


def _update_stats_title(self, side: str, mode: str = "Market"):
    """Update the right-top title to include 'Buy/Sell at Market' or 'Buy/Sell SOR' with color."""
    try:
        if side.lower() == "buy":
            color = BLOOM_GREEN
            tag_side = "Buy"
        elif side.lower() == "sell":
            color = BLOOM_RED
            tag_side = "Sell"
        else:
            color = FG_MAIN
            tag_side = ""
        suffix = "at Market" if mode.lower() == "market" else "SOR"
        tag = f"{tag_side} {suffix}".strip()
        self.stats_side_lbl.configure(text=(f"— {tag}" if tag else ""), foreground=color)
    except Exception:
        pass


def _on_close(self):
    self.destroy()


# ---------- Main ----------
if __name__ == "__main__":
    app = FrictionApp()
    app.mainloop()
