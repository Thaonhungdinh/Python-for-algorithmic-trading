# Mkt_impact_app.py
# ----------------------------------------------------
# Market Impact & Liquidity — Mono-venue vs Multi-venue (SOR)
# ----------------------------------------------------
import tkinter as tk
from tkinter import ttk, messagebox
from dataclasses import dataclass
from typing import List, Tuple, Optional, Dict
from trading_utils import aggregate_orderbooks

import ccxt
import numpy as np
import matplotlib
matplotlib.use("TkAgg")
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg, NavigationToolbar2Tk
from matplotlib.patches import FancyArrowPatch

# ---------- Palette ----------
BLOOM_BLUE   = "#2a6df4"
BLOOM_BLUE_H = "#3b7cff"
BLOOM_GREEN  = "#2bb673"
BLOOM_GREEN_H= "#31c27f"
BLOOM_AMBER  = "#f4a62a"   # yellow (numbers + consumed fill)
BLOOM_RED    = "#f05454"
BLOOM_RED_H  = "#ff6a6a"
FG_MAIN      = "#e9edf3"
FG_MUTED     = "#aeb7c7"
BG_DARK      = "#0b0f17"
BG_PANEL     = "#161b26"
SEP          = "#444a60"

plt.rcParams.update({
    "figure.facecolor":   "#0e1118",
    "axes.facecolor":     BG_DARK,
    "axes.edgecolor":     "#2b3245",
    "axes.labelcolor":    FG_MAIN,
    "axes.grid":          True,
    "grid.color":         "#30394e",
    "grid.linewidth":     0.6,
    "xtick.color":        "#cbd3e1",
    "ytick.color":        "#cbd3e1",
    "legend.facecolor":   BG_DARK,
    "legend.edgecolor":   "#2b3245",
    "text.color":         FG_MAIN,
    "font.size":          11,
})

# ---------- Fixed SOR venue list ----------
TOP10_VENUES = [
    "binance", "okx", "bybit", "kraken", "coinbase",
    "kucoin", "bitget", "huobi", "bitstamp", "gateio"
]

# ---------- Formatting ----------
def fmt_px(x):   return f"{x:,.2f}" if np.isfinite(x) else "—"
def fmt_qty(x):  return f"{x:,.6f}" if np.isfinite(x) else "—"
def fmt_pct4_signed(x):
    if not np.isfinite(x): return "—"
    return f"{x:+.4f}%"
def fmt_pct4_plain(x):
    if not np.isfinite(x): return "—"
    return f"{x:.4f}%"
def fmt_bps1_abs(x):
    if not np.isfinite(x): return "—"
    return f"{abs(x):.1f} bps"

def parse_units(symbol: str) -> Tuple[str, str]:
    s = symbol.strip()
    if "/" in s:
        left, right = s.split("/", 1)
        return left.upper(), right.split(":")[0].upper()
    if len(s) >= 6:
        return s[:-4].upper(), s[-4:].upper()
    return s.upper(), "QUOTE"

# ---------- OB helpers ----------
def fetch_snapshot(exchange_name: str, symbol: str, limit: int = 1000) -> Dict[str, List[List[float]]]:
    """Get as many levels as the venue returns (ask for 1000)."""
    ex = getattr(ccxt, exchange_name)()
    ob = ex.fetch_order_book(symbol, limit=limit)
    # some venues return [price, size, id, ...] -> ignore extras
    bids = sorted([[float(x[0]), float(x[1])] for x in ob.get("bids", [])], key=lambda v: v[0], reverse=True)
    asks = sorted([[float(x[0]), float(x[1])] for x in ob.get("asks", [])], key=lambda v: v[0])
    return {"bids": bids, "asks": asks}

def ladder_to_arrays(bids: List[List[float]], asks: List[List[float]]):
    if bids:
        b_px = np.array([float(p) for p, *_ in bids], dtype=float)
        b_sz = np.array([float(s) for *_, s in [[x[0], x[1]] for x in bids]], dtype=float)
        b_cum = np.cumsum(b_sz)
    else:
        b_px = np.array([]); b_sz = np.array([]); b_cum = np.array([])
    if asks:
        a_px = np.array([float(p) for p, *_ in asks], dtype=float)
        a_sz = np.array([float(s) for *_, s in [[x[0], x[1]] for x in asks]], dtype=float)
        a_cum = np.cumsum(a_sz)
    else:
        a_px = np.array([]); a_sz = np.array([]); a_cum = np.array([])
    best_bid = float(b_px[0]) if b_px.size else np.nan
    best_ask = float(a_px[0]) if a_px.size else np.nan
    mid = (best_bid + best_ask)/2.0 if np.isfinite(best_bid) and np.isfinite(best_ask) else np.nan
    return b_px, b_sz, b_cum, a_px, a_sz, a_cum, best_bid, best_ask, mid

def not_enough_depth_err(side_text: str):
    raise RuntimeError(
        f"Requested {side_text} exceeds visible order book depth. "
        "Use a smaller amount or increase snapshot depth."
    )

# ---------- Result model ----------
@dataclass
class ImpactResult:
    side: str
    consumed_to_price: float
    vwap_price: float
    base_executed: float
    quote_spent: float
    new_best_bid: float
    new_best_ask: float
    impact_pct_mid: float
    arrival_price: float
    exec_perf_arrival_bps: float
    impact_touch_pct: float
    impact_cost_quote: float
    consumed_min_px: float
    consumed_max_px: float
    old_best_bid: float
    old_best_ask: float

# ---------- Simulations (mono OR aggregated) ----------
def simulate_instant_impact(bids, asks, side: str, quote_qty: float) -> ImpactResult:
    b_px, b_sz, b_cum, a_px, a_sz, a_cum, best_bid, best_ask, mid = ladder_to_arrays(bids, asks)
    if not np.isfinite(mid): raise RuntimeError("Order book incomplete (mid undefined).")

    quote_left = float(abs(quote_qty))
    base_filled = 0.0
    quote_used = 0.0
    vwap_num = 0.0

    if side == "buy":
        if a_px.size == 0: not_enough_depth_err("buy")
        arrival = best_ask
        last_px = arrival
        consumed_min, consumed_max = arrival, arrival
        new_best_ask = arrival
        for i, (price, size, *_) in enumerate(asks):
            price = float(price); size = float(size)
            cap_q = price * size
            if cap_q <= quote_left + 1e-12:
                take_base, take_quote = size, cap_q
                new_best_ask = float(asks[i+1][0]) if (i+1) < len(asks) else np.nan
            else:
                take_base, take_quote = quote_left/price, quote_left
                new_best_ask = price
            base_filled += take_base; quote_used += take_quote
            vwap_num += price * take_base
            quote_left -= take_quote
            last_px = price
            consumed_max = max(consumed_max, price)
            if quote_left <= 1e-12: break
        else:
            not_enough_depth_err("buy")

        vwap = vwap_num/base_filled
        exec_perf_bps = (vwap/arrival - 1.0)*1e4
        impact_touch = (new_best_ask/arrival - 1.0) if np.isfinite(new_best_ask) else float("nan")
        impact_cost_q = max(vwap-arrival, 0.0) * base_filled
        return ImpactResult("buy", last_px, vwap, base_filled, quote_used,
                            best_bid, new_best_ask, (vwap/mid - 1.0)*100.0,
                            arrival, exec_perf_bps, (impact_touch*100.0) if np.isfinite(impact_touch) else float("nan"),
                            impact_cost_q, consumed_min, consumed_max,
                            old_best_bid=best_bid, old_best_ask=best_ask)

    # SELL
    if b_px.size == 0: not_enough_depth_err("sell")
    arrival = best_bid
    last_px = arrival
    consumed_min, consumed_max = arrival, arrival
    new_best_bid = arrival
    for i, (price, size, *_) in enumerate(bids):
        price = float(price); size = float(size)
        cap_q = price * size
        if cap_q <= quote_left + 1e-12:
            take_base, take_quote = size, cap_q
            new_best_bid = float(bids[i+1][0]) if (i+1) < len(bids) else np.nan
        else:
            take_base, take_quote = quote_left/price, quote_left
            new_best_bid = price
        base_filled += take_base; quote_used += take_quote
        vwap_num += price * take_base
        quote_left -= take_quote
        last_px = price
        consumed_min = min(consumed_min, price)
        if quote_left <= 1e-12: break
    else:
        not_enough_depth_err("sell")

    vwap = vwap_num/base_filled
    exec_perf_bps = (vwap/arrival - 1.0)*1e4
    impact_touch = (new_best_bid/arrival - 1.0) if np.isfinite(new_best_bid) else float("nan")
    impact_cost_q = max(arrival - vwap, 0.0) * base_filled
    return ImpactResult("sell", last_px, vwap, base_filled, quote_used,
                        new_best_bid, best_ask, (vwap/mid - 1.0)*100.0,
                        arrival, exec_perf_bps, (impact_touch*100.0) if np.isfinite(impact_touch) else float("nan"),
                        impact_cost_q, consumed_min, consumed_max,
                        old_best_bid=best_bid, old_best_ask=best_ask)

# ---------- Base App ----------
class OrderBookImpactApp(tk.Tk):
    def __init__(self):
        super().__init__()
        self.title("Market Impact & Liquidity — Mono vs Multi Venue")
        self.geometry("1500x1000")
        self.configure(bg=BG_DARK)
        self.base_unit = "BASE"; self.quote_unit = "QUOTE"

        self._build_style()
        self._build_notebook()

    # ----- styles -----
    def _build_style(self):
        s = ttk.Style(); s.theme_use("clam")
        s.configure(".", background=BG_DARK, foreground=FG_MAIN)
        s.map(".", foreground=[("disabled", "#6d7990")])

        # Notebook tabs bigger + dark
        s.configure("Bloom.TNotebook", background=BG_DARK, borderwidth=0)
        s.configure("Bloom.TNotebook.Tab",
                   padding=(18, 10),
                   font=("Helvetica", 12, "bold"),
                   background=BG_PANEL, foreground=FG_MAIN)
        s.map("Bloom.TNotebook.Tab",
              background=[("selected", "#0f1320"), ("active", "#131a29")],
              foreground=[("selected", FG_MAIN), ("active", FG_MAIN)])

        s.configure("Bloom.Blue.TButton", padding=(12, 8), background=BLOOM_BLUE,
                    foreground="#ffffff", font=("Helvetica", 12, "bold"), borderwidth=0)
        s.map("Bloom.Blue.TButton", background=[("active", BLOOM_BLUE_H)])
        s.configure("Bloom.Green.TButton", padding=(12, 8), background=BLOOM_GREEN,
                    foreground=BG_DARK, font=("Helvetica", 12, "bold"), borderwidth=0)
        s.map("Bloom.Green.TButton", background=[("active", BLOOM_GREEN_H)])
        s.configure("Bloom.Amber.TButton", padding=(12, 8), background=BLOOM_AMBER,
                    foreground=BG_DARK, font=("Helvetica", 12, "bold"), borderwidth=0)
        s.map("Bloom.Amber.TButton", background=[("active", "#ffb23b")])

        s.configure("Dark.TEntry", fieldbackground=BG_PANEL, foreground=FG_MAIN,
                    insertcolor=FG_MAIN, padding=4)

        # Radios + hover styles
        s.configure("Slim.TRadiobutton", background=BG_DARK, foreground=FG_MAIN)
        s.configure("HoverRed.TRadiobutton", background=BG_DARK, foreground=BLOOM_RED_H)
        s.configure("HoverGreen.TRadiobutton", background=BG_DARK, foreground=BLOOM_GREEN_H)

        # Checkbuttons (venues)
        s.configure("Venue.Default.TCheckbutton", background=BG_DARK, foreground=FG_MAIN)
        s.map("Venue.Default.TCheckbutton", background=[("active", BG_PANEL)])
        s.configure("Venue.Amber.TCheckbutton", background=BLOOM_AMBER, foreground=BG_DARK)
        s.configure("Venue.Green.TCheckbutton", background=BLOOM_GREEN, foreground=BG_DARK)
        s.configure("Venue.Red.TCheckbutton",   background=BLOOM_RED,   foreground="#ffffff")

        # Results typography
        s.configure("StatRow.TFrame", background=BG_DARK)
        s.configure("StatName.TLabel", background=BG_DARK, foreground=FG_MUTED, font=("Menlo", 12, "bold"))
        s.configure("StatValue.TLabel", background=BG_DARK, foreground=BLOOM_AMBER, font=("Menlo", 13, "bold"))
        s.configure("StatValueRed.TLabel", background=BG_DARK, foreground=BLOOM_RED_H, font=("Menlo", 13, "bold"))
        s.configure("StatValueGreen.TLabel", background=BG_DARK, foreground=BLOOM_GREEN_H, font=("Menlo", 13, "bold"))
        s.configure("Bloom.TSeparator", background=SEP)

    # ----- notebook with two tabs -----
    def _build_notebook(self):
        self.nb = ttk.Notebook(self, style="Bloom.TNotebook")
        self.nb.pack(side="top", fill="both", expand=True, padx=10, pady=10)

        # Tab 1 — Mono venue
        self.tab_mono = MonoVenueTab(self.nb, parent_app=self)
        self.nb.add(self.tab_mono, text="(1) Mono-venue Impact", padding=4)

        # Tab 2 — Multi venue (SOR)
        self.tab_multi = MultiVenueTab(self.nb, parent_app=self)
        self.nb.add(self.tab_multi, text="(2) Multi-venue SOR", padding=4)
        self.nb.enable_traversal()
        self.nb.option_add("*TNotebook.Tab*style", "Bloom.TNotebook.Tab")

# ---------- Tab 1 (Mono) ----------
class MonoVenueTab(ttk.Frame):
    def __init__(self, master, parent_app: OrderBookImpactApp):
        super().__init__(master)
        self.parent_app = parent_app
        self.base_unit = "BASE"; self.quote_unit = "QUOTE"

        self._snapshot: Optional[Dict[str, List[List[float]]]] = None
        self._fig = None; self._ax = None; self._canvas = None
        self._hover_ann = None; self._hover_marker = None
        self._yellow_patches = []; self._consumed = None
        self._plot_art = {"arrival_v":None, "last_v":None, "arr_last_arrow":None, "arr_last_text":None}

        self._build_controls()
        self._build_plot_and_stats()

    # ---------- UI ----------
    def _build_controls(self):
        bar = ttk.Frame(self, padding=(10,6)); bar.pack(side="top", fill="x")

        # Group 1
        g1 = ttk.Frame(bar, padding=(2,1)); g1.pack(side="left")
        ttk.Label(g1, text="Exchange:").grid(row=0, column=0, sticky="e", padx=5, pady=2)
        self.exchange_var = tk.StringVar(value="binance")
        ttk.Entry(g1, textvariable=self.exchange_var, width=14, style="Dark.TEntry").grid(row=0, column=1, padx=5, pady=2)
        ttk.Label(g1, text="Symbol:").grid(row=0, column=2, sticky="e", padx=5, pady=2)
        self.symbol_var = tk.StringVar(value="BTC/USDT")
        ttk.Entry(g1, textvariable=self.symbol_var, width=14, style="Dark.TEntry").grid(row=0, column=3, padx=5, pady=2)
        ttk.Button(g1, text="Snapshot OB", style="Bloom.Blue.TButton", command=self._load_snapshot)\
            .grid(row=1, column=0, columnspan=4, pady=(6,2))

        ttk.Separator(bar, orient="vertical", style="Bloom.TSeparator").pack(side="left", fill="y", padx=10, pady=2)

        # Group 2 (instant impact)
        g2 = ttk.Frame(bar, padding=(2,1)); g2.pack(side="left")
        self.side_var = tk.StringVar(value="buy")
        self.buy_rb  = ttk.Radiobutton(g2, text="Buy", value="buy", variable=self.side_var, style="Slim.TRadiobutton")
        self.sell_rb = ttk.Radiobutton(g2, text="Sell", value="sell", variable=self.side_var, style="Slim.TRadiobutton")
        self.buy_rb.grid(row=0, column=0, padx=6)
        self.sell_rb.grid(row=0, column=1, padx=6)
        self.buy_rb.bind("<Enter>", lambda e: self.buy_rb.configure(style="HoverRed.TRadiobutton"))
        self.buy_rb.bind("<Leave>", lambda e: self.buy_rb.configure(style="Slim.TRadiobutton"))
        self.sell_rb.bind("<Enter>", lambda e: self.sell_rb.configure(style="HoverGreen.TRadiobutton"))
        self.sell_rb.bind("<Leave>", lambda e: self.sell_rb.configure(style="Slim.TRadiobutton"))

        ttk.Label(g2, text="Quote Qty:").grid(row=0, column=2, sticky="e", padx=6)
        self.quote_qty_var = tk.DoubleVar(value=1_000_000.0)
        ttk.Entry(g2, textvariable=self.quote_qty_var, width=14, style="Dark.TEntry").grid(row=0, column=3, padx=6)
        ttk.Button(g2, text="Calculate instant impact", style="Bloom.Green.TButton",
                   command=self._do_instant_impact).grid(row=1, column=0, columnspan=4, pady=(6,2))

        ttk.Separator(bar, orient="vertical", style="Bloom.TSeparator").pack(side="left", fill="y", padx=10, pady=2)

        # Group 3 (volume for target impact)
        g3 = ttk.Frame(bar, padding=(2,1)); g3.pack(side="left")
        self.ladder_side_var = tk.StringVar(value="asks")
        self.asks_rb = ttk.Radiobutton(g3, text="Asks (push up)", value="asks", variable=self.ladder_side_var,
                                       style="Slim.TRadiobutton")
        self.bids_rb = ttk.Radiobutton(g3, text="Bids (push down)", value="bids", variable=self.ladder_side_var,
                                       style="Slim.TRadiobutton")
        self.asks_rb.grid(row=0, column=0, padx=6)
        self.bids_rb.grid(row=0, column=1, padx=6)
        ttk.Label(g3, text="Impact %:").grid(row=0, column=2, sticky="e", padx=6)
        self.impact_pct_var = tk.DoubleVar(value=0.03)
        ttk.Entry(g3, textvariable=self.impact_pct_var, width=10, style="Dark.TEntry").grid(row=0, column=3, padx=6)
        ttk.Button(g3, text="Volume for impact", style="Bloom.Amber.TButton",
                   command=self._do_volume_for_impact).grid(row=1, column=0, columnspan=4, pady=(6,2))

    def _build_plot_and_stats(self):
        self._root_pane = ttk.Panedwindow(self, orient="vertical")
        self._root_pane.pack(side="top", fill="both", expand=True)

        plot_frame = ttk.Frame(self._root_pane, padding=(10, 6))
        self._root_pane.add(plot_frame, weight=3)

        self._fig = plt.Figure(dpi=100, constrained_layout=True)
        self._ax = self._fig.add_subplot(111)
        self._canvas = FigureCanvasTkAgg(self._fig, master=plot_frame)
        self._canvas_widget = self._canvas.get_tk_widget()
        self._canvas_widget.pack(side="top", fill="both", expand=True)
        NavigationToolbar2Tk(self._canvas, plot_frame).update()
        self._canvas.mpl_connect("motion_notify_event", self._on_hover)
        self._hover_ann = self._ax.annotate(
            "", xy=(0,0), xytext=(14,18), textcoords="offset points",
            bbox=dict(boxstyle="round,pad=0.5", fc=BG_PANEL, ec="#ffffff", alpha=0.98),
            arrowprops=dict(arrowstyle="->", color="#ffffff"),
            color="#ffffff", fontsize=12, fontweight="bold", visible=False, zorder=10
        )
        self._hover_marker, = self._ax.plot([], [], marker="o", ms=6, mec="#ffffff",
                                            mfc=BLOOM_AMBER, alpha=0.95, lw=0, zorder=9)
        self._root_pane.add(self._build_stats_block(two_blocks=True), weight=2)
        self.bind("<Configure>", self._on_resize)
        self._redraw_depth(None); self._set_stats_empty()

    def _build_stats_block(self, two_blocks: bool):
        stats_outer = ttk.Frame(self, padding=(10,6))
        stats_center = ttk.Frame(stats_outer); stats_center.pack(expand=True, fill="x")
        self._block1 = ttk.Frame(stats_center, padding=(1,1))
        self._block1.pack(side="left", padx=8, fill="x", expand=True)

        if two_blocks:
            ttk.Separator(stats_center, orient="vertical", style="Bloom.TSeparator")\
                .pack(side="left", fill="y", padx=8)
            self._block2 = ttk.Frame(stats_center, padding=(1,1))
            self._block2.pack(side="left", padx=8, fill="x", expand=True)

        self._spec_block1 = [
            ("arrival","Arrival"),
            ("last","Last exec px"),
            ("base","Base executed"),
            ("quote","Quote executed"),
        ]
        self._spec_block2 = [
            ("touch","Touch (old → new)"),
            ("spread","Spread (old → new)"),
            ("vwap","VWAP"),
            ("imp_cost","Impact cost"),
        ]
        self._rows_b1 = self._make_rows(self._block1, self._spec_block1)
        self._rows_b2 = self._make_rows(self._block2, self._spec_block2) if two_blocks else {}
        return stats_outer

    def _make_rows(self, parent: ttk.Frame, spec: List[Tuple[str, str]]):
        rows = {}
        for k, label in spec:
            row = ttk.Frame(parent, padding=(4,2), style="StatRow.TFrame")
            row.pack(side="top", anchor="center", padx=2, pady=1, fill="x")
            row.columnconfigure(0, weight=0, minsize=180)
            row.columnconfigure(1, weight=1)

            name = ttk.Label(row, text=label, style="StatName.TLabel", anchor="w")
            name.grid(row=0, column=0, sticky="w")

            val_frame = ttk.Frame(row, style="StatRow.TFrame")
            val_frame.grid(row=0, column=1, sticky="e", padx=(4,0))

            price_var = tk.StringVar(value="—")
            price_lbl = ttk.Label(val_frame, textvariable=price_var, style="StatValue.TLabel", anchor="e")
            price_lbl.pack(side="left")

            pct_var = tk.StringVar(value="")
            pct_lbl = ttk.Label(val_frame, textvariable=pct_var, style="StatValue.TLabel", anchor="e")
            pct_lbl.pack(side="left", padx=(8,0))

            rows[k] = {"row": row, "price_lbl": price_lbl, "price_var": price_var,
                       "pct_lbl": pct_lbl, "pct_var": pct_var, "val_frame": val_frame}
        return rows

    # ---------- plotting / hover ----------
    def _redraw_depth(self, snapshot: Optional[Dict[str, List[List[float]]]]):
        self._ax.clear()
        self._ax.set_title("Depth (Cumulative Base Qty vs Price)")
        self._ax.set_xlabel("Price"); self._ax.set_ylabel("Cumulative Base Qty")
        if not snapshot:
            self._fig.set_constrained_layout(True); self._canvas.draw_idle(); return

        bids = snapshot["bids"]; asks = snapshot["asks"]
        b_px, b_sz, b_cum, a_px, a_sz, a_cum, *_ = ladder_to_arrays(bids, asks)

        if b_px.size:
            self._ax.fill_between(b_px, b_cum, step="post", alpha=0.35, label="Bids", color=BLOOM_GREEN)
            self._ax.plot(b_px, b_cum, drawstyle="steps-post", color=BLOOM_GREEN, linewidth=1.4)
        if a_px.size:
            self._ax.fill_between(a_px, a_cum, step="post", alpha=0.35, label="Asks", color=BLOOM_RED)
            self._ax.plot(a_px, a_cum, drawstyle="steps-post", color=BLOOM_RED, linewidth=1.4)

        self._ax.legend(loc="best")
        self._fig.set_constrained_layout(True)
        self._canvas.draw_idle()

    def _on_hover(self, event):
        if event.inaxes != self._ax or self._snapshot is None:
            if self._hover_ann.get_visible():
                self._hover_ann.set_visible(False); self._hover_marker.set_data([], []); self._canvas.draw_idle()
            return
        bids = self._snapshot["bids"]; asks = self._snapshot["asks"]
        b_px, b_sz, b_cum, a_px, a_sz, a_cum, best_bid, best_ask, mid = ladder_to_arrays(bids, asks)
        px = event.xdata
        if px is None or not np.isfinite(px) or not np.isfinite(mid):
            return

        nearest_text = None; nearest_xy=None; best_dist=float("inf"); in_consumed=False

        if b_px.size:
            idx = np.searchsorted(-b_px[::-1], -px)
            idx = max(0, min(len(b_px)-1, len(b_px)-1-idx))
            dist = abs(b_px[idx] - px)
            if dist < best_dist:
                best_dist = dist
                rng = (b_px[idx]/mid - 1.0)*100.0
                nearest_text = f"Range  {rng:+.3f}%\nPrice  {fmt_px(b_px[idx])}\nAmount {fmt_qty(b_sz[idx])}"
                nearest_xy = (b_px[idx], b_cum[idx])

        if a_px.size:
            idx2 = np.searchsorted(a_px, px)
            idx2 = max(0, min(len(a_px)-1, idx2))
            dist2 = abs(a_px[idx2] - px)
            if dist2 < best_dist:
                best_dist = dist2
                rng = (a_px[idx2]/mid - 1.0)*100.0
                nearest_text = f"Range  {rng:+.3f}%\nPrice  {fmt_px(a_px[idx2])}\nAmount {fmt_qty(a_sz[idx2])}"
                nearest_xy = (a_px[idx2], a_cum[idx2])

        if nearest_text and nearest_xy:
            if self._consumed is not None:
                lo, hi = self._consumed["px_min"], self._consumed["px_max"]
                in_consumed = (lo <= nearest_xy[0] <= hi)
                if in_consumed: nearest_text = "Consumed\n" + nearest_text
            self._hover_ann.xy = nearest_xy
            self._hover_ann.set_text(nearest_text)
            self._hover_ann.set_visible(True)
            self._hover_marker.set_data([nearest_xy[0]],[nearest_xy[1]])
            self._hover_ann.get_bbox_patch().set_facecolor(BG_PANEL if not in_consumed else BLOOM_AMBER)
            self._hover_ann.get_bbox_patch().set_alpha(0.98)
            self._canvas.draw_idle()

    # ---------- actions ----------
    def _load_snapshot(self):
        try:
            ex = self.exchange_var.get().strip(); sym = self.symbol_var.get().strip()
            self.base_unit, self.quote_unit = parse_units(sym)
            self._snapshot = fetch_snapshot(ex, sym, limit=1000)
            self._clear_yellow(); self._redraw_depth(self._snapshot); self._set_stats_empty()
        except Exception as e:
            messagebox.showerror("Error", f"{type(e).__name__}: {e}")

    def _do_instant_impact(self):
        if not self._snapshot:
            messagebox.showwarning("No snapshot", "Click 'Snapshot OB' first."); return
        try:
            side = self.side_var.get()
            q = float(self.quote_qty_var.get())
            if q <= 0: raise ValueError("Quote quantity must be positive.")
            res = simulate_instant_impact(self._snapshot["bids"], self._snapshot["asks"], side, q)
            self._clear_yellow(); self._highlight_consumed(res); self._fill_stats_from_result(res, q)
        except Exception as e:
            messagebox.showerror("Error", f"{type(e).__name__}: {e}")

    def _do_volume_for_impact(self):
        if not self._snapshot:
            messagebox.showwarning("No snapshot", "Click 'Snapshot OB' first."); return
        try:
            side = self.ladder_side_var.get()
            pct = abs(float(self.impact_pct_var.get()))
            res = volume_for_target_impact(self._snapshot["bids"], self._snapshot["asks"], side, pct)
            self._clear_yellow(); self._highlight_consumed(res); self._fill_stats_from_result(res, res.quote_spent)
        except Exception as e:
            messagebox.showerror("Error", f"{type(e).__name__}: {e}")

    # ---------- visuals ----------
    def _set_stats_empty(self):
        for section in (self._rows_b1, self._rows_b2):
            for _, d in section.items():
                d["price_var"].set("—"); d["pct_var"].set("")

    def _clear_yellow(self):
        for p in self._yellow_patches:
            try: p.remove()
            except Exception: pass
        self._yellow_patches = []; self._consumed = None
        self._clear_plot_helpers()

    def _clear_plot_helpers(self):
        for k in ("arrival_v","last_v","arr_last_arrow","arr_last_text"):
            artist = self._plot_art.get(k)
            if artist is not None:
                try: artist.remove()
                except Exception: pass
            self._plot_art[k] = None
        self._fig.canvas.draw_idle()

    def _highlight_consumed(self, res: ImpactResult):
        bids = self._snapshot["bids"]; asks = self._snapshot["asks"]
        b_px, b_sz, b_cum, a_px, a_sz, a_cum, *_ = ladder_to_arrays(bids, asks)
        if res.side == "buy" and a_px.size:
            mask = (a_px >= res.consumed_min_px - 1e-12) & (a_px <= res.consumed_max_px + 1e-12)
            if mask.any():
                patch = self._ax.fill_between(a_px[mask], a_cum[mask], step="post",
                                              color=BLOOM_AMBER, alpha=0.35, label="Consumed")
                self._yellow_patches.append(patch)
                self._consumed = {"side":"buy", "px_min": float(a_px[mask][0]), "px_max": float(a_px[mask][-1])}
        elif res.side == "sell" and b_px.size:
            mask = (b_px <= res.consumed_max_px + 1e-12) & (b_px >= res.consumed_min_px - 1e-12)
            if mask.any():
                patch = self._ax.fill_between(b_px[mask], b_cum[mask], step="post",
                                              color=BLOOM_AMBER, alpha=0.35, label="Consumed")
                self._yellow_patches.append(patch)
                self._consumed = {"side":"sell", "px_min": float(b_px[mask][-1]), "px_max": float(b_px[mask][0])}
        for line in self._ax.lines: line.set_zorder(3)
        self._fig.set_constrained_layout(True); self._canvas.draw_idle()

    def _draw_arrival_last_helpers(self, res: ImpactResult):
        x_arrival = res.arrival_price; x_last = res.consumed_to_price
        if not (np.isfinite(x_arrival) and np.isfinite(x_last)): return
        self._plot_art["arrival_v"] = self._ax.axvline(x_arrival, color=BLOOM_AMBER, lw=1.6, label="_nolegend_")
        self._plot_art["last_v"]    = self._ax.axvline(x_last,    color=BLOOM_AMBER, lw=1.6, label="_nolegend_")
        ylo, yhi = self._ax.get_ylim()
        y = (ylo*0.7 + yhi*0.3)
        delta_pct = (x_last/x_arrival - 1.0)*100.0
        color = BLOOM_GREEN_H if delta_pct >= 0 else BLOOM_RED_H
        arrow = FancyArrowPatch((min(x_arrival, x_last), y), (max(x_arrival, x_last), y),
                                arrowstyle="<->", mutation_scale=12, lw=1.6,
                                color=color, alpha=0.95, zorder=6)
        self._ax.add_patch(arrow)
        self._plot_art["arr_last_arrow"] = arrow
        txt = self._ax.text((x_arrival+x_last)/2.0, y + (yhi-ylo)*0.01, f"{delta_pct:+.4f}%",
                            ha="center", va="bottom", color=color, fontsize=11,
                            fontweight="bold", zorder=7)
        self._plot_art["arr_last_text"] = txt
        self._ax.legend(loc="best"); self._fig.canvas.draw_idle()

    # ---------- fillers ----------
    def _set_pct_label_style(self, lbl: ttk.Label, value_float: float):
        if not np.isfinite(value_float):
            lbl.configure(style="StatValue.TLabel"); return
        lbl.configure(style="StatValueGreen.TLabel" if value_float > 0
                      else "StatValueRed.TLabel" if value_float < 0
                      else "StatValue.TLabel")

    def _fill_stats_from_result(self, res: ImpactResult, quote_in: float):
        bu, qu = self.base_unit, self.quote_unit
        price_unit = f" {qu}"

        # Block 1
        self._rows_b1["arrival"]["price_var"].set(f"{fmt_px(res.arrival_price)}{price_unit}")
        self._rows_b1["arrival"]["pct_var"].set("")
        last_pct = (res.consumed_to_price / res.arrival_price - 1.0) * 100.0 if np.isfinite(res.arrival_price) else np.nan
        self._rows_b1["last"]["price_var"].set(f"{fmt_px(res.consumed_to_price)}{price_unit}")
        self._rows_b1["last"]["pct_var"].set(fmt_pct4_signed(last_pct))   # SIGNED
        self._set_pct_label_style(self._rows_b1["last"]["pct_lbl"], last_pct)
        self._rows_b1["base"]["price_var"].set(f"{fmt_qty(res.base_executed)} {bu}")
        self._rows_b1["base"]["pct_var"].set("")
        self._rows_b1["quote"]["price_var"].set(f"{quote_in:,.2f} {qu}")
        self._rows_b1["quote"]["pct_var"].set("")

        # Block 2
        touch_old = f"{fmt_px(res.old_best_bid)} / {fmt_px(res.old_best_ask)}{price_unit}"
        touch_new = f"{fmt_px(res.new_best_bid)} / {fmt_px(res.new_best_ask)}{price_unit}"
        self._rows_b2["touch"]["price_var"].set(f"{touch_old}  →  {touch_new}")
        self._rows_b2["touch"]["pct_var"].set("")
        sp_old = (res.old_best_ask - res.old_best_bid)
        sp_new = (res.new_best_ask - res.new_best_bid)
        mid_old = (res.old_best_bid + res.old_best_ask)/2.0 if np.isfinite(res.old_best_bid) and np.isfinite(res.old_best_ask) else np.nan
        old_bps = (sp_old/mid_old*1e4) if (np.isfinite(sp_old) and np.isfinite(mid_old) and mid_old>0) else np.nan
        new_bps = (sp_new/mid_old*1e4) if (np.isfinite(sp_new) and np.isfinite(mid_old) and mid_old>0) else np.nan
        spread_text = (f"{sp_old:,.2f} {qu} → {sp_new:,.2f} {qu}    "
                       f"{fmt_bps1_abs(old_bps)} -> {fmt_bps1_abs(new_bps)}")
        self._rows_b2["spread"]["price_var"].set(spread_text)
        self._rows_b2["spread"]["pct_var"].set("")
        vwap_pct = (res.vwap_price / res.arrival_price - 1.0) * 100.0 if np.isfinite(res.arrival_price) else np.nan
        self._rows_b2["vwap"]["price_var"].set(f"{fmt_px(res.vwap_price)}{price_unit}")
        self._rows_b2["vwap"]["pct_var"].set(fmt_pct4_signed(vwap_pct))   # SIGNED
        self._set_pct_label_style(self._rows_b2["vwap"]["pct_lbl"], vwap_pct)
        imp_pct_of_quote = (res.impact_cost_quote / quote_in * 100.0) if quote_in > 0 else np.nan
        self._rows_b2["imp_cost"]["price_var"].set(f"{res.impact_cost_quote:,.2f} {qu}  {fmt_pct4_plain(imp_pct_of_quote)}")
        self._rows_b2["imp_cost"]["pct_var"].set("")
        self._rows_b2["imp_cost"]["price_lbl"].configure(style="StatValueRed.TLabel")
        self._draw_arrival_last_helpers(res)

    # ---------- resize ----------
    def _on_resize(self, _event):
        if not hasattr(self, "_canvas_widget") or self._fig is None: return
        w = max(self._canvas_widget.winfo_width(), 300)
        h = max(self._canvas_widget.winfo_height(), 260)
        dpi = self._fig.get_dpi()
        self._fig.set_size_inches(w/dpi, h/dpi, forward=True)
        self._fig.set_constrained_layout(True)
        self._canvas.draw_idle()

# ---------- Tab 2 (Multi / SOR) ----------
class MultiVenueTab(ttk.Frame):
    def __init__(self, master, parent_app: OrderBookImpactApp):
        super().__init__(master)
        self.parent_app = parent_app
        self.base_unit = "BASE"; self.quote_unit = "QUOTE"

        self._mono_snapshot: Optional[Dict[str, List[List[float]]]] = None
        self._agg_snapshot: Optional[Dict[str, List[List[float]]]] = None
        self._mono_fig = None; self._mono_ax = None; self._mono_canvas = None
        self._agg_fig = None; self._agg_ax = None; self._agg_canvas = None
        self._mono_yellows = []; self._agg_yellows = []
        self._mono_art = {"arrival_v":None, "last_v":None, "arr_last_arrow":None, "arr_last_text":None}
        self._agg_art  = {"arrival_v":None, "last_v":None, "arr_last_arrow":None, "arr_last_text":None}
        self._venue_vars: Dict[str, tk.BooleanVar] = {}
        self._venue_widgets: Dict[str, ttk.Checkbutton] = {}
        self._venue_status: Dict[str, str] = {}  # "green" | "red" | "default"

        self._build_controls()
        self._build_plots_and_stats()

    # ---------- UI ----------
    def _build_controls(self):
        bar = ttk.Frame(self, padding=(10,6)); bar.pack(side="top", fill="x")

        # Group 1 (exchange/symbol + snapshot)
        g1 = ttk.Frame(bar, padding=(2,1)); g1.pack(side="left")
        ttk.Label(g1, text="Exchange:").grid(row=0, column=0, sticky="e", padx=5, pady=2)
        self.exchange_var = tk.StringVar(value="binance")
        ttk.Entry(g1, textvariable=self.exchange_var, width=14, style="Dark.TEntry").grid(row=0, column=1, padx=5, pady=2)
        ttk.Label(g1, text="Symbol:").grid(row=0, column=2, sticky="e", padx=5, pady=2)
        self.symbol_var = tk.StringVar(value="BTC/USDT")
        ttk.Entry(g1, textvariable=self.symbol_var, width=14, style="Dark.TEntry").grid(row=0, column=3, padx=5, pady=2)
        ttk.Button(g1, text="Snapshot OBs", style="Bloom.Blue.TButton", command=self._load_snapshots)\
            .grid(row=1, column=0, columnspan=4, pady=(6,2))

        ttk.Separator(bar, orient="vertical", style="Bloom.TSeparator").pack(side="left", fill="y", padx=10, pady=2)

        # Group 2 (side + quote + calc)
        g2 = ttk.Frame(bar, padding=(2,1)); g2.pack(side="left")
        self.side_var = tk.StringVar(value="buy")
        self.buy_rb  = ttk.Radiobutton(g2, text="Buy", value="buy", variable=self.side_var, style="Slim.TRadiobutton")
        self.sell_rb = ttk.Radiobutton(g2, text="Sell", value="sell", variable=self.side_var, style="Slim.TRadiobutton")
        self.buy_rb.grid(row=0, column=0, padx=6)
        self.sell_rb.grid(row=0, column=1, padx=6)
        self.buy_rb.bind("<Enter>", lambda e: self.buy_rb.configure(style="HoverRed.TRadiobutton"))
        self.buy_rb.bind("<Leave>", lambda e: self.buy_rb.configure(style="Slim.TRadiobutton"))
        self.sell_rb.bind("<Enter>", lambda e: self.sell_rb.configure(style="HoverGreen.TRadiobutton"))
        self.sell_rb.bind("<Leave>", lambda e: self.sell_rb.configure(style="Slim.TRadiobutton"))

        ttk.Label(g2, text="Quote Qty:").grid(row=0, column=2, sticky="e", padx=6)
        self.quote_qty_var = tk.DoubleVar(value=1_000_000.0)
        ttk.Entry(g2, textvariable=self.quote_qty_var, width=14, style="Dark.TEntry").grid(row=0, column=3, padx=6)
        ttk.Button(g2, text="Run Instant Impact (mono vs multi)", style="Bloom.Green.TButton",
                   command=self._run_dual_impact).grid(row=1, column=0, columnspan=4, pady=(6,2))

        ttk.Separator(bar, orient="vertical", style="Bloom.TSeparator").pack(side="left", fill="y", padx=10, pady=2)

        # Group 3 (target impact; with "apply to")
        g3 = ttk.Frame(bar, padding=(2,1)); g3.pack(side="left")
        self.ladder_side_var = tk.StringVar(value="asks")
        self.asks_rb = ttk.Radiobutton(g3, text="Asks (push up)", value="asks", variable=self.ladder_side_var,
                                       style="Slim.TRadiobutton")
        self.bids_rb = ttk.Radiobutton(g3, text="Bids (push down)", value="bids", variable=self.ladder_side_var,
                                       style="Slim.TRadiobutton")
        self.asks_rb.grid(row=0, column=0, padx=6)
        self.bids_rb.grid(row=0, column=1, padx=6)
        ttk.Label(g3, text="Impact %:").grid(row=0, column=2, sticky="e", padx=6)
        self.impact_pct_var = tk.DoubleVar(value=0.03)
        ttk.Entry(g3, textvariable=self.impact_pct_var, width=10, style="Dark.TEntry").grid(row=0, column=3, padx=6)

        ttk.Label(g3, text="Apply to:").grid(row=0, column=4, sticky="e", padx=(14,6))
        self.apply_to_var = tk.StringVar(value="mono")
        self.apply_to_cb = ttk.Combobox(g3, textvariable=self.apply_to_var, width=12,
                                        values=["mono","aggregated"], state="readonly")
        self.apply_to_cb.grid(row=0, column=5, padx=6)

        ttk.Button(g3, text="Volume for impact (cross-apply)", style="Bloom.Amber.TButton",
                   command=self._volume_for_impact_cross).grid(row=1, column=0, columnspan=6, pady=(6,2))

        # Row under the 3 buttons — checkboxes of fixed venues
        checks_row = ttk.Frame(self, padding=(10, 0)); checks_row.pack(side="top", fill="x")
        ttk.Label(checks_row, text="Select venues to aggregate:").pack(side="left", padx=(0,12))
        grid = ttk.Frame(checks_row); grid.pack(side="left")
        for i, ven in enumerate(TOP10_VENUES):
            var = tk.BooleanVar(value=(ven in ("binance","okx","bybit")))
            self._venue_vars[ven] = var
            cb = ttk.Checkbutton(grid, text=ven, variable=var, style="Venue.Default.TCheckbutton")
            cb.grid(row=i//5, column=i%5, sticky="w", padx=8, pady=2)
            cb.bind("<Enter>", lambda e, w=cb: w.configure(style="Venue.Amber.TCheckbutton"))
            cb.bind("<Leave>", lambda e, w=cb, name=ven: self._apply_venue_style(name))
            self._venue_widgets[ven] = cb
            self._venue_status.setdefault(ven, "default")

    def _apply_venue_style(self, ven: str):
        cb = self._venue_widgets.get(ven)
        if not cb: return
        st = self._venue_status.get(ven, "default")
        if st == "green":
            cb.configure(style="Venue.Green.TCheckbutton")
        elif st == "red":
            cb.configure(style="Venue.Red.TCheckbutton")
        else:
            cb.configure(style="Venue.Default.TCheckbutton")

    def _build_plots_and_stats(self):
        # Layout: grid with 2 columns (mono | aggregated) and 2 rows (plots | results)
        container = ttk.Frame(self, padding=(6, 6))
        container.pack(side="top", fill="both", expand=True)

        # two columns for side-by-side charts
        container.columnconfigure(0, weight=1)
        container.columnconfigure(1, weight=1)
        # row 0 = charts, row 1 = results
        container.rowconfigure(0, weight=1)
        container.rowconfigure(1, weight=0, minsize=170)  # results always visible

        # --- Mono plot (left)
        mono_frame = ttk.Frame(container, padding=(10, 6))
        mono_frame.grid(row=0, column=0, sticky="nsew")
        self._mono_fig = plt.Figure(dpi=100, constrained_layout=True)
        self._mono_ax = self._mono_fig.add_subplot(111)
        self._mono_canvas = FigureCanvasTkAgg(self._mono_fig, master=mono_frame)
        self._mono_canvas.get_tk_widget().pack(side="top", fill="both", expand=True)
        NavigationToolbar2Tk(self._mono_canvas, mono_frame).update()

        # --- Aggregated plot (right)
        agg_frame = ttk.Frame(container, padding=(10, 6))
        agg_frame.grid(row=0, column=1, sticky="nsew")
        self._agg_fig = plt.Figure(dpi=100, constrained_layout=True)
        self._agg_ax = self._agg_fig.add_subplot(111)
        self._agg_canvas = FigureCanvasTkAgg(self._agg_fig, master=agg_frame)
        self._agg_canvas.get_tk_widget().pack(side="top", fill="both", expand=True)
        NavigationToolbar2Tk(self._agg_canvas, agg_frame).update()

        # --- Results (spans both columns)
        stats_outer = ttk.Frame(container, padding=(10, 6))
        stats_outer.grid(row=1, column=0, columnspan=2, sticky="nsew")
        stats_center = ttk.Frame(stats_outer);
        stats_center.pack(expand=True)
        self._result_block = ttk.Frame(stats_center, padding=(1, 1))
        self._result_block.pack(side="top")
        spec = [
            ("base", "Base executed"),
            ("quote", "Quote executed"),
            ("vwap_mono", "Mono-venue VWAP"),
            ("vwap_multi", "Multi-venue VWAP (±diff%)"),
            ("imp_mono", "Impact cost mono"),
            ("imp_multi", "Impact cost multi"),
            ("gain_usd", "Gain USD (±%)"),
        ]
        self._rows = self._make_rows(self._result_block, spec)

        self.bind("<Configure>", self._on_resize)
        self._redraw_depth(self._mono_ax, self._mono_canvas, None, title="Mono-venue Depth")
        self._redraw_depth(self._agg_ax, self._agg_canvas, None, title="Aggregated Depth (Selected Venues)")
        self._set_center_results_empty()

    def _make_rows(self, parent: ttk.Frame, spec: List[Tuple[str, str]]):
        rows = {}
        for k, label in spec:
            row = ttk.Frame(parent, padding=(4,2), style="StatRow.TFrame")
            row.pack(side="top", anchor="center", padx=2, pady=1)
            name = ttk.Label(row, text=label, style="StatName.TLabel", anchor="center")
            name.grid(row=0, column=0, sticky="e")
            val_frame = ttk.Frame(row, style="StatRow.TFrame")
            val_frame.grid(row=0, column=1, sticky="w", padx=(12,0))

            price_var = tk.StringVar(value="—")
            price_lbl = ttk.Label(val_frame, textvariable=price_var, style="StatValue.TLabel")
            price_lbl.pack(side="left")

            pct_var = tk.StringVar(value="")
            pct_lbl = ttk.Label(val_frame, textvariable=pct_var, style="StatValue.TLabel")
            pct_lbl.pack(side="left", padx=(8,0))

            rows[k] = {"row": row, "price_lbl": price_lbl, "price_var": price_var,
                       "pct_lbl": pct_lbl, "pct_var": pct_var}
        return rows

    # ---------- fetch / aggregate ----------
    def _selected_venues(self) -> List[str]:
        chosen = [v for v, var in self._venue_vars.items() if var.get()]
        ex_typed = self.exchange_var.get().strip()
        if ex_typed not in chosen:
            chosen.append(ex_typed)  # ensure typed venue is included
        return chosen

    def _load_snapshots(self):
        try:
            sym = self.symbol_var.get().strip()
            self.base_unit, self.quote_unit = parse_units(sym)
            venues = self._selected_venues()

            successes: List[Tuple[str, Dict[str, List[List[float]]]]] = []
            for ven in venues:
                try:
                    ob = fetch_snapshot(ven, sym, limit=1000)
                    successes.append((ven, ob))
                    self._venue_status[ven] = "green"
                except Exception:
                    self._venue_status[ven] = "red"

            # apply persisted styles to all visible checkboxes
            for ven in TOP10_VENUES:
                self._apply_venue_style(ven)

            if not successes:
                raise RuntimeError("No snapshots fetched. Check symbol/venues.")

            # Mono is the typed exchange if successful, else first success
            mono_ex = self.exchange_var.get().strip()
            mono_pair = next(((v, ob) for v, ob in successes if v == mono_ex), successes[0])
            self._mono_snapshot = mono_pair[1]
            self._agg_snapshot = aggregate_orderbooks([ob for _, ob in successes], depth=1000)

            # Draw both (full OB)
            self._clear_yellow(self._mono_ax, self._mono_yellows, self._mono_art, self._mono_fig)
            self._redraw_depth(self._mono_ax, self._mono_canvas, self._mono_snapshot, title=f"Mono-venue Depth — {mono_pair[0]}")

            self._clear_yellow(self._agg_ax,  self._agg_yellows, self._agg_art,  self._agg_fig)
            self._redraw_depth(self._agg_ax,  self._agg_canvas,  self._agg_snapshot, title="Aggregated Depth (Selected Venues)")

            self._set_center_results_empty()
        except Exception as e:
            messagebox.showerror("Error", f"{type(e).__name__}: {e}")

    # ---------- core calcs ----------
    def _run_dual_impact(self):
        if self._mono_snapshot is None or self._agg_snapshot is None:
            messagebox.showwarning("No snapshots", "Click 'Snapshot OBs' first."); return
        try:
            side = self.side_var.get()
            q = float(self.quote_qty_var.get())
            if q <= 0: raise ValueError("Quote quantity must be positive.")

            res_mono = simulate_instant_impact(self._mono_snapshot["bids"], self._mono_snapshot["asks"], side, q)
            res_agg  = simulate_instant_impact(self._agg_snapshot["bids"],  self._agg_snapshot["asks"],  side, q)

            # visuals: highlight + helpers on both
            self._clear_yellow(self._mono_ax, self._mono_yellows, self._mono_art, self._mono_fig)
            self._highlight_consumed(self._mono_snapshot, self._mono_ax, self._mono_yellows, res_mono)
            self._draw_arrival_last(self._mono_ax, self._mono_art, self._mono_fig, res_mono)

            self._clear_yellow(self._agg_ax, self._agg_yellows, self._agg_art, self._agg_fig)
            self._highlight_consumed(self._agg_snapshot,  self._agg_ax,  self._agg_yellows, res_agg)
            self._draw_arrival_last(self._agg_ax,  self._agg_art,  self._agg_fig,  res_agg)

            self._fill_center_results(res_mono, res_agg, q)
        except Exception as e:
            messagebox.showerror("Error", f"{type(e).__name__}: {e}")

    def _volume_for_impact_cross(self):
        if self._mono_snapshot is None or self._agg_snapshot is None:
            messagebox.showwarning("No snapshots", "Click 'Snapshot OBs' first."); return
        try:
            ladder_side = self.ladder_side_var.get()  # "asks" => buy ; "bids" => sell
            side = "buy" if ladder_side == "asks" else "sell"
            pct = abs(float(self.impact_pct_var.get()))
            apply_to = self.apply_to_var.get()  # "mono" or "aggregated"

            # compute quote on selected book
            src = self._mono_snapshot if apply_to == "mono" else self._agg_snapshot
            res_src = volume_for_target_impact(src["bids"], src["asks"], ladder_side, pct)
            q = float(res_src.quote_spent)

            # apply that quote to the other book
            dst = self._agg_snapshot if apply_to == "mono" else self._mono_snapshot
            try:
                res_dst = simulate_instant_impact(dst["bids"], dst["asks"], side, q)
            except RuntimeError as e:
                raise RuntimeError(f"Not enough depth on the {'aggregated' if apply_to=='mono' else 'mono'} book to execute the same quote ({q:,.2f}).") from e

            # order for results: mono vs multi
            if apply_to == "mono":
                res_mono, res_agg = res_src, res_dst
            else:
                res_mono, res_agg = res_dst, res_src

            # visuals
            self._clear_yellow(self._mono_ax, self._mono_yellows, self._mono_art, self._mono_fig)
            self._highlight_consumed(self._mono_snapshot, self._mono_ax, self._mono_yellows, res_mono)
            self._draw_arrival_last(self._mono_ax, self._mono_art, self._mono_fig, res_mono)

            self._clear_yellow(self._agg_ax, self._agg_yellows, self._agg_art, self._agg_fig)
            self._highlight_consumed(self._agg_snapshot,  self._agg_ax,  self._agg_yellows, res_agg)
            self._draw_arrival_last(self._agg_ax,  self._agg_art,  self._agg_fig,  res_agg)

            self._fill_center_results(res_mono, res_agg, q)
        except Exception as e:
            messagebox.showerror("Error", f"{type(e).__name__}: {e}")

    def _volume_for_impact_multi(self):
        return self._volume_for_impact_cross()

    # ---------- center results (Tab 2 only) ----------
    def _set_center_results_empty(self):
        for _, d in self._rows.items():
            d["price_var"].set("—"); d["pct_var"].set("")

    def _fill_center_results(self, mono: ImpactResult, multi: ImpactResult, quote_in: float):
        bu, qu = self.base_unit, self.quote_unit

        # Base & Quote (keep as-is)
        self._rows["base"]["price_var"].set(f"{fmt_qty(multi.base_executed)} {bu}")
        self._rows["base"]["pct_var"].set("")
        self._rows["quote"]["price_var"].set(f"{quote_in:,.2f} {qu}")
        self._rows["quote"]["pct_var"].set("")

        # VWAPs (keep as-is)
        self._rows["vwap_mono"]["price_var"].set(f"{fmt_px(mono.vwap_price)} {qu}")
        self._rows["vwap_mono"]["pct_var"].set("")
        diff_pct = (multi.vwap_price / mono.vwap_price - 1.0) * 100.0 if np.isfinite(multi.vwap_price) and np.isfinite(mono.vwap_price) and mono.vwap_price > 0 else np.nan
        self._rows["vwap_multi"]["price_var"].set(f"{fmt_px(multi.vwap_price)} {qu}")
        self._rows["vwap_multi"]["pct_var"].set(fmt_pct4_signed(diff_pct))
        if np.isfinite(diff_pct):
            self._rows["vwap_multi"]["pct_lbl"].configure(
                style="StatValueGreen.TLabel" if diff_pct > 0 else "StatValueRed.TLabel" if diff_pct < 0 else "StatValue.TLabel"
            )
        else:
            self._rows["vwap_multi"]["pct_lbl"].configure(style="StatValue.TLabel")

        # --- Rebased impact costs: compare both books to the same arrival ---
        side = self.side_var.get()
        if side == "buy":
            common_arrival = min(mono.arrival_price, multi.arrival_price)
            imp_mono = max(mono.vwap_price - common_arrival, 0.0) * mono.base_executed
            imp_multi = max(multi.vwap_price - common_arrival, 0.0) * multi.base_executed
        else:  # sell
            common_arrival = max(mono.arrival_price, multi.arrival_price)
            imp_mono = max(common_arrival - mono.vwap_price, 0.0) * mono.base_executed
            imp_multi = max(common_arrival - multi.vwap_price, 0.0) * multi.base_executed

        self._rows["imp_mono"]["price_var"].set(f"{imp_mono:,.2f} {qu}")
        self._rows["imp_mono"]["pct_var"].set("")
        self._rows["imp_multi"]["price_var"].set(f"{imp_multi:,.2f} {qu}")
        self._rows["imp_multi"]["pct_var"].set("")

        # Gain USD — keep (benefit of SOR on executed base)
        gain_usd = (mono.vwap_price - multi.vwap_price) * multi.base_executed
        gain_pct = (gain_usd / quote_in * 100.0) if quote_in > 0 else np.nan
        self._rows["gain_usd"]["price_var"].set(f"{gain_usd:,.2f} {qu}")
        self._rows["gain_usd"]["pct_var"].set(fmt_pct4_signed(gain_pct))
        self._rows["gain_usd"]["pct_lbl"].configure(style="StatValueGreen.TLabel")

    # ---------- plotting helpers ----------
    def _redraw_depth(self, ax, canvas, snapshot: Optional[Dict[str, List[List[float]]]], title: str):
        ax.clear()
        ax.set_title(title)
        ax.set_xlabel("Price"); ax.set_ylabel("Cumulative Base Qty")
        if snapshot:
            bids = snapshot["bids"]; asks = snapshot["asks"]
            b_px, b_sz, b_cum, a_px, a_sz, a_cum, *_ = ladder_to_arrays(bids, asks)
            if b_px.size:
                ax.fill_between(b_px, b_cum, step="post", alpha=0.35, label="Bids", color=BLOOM_GREEN)
                ax.plot(b_px, b_cum, drawstyle="steps-post", color=BLOOM_GREEN, linewidth=1.4)
            if a_px.size:
                ax.fill_between(a_px, a_cum, step="post", alpha=0.35, label="Asks", color=BLOOM_RED)
                ax.plot(a_px, a_cum, drawstyle="steps-post", color=BLOOM_RED, linewidth=1.4)
            ax.legend(loc="best")
        canvas.draw_idle()

    def _clear_yellow(self, ax, patches_list, art_dict, fig):
        for p in patches_list:
            try: p.remove()
            except Exception: pass
        patches_list.clear()
        for k in ("arrival_v","last_v","arr_last_arrow","arr_last_text"):
            artist = art_dict.get(k)
            if artist is not None:
                try: artist.remove()
                except Exception: pass
            art_dict[k] = None
        fig.canvas.draw_idle()

    def _highlight_consumed(self, snapshot, ax, patches_list, res: ImpactResult):
        bids = snapshot["bids"]; asks = snapshot["asks"]
        b_px, b_sz, b_cum, a_px, a_sz, a_cum, *_ = ladder_to_arrays(bids, asks)
        if res.side == "buy" and a_px.size:
            mask = (a_px >= res.consumed_min_px - 1e-12) & (a_px <= res.consumed_max_px + 1e-12)
            if mask.any():
                patch = ax.fill_between(a_px[mask], a_cum[mask], step="post",
                                        color=BLOOM_AMBER, alpha=0.35, label="Consumed")
                patches_list.append(patch)
        elif res.side == "sell" and b_px.size:
            mask = (b_px <= res.consumed_max_px + 1e-12) & (b_px >= res.consumed_min_px - 1e-12)
            if mask.any():
                patch = ax.fill_between(b_px[mask], b_cum[mask], step="post",
                                        color=BLOOM_AMBER, alpha=0.35, label="Consumed")
                patches_list.append(patch)
        for line in ax.lines: line.set_zorder(3)

    def _draw_arrival_last(self, ax, art_dict, fig, res: ImpactResult):
        x_arrival = res.arrival_price; x_last = res.consumed_to_price
        if not (np.isfinite(x_arrival) and np.isfinite(x_last)): return
        art_dict["arrival_v"] = ax.axvline(x_arrival, color=BLOOM_AMBER, lw=1.6, label="_nolegend_")
        art_dict["last_v"]    = ax.axvline(x_last,    color=BLOOM_AMBER, lw=1.6, label="_nolegend_")
        ylo, yhi = ax.get_ylim(); y = (ylo*0.7 + yhi*0.3)
        delta_pct = (x_last/x_arrival - 1.0)*100.0
        color = BLOOM_GREEN_H if delta_pct >= 0 else BLOOM_RED_H
        arrow = FancyArrowPatch((min(x_arrival, x_last), y), (max(x_arrival, x_last), y),
                                arrowstyle="<->", mutation_scale=12, lw=1.6,
                                color=color, alpha=0.95, zorder=6)
        ax.add_patch(arrow); art_dict["arr_last_arrow"] = arrow
        txt = ax.text((x_arrival+x_last)/2.0, y + (yhi-ylo)*0.01, f"{delta_pct:+.4f}%",
                      ha="center", va="bottom", color=color, fontsize=11, fontweight="bold", zorder=7)
        art_dict["arr_last_text"] = txt
        ax.legend(loc="best"); fig.canvas.draw_idle()

    # ---------- resize ----------
    def _on_resize(self, _event):
        for fig, canvas in ((self._mono_fig, self._mono_canvas), (self._agg_fig, self._agg_canvas)):
            if fig is None or canvas is None: continue
            widget = canvas.get_tk_widget()
            w = max(widget.winfo_width(), 300)
            h = max(widget.winfo_height(), 240)
            dpi = fig.get_dpi()
            fig.set_size_inches(w/dpi, h/dpi, forward=True)
            fig.set_constrained_layout(True)
            canvas.draw_idle()

# ---------- Extra: target impact (used by both tabs) ----------
def volume_for_target_impact(bids, asks, ladder_side: str, impact_pct: float) -> ImpactResult:
    b_px, b_sz, b_cum, a_px, a_sz, a_cum, best_bid, best_ask, mid = ladder_to_arrays(bids, asks)
    if not np.isfinite(mid): raise RuntimeError("Order book incomplete (mid undefined).")
    impact_pct = abs(impact_pct)
    target_up = mid * (1.0 + impact_pct/100.0)

    if ladder_side == "asks":
        if a_px.size == 0: not_enough_depth_err("buy")
        arrival = best_ask
        needed_quote = 0.0; vwap_num = 0.0; base_filled = 0.0
        last_px = arrival; new_best_ask = arrival
        consumed_min, consumed_max = arrival, arrival
        for i,(price,size,*_) in enumerate(asks):
            price=float(price); size=float(size)
            if price <= target_up + 1e-12:
                needed_quote += price*size; vwap_num += price*size
                base_filled += size; last_px = price
                consumed_max = max(consumed_max, price)
                new_best_ask = float(asks[i+1][0]) if (i+1) < len(asks) else np.nan
            else:
                break
        if base_filled <= 0.0: raise RuntimeError("Target impact is inside the spread; increase %.")
        if target_up > float(asks[-1][0]) + 1e-12: not_enough_depth_err("buy for target impact")
        vwap = vwap_num/base_filled
        exec_perf_bps = (vwap/arrival - 1.0)*1e4
        impact_touch = (new_best_ask/arrival - 1.0) if np.isfinite(new_best_ask) else float("nan")
        impact_cost_q = max(vwap-arrival,0.0)*base_filled
        return ImpactResult("buy", last_px, vwap, base_filled, needed_quote,
                            best_bid, new_best_ask, (vwap/mid-1.0)*100.0,
                            arrival, exec_perf_bps, (impact_touch*100.0) if np.isfinite(impact_touch) else float("nan"),
                            impact_cost_q, consumed_min, consumed_max,
                            old_best_bid=best_bid, old_best_ask=best_ask)

    # sell target down
    if b_px.size == 0: not_enough_depth_err("sell")
    arrival = best_bid
    target_down = mid * (1.0 - impact_pct/100.0)
    needed_quote = 0.0; vwap_num = 0.0; base_filled = 0.0
    last_px = arrival; new_best_bid = arrival
    consumed_min, consumed_max = arrival, arrival
    for i,(price,size,*_) in enumerate(bids):
        price=float(price); size=float(size)
        if price >= target_down - 1e-12:
            needed_quote += price*size; vwap_num += price*size
            base_filled += size; last_px = price
            consumed_min = min(consumed_min, price)
            new_best_bid = float(bids[i+1][0]) if (i+1) < len(bids) else np.nan
        else:
            break
    if base_filled <= 0.0: raise RuntimeError("Target impact is inside the spread; increase %.")
    if target_down < float(bids[-1][0]) - 1e-12: not_enough_depth_err("sell for target impact")
    vwap = vwap_num/base_filled
    exec_perf_bps = (vwap/arrival - 1.0)*1e4
    impact_touch = (new_best_bid/arrival - 1.0) if np.isfinite(new_best_bid) else float("nan")
    impact_cost_q = max(arrival-vwap,0.0)*base_filled
    return ImpactResult("sell", last_px, vwap, base_filled, needed_quote,
                        new_best_bid, best_ask, (vwap/mid-1.0)*100.0,
                        arrival, exec_perf_bps, (impact_touch*100.0) if np.isfinite(impact_touch) else float("nan"),
                        impact_cost_q, consumed_min, consumed_max,
                        old_best_bid=best_bid, old_best_ask=best_ask)

# ---------- main ----------
if __name__ == "__main__":
    app = OrderBookImpactApp()
    app.mainloop()
