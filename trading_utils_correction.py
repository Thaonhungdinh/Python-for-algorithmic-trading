# trading_utils.py
import math
import ccxt.pro as ccxtpro
import ccxt
import pandas as pd
import numpy as np
from typing import Optional, List, Dict, Tuple

# 1. Historical Data Retrieval
def fetch_ohlcv_data(exchange_name: str,
                     symbol: str,
                     timeframe: str = '5m',
                     limit: int = 1000) -> pd.DataFrame:
    """
    Fetch historical OHLCV candles from a given exchange and symbol.

    Returns a pandas DataFrame with columns:
        ['datetime', 'open', 'high', 'low', 'close', 'volume']

    - 'datetime' is a pandas Timestamp (UTC from the exchange ms timestamp)
    """

    # 1. build the ccxt exchange object from its name
    exchange_class = getattr(ccxt, exchange_name)
    exchange = exchange_class()

    # 2. fetch OHLCV: [ ms, open, high, low, close, volume ]
    raw = exchange.fetch_ohlcv(symbol, timeframe=timeframe, limit=limit)

    # 3. put in DataFrame
    df = pd.DataFrame(
        raw,
        columns=['ms', 'open', 'high', 'low', 'close', 'volume']
    )

    # 4. convert ms -> pandas Timestamp
    df['datetime'] = pd.to_datetime(df['ms'], unit='ms')

    # 5. keep only what the app actually uses
    df = df[['datetime', 'open', 'high', 'low', 'close', 'volume']]

    return df

# 2. Rolling Statistics

def moving_average(series: pd.Series, window: int):
    """
        Rolling mean over last N points. Returns NaN until window is full.
    """
    return series.rolling(window=window).mean()

def rolling_std(series: pd.Series, window: int):
    """
        Rolling standard deviation (volatility proxy).
    """
    return series.rolling(window=window).std()

def max_drawdown(series: pd.Series):
    """
        Maximum drawdown (str) in percent ( e.g. 0.40 = -40%).
        Definition: max peak-to-trough drop / peak.
    """
    running_max = np.maximum.accumulate(series)
    drawdowns = (series - running_max) / running_max
    return str( drawdowns.min() * 100 ) + " %"

# 3. Moving Average Crossover Strategy

def generate_signals(price_series: pd.Series,
                     short_window: int,
                     long_window: int) -> pd.Series:
    """
    Generate +1 on golden cross (short MA crosses above long MA),
    -1 on death cross (short MA crosses below long MA),
     0 otherwise.
    """

    short_ma = price_series.rolling(short_window).mean()
    long_ma = price_series.rolling(long_window).mean()

    prev_short_above = short_ma.shift(1) > long_ma.shift(1)
    curr_short_above = short_ma > long_ma

    buy_signal = (~prev_short_above) & (curr_short_above)   # just crossed up
    sell_signal = (prev_short_above) & (~curr_short_above)  # just crossed down

    signal = pd.Series(0, index=price_series.index, dtype=int)
    signal[buy_signal] = 1
    signal[sell_signal] = -1

    return signal

def backtest_strategy(price_series: pd.Series,
                      signal_series: pd.Series) -> Dict[str, object]:
    """
    Extremely naive backtest:
    - When we get +1, we 'enter long' at that price (if flat).
    - When we get -1, we 'exit' at that price (if long).
    - Ignore shorts for simplicity.

    Returns dict with:
      total_pnl,
      trades: list of dicts {entry_idx, entry_px, exit_idx, exit_px, pnl}
      equity_curve: pd.Series of cumulative PnL over time
    """

    position_open = False
    entry_price = None
    trades = []
    pnl_curve = []

    cum_pnl = 0.0

    for i, (px, sig) in enumerate(zip(price_series, signal_series)):
        # open long
        if (sig == 1) and (not position_open):
            position_open = True
            entry_price = px

        # close long
        elif (sig == -1) and position_open:
            trade_pnl = px - entry_price
            cum_pnl += trade_pnl
            trades.append({
                "entry_idx": i,
                "entry_px": entry_price,
                "exit_idx": i,
                "exit_px": px,
                "pnl": trade_pnl,
            })
            position_open = False
            entry_price = None

        pnl_curve.append(cum_pnl)

    equity_curve = pd.Series(pnl_curve, index=price_series.index)

    return {
        "total_pnl": cum_pnl,
        "trades": trades,
        "equity_curve": equity_curve,
    }



# 4. Stat Arb
def rolling_correlation(series_a: pd.Series,
                        series_b: pd.Series,
                        window: int) -> pd.Series:
    """
    Rolling Pearson correlation between two price series.
    """
    return series_a.rolling(window).corr(series_b)

def identify_pair_trade_signals(series_a: pd.Series,
                                series_b: pd.Series,
                                lookback: int = 50,
                                threshold_sigma: float = 2.0):
    """
    Very simple pairs logic:
    - Compute spread = (A - B).
    - Compute rolling mean and std of spread over 'lookback'.
    - Entry long A / short B if spread << mean - threshold_sigma * std.
    - Entry short A / long B if spread >> mean + threshold_sigma * std.
    - Exit when spread goes back near mean.

    Returns dict with entries, exits for illustration.
    """

    spread = series_a - series_b
    spread_mean = spread.rolling(lookback).mean()
    spread_std = spread.rolling(lookback).std()

    upper_band = spread_mean + threshold_sigma * spread_std
    lower_band = spread_mean - threshold_sigma * spread_std

    signals = pd.Series("HOLD", index=spread.index, dtype=object)

    long_signal = spread < lower_band
    short_signal = spread > upper_band
    exit_signal = (spread < upper_band) & (spread > lower_band)

    signals[long_signal] = "LONG_A_SHORT_B"
    signals[short_signal] = "SHORT_A_LONG_B"
    signals[exit_signal] = "EXIT"

    return {
        "spread": spread,
        "spread_mean": spread_mean,
        "upper_band": upper_band,
        "lower_band": lower_band,
        "signal": signals,
    }

# 6. Collecting Live Trades from a WebSocket Feed
async def collect_trades_loop(
    exchange,
    symbol: str,
    candle_df: Optional[pd.DataFrame] = None,
    max_loops: Optional[int] = None
) -> List[Dict[str, float]]:
    """
    Listen to trades for `symbol` on `exchange` and build a list of cleaned trades.

    We only keep for each trade:
        {
            'timestamp': int,
            'price': float,
            'amount': float
        }

    Behavior:
    - Repeatedly call `await ex.watch_trades(symbol)`.
    - The websocket result can be:
        - one dict (single trade), OR
        - a list of dicts (many trades).
    - We normalize to a list, clean the keys, and append to all_trades.
    - If max_loops is an int N, we stop after N reads and return all_trades.
    - If max_loops is None, this would conceptually run forever
      (we never hit the return in that mode).
    """
    all_trades: List[Dict[str, float]] = []
    loops_done = 0

    while True:
        # 1. get new trades from the exchange websocket
        raw_msg = await exchange.watch_trades(symbol)

        # 2. normalize: ensure we always iterate over a list
        if isinstance(raw_msg, list):
            trades_list = raw_msg
        else:
            trades_list = [raw_msg]

        # 3. clean each trade and add to all_trades
        for trade in trades_list:
            cleaned = {
                'timestamp': int(trade['timestamp']),
                'price': float(trade['price']),
                'amount': float(trade['amount']),
            }
            all_trades.append(cleaned)
            if max_loops is None:
                update_candle(cleaned, candle_df)

        # 4. stopping condition for testing / finite run
        loops_done += 1
        if max_loops is not None and loops_done >= max_loops:
            return all_trades

        # if max_loops is None => loop keeps going forever


# 7. Update Candle
def update_candle(
    trade: Dict[str, float],
    candles_df: Optional[pd.DataFrame]
) -> pd.DataFrame:
    """
    Update (or create) the 1-minute OHLCV candle for a single trade.

    candles_df:
        - index: pandas Timestamp in UTC, floored to the minute
        - columns: ['open', 'high', 'low', 'close', 'volume']
        - may be None or empty at the start

    trade: dict with keys:
        'timestamp' (ms since epoch),
        'price' (float),
        'amount' (float)

    Returns:
        candles_df (same object updated, or a new DataFrame if it was None)
    """

    # If candles_df is None, start a fresh empty DataFrame
    if candles_df is None:
        candles_df = pd.DataFrame(
            columns=['open', 'high', 'low', 'close', 'volume']
        )

    ts_ms = int(trade['timestamp'])
    price = float(trade['price'])
    amount = float(trade['amount'])

    # floor timestamp to the minute (ms -> minute boundary)
    minute_start_ms = (ts_ms // 60000) * 60000
    minute_ts = pd.to_datetime(minute_start_ms, unit='ms', utc=True)

    # If this minute already exists, update the row
    if minute_ts in candles_df.index:
        # existing row
        old_open = candles_df.at[minute_ts, 'open']
        old_high = candles_df.at[minute_ts, 'high']
        old_low = candles_df.at[minute_ts, 'low']
        old_close = candles_df.at[minute_ts, 'close']
        old_vol = candles_df.at[minute_ts, 'volume']

        candles_df.at[minute_ts, 'open'] = old_open  # unchanged
        candles_df.at[minute_ts, 'high'] = max(old_high, price)
        candles_df.at[minute_ts, 'low'] = min(old_low, price)
        candles_df.at[minute_ts, 'close'] = price   # latest price wins
        candles_df.at[minute_ts, 'volume'] = old_vol + amount

    # Otherwise create a brand new candle row for that minute
    else:
        candles_df.loc[minute_ts, 'open'] = price
        candles_df.loc[minute_ts, 'high'] = price
        candles_df.loc[minute_ts, 'low'] = price
        candles_df.loc[minute_ts, 'close'] = price
        candles_df.loc[minute_ts, 'volume'] = amount

    return candles_df

# 8. Orderbook
async def build_order_book(exchange, symbol: str, depth: int = 5):
    """
    Build simplified order book tables (top N levels).
    Returns two DataFrames: bids_df and asks_df.
    """

    # 1. Get snapshot
    ob = await exchange.watch_order_book(symbol)
    bids = ob.get("bids", [])
    asks = ob.get("asks", [])

    # 2. Round and aggregate
    bid_dict = {}
    for price, size in bids:
        p = math.floor(price)
        bid_dict[p] = bid_dict.get(p, 0.0) + float(size)

    ask_dict = {}
    for price, size in asks:
        p = math.ceil(price)
        ask_dict[p] = ask_dict.get(p, 0.0) + float(size)

    # 3. Convert to DataFrames and sort
    bids_df = (
        pd.DataFrame(list(bid_dict.items()), columns=["price", "size"])
        .sort_values("price", ascending=False)
        .head(depth)
        .reset_index(drop=True)
    )

    asks_df = (
        pd.DataFrame(list(ask_dict.items()), columns=["price", "size"])
        .sort_values("price", ascending=True)
        .head(depth)
        .reset_index(drop=True)
    )

    return bids_df, asks_df

# 9. Arbitrage
def find_arbitrage_opportunities(top_books: dict) -> list:
    """
    Scan multiple exchanges' top-of-book quotes and build all possible
    buy/sell combinations.

    Parameters
    ----------
    top_books : dict
        Example:
        {
          "binance": {"bid": 30050.0, "ask": 30049.5},
          "kraken":  {"bid": 30060.0, "ask": 30055.0},
          "coinbase":{"bid": 30058.0, "ask": 30052.0}
        }

        - "bid" = best bid (highest buy price on that exchange)
        - "ask" = best ask (lowest sell price on that exchange)

    Returns
    -------
    opportunities : list of dict
        Each dict looks like:
        {
          "buy_from":  <exchange A>,
          "sell_to":   <exchange B>,
          "buy_ask":   <A's ask>,
          "sell_bid":  <B's bid>,
          "diff":      <B.bid - A.ask>
        }

        We include ALL pairs A != B, regardless of whether diff > 0.
        (You can always filter later.)
    """

    results = []

    # loop over all possible BUY venues
    for buy_exch, quotes_buy in top_books.items():
        buy_ask = quotes_buy["ask"]

        # loop over all possible SELL venues
        for sell_exch, quotes_sell in top_books.items():
            if sell_exch == buy_exch:
                continue  # can't buy and sell on the same venue in this check

            sell_bid = quotes_sell["bid"]

            diff = sell_bid - buy_ask

            results.append({
                "buy_from": buy_exch,
                "sell_to": sell_exch,
                "buy_ask": buy_ask,
                "sell_bid": sell_bid,
                "diff": diff,
            })

    return results