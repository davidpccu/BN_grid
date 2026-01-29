import asyncio
import websockets
import json
import logging
import hmac
import hashlib
import time
import ccxt
import math
import os
import socket
import asyncio

# ==================== 參數配置 ====================
API_KEY = os.getenv("BINANCE_API_KEY")
API_SECRET = os.getenv("BINANCE_API_SECRET")
COIN_NAME = "XRP"  # 交易幣種
CONTRACT_TYPE = "USDC"  # 合約類型：USDT 或 USDC
GRID_SPACING = 0.003  # 網格間距（0.3%）
INITIAL_QUANTITY = 10  # 初始交易數量（幣數）
LEVERAGE = 8  # 槓桿倍數
WEBSOCKET_URL = "wss://fstream.binance.com/ws"  # WebSocket 連線位址
POSITION_THRESHOLD = 350  # 鎖倉閾值
POSITION_LIMIT = 300  # 持倉數量閾值
SYNC_TIME = 10  # 同步時間（秒）
ORDER_FIRST_TIME = 10  # 首單間隔時間（秒）
STARTUP_GRACE_PERIOD = 40  # 啟動寬限期（秒），期間只同步不下單

# ==================== 日誌配置 ====================
# 取得目前腳本檔名（不含副檔名）
script_name = os.path.splitext(os.path.basename(__file__))[0]
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[
        logging.FileHandler(f"log/{script_name}.log"),  # 日誌檔案輸出
        logging.StreamHandler(),  # 控制台輸出
    ],
)
logger = logging.getLogger()


class CustomGate(ccxt.binance):
    def fetch(self, url, method='GET', headers=None, body=None):
        if headers is None:
            headers = {}
        # headers['X-Gate-Channel-Id'] = 'laohuoji'
        # headers['Accept'] = 'application/json'
        # headers['Content-Type'] = 'application/json'
        return super().fetch(url, method, headers, body)


# ==================== 網格交易機器人 ====================
class GridTradingBot:
    def __init__(self, api_key, api_secret, coin_name, contract_type, grid_spacing, initial_quantity, leverage):
        self.lock = asyncio.Lock()  # 初始化同步鎖
        self.api_key = api_key
        self.api_secret = api_secret
        self.coin_name = coin_name
        self.contract_type = contract_type  # 合約類型：USDT 或 USDC
        self.grid_spacing = grid_spacing
        self.initial_quantity = initial_quantity
        self.leverage = leverage
        self.ccxt_symbol = f"{coin_name}/{contract_type}:{contract_type}"  # 動態生成交易對
        self.exchange = self._initialize_exchange()  # 初始化交易所

        # 取得價格精度/數量精度/最小下單量
        self._get_price_precision()

        self.long_initial_quantity = 0  # 多頭下單數量
        self.short_initial_quantity = 0  # 空頭下單數量
        self.long_position = 0  # 多頭持倉（WS 監控）
        self.short_position = 0  # 空頭持倉（WS 監控）
        self.last_long_order_time = 0  # 上次多頭掛單時間
        self.last_short_order_time = 0  # 上次空頭掛單時間
        self.buy_long_orders = 0.0  # 多頭買入剩餘掛單量
        self.sell_long_orders = 0.0  # 多頭賣出剩餘掛單量
        self.sell_short_orders = 0.0  # 空頭賣出剩餘掛單量
        self.buy_short_orders = 0.0  # 空頭買入剩餘掛單量
        self.last_position_update_time = 0  # 上次持倉更新時間
        self.last_orders_update_time = 0  # 上次掛單更新時間
        self.last_ticker_update_time = 0  # ticker 更新限速用時間
        self.last_order_cycle_ts = 0  # 本輪下單處理時間戳
        self.latest_price = 0  # 最新價格
        self.best_bid_price = None  # 最佳買價
        self.best_ask_price = None  # 最佳賣價
        self.balance = {}  # 合約帳戶餘額
        self.mid_price_long = 0  # 多頭中間價
        self.lower_price_long = 0  # 多頭網格下緣
        self.upper_price_long = 0  # 多頭網格上緣
        self.mid_price_short = 0  # 空頭中間價
        self.lower_price_short = 0  # 空頭網格下緣
        self.upper_price_short = 0  # 空頭網格上緣
        self.long_entry_price = None  # 多頭平均成本
        self.short_entry_price = None  # 空頭平均成本
        self.listenKey = self.get_listen_key()  # 取得初始 listenKey
        self.startup_time = None  # 啟動時間戳（用於寬限期）
        self.last_grace_log_time = 0  # 啟動寬限期日誌節流
        self.client_order_prefix = self._build_client_order_prefix()  # 本實例下單識別前綴
        self.client_order_counter = 0  # 本實例下單序號

        # 檢查持倉模式，若非雙向持倉則停止程式
        self.check_and_enable_hedge_mode()

    def _initialize_exchange(self):
        """初始化交易所 API"""
        exchange = CustomGate({
            "apiKey": self.api_key,
            "secret": self.api_secret,
            "options": {
                "defaultType": "future",  # 使用永續合約
            },
        })
        # 載入市場資料
        exchange.load_markets(reload=False)
        try:
            exchange.set_leverage(LEVERAGE, self.ccxt_symbol)
            logger.info(f"設定槓桿成功: {self.ccxt_symbol} {LEVERAGE}x")
        except Exception:
            logger.exception(f"設定槓桿失敗: {self.ccxt_symbol} {LEVERAGE}x")
            raise
        return exchange

    def _get_price_precision(self):
        """取得交易對的價格精度、數量精度與最小下單量"""
        markets = self.exchange.fetch_markets()
        symbol_info = next(market for market in markets if market["symbol"] == self.ccxt_symbol)

        # 取得價格精度
        price_precision = symbol_info["precision"]["price"]
        if isinstance(price_precision, float):
            # 若 price_precision 為浮點數（如 0.01），計算小數位數
            self.price_precision = int(abs(math.log10(price_precision)))
        elif isinstance(price_precision, int):
            # 若 price_precision 為整數，直接使用
            self.price_precision = price_precision
        else:
            raise ValueError(f"未知的價格精度類型: {price_precision}")

        # 取得數量精度
        amount_precision = symbol_info["precision"]["amount"]
        if isinstance(amount_precision, float):
            # 若 amount_precision 為浮點數（如 0.001），計算小數位數
            self.amount_precision = int(abs(math.log10(amount_precision)))
        elif isinstance(amount_precision, int):
            # 若 amount_precision 為整數，直接使用
            self.amount_precision = amount_precision
        else:
            raise ValueError(f"未知的數量精度類型: {amount_precision}")

        # 取得最小下單數量
        self.min_order_amount = symbol_info["limits"]["amount"]["min"]

        logger.info(
            f"價格精度: {self.price_precision}, 數量精度: {self.amount_precision}, 最小下單數量: {self.min_order_amount}")

    def _in_startup_grace_period(self):
        if self.startup_time is None:
            return False
        return time.time() - self.startup_time < STARTUP_GRACE_PERIOD

    def _build_client_order_prefix(self):
        base_id = os.getenv("BOT_INSTANCE_ID")
        if not base_id:
            base_id = f"{socket.gethostname()}-{int(time.time())}"
        short_hash = hashlib.sha256(base_id.encode("utf-8")).hexdigest()[:8]
        return f"grid-{short_hash}-"

    def _next_client_order_id(self, label):
        self.client_order_counter += 1
        return f"{self.client_order_prefix}{label}-{self.client_order_counter}"

    def _is_own_order(self, order):
        client_order_id = order.get("clientOrderId") or order.get("info", {}).get("clientOrderId")
        return bool(client_order_id and client_order_id.startswith(self.client_order_prefix))

    def _get_own_open_orders(self):
        orders = self.exchange.fetch_open_orders(self.ccxt_symbol)
        return [order for order in orders if self._is_own_order(order)]

    def get_position(self):
        """取得目前持倉"""
        params = {
            'type': 'future'  # 永續合約
        }
        positions = self.exchange.fetch_positions(params=params)
        # print(positions)
        long_position = 0
        short_position = 0
        self.long_entry_price = None
        self.short_entry_price = None

        for position in positions:
            if position['symbol'] == self.ccxt_symbol:  # 使用動態 symbol
                contracts = position.get('contracts', 0)  # 取得合約數量
                side = position.get('side', None)  # 取得持倉方向
                entry_price = position.get('entryPrice')
                if entry_price is None:
                    entry_price = position.get('info', {}).get('entryPrice')
                if entry_price is not None:
                    try:
                        entry_price = float(entry_price)
                    except (TypeError, ValueError):
                        entry_price = None

                # 判斷多頭或空頭
                if side == 'long':  # 多頭
                    long_position = contracts
                    if entry_price:
                        self.long_entry_price = entry_price
                elif side == 'short':  # 空頭
                    short_position = abs(contracts)  # 使用絕對值計算空頭合約數
                    if entry_price:
                        self.short_entry_price = entry_price

        if long_position > 0 and self.long_entry_price:
            self.update_mid_price('long', self.long_entry_price)
        if short_position > 0 and self.short_entry_price:
            self.update_mid_price('short', self.short_entry_price)

        # 若沒有持倉，回傳 0
        if long_position == 0 and short_position == 0:
            return 0, 0

        return long_position, short_position

    async def monitor_orders(self):
        """監控掛單狀態，超過 300 秒未成交即取消"""
        while True:
            try:
                await asyncio.sleep(60)  # 每 60 秒檢查一次
                current_time = time.time()  # 目前時間（秒）
                orders = self._get_own_open_orders()

                if not orders:
                    logger.info("目前沒有本實例未成交掛單")
                    self.buy_long_orders = 0.0  # 多頭買入剩餘掛單量
                    self.sell_long_orders = 0.0  # 多頭賣出剩餘掛單量
                    self.sell_short_orders = 0.0  # 空頭賣出剩餘掛單量
                    self.buy_short_orders = 0.0  # 空頭買入剩餘掛單量
                    continue

                for order in orders:
                    order_id = order['id']
                    order_timestamp = order.get('timestamp')  # 取得訂單建立時間戳（毫秒）
                    create_time = float(order['info'].get('create_time', 0))  # 取得訂單建立時間（秒）

                    # 優先使用 create_time，若不存在則使用 timestamp
                    order_time = create_time if create_time > 0 else order_timestamp / 1000

                    if not order_time:
                        logger.warning(f"訂單 {order_id} 缺少時間戳，無法檢查超時")
                        continue

                    if current_time - order_time > 300:  # 超過 300 秒未成交
                        logger.info(f"訂單 {order_id} 超過 300 秒未成交，取消掛單")
                        try:
                            self.cancel_order(order_id)
                        except Exception as e:
                            logger.error(f"取消訂單 {order_id} 失敗: {e}")

            except Exception as e:
                logger.error(f"監控掛單狀態失敗: {e}")

    def check_orders_status(self):
        """檢查目前所有掛單狀態，更新多空掛單數量"""
        # 取得本實例掛單（限制指定交易對）
        orders = self._get_own_open_orders()

        # 初始化統計值
        buy_long_orders = 0.0  # 使用浮點數
        sell_long_orders = 0.0  # 使用浮點數
        buy_short_orders = 0.0  # 使用浮點數
        sell_short_orders = 0.0  # 使用浮點數

        for order in orders:
            # 取得原始委託數量（取絕對值）
            orig_quantity = abs(float(order.get('info', {}).get('origQty', 0)))  # 從 info 取得 origQty
            side = order.get('side')  # 訂單方向：buy 或 sell
            position_side = order.get('info', {}).get('positionSide')  # 倉位方向：LONG 或 SHORT

            # 判斷訂單類型
            if side == 'buy' and position_side == 'LONG':  # 多頭買單
                buy_long_orders += orig_quantity
            elif side == 'sell' and position_side == 'LONG':  # 多頭賣單
                sell_long_orders += orig_quantity
            elif side == 'buy' and position_side == 'SHORT':  # 空頭買單
                buy_short_orders += orig_quantity
            elif side == 'sell' and position_side == 'SHORT':  # 空頭賣單
                sell_short_orders += orig_quantity

        # 更新實例變數
        self.buy_long_orders = buy_long_orders
        self.sell_long_orders = sell_long_orders
        self.buy_short_orders = buy_short_orders
        self.sell_short_orders = sell_short_orders

    async def run(self):
        """啟動 WebSocket 監聽"""
        self.startup_time = time.time()
        # 初始化時先抓一次持倉資料
        self.long_position, self.short_position = self.get_position()
        # self.last_position_update_time = time.time()
        logger.info(f"初始化持倉: 多頭 {self.long_position} 張, 空頭 {self.short_position} 張")

        # 等待狀態同步完成
        await asyncio.sleep(5)  # 等待 5 秒

        # 初始化時先抓一次掛單狀態
        self.check_orders_status()
        logger.info(
            f"初始化掛單狀態: 多頭開倉={self.buy_long_orders}, 多頭止盈={self.sell_long_orders}, 空頭開倉={self.sell_short_orders}, 空頭止盈={self.buy_short_orders}")

        # 啟動掛單監控任務
        # asyncio.create_task(self.monitor_orders())
        # 啟動 listenKey 更新任務
        asyncio.create_task(self.keep_listen_key_alive())

        while True:
            try:
                await self.connect_websocket()
            except Exception as e:
                logger.error(f"WebSocket 連線失敗: {e}")
                await asyncio.sleep(5)  # 等待 5 秒後重試

    async def sync_after_reconnect(self):
        """重連後同步持倉與掛單，視情況重建網格"""
        self.long_position, self.short_position = self.get_position()
        self.check_orders_status()
        self.last_position_update_time = time.time()
        self.last_orders_update_time = time.time()
        logger.info(
            f"重連後同步: 多頭 {self.long_position} 張, 空頭 {self.short_position} 張, "
            f"多頭開倉={self.buy_long_orders}, 多頭止盈={self.sell_long_orders}, "
            f"空頭開倉={self.sell_short_orders}, 空頭止盈={self.buy_short_orders}"
        )

        if self._in_startup_grace_period():
            logger.info("啟動寬限期內，略過重連後的網格調整")
            return

        if self.latest_price:
            await self.adjust_grid_strategy()
        else:
            logger.info("重連後尚無最新價格，等待 ticker 更新再重建網格")

    async def connect_websocket(self):
        """連線 WebSocket 並訂閱 ticker 與掛單更新"""
        async with websockets.connect(WEBSOCKET_URL) as websocket:
            # 訂閱 ticker 資料
            await self.subscribe_ticker(websocket)
            # 訂閱掛單資料
            await self.subscribe_orders(websocket)
            await self.sync_after_reconnect()
            while True:
                try:
                    message = await websocket.recv()
                    data = json.loads(message)
                    # print(data)
                    if data.get("e") == "bookTicker":
                        await self.handle_ticker_update(message)
                    elif data.get("e") == "ORDER_TRADE_UPDATE":  # 處理掛單更新
                        await self.handle_order_update(message)
                except Exception as e:
                    logger.error(f"WebSocket 訊息處理失敗: {e}")
                    break

    async def subscribe_ticker(self, websocket):
        """訂閱 ticker 資料"""
        payload = {
            "method": "SUBSCRIBE",
            "params": [f"{self.coin_name.lower()}{self.contract_type.lower()}@bookTicker"],
            "id": 1
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已送出 ticker 訂閱請求: {payload}")

    async def subscribe_orders(self, websocket):
        """訂閱掛單資料"""
        if not self.listenKey:
            logger.error("listenKey 為空，無法訂閱訂單更新")
            return

        payload = {
            "method": "SUBSCRIBE",
            "params": [f"{self.listenKey}"],  # 使用 self.listenKey 訂閱
            "id": 3
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已送出掛單訂閱請求: {payload}")

    def get_listen_key(self):
        """取得 listenKey"""
        try:
            response = self.exchange.fapiPrivatePostListenKey()
            listenKey = response.get("listenKey")
            if not listenKey:
                raise ValueError("取得的 listenKey 為空")
            logger.info(f"成功取得 listenKey: {listenKey}")
            return listenKey
        except Exception as e:
            logger.error(f"取得 listenKey 失敗: {e}")
            raise e

    async def keep_listen_key_alive(self):
        """定期更新 listenKey"""
        while True:
            try:
                await asyncio.sleep(1800)  # 每 30 分鐘更新一次
                self.exchange.fapiPrivatePutListenKey()
                self.listenKey = self.get_listen_key()  # 更新 self.listenKey
                logger.info(f"listenKey 已更新: {self.listenKey}")
            except Exception as e:
                logger.error(f"更新 listenKey 失敗: {e}")
                await asyncio.sleep(60)  # 等待 60 秒後重試

    def _generate_sign(self, message):
        """產生 HMAC-SHA256 簽名"""
        return hmac.new(self.api_secret.encode("utf-8"), message.encode("utf-8"), hashlib.sha256).hexdigest()

    async def handle_ticker_update(self, message):
        current_time = time.time()
        if current_time - self.last_ticker_update_time < 0.5:  # 100ms
            return  # 略過本次更新

        self.last_ticker_update_time = current_time
        """處理 ticker 更新"""
        data = json.loads(message)
        if data.get("e") == "bookTicker":  # Binance bookTicker 事件
            best_bid_price = data.get("b")
            best_ask_price = data.get("a")

            # 檢查欄位是否存在且有效
            if best_bid_price is None or best_ask_price is None:
                logger.warning("bookTicker 訊息缺少最佳買價或最佳賣價")
                return

            try:
                self.best_bid_price = float(best_bid_price)  # 最佳買價
                self.best_ask_price = float(best_ask_price)  # 最佳賣價
                self.latest_price = (self.best_bid_price + self.best_ask_price) / 2  # 最新價格
                # logger.info(
                #     f"最新價格: {self.latest_price}, 最佳買價: {self.best_bid_price}, 最佳賣價: {self.best_ask_price}")
            except ValueError as e:
                logger.error(f"解析價格失敗: {e}")

            # 檢查持倉是否過期
            if time.time() - self.last_position_update_time > SYNC_TIME:  # 超過 SYNC_TIME 未更新
                self.long_position, self.short_position = self.get_position()
                self.last_position_update_time = time.time()
                logger.info(f"同步 position: 多頭 {self.long_position} 張, 空頭 {self.short_position} 張 @ ticker")

            # 檢查掛單是否過期
            if time.time() - self.last_orders_update_time > SYNC_TIME:  # 超過 SYNC_TIME 未更新
                self.check_orders_status()
                self.last_orders_update_time = time.time()
                logger.info(
                    f"同步 orders: 多頭買單 {self.buy_long_orders} 張, 多頭賣單 {self.sell_long_orders} 張, 空頭賣單 {self.sell_short_orders} 張, 空頭買單 {self.buy_short_orders} 張 @ ticker")

            await self.adjust_grid_strategy()

    async def handle_order_update(self, message):
        async with self.lock:
            """處理訂單更新並同步持倉"""
            data = json.loads(message)
            # print(f"收到訊息: {data}")  # 印出原始資料

            if data.get("e") == "ORDER_TRADE_UPDATE":  # 處理訂單更新
                order = data.get("o", {})
                symbol = order.get("s")  # 交易對
                if symbol == f"{self.coin_name}{self.contract_type}":  # 匹配交易對
                    side = order.get("S")  # 訂單方向：BUY 或 SELL
                    position_side = order.get("ps")  # 倉位方向：LONG 或 SHORT
                    reduce_only = order.get("R")  # 是否為平倉單
                    status = order.get("X")  # 訂單狀態
                    quantity = float(order.get("q", 0))  # 訂單數量
                    filled = float(order.get("z", 0))  # 已成交數量
                    remaining = quantity - filled  # 剩餘數量

                    if status == "NEW":
                        if side == "BUY":
                            if position_side == "LONG":  # 多頭開倉單
                                self.buy_long_orders += remaining
                            elif position_side == "SHORT":  # 空頭止盈單
                                self.buy_short_orders += remaining
                        elif side == "SELL":
                            if position_side == "LONG":  # 多頭止盈單
                                self.sell_long_orders += remaining
                            elif position_side == "SHORT":  # 空頭開倉單
                                self.sell_short_orders += remaining
                    elif status == "FILLED":  # 訂單已成交
                        if side == "BUY":
                            if position_side == "LONG":  # 多頭開倉單
                                self.long_position += filled  # 更新多頭持倉
                                self.buy_long_orders = max(0.0, self.buy_long_orders - filled)  # 更新掛單狀態
                            elif position_side == "SHORT":  # 空頭止盈單
                                self.short_position = max(0.0, self.short_position - filled)  # 更新空頭持倉
                                self.buy_short_orders = max(0.0, self.buy_short_orders - filled)  # 更新掛單狀態
                        elif side == "SELL":
                            if position_side == "LONG":  # 多頭止盈單
                                self.long_position = max(0.0, self.long_position - filled)  # 更新多頭持倉
                                self.sell_long_orders = max(0.0, self.sell_long_orders - filled)  # 更新掛單狀態
                            elif position_side == "SHORT":  # 空頭開倉單
                                self.short_position += filled  # 更新空頭持倉
                                self.sell_short_orders = max(0.0, self.sell_short_orders - filled)  # 更新掛單狀態
                    elif status == "CANCELED":  # 訂單已取消
                        if side == "BUY":
                            if position_side == "LONG":  # 多頭開倉單
                                self.buy_long_orders = max(0.0, self.buy_long_orders - quantity)
                            elif position_side == "SHORT":  # 空頭止盈單
                                self.buy_short_orders = max(0.0, self.buy_short_orders - quantity)
                        elif side == "SELL":
                            if position_side == "LONG":  # 多頭止盈單
                                self.sell_long_orders = max(0.0, self.sell_long_orders - quantity)
                            elif position_side == "SHORT":  # 空頭開倉單
                                self.sell_short_orders = max(0.0, self.sell_short_orders - quantity)

                    # # 印出目前掛單狀態
                    # logger.info(
                    #     f"掛單狀態: 多頭開倉={self.buy_long_orders}, 多頭止盈={self.sell_long_orders}, 空頭開倉={self.sell_short_orders}, 空頭止盈={self.buy_short_orders}")
                    # # 印出目前持倉狀態
                    # logger.info(f"持倉狀態: 多頭={self.long_position}, 空頭={self.short_position}")

    def get_take_profit_quantity(self, position, side):
        # print(side)

        """計算止盈下單數量"""
        if side == 'long':
            if position > POSITION_LIMIT:
                # logger.info(f"持倉過大超過閾值{POSITION_LIMIT}, {side} 雙倍止盈止損")
                self.long_initial_quantity = self.initial_quantity * 2

            # 若空頭鎖倉超過閾值，拉高多頭止盈量
            elif self.short_position >= POSITION_THRESHOLD:
                self.long_initial_quantity = self.initial_quantity * 2
            else:
                self.long_initial_quantity = self.initial_quantity

        elif side == 'short':
            if position > POSITION_LIMIT:
                # logger.info(f"持倉過大超過閾值{POSITION_LIMIT}, {side} 雙倍止盈止損")
                self.short_initial_quantity = self.initial_quantity * 2

            # 若多頭鎖倉超過閾值，拉高空頭止盈量
            elif self.long_position >= POSITION_THRESHOLD:
                self.short_initial_quantity = self.initial_quantity * 2
            else:
                self.short_initial_quantity = self.initial_quantity

    async def initialize_long_orders(self):
        # 檢查上次掛單時間，避免短時間重複掛單
        current_time = time.time()
        if current_time - self.last_long_order_time < ORDER_FIRST_TIME:
            logger.info(f"距離上次多頭掛單不足 {ORDER_FIRST_TIME} 秒，略過本次掛單")
            return

        # # 檢查是否有未成交掛單
        # orders = self.exchange.fetch_open_orders(self.ccxt_symbol)
        # if any(order['side'] == 'buy' and order['info'].get('positionSide') == 'LONG' for order in orders):
        #     logger.info("發現未成交多頭補倉單，略過撤單與掛單")
        #     return

        self.cancel_orders_for_side('long')

        # 掛出多頭開倉單
        order = self.place_order('buy', self.best_bid_price, self.initial_quantity, False, 'long')
        logger.info(f"掛出多頭開倉單: 買入 @ {self.latest_price}")

        # 更新上次多頭掛單時間
        if order:
            self.last_long_order_time = time.time()
        logger.info("初始化多頭掛單完成")

    async def initialize_short_orders(self):
        # 檢查上次掛單時間，避免短時間重複掛單
        current_time = time.time()
        if current_time - self.last_short_order_time < ORDER_FIRST_TIME:
            print(f"距離上次空頭掛單不足 {ORDER_FIRST_TIME} 秒，略過本次掛單")
            return

        # 撤銷所有空頭掛單
        self.cancel_orders_for_side('short')

        # 掛出空頭開倉單
        order = self.place_order('sell', self.best_ask_price, self.initial_quantity, False, 'short')
        logger.info(f"掛出空頭開倉單: 賣出 @ {self.latest_price}")

        # 更新上次空頭掛單時間
        if order:
            self.last_short_order_time = time.time()
        logger.info("初始化空頭掛單完成")

    def cancel_orders_for_side(self, position_side):
        """撤銷某個方向的所有掛單"""
        orders = self._get_own_open_orders()

        if len(orders) == 0:
            logger.info("沒有找到掛單")
        else:
            try:
                for order in orders:
                    # 取得訂單方向與倉位方向
                    side = order.get('side')  # 訂單方向：buy 或 sell
                    reduce_only = order.get('reduceOnly', False)  # 是否為平倉單
                    position_side_order = order.get('info', {}).get('positionSide', 'BOTH')  # 倉位方向：LONG 或 SHORT

                    if position_side == 'long':
                        # 多頭開倉單：買單且 reduceOnly 為 False
                        if not reduce_only and side == 'buy' and position_side_order == 'LONG':
                            # logger.info("發現多頭開倉掛單，準備撤銷")
                            self.cancel_order(order['id'])  # 撤銷該訂單
                        # 多頭止盈單：賣單且 reduceOnly 為 True
                        elif reduce_only and side == 'sell' and position_side_order == 'LONG':
                            # logger.info("發現多頭止盈掛單，準備撤銷")
                            self.cancel_order(order['id'])  # 撤銷該訂單

                    elif position_side == 'short':
                        # 空頭開倉單：賣單且 reduceOnly 為 False
                        if not reduce_only and side == 'sell' and position_side_order == 'SHORT':
                            # logger.info("發現空頭開倉掛單，準備撤銷")
                            self.cancel_order(order['id'])  # 撤銷該訂單
                        # 空頭止盈單：買單且 reduceOnly 為 True
                        elif reduce_only and side == 'buy' and position_side_order == 'SHORT':
                            # logger.info("發現空頭止盈掛單，準備撤銷")
                            self.cancel_order(order['id'])  # 撤銷該訂單
            except ccxt.OrderNotFound as e:
                logger.warning(f"訂單 {order['id']} 不存在，無需撤銷: {e}")
                self.check_orders_status()  # 強制更新掛單狀態
            except Exception as e:
                logger.error(f"撤單失敗: {e}")

    def cancel_order(self, order_id):
        """撤單"""
        try:
            self.exchange.cancel_order(order_id, self.ccxt_symbol)
            # logger.info(f"撤銷掛單成功, 訂單ID: {order_id}")
        except ccxt.BaseError as e:
            logger.error(f"撤單失敗: {e}")

    def _build_order_params(self, is_reduce_only, position_side, order_label):
        params = {
            'newClientOrderId': self._next_client_order_id(order_label),
        }
        if position_side is not None:
            params['positionSide'] = position_side.upper()  # Binance 需要大寫：LONG 或 SHORT
        if is_reduce_only and self.contract_type == 'USDT':
            params['reduceOnly'] = True
        return params

    def place_order(self, side, price, quantity, is_reduce_only=False, position_side=None, order_type='limit'):
        """掛單函式，支援雙向持倉"""
        try:
            # 修正價格精度
            price = round(price, self.price_precision)

            # 修正數量精度並確保不低於最小下單量
            quantity = round(quantity, self.amount_precision)
            quantity = max(quantity, self.min_order_amount)

            # 市價單不需要價格參數
            if order_type == 'market':
                params = self._build_order_params(is_reduce_only, position_side, f"{side}-mkt")
                order = self.exchange.create_order(self.ccxt_symbol, 'market', side, quantity, None, params)
                return order
            else:
                # 檢查 price 是否為 None
                if price is None:
                    logger.error("限價單必須提供 price 參數")
                    return None

                params = self._build_order_params(is_reduce_only, position_side, f"{side}-lmt")
                order = self.exchange.create_order(self.ccxt_symbol, 'limit', side, quantity, price, params)
                return order

        except ccxt.BaseError as e:
            logger.error(f"下單錯誤: {e}")
            return None

    def place_take_profit_order(self, ccxt_symbol, side, price, quantity):
        # print('止盈單價格', price)
        # 檢查是否已有相同價格的掛單
        orders = self._get_own_open_orders()
        for order in orders:
            if (
                    order['info'].get('positionSide') == side.upper()
                    and float(order['price']) == price
                    and order['side'] == ('sell' if side == 'long' else 'buy')
            ):
                logger.info(f"已存在相同價格的 {side} 止盈單，略過掛單")
                return
        """掛止盈單（雙向持倉模式）"""
        try:
            # 檢查持倉
            if side == 'long' and self.long_position <= 0:
                logger.warning("沒有多頭持倉，略過多頭止盈單")
                return
            elif side == 'short' and self.short_position <= 0:
                logger.warning("沒有空頭持倉，略過空頭止盈單")
                return
            # 修正價格精度
            price = round(price, self.price_precision)

            # 修正數量精度並確保不低於最小下單量
            quantity = round(quantity, self.amount_precision)
            quantity = max(quantity, self.min_order_amount)

            if side == 'long':
                # 賣出多頭持倉止盈
                params = self._build_order_params(True, 'LONG', "tp-long")
                order = self.exchange.create_order(ccxt_symbol, 'limit', 'sell', quantity, price, params)
                logger.info(f"成功掛 long 止盈單: 賣出 {quantity} {ccxt_symbol} @ {price}")
                return order
            elif side == 'short':
                # 買入空頭持倉止盈
                params = self._build_order_params(True, 'SHORT', "tp-short")
                order = self.exchange.create_order(ccxt_symbol, 'limit', 'buy', quantity, price, params)
                logger.info(f"成功掛 short 止盈單: 買入 {quantity} {ccxt_symbol} @ {price}")
                return order
        except ccxt.BaseError as e:
            logger.error(f"掛止盈單失敗: {e}")
        return None

    async def place_long_orders(self, latest_price):
        """掛多頭訂單"""
        try:
            self.get_take_profit_quantity(self.long_position, 'long')
            if self.long_position > 0:
                # print('多頭持倉', self.long_position)
                # 檢查持倉是否超過閾值
                if self.long_position > POSITION_THRESHOLD:
                    print(f"持倉{self.long_position}超過極限閾值 {POSITION_THRESHOLD}，long 裝死")
                    if self.sell_long_orders <= 0:
                        if self.short_position == 0:
                            r = 1 + GRID_SPACING
                        else:
                            r = float((self.long_position / self.short_position) / 100 + 1)
                        take_profit_order = self.place_take_profit_order(
                            self.ccxt_symbol,
                            'long',
                            self.latest_price * r,
                            self.long_initial_quantity,
                        )  # 掛止盈
                        if take_profit_order:
                            self.last_long_order_time = time.time()
                else:
                    # 更新中間價
                    mid_price = self.long_entry_price or latest_price
                    self.update_mid_price('long', mid_price)
                    self.cancel_orders_for_side('long')
                    take_profit_order = self.place_take_profit_order(
                        self.ccxt_symbol,
                        'long',
                        self.upper_price_long,
                        self.long_initial_quantity,
                    )  # 掛止盈
                    if take_profit_order:
                        self.last_long_order_time = time.time()
                    open_order = self.place_order(
                        'buy',
                        self.lower_price_long,
                        self.long_initial_quantity,
                        False,
                        'long',
                    )  # 掛補倉
                    if open_order:
                        self.last_long_order_time = time.time()
                    logger.info("掛多頭止盈，掛多頭補倉")

        except Exception as e:
            logger.error(f"掛多頭訂單失敗: {e}")

    async def place_short_orders(self, latest_price):
        """掛空頭訂單"""
        try:
            self.get_take_profit_quantity(self.short_position, 'short')
            if self.short_position > 0:
                # 檢查持倉是否超過閾值
                if self.short_position > POSITION_THRESHOLD:
                    print(f"持倉{self.short_position}超過極限閾值 {POSITION_THRESHOLD}，short 裝死")
                    if self.buy_short_orders <= 0:
                        if self.long_position == 0:
                            r = 1 + GRID_SPACING
                        else:
                            r = float((self.short_position / self.long_position) / 100 + 1)
                        logger.info("發現空頭止盈單缺失，需要補止盈單")
                        take_profit_order = self.place_take_profit_order(
                            self.ccxt_symbol,
                            'short',
                            self.latest_price * r,
                            self.short_initial_quantity,
                        )  # 掛止盈
                        if take_profit_order:
                            self.last_short_order_time = time.time()

                else:
                    # 更新中間價
                    mid_price = self.short_entry_price or latest_price
                    self.update_mid_price('short', mid_price)
                    self.cancel_orders_for_side('short')
                    take_profit_order = self.place_take_profit_order(
                        self.ccxt_symbol,
                        'short',
                        self.lower_price_short,
                        self.short_initial_quantity,
                    )  # 掛止盈
                    if take_profit_order:
                        self.last_short_order_time = time.time()
                    open_order = self.place_order(
                        'sell',
                        self.upper_price_short,
                        self.short_initial_quantity,
                        False,
                        'short',
                    )  # 掛補倉
                    if open_order:
                        self.last_short_order_time = time.time()
                    logger.info("掛空頭止盈，掛空頭補倉")

        except Exception as e:
            logger.error(f"掛空頭訂單失敗: {e}")

    def check_and_enable_hedge_mode(self):
        """檢查並啟用雙向持倉模式，若切換失敗則停止程式"""
        try:
            # 取得目前持倉模式
            position_mode = self.exchange.fetch_position_mode(symbol=self.ccxt_symbol)
            if not position_mode['hedged']:
                # 若目前不是雙向持倉，嘗試啟用
                logger.info("目前不是雙向持倉模式，嘗試自動啟用...")
                self.enable_hedge_mode()

                # 再次檢查持倉模式，確認是否啟用成功
                position_mode = self.exchange.fetch_position_mode(symbol=self.ccxt_symbol)
                if not position_mode['hedged']:
                    # 若仍不是雙向持倉，記錄錯誤並停止程式
                    logger.error("啟用雙向持倉模式失敗，請手動啟用後再執行。")
                    raise Exception("啟用雙向持倉模式失敗，請手動啟用後再執行。")
                else:
                    logger.info("雙向持倉模式已成功啟用，程式繼續執行。")
            else:
                logger.info("目前已是雙向持倉模式，程式繼續執行。")
        except Exception as e:
            logger.error(f"檢查或啟用雙向持倉模式失敗: {e}")
            raise e  # 拋出例外以停止程式

    def enable_hedge_mode(self):
        """啟用雙向持倉模式"""
        try:
            # 使用 ccxt 的 fapiPrivatePostPositionSideDual 函式
            params = {
                'dualSidePosition': 'true',  # 啟用雙向持倉模式
            }
            response = self.exchange.fapiPrivatePostPositionSideDual(params)
            logger.info(f"啟用雙向持倉模式: {response}")
        except Exception as e:
            logger.error(f"啟用雙向持倉模式失敗: {e}")
            raise e  # 拋出例外以停止程式

    def check_and_reduce_positions(self):
        """檢查持倉並降低庫存風險"""

        # 設定持倉閾值
        local_position_threshold = POSITION_THRESHOLD * 0.8  # 閾值的 80%

        # 設定平倉數量
        quantity = POSITION_THRESHOLD * 0.1  # 閾值的 10%

        if self.long_position >= local_position_threshold and self.short_position >= local_position_threshold:
            logger.info(f"多頭與空頭持倉皆超過閾值 {local_position_threshold}，開始雙向平倉降低風險")
            # 平倉多頭（使用市價單）
            if self.long_position > 0:
                self.place_order('sell', price=self.best_ask_price, quantity=quantity, is_reduce_only=True, position_side='long',
                                 order_type='market')
                logger.info(f"市價平倉多頭 {quantity} 個")

            # 平倉空頭（使用市價單）
            if self.short_position > 0:
                self.place_order('buy', price=self.best_bid_price, quantity=quantity, is_reduce_only=True, position_side='short',
                                 order_type='market')
                logger.info(f"市價平倉空頭 {quantity} 個")

    def update_mid_price(self, side, price):
        """更新中間價"""
        if side == 'long':
            self.mid_price_long = price  # 更新多頭中間價
            # 計算多頭上下網格價格
            self.upper_price_long = self.mid_price_long * (1 + self.grid_spacing)
            self.lower_price_long = self.mid_price_long * (1 - self.grid_spacing)
            print("更新 long 中間價")

        elif side == 'short':
            self.mid_price_short = price  # 更新空頭中間價
            # 計算空頭上下網格價格
            self.upper_price_short = self.mid_price_short * (1 + self.grid_spacing)
            self.lower_price_short = self.mid_price_short * (1 - self.grid_spacing)
            print("更新 short 中間價")

    # ==================== 策略邏輯 ====================
    async def adjust_grid_strategy(self):

        """依最新價格與持倉狀態調整網格策略"""
        cycle_ts = self.last_ticker_update_time or time.time()
        if cycle_ts == self.last_order_cycle_ts:
            return
        self.last_order_cycle_ts = cycle_ts

        # 檢查雙向持倉是否同時過大，必要時部分平倉降低風險
        self.check_and_reduce_positions()
        # print(self.latest_price, '多掛', self.buy_long_orders, '多平', self.buy_long_orders, '空掛', self.sell_short_orders, '空平', self.buy_short_orders)

        if self._in_startup_grace_period():
            if time.time() - self.last_grace_log_time > 5:
                logger.info("啟動寬限期內，暫停下單，僅同步狀態")
                self.last_grace_log_time = time.time()
            return

        # 檢查多頭持倉
        if self.long_position == 0:
            print(f"偵測到沒有多頭持倉 {self.long_position}，初始化多頭掛單 @ ticker")
            await self.initialize_long_orders()
        else:
            orders_valid = not (0 < self.buy_long_orders <= self.long_initial_quantity) or \
                           not (0 < self.sell_long_orders <= self.long_initial_quantity)
            if orders_valid:
                if self.long_position < POSITION_THRESHOLD:
                    print('若 long 持倉未達閾值，先同步後再確認！')
                    self.check_orders_status()
                    if orders_valid:
                        await self.place_long_orders(self.latest_price)
                else:
                    await self.place_long_orders(self.latest_price)
        # 檢查空頭持倉
        if self.short_position == 0:
            await self.initialize_short_orders()
        else:
            # 檢查掛單數量是否在合理範圍
            orders_valid = not (0 < self.sell_short_orders <= self.short_initial_quantity) or \
                           not (0 < self.buy_short_orders <= self.short_initial_quantity)
            if orders_valid:
                if self.short_position < POSITION_THRESHOLD:
                    print('若 short 持倉未達閾值，先同步後再確認！')
                    self.check_orders_status()
                    if orders_valid:
                        await self.place_short_orders(self.latest_price)
                else:
                    await self.place_short_orders(self.latest_price)


# ==================== 主程式 ====================
async def main():
    bot = GridTradingBot(API_KEY, API_SECRET, COIN_NAME, CONTRACT_TYPE, GRID_SPACING, INITIAL_QUANTITY, LEVERAGE)
    await bot.run()

if __name__ == "__main__":
    asyncio.run(main())
