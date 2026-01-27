import asyncio
import websockets
import json
import logging
import hmac
import hashlib
import time
import ccxt
import math
from decimal import Decimal, ROUND_HALF_UP
import os

# ==================== 配置 ====================
API_KEY = ""  # 替换为你的 API Key
API_SECRET = ""  # 替换为你的 API Secret
COIN_NAME = "X"  # 交易币种
GRID_SPACING = 0.004  # 网格间距 (0.3%)
INITIAL_QUANTITY = 1  # 初始交易数量 (张数)
LEVERAGE = 20  # 杠杆倍数
WEBSOCKET_URL = "wss://fx-ws.gateio.ws/v4/ws/usdt"  # WebSocket URL
POSITION_THRESHOLD = 60 * INITIAL_QUANTITY / GRID_SPACING * 2 / 100  # 锁仓阈值
POSITION_LIMIT = 30 * INITIAL_QUANTITY / GRID_SPACING * 2 / 100  # 持仓数量阈值
ORDER_COOLDOWN_TIME = 60  # 锁仓后的反向挂单冷却时间（秒）
SYNC_TIME = 3  # 同步时间（秒）
ORDER_FIRST_TIME = 1  # 首单间隔时间

# ==================== 日志配置 ====================
# 获取当前脚本的文件名（不带扩展名）
script_name = os.path.splitext(os.path.basename(__file__))[0]
logging.basicConfig(
    level=logging.INFO,
    format="%(asctime)s - %(levelname)s - %(message)s",
    handlers=[
        logging.FileHandler(f"log/{script_name}.log"),  # 日志文件
        logging.StreamHandler(),  # 控制台输出
    ],
)
logger = logging.getLogger()


class CustomGate(ccxt.gate):
    def fetch(self, url, method='GET', headers=None, body=None):
        if headers is None:
            headers = {}
        headers['X-Gate-Channel-Id'] = 'laohuoji'
        headers['Accept'] = 'application/json'
        headers['Content-Type'] = 'application/json'
        return super().fetch(url, method, headers, body)


# ==================== 网格交易机器人 ====================
class GridTradingBot:
    def __init__(self, api_key, api_secret, coin_name, grid_spacing, initial_quantity, leverage):
        self.api_key = api_key
        self.api_secret = api_secret
        self.coin_name = coin_name
        self.grid_spacing = grid_spacing
        self.initial_quantity = initial_quantity
        self.leverage = leverage
        self.exchange = self._initialize_exchange()  # 初始化交易所
        self.ccxt_symbol = f"{coin_name}/USDT:USDT"  # CCXT 格式的交易对
        self.ws_symbol = f"{coin_name}_USDT"  # WebSocket 格式的交易对
        self.price_precision = self._get_price_precision()  # 价格精度

        self.long_initial_quantity = 0  # 多头下单数量
        self.short_initial_quantity = 0  # 空头下单数量
        self.long_position = 0  # 多头持仓 ws监控
        self.short_position = 0  # 空头持仓 ws监控
        self.last_long_order_time = 0  # 上次多头挂单时间
        self.last_short_order_time = 0  # 上次空头挂单时间
        self.buy_long_orders = 0  # 多头买入剩余挂单数量
        self.sell_long_orders = 0  # 多头卖出剩余挂单数量
        self.sell_short_orders = 0  # 空头卖出剩余挂单数量
        self.buy_short_orders = 0  # 空头买入剩余挂单数量
        self.last_position_update_time = 0  # 上次持仓更新时间
        self.last_orders_update_time = 0  # 上次订单更新时间
        self.latest_price = 0  # 最新价格
        self.best_bid_price = None  # 最佳买价
        self.best_ask_price = None  # 最佳卖价
        self.balance = {}  # 用于存储合约账户余额
        self.mid_price_long = 0  # long 中间价
        self.lower_price_long = 0  # long 网格上
        self.upper_price_long = 0  # long 网格下
        self.mid_price_short = 0  # short 中间价
        self.lower_price_short = 0  # short 网格上
        self.upper_price_short = 0  # short 网格下

    def _initialize_exchange(self):
        """初始化交易所 API"""
        exchange = CustomGate({
            "apiKey": self.api_key,
            "secret": self.api_secret,
            "options": {
                "defaultType": "future",  # 使用永续合约
            },
        })
        return exchange

    def _get_price_precision(self):
        """获取交易对的价格精度"""
        markets = self.exchange.fetch_markets()
        symbol_info = next(market for market in markets if market["symbol"] == self.ccxt_symbol)
        return int(-math.log10(float(symbol_info["precision"]["price"])))

    def get_position(self):
        """获取当前持仓"""
        params = {
            'settle': 'usdt',  # 设置结算货币为 USDT
            'type': 'swap'  # 永续合约
        }
        positions = self.exchange.fetch_positions(params=params)
        long_position = 0
        short_position = 0

        for position in positions:
            if position['symbol'] == self.ccxt_symbol:  # 使用动态的 symbol 变量
                contracts = position.get('contracts', 0)  # 获取合约数量
                side = position.get('side', None)  # 获取仓位方向

                # 判断是否为多头或空头
                if side == 'long':  # 多头
                    long_position = contracts
                elif side == 'short':  # 空头
                    short_position = abs(contracts)  # 使用绝对值来计算空头合约数

        # 如果没有持仓，返回 0
        if long_position == 0 and short_position == 0:
            return 0, 0

        return long_position, short_position

    async def monitor_orders(self):
        """监控挂单状态，超过300秒未成交的挂单自动取消"""
        while True:
            try:
                await asyncio.sleep(60)  # 每60秒检查一次
                current_time = time.time()  # 当前时间（秒）
                orders = self.exchange.fetch_open_orders(self.ccxt_symbol)

                if not orders:
                    logger.info("当前没有未成交的挂单")
                    self.buy_long_orders = 0  # 多头买入剩余挂单数量
                    self.sell_long_orders = 0  # 多头卖出剩余挂单数量
                    self.sell_short_orders = 0  # 空头卖出剩余挂单数量
                    self.buy_short_orders = 0  # 空头买入剩余挂单数量
                    continue

                for order in orders:
                    order_id = order['id']
                    order_timestamp = order.get('timestamp')  # 获取订单创建时间戳（毫秒）
                    create_time = float(order['info'].get('create_time', 0))  # 获取订单创建时间（秒）

                    # 优先使用 create_time，如果不存在则使用 timestamp
                    order_time = create_time if create_time > 0 else order_timestamp / 1000

                    if not order_time:
                        logger.warning(f"订单 {order_id} 缺少时间戳，无法检查超时")
                        continue

                    if current_time - order_time > 300:  # 超过300秒未成交
                        logger.info(f"订单 {order_id} 超过300秒未成交，取消挂单")
                        try:
                            self.cancel_order(order_id)
                        except Exception as e:
                            logger.error(f"取消订单 {order_id} 失败: {e}")

            except Exception as e:
                logger.error(f"监控挂单状态失败: {e}")

    def check_orders_status(self):
        """检查当前所有挂单的状态"""
        orders = self.exchange.fetch_open_orders(self.ccxt_symbol)  # 获取所有未成交订单
        # print(orders)
        buy_long_orders_count = 0
        sell_long_orders_count = 0
        sell_short_orders_count = 0
        buy_short_orders_count = 0

        for order in orders:
            # 确保 order 中有 'info' 字段，并且 'info' 中有 'left' 字段
            if not order.get('info') or 'left' not in order['info']:
                continue  # 跳过不符合条件的订单

            # 获取未成交数量，如果 'left' 不存在则默认为 '0'
            left_amount = abs(float(order['info'].get('left', '0')))

            # 如果是多头止盈订单：卖单且仓位方向是多头的平仓单
            if order.get('reduceOnly') == True and order.get('side') == 'sell' and order.get('status') == 'open':
                sell_long_orders_count = left_amount
            # 如果是空头买入挂单：买单且仓位方向是空头的平仓单（空头止盈）
            elif order.get('reduceOnly') == True and order.get('side') == 'buy' and order.get('status') == 'open':
                buy_short_orders_count = left_amount
            # 如果是多头开仓订单：买单且 reduceOnly 为 False（开多仓）
            elif order.get('reduceOnly') == False and order.get('side') == 'buy' and order.get('status') == 'open':
                buy_long_orders_count = left_amount
            # 如果是空头开仓订单：卖单且 reduceOnly 为 False（开空仓）
            elif order.get('reduceOnly') == False and order.get('side') == 'sell' and order.get('status') == 'open':
                sell_short_orders_count = left_amount

        return buy_long_orders_count, sell_long_orders_count, sell_short_orders_count, buy_short_orders_count

    async def run(self):
        """启动 WebSocket 监听"""
        # 初始化时获取一次持仓数据
        self.long_position, self.short_position = self.get_position()
        # self.last_position_update_time = time.time()
        logger.info(f"初始化持仓: 多头 {self.long_position} 张, 空头 {self.short_position} 张")

        # 初始化时获取一次挂单状态
        self.buy_long_orders, self.sell_long_orders, self.sell_short_orders, self.buy_short_orders = self.check_orders_status()
        logger.info(
            f"初始化挂单状态: 多头开仓={self.buy_long_orders}, 多头止盈={self.sell_long_orders}, 空头开仓={self.sell_short_orders}, 空头止盈={self.buy_short_orders}")

        # 启动挂单监控任务
        # asyncio.create_task(self.monitor_orders())

        while True:
            try:
                await self.connect_websocket()
            except Exception as e:
                logger.error(f"WebSocket 连接失败: {e}")
                await asyncio.sleep(5)  # 等待 5 秒后重试

    async def sync_after_reconnect(self):
        """重连后同步持仓与挂单，并按需重建网格"""
        self.long_position, self.short_position = self.get_position()
        (
            self.buy_long_orders,
            self.sell_long_orders,
            self.sell_short_orders,
            self.buy_short_orders,
        ) = self.check_orders_status()
        self.last_position_update_time = time.time()
        self.last_orders_update_time = time.time()
        logger.info(
            f"重连后同步: 多头 {self.long_position} 张, 空头 {self.short_position} 张, "
            f"多头开仓={self.buy_long_orders}, 多头止盈={self.sell_long_orders}, "
            f"空头开仓={self.sell_short_orders}, 空头止盈={self.buy_short_orders}"
        )

        if self.latest_price:
            await self.adjust_grid_strategy()
        else:
            logger.info("重连后暂无最新价格，等待行情更新再重建网格")

    async def connect_websocket(self):
        """连接 WebSocket 并订阅 ticker 和持仓数据"""
        async with websockets.connect(WEBSOCKET_URL) as websocket:
            await self.subscribe_ticker(websocket)
            await self.subscribe_positions(websocket)
            await self.subscribe_orders(websocket)  # 订阅挂单更新
            await self.subscribe_book_ticker(websocket)  # 订阅 book_ticker
            await self.subscribe_balances(websocket)  # 订阅余额
            await self.sync_after_reconnect()
            while True:
                try:
                    message = await websocket.recv()
                    data = json.loads(message)
                    if data.get("channel") == "futures.tickers":
                        await self.handle_ticker_update(message)
                    elif data.get("channel") == "futures.positions":
                        await self.handle_position_update(message)
                    elif data.get("channel") == "futures.orders":  # 处理挂单更新
                        await self.handle_order_update(message)
                    elif data.get("channel") == "futures.book_ticker":  # 处理 book_ticker 更新
                        await self.handle_book_ticker_update(message)
                    elif data.get("channel") == "futures.balances":  # 处理余额更新
                        await self.handle_balance_update(message)
                except Exception as e:
                    logger.error(f"WebSocket 消息处理失败: {e}")
                    break

    async def subscribe_balances(self, websocket):
        """订阅合约账户余额频道"""
        current_time = int(time.time())
        message = f"channel=futures.balances&event=subscribe&time={current_time}"
        sign = self._generate_sign(message)
        payload = {
            "time": current_time,
            "channel": "futures.balances",
            "event": "subscribe",
            "payload": ["USDT"],  # 订阅 USDT 余额
            "auth": {
                "method": "api_key",
                "KEY": self.api_key,
                "SIGN": sign,
            },
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已发送余额订阅请求: {payload}")

    async def subscribe_ticker(self, websocket):
        """订阅 ticker 数据"""
        current_time = int(time.time())
        message = f"channel=futures.tickers&event=subscribe&time={current_time}"
        sign = self._generate_sign(message)
        payload = {
            "time": current_time,
            "channel": "futures.tickers",
            "event": "subscribe",
            "payload": [self.ws_symbol],
            "auth": {
                "method": "api_key",
                "KEY": self.api_key,
                "SIGN": sign,
            },
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已发送 ticker 订阅请求: {payload}")

    async def subscribe_book_ticker(self, websocket):
        """订阅 book_ticker 数据"""
        current_time = int(time.time())
        message = f"channel=futures.book_ticker&event=subscribe&time={current_time}"
        sign = self._generate_sign(message)
        payload = {
            "time": current_time,
            "channel": "futures.book_ticker",
            "event": "subscribe",
            "payload": [self.ws_symbol],
            "auth": {
                "method": "api_key",
                "KEY": self.api_key,
                "SIGN": sign,
            },
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已发送 book_ticker 订阅请求: {payload}")

    async def subscribe_orders(self, websocket):
        """订阅挂单更新频道"""
        current_time = int(time.time())
        message = f"channel=futures.orders&event=subscribe&time={current_time}"
        sign = self._generate_sign(message)
        payload = {
            "time": current_time,
            "channel": "futures.orders",
            "event": "subscribe",
            "payload": [self.ws_symbol],
            "auth": {
                "method": "api_key",
                "KEY": self.api_key,
                "SIGN": sign,
            },
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已发送挂单订阅请求: {payload}")

    async def handle_balance_update(self, message):
        """处理余额更新"""
        data = json.loads(message)
        if data.get("channel") == "futures.balances" and data.get("event") == "update":
            balances = data.get("result", [])
            for balance in balances:
                currency = balance.get("currency", "UNKNOWN")  # 币种，默认值为 "UNKNOWN"
                balance_amount = float(balance.get("balance", 0))  # 余额最终数量，默认值为 0
                change = float(balance.get("change", 0))  # 余额变化数量，默认值为 0
                text = balance.get("text", "")  # 附带信息，默认值为空字符串
                balance_time = balance.get("time", 0)  # 时间（秒），默认值为 0
                balance_time_ms = balance.get("time_ms", 0)  # 时间（毫秒），默认值为 0
                balance_type = balance.get("type", "UNKNOWN")  # 类型，默认值为 "UNKNOWN"
                user = balance.get("user", "UNKNOWN")  # 用户 ID，默认值为 "UNKNOWN"

                # 更新余额数据
                self.balance[currency] = {
                    "balance": balance_amount,
                    "change": change,
                    "text": text,
                    "time": balance_time,
                    "time_ms": balance_time_ms,
                    "type": balance_type,
                    "user": user,
                }
                print(
                    f"余额更新: 币种={currency}, 余额={balance_amount}, 变化={change}"
                )


    async def subscribe_positions(self, websocket):
        """订阅持仓数据"""
        current_time = int(time.time())
        message = f"channel=futures.positions&event=subscribe&time={current_time}"
        sign = self._generate_sign(message)
        payload = {
            "time": current_time,
            "channel": "futures.positions",
            "event": "subscribe",
            "payload": [self.ws_symbol],
            "auth": {
                "method": "api_key",
                "KEY": self.api_key,
                "SIGN": sign,
            },
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已发送持仓订阅请求: {payload}")

    def _generate_sign(self, message):
        """生成 HMAC-SHA512 签名"""
        return hmac.new(self.api_secret.encode("utf-8"), message.encode("utf-8"), hashlib.sha512).hexdigest()

    async def handle_ticker_update(self, message):
        """处理 ticker 更新"""
        data = json.loads(message)
        if data.get("event") == "update":
            self.latest_price = float(data["result"][0]["last"])
            print(f"最新价格: {self.latest_price:.8f}")

            # 检查持仓状态是否过时
            if time.time() - self.last_position_update_time > SYNC_TIME:  # 超过 60 秒未更新
                self.long_position, self.short_position = self.get_position()
                self.last_position_update_time = time.time()
                print(f"同步 position: 多头 {self.long_position} 张, 空头 {self.short_position} 张 @ ticker")

            # 检查持仓状态是否过时
            if time.time() - self.last_orders_update_time > SYNC_TIME:  # 超过 60 秒未更新
                self.buy_long_orders, self.sell_long_orders, self.sell_short_orders, self.buy_short_orders = self.check_orders_status()
                self.last_orders_update_time = time.time()
                print(f"同步 orders: 多头买单 {self.buy_long_orders} 张, 多头卖单 {self.sell_long_orders} 张,空头卖单 {self.sell_short_orders} 张, 空头买单 {self.buy_short_orders} 张 @ ticker")

            await self.adjust_grid_strategy()

    async def handle_book_ticker_update(self, message):
        """处理 book_ticker 更新"""
        data = json.loads(message)
        if data.get("event") == "update":
            ticker_data = data["result"]
            # print('book数据', ticker_data)
            if len(ticker_data) > 0:
                ticker = ticker_data
                self.best_bid_price = float(ticker.get("b", 0))  # 最佳买价
                self.best_ask_price = float(ticker.get("a", 0))  # 最佳卖价
                # logger.info(f"最佳买价: {self.best_bid_price}, 最佳卖价: {self.best_ask_price}")

    async def handle_position_update(self, message):
        """处理持仓更新"""
        data = json.loads(message)
        if data.get("event") == "update":
            position_data = data["result"]
            if isinstance(position_data, list) and len(position_data) > 0:
                position = position_data[0]
                if position.get("mode") == "dual_long":
                    self.long_position = abs(float(position.get("size", 0)))  # 更新多头持仓
                    logger.info(f"更新多头持仓: {self.long_position}")
                    # 直接用ticker 数据监控挂单是否有就好了，不需要监控持仓
                    # await self.handle_long_position_update(position)
                else:
                    self.short_position = abs(float(position.get("size", 0)))  # 更新空头持仓
                    logger.info(f"更新空头持仓: {self.short_position}")
                    # await self.handle_short_position_update(position)
                # self.last_position_update_time = time.time()  # 更新持仓时间

    async def handle_order_update(self, message):
        """处理挂单更新"""
        data = json.loads(message)
        # print(data)
        if data.get("event") == "update":
            order_data = data["result"]
            if isinstance(order_data, list) and len(order_data) > 0:
                for order in order_data:
                    # 检查是否包含必要字段
                    if 'is_reduce_only' not in order or 'size' not in order:
                        logger.warning(f"订单 {order.get('id')} 缺少必要字段，跳过处理")
                        continue

                    # 从 order 中提取 size 和 is_reduce_only
                    size = order.get('size', 0)
                    is_reduce_only = order.get('is_reduce_only', False)

                    # 根据 size 和 is_reduce_only 推断订单类型
                    if size > 0:  # 买入
                        if is_reduce_only:
                            order_type = "多头止盈"  # 买入平仓（平掉多头仓位）
                            self.buy_short_orders = abs(order.get('left', 0))  # 空头止盈是买入
                        else:
                            order_type = "多头开仓"  # 买入开仓（建立多头仓位）
                            self.buy_long_orders = abs(order.get('left', 0))
                    else:  # 卖出
                        if is_reduce_only:
                            order_type = "空头止盈"  # 卖出平仓（平掉空头仓位）
                            self.sell_long_orders = abs(order.get('left', 0))  # 多头止盈是卖出
                        else:
                            order_type = "空头开仓"  # 卖出开仓（建立空头仓位）
                            self.sell_short_orders = abs(order.get('left', 0))

                    # print(
                        # f"订单推: {order_type}, size: {size}{is_reduce_only}, left={order.get('left', 0)}")
                    # self.last_orders_update_time = time.time()  # 更新挂单时间

    # async def adjust_long_strategy(self, long_position):
    #     """根据多头持仓调整策略"""
    #
    #     if long_position == 0:
    #         logger.info("多头持仓为 0，初始化多头挂单")
    #         await self.initialize_long_orders()
    #     else:
    #         logger.info("多头持仓不为 0，撤单并重新挂单")
    #         await self.place_long_orders(self.latest_price)
    #
    # async def adjust_short_strategy(self, short_position):
    #     """根据空头持仓调整策略"""
    #
    #     if short_position == 0:
    #         logger.info("空头持仓为 0，初始化空头挂单")
    #         await self.initialize_short_orders()
    #     else:
    #         logger.info("空头持仓不为 0，撤单并重新挂单")
    #         await self.place_short_orders(self.latest_price)

    def get_take_profit_quantity(self, position, side):
        # print(side)

        """调整止盈单的交易数量"""
        if side == 'long' and POSITION_LIMIT < position:
            # logger.info(f"持仓过大超过阈值{POSITION_LIMIT}, {side}双倍止盈止损")
            self.long_initial_quantity = self.initial_quantity * 2

        elif side == 'short' and POSITION_LIMIT < position:
            # logger.info(f"持仓过大超过阈值{POSITION_LIMIT}, {side}双倍止盈止损")
            self.short_initial_quantity = self.initial_quantity * 2

        else:
            self.long_initial_quantity = self.initial_quantity
            self.short_initial_quantity = self.initial_quantity

    async def initialize_long_orders(self):
        # 检查上次挂单时间，确保 10 秒内不重复挂单
        current_time = time.time()
        if current_time - self.last_long_order_time < ORDER_FIRST_TIME:
            logger.info(f"距离上次多头挂单时间不足 {ORDER_FIRST_TIME} 秒，跳过本次挂单")
            return

        self.cancel_orders_for_side('long')

        # 挂出多头开仓单
        self.place_order('buy', (self.best_bid_price + self.best_ask_price) / 2, self.initial_quantity, False, 'long')
        logger.info(f"挂出多头开仓单: 买入 @ {self.latest_price}")

        # 更新上次多头挂单时间
        self.last_long_order_time = time.time()
        logger.info("初始化多头挂单完成")

    async def initialize_short_orders(self):
        # 检查上次挂单时间，确保 10 秒内不重复挂单
        current_time = time.time()
        if current_time - self.last_short_order_time < ORDER_FIRST_TIME:
            print(f"距离上次空头挂单时间不足 {ORDER_FIRST_TIME} 秒，跳过本次挂单")
            return

        # 撤销所有空头挂单
        self.cancel_orders_for_side('short')

        # 挂出空头开仓单
        self.place_order('sell', (self.best_bid_price + self.best_ask_price) / 2, self.initial_quantity, False, 'short')
        logger.info(f"挂出空头开仓单: 卖出 @ {self.latest_price}")

        # 更新上次空头挂单时间
        self.last_short_order_time = time.time()
        logger.info("初始化空头挂单完成")

    def cancel_orders_for_side(self, position_side):
        """撤销某个方向的所有挂单"""
        orders = self.exchange.fetch_open_orders(self.ccxt_symbol)

        if len(orders) == 0:
            logger.info("没有找到挂单")
        else:
            for order in orders:
                if position_side == 'long':
                    # 如果是多头开仓订单：买单且 reduceOnly 为 False
                    if order['reduceOnly'] == False and order['side'] == 'buy' and order['status'] == 'open':
                        # logger.info("发现多头开仓挂单，准备撤销")
                        self.cancel_order(order['id'])  # 撤销该订单
                    # 如果是多头止盈订单：卖单且仓位方向是多头的平仓单
                    elif order['reduceOnly'] == True and order['side'] == 'sell' and order['status'] == 'open':
                        # logger.info("发现多头止盈挂单，准备撤销")
                        self.cancel_order(order['id'])  # 撤销该订单

                elif position_side == 'short':
                    # 如果是空头开仓订单：卖单且 reduceOnly 为 False
                    if order['reduceOnly'] == False and order['side'] == 'sell' and order['status'] == 'open':
                        # logger.info("发现空头开仓挂单，准备撤销")
                        self.cancel_order(order['id'])  # 撤销该订单
                    # 如果是空头止盈订单：买单且仓位方向是空头的平仓单
                    elif order['reduceOnly'] == True and order['side'] == 'buy' and order['status'] == 'open':
                        # logger.info("发现空头止盈挂单，准备撤销")
                        self.cancel_order(order['id'])  # 撤销该订单

    def cancel_order(self, order_id):
        """撤单"""
        try:
            self.exchange.cancel_order(order_id, self.ccxt_symbol)
            # logger.info(f"撤销挂单成功, 订单ID: {order_id}")
        except ccxt.BaseError as e:
            logger.error(f"撤单失败: {e}")

    def place_order(self, side, price, quantity, is_reduce_only=False, position_side=None):
        """挂单函数，增加双向持仓支持"""
        try:
            params = {
                # 'tif': 'poc',
                'reduce_only': is_reduce_only,
                # 'position_side': position_side,  # 'long' 或 'short'
            }
            order = self.exchange.create_order(self.ccxt_symbol, 'limit', side, quantity, price, params)
            # logger.info(
            #     f"挂单成功: {side} {quantity} {self.ccxt_symbol} @ {price}, reduceOnly={is_reduce_only}, position_side={position_side}")
            return order
        except ccxt.BaseError as e:
            logger.error(f"下单报错: {e}")
            return None

    def place_take_profit_order(self, ccxt_symbol, side, price, quantity):
        """挂止盈单（双仓模式）"""
        try:
            if side == 'long':
                # 卖出多头仓位止盈，应该使用 close_long 来平仓
                params = {
                    'reduce_only': True,
                }
                order = self.exchange.create_order(ccxt_symbol, 'limit', 'sell', quantity, price, params)
                logger.info(f"成功挂 long 止盈单: 卖出 {quantity} {ccxt_symbol} @ {price}")
            elif side == 'short':
                # 买入空头仓位止盈，应该使用 close_short 来平仓
                order = self.exchange.create_order(ccxt_symbol, 'limit', 'buy', quantity, price, {
                    'reduce_only': True,
                })
                logger.info(f"成功挂 short 止盈单: 买入 {quantity} {ccxt_symbol} @ {price}")
        except ccxt.BaseError as e:
            logger.error(f"挂止盈单失败: {e}")

    async def place_long_orders(self, latest_price):
        """挂多头订单"""
        try:
            self.get_take_profit_quantity(self.long_position, 'long')
            if self.long_position > 0:
                # print('多头持仓', self.long_position)
                # 检查持仓是否超过阈值
                if self.long_position > POSITION_THRESHOLD:
                    print(f"持仓{self.long_position}超过极限阈值 {POSITION_THRESHOLD}，long装死")
                    # print('多头止盈单', self.sell_long_orders)
                    if self.sell_long_orders <= 0:
                        r = float((int(self.long_position / self.short_position) / 100) + 1)
                        self.place_take_profit_order(self.ccxt_symbol, 'long', self.latest_price * r,
                                                     self.long_initial_quantity)  # 挂止盈
                else:
                    # 检查上次挂单时间，确保 60 秒内不重复挂单
                    # print(f"持仓没超过库存阈值")
                    # 更新中间价
                    self.update_mid_price('long', latest_price)
                    self.cancel_orders_for_side('long')
                    self.place_take_profit_order(self.ccxt_symbol, 'long', self.upper_price_long,
                                                 self.long_initial_quantity)  # 挂止盈
                    self.place_order('buy', self.lower_price_long, self.long_initial_quantity, False, 'long')  # 挂补仓
                    logger.info("挂多头止盈，挂多头补仓")

        except Exception as e:
            logger.error(f"挂多头订单失败: {e}")

    async def place_short_orders(self, latest_price):
        """挂空头订单"""
        try:
            self.get_take_profit_quantity(self.short_position, 'short')
            if self.short_position > 0:
                # 检查持仓是否超过阈值
                if self.short_position > POSITION_THRESHOLD:
                    print(f"持仓{self.short_position}超过极限阈值 {POSITION_THRESHOLD}，short 装死")
                    if self.buy_short_orders <= 0:
                        r = float((int(self.short_position / self.long_position) / 100) + 1)
                        logger.info("发现多头止盈单缺失。。需要补止盈单")
                        self.place_take_profit_order(self.ccxt_symbol, 'short', self.latest_price * r,
                                                     self.short_initial_quantity)  # 挂止盈
                    # self.cancel_orders_for_side('short')
                    #
                else:
                    # 更新中间价
                    self.update_mid_price('short', latest_price)
                    self.cancel_orders_for_side('short')
                    self.place_take_profit_order(self.ccxt_symbol, 'short', self.lower_price_short,
                                                 self.short_initial_quantity)  # 挂止盈
                    self.place_order('sell', self.upper_price_short, self.short_initial_quantity, False, 'short')  # 挂补仓
                    # logger.info("挂空头止盈，挂空头补仓")

        except Exception as e:
            logger.error(f"挂空头订单失败: {e}")

    def check_and_reduce_positions(self):
        """检查持仓并减少库存风险"""

        # 设置持仓阈值
        local_position_threshold = int(POSITION_THRESHOLD * 0.8)  # 阈值的 80%

        # 设置平仓数量
        REDUCE_QUANTITY = int(POSITION_THRESHOLD * 0.1)  # 阈值的 10%

        if self.long_position >= local_position_threshold and self.short_position >= local_position_threshold:
            logger.info(f"多头和空头持仓均超过阈值 {local_position_threshold}，开始双向平仓，减少库存风险")

            # 平仓多头
            if self.long_position > 0:
                self.place_order('sell', self.latest_price, REDUCE_QUANTITY, True, 'long')
                logger.info(f"平仓多头 {REDUCE_QUANTITY} 张")

            # 平仓空头
            if self.short_position > 0:
                self.place_order('buy', self.latest_price, REDUCE_QUANTITY, True, 'short')
                logger.info(f"平仓空头 {REDUCE_QUANTITY} 张")

    def update_mid_price(self, side, price):
        """更新中间价"""
        if side == 'long':
            self.mid_price_long = price  # 更新多头中间价
            # 计算上下网格价格 加上价格精度，price_precision
            self.upper_price_long = self.mid_price_long * (1 + self.grid_spacing)
            self.lower_price_long = self.mid_price_long * (1 - self.grid_spacing)
            print("更新 long 中间价")

        elif side == 'short':
            self.mid_price_short = price  # 更新空头中间价
            # 计算上下网格价格
            self.upper_price_short = self.mid_price_short * (1 + self.grid_spacing)
            self.lower_price_short = self.mid_price_short * (1 - self.grid_spacing)
            print("更新 short 中间价")


    # ==================== 策略逻辑 ====================
    async def adjust_grid_strategy(self):
        """根据最新价格和持仓调整网格策略"""
        # 检查双向仓位库存，如果同时达到，就统一部分平仓减少库存风险，提高保证金使用率
        self.check_and_reduce_positions()

        # # order推流不准没解决，rest请求确认下
        # if (self.buy_long_orders != INITIAL_QUANTITY or self.sell_long_orders != INITIAL_QUANTITY or self.sell_short_orders != INITIAL_QUANTITY or self.buy_short_orders != INITIAL_QUANTITY):
        #     self.buy_long_orders, self.sell_long_orders, self.sell_short_orders, self.buy_short_orders = self.check_orders_status()
        #
        # print('ticker的挂单状态', self.buy_long_orders, self.sell_long_orders, self.sell_short_orders,
        #       self.buy_short_orders)

        current_time = time.time()
        # 检测多头持仓
        if self.long_position == 0:
            print(f"检测到没有多头持仓{self.long_position}，初始化多头挂单@ ticker")
            await self.initialize_long_orders()
        else:
            if not (0 < self.buy_long_orders <= self.long_initial_quantity) or not (0 < self.sell_long_orders <= self.long_initial_quantity):
                if self.long_position > POSITION_THRESHOLD and current_time - self.last_long_order_time < ORDER_COOLDOWN_TIME:
                    print(f"距离上次 long 挂止盈时间不足 {ORDER_COOLDOWN_TIME} 秒，跳过本次 long 挂单@ ticker")
                else:
                    await self.place_long_orders(self.latest_price)

        # 检测空头持仓
        if self.short_position == 0:
            await self.initialize_short_orders()
        else:
            if not (0 < self.sell_short_orders <= self.short_initial_quantity) or not (0 < self.buy_short_orders <= self.short_initial_quantity):
                if self.short_position > POSITION_THRESHOLD and current_time - self.last_short_order_time < ORDER_COOLDOWN_TIME:
                    print(f"距离上次 short 挂止盈时间不足 {ORDER_COOLDOWN_TIME} 秒，跳过本次 short 挂单@ ticker")
                else:
                    await self.place_short_orders(self.latest_price)


# ==================== 主程序 ====================
async def main():
    bot = GridTradingBot(API_KEY, API_SECRET, COIN_NAME, GRID_SPACING, INITIAL_QUANTITY, LEVERAGE)
    await bot.run()

if __name__ == "__main__":
    asyncio.run(main())
