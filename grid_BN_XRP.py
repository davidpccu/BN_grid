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
import asyncio

# ==================== 配置 ====================
API_KEY = os.getenv("BINANCE_API_KEY")
API_SECRET = os.getenv("BINANCE_API_SECRET")
COIN_NAME = "XRP"  # 交易币种
CONTRACT_TYPE = "USDC"  # 合约类型：USDT 或 USDC
GRID_SPACING = 0.0015  # 网格间距 (0.3%)
INITIAL_QUANTITY = 10  # 初始交易数量 (币数量)
LEVERAGE = 5  # 杠杆倍数
WEBSOCKET_URL = "wss://fstream.binance.com/ws"  # WebSocket URL
POSITION_THRESHOLD = 500  # 锁仓阈值
POSITION_LIMIT = 400  # 持仓数量阈值
SYNC_TIME = 10  # 同步时间（秒）
ORDER_FIRST_TIME = 10  # 首单间隔时间

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


class CustomGate(ccxt.binance):
    def fetch(self, url, method='GET', headers=None, body=None):
        if headers is None:
            headers = {}
        # headers['X-Gate-Channel-Id'] = 'laohuoji'
        # headers['Accept'] = 'application/json'
        # headers['Content-Type'] = 'application/json'
        return super().fetch(url, method, headers, body)


# ==================== 网格交易机器人 ====================
class GridTradingBot:
    def __init__(self, api_key, api_secret, coin_name, contract_type, grid_spacing, initial_quantity, leverage):
        self.lock = asyncio.Lock()  # 初始化线程锁
        self.api_key = api_key
        self.api_secret = api_secret
        self.coin_name = coin_name
        self.contract_type = contract_type  # 合约类型：USDT 或 USDC
        self.grid_spacing = grid_spacing
        self.initial_quantity = initial_quantity
        self.leverage = leverage
        self.ccxt_symbol = f"{coin_name}/{contract_type}:{contract_type}"  # 动态生成交易对
        self.exchange = self._initialize_exchange()  # 初始化交易所

        # 获取价格精度{self.price_precision}, 数量精度: {self.amount_precision}, 最小下单数量: {self.min_order_amount}
        self._get_price_precision()

        self.long_initial_quantity = 0  # 多头下单数量
        self.short_initial_quantity = 0  # 空头下单数量
        self.long_position = 0  # 多头持仓 ws监控
        self.short_position = 0  # 空头持仓 ws监控
        self.last_long_order_time = 0  # 上次多头挂单时间
        self.last_short_order_time = 0  # 上次空头挂单时间
        self.buy_long_orders = 0.0  # 多头买入剩余挂单数量
        self.sell_long_orders = 0.0  # 多头卖出剩余挂单数量
        self.sell_short_orders = 0.0  # 空头卖出剩余挂单数量
        self.buy_short_orders = 0.0  # 空头买入剩余挂单数量
        self.last_position_update_time = 0  # 上次持仓更新时间
        self.last_orders_update_time = 0  # 上次订单更新时间
        self.last_ticker_update_time = 0  # ticker 时间限速
        self.last_order_cycle_ts = 0  # 本轮下单处理时间戳
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
        self.listenKey = self.get_listen_key()  # 获取初始 listenKey

        # 检查持仓模式，如果不是双向持仓模式则停止程序
        self.check_and_enable_hedge_mode()


    def _initialize_exchange(self):
        """初始化交易所 API"""
        exchange = CustomGate({
            "apiKey": self.api_key,
            "secret": self.api_secret,
            "options": {
                "defaultType": "future",  # 使用永续合约
            },
        })
        # 加载市场数据
        exchange.load_markets(reload=False)
        try:
            exchange.set_leverage(LEVERAGE, self.ccxt_symbol)
            logger.info(f"设置杠杆成功: {self.ccxt_symbol} {LEVERAGE}x")
        except Exception:
            logger.exception(f"设置杠杆失败: {self.ccxt_symbol} {LEVERAGE}x")
            raise
        return exchange

    def _get_price_precision(self):
        """获取交易对的价格精度、数量精度和最小下单数量"""
        markets = self.exchange.fetch_markets()
        symbol_info = next(market for market in markets if market["symbol"] == self.ccxt_symbol)

        # 获取价格精度
        price_precision = symbol_info["precision"]["price"]
        if isinstance(price_precision, float):
            # 如果 price_precision 是浮点数（例如 0.01），计算小数点后的位数
            self.price_precision = int(abs(math.log10(price_precision)))
        elif isinstance(price_precision, int):
            # 如果 price_precision 是整数，直接使用
            self.price_precision = price_precision
        else:
            raise ValueError(f"未知的价格精度类型: {price_precision}")

        # 获取数量精度
        amount_precision = symbol_info["precision"]["amount"]
        if isinstance(amount_precision, float):
            # 如果 amount_precision 是浮点数（例如 0.001），计算小数点后的位数
            self.amount_precision = int(abs(math.log10(amount_precision)))
        elif isinstance(amount_precision, int):
            # 如果 amount_precision 是整数，直接使用
            self.amount_precision = amount_precision
        else:
            raise ValueError(f"未知的数量精度类型: {amount_precision}")

        # 获取最小下单数量
        self.min_order_amount = symbol_info["limits"]["amount"]["min"]

        logger.info(
            f"价格精度: {self.price_precision}, 数量精度: {self.amount_precision}, 最小下单数量: {self.min_order_amount}")

    def get_position(self):
        """获取当前持仓"""
        params = {
            'type': 'future'  # 永续合约
        }
        positions = self.exchange.fetch_positions(params=params)
        # print(positions)
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
                    self.buy_long_orders = 0.0  # 多头买入剩余挂单数量
                    self.sell_long_orders = 0.0  # 多头卖出剩余挂单数量
                    self.sell_short_orders = 0.0  # 空头卖出剩余挂单数量
                    self.buy_short_orders = 0.0  # 空头买入剩余挂单数量
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
        """检查当前所有挂单的状态，并更新多头和空头的挂单数量"""
        # 获取当前所有挂单（带 symbol 参数，限制为某个交易对）
        orders = self.exchange.fetch_open_orders(symbol=self.ccxt_symbol)

        # 初始化计数器
        buy_long_orders = 0.0  # 使用浮点数
        sell_long_orders = 0.0  # 使用浮点数
        buy_short_orders = 0.0  # 使用浮点数
        sell_short_orders = 0.0  # 使用浮点数

        for order in orders:
            # 获取订单的原始委托数量（取绝对值）
            orig_quantity = abs(float(order.get('info', {}).get('origQty', 0)))  # 从 info 中获取 origQty
            side = order.get('side')  # 订单方向：buy 或 sell
            position_side = order.get('info', {}).get('positionSide')  # 仓位方向：LONG 或 SHORT

            # 判断订单类型
            if side == 'buy' and position_side == 'LONG':  # 多头买单
                buy_long_orders += orig_quantity
            elif side == 'sell' and position_side == 'LONG':  # 多头卖单
                sell_long_orders += orig_quantity
            elif side == 'buy' and position_side == 'SHORT':  # 空头买单
                buy_short_orders += orig_quantity
            elif side == 'sell' and position_side == 'SHORT':  # 空头卖单
                sell_short_orders += orig_quantity

        # 更新实例变量
        self.buy_long_orders = buy_long_orders
        self.sell_long_orders = sell_long_orders
        self.buy_short_orders = buy_short_orders
        self.sell_short_orders = sell_short_orders

    async def run(self):
        """启动 WebSocket 监听"""
        # 初始化时获取一次持仓数据
        self.long_position, self.short_position = self.get_position()
        # self.last_position_update_time = time.time()
        logger.info(f"初始化持仓: 多头 {self.long_position} 张, 空头 {self.short_position} 张")

        # 等待状态同步完成
        await asyncio.sleep(5)  # 等待 5 秒

        # 初始化时获取一次挂单状态
        self.check_orders_status()
        logger.info(
            f"初始化挂单状态: 多头开仓={self.buy_long_orders}, 多头止盈={self.sell_long_orders}, 空头开仓={self.sell_short_orders}, 空头止盈={self.buy_short_orders}")

        # 启动挂单监控任务
        # asyncio.create_task(self.monitor_orders())
        # 启动 listenKey 更新任务
        asyncio.create_task(self.keep_listen_key_alive())

        while True:
            try:
                await self.connect_websocket()
            except Exception as e:
                logger.error(f"WebSocket 连接失败: {e}")
                await asyncio.sleep(5)  # 等待 5 秒后重试

    async def sync_after_reconnect(self):
        """重连后同步持仓与挂单，并按需重建网格"""
        self.long_position, self.short_position = self.get_position()
        self.check_orders_status()
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
            logger.info("重连后暂无最新价格，等待 ticker 更新再重建网格")

    async def connect_websocket(self):
        """连接 WebSocket 并订阅 ticker 和持仓数据"""
        async with websockets.connect(WEBSOCKET_URL) as websocket:
            # 订阅 ticker 数据
            await self.subscribe_ticker(websocket)
            # 订阅挂单数据
            await self.subscribe_orders(websocket)
            await self.sync_after_reconnect()
            while True:
                try:
                    message = await websocket.recv()
                    data = json.loads(message)
                    # print(data)
                    if data.get("e") == "bookTicker":
                        await self.handle_ticker_update(message)
                    elif data.get("e") == "ORDER_TRADE_UPDATE":  # 处理挂单更新
                        await self.handle_order_update(message)
                except Exception as e:
                    logger.error(f"WebSocket 消息处理失败: {e}")
                    break

    async def subscribe_ticker(self, websocket):
        """订阅 ticker 数据"""
        payload = {
            "method": "SUBSCRIBE",
            "params": [f"{self.coin_name.lower()}{self.contract_type.lower()}@bookTicker"],
            "id": 1
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已发送 ticker 订阅请求: {payload}")

    async def subscribe_orders(self, websocket):
        """订阅挂单数据"""
        if not self.listenKey:
            logger.error("listenKey 为空，无法订阅订单更新")
            return

        payload = {
            "method": "SUBSCRIBE",
            "params": [f"{self.listenKey}"],  # 使用 self.listenKey 订阅
            "id": 3
        }
        await websocket.send(json.dumps(payload))
        logger.info(f"已发送挂单订阅请求: {payload}")

    def get_listen_key(self):
        """获取 listenKey"""
        try:
            response = self.exchange.fapiPrivatePostListenKey()
            listenKey = response.get("listenKey")
            if not listenKey:
                raise ValueError("获取的 listenKey 为空")
            logger.info(f"成功获取 listenKey: {listenKey}")
            return listenKey
        except Exception as e:
            logger.error(f"获取 listenKey 失败: {e}")
            raise e

    async def keep_listen_key_alive(self):
        """定期更新 listenKey"""
        while True:
            try:
                await asyncio.sleep(1800)  # 每 30 分钟更新一次
                self.exchange.fapiPrivatePutListenKey()
                self.listenKey = self.get_listen_key()  # 更新 self.listenKey
                logger.info(f"listenKey 已更新: {self.listenKey}")
            except Exception as e:
                logger.error(f"更新 listenKey 失败: {e}")
                await asyncio.sleep(60)  # 等待 60 秒后重试

    def _generate_sign(self, message):
        """生成 HMAC-SHA256 签名"""
        return hmac.new(self.api_secret.encode("utf-8"), message.encode("utf-8"), hashlib.sha256).hexdigest()

    async def handle_ticker_update(self, message):
        current_time = time.time()
        if current_time - self.last_ticker_update_time < 0.5:  # 100ms
            return  # 跳过本次更新

        self.last_ticker_update_time = current_time
        """处理 ticker 更新"""
        data = json.loads(message)
        if data.get("e") == "bookTicker":  # Binance 的 bookTicker 事件
            best_bid_price = data.get("b")
            best_ask_price = data.get("a")

            # 校验字段是否存在且有效
            if best_bid_price is None or best_ask_price is None:
                logger.warning("bookTicker 消息中缺少最佳买价或最佳卖价")
                return

            try:
                self.best_bid_price = float(best_bid_price)  # 最佳买价
                self.best_ask_price = float(best_ask_price)  # 最佳卖价
                self.latest_price = (self.best_bid_price + self.best_ask_price) / 2  # 最新价格
                # logger.info(
                #     f"最新价格: {self.latest_price}, 最佳买价: {self.best_bid_price}, 最佳卖价: {self.best_ask_price}")
            except ValueError as e:
                logger.error(f"解析价格失败: {e}")

            # 检查持仓状态是否过时
            if time.time() - self.last_position_update_time > SYNC_TIME:  # 超过 60 秒未更新
                self.long_position, self.short_position = self.get_position()
                self.last_position_update_time = time.time()
                logger.info(f"同步 position: 多头 {self.long_position} 张, 空头 {self.short_position} 张 @ ticker")

            # 检查持仓状态是否过时
            if time.time() - self.last_orders_update_time > SYNC_TIME:  # 超过 60 秒未更新
                self.check_orders_status()
                self.last_orders_update_time = time.time()
                logger.info(f"同步 orders: 多头买单 {self.buy_long_orders} 张, 多头卖单 {self.sell_long_orders} 张,空头卖单 {self.sell_short_orders} 张, 空头买单 {self.buy_short_orders} 张 @ ticker")

            await self.adjust_grid_strategy()

    async def handle_order_update(self, message):
        async with self.lock:
            """处理订单更新和持仓更新"""
            data = json.loads(message)
            # print(f"收到消息: {data}")  # 打印原始数据

            if data.get("e") == "ORDER_TRADE_UPDATE":  # 处理订单更新
                order = data.get("o", {})
                symbol = order.get("s")  # 交易对
                if symbol == f"{self.coin_name}{self.contract_type}":  # 匹配交易对
                    side = order.get("S")  # 订单方向：BUY 或 SELL
                    position_side = order.get("ps")  # 仓位方向：LONG 或 SHORT
                    reduce_only = order.get("R")  # 是否为平仓单
                    status = order.get("X")  # 订单状态
                    quantity = float(order.get("q", 0))  # 订单数量
                    filled = float(order.get("z", 0))  # 已成交数量
                    remaining = quantity - filled  # 剩余数量

                    if status == "NEW":
                        if side == "BUY":
                            if position_side == "LONG":  # 多头开仓单
                                self.buy_long_orders += remaining
                            elif position_side == "SHORT":  # 空头止盈单
                                self.buy_short_orders += remaining
                        elif side == "SELL":
                            if position_side == "LONG":  # 多头止盈单
                                self.sell_long_orders += remaining
                            elif position_side == "SHORT":  # 空头开仓单
                                self.sell_short_orders += remaining
                    elif status == "FILLED":  # 订单已成交
                        if side == "BUY":
                            if position_side == "LONG":  # 多头开仓单
                                self.long_position += filled  # 更新多头持仓
                                self.buy_long_orders = max(0.0, self.buy_long_orders - filled)  # 更新挂单状态
                            elif position_side == "SHORT":  # 空头止盈单
                                self.short_position = max(0.0, self.short_position - filled)  # 更新空头持仓
                                self.buy_short_orders = max(0.0, self.buy_short_orders - filled)  # 更新挂单状态
                        elif side == "SELL":
                            if position_side == "LONG":  # 多头止盈单
                                self.long_position = max(0.0, self.long_position - filled)  # 更新多头持仓
                                self.sell_long_orders = max(0.0, self.sell_long_orders - filled)  # 更新挂单状态
                            elif position_side == "SHORT":  # 空头开仓单
                                self.short_position += filled  # 更新空头持仓
                                self.sell_short_orders = max(0.0, self.sell_short_orders - filled)  # 更新挂单状态
                    elif status == "CANCELED":  # 订单已取消
                        if side == "BUY":
                            if position_side == "LONG":  # 多头开仓单
                                self.buy_long_orders = max(0.0, self.buy_long_orders - quantity)
                            elif position_side == "SHORT":  # 空头止盈单
                                self.buy_short_orders = max(0.0, self.buy_short_orders - quantity)
                        elif side == "SELL":
                            if position_side == "LONG":  # 多头止盈单
                                self.sell_long_orders = max(0.0, self.sell_long_orders - quantity)
                            elif position_side == "SHORT":  # 空头开仓单
                                self.sell_short_orders = max(0.0, self.sell_short_orders - quantity)

                    # # 打印当前挂单状态
                    # logger.info(
                    #     f"挂单状态: 多头开仓={self.buy_long_orders}, 多头止盈={self.sell_long_orders}, 空头开仓={self.sell_short_orders}, 空头止盈={self.buy_short_orders}")
                    # # 打印当前持仓状态
                    # logger.info(f"持仓状态: 多头={self.long_position}, 空头={self.short_position}")

    def get_take_profit_quantity(self, position, side):
        # print(side)

        """调整止盈单的交易数量"""
        if side == 'long':
            if position > POSITION_LIMIT:
                # logger.info(f"持仓过大超过阈值{POSITION_LIMIT}, {side}双倍止盈止损")
                self.long_initial_quantity = self.initial_quantity * 2

            # 如果 short 锁仓 long 两倍
            elif self.short_position >= POSITION_THRESHOLD:
                self.long_initial_quantity = self.initial_quantity * 2
            else:
                self.long_initial_quantity = self.initial_quantity

        elif side == 'short':
            if position > POSITION_LIMIT:
                # logger.info(f"持仓过大超过阈值{POSITION_LIMIT}, {side}双倍止盈止损")
                self.short_initial_quantity = self.initial_quantity * 2

            # 如果 long 锁仓 short 两倍
            elif self.long_position >= POSITION_THRESHOLD:
                self.short_initial_quantity = self.initial_quantity * 2
            else:
                self.short_initial_quantity = self.initial_quantity

    async def initialize_long_orders(self):
        # 检查上次挂单时间，确保 10 秒内不重复挂单
        current_time = time.time()
        if current_time - self.last_long_order_time < ORDER_FIRST_TIME:
            logger.info(f"距离上次多头挂单时间不足 {ORDER_FIRST_TIME} 秒，跳过本次挂单")
            return

        # # 检查是否有未成交的挂单
        # orders = self.exchange.fetch_open_orders(self.ccxt_symbol)
        # if any(order['side'] == 'buy' and order['info'].get('positionSide') == 'LONG' for order in orders):
        #     logger.info("发现未成交的多头补仓单，跳过撤销和挂单")
        #     return

        self.cancel_orders_for_side('long')

        # 挂出多头开仓单
        order = self.place_order('buy', self.best_bid_price, self.initial_quantity, False, 'long')
        logger.info(f"挂出多头开仓单: 买入 @ {self.latest_price}")

        # 更新上次多头挂单时间
        if order:
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
        order = self.place_order('sell', self.best_ask_price, self.initial_quantity, False, 'short')
        logger.info(f"挂出空头开仓单: 卖出 @ {self.latest_price}")

        # 更新上次空头挂单时间
        if order:
            self.last_short_order_time = time.time()
        logger.info("初始化空头挂单完成")

    def cancel_orders_for_side(self, position_side):
        """撤销某个方向的所有挂单"""
        orders = self.exchange.fetch_open_orders(self.ccxt_symbol)

        if len(orders) == 0:
            logger.info("没有找到挂单")
        else:
            try:
                for order in orders:
                    # 获取订单的方向和仓位方向
                    side = order.get('side')  # 订单方向：buy 或 sell
                    reduce_only = order.get('reduceOnly', False)  # 是否为平仓单
                    position_side_order = order.get('info', {}).get('positionSide', 'BOTH')  # 仓位方向：LONG 或 SHORT

                    if position_side == 'long':
                        # 如果是多头开仓订单：买单且 reduceOnly 为 False
                        if not reduce_only and side == 'buy' and position_side_order == 'LONG':
                            # logger.info("发现多头开仓挂单，准备撤销")
                            self.cancel_order(order['id'])  # 撤销该订单
                        # 如果是多头止盈订单：卖单且 reduceOnly 为 True
                        elif reduce_only and side == 'sell' and position_side_order == 'LONG':
                            # logger.info("发现多头止盈挂单，准备撤销")
                            self.cancel_order(order['id'])  # 撤销该订单

                    elif position_side == 'short':
                        # 如果是空头开仓订单：卖单且 reduceOnly 为 False
                        if not reduce_only and side == 'sell' and position_side_order == 'SHORT':
                            # logger.info("发现空头开仓挂单，准备撤销")
                            self.cancel_order(order['id'])  # 撤销该订单
                        # 如果是空头止盈订单：买单且 reduceOnly 为 True
                        elif reduce_only and side == 'buy' and position_side_order == 'SHORT':
                            # logger.info("发现空头止盈挂单，准备撤销")
                            self.cancel_order(order['id'])  # 撤销该订单
            except ccxt.OrderNotFound as e:
                logger.warning(f"订单 {order['id']} 不存在，无需撤销: {e}")
                self.check_orders_status()  # 强制更新挂单状态
            except Exception as e:
                logger.error(f"撤单失败: {e}")

    def cancel_order(self, order_id):
        """撤单"""
        try:
            self.exchange.cancel_order(order_id, self.ccxt_symbol)
            # logger.info(f"撤销挂单成功, 订单ID: {order_id}")
        except ccxt.BaseError as e:
            logger.error(f"撤单失败: {e}")

    def place_order(self, side, price, quantity, is_reduce_only=False, position_side=None, order_type='limit'):
        """挂单函数，增加双向持仓支持"""
        try:
            # 修正价格精度
            price = round(price, self.price_precision)

            # 修正数量精度并确保不低于最小下单数量
            quantity = round(quantity, self.amount_precision)
            quantity = max(quantity, self.min_order_amount)

            # 如果是市价单，不需要价格参数
            if order_type == 'market':
                params = {
                    'reduce_only': is_reduce_only,
                }
                if position_side is not None:
                    params['positionSide'] = position_side.upper()  # Binance 要求大写：LONG 或 SHORT
                order = self.exchange.create_order(self.ccxt_symbol, 'market', side, quantity, params=params)
                return order
            else:
                # 检查 price 是否为 None
                if price is None:
                    logger.error("限价单必须提供 price 参数")
                    return None

                params = {
                    'reduce_only': is_reduce_only,
                }
                if position_side is not None:
                    params['positionSide'] = position_side.upper()  # Binance 要求大写：LONG 或 SHORT
                order = self.exchange.create_order(self.ccxt_symbol, 'limit', side, quantity, price, params)
                return order

        except ccxt.BaseError as e:
            logger.error(f"下单报错: {e}")
            return None

    def place_take_profit_order(self, ccxt_symbol, side, price, quantity):
        # print('止盈单价格', price)
        # 检查是否已有相同价格的挂单
        orders = self.exchange.fetch_open_orders(ccxt_symbol)
        for order in orders:
            if (
                    order['info'].get('positionSide') == side.upper()
                    and float(order['price']) == price
                    and order['side'] == ('sell' if side == 'long' else 'buy')
            ):
                logger.info(f"已存在相同价格的 {side} 止盈单，跳过挂单")
                return
        """挂止盈单（双仓模式）"""
        try:
            # 检查持仓
            if side == 'long' and self.long_position <= 0:
                logger.warning("没有多头持仓，跳过挂出多头止盈单")
                return
            elif side == 'short' and self.short_position <= 0:
                logger.warning("没有空头持仓，跳过挂出空头止盈单")
                return
            # 修正价格精度
            price = round(price, self.price_precision)

            # 修正数量精度并确保不低于最小下单数量
            quantity = round(quantity, self.amount_precision)
            quantity = max(quantity, self.min_order_amount)

            if side == 'long':
                # 卖出多头仓位止盈，应该使用 close_long 来平仓
                params = {
                    'reduce_only': True,
                    'positionSide': 'LONG'
                }
                order = self.exchange.create_order(ccxt_symbol, 'limit', 'sell', quantity, price, params)
                logger.info(f"成功挂 long 止盈单: 卖出 {quantity} {ccxt_symbol} @ {price}")
                return order
            elif side == 'short':
                # 买入空头仓位止盈，应该使用 close_short 来平仓
                order = self.exchange.create_order(ccxt_symbol, 'limit', 'buy', quantity, price, {
                    'reduce_only': True,
                    'positionSide': 'SHORT'
                })
                logger.info(f"成功挂 short 止盈单: 买入 {quantity} {ccxt_symbol} @ {price}")
                return order
        except ccxt.BaseError as e:
            logger.error(f"挂止盈单失败: {e}")
        return None

    async def place_long_orders(self, latest_price):
        """挂多头订单"""
        try:
            self.get_take_profit_quantity(self.long_position, 'long')
            if self.long_position > 0:
                # print('多头持仓', self.long_position)
                # 检查持仓是否超过阈值
                if self.long_position > POSITION_THRESHOLD:
                    print(f"持仓{self.long_position}超过极限阈值 {POSITION_THRESHOLD}，long装死")
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
                        )  # 挂止盈
                        if take_profit_order:
                            self.last_long_order_time = time.time()
                else:
                    # 更新中间价
                    self.update_mid_price('long', latest_price)
                    self.cancel_orders_for_side('long')
                    take_profit_order = self.place_take_profit_order(
                        self.ccxt_symbol,
                        'long',
                        self.upper_price_long,
                        self.long_initial_quantity,
                    )  # 挂止盈
                    if take_profit_order:
                        self.last_long_order_time = time.time()
                    open_order = self.place_order(
                        'buy',
                        self.lower_price_long,
                        self.long_initial_quantity,
                        False,
                        'long',
                    )  # 挂补仓
                    if open_order:
                        self.last_long_order_time = time.time()
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
                        if self.long_position == 0:
                            r = 1 + GRID_SPACING
                        else:
                            r = float((self.short_position / self.long_position) / 100 + 1)
                        logger.info("发现多头止盈单缺失。。需要补止盈单")
                        take_profit_order = self.place_take_profit_order(
                            self.ccxt_symbol,
                            'short',
                            self.latest_price * r,
                            self.short_initial_quantity,
                        )  # 挂止盈
                        if take_profit_order:
                            self.last_short_order_time = time.time()

                else:
                    # 更新中间价
                    self.update_mid_price('short', latest_price)
                    self.cancel_orders_for_side('short')
                    take_profit_order = self.place_take_profit_order(
                        self.ccxt_symbol,
                        'short',
                        self.lower_price_short,
                        self.short_initial_quantity,
                    )  # 挂止盈
                    if take_profit_order:
                        self.last_short_order_time = time.time()
                    open_order = self.place_order(
                        'sell',
                        self.upper_price_short,
                        self.short_initial_quantity,
                        False,
                        'short',
                    )  # 挂补仓
                    if open_order:
                        self.last_short_order_time = time.time()
                    logger.info("挂空头止盈，挂空头补仓")

        except Exception as e:
            logger.error(f"挂空头订单失败: {e}")

    def check_and_enable_hedge_mode(self):
        """检查并启用双向持仓模式，如果切换失败则停止程序"""
        try:
            # 获取当前持仓模式
            position_mode = self.exchange.fetch_position_mode(symbol=self.ccxt_symbol)
            if not position_mode['hedged']:
                # 如果当前不是双向持仓模式，尝试启用双向持仓模式
                logger.info("当前不是双向持仓模式，尝试自动启用双向持仓模式...")
                self.enable_hedge_mode()

                # 再次检查持仓模式，确认是否启用成功
                position_mode = self.exchange.fetch_position_mode(symbol=self.ccxt_symbol)
                if not position_mode['hedged']:
                    # 如果仍然不是双向持仓模式，记录错误日志并停止程序
                    logger.error("启用双向持仓模式失败，请手动启用双向持仓模式后再运行程序。")
                    raise Exception("启用双向持仓模式失败，请手动启用双向持仓模式后再运行程序。")
                else:
                    logger.info("双向持仓模式已成功启用，程序继续运行。")
            else:
                logger.info("当前已是双向持仓模式，程序继续运行。")
        except Exception as e:
            logger.error(f"检查或启用双向持仓模式失败: {e}")
            raise e  # 抛出异常，停止程序

    def enable_hedge_mode(self):
        """启用双向持仓模式"""
        try:
            # 使用 ccxt 的 fapiPrivatePostPositionSideDual 函数
            params = {
                'dualSidePosition': 'true',  # 启用双向持仓模式
            }
            response = self.exchange.fapiPrivatePostPositionSideDual(params)
            logger.info(f"启用双向持仓模式: {response}")
        except Exception as e:
            logger.error(f"启用双向持仓模式失败: {e}")
            raise e  # 抛出异常，停止程序

    def check_and_reduce_positions(self):
        """检查持仓并减少库存风险"""

        # 设置持仓阈值
        local_position_threshold = POSITION_THRESHOLD * 0.8  # 阈值的 80%

        # 设置平仓数量
        quantity = POSITION_THRESHOLD * 0.1  # 阈值的 10%

        if self.long_position >= local_position_threshold and self.short_position >= local_position_threshold:
            logger.info(f"多头和空头持仓均超过阈值 {local_position_threshold}，开始双向平仓，减少库存风险")
            # 平仓多头（使用市价单）
            if self.long_position > 0:
                self.place_order('sell', price=self.best_ask_price, quantity=quantity, is_reduce_only=True, position_side='long',
                                 order_type='market')
                logger.info(f"市价平仓多头 {quantity} 个")

            # 平仓空头（使用市价单）
            if self.short_position > 0:
                self.place_order('buy', price=self.best_bid_price, quantity=quantity, is_reduce_only=True, position_side='short',
                                 order_type='market')
                logger.info(f"市价平仓空头 {quantity} 个")

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
        cycle_ts = self.last_ticker_update_time or time.time()
        if cycle_ts == self.last_order_cycle_ts:
            return
        self.last_order_cycle_ts = cycle_ts

        # 检查双向仓位库存，如果同时达到，就统一部分平仓减少库存风险，提高保证金使用率
        self.check_and_reduce_positions()
        # print(self.latest_price, '多挂', self.buy_long_orders, '多平', self.buy_long_orders, '空挂', self.sell_short_orders, '空平', self.buy_short_orders)

        # 检测多头持仓
        if self.long_position == 0:
            print(f"检测到没有多头持仓{self.long_position}，初始化多头挂单@ ticker")
            await self.initialize_long_orders()
        else:
            orders_valid = not (0 < self.buy_long_orders <= self.long_initial_quantity) or \
                           not (0 < self.sell_long_orders <= self.long_initial_quantity)
            if orders_valid:
                if self.long_position < POSITION_THRESHOLD:
                    print('如果 long 持仓没到阈值，同步后再次确认！')
                    self.check_orders_status()
                    if orders_valid:
                        await self.place_long_orders(self.latest_price)
                else:
                    await self.place_long_orders(self.latest_price)
        # 检测空头持仓
        if self.short_position == 0:
            await self.initialize_short_orders()
        else:
            # 检查订单数量是否在合理范围内
            orders_valid = not (0 < self.sell_short_orders <= self.short_initial_quantity) or \
                           not (0 < self.buy_short_orders <= self.short_initial_quantity)
            if orders_valid:
                if self.short_position < POSITION_THRESHOLD:
                    print('如果 short 持仓没到阈值，同步后再次确认！')
                    self.check_orders_status()
                    if orders_valid:
                        await self.place_short_orders(self.latest_price)
                else:
                    await self.place_short_orders(self.latest_price)


# ==================== 主程序 ====================
async def main():
    bot = GridTradingBot(API_KEY, API_SECRET, COIN_NAME, CONTRACT_TYPE, GRID_SPACING, INITIAL_QUANTITY, LEVERAGE)
    await bot.run()

if __name__ == "__main__":
    asyncio.run(main())
