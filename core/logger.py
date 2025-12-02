"""
日志配置模块：为整个项目提供统一的日志管理
"""
import logging
import sys
from pathlib import Path
from datetime import datetime
from typing import Optional
from functools import wraps


# 全局变量：存储当前批次的时间戳和根目录
_current_timestamp = None
_current_log_root = None
_current_constraint_id = None


def get_timestamp_dir() -> Path:
    """获取当前批次的时间戳目录"""
    global _current_timestamp, _current_log_root
    
    if _current_log_root is None:
        if _current_timestamp is None:
            _current_timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        
        # 从 logger.py 文件位置推断项目根目录
        # E:\vscode_workplace\cube\core\logger.py -> E:\vscode_workplace\cube
        project_root = Path(__file__).resolve().parent.parent
        
        _current_log_root = project_root / "logs" / _current_timestamp
        _current_log_root.mkdir(parents=True, exist_ok=True)
    
    return _current_log_root


def set_current_constraint(constraint_id: str):
    """设置当前处理的约束 ID"""
    global _current_constraint_id
    _current_constraint_id = constraint_id


def get_current_constraint() -> Optional[str]:
    """获取当前约束 ID"""
    return _current_constraint_id


class ColoredFormatter(logging.Formatter):
    """彩色日志格式化器（仅用于控制台输出）"""
    
    COLORS = {
        'DEBUG': '\033[36m',
        'INFO': '\033[32m',
        'WARNING': '\033[33m',
        'ERROR': '\033[31m',
        'CRITICAL': '\033[35m',
        'RESET': '\033[0m'
    }
    
    def format(self, record):
        record = logging.makeLogRecord(record.__dict__)
        levelname = record.levelname
        if levelname in self.COLORS:
            record.levelname = f"{self.COLORS[levelname]}{levelname}{self.COLORS['RESET']}"
        return super().format(record)


# ✅ 在这里添加 AlignedFormatter 类
class AlignedFormatter(logging.Formatter):
    """对齐的日志格式化器（用于文件输出，智能处理过长的模块名）"""
    
    def format(self, record):
        location = f"{record.name}:{record.lineno}"
        width = 20
        
        # 智能截断：保留模块末尾和行号
        if len(location) > width:
            line_no = str(record.lineno)
            available = width - len(line_no) - 4  # 预留 "...:" 的空间
            location = f"{record.name[:available]}...:{line_no}"
        
        location_str = location.ljust(width)
        
        log_format = (
            f"%(asctime)s|%(levelname)-7s|"
            f"{location_str}|%(funcName)-17s| %(message)s"
        )
        formatter = logging.Formatter(log_format, datefmt='%Y-%m-%d %H:%M:%S')
        return formatter.format(record)


def flush_all_handlers():
    """刷新所有 logger 的 handlers"""
    root_logger = logging.getLogger()
    for handler in root_logger.handlers:
        try:
            handler.flush()
        except Exception:
            pass
    
    for name in list(logging.Logger.manager.loggerDict.keys()):
        logger = logging.getLogger(name)
        for handler in logger.handlers:
            try:
                handler.flush()
            except Exception:
                pass


def setup_logger(
    name: str = "cube",
    level: int = logging.DEBUG,
    log_to_file: bool = True,
    console_level: int = logging.INFO,
    file_level: int = logging.DEBUG
) -> logging.Logger:
    """
    设置主日志系统。
    
    参数:
        name: logger 名称
        level: 整体日志级别
        log_to_file: 是否写入文件
        console_level: 控制台日志级别
        file_level: 文件日志级别
    
    返回:
        配置好的 logger
    """
    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.handlers.clear()
    
    # 格式化器
    console_format = logging.Formatter(
        fmt='%(asctime)s | %(levelname)-8s | %(message)s',  # -7 → -8
        datefmt='%H:%M:%S'
    )
    
    file_format = logging.Formatter(
        fmt='%(asctime)s|%(levelname)-8s|%(funcName)-15s| %(message)s',  # -7 → -8
        datefmt='%H:%M:%S'
    )
    
    # 控制台 handler
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(console_level)
    console_handler.setFormatter(console_format)
    logger.addHandler(console_handler)
    
    # 文件 handler（batch_main.log）
    if log_to_file:
        timestamp_dir = get_timestamp_dir()
        batch_log = timestamp_dir / "batch_main.log"
        
        batch_handler = logging.FileHandler(batch_log, encoding='utf-8')
        batch_handler.setLevel(file_level)
        batch_handler.setFormatter(file_format)
        logger.addHandler(batch_handler)
        
        logger.info(f"Batch log: {batch_log.absolute()}")
    
    logger.propagate = False
    return logger


_global_logger: Optional[logging.Logger] = None


def get_logger(name: Optional[str] = None) -> logging.Logger:
    """获取 logger 实例"""
    global _global_logger
    
    if name is None:
        if _global_logger is None:
            _global_logger = setup_logger()
        return _global_logger
    
    return logging.getLogger(f"cube.{name}")


def set_log_level(level: int):
    """动态设置日志级别"""
    logger = get_logger()
    logger.setLevel(level)
    for handler in logger.handlers:
        handler.setLevel(level)


# ========== ✅ 新增：异常处理装饰器 ==========

def log_on_error(logger=None, reraise=True, default_return=None):
    """
    装饰器：当函数抛出异常时自动记录日志。
    
    这是"三层异常处理架构"的核心工具：
    - 底层函数：不使用此装饰器，直接抛出异常
    - 中层函数：使用 @log_on_error(reraise=True)，记录后重新抛出
    - 顶层函数：使用 @log_on_error(reraise=False)，记录后返回默认值
    
    参数:
        logger: 使用的 logger，默认使用函数所在模块的 logger
        reraise: 是否重新抛出异常，默认 True
        default_return: 如果不重新抛出，返回的默认值
    
    使用示例:
        @log_on_error()  # 中层：记录并重新抛出
        def middle_function():
            raise ValueError("Something wrong")
        
        @log_on_error(reraise=False, default_return={})  # 顶层：记录但不抛出
        def top_function():
            raise ValueError("Something wrong")
    """
    def decorator(func):
        @wraps(func)
        def wrapper(*args, **kwargs):
            func_logger = logger or get_logger()
            try:
                return func(*args, **kwargs)
            except Exception as e:
                # 记录异常（使用 exception 自动记录堆栈）
                func_logger.exception(
                    f"异常发生在 {func.__module__}.{func.__name__}(): "
                    f"{type(e).__name__}: {e}"
                )
                
                # 立即刷新日志
                flush_all_handlers()
                
                # 决定是否重新抛出
                if reraise:
                    raise
                else:
                    func_logger.warning(f"异常被捕获，返回默认值: {default_return}")
                    return default_return
        return wrapper
    return decorator


# 便捷函数
def debug(msg, *args, **kwargs):
    get_logger().debug(msg, *args, **kwargs)


def info(msg, *args, **kwargs):
    get_logger().info(msg, *args, **kwargs)


def warning(msg, *args, **kwargs):
    get_logger().warning(msg, *args, **kwargs)


def error(msg, *args, **kwargs):
    get_logger().error(msg, *args, **kwargs)


def critical(msg, *args, **kwargs):
    get_logger().critical(msg, *args, **kwargs)


class TruncatingFormatter(logging.Formatter):
    """自定义格式化器：截断过长的 logger 名称并保持对齐"""
    
    def __init__(self, fmt=None, datefmt=None, max_name_width=25):
        """
        参数:
            fmt: 格式字符串
            datefmt: 时间格式
            max_name_width: logger 名称最大宽度（超出用省略号）
        """
        super().__init__(fmt, datefmt)
        self.max_name_width = max_name_width
    
    def format(self, record):
        # 保存原始名称
        original_name = record.name
        
        # 如果名称太长，截断并添加省略号
        if len(record.name) > self.max_name_width:
            truncated = record.name[:self.max_name_width - 3] + "..."
        else:
            truncated = record.name
        
        # ✅ 关键：强制填充到固定宽度（左对齐）
        record.name = truncated.ljust(self.max_name_width)
        
        # 调用父类格式化
        result = super().format(record)
        
        # 恢复原始名称
        record.name = original_name
        
        return result


class DualTruncatingFormatter(logging.Formatter):
    """自定义格式化器：同时截断 logger 名称和函数名"""
    
    def __init__(self, fmt=None, datefmt=None, max_name_width=30, max_func_width=20):
        """
        参数:
            fmt: 格式字符串
            datefmt: 时间格式
            max_name_width: logger 名称最大宽度
            max_func_width: 函数名最大宽度
        """
        super().__init__(fmt, datefmt)
        self.max_name_width = max_name_width
        self.max_func_width = max_func_width
    
    def format(self, record):
        # 保存原始值
        original_name = record.name
        original_func = record.funcName
        
        # 截断并填充 logger 名称
        if len(record.name) > self.max_name_width:
            truncated_name = record.name[:self.max_name_width - 3] + "..."
        else:
            truncated_name = record.name
        record.name = truncated_name.ljust(self.max_name_width)
        
        # 截断并填充函数名
        if len(record.funcName) > self.max_func_width:
            truncated_func = record.funcName[:self.max_func_width - 3] + "..."
        else:
            truncated_func = record.funcName
        record.funcName = truncated_func.ljust(self.max_func_width)
        
        # 格式化
        result = super().format(record)
        
        # 恢复原始值
        record.name = original_name
        record.funcName = original_func
        
        return result


# 全局统一的格式配置
COMMON_DATE_FORMAT = '%H:%M:%S'
LOGGER_NAME_WIDTH = 30  # Logger 名称列宽度
FUNC_NAME_WIDTH = 20    # 函数名列宽度


class ConstraintLoggerGroup:
    """约束日志组：管理一个约束的所有日志文件"""
    
    def __init__(self, constraint_id: str):
        self.constraint_id = constraint_id
        
        # 创建目录结构
        timestamp_dir = get_timestamp_dir()
        self.constraint_dir = timestamp_dir / constraint_id
        self.sp_dir = self.constraint_dir / "SP"
        self.constraint_dir.mkdir(parents=True, exist_ok=True)
        self.sp_dir.mkdir(exist_ok=True)
        
        # ✅ 统一使用 5 列格式（时间 | 级别 | Logger名 | 函数名 | 消息）
        self.file_format = DualTruncatingFormatter(
            fmt='%(asctime)s|%(levelname)-8s|%(name)s|%(funcName)s| %(message)s',
            datefmt=COMMON_DATE_FORMAT,
            max_name_width=LOGGER_NAME_WIDTH,
            max_func_width=FUNC_NAME_WIDTH
        )
        
        # 创建 3 个文件 handler
        # 1. main.log
        self.main_handler = logging.FileHandler(
            self.constraint_dir / "main.log", 
            encoding='utf-8'
        )
        self.main_handler.setLevel(logging.DEBUG)
        self.main_handler.setFormatter(self.file_format)
        
        # 2. errors.log
        self.errors_handler = logging.FileHandler(
            self.constraint_dir / "errors.log",
            encoding='utf-8'
        )
        self.errors_handler.setLevel(logging.ERROR)
        self.errors_handler.setFormatter(self.file_format)
        
        # 3. batch_main.log handler（使用相同格式）
        # self.batch_handler = logging.FileHandler(
        #     timestamp_dir / "batch_main.log",
        #     encoding='utf-8'
        # )
        # self.batch_handler.setLevel(logging.INFO)
        # self.batch_handler.setFormatter(self.file_format)
        
        # 创建约束级别的 logger
        self.constraint_logger = self._create_constraint_logger()
    
    def _create_constraint_logger(self) -> logging.Logger:
        """创建约束级别的 logger"""
        logger = logging.getLogger(f"cube.constraint.{self.constraint_id}")
        logger.setLevel(logging.DEBUG)
        logger.handlers.clear()
        logger.propagate = False
        
        # 添加 handler
        logger.addHandler(self.main_handler)
        logger.addHandler(self.errors_handler)
        # logger.addHandler(self.batch_handler)
        
        return logger
    
    def create_sp_logger(self, sp_id: str, sp_type: str) -> logging.Logger:
        """
        创建 Solver/Partition 专用 logger。
        
        自动记录到：
        1. SP/{sp_id}_{sp_type}.log（专用日志）
        2. main.log（通过添加 main_handler）
        3. errors.log（ERROR 及以上，通过 errors_handler）
        
        参数:
            sp_id: 如 "x6eq2mx5_0_0"
            sp_type: "solver" 或 "partition"
        """
        # SP 专用日志文件
        sp_log_file = self.sp_dir / f"{sp_id}_{sp_type}.log"
        sp_handler = logging.FileHandler(sp_log_file, encoding='utf-8')
        sp_handler.setLevel(logging.DEBUG)
        sp_handler.setFormatter(self.file_format)  # ✅ 使用 5 列格式
        
        # 创建 logger
        logger = logging.getLogger(f"cube.constraint.{self.constraint_id}.{sp_type}.{sp_id}")
        logger.setLevel(logging.DEBUG)
        logger.handlers.clear()
        logger.propagate = False  # ✅ 不传播，手动控制
        
        # ✅ 添加 3 个 handler：SP 专用 + main.log + errors.log
        logger.addHandler(sp_handler)           # SP/{sp_id}_{sp_type}.log
        logger.addHandler(self.main_handler)    # main.log
        logger.addHandler(self.errors_handler)  # errors.log
        
        return logger
    
    def get_constraint_logger(self) -> logging.Logger:
        """获取约束级别的 logger"""
        return self.constraint_logger


# 全局管理器：存储当前约束的 LoggerGroup
_current_logger_group: Optional[ConstraintLoggerGroup] = None


def setup_logger(
    name: str = "cube",
    level: int = logging.DEBUG,
    log_to_file: bool = True,
    console_level: int = logging.INFO
) -> logging.Logger:
    """设置主日志系统（batch 级别）"""
    logger = logging.getLogger(name)
    logger.setLevel(level)
    logger.handlers.clear()
    
    # 控制台格式（简化，3列）
    console_format = logging.Formatter(
        fmt='%(asctime)s | %(levelname)-8s | %(message)s',
        datefmt=COMMON_DATE_FORMAT
    )
    
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(console_level)
    console_handler.setFormatter(console_format)
    logger.addHandler(console_handler)
    
    # ✅ batch_main.log：使用 5 列格式
    if log_to_file:
        timestamp_dir = get_timestamp_dir()
        batch_log = timestamp_dir / "batch_main.log"
        
        batch_handler = logging.FileHandler(batch_log, encoding='utf-8')
        batch_handler.setLevel(logging.INFO)
        
        file_format = DualTruncatingFormatter(
            fmt='%(asctime)s|%(levelname)-8s|%(name)s|%(funcName)s| %(message)s',
            datefmt=COMMON_DATE_FORMAT,
            max_name_width=LOGGER_NAME_WIDTH,
            max_func_width=FUNC_NAME_WIDTH
        )
        batch_handler.setFormatter(file_format)
        logger.addHandler(batch_handler)
        
        logger.info(f"Batch log: {batch_log.absolute()}")
    
    logger.propagate = False
    return logger


def setup_constraint_logger(constraint_id: str) -> logging.Logger:
    """
    为约束组设置日志系统。
    
    返回约束级别的 logger（记录到 main.log + errors.log + batch_main.log）
    """
    global _current_logger_group
    
    set_current_constraint(constraint_id)
    _current_logger_group = ConstraintLoggerGroup(constraint_id)
    
    logger = _current_logger_group.get_constraint_logger()
    logger.info(f"Constraint logger initialized: {constraint_id}")
    
    return logger


def get_sp_logger(sp_id: str, sp_type: str) -> logging.Logger:
    """
    获取 Solver/Partition 的 logger。
    
    参数:
        sp_id: 如 "x6eq2mx5_0_0"
        sp_type: "solver" 或 "partition"
    
    返回:
        logger（自动记录到 SP 专用日志 + main.log + errors.log）
    """
    if _current_logger_group is None:
        raise ValueError("请先调用 setup_constraint_logger")
    
    return _current_logger_group.create_sp_logger(sp_id, sp_type)


def get_logger(name: str = "cube") -> logging.Logger:
    """获取 logger"""
    return logging.getLogger(name)


def flush_all_handlers():
    """刷新所有 handlers"""
    for logger_name in logging.Logger.manager.loggerDict:
        logger_obj = logging.getLogger(logger_name)
        for handler in logger_obj.handlers:
            handler.flush()

def close_logger_handlers(logger: logging.Logger):
    """
    关闭 logger 的所有 handlers
    
    参数:
        logger: Logger 实例（不是 name）
    """
    if logger is None:
        return
    
    for handler in logger.handlers[:]:
        try:
            handler.flush()
            handler.close()
            logger.removeHandler(handler)
        except Exception:
            pass

def setup_batch_logger() -> logging.Logger:
    """
    为 batch_solve 设置专用 logger
    
    返回:
        logging.Logger: 配置好的 batch logger
    """
    from datetime import datetime
    from pathlib import Path
    
    # 生成 batch 日志目录
    timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
    batch_log_dir = Path("logs") / timestamp
    batch_log_dir.mkdir(parents=True, exist_ok=True)
    
    # 创建 batch logger
    logger = logging.getLogger("cube.batch")
    logger.setLevel(logging.DEBUG)
    logger.handlers.clear()
    
    # 控制台 handler
    console_handler = logging.StreamHandler()
    console_handler.setLevel(logging.INFO)
    console_formatter = logging.Formatter('%(levelname)-8s | %(message)s')
    console_handler.setFormatter(console_formatter)
    logger.addHandler(console_handler)
    
    # 文件 handler
    file_handler = logging.FileHandler(
        batch_log_dir / "batch_main.log",
        mode='a',
        encoding='utf-8'
    )
    file_handler.setLevel(logging.DEBUG)
    file_formatter = logging.Formatter(
        '%(asctime)s | %(levelname)-8s | %(message)s',
        datefmt='%H:%M:%S'
    )
    file_handler.setFormatter(file_formatter)
    logger.addHandler(file_handler)
    
    logger.propagate = False
    
    return logger        