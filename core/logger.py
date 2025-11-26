"""
日志配置模块：为整个项目提供统一的日志管理
"""
import logging
import sys
import atexit
from pathlib import Path
from datetime import datetime
from typing import Optional
from functools import wraps


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
    log_dir: str = "logs",
    console_level: int = logging.INFO,
    file_level: int = logging.DEBUG
) -> logging.Logger:
    """设置并返回配置好的 logger"""
    logger = logging.getLogger(name)
    logger.setLevel(level)
    
    if logger.handlers:
        return logger
    
    # 控制台 handler
    console_handler = logging.StreamHandler(sys.stdout)
    console_handler.setLevel(console_level)
    console_format = ColoredFormatter(
        fmt='%(levelname)-8s|%(name)-12s|%(message)s',
        datefmt='%H:%M:%S'
    )
    console_handler.setFormatter(console_format)
    logger.addHandler(console_handler)
    
    # 文件 handler
    if log_to_file:
        if not Path(log_dir).is_absolute():
            project_root = Path(__file__).parent.parent
            log_path = project_root / log_dir
        else:
            log_path = Path(log_dir)
        
        log_path.mkdir(exist_ok=True, parents=True)
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
        log_file = log_path / f"{name}_{timestamp}.log"
        
        file_handler = logging.FileHandler(log_file, encoding='utf-8')
        file_handler.setLevel(file_level)
        
        # ✅ 使用新的 AlignedFormatter 替代原来的 Formatter
        file_format = AlignedFormatter()
        file_handler.setFormatter(file_format)
        logger.addHandler(file_handler)
        
        logger.info(f"日志文件: {log_file.absolute()}")
    
    atexit.register(flush_all_handlers)
    
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