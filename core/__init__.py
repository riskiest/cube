"""
核心模块

主要功能：
- batch_prove: 批量证明约束集
- prove: 证明单个约束
- constraints_to_prove: 提供需要证明的约束集

建议使用batch_prove，日志更加丰富

使用示例：
    >>> from core import batch_prove, Constants
    >>> results = batch_prove(Constants.Constraints.constraints_to_prove, 
                                allow_breakdown_incompleteness=True)
"""
from .pipeline import batch_prove, prove
from .constants import Constants

# 便捷访问约束列表
constraints_to_prove = Constants.Constraints.constraints_to_prove

__all__ = [
    'batch_prove',           # 主接口：批量证明
    'prove',                 # 单个证明接口
    'constraints_to_prove'   # 便捷访问
]