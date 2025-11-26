"""
基础示例：演示 SMTSolver 和 Optimizer 的基本工作流程
"""
import sys
sys.path.insert(0, '..')  # 添加父目录到路径

from core import SMTSolver, Partition
from optimization import Optimizer
from pprint import pprint


def example_simple_workflow():
    """示例：简单的工作流程"""
    print("=" * 60)
    print("基础示例：分解和优化")
    print("=" * 60)
    
    # 创建 solver
    solver = SMTSolver(text_constraints=["x6 == 2*x5", "x5 == x4 + x3"])
    
    # 检查可满足性
    if solver.check() != "sat":
        print("Solver is unsat.")
        return
    
    # 分解
    groups, i_min = solver.decompose()
    print(f"\n生成 {len(groups)} 个 partitions, i_min={i_min}")
    
    partitions = [Partition(i_min, solver=solver, **g) for g in groups]
    
    # 优化器
    opt = Optimizer()
    
    # 处理第一个 partition
    p = partitions[0]
    p.calc_n_LHS(n=1)
    
    print(f"\nPartition 信息:")
    pprint(p.to_dict())
    
    # 分析和优化
    analysis_results = opt.analyze_partition(p)
    optimize_results = opt.optimize_selection(analysis_results)
    
    print(f"\n优化结果:")
    pprint(optimize_results)


if __name__ == "__main__":
    example_simple_workflow()