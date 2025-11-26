# import sys
# sys.path.insert(0, '..')  # 添加父目录到路径，这样可以找到 core 模块

from core import SMTSolver, Partition, Optimizer, F  # ✅ 从 core 包导入
from pprint import pprint
from z3 import sat
from typing import List, Tuple


def example():
    solver = SMTSolver(text_constraints=["x6 == 2*x5", "x5 == x4 + x3"])
    ck = solver.check()
    if ck != sat:
        print("Solver is unsat.")
        return
    assertions = solver.assertions()
    print("Assertions:", assertions)
    opt = Optimizer()

    # solver 生成 partitions
    groups, i_min = solver.decompose()
    partitions = [Partition(i_min, **g) for g in groups]

    
    # 用partitions生成solver
    p = partitions[1]
    # for p in partitions:
    if p.i_min == 1:
        return
    # pprint(p.to_dict())

    # p = partitions[1]
    n = 1
    p.calc_n_LHS(n)
    # pprint(p.to_dict())
    
    analysis_results = opt.get_partition_f(p)
    optimize_results = opt.optimize(analysis_results)
    status = optimize_results['status']
    if status == 'pruned':
        # 剪枝成功，直接返回
        return
    if status == 'success':
        # 求值成功，返回结果
        print(p.solver.assertions())
        return
    if status == 'optimization_failed':
        # 不使用优化，直接输出分析结果
        return
    if status == 'extend':
        # 用 n=2 处理
        return
    if status != 'split':
        # 其他未知状态，直接返回
        return
    constraints = p.gen_constraints(optimize_results['member_indices_for_zero'], n)
    filtered_solvers = p.filter(constraints)
    print(len(filtered_solvers), "unique solvers after filtering and deduplication.")
    # for c in constraints:
    #     print(c)
    # pprint(optimize_results)
    # n = 1

    # opt_results = opt.optimize_partition(p, n)
if __name__ == "__main__":
    example()