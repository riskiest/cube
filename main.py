from fractions import Fraction
import logging
import sys
from core import SMTSolver, Partition, Optimizer, setup_logger, get_logger
from core.logger import flush_all_handlers
from core.smt import Z3UnknownError
from pprint import pformat, pprint
from typing import Tuple, List
from z3 import sat
from core import F

# 设置日志
setup_logger(
    name="cube",
    level=logging.DEBUG,
    log_to_file=True,
    log_dir="logs",
    console_level=logging.INFO,
    file_level=logging.DEBUG
)

logger = get_logger()

def f_example():
    f = F(n_max=15)
    fs = [None] * 4
    fs[0] = f.get((1,2), 2)[1]
    fs[1] = f.get((1,1), 2)[2]
    fs[2] = f.get((1,), 2)[3]
    fs[3] = f._sigma((1, 3))
    # fs[3] = f.evaluator.compute_expression("0.0004_6")  
    for j, frac in enumerate(fs):
        print(f"F{j}: {frac}  ({f.formatter.fraction_to_base(frac)})")  
    f_sum = sum(fs, start=Fraction(0))
    print(f"Sum: {f_sum}  ({f.formatter.fraction_to_base(f_sum)})")

    # K_example = tuple((1,1))
    # i_example = 2
    # fracs = f.get(K_example, i_example)
    # for n in f.n_range:
    #     print(f"n={n}: {fracs[n]}  ({f.formatter.fraction_to_base(fracs[n])})")
    # K_example = tuple()
    # i_example = 3
    # fracs = f.get(K_example, i_example)
    # print("----")
    # for n in f.n_range:
    #     print(f"n={n}: {fracs[n]}  ({f.formatter.fraction_to_base(fracs[n])})")
    # K_example = tuple((2,))
    # i_example = 3
    # fracs = f.get(K_example, i_example)
    # print("----")
    # for n in f.n_range:
    #     print(f"n={n}: {fracs[n]}  ({f.formatter.fraction_to_base(fracs[n])})")
def new_example():
    """示例：演示完整的处理流程"""
    try:
        logger.info("=" * 60)
        logger.info("示例：Solver → Partitions → 优化 → 新 Solvers")
        logger.info("=" * 60)
        
        # 创建初始 solver
        solver = SMTSolver(text_constraints=["x6 == 2*x5", "x5 == 2*x4"])
        solver.log_assertions()
            
        # 检查可满足性
        ck = solver.check()
        if ck != sat:
            logger.error("Solver is unsat.")
            return
        
        opt = Optimizer()

        # solver 生成 partitions
        groups, i_min = solver.decompose()
        partitions = [Partition(i_min, **g) for g in groups]
        logger.info(f"Generated {len(partitions)} partitions from solver")

        # 用partitions生成solver
        p = partitions[0]
        p.set_id('2_')
        p.log_assertions()
        p.log_members()
        

        if p.i_min == 1:
            return
        
        n = 1
        p.calc_n_LHS(n)
        opt.process_partition(p, n)
        p.log_LHS(n)
        # p.log_structure()
        # return
        
        # 优化（先尝试 pulp，失败则尝试 enum）
        optimize_results = opt.optimize(p, n, method='pulp')
        status = optimize_results['status']
        
        if status == 'optimization_failed':
            logger.warning("pulp 优化失败，尝试 enum 方法")
            return
            # optimize_results = opt.optimize(p, n, method='enum')
            # status = optimize_results['status']

        if status == 'pruned':
            return
        if status == 'success':
            logger.info("Optimization successful, final solver assertions:")
            p.solver.log_assertions()
            return
        if status == 'optimization_failed':
            return
        if status == 'extend':
            logger.info("需要扩展，尝试 n=2")
            p.calc_n_LHS(2)
            optimize_results = opt.optimize(p, 2, method='pulp')
            return
        if status != 'split':
            return
        
        constraints = p.gen_constraints(optimize_results['member_indices_for_zero'], n)
        filtered_solvers = p.filter(constraints)
        logger.info(f"Generated {len(filtered_solvers)} unique solvers")
    
    except KeyboardInterrupt:
        logger.warning("用户中断 (Ctrl+C)")
        flush_all_handlers()
        sys.exit(130)
    except Z3UnknownError as e:
        logger.error(f"Z3 求解器超时: {e.reason}")
        logger.debug(f"约束数量: {e.num_constraints}")
        flush_all_handlers()
    except Exception:
        logger.exception("示例函数发生异常")
        flush_all_handlers()
    finally:
        flush_all_handlers()

def example():
    """示例：演示完整的处理流程"""
    try:
        logger.info("=" * 60)
        logger.info("示例：Solver → Partitions → 优化 → 新 Solvers")
        logger.info("=" * 60)
        
        # 创建初始 solver
        solver = SMTSolver(text_constraints=["x6 == 2*x5", "x5 == x4 + x3"])
        solver.log_assertions()
            
        # 检查可满足性
        ck = solver.check()
        if ck != sat:
            logger.error("Solver is unsat.")
            return
        
        opt = Optimizer()

        # solver 生成 partitions
        groups, i_min = solver.decompose()
        partitions = [Partition(i_min, **g) for g in groups]

        # 用partitions生成solver
        p = partitions[1]
        p.log_members()

        if p.i_min == 1:
            return
        
        n = 1
        p.calc_n_LHS(n)
        p.log_LHS(n)
        
        # 优化（先尝试 pulp，失败则尝试 enum）
        optimize_results = opt.optimize(p, n, method='pulp')
        status = optimize_results['status']
        
        if status == 'optimization_failed':
            logger.warning("pulp 优化失败，尝试 enum 方法")
            optimize_results = opt.optimize(p, n, method='enum')
            status = optimize_results['status']

        if status == 'pruned':
            return
        if status == 'success':
            logger.info("Optimization successful, final solver assertions:")
            p.solver.log_assertions()
            return
        if status == 'optimization_failed':
            return
        if status == 'extend':
            logger.info("需要扩展，尝试 n=2")
            p.calc_n_LHS(2)
            optimize_results = opt.optimize(p, 2, method='pulp')
            return
        if status != 'split':
            return
        
        constraints = p.gen_constraints(optimize_results['member_indices_for_zero'], n)
        filtered_solvers = p.filter(constraints)
        logger.info(f"Generated {len(filtered_solvers)} unique solvers")
    
    except KeyboardInterrupt:
        logger.warning("用户中断 (Ctrl+C)")
        flush_all_handlers()
        sys.exit(130)
    except Z3UnknownError as e:
        logger.error(f"Z3 求解器超时: {e.reason}")
        logger.debug(f"约束数量: {e.num_constraints}")
        flush_all_handlers()
    except Exception:
        logger.exception("示例函数发生异常")
        flush_all_handlers()
    finally:
        flush_all_handlers()


def process_solver(
    solver: SMTSolver,
    opt: Optimizer,
    depth: int = 0,
    max_depth: int = 10,
    solver_id: str = "0"
) -> List[SMTSolver]:
    """
    递归处理单个 solver，收集所有成功的 solver。
    
    终止条件（自然停止）：
    1. i_min == 1 → 返回该 solver（✅ success）
    2. status != 'split' → 该分支停止，不产生新 solver
    3. 达到最大递归深度 → 强制停止
    
    参数:
        solver: 当前的 SMTSolver
        opt: Optimizer 实例
        depth: 当前递归深度
        max_depth: 最大递归深度
        solver_id: 当前 solver 的 ID（树状结构）
    
    返回:
        List[SMTSolver]: 所有成功的 solver 列表
    
    ID 格式说明:
        - Solver ID: "0", "0.0_.1", "0.1_.2.0_" (数字+点号，无下划线结尾)
        - Partition ID: "0.0_", "0.1_.2_" (数字+点号+下划线结尾)
        
    示例:
        solver: 0
        ├── partition: 0.0_
        │   ├── solver: 0.0_.0
        │   │   ├── partition: 0.0_.0.0_
        │   │   └── partition: 0.0_.0.1_
        │   └── solver: 0.0_.1
        └── partition: 0.1_
            └── solver: 0.1_.0
    """
    # 设置 solver ID
    solver.set_id(solver_id)
    
    logger.info("=" * 40)
    logger.info(f"[Depth {depth}] Processing solver (ID: {solver_id})")
    logger.info("=" * 40)
    
    # 检查递归深度
    if depth >= max_depth:
        logger.warning(f"Reached max depth {max_depth}")
        return []
    solver.log_assertions()
    
    # 分解生成 partitions
    groups, i_min = solver.decompose()
    partitions = [Partition(i_min, **g) for g in groups]
    
    # 收集所有成功的 solver
    success_solvers: List[SMTSolver] = []
    
    # 遍历每个 partition
    for p_idx, p in enumerate(partitions):
        # 设置 partition ID：solver_id + . + p_idx + _
        # 例如：0.0_, 0.1_, 0.0_.1.0_, 0.1_.2.1_
        partition_id = f"{solver_id}.{p_idx}_"
        p.set_id(partition_id)
        
        logger.info("-" * 40)
        logger.info(f"Partition [{p_idx+1}/{len(partitions)}] (ID: {partition_id}, i_min={p.i_min})")
        logger.info("-" * 40)
        p.log_assertions()
        p.log_members()

        # 终止条件 1：i_min == 1（成功！）
        if p.i_min == 1:
            
            optimize_results = opt.get_f_1(p)
            status = optimize_results['status']

            # 根据状态处理
            if status == 'pruned':
                logger.info("✂️ Pruned")
                continue  # 该 partition 被剪枝，处理下一个
            
            elif status == 'success':
                logger.info("✅ Success: i_min == 1 and optimization successful")
                success_solvers.append(p.solver)
                continue  # 该 partition 成功，处理下一个
        
        # 尝试不同的 n 值
        nmax = 2
        for n in range(1, nmax):
            logger.info("." * 30)
            logger.info(f"[n={n}] Starting analysis")
            logger.info("." * 30)
            
            # 计算 n_LHS
            p.calc_n_LHS(n)
            opt.process_partition(p, n)
            p.log_LHS(n)
            
            # 优化（先尝试 pulp）
            logger.info("Optimizing with method=pulp")
            optimize_results = opt.optimize(p, n, method='pulp')
            status = optimize_results['status']
            
            # 如果 pulp 失败，尝试 enum
            if status == 'optimization_failed':
                logger.warning("pulp failed, retrying with method=enum")
                optimize_results = opt.optimize(p, n, method='enum')
                status = optimize_results['status']
                
                if status == 'optimization_failed':
                    logger.error("Both pulp and enum failed")
                    continue
            
            logger.info(f"Status: {status}")
            
            # 根据状态处理
            if status == 'pruned':
                logger.info("✂️ Pruned")
                break  # 该 partition 被剪枝，处理下一个
            
            elif status == 'success':
                logger.info("✅ Success: optimization successful")
                success_solvers.append(p.solver)
                break  # 该 partition 成功，处理下一个
            
            elif status == 'extend':
                logger.info("🔄 Need to extend to larger n")
                if nmax == 2:
                    raise ValueError("nmax is 2, cannot extend further")
                else:
                    if n == 1:
                        logger.critical("Will try n=2 next")
                        continue
                    else:
                        logger.critical(f"Already at n={n}, cannot extend further")
                        break  # 无法继续，处理下一个 partition
            
            elif status == 'split':
                logger.info("🌳 Split: generating new solvers")
                
                # 生成约束和新 solvers
                constraints = p.gen_constraints(optimize_results['member_indices_for_zero'], n)
                filtered_solvers = p.filter(constraints)
                logger.info(f"Generated {len(filtered_solvers)} new solvers")
                
                # 递归处理每个新 solver，收集所有成功的结果
                for s_idx, new_solver in enumerate(filtered_solvers):
                    # 新 solver ID 格式：partition_id + . + s_idx
                    # 例如：0.0_.0, 0.0_.1, 0.1_.2.0_.1
                    new_solver_id = f"{partition_id}.{s_idx}"
                    
                    logger.info("-" * 20)
                    logger.info(f"Recursively processing solver [{s_idx+1}/{len(filtered_solvers)}] (ID: {new_solver_id})")
                    
                    sub_success_solvers = process_solver(
                        new_solver, opt, depth + 1, max_depth, solver_id=new_solver_id
                    )
                    
                    # 收集子分支的所有成功 solver
                    success_solvers.extend(sub_success_solvers)
                    logger.info(f"Sub-solver [{s_idx+1}] returned {len(sub_success_solvers)} success(es)")
                
                break  # 该 partition 已经分裂并递归处理，处理下一个
            
            else:
                logger.warning(f"Unknown status: {status}")
                continue
        
        else:
            # for-else: 所有 n 都尝试完毕但没有 break
            logger.info(f"Partition [{p_idx+1}] exhausted all n values")
    
    # 所有 partitions 处理完毕
    logger.info(f"Collected {len(success_solvers)} success solver(s) at depth {depth}")
    return success_solvers


def main():
    """主函数：初始化 solver 并启动递归处理"""
    try:
        logger.info("=" * 60)
        logger.info("Cube Decomposition Solver")
        logger.info("=" * 60)
        
        # 1. 初始化 solver（根节点 ID 为 "0"）
        initial_solver = SMTSolver(text_constraints=["x6 == x5 + x3", "x5 == x3 + x2"])
        if initial_solver.check() != sat:
            logger.error("Initial solver is unsat.")
            return
        logger.debug("Initial solver created with ID: 0")
        
        # 2. 初始化 optimizer
        opt = Optimizer(n_max=36)
        logger.debug("Optimizer initialized")
        
        # 3. 递归处理（根节点 ID 为 "0"）
        logger.info("\n" + "Starting recursive processing...")
        success_solvers = process_solver(
            initial_solver, opt, depth=0, max_depth=10, solver_id="0"
        )
        
        # 4. 输出最终结果
        logger.info("\n" + "=" * 60)
        logger.info("Final Result")
        logger.info("=" * 60)
        logger.info(f"Total success solvers: {len(success_solvers)}")
        
        if success_solvers:
            logger.info("\n✅ Successfully found solution(s)!")
            for idx, solver in enumerate(success_solvers, 1):
                solver_id = solver.get_id() if hasattr(solver, 'get_id') else f"solver_{idx}"
                logger.info(f"\n--- Solution {idx} (ID: {solver_id}) ---")
                logger.info("Constraints:")
                for a in solver.assertions():
                    logger.info(f"  - {a}")
        else:
            logger.warning("\nNo success solvers found")
    
    except KeyboardInterrupt:
        logger.warning("\nUser interrupted (Ctrl+C)")
        flush_all_handlers()
        sys.exit(130)
    
    except Z3UnknownError as e:
        logger.critical("=" * 60)
        logger.critical("Z3 solver returned unknown")
        logger.critical("=" * 60)
        logger.exception("Full traceback:")
        flush_all_handlers()
        sys.exit(1)
    
    except Exception as e:
        logger.critical("=" * 60)
        logger.critical("Unexpected error occurred")
        logger.critical("=" * 60)
        logger.critical(f"Exception type: {type(e).__name__}")
        logger.critical(f"Exception message: {e}")
        logger.exception("Full traceback:")
        flush_all_handlers()
        sys.exit(1)
    
    finally:
        logger.info("\n" + "=" * 60)
        logger.info("Program ended, flushing logs...")
        logger.info("=" * 60)
        flush_all_handlers()


if __name__ == "__main__":
    main()
    # new_example()
    # f_example()
    # example()