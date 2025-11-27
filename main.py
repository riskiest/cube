from fractions import Fraction
import logging
import sys
import traceback
from core import SMTSolver, Partition, Optimizer, setup_logger, get_logger
from core.logger import flush_all_handlers, setup_constraint_logger
from core.smt import Z3UnknownError
from pprint import pformat, pprint
from typing import Dict, Tuple, List
from z3 import sat
from core import F

# 设置日志
# setup_logger(
#     name="cube",
#     level=logging.DEBUG,
#     log_to_file=True,
#     # log_dir="logs",
#     console_level=logging.INFO,
#     # file_level=logging.DEBUG
# )



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
    setup_logger(
        name="cube",
        level=logging.DEBUG,
        log_to_file=True,
        console_level=logging.INFO
    )    
    logger = get_logger()
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
    setup_logger(
        name="cube",
        level=logging.DEBUG,
        log_to_file=True,
        console_level=logging.INFO
    )    
    logger = get_logger()
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
    solver_id: str = None
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
        - Solver ID: "0", "0.0.1", "0.1.2.0" (数字+点号，无下划线结尾)
        - Partition ID: "0.0", "0.1.2" (数字+点号，无下划线结尾)
        
    示例:
        solver: 0
        ├── partition: 0.0
        │   ├── solver: 0.0.0
        │   │   ├── partition: 0.0.0.0
        │   │   └── partition: 0.0.0.1
        │   └── solver: 0.0.1
        └── partition: 0.1
            └── solver: 0.1.0
    """
    # 设置 solver ID
    solver.set_id(solver_id)

    slogger = solver.get_logger()
    slogger.info("=" * 40)
    slogger.critical(f"[Depth {depth}] Processing solver (ID: {solver_id})")
    slogger.info("=" * 40)
    
    # 检查递归深度
    if depth >= max_depth:
        slogger.critical(f"Reached max depth {max_depth}")
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
        partition_id = f"{solver_id}.{p_idx}"
        p.set_id(partition_id)
        plogger = p.get_logger()
        
        plogger.critical("-" * 40)
        plogger.critical(f"Partition [{p_idx+1}/{len(partitions)}] (ID: {partition_id}, i_min={p.i_min})")
        plogger.info("-" * 40)
        p.log_assertions()
        p.log_members()

        # 终止条件 1：i_min == 1（成功！）
        if p.i_min == 1:
            
            optimize_results = opt.get_f_1(p)
            status = optimize_results['status']

            # 根据状态处理
            if status == 'pruned':
                plogger.info("✂️ Pruned")
                continue  # 该 partition 被剪枝，处理下一个
            
            elif status == 'success':
                logger.info("✅ Success: i_min == 1 and optimization successful")
                success_solvers.append(p.solver)
                continue  # 该 partition 成功，处理下一个
        
        # 尝试不同的 n 值
        nmax = 2
        for n in range(1, nmax):
            plogger.info("." * 30)
            plogger.info(f"[n={n}] Starting analysis")
            plogger.info("." * 30)
            
            # 计算 n_LHS
            p.calc_n_LHS(n)
            opt.process_partition(p, n)
            p.log_LHS(n)
            
            # 优化（先尝试 pulp）
            plogger.info("Optimizing with method=pulp")
            optimize_results = opt.optimize(p, n, method='pulp')
            status = optimize_results['status']
            
            # 如果 pulp 失败，尝试 enum
            if status == 'optimization_failed':
                plogger.warning("pulp failed, retrying with method=enum")
                optimize_results = opt.optimize(p, n, method='enum')
                status = optimize_results['status']
                
                if status == 'optimization_failed':
                    plogger.error("Both pulp and enum failed")
                    continue
            
            plogger.info(f"Status: {status}")
            
            # 根据状态处理
            if status == 'pruned':
                plogger.critical("✂️ Pruned")
                break  # 该 partition 被剪枝，处理下一个
            
            elif status == 'success':
                plogger.critical("✅ Success: optimization successful")
                success_solvers.append(p.solver)
                break  # 该 partition 成功，处理下一个
            
            elif status == 'extend':
                plogger.critical("🔄 Need to extend to larger n")
                if nmax == 2:
                    raise ValueError("nmax is 2, cannot extend further")
                else:
                    if n == 1:
                        plogger.critical("Will try n=2 next")
                        continue
                    else:
                        plogger.critical(f"Already at n={n}, cannot extend further")
                        break  # 无法继续，处理下一个 partition
            
            elif status == 'split':
                plogger.critical("🌳 Split: generating new solvers")
                
                # 生成约束和新 solvers
                constraints = p.gen_constraints(optimize_results['member_indices_for_zero'], n)
                filtered_solvers = p.filter(constraints)
                plogger.critical(f"Generated {len(filtered_solvers)} new solvers")
                
                # 递归处理每个新 solver，收集所有成功的结果
                for s_idx, new_solver in enumerate(filtered_solvers):
                    # 新 solver ID 格式：partition_id + . + s_idx
                    # 例如：0.0_.0, 0.0_.1, 0.1_.2.0_.1
                    new_solver_id = f"{partition_id}.{s_idx}"
                    
                    plogger.info("-" * 20)
                    plogger.info(f"Recursively processing solver [{s_idx+1}/{len(filtered_solvers)}] (ID: {new_solver_id})")
                    
                    sub_success_solvers = process_solver(
                        new_solver, opt, depth + 1, max_depth, solver_id=new_solver_id
                    )
                    
                    # 收集子分支的所有成功 solver
                    success_solvers.extend(sub_success_solvers)
                    plogger.info(f"Sub-solver [{s_idx+1}] returned {len(sub_success_solvers)} success(es)")
                
                break  # 该 partition 已经分裂并递归处理，处理下一个
            
            else:
                plogger.error(f"Unknown status: {status}")
                continue
        
        else:
            # for-else: 所有 n 都尝试完毕但没有 break
            plogger.error(f"Partition [{p_idx+1}] exhausted all n values")
    
    # 所有 partitions 处理完毕
    slogger.critical(f"Collected {len(success_solvers)} success solver(s) at depth {depth}")
    return success_solvers

def solve(
    text_constraints: List[str],
    n_max: int = 36,
    max_depth: int = 10
) -> Dict:
    """
    处理单个约束组。
    
    参数:
        text_constraints: 约束字符串列表，如 ["x6 == 2*x5", "x5 == x4 + x3"]
        n_max: F 函数的 n 上限
        max_depth: 最大递归深度
    
    返回:
        Dict: {
            "status": "success" | "failed" | "error",
            "solver_id": str,
            "success_solvers": List[SMTSolver],
            "error_message": str (if error)
        }
    """
    result = {
        "status": "unknown",
        "solver_id": None,
        "success_solvers": [],
        "error_message": None
    }
    
    try:
        # 生成约束 ID
        constraint_id = SMTSolver.constraints_to_id(text_constraints)
        
        # ✅ 设置该约束的专用日志
        logger = setup_constraint_logger(constraint_id)


        logger.info("=" * 80)
        logger.info(f"Starting solve_constraints")
        logger.info(f"Constraints: {text_constraints}")
        logger.info(f"n_max: {n_max}, max_depth: {max_depth}")
        logger.info("=" * 80)
        
        # 1. 初始化 solver（自动生成 ID）
        initial_solver = SMTSolver(text_constraints=text_constraints)
        solver_id = f"{constraint_id}_0"
        result["solver_id"] = solver_id
        
        logger.info(f"Solver ID: {solver_id}")
        
        # 2. 检查初始 solver 是否可满足
        if initial_solver.check() != sat:
            logger.error("Initial solver is unsat")
            result["status"] = "failed"
            result["error_message"] = "Initial solver is unsat"
            return result
        
        logger.info("Initial solver is satisfiable")
        
        # 3. 初始化 optimizer
        opt = Optimizer(n_max=n_max)
        logger.info(f"Optimizer initialized with n_max={n_max}")
        
        # 4. 递归处理
        logger.info("Starting recursive processing...")
        success_solvers = process_solver(
            initial_solver, opt, depth=0, max_depth=max_depth, solver_id=solver_id
        )
        
        # 5. 汇总结果
        result["status"] = "success" if success_solvers else "failed"
        result["success_solvers"] = success_solvers
        
        logger.info("=" * 80)
        logger.info(f"solve_constraints completed")
        logger.info(f"Status: {result['status']}")
        logger.info(f"Total success solvers: {len(success_solvers)}")
        logger.info("=" * 80)
        
        # 6. 输出成功的 solver
        if success_solvers:
            logger.info(f"\n🎉 Found {len(success_solvers)} valid solution(s):")
            for idx, solver in enumerate(success_solvers, 1):
                model = solver.get_model()
                logger.info(f"  Solution {idx} (ID: {solver.get_id()}):")
                for var_name in ['x1', 'x2', 'x3', 'x4', 'x5', 'x6']:
                    value = model.get(var_name)
                    logger.info(f"    {var_name} = {value}")
        else:
            logger.warning("⚠️ No valid solutions found")
        
        return result
    
    except KeyboardInterrupt:
        logger.warning("❌ Interrupted by user")
        result["status"] = "error"
        result["error_message"] = "Interrupted by user"
        return result
    
    except Exception as e:
        logger.error(f"❌ Error in solve_constraints: {e}")
        logger.error(traceback.format_exc())
        result["status"] = "error"
        result["error_message"] = str(e)
        return result
    
    finally:
        # logger.info(f"solve_constraints finished for {text_constraints}")
        # logger.info("-" * 80)
        flush_all_handlers()


def batch_solve(
    text_constraints_list: List[List[str]],
    n_max: int = 36,
    max_depth: int = 10,
    stop_on_error: bool = False
) -> List[Dict]:
    """
    批量处理多个约束组。
    
    参数:
        text_constraints_list: 约束组列表，每个元素是一个约束字符串列表
            例如: [
                ["x6 == 2*x5", "x5 == x4 + x3"],
                ["x6 > x5", "x5 == x4 + x3"],
                ["x6 == x5 + x4"]
            ]
        n_max: F 函数的 n 上限
        max_depth: 最大递归深度
        stop_on_error: 是否在遇到错误时停止（默认 False，继续处理）
    
    返回:
        List[Dict]: 每个约束组的处理结果
    """
    # ✅ 获取 batch logger（只记录到 batch_main.log + 控制台）
    logger = get_logger("cube")

    logger.info("=" * 80)
    logger.info(f"🚀 Starting batch_solve_constraints")
    logger.info(f"Total constraint groups: {len(text_constraints_list)}")
    logger.info(f"Parameters: n_max={n_max}, max_depth={max_depth}, stop_on_error={stop_on_error}")
    logger.info("=" * 80)
    
    results = []
    
    for idx, text_constraints in enumerate(text_constraints_list, 1):
        logger.info("\n" + "=" * 80)
        logger.info(f"📋 Processing constraint group {idx}/{len(text_constraints_list)}")
        logger.info("=" * 80)
        
        try:
            result = solve(text_constraints, n_max, max_depth)
            results.append(result)
            
            # 记录当前结果
            if result["status"] == "success":
                logger.info(f"✅ Group {idx} SUCCESS: {len(result['success_solvers'])} solution(s)")
            elif result["status"] == "failed":
                logger.warning(f"⚠️ Group {idx} FAILED: {result.get('error_message', 'No solutions')}")
            else:
                logger.error(f"❌ Group {idx} ERROR: {result.get('error_message', 'Unknown error')}")
            
            # 如果设置了 stop_on_error 且当前出错，则停止
            if stop_on_error and result["status"] == "error":
                logger.error(f"❌ Stopping batch processing due to error in group {idx}")
                break
        
        except Exception as e:
            logger.error(f"❌ Unexpected error in group {idx}: {e}")
            logger.error(traceback.format_exc())
            
            results.append({
                "status": "error",
                "solver_id": None,
                "success_solvers": [],
                "error_message": f"Unexpected error: {str(e)}"
            })
            
            if stop_on_error:
                logger.error(f"❌ Stopping batch processing due to unexpected error")
                break
    
    # 汇总统计
    logger.info("\n" + "=" * 80)
    logger.info("📊 Batch Processing Summary")
    logger.info("=" * 80)
    
    success_count = sum(1 for r in results if r["status"] == "success")
    failed_count = sum(1 for r in results if r["status"] == "failed")
    error_count = sum(1 for r in results if r["status"] == "error")
    total_solutions = sum(len(r["success_solvers"]) for r in results)
    
    logger.info(f"Total groups processed: {len(results)}/{len(text_constraints_list)}")
    logger.info(f"✅ Success: {success_count}")
    logger.info(f"⚠️ Failed (no solutions): {failed_count}")
    logger.info(f"❌ Error: {error_count}")
    logger.info(f"🎯 Total solutions found: {total_solutions}")
    logger.info("=" * 80)
    
    # 详细结果表格
    logger.info("\nDetailed Results:")
    logger.info("-" * 80)
    logger.info(f"{'No.':<5} {'Solver ID':<30} {'Status':<10} {'Solutions':<10}")
    logger.info("-" * 80)
    
    for idx, result in enumerate(results, 1):
        solver_id = result.get("solver_id", "N/A")[:28]
        status = result["status"]
        solutions = len(result["success_solvers"])
        logger.info(f"{idx:<5} {solver_id:<30} {status:<10} {solutions:<10}")
    
    logger.info("=" * 80)
    
    return results

def main():
    """主函数：演示单个约束组的处理"""
    setup_logger(
        name="cube",
        level=10,  # DEBUG
        log_to_file=True,
        console_level=20  # INFO
    )
    
    # 单个约束组示例
    # text_constraints = ["x6 == 2 * x5", "x5 == x4 + x3"]
    text_constraints = ["x6 == 2 * x5", "x5 == x4 + x2"]
    
    result = solve(
        text_constraints=text_constraints,
        n_max=36,
        max_depth=10
    )
    
    flush_all_handlers()


def batch_main():
    """批量处理示例"""
    setup_logger(
        name="cube",
        level=logging.DEBUG,
        log_to_file=True,
        console_level=logging.INFO,
        # file_level=logging.DEBUG
    )
    # print(f"Logger created: {logger}")
    # print(f"Logger handlers: {logger.handlers}")

    # return
    # 多个约束组
    # text_constraints = ["x6 == 2 * x5", "x5 == x4 + x3"]
    # text_constraints = ["x6 == 2 * x5", "x5 == x4 + x2"]

    text_constraints_list = [
        ["x6 == 2 * x5", "x5 == x4 + x2"],
        ["x6 == 2 * x5", "x5 == x4 + x3"],
        # ["x6 == x5 + x4"],
        # ["x6 == x5 + x3", "x5 == x3 + x2"],
        # ["x6 >= x5", "x5 >= x4"],
    ]
    
    results = batch_solve(
        text_constraints_list=text_constraints_list,
        n_max=36,
        max_depth=10,
        stop_on_error=False  # 遇到错误继续处理
    )
    
    flush_all_handlers()

def old_main():
    """主函数：初始化 solver 并启动递归处理"""
    setup_logger(
        name="cube",
        level=logging.DEBUG,
        log_to_file=True,
        console_level=logging.INFO
    )    
    logger = get_logger()    
    try:
        logger.info("=" * 60)
        logger.info("Cube Decomposition Solver")
        logger.info("=" * 60)
        
        # 1. 初始化 solver（根节点 ID 为 "0"）
        text_constraints=["x6 == 2*x5", "x5 == x4 + x3"]
        initial_solver = SMTSolver(text_constraints=text_constraints)
        solver_id = f"{SMTSolver.constraints_to_id(text_constraints)}_0"
        if initial_solver.check() != sat:
            logger.error("Initial solver is unsat.")
            return
        logger.debug(f"Initial solver created with ID: {solver_id}")
        
        # 2. 初始化 optimizer
        opt = Optimizer(n_max=36)
        logger.debug("Optimizer initialized")
        
        # 3. 递归处理（根节点 ID 为 "0"）
        logger.info("\n" + "Starting recursive processing...")
        success_solvers = process_solver(
            initial_solver, opt, depth=0, max_depth=10, solver_id=solver_id
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
    # main()
    batch_main()
    # new_example()
    # f_example()
    # example()