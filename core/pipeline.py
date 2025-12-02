"""
Pipeline 模块：处理从约束到求解的完整流程
"""
from typing import List, Dict, Optional
import logging
import traceback
from z3 import sat
import time  # ✅ 在文件顶部添加

from .smt import SMTSolver, Z3UnknownError
from .partition import Partition
from .optim import Optimizer
from .logger import (
    get_logger, 
    setup_constraint_logger, 
    flush_all_handlers,
    setup_logger,
    setup_batch_logger
)

__all__ = ['process_solver', 'solve', 'batch_solve', 'constraint_test']

constraints_to_prove = [
    # when x6 == 2*x5
    ["x6 == 2*x5", "x5 == x1 + x1"],
    ["x6 == 2*x5", "x5 == x1 + x2"],
    ["x6 == 2*x5", "x5 == x1 + x3"],
    ["x6 == 2*x5", "x5 == x1 + x4"],    
    ["x6 == 2*x5", "x5 == x2 + x2"],
    ["x6 == 2*x5", "x5 == x2 + x3"],
    ["x6 == 2*x5", "x5 == x2 + x4"],
    ["x6 == 2*x5", "x5 == x3 + x3"],   
    ["x6 == 2*x5", "x5 == x3 + x4"],
    ["x6 == 2*x5", "x5 == x4 + x4"],   
    # when x6 != x_{1-4} + x_{1-4}
    ["x6 == x1 + x1"],
    ["x6 == x1 + x2"],
    ["x6 == x1 + x3"],
    ["x6 == x1 + x4"],
    ["x6 == x2 + x2"],
    ["x6 == x2 + x3"],
    ["x6 == x2 + x4"],
    ["x6 == x3 + x3"],
    ["x6 == x3 + x4"],
    ["x6 == x4 + x4"],
    # when x6 == x5 + x_{1-4}
    ["x6 == x5 + x1"],
    ["x6 == x5 + x2"],
    ["x6 == x5 + x4"],
    # Specailly, when x6 == x5 + x_3
    ["x6 == x5 + x3", "x5 == x1 + x1"],
    ["x6 == x5 + x3", "x5 == x1 + x2"],
    ["x6 == x5 + x3", "x5 == x1 + x3"],
    ["x6 == x5 + x3", "x5 == x1 + x4"],    
    ["x6 == x5 + x3", "x5 == x2 + x2"],
    ["x6 == x5 + x3", "x5 == x2 + x3"],
    ["x6 == x5 + x3", "x5 == x2 + x4"],
    ["x6 == x5 + x3", "x5 == x3 + x3"],   
    ["x6 == x5 + x3", "x5 == x3 + x4"],
    ["x6 == x5 + x3", "x5 == x4 + x4"],    
]


def process_solver(
    solver: SMTSolver,
    opt: Optimizer,
    depth: int = 0,
    max_depth: int = 10,
    solver_id: str = None
    ) -> tuple[List[Partition], Dict]:
    """
    递归处理 solver：分解 → 分类 → 优化 → 生成新 solver
    
    参数:
        solver: 当前要处理的 SMTSolver
        opt: Optimizer 实例
        depth: 当前递归深度
        max_depth: 最大递归深度
        solver_id: Solver 的 ID
    
    返回:
        tuple[List[Partition], Dict]: 成功的 Partition 列表和统计信息
    
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
    # ✅ 添加：根据深度计算缩进
    indent = "  " * depth

    # 设置 solver ID
    solver.set_id(solver_id)

    slogger = solver.get_logger()
    slogger.info("=" * 40)
    if depth == 0:
        slogger.critical(f"{indent}[Depth {depth}] Processing solver (ID: {solver_id})")
    # slogger.info("=" * 40)
    
    # 检查递归深度
    if depth >= max_depth:
        slogger.critical(f"{indent}❌ Reached max depth {max_depth}")
        raise ValueError(f"Max depth {max_depth} reached at solver ID: {solver_id}")
        # return []
    solver.log_assertions()

    # ✅ 初始化统计信息
    stats = {
        'total_partitions': 0,      # recursive_classify 生成的总数
        'selected_partitions': 0,   # 本层挑出来处理的数量
        'total_solvers': 0           # filter 生成的 solver 总数
    }    
    # 分解生成 partitions

    # tree = solver.new_decompose()
    # partitions = solver.new_classify(tree)
    partitions, total_generated = solver.recursive_classify()

    partitions = [Partition(**p) for p in partitions]
    # slogger.info(f"Generated {len(partitions)} partitions from solver")

    # ✅ 记录 recursive_classify 生成的总数
    stats['total_partitions'] = total_generated
    # ✅ 记录被挑出来的 partition 数量
    stats['selected_partitions'] = len(partitions)
    slogger.critical(f"{indent}🧬 Solver produces [{len(partitions)}/{total_generated}] partitions.")
    slogger.critical(f"{indent}" + "-" * 40)

    # 收集所有成功的 solver
    success_solvers: List[Partition] = []
    
    # 遍历每个 partition
    for p_idx, p in enumerate(partitions):
        # 设置 partition ID：solver_id + . + p_idx + _
        # 例如：0.0_, 0.1_, 0.0_.1.0_, 0.1_.2.1_
        partition_id = f"{solver_id}.{p_idx}"
        p.set_id(partition_id)
        plogger = p.get_logger()
        
        # plogger.critical(f"{indent}" + "-" * 40)
        plogger.critical(f"{indent}Partition [{p_idx+1}/{len(partitions)}] (ID: {partition_id})")
        plogger.info(f"{indent}" + "-" * 40)
        p.log_assertions()
        # p.log_members()
        p.log_nodes()

        # ✅ 添加：Partition 内容的额外缩进
        p_indent = indent + "  "
        # ✅ 记录本 partition 生成的 solver 数量（初始为 0）
        partition_solver_count = 0

        # 尝试不同的 n 值
        nmax = 2
        for n in range(1, nmax):
            plogger.info("." * 30)
            plogger.info(f"[n={n}] Starting analysis")
            plogger.info("." * 30)
            
            # 计算 n_LHS
            p.calc_n_LHS(n)
            # opt.process_partition(p, n)
            opt.new_calc_node(p, n)
            p.log_LHS(n)
            
            # 优化（先尝试 pulp）
            plogger.info("Optimizing with method=pulp")
            # optimize_results = opt.optimize(p, n, method='pulp')
            optimize_results = opt.new_optimize(p, n, method='pulp')
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
                plogger.critical(f"{p_indent}✂️ Pruned")
                plogger.critical(f"{p_indent}" + "-" * 40)
                break  # 该 partition 被剪枝，处理下一个
            
            elif status == 'success':
                plogger.critical(f"{p_indent}✅ Success: optimization successful")
                plogger.critical(f"{p_indent}" + "-" * 40)
                success_solvers.append(p)
                break  # 该 partition 成功，处理下一个
            
            elif status == 'extend':
                plogger.critical(f"{p_indent}🔄 Need to extend to larger n")
                plogger.critical(f"{p_indent}" + "-" * 40)
                if nmax == 2:
                    raise ValueError("nmax is 2, cannot extend further")
                else:
                    if n == 1:
                        plogger.critical(f"{p_indent}Will try n=2 next")
                        continue
                    else:
                        plogger.critical(f"{p_indent}Already at n={n}, cannot extend further")
                        raise ValueError(f"Cannot extend beyond n={n}")
                        # break  # 无法继续，处理下一个 partition
            
            elif status == 'split':
                plogger.critical(f"{p_indent}🌳 Split: generating new solvers")
                
                # 生成约束和新 solvers
                # constraints = p.gen_constraints(optimize_results['member_indices_for_zero'], n)
                constraints = p.new_gen_constraints(optimize_results['member_indices_for_zero'], n)
                filtered_solvers = p.filter(constraints)
                plogger.critical(f"{p_indent}🌾Generated {len(filtered_solvers)} new solvers")
                plogger.critical(f"{p_indent}" + "-" * 40)

                # ✅ 记录生成的 solver 数量
                partition_solver_count = len(filtered_solvers)
                stats['total_solvers'] += partition_solver_count

                # 新增逻辑，如果生成的partition的solver与当前solver相同，则报错
                # for fs in filtered_solvers:
                #     if SMTSolver.are_equivalent(fs, solver):
                #         plogger.error("Generated solver is equivalent to current solver, aborting to prevent infinite loop")
                #         raise ValueError("Generated solver is equivalent to current solver")
                
                # 递归处理每个新 solver，收集所有成功的结果
                for s_idx, new_solver in enumerate(filtered_solvers):
                    # 新 solver ID 格式：partition_id + . + s_idx
                    # 例如：0.0_.0, 0.0_.1, 0.1_.2.0_.1
                    new_solver_id = f"{partition_id}.{s_idx}"
                    
                    plogger.info(f"{p_indent}" + "-" * 20)
                    plogger.critical(f"{p_indent}[Depth {depth + 1}] processing solver [{s_idx+1}/{len(filtered_solvers)}] (ID: {new_solver_id})")
                    
                    # ✅ 递归调用，获取子统计信息                    
                    sub_success_solvers, sub_stats = process_solver(
                        new_solver, opt, depth + 1, max_depth, solver_id=new_solver_id
                    )

                    # ✅ 累加子统计信息
                    stats['total_partitions'] += sub_stats['total_partitions']
                    stats['selected_partitions'] += sub_stats['selected_partitions']
                    stats['total_solvers'] += sub_stats['total_solvers']

                    # 收集子分支的所有成功 solver
                    success_solvers.extend(sub_success_solvers)

                    # ✅ 输出递归返回的统计信息
                    plogger.info(f"Sub-solver [{s_idx+1}] returned {len(sub_success_solvers)} success(es)")
                    plogger.info(f"  递归统计: partitions={sub_stats['total_partitions']}, "
                               f"selected={sub_stats['selected_partitions']}, "
                               f"solvers={sub_stats['total_solvers']}")
                
                break  # 该 partition 已经分裂并递归处理，处理下一个
            
            else:
                plogger.error(f"Unknown status: {status}")
                continue
        
        else:
            # for-else: 所有 n 都尝试完毕但没有 break
            plogger.error(f"{p_indent}Partition [{p_idx+1}] exhausted all n values")

        # ✅ 输出本 partition 的统计信息
        plogger.info(f"{indent}📊 Partition [{p_idx+1}] 统计: 生成 {partition_solver_count} 个 solvers")

        p.close_logger()
    
    # 所有 partitions 处理完毕
    # ✅ 输出本层汇总统计
    slogger.info("=" * 40)
    slogger.info(f"{indent}[Depth {depth}] 完成统计:")
    slogger.info(f"{indent}  本层: partitions={total_generated}, selected={len(partitions)}, solvers={stats['total_solvers'] - sum(1 for s in success_solvers if s)}")
    slogger.info(f"{indent}  累计: partitions={stats['total_partitions']}, selected={stats['selected_partitions']}, solvers={stats['total_solvers']}")
    slogger.info(f"{indent}  成功的 solver 数: {len(success_solvers)}")
    slogger.info("=" * 40)

    return success_solvers, stats


def solve(
    text_constraints: List[str],
    n_max: int = 36,
    max_depth: int = 10
) -> Dict:
    """处理单个约束组"""
    # ✅ 记录开始时间
    start_time = time.time()
    
    result = {
        "status": "unknown",
        "solver_id": None,
        "success_solvers": [],
        "verified_solvers": [],
        "error_message": None,
        "statistics": {},
        "elapsed_time": 0.0  # ✅ 添加运行时间字段
    }
    
    try:
        # 生成约束 ID
        constraint_id = SMTSolver.constraints_to_id(text_constraints)
        
        # 设置该约束的专用日志
        logger = setup_constraint_logger(constraint_id)

        logger.info("=" * 80)
        logger.info(f"Starting solve_constraints")
        logger.info(f"Constraints: {text_constraints}")
        logger.info(f"n_max: {n_max}, max_depth: {max_depth}")
        logger.info("=" * 80)
        
        # 1. 初始化 solver
        initial_solver = SMTSolver(text_constraints=text_constraints)
        solver_id = f"{constraint_id}_0"
        result["solver_id"] = solver_id
        
        logger.info(f"Solver ID: {solver_id}")
        
        # 2. 检查初始 solver 是否可满足
        if initial_solver.check() != sat:
            logger.error("Initial solver is unsat")
            result["status"] = "failed"
            result["error_message"] = "Initial solver is unsat"
            # ✅ 计算运行时间
            result["elapsed_time"] = time.time() - start_time
            return result
        
        logger.info("Initial solver is satisfiable")
        
        # 3. 初始化 optimizer
        opt = Optimizer(n_max=n_max)
        logger.info(f"Optimizer initialized with n_max={n_max}")
        
        # 4. 递归处理，获取统计信息
        logger.info("Starting recursive processing...")
        success_solvers, stats = process_solver(
            initial_solver, opt, depth=0, max_depth=max_depth, solver_id=solver_id
        )
        
        # 5. 验证每个成功的 solver
        verified_solvers = []
        if success_solvers:
            # logger.critical("=" * 80)
            logger.critical("🔍 验证成功的 solvers...")
            logger.critical("-" * 80)
            
            for idx, partition in enumerate(success_solvers, 1):
                logger.critical(f"验证 Solver {getattr(partition, 'id', 'unnamed')} [{idx}/{len(success_solvers)}]...")
                passed = constraint_test(partition.solver)
                
                if passed:
                    verified_solvers.append(partition)
                    logger.critical(f"  ✅ Solver [{idx}] 通过验证")
                else:
                    logger.critical(f"  ❌ Solver [{idx}] 未通过验证")
        
        # ✅ 计算总运行时间
        elapsed_time = time.time() - start_time
        
        # 6. 汇总结果
        result["status"] = "success" if success_solvers else "failed"
        result["success_solvers"] = success_solvers
        result["verified_solvers"] = verified_solvers
        result["statistics"] = stats
        result["elapsed_time"] = elapsed_time  # ✅ 保存运行时间
        
        # 添加验证统计
        result["statistics"]["verified_count"] = len(verified_solvers)
        result["statistics"]["success_count"] = len(success_solvers)
        
        logger.info("=" * 80)
        logger.info(f"solve_constraints completed")
        logger.info(f"Status: {result['status']}")
        logger.info(f"Total success solvers: {len(success_solvers)}")
        logger.info(f"Total verified solvers: {len(verified_solvers)}")
        logger.info(f"Elapsed time: {elapsed_time:.2f}s")  # ✅ 输出运行时间
        logger.info("=" * 80)
        
        # 输出全局统计信息
        logger.critical("=" * 80)
        logger.critical("📊 全局统计:")
        logger.critical(f"  总运行 Partitions: {stats['total_partitions']} 个")
        logger.critical(f"  总挑出 Partitions: {stats['selected_partitions']} 个")
        logger.critical(f"  总生成 Solvers: {stats['total_solvers']} 个")
        logger.critical(f"  成功 Solvers: {len(success_solvers)} 个")
        logger.critical(f"  验证通过: {len(verified_solvers)}/{len(success_solvers)}")
        logger.critical(f"  运行时间: {elapsed_time:.2f}s")  # ✅ 添加到统计信息
        logger.critical("=" * 80)

        # 7. 输出成功的 solver
        if success_solvers:
            logger.critical(f"\n🎉 Found {len(success_solvers)} valid solution(s):")
            logger.critical(f"✅ Verified {len(verified_solvers)}/{len(success_solvers)} solution(s)")
            logger.critical("-" * 40)
            
            # for idx, partition in enumerate(success_solvers, 1):
            #     logger.critical(f"Success Solver {idx} Assertions:")
                
            #     for aidx, a in enumerate(partition.solver.assertions(), 1):
            #         logger.critical(f"  [{aidx}] {a}")
                
            #     # 验证约束
            #     entailed = constraint_test(partition.solver)
            #     if not entailed:
            #         logger.critical(f"❌ Solution {idx} failed constraint test!")
            #     else:
            #         logger.critical(f"✅ Solution {idx} passed constraint test!")
            #     logger.critical("-" * 40)
        else:
            logger.warning("⚠️ No valid solutions found")
        
        return result
    
    except KeyboardInterrupt:
        logger.warning("❌ Interrupted by user")
        result["status"] = "error"
        result["error_message"] = "Interrupted by user"
        result["elapsed_time"] = time.time() - start_time  # ✅ 记录时间
        return result
    
    except Exception as e:
        logger.error(f"❌ Error in solve_constraints: {e}")
        logger.error(traceback.format_exc())
        result["status"] = "error"
        result["error_message"] = str(e)
        result["elapsed_time"] = time.time() - start_time  # ✅ 记录时间
        return result
    
    finally:
        flush_all_handlers()


def batch_solve(
    text_constraints_list: List[List[str]],
    n_max: int = 36,
    max_depth: int = 10,
    stop_on_error: bool = False
) -> List[Dict]:
    """批量处理多个约束组"""
    logger = setup_batch_logger()

    # ✅ 记录批量处理的总开始时间
    batch_start_time = time.time()

    logger.info("=" * 80)
    logger.info(f"🚀 Starting batch_solve_constraints")
    logger.info(f"Total constraint groups: {len(text_constraints_list)}")
    logger.info(f"Parameters: n_max={n_max}, max_depth={max_depth}, stop_on_error={stop_on_error}")
    logger.info("=" * 80)
    
    results = []

    # 全局统计信息
    global_stats = {
        'total_constraints': len(text_constraints_list),
        'success_count': 0,
        'failed_count': 0,
        'error_count': 0,
        'total_partitions': 0,
        'total_selected_partitions': 0,
        'total_solvers': 0,
        'total_success_solvers': 0,
        'total_verified_solvers': 0,
        'total_time': 0.0  # ✅ 添加总时间统计
    }
    
    for idx, text_constraints in enumerate(text_constraints_list, 1):
        logger.info("")
        logger.info("=" * 80)
        logger.critical(f"📋 处理约束组 [{idx}/{len(text_constraints_list)}]")
        logger.info(f"约束: {text_constraints}")
        logger.info("=" * 80)
        
        try:
            result = solve(text_constraints, n_max, max_depth)
            results.append(result)

            # ✅ 累加总运行时间
            global_stats['total_time'] += result.get('elapsed_time', 0.0)

            # 更新全局统计
            if result["status"] == "success":
                global_stats['success_count'] += 1
                
                if 'statistics' in result:
                    stats = result['statistics']
                    global_stats['total_partitions'] += stats.get('total_partitions', 0)
                    global_stats['total_selected_partitions'] += stats.get('selected_partitions', 0)
                    global_stats['total_solvers'] += stats.get('total_solvers', 0)
                    global_stats['total_success_solvers'] += len(result.get('success_solvers', []))
                    global_stats['total_verified_solvers'] += len(result.get('verified_solvers', []))
            
            elif result["status"] == "failed":
                global_stats['failed_count'] += 1
            else:
                global_stats['error_count'] += 1

            # 输出当前约束组的统计信息
            logger.info("-" * 80)
            logger.critical(f"✅ 约束组 [{idx}] 完成:")
            logger.critical(f"   状态: {result['status']}")
            logger.critical(f"   Solver ID: {result.get('solver_id', 'N/A')}")
            logger.critical(f"   运行时间: {result.get('elapsed_time', 0.0):.2f}s")  # ✅ 显示时间
            
            if 'statistics' in result:
                stats = result['statistics']
                success_count = len(result.get('success_solvers', []))
                verified_count = len(result.get('verified_solvers', []))
                
                logger.critical(f"   本组统计:")
                logger.critical(f"     - Partitions: {stats.get('total_partitions', 0)} 个")
                logger.critical(f"     - Selected: {stats.get('selected_partitions', 0)} 个")
                logger.critical(f"     - Solvers: {stats.get('total_solvers', 0)} 个")
                logger.critical(f"     - Success: {success_count} 个")
                logger.critical(f"     - Verified: {verified_count}/{success_count}")
            
            if result.get('error_message'):
                logger.error(f"   错误信息: {result['error_message']}")
            
            logger.info("-" * 80)

            # 记录当前结果
            elapsed = result.get('elapsed_time', 0.0)
            if result["status"] == "success":
                verified_count = len(result.get('verified_solvers', []))
                success_count = len(result.get('success_solvers', []))
                logger.info(f"✅ Group {idx} SUCCESS: {success_count} solution(s), verified {verified_count}/{success_count}, time: {elapsed:.2f}s")
            elif result["status"] == "failed":
                logger.warning(f"⚠️ Group {idx} FAILED: {result.get('error_message', 'No solutions')}, time: {elapsed:.2f}s")
            else:
                logger.error(f"❌ Group {idx} ERROR: {result.get('error_message', 'Unknown error')}, time: {elapsed:.2f}s")
            
            # 输出累计进度
            logger.info("")
            logger.info(f"📊 进度: [{idx}/{len(text_constraints_list)}]")
            logger.info(f"   成功: {global_stats['success_count']} 个")
            logger.info(f"   失败: {global_stats['failed_count']} 个")
            logger.info(f"   错误: {global_stats['error_count']} 个")
            logger.info(f"   验证通过: {global_stats['total_verified_solvers']}/{global_stats['total_success_solvers']}")
            logger.info(f"   累计用时: {global_stats['total_time']:.2f}s")  # ✅ 显示累计时间
            logger.info("")

            if stop_on_error and result["status"] == "error":
                logger.error(f"❌ Stopping batch processing due to error in group {idx}")
                break
        
        except KeyboardInterrupt:
            logger.warning("⚠️ 用户中断批量处理")
            break
        
        except Exception as e:
            logger.error(f"❌ Unexpected error in group {idx}: {e}")
            logger.error(traceback.format_exc())
            
            error_result = {
                "status": "error",
                "solver_id": None,
                "success_solvers": [],
                "verified_solvers": [],
                "error_message": str(e),
                "statistics": {},
                "elapsed_time": 0.0  # ✅ 错误情况也记录时间
            }
            results.append(error_result)
            global_stats['error_count'] += 1
            
            if stop_on_error:
                logger.error(f"❌ Stopping batch processing due to unexpected error")
                break
    
    # ✅ 计算批量处理的总时间（包括所有约束组的处理时间 + 批量处理本身的开销）
    batch_total_time = time.time() - batch_start_time

    # 输出全局统计汇总
    logger.info("")
    logger.info("=" * 80)
    logger.critical("🎉 批量处理完成!")
    logger.info("=" * 80)
    
    logger.critical(f"📊 总体统计:")
    logger.critical(f"   总约束组数: {global_stats['total_constraints']} 个")
    logger.critical(f"   成功: {global_stats['success_count']} 个 ({global_stats['success_count']}/{global_stats['total_constraints']})")
    logger.critical(f"   失败: {global_stats['failed_count']} 个 ({global_stats['failed_count']}/{global_stats['total_constraints']})")
    logger.critical(f"   错误: {global_stats['error_count']} 个 ({global_stats['error_count']}/{global_stats['total_constraints']})")
    
    logger.critical(f"")
    logger.critical(f"📈 资源统计:")
    logger.critical(f"   总生成 Partitions: {global_stats['total_partitions']} 个")
    logger.critical(f"   总挑出 Partitions: {global_stats['total_selected_partitions']} 个")
    logger.critical(f"   总生成 Solvers: {global_stats['total_solvers']} 个")
    logger.critical(f"   总成功 Solvers: {global_stats['total_success_solvers']} 个")
    logger.critical(f"   总验证通过: {global_stats['total_verified_solvers']}/{global_stats['total_success_solvers']}")
    
    # ✅ 添加时间统计
    logger.critical(f"")
    logger.critical(f"⏱️  时间统计:")
    logger.critical(f"   约束处理总时间: {global_stats['total_time']:.2f}s")
    logger.critical(f"   批量处理总时间: {batch_total_time:.2f}s")
    logger.critical(f"   平均每个约束: {global_stats['total_time']/len(text_constraints_list):.2f}s")
    
    if global_stats['total_partitions'] > 0:
        logger.critical(f"")
        logger.critical(f"📉 效率指标:")
        logger.critical(f"   Partition 选择率: {global_stats['total_selected_partitions']}/{global_stats['total_partitions']} ({global_stats['total_selected_partitions']/global_stats['total_partitions']*100:.1f}%)")
        if global_stats['total_solvers'] > 0:
            logger.critical(f"   Solver 成功率: {global_stats['total_success_solvers']}/{global_stats['total_solvers']} ({global_stats['total_success_solvers']/global_stats['total_solvers']*100:.1f}%)")

    logger.info("=" * 80)
    
    # 输出每个约束组的详细结果
    logger.critical("")
    logger.critical("📋 详细结果列表:")
    logger.critical("-" * 80)
    
    for idx, result in enumerate(results, 1):
        status_emoji = {
            'success': '✅',
            'failed': '❌',
            'error': '⚠️'
        }.get(result['status'], '❓')
        
        logger.critical(f"[{idx}] {status_emoji} {result['status'].upper()}")
        logger.critical(f"    Solver ID: {result.get('solver_id', 'N/A')}")
        logger.critical(f"    运行时间: {result.get('elapsed_time', 0.0):.2f}s")  # ✅ 显示时间
        
        if 'statistics' in result and result['statistics']:
            stats = result['statistics']
            success_count = len(result.get('success_solvers', []))
            verified_count = len(result.get('verified_solvers', []))
            
            logger.critical(f"    统计: P={stats.get('total_partitions', 0)}, "
                          f"S={stats.get('selected_partitions', 0)}, "
                          f"Sol={stats.get('total_solvers', 0)}, "
                          f"Succ={success_count}, "
                          f"Verified={verified_count}/{success_count}")
        
        if result.get('error_message'):
            logger.critical(f"    错误: {result['error_message']}")
        
        logger.critical("-" * 80)

    # ✅ 详细结果表格（添加时间列）
    logger.info("\nDetailed Results:")
    logger.info("-" * 145)
    logger.info(f"{'No.':<5} {'Solver ID':<30} {'Status':<10} {'Partitions':<15} {'Solvers':<10} {'Success':<10} {'Verified':<12} {'Time(s)':<10}")
    logger.info("-" * 145)
    
    for idx, result in enumerate(results, 1):
        solver_id = result.get("solver_id", "N/A")[:28]
        status = result["status"]
        
        # 获取统计信息
        stats = result.get('statistics', {})
        total_partitions = stats.get('total_partitions', 0)
        selected_partitions = stats.get('selected_partitions', 0)
        total_solvers = stats.get('total_solvers', 0)
        
        success_count = len(result.get("success_solvers", []))
        verified_count = len(result.get("verified_solvers", []))
        elapsed_time = result.get('elapsed_time', 0.0)  # ✅ 获取运行时间
        
        # 格式化各列
        partition_ratio = f"{selected_partitions}/{total_partitions}" if total_partitions > 0 else "N/A"
        verified_ratio = f"{verified_count}/{success_count}" if success_count > 0 else "N/A"
        time_str = f"{elapsed_time:.2f}"  # ✅ 格式化时间（保留2位小数）
        
        logger.info(f"{idx:<5} {solver_id:<30} {status:<10} {partition_ratio:<15} {total_solvers:<10} {success_count:<10} {verified_ratio:<12} {time_str:<10}")
    
    logger.info("-" * 145)
    
    # ✅ 在表格后添加时间汇总
    logger.info(f"\n总处理时间: {global_stats['total_time']:.2f}s (平均: {global_stats['total_time']/len(text_constraints_list):.2f}s/约束)")
    logger.info(f"批量总时间: {batch_total_time:.2f}s")
    
    return results


def constraint_test(solver: SMTSolver) -> bool:
    """
    验证 solver 是否等价于[1,2,3,4,5,8]
    
    参数:
        solver: 要验证的 SMTSolver
    
    返回:
        bool: 是否满足所有约束
    """
    text_constraints = [
        "x6 == 8*x1",
        "x5 == 5*x1",
        "x4 == 4*x1",
        "x3 == 3*x1",
        "x2 == 2*x1"
    ]
    constraints = [SMTSolver.text_to_constraint(tc) for tc in text_constraints]
    
    for c in constraints:
        if not solver.is_entailed(c):
            return False
    return True


def prove(text_constraints: List[str]):
    """主函数：演示单个约束组的处理"""
    # setup_logger(
    #     name="cube",
    #     level=10,  # DEBUG
    #     log_to_file=True,
    #     console_level=20  # INFO
    # )
    
    # 单个约束组示例
    # text_constraints = ["x6 == 2 * x5", "x5 == x4 + x3"]
    # text_constraints = ["x6 == x5 + x1", "x5 == x1 + x1"]
    
    result = solve(
        text_constraints=text_constraints,
        n_max=36,
        max_depth=10
    )
    
    flush_all_handlers()


def batch_prove(text_constraints_list: List[List[str]]):
    """批量处理示例"""
    # setup_logger(
    #     name="cube",
    #     level=logging.DEBUG,
    #     log_to_file=True,
    #     console_level=logging.INFO,
    #     # file_level=logging.DEBUG
    # )
    # print(f"Logger created: {logger}")
    # print(f"Logger handlers: {logger.handlers}")

    # return
    # 多个约束组
    # text_constraints = ["x6 == 2 * x5", "x5 == x4 + x3"]
    # text_constraints = ["x6 == 2 * x5", "x5 == x4 + x2"]

    # text_constraints_list = [
    #     ["x6 == 2 * x5", "x5 == x4 + x2"],
    #     ["x6 == 2 * x5", "x5 == x4 + x3"],
    #     # ["x6 == x5 + x4"],
    #     # ["x6 == x5 + x3", "x5 == x3 + x2"],
    #     # ["x6 >= x5", "x5 >= x4"],
    # ]
    
    results = batch_solve(
        text_constraints_list=text_constraints_list,
        n_max=36,
        max_depth=10,
        stop_on_error=False  # 遇到错误继续处理
    )
    
    # flush_all_handlers()