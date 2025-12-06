"""
Optimizer 模块：用于对 Partition 进行优化分析。
引用 F.py 的 F 类和 partition.py 的 Partition 类。
"""
from typing import Optional, List, Dict, Tuple
from fractions import Fraction
from math import comb
import pulp

from core.breakdown import BreakdownNode

from .F import F  # 使用相对导入（同一包内）
from .partition import Partition  # 使用相对导入
from .logger import get_logger, log_on_error  # 导入 get_logger 函数
from .smt import SMTSolver  # 导入 SMTSolver 类
from .constants import Constants  # 导入 Constants 类
# logger = get_logger("optim")

class OptimizationError(Exception):
    """优化相关的异常类"""
    pass

class Optimizer:
    """
    优化器类：
    - 持有一个 F 类实例（来自 F.py），用于进行相关计算
    - 提供方法接受 Partition 实例作为输入，进行优化分析
    
    主要功能：
    - 对给定 Partition 进行约束优化
    - 利用 F 类的功能辅助计算
    - 返回优化后的结果或建议
    """
    
    def __init__(self, n_max: int = None):
        """
        初始化优化器。
        
        参数:
            f_instance: F 类的实例。若为 None，则在内部创建默认实例。
        """
        if n_max is None:
            n_max = Constants.F_N_MAX
        self.f = F(n_max)
        self.theta_6 = self.f.theta[6] - Fraction(1, 6)
    
    def s(self, n: int, i: int) -> int:
        """
        辅助函数：s(n, i) = binom(n+i, i-1)
        返回组合数 C(n+i, i-1)
        # 实际是 (n+1)x_{1-i}的组合数， i = i_min - 1
        """
        return comb(n + i, i - 1)

    def new_calc_node(self, p: Partition, n: int, breakdown_incompleteness: bool) -> None:
        """
        对单个 Partition 进行分析，返回所有 member 的计算结果。
        
        算法：
        1. 读取 partition.i_min，令 i = i_min - 1
        2. 对每个 member：
           - 读取 coeffs 的 K = tuple(coeffs.values())
           - 读取 relation（即 member['relation']）
           - 如果 relation == '='：
               返回 F._sigma(K)（Fraction 类型）
           - 否则（relation == '>'）：
               - 获取 F(K, i) 的结果（Fraction 列表，对应 n=-2..10）
               - 读取 member['n_LHS'][1]，假设返回 (k_val, op)
               - 如果 op == '>'：
                   返回 ((F(K,i)[n_lhs], s(n_lhs, i)), (F(K,i)[n_lhs-1], 0))
               - 如果 op == '='：
                   返回 ((F(K,i)[n_lhs-2], 0), (F(K,i)[n_lhs-2], 0))
        
        参数:
            partition: Partition 实例
        
        返回:
            List: 每个元素为 Fraction 或 ((Fraction, int), (Fraction, int))
        """

        logger = p.get_logger()
        for node in p.nodes:        
            K = tuple(node.coeffs.values())
            relation = node.relation
            
            if relation == '=':
                sigma_val = self.f._sigma(K)
                node.n_LHS[n].update({
                    'values': [sigma_val, sigma_val],
                    'combo': 0,
                    'type': 'fixed'
                })                
                # results.append(((sigma_val, 'fixed'),))
            else:
                # 需要node.i_min>=2, 由于node.i_min == 1且node.relation != '='已被排除
                # 可以放心使用
                fracs = self.f.get(K, node.i_min - 1)
                # n_to_idx = {n: idx for idx, n in enumerate(self.f.n_range)}
                
                n_lhs = node.n_LHS[n]['n_lhs']
                op = node.n_LHS[n]['op']
                
                if op == '>':
                    lower = fracs[n_lhs]
                    upper = fracs[n_lhs - 1]
                    combo = self.s(n_lhs, node.i_min - 1)
                    node.n_LHS[n].update({
                        'values': [lower, upper],
                        'combo': combo,
                        'type': 'gt'
                    })                    
                # op == '=' 只会在breakdown_incompleteness为True时出现
                elif op == '=':
                    if not breakdown_incompleteness:
                        raise Exception("op == '=' should not appear in new_calc_node")
                    value = fracs[n_lhs - 2]
                    node.n_LHS[n].update({
                        'values': [value, value],
                        'combo': 0,
                        'type': 'equ'
                    })                   
        return 

    def new_optimize(self, p: Partition, n = 1, method = 'pulp') -> Dict:
        """
        对 analyze 的输出进行优化选择（使用 PuLP，Fraction 通分后优化）。
        
        算法：
        1. 提取所有非 tuple 成员（Fraction 类型），计算它们的和 sigma_sum
        2. 计算上限 m = self.theta_6 - sigma_sum
        3. 若没有 tuple 成员：
           - m > 0: 剪枝
           - m <= 0: 这是一个可行解，直接返回
        4. 快速剪枝检查（有 tuple 时）：
           - 若所有 tuple[0][0] 之和 > m，返回 "n=1 too small"
           - 若所有 tuple[1][0] 之和 < m，返回 "pruned"
        5. 将所有 Fraction 通分为整数后，使用 PuLP 求解最优选择：
           - 决策变量：每个 tuple 选择 t=0（第一项）或 t=1（第二项）
           - 约束：sum(tuple[t][0]) < m（通分后的整数约束）
           - 目标：min(sum(tuple[t][1]))
        
        参数:
            method: 1. 'pulp' 2. 'enum' (遍历)
            part_fs: analyze_partition 的输出
        
        返回:
            Dict with status, selection, member_indices_for_zero, etc.
        """
        
        logger = p.get_logger()
        logger.info("Starting optimization...")

        # 先处理 partition
        # self.process_partition(partition, n, Breakdown)
        
        # 初始化分类容器
        fixed_terms = []
        equ_terms = []
        gt_lower = []
        gt_upper = []
        combo_lower = []
        combo_upper = []
        gt_idx = []  # 记录索引，可能是 int 或 tuple(member_id, breakdown_id)
        
        for idx, node in enumerate(p.nodes):
            n_lhs_info = node.n_LHS[n]
            type_val = n_lhs_info['type']
            if type_val == 'fixed':
                value = n_lhs_info['values'][0]
                fixed_terms.append(value)
            elif type_val == 'gt':
                lower, upper = n_lhs_info['values']
                combo = n_lhs_info['combo']
                
                gt_lower.append(lower)
                gt_upper.append(upper)
                combo_lower.append(combo)
                combo_upper.append(0)
                gt_idx.append(idx)
            elif type_val == 'equ':
                equ_value = n_lhs_info['values'][0]
                equ_terms.append(equ_value)
        
        # 计算各部分的和
        fixed_sum = sum(fixed_terms, Fraction(0))
        equ_sum = sum(equ_terms, Fraction(0))
        gt_lower_sum = sum(gt_lower, Fraction(0))
        gt_upper_sum = sum(gt_upper, Fraction(0))
        
        # 计算上下界
        lower = fixed_sum + equ_sum + gt_lower_sum
        upper = fixed_sum + equ_sum + gt_upper_sum
        lower_op = ">" if lower > self.theta_6 else "==" if lower == self.theta_6 else "<"
        upper_op = ">" if upper > self.theta_6 else "==" if upper == self.theta_6 else "<"
        
        logger.info(f" lower bound: {self.f.formatter.fraction_to_base(lower)} ({lower_op} {self.f.formatter.fraction_to_base(self.theta_6)})")
        logger.info(f" upper bound: {self.f.formatter.fraction_to_base(upper)} ({upper_op} {self.f.formatter.fraction_to_base(self.theta_6)})")
        logger.info("-" * 40)
        
        m = self.theta_6 - fixed_sum - equ_sum
        
        # 2. 若没有 gt 成员，此时是定值，没有优化的必要
        if not gt_lower:
            if m > 0:
                result = {
                    "status": "pruned",
                    "result": self.f.formatter.fraction_to_base(lower),
                    "details": f"too small, pruned"
                }
                self.log_result(p, result)
                return result
            elif not equ_terms:
                result = {
                    "status": "success",
                    "result": self.f.formatter.fraction_to_base(lower),
                    "details": f"valid solution"
                }
                self.log_result(p, result)
                return result
            else:
                result = {
                    "status": "extend",
                    "result": self.f.formatter.fraction_to_base(lower),
                    "details": f"n=1 too small"
                }
                self.log_result(p, result)
                return result

        
        # 4. 快速剪枝检查
        if lower_op == '>':
            result = {
                "status": "extend",
                "result": [self.f.formatter.fraction_to_base(lower),
                           self.f.formatter.fraction_to_base(upper)],
                "details": f"n=1 too small"
            }
            self.log_result(p, result)
            return result
        
        if upper_op == '<':
            result = {
                "status": "pruned",
                "result": [self.f.formatter.fraction_to_base(lower),
                           self.f.formatter.fraction_to_base(upper)],
                "details": f"too small, pruned"
            }
            self.log_result(p, result)
            return result
        
        # 5. 通分：计算所有 Fraction 的最小公倍数作为缩放因子
        from math import gcd
        from functools import reduce
        
        def lcm(a, b):
            return abs(a * b) // gcd(a, b)
        
        gts = gt_lower + gt_upper + [m]
        denominators = [f.denominator for f in gts]
        scale = reduce(lcm, denominators, 1)
        
        # 缩放后的整数值
        gt_lower_int = [int(f * scale) for f in gt_lower]
        gt_upper_int = [int(f * scale) for f in gt_upper]
        m_int = int(m * scale)

        logger.info(f" Optimization Problem: ")
        logger.info(f" Decision variables: choices[i] ∈ {{0, 1}} for i in [0, {len(gt_lower)-1}]")
        logger.info(f" Objective: min sum([(1-choices[i]) * lower_combo[i] + choices[i] * upper_combo[i]])")
        logger.info(f" constraints: sum([(1-choices[i]) * lower[i] + choices[i] * upper[i]]) < constUpper")
        logger.info(f"   Scaling factor: {scale}")
        logger.info(f"   lower: {gt_lower_int}, lower_combo: {combo_lower}")
        logger.info(f"   upper: {gt_upper_int}, upper_combo: {combo_upper}")
        logger.info(f"   constUpper (int): {m_int}")
        logger.info("-" * 40)
        
        n_vars = len(gt_lower)
        # 6. 使用 PuLP 求解（整数版本）
        if method == 'pulp':
            status, selection_or_failure_info = self._optimize_pulp(
                p, gt_lower_int, gt_upper_int,
                combo_lower, combo_upper,
                m_int)
        elif method == 'enum':
            status, selection_or_failure_info = self._optimize_enum(
                p, gt_lower_int, gt_upper_int,
                combo_lower, combo_upper,
                m_int)
        else:
            raise NotImplementedError("Unknown optimization method.")

        if status is not None:
            # total_combo = int(pulp.value(objective_expr))
            selected_gts = [
                gt_lower[i] if selection_or_failure_info[i] == 0 else gt_upper[i]
                for i in range(n_vars)
            ]
            selected_combos = [
                combo_lower[i] if selection_or_failure_info[i] == 0 else combo_upper[i]
                for i in range(n_vars)
            ]
            selected_gts_sum = sum(selected_gts, Fraction(0))
            
            # 找出 selection 中为 0 的项对应的 member 索引
            selected_idx = [gt_idx[i] for i in range(n_vars) if selection_or_failure_info[i] == 0]
            
            result = {
                "status": "split",
                "selection": selection_or_failure_info,
                "member_indices_for_zero": selected_idx,
                "selected_s_values": selected_combos,
                "details": f"split into {sum(selected_combos)} terms, " 
                    f"with f = {self.f.formatter.fraction_to_base(selected_gts_sum + fixed_sum + equ_sum)}",
            }
            self.log_result(p, result)
            return result
        else:
            result = {
                "status": "optimization_failed",
                "details": f"PuLP solver status: {selection_or_failure_info}"
            }
            self.log_result(p, result)
            return result


    def log_result(self,  p: Partition, result: Dict) -> None:
        """
        记录优化结果的日志信息。
        """
        logger = p.get_logger()
        logger.info("Optimization result:")
        for k, v in result.items():
            logger.info(f" {k}: {v}")
        logger.info("-" * 40)

    def _optimize_enum(self, p: Partition, const0: List[int],
                    constr1: List[int],
                    obj0: List[int],
                    obj1: List[int],
                    constUpper: int) -> Tuple[str, any]:
        """
        使用遍历法进行优化选择
    
        约束条件：sum((1-choices[i])*const0[i] + choices[i]*constr1[i]) < constUpper（整数版本）
        目标：min(sum((1-choices[i])*obj0[i] + choices[i]*obj1[i]))
    
        参数:
            const0: 选择第一项时的约束系数（整数）
            constr1: 选择第二项时的约束系数（整数）
            obj0: 选择第一项时的目标值（s-value）
            obj1: 选择第二项时的目标值（s-value）
            constUpper: 约束上界（整数，严格小于）
    
        返回:
            Tuple[str, any]: 
                - ('success', selection): 成功找到最优解，返回选择列表
                - ('failed', reason): 失败，返回失败原因
        """
        n = len(const0)
        logger = p.get_logger()
        logger.info(f" Enumerating {2**n} combinations...")
        
        best_selection = None
        best_obj_value = float('inf')
        feasible_count = 0
        
        # 遍历所有 2^n 种选择组合
        for combo in range(2**n):
            # 将整数转换为二进制选择列表
            # combo=5 (二进制 101) -> [1, 0, 1] (n=3)
            selection = [(combo >> i) & 1 for i in range(n)]
        
            # 计算约束值：sum((1-choices[i])*const0[i] + choices[i]*constr1[i])
            constraint_value = sum(
                const0[i] + selection[i] * (constr1[i] - const0[i])
                for i in range(n)
            )
        
            # 检查约束是否满足（严格小于）
            if constraint_value >= constUpper:
                continue  # 不满足约束，跳过
        
            # 计算目标值：sum((1-choices[i])*obj0[i] + choices[i]*obj1[i])
            obj_value = sum(
                obj0[i] + selection[i] * (obj1[i] - obj0[i])
                for i in range(n)
            )
        
            feasible_count += 1
        
            # 更新最优解
            if obj_value < best_obj_value:
                best_obj_value = obj_value
                best_selection = selection

    
        # 检查是否找到可行解
        if best_selection is None:
            logger.warning(f" No feasible solution found (checked {2**n} combinations)")
            return 'failed', "No feasible solution found by enumeration"
    
        logger.info(
            f" Enumeration complete: "
            f"best_obj={best_obj_value}, "
            f"selection={best_selection}, "
        )
    
        return 'success', best_selection

    def _optimize_pulp(self, p: Partition, const0: List[int],
                       constr1: List[int],
                       obj0: List[int],
                       obj1: List[int],
                       constUpper: int) -> Dict:
        """
        使用 PuLP 线性规划求解器进行优化选择。
        
        本方法将优化问题建模为一个 0-1 整数线性规划问题：
        - 对于每个 inequality 项，有两个选择（第一项或第二项）
        - 每个选择对应不同的约束系数和目标值
        - 使用二元决策变量表示选择，choices[i] = 0 表示选第一项，= 1 表示选第二项
        
        数学模型：
            决策变量: choices[i] ∈ {0, 1}, i = 0..n-1
            
            约束条件: 
                sum_{i=0}^{n-1} [(1-choices[i]) * const0[i] + choices[i] * constr1[i]] < constUpper
                等价于: sum_{i=0}^{n-1} [const0[i] + choices[i] * (constr1[i] - const0[i])] ≤ constUpper - 1
            
            目标函数 (最小化):
                min sum_{i=0}^{n-1} [(1-choices[i]) * obj0[i] + choices[i] * obj1[i]]
                等价于: min sum_{i=0}^{n-1} [obj0[i] + choices[i] * (obj1[i] - obj0[i])]
        
        参数:
            const0: 选择第一项时的约束系数列表（已通分为整数）
                对应 gt_terms[i][0][0] 缩放后的值
            constr1: 选择第二项时的约束系数列表（已通分为整数）
                    对应 gt_terms[i][1][0] 缩放后的值
            obj0: 选择第一项时的目标值列表（s-value）
                对应 gt_terms[i][0][1]（组合数）
            obj1: 选择第二项时的目标值列表（s-value）
                对应 gt_terms[i][1][1]（通常为 0）
            constUpper: 约束上界（已通分为整数）
                    对应 (theta_6 - fixed_sum - equ_sum) * scale
        
        返回:
            Tuple[str, any]: 
                - ('success', selection): 成功找到最优解
                    * selection: List[int] - 长度为 n 的列表，每个元素为 0 或 1
                    * selection[i] = 0 表示第 i 个 inequality 项选择第一项
                    * selection[i] = 1 表示第 i 个 inequality 项选择第二项
                - ('failed', reason): 求解失败
                    * reason: str - 失败原因，PuLP 求解器的状态字符串
        
        示例:
            >>> const0 = [10, 20, 30]      # 第一项的约束系数
            >>> constr1 = [15, 25, 35]     # 第二项的约束系数
            >>> obj0 = [5, 3, 2]           # 第一项的目标值
            >>> obj1 = [0, 0, 0]           # 第二项的目标值
            >>> constUpper = 50            # 约束上界
            >>> 
            >>> status, result = optimizer._optimize_pulp(
            ...     const0, constr1, obj0, obj1, constUpper
            ... )
            >>> 
            >>> if status == 'success':
            ...     print(f"最优选择: {result}")
            ...     # 例如: [0, 1, 0] 表示选择第1项、第2项、第1项
            ...     total_const = sum(
            ...         const0[i] if result[i] == 0 else constr1[i]
            ...         for i in range(len(result))
            ...     )
            ...     total_obj = sum(
            ...         obj0[i] if result[i] == 0 else obj1[i]
            ...         for i in range(len(result))
            ...     )
            ...     print(f"约束值: {total_const} < {constUpper}")
            ...     print(f"目标值: {total_obj}")
        
        注意:
            1. 所有输入的约束系数和上界都应该是整数（已通分）
            2. 约束是严格小于 (<)，在整数域中实现为 <= constUpper - 1
            3. 使用 CBC 求解器，求解时间通常为 O(多项式)
            4. 如果问题规模很大（n > 100），可能需要较长时间
            5. 返回的 selection 保证满足约束且目标值最小
        
        实现细节:
            - 使用 PuLP 库建模 0-1 整数线性规划问题
            - 求解器: PULP_CBC_CMD（开源求解器）
            - 求解模式: 静默模式 (msg=0)，不输出中间信息
            - 时间复杂度: 理论上 O(2^n)，实际上通过分支定界等技术优化
        
        相关方法:
            - _optimize_enum: 使用遍历法的替代实现
            - optimize: 调用本方法的上层接口
        """
        n = len(const0)
        logger = p.get_logger()
        
        # 创建问题实例
        prob = pulp.LpProblem("MinimizeS", pulp.LpMinimize)
        
        # 决策变量：choice[i] = 0 表示选第一项，= 1 表示选第二项
        choices = [pulp.LpVariable(f"choice_{i}", cat='Binary') for i in range(n)]
        
        # 约束：sum(tuple[choice[i]][0]) < m（整数版本）
        constraint_expr = pulp.lpSum([
            const0[i] + choices[i] * (constr1[i] - const0[i])
            for i in range(n)
        ])
        
        # 严格小于：在整数域中 < m_scaled 等价于 <= m_scaled - 1
        prob += constraint_expr <= constUpper - 1, "FractionConstraint"
        
        # 目标：min(sum(tuple[choice[i]][1]))
        objective_expr = pulp.lpSum([
            obj0[i] + choices[i] * (obj1[i] - obj0[i])
            for i in range(n)
        ])
        prob += objective_expr
        
        # 求解
        prob.solve(pulp.PULP_CBC_CMD(msg=0))  # 使用 CBC 求解器，静默模式
        
        # 检查求解状态
        if prob.status == pulp.LpStatusOptimal:
            selection = [int(pulp.value(choices[i])) for i in range(n)]
            logger.info(f" PuLP optimization successful: selection={selection}")            
            return 'success', selection
        
        failure_reason = pulp.LpStatus[prob.status]
        logger.warning(f" PuLP optimization failed: {failure_reason}")        
        return 'failed', failure_reason

# 简单示例用法
if __name__ == "__main__":
    pass
