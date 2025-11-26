"""
Optimizer 模块：用于对 Partition 进行优化分析。
引用 F.py 的 F 类和 smt_tools.py 的 Partition 类。
"""

from typing import Optional, List, Dict, Tuple
from fractions import Fraction
from math import comb
from F import F
from smt_tools import Partition
import pulp


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
    
    def __init__(self, f_instance: Optional[F] = None):
        """
        初始化优化器。
        
        参数:
            f_instance: F 类的实例。若为 None，则在内部创建默认实例。
        """
        self.f = f_instance if f_instance is not None else F()
        self.theta_6 = self.f.theta[6] - Fraction(1, 6)
    
    def s(self, n: int, i: int) -> int:
        """
        辅助函数：s(n, i) = binom(n+i, i-1)
        返回组合数 C(n+i, i-1)
        """
        if i < 1:
            return 0
        return comb(n + i, i - 1)
    
    def analyze_partition(self, partition: Partition) -> List:
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
        if partition.i_min is None or partition.i_min <= 1:
            return []
        
        i = partition.i_min - 1
        results = []
        
        for member in partition.members:
            coeffs = member.get('coeffs', {})
            K = tuple(coeffs.values())
            relation = member.get('relation', '>')
            
            if relation == '=':
                sigma_val = self.f._sigma(K)
                results.append(((sigma_val, 'fixed'),))
            else:
                fracs, _ = self.f.get(K, i, old=True)
                n_to_idx = {n: idx for idx, n in enumerate(self.f.n_range)}
                
                n_LHS = member.get('n_LHS', {})
                if 1 not in n_LHS:
                    continue
                k_val, op = n_LHS[1]
                
                if k_val is None:
                    continue
                
                if op == '>':
                    n_lhs = k_val
                    if n_lhs not in n_to_idx or (n_lhs - 1) not in n_to_idx:
                        continue
                    idx_n = n_to_idx[n_lhs]
                    idx_n_minus1 = n_to_idx[n_lhs - 1]
                    val1 = (fracs[idx_n], self.s(n_lhs, i))
                    val2 = (fracs[idx_n_minus1], 0)
                    results.append((val1, val2))
                elif op == '=':
                    n_lhs = k_val
                    # if (n_lhs - 2) not in n_to_idx or (n_lhs - 3) not in n_to_idx:
                    #     continue
                    idx_n_minus2 = n_to_idx[n_lhs - 2]
                    # idx_n_minus3 = n_to_idx[n_lhs - 3]
                    # val1 = (fracs[idx_n_minus2], 0)
                    # val2 = (fracs[idx_n_minus2], 0)
                    results.append(((fracs[idx_n_minus2], 'upperBound'),))
        
        return results
    
    def optimize_selection(self, analysis_results: List) -> Dict:
        """
        对 analyze_partition 的输出进行优化选择（使用 PuLP，Fraction 通分后优化）。
        
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
            analysis_results: analyze_partition 的输出
        
        返回:
            Dict with status, selection, member_indices_for_zero, etc.
        """
        # 1. 分离非 tuple（Fraction）和 tuple 成员，同时记录原始索引
        fixed_terms = []
        upper_bound_terms = []
        tuple_members = []
        tuple_to_member_idx = []  # 记录 tuple 在 analysis_results 中的原始索引
        
        for idx, item in enumerate(analysis_results):
            if len(item) == 1 and isinstance(item[0], tuple) and item[0][1] in ('fixed', 'upperBound'):
                if item[0][1] == 'fixed':
                    fixed_terms.append(item[0][0])
                else:
                    upper_bound_terms.append(item[0][0])
            elif isinstance(item, tuple) and len(item) == 2:
                tuple_members.append(item)
                tuple_to_member_idx.append(idx)  # 记录该 tuple 对应的 member 索引
        
        fixed_sum = sum(fixed_terms, Fraction(0))
        upper_bound_sum = sum(upper_bound_terms, Fraction(0))
        m = self.theta_6 - fixed_sum
        
        # 2. 若没有 tuple 成员，检查 m 与 0 的关系
        if (not tuple_members) and (not upper_bound_terms):
            if m > 0:
                return {
                    "status": "pruned",
                    "result": fixed_sum + Fraction(1, 6),
                    "details": f"too small, pruned"
                }
            else:
                return {
                    "status": "success",
                    "result": fixed_sum + Fraction(1, 6),
                    "details": f"valid solution"
                }
        
        if (not tuple_members) and upper_bound_terms:
            if m > upper_bound_sum:
                return {
                    "status": "pruned",
                    "result": fixed_sum + upper_bound_sum + Fraction(1, 6),
                    "details": f"too small even with upper bounds, pruned"
                }
            else:
                return {
                    "status": "extend",
                    "result": fixed_sum + upper_bound_sum + Fraction(1, 6),
                    "details": f"n=1 too small"
                }
        
        m -= upper_bound_sum  # 减去 upper bound 部分

        # 3. 提取所有 tuple 的第一项和第二项
        first_fracs = [t[0][0] for t in tuple_members]
        first_s = [t[0][1] for t in tuple_members]
        second_fracs = [t[1][0] for t in tuple_members]
        second_s = [t[1][1] for t in tuple_members]
        
        sum_first_frac = sum(first_fracs, Fraction(0))
        sum_second_frac = sum(second_fracs, Fraction(0))
        
        # 4. 快速剪枝检查
        if sum_first_frac > m:
            return {
                "status": "extend",
                "result": [fixed_sum + upper_bound_sum + sum_first_frac + Fraction(1, 6),
                           fixed_sum + upper_bound_sum + sum_second_frac + Fraction(1, 6)],
                "details": f"n=1 too small"
            }
        
        if sum_second_frac < m:
            return {
                "status": "pruned",
                "result": [fixed_sum + upper_bound_sum + sum_first_frac + Fraction(1, 6),
                           fixed_sum + upper_bound_sum + sum_second_frac + Fraction(1, 6)],
                "details": f"too small even with upper bounds, pruned"
            }
        
        # 5. 通分：计算所有 Fraction 的最小公倍数作为缩放因子
        from math import gcd
        from functools import reduce
        
        def lcm(a, b):
            return abs(a * b) // gcd(a, b)
        
        all_fracs = first_fracs + second_fracs + [m]
        denominators = [f.denominator for f in all_fracs]
        scale = reduce(lcm, denominators, 1)
        
        # 缩放后的整数值
        first_fracs_scaled = [int(f * scale) for f in first_fracs]
        second_fracs_scaled = [int(f * scale) for f in second_fracs]
        m_scaled = int(m * scale)
        
        # 6. 使用 PuLP 求解（整数版本）
        n = len(tuple_members)
        
        # 创建问题实例
        prob = pulp.LpProblem("MinimizeS", pulp.LpMinimize)
        
        # 决策变量：choice[i] = 0 表示选第一项，= 1 表示选第二项
        choices = [pulp.LpVariable(f"choice_{i}", cat='Binary') for i in range(n)]
        
        # 约束：sum(tuple[choice[i]][0]) < m（整数版本）
        constraint_expr = pulp.lpSum([
            first_fracs_scaled[i] + choices[i] * (second_fracs_scaled[i] - first_fracs_scaled[i])
            for i in range(n)
        ])
        
        # 严格小于：在整数域中 < m_scaled 等价于 <= m_scaled - 1
        prob += constraint_expr <= m_scaled - 1, "FractionConstraint"
        
        # 目标：min(sum(tuple[choice[i]][1]))
        objective_expr = pulp.lpSum([
            first_s[i] + choices[i] * (second_s[i] - first_s[i])
            for i in range(n)
        ])
        prob += objective_expr
        
        # 求解
        prob.solve(pulp.PULP_CBC_CMD(msg=0))  # 使用 CBC 求解器，静默模式
        
        # 检查求解状态
        if prob.status == pulp.LpStatusOptimal:
            selection = [int(pulp.value(choices[i])) for i in range(n)]
            total_s = int(pulp.value(objective_expr))
            selected_fractions = [tuple_members[i][selection[i]][0] for i in range(n)]
            selected_s_values = [tuple_members[i][selection[i]][1] for i in range(n)]
            sum_fracs = sum(selected_fractions, Fraction(0))
            
            # 找出 selection 中为 0 的项对应的 member 索引
            member_indices_for_zero = [tuple_to_member_idx[i] for i in range(n) if selection[i] == 0]
            
            return {
                "status": "split",
                "selection": selection,
                "member_indices_for_zero": member_indices_for_zero,
                "selected_s_values": selected_s_values,
                "details": f"split into {selected_s_values} terms from {first_s}, members choosing first option: {member_indices_for_zero}",
            }
        else:
            return {
                "status": "optimization_failed",
                "details": f"PuLP solver status: {pulp.LpStatus[prob.status]}"
            }
    


# 简单示例用法
if __name__ == "__main__":
    texts = [
        [["x6 = 2*x5", "x5 = 2*x4"], 4],
        [["x6 = 2*x5", "x5 = x4 + x3"], 4],
        [["x6 = 2*x5"], 5],
        [["x6 = x2 + x3"], 3],
        [["x6 = 2x3"], 3],
    ]
    
    from smt_tools import SMTAnalyzer
    from pprint import pprint

    txts = texts[1][0]  
    an = SMTAnalyzer()
    an.add_constraints_from_text(txts)
    results, i_min = an.enumerate_decompositions()
    partitions = an.classify_decompositions(results, i_min)
    partition = partitions[1]
    pprint(partition.to_dict())
    
    opt = Optimizer()
    analysis_results = opt.analyze_partition(partition)
    # print(analysis_results)
    # exit()
    
    # print("Analysis Results:")
    # for i, (mem, res) in enumerate(zip(partition.members, analysis_results)):
    #     print(f"Member {i}:")
    #     pprint(mem)
    #     print("-------")
    #     pprint(res)
    #     print("=======")
    
    # 测试优化选择
    print("\n" + "="*50)
    print("Optimization Selection:")
    opt_result = opt.optimize_selection(analysis_results)
    pprint(opt_result)