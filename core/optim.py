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
# logger = get_logger("optim")

__all__ = ['SMTSolver', 'Partition', 'F', 'Optimizer']

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
    
    def __init__(self, n_max: int = 10):
        """
        初始化优化器。
        
        参数:
            f_instance: F 类的实例。若为 None，则在内部创建默认实例。
        """
        self.f = F(n_max)
        self.theta_6 = self.f.theta[6] - Fraction(1, 6)
    
    def s(self, n: int, i: int) -> int:
        """
        辅助函数：s(n, i) = binom(n+i, i-1)
        返回组合数 C(n+i, i-1)
        # 实际是 (n+1)x_{1-i}的组合数， i = i_min - 1
        """
        # if i < 1:
        #     return 0
        return comb(n + i, i - 1)

    def get_f_1(self, p: Partition) -> List:
        """
        对i_min = 1的Partition 计算f值，并输出到日志
        
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
        # if partition.i_min is None or partition.i_min <= 1:
        #     return []
        logger = p.get_logger()
        # i = partition.i_min - 1
        fs = []
        
        for idx, member in enumerate(p.breakdowns):
            if member['relation'] != '=':
                continue
            
            K = tuple(member['coeffs'].values())
            sigma_val = self.f._sigma(K)
            fs.append(sigma_val)
            logger.info(f" [{idx+1}] : f = {self.f.formatter.fraction_to_base(sigma_val)}")
        f_sum = sum(fs, Fraction(0))
        if f_sum >= self.theta_6:
            result = {
                "status": "success",
                "result": self.f.formatter.fraction_to_base(f_sum),
                "details": f"valid solution"
            }
            self.log_result(result)
            return result
        else:
            result = {
                "status": "pruned",
                "result": self.f.formatter.fraction_to_base(f_sum),
                "details": f"too small, pruned"
            }
            self.log_result(result)
            return result                    

   # ==================== Member 级别的函数 ====================
    
    # def process_member_f(self, member: Dict, i: int, n: int = 1) -> None:
    #     """
    #     对单个 member 计算 f 值，结果写入 member['n_LHS'][n]。
        
    #     参数:
    #         member: 单个 member 字典
    #         i: partition.i_min - 1
    #         n: 要计算的 n 值
    #     """
    #     K = tuple(member['coeffs'].values())
    #     relation = member['relation']
        
    #     # 初始化 n_LHS 字典
    #     if 'n_LHS' not in member:
    #         member['n_LHS'] = {}
        
    #     if relation == '=':
    #         # 情况1：relation == '='
    #         sigma_val = self.f._sigma(K)
    #         member['n_LHS'][n] = {
    #             **member['n_LHS'].get(n, {}),
    #             'values': [sigma_val, sigma_val],
    #             'combo': 0,
    #             'type': 'fixed'
    #         }
    #     else:
    #         # 情况2：relation == '>'
    #         fracs = self.f.get(K, i)
            
    #         # 检查是否已经有 n_lhs 和 op
    #         if n not in member['n_LHS']:
    #             logger.warning(f"n_LHS[{n}] not found, please call calc_n_LHS({n}) first")
    #             return
            
    #         n_lhs = member['n_LHS'][n]['n_lhs']
    #         op = member['n_LHS'][n]['op']
            
    #         if op == '>':
    #             # 情况2a：op == '>'
    #             lower = fracs[n_lhs]
    #             upper = fracs[n_lhs - 1] if n_lhs > 0 else fracs[0]
    #             combo = self.s(n_lhs, i)
    #             type_val = 'gt'
                
    #             member['n_LHS'][n].update({
    #                 'values': [lower, upper],
    #                 'combo': combo,
    #                 'type': type_val
    #             })
            
    #         elif op == '=':
    #             # 情况2b：op == '='
    #             value = fracs[n_lhs - 2] if (n_lhs - 2) in fracs else fracs[min(fracs.keys())]
                
    #             member['n_LHS'][n].update({
    #                 'values': [value, value],
    #                 'combo': 0,
    #                 'type': 'equ'
    #             })

    # def breakdown_member(self, member: Dict, i: int, n: int = 1) -> None:
    #     """
    #     对单个 member 进行 breakdown，将 LHS = k * x_i 拆分为多个不等式。
    #     结果写入 member['breakdown']。
        
    #     参数:
    #         member: 单个 member 字典
    #         i: partition.i_min - 1
    #         n: 要计算的 n 值
        
    #     前提条件:
    #         - i >= 2 (即 i_min >= 3)
    #         - member['n_LHS'][n]['op'] == '='
    #     """
    #     # 检查前提条件
    #     # if i < 2:
    #     #     logger.warning(f"i={i} < 2, cannot perform breakdown")
    #     #     return
        
    #     # if n not in member.get('n_LHS', {}):
    #     #     logger.warning(f"n_LHS[{n}] not found")
    #     #     return
        
    #     n_lhs_info = member['n_LHS'][n]
    #     op = n_lhs_info.get('op')
        
    #     # 只处理 op == '=' 的情况
    #     if op != '=':
    #         return
        
    #     k = n_lhs_info['n_lhs']
    #     LHS = member['LHS']
    #     K = tuple(member['coeffs'].values())
        
    #     logger.info(f"Breaking down: LHS = {k} * x_{i}")
        
    #     # 创建 breakdown 列表
    #     breakdown = []
        
    #     # 生成 k+1 个分解项：从 j=k 到 j=0
    #     for j in range(k, -1, -1):
    #         breakdown_item = {}
            
    #         # 1. LHS 字段 (z3表达式)
    #         # breakdown[j]['LHS'] = LHS - j * x_{i}
    #         # 需要从 partition.solver 获取变量
    #         breakdown_item['LHS'] = LHS - j  # 这里简化，实际需要 z3 表达式
            
    #         # 2. i 字段
    #         breakdown_item['i'] = i - 1  # i_min - 2
            
    #         # 3. relation 字段
    #         breakdown_item['relation'] = '=' if j == k else '>'
            
    #         # 4. expr 字段
    #         breakdown_item['expr'] = f"LHS - {j}*x{i} {'=' if j == k else '>'} 0"
            
    #         # 5. coeffs 字段
    #         breakdown_item['coeffs'] = {**member['coeffs'], "xi": j}
            
    #         # 6. n_LHS 字段
    #         breakdown_item['n_LHS'] = {}
    #         n_lhs_value = k - j
            
    #         # 计算 values
    #         if j == k:
    #             # j == k 时，op = '='
    #             sigma_val = self.f._sigma((*K, k))
    #             lower = sigma_val
    #             upper = sigma_val
    #             op_type = '='
    #             combo = 0
    #             type_val = 'fixed'
    #         else:
    #             # j != k 时，op = '>'
    #             fracs = self.f.get((*K, j), i - 1)
    #             lower = fracs[n_lhs_value]
    #             upper = fracs[n_lhs_value - 1]
    #             op_type = '>'
    #             combo = self.s(n_lhs_value, i - 1)
    #             type_val = 'gt'
            
    #         breakdown_item['n_LHS'][n] = {
    #             'values': [lower, upper],
    #             'n_lhs': n_lhs_value,
    #             'op': op_type,
    #             'combo': combo,
    #             'type': type_val
    #         }
            
    #         breakdown.append(breakdown_item)
        
    #     # 将 breakdown 添加到 member 中
    #     member['breakdown'] = breakdown
    #     logger.debug(f"Breakdown complete: {len(breakdown)} items")

    # ==================== Partition 级别的函数 ====================
    
    def process_partition(
        self, 
        p: Partition, 
        n: int = 1, 
        Breakdown: bool = True
    ) -> None:
        """
        对整个 Partition 进行处理，循环处理所有 members。
        
        算法流程:
        1. 对每个 member 调用 process_member_f，计算 f 值
        2. 如果 use_breakdown=True 且 i_min >= 3:
           - 对 op == '=' 的 member 调用 breakdown_member
        
        参数:
            partition: Partition 实例
            n: 要计算的 n 值，默认为 1
            use_breakdown: 是否进行 breakdown，默认为 True
        
        返回:
            None（结果写入 partition.members）
        """
        i = p.i_min - 1
        # logger = p.get_logger()
        # logger.info("=" * 40)
        # logger.info(f"Processing partition (i_min={partition.i_min}, n={n}, breakdown={use_breakdown})")
        # logger.info("=" * 40)
        
        # 第一步：对所有 member 计算 f 值
        for member in p.breakdowns:
            # logger.info(f"Processing member [{member_idx+1}/{len(partition.members)}]")
            self.get_pf(p, member, i, n)
            if member['relation']!='=' and Breakdown and i >= 2: 
                self.get_pf_breakdown(p, member, i, n)


            # 日志输出
            # if n in member.get('n_LHS', {}):
            #     info = member['n_LHS'][n]
            #     type_val = info.get('type', 'unknown')
            #     op = info.get('op', 'unknown')
                
                # if type_val == 'fixed':
                #     logger.info(
                #         f"  type=fixed, "
                #         f"value={self.f.formatter.fraction_to_base(info['values'][0])}"
                #     )
                # elif type_val == 'equ':
                #     logger.info(
                #         f"  type=equ, op={op}, "
                #         f"n_lhs={info.get('n_lhs')}, "
                #         f"value={self.f.formatter.fraction_to_base(info['values'][0])}"
                #     )
                # elif type_val == 'gt':
                #     logger.info(
                #         f"  type=gt, op={op}, "
                #         f"n_lhs={info.get('n_lhs')}, "
                #         f"values=[{self.f.formatter.fraction_to_base(info['values'][0])}, "
                #         f"{self.f.formatter.fraction_to_base(info['values'][1])}], "
                #         f"combo={info.get('combo')}"
                #     )
        
        # 第二步：如果启用 breakdown 且条件满足，对符合条件的 member 进行 breakdown
        # if use_breakdown and i >= 2:  # i_min >= 3
        #     logger.info("-" * 40)
        #     logger.info("Starting breakdown for members with op='='")
        #     logger.info("-" * 40)
            
        #     breakdown_count = 0
        #     for member_idx, member in enumerate(partition.members):
        #         if n in member.get('n_LHS', {}) and member['n_LHS'][n].get('op') == '=':
        #             logger.info(f"Breakdown member [{member_idx+1}]")
        #             self.breakdown_member(member, i, n)
        #             breakdown_count += 1
            
        #     logger.info(f"Breakdown complete: {breakdown_count} members processed")
        # elif use_breakdown and i < 2:
        #     logger.warning(f"Breakdown disabled: i={i} < 2 (i_min must >= 3)")
        
        # logger.info("=" * 40)
        # logger.info("Partition processing complete")
        # logger.info("=" * 40)

    # ==================== 其他函数 ====================


    def get_pf_breakdown(self, p: Partition, member, i, n = 1) -> List:
        """
        为了降低下限，把n_LHS的op为=的项拆分出来，仍然定义 i = i_min - 1
        对于LHS = k * x_{i} 的项，做如下拆解：
        > (k) LHS = k * x_{i}  
        > (k-1) LHS = (k-1) * x_{i} + Sum_{1-2}, Sum_{1-2} = x_{i} > x_{i-1}
        > (k-2) LHS = (k-2) * x_{i} + Sum_{1-2}, Sum_{1-2} = 2x_{i} > 2x_{i-1}
        > ...
        > (0) LHS = 0 * x_{i} + Sum_{1-2}, Sum_{1-2} = k*x_{i} > k*x_{i-1}
        通过这样的方式，可以将等式拆分为多个不等式，从而降低下限

        在partition的满足LHS = k * x_{i}的member中，增加breakdown字段，是一个list，每一项对应上面的一个分解式，
        里面的数据包含 member本身的字段，但数值发生变化：

        1. LHS字段，仍为z3表达式
           breakdown[0][LHS] = LHS - 0 * x_{i}
           ...
           breakdown[k][LHS] = LHS - k * x_{i}
        2. i字段，为partition.i_min-2
        3. relation字段，breakdown[k][relation] = '='， 其他为'>'
        3. expr字段，
            breakdown[j][expr] = (breakdown[j][expr] > or = 0 
            其中 > or = 取决于 breakdown[j][relation]
        4. coeffs字段，
            breakdown[j][coeffs] = {**member['coeffs'], "xi": j}
            解释：
                coeffs(k) = {**member['coeffs'], "xi": k} 
                coeffs(k-1) = {**member['coeffs'], "xi": k-1}
                , ...
                coeffs(0) = {**member['coeffs'], "xi": 0}
        5. n_LHS字段，由于此时x_{i_min}>x_i, 无法对新的分解造成影响，这里设n=1即可
           n_LHS = {}; 例如
           n_LHS[1] = {'values': [lower, upper], 
                        'n_lhs': k-j,
                        'op': '>', 
                        'combo': s(k-j, i-1),
                        'type': 'fixed' # equ or fixed or gt
                    }
            5.1 n_lhs字段，n_lhs = k-j
                LHS - j * x_{i} = (k-j) * x_{i} > (<--此处是op字段) n_lhs * x_{i-1}
                => n_lhs = k-j
            5.2 op字段，op = '>', 但当 j == k 时，op = '='
            5.3 values字段，分成[lower, upper]两项
                j != k时
                    [j][lower] = self.f.get(K = (*K, j), i = i-1)[j]
                    [j][upper] = self.f.get(K = (*K, j), i = i-1)[j-1]
                j == k时
                    [j][lower] = self.f._sigma((*K, k))
                    [j][upper] = self.f._sigma((*K, k))

                解释：
                    其中，K = coeffs. 则
                    > f(k) = sigma(*K, k);
                    > f(k-1) = self.f(K = (*K, k-1), i = i-1)[1]
                    > f(k-2) = self.f(K = (*K, k-2), i = i-1)[2]
                    ...
                    > f(0) = self.f(K = *K, i = i-1)[k]
            5.4 combo字段，
                breakdown[k][combo] = 0
                breakdown[j][combo] = s(k-j, i-1)
            5.5 type字段(这个字段是跨域的，因此下面的i定义为 RHS的最大下标，在此处为 i_min-2)，
                fixed: sum (x_{j>i}) = 0 
                    这个值已经是准确计算的，不需要优化选择
                equ: LHS == k * x_{i} 这个值虽然只有上限，没有准确值，但不参与优化，
                    在breakdown里应该不存在了
                gt: LHS > k * x_{i} 这个值有上下限，需要参与优化选择
        
        前提条件
            i-1>=1 => i>=2 => i_min>=3
        """
        
        # i = p.i_min - 1  # RHS的最大下标
        logger = p.get_logger()
        # 遍历所有 member
        # for member_idx, member in enumerate(p.members):
            # 只处理 relation == '=' 且 n_LHS 存在的 member
            # if member['relation'] != '=' or n not in member.get('n_LHS', {}):
            #     continue
        

        LHS = member['LHS']
        n_lhs_info = member['n_LHS'][n]
        k = n_lhs_info['n_lhs']  # LHS = k * x_i
        op = n_lhs_info['op']
        
        # 只处理 op == '=' 的情况
        if op != '=':
            return
        
        logger.info(f"Breaking down: {LHS} = {k} * x_{i}")
        
        # 创建 breakdown 列表
        breakdown = []
        K = tuple(member['coeffs'].values())  # 原始 coeffs
        
        # 生成 k+1 个分解项：从 j=k 到 j=0
        for j in range(k, -1, -1):
            breakdown_item = {}
            
            # 1. LHS 字段 (z3表达式)
            # breakdown[j]['LHS'] = LHS - j * x_{i}
            # 这里用字符串表示，实际使用时需要转换为 z3 表达式
            breakdown_item['LHS'] = LHS - j * SMTSolver.get_var(f"x{i}")
            
            # 2. i 字段
            breakdown_item['i'] = i - 1  # i_min - 2
            
            # 3. relation 字段
            breakdown_item['relation'] = '=' if j == k else '>'
            
            # 4. expr 字段
            if j == k:
                breakdown_item['expr'] = (breakdown_item['LHS'] == 0)
            else:
                breakdown_item['expr'] = (breakdown_item['LHS'] > 0)
            
            # 5. coeffs 字段
            breakdown_item['coeffs'] = {**member['coeffs'], f"x{i}": j}
            
            # 6. n_LHS 字段
            breakdown_item['n_LHS'] = {}
            n_lhs_value = k - j
            
            # 计算 values
            if j == k:
                # j == k 时，op = '='
                sigma_val = self.f._sigma((*K, k))
                lower = sigma_val
                upper = sigma_val
                op_type = '='
            else:
                # j != k 时，op = '>'
                fracs = self.f.get((*K, j), i - 1)
                lower = fracs[n_lhs_value]
                upper = fracs[n_lhs_value - 1]
                op_type = '>'
            
            # 计算 combo
            if j == k:
                combo = 0
            else:
                combo = self.s(n_lhs_value, i - 1)
            
            # 确定 type
            if j == k:
                type_val = 'fixed'  # 虽然说明中说不应该存在，但按规范实现
            else:
                # 检查是否为 fixed
                # sum_xi_gt_i = sum(member['coeffs'].get(f'x{idx}', 0) for idx in range(i+1, 7))
                # if sum_xi_gt_i == 0:
                #     type_val = 'fixed'
                # else:
                type_val = 'gt'
            
            breakdown_item['n_LHS'][n] = {
                'values': [lower, upper],
                'n_lhs': n_lhs_value,
                'op': op_type,
                'combo': combo,
                'type': type_val
            }
            
            breakdown.append(breakdown_item)
            
            # 日志输出
            # logger.info(
            #     f"  [{j}] LHS - {j}*x{i} {op_type} 0, "
            #     f"coeffs={{...xi:{j}}}, "
            #     f"n_lhs={n_lhs_value}, "
            #     f"combo={combo}, "
            #     f"type={type_val}"
            # )
        
        # 将 breakdown 添加到 member 中
        member['breakdown'] = breakdown
        logger.info(f"Breakdown complete: {len(breakdown)} items")
        # logger.info("-" * 40)


        return

    def get_pf(self, p: Partition, node, i, n = 1) -> List:
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
        # for member in partition.members:
        K = tuple(node['coeffs'].values())
        relation = node['relation']
        
        if relation == '=':
            sigma_val = self.f._sigma(K)
            node['n_LHS'][n].update({
                'values': [sigma_val, sigma_val],
                'combo': 0,
                'type': 'fixed'
            })                
            # results.append(((sigma_val, 'fixed'),))
        else:
            fracs = self.f.get(K, i)
            # n_to_idx = {n: idx for idx, n in enumerate(self.f.n_range)}
            
            n_lhs = node['n_LHS'][n]['n_lhs']
            op = node['n_LHS'][n]['op']
            # if 1 not in n_LHS:
            #     continue
            #  = n_LHS[1]
            
            # if k_val is None:
            #     continue
            
            if op == '>':
                # if n_lhs not in n_to_idx or (n_lhs - 1) not in n_to_idx:
                #     continue
                lower = fracs[n_lhs]
                upper = fracs[n_lhs - 1]
                combo = self.s(n_lhs, i)
                type_val = 'gt'
                node['n_LHS'][n].update({
                    'values': [lower, upper],
                    'combo': combo,
                    'type': type_val
                })                    
                # val1 = (fracs[n_lhs], self.s(n_lhs, i))
                # val2 = (fracs[n_lhs - 1], 0)
                # results.append((val1, val2))
            elif op == '=':
                value = fracs[n_lhs - 2]
                node['n_LHS'][n].update({
                    'values': [value, value],
                    'combo': 0,
                    'type': 'equ'
                })                   
                # if (n_lhs - 2) not in n_to_idx or (n_lhs - 3) not in n_to_idx:
                #     continue
                # idx_n_minus2 = n_to_idx[n_lhs - 2]
                # idx_n_minus3 = n_to_idx[n_lhs - 3]
                # val1 = (fracs[idx_n_minus2], 0)
                # val2 = (fracs[idx_n_minus2], 0)
                # results.append(((fracs[n_lhs - 2], 'equ'),))
        return 

    def new_calc_node(self, p: Partition, n = 1) -> None:
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
                # if 1 not in n_LHS:
                #     continue
                #  = n_LHS[1]
                
                # if k_val is None:
                #     continue
                
                if op == '>':
                    # if n_lhs not in n_to_idx or (n_lhs - 1) not in n_to_idx:
                    #     continue
                    lower = fracs[n_lhs]
                    upper = fracs[n_lhs - 1]
                    combo = self.s(n_lhs, node.i_min - 1)
                    node.n_LHS[n].update({
                        'values': [lower, upper],
                        'combo': combo,
                        'type': 'gt'
                    })                    
                    # val1 = (fracs[n_lhs], self.s(n_lhs, i))
                    # val2 = (fracs[n_lhs - 1], 0)
                    # results.append((val1, val2))
                # 理论上op == '=' 不会出现了，暂时保留代码
                elif op == '=':
                    raise Exception("op == '=' should not appear in new_calc_node")
                    # value = fracs[n_lhs - 2]
                    # node.n_LHS[n].update({
                    #     'values': [value, value],
                    #     'combo': 0,
                    #     'type': 'equ'
                    # })                   
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

        # 遍历所有 member
        # for member_id, member in enumerate(p.breakdowns):
        #     # if n not in member.get('n_LHS', {}):
        #     #     continue
            
        #     n_lhs_info = member['n_LHS'][n]
        #     type_val = n_lhs_info['type']
            
        #     if type_val == 'fixed':
        #         # 情况1: fixed 类型
        #         value = n_lhs_info['values'][0]
        #         fixed_terms.append(value)
        #         # logger.info(f" [{member_id+1}] {self.f.formatter.fraction_to_base(value)} (fixed)")
            
        #     elif type_val == 'gt':
        #         # 情况2: gt 类型
        #         lower, upper = n_lhs_info['values']
        #         combo = n_lhs_info['combo']
                
        #         gt_lower.append(lower)
        #         gt_upper.append(upper)
        #         combo_lower.append(combo)
        #         combo_upper.append(0)
        #         gt_idx.append(member_id)
                
        #         # logger.info(
        #         #     f" [{member_id+1}] [{self.f.formatter.fraction_to_base(lower)}, "
        #         #     f"{self.f.formatter.fraction_to_base(upper)}] s:[{combo}] (gt)"
        #         # )
            
        #     elif type_val == 'equ':
        #         # 情况3: equ 类型
        #         equ_value = n_lhs_info['values'][0]
                
        #         # 检查是否使用 breakdown
        #         use_breakdown = False
        #         if Breakdown and 'breakdown' in member:
        #             # 计算 breakdown 各项之和
        #             breakdown_sum = Fraction(0)
        #             for bd_item in member['breakdown']:
        #                 # if n in bd_item.get('n_LHS', {}):
        #                 breakdown_sum += bd_item['n_LHS'][n]['values'][0]
                    
        #             # 比较 equ 值与 breakdown 之和
        #             if breakdown_sum < equ_value:
        #                 use_breakdown = True
        #                 logger.info(
        #                     f" [{member_id+1}] Using breakdown "
        #                     f"(breakdown={self.f.formatter.fraction_to_base(breakdown_sum)} "
        #                     f"< equ={self.f.formatter.fraction_to_base(equ_value)})"
        #                 )
        #             else:
        #                 logger.info(
        #                     f" [{member_id+1}] Using equ value "
        #                     f"(breakdown={self.f.formatter.fraction_to_base(breakdown_sum)} "
        #                     f">= equ={self.f.formatter.fraction_to_base(equ_value)})" 
        #                 )
                
        #         if use_breakdown:
        #             # 使用 breakdown，分别处理其中的 fixed 和 gt 项
        #             for bd_id, bd_item in enumerate(member['breakdown']):
        #                 # if n not in bd_item.get('n_LHS', {}):
        #                 #     continue
                        
        #                 bd_n_lhs = bd_item['n_LHS'][n]
        #                 bd_type = bd_n_lhs['type']
                        
        #                 if bd_type == 'fixed':
        #                     bd_value = bd_n_lhs['values'][0]
        #                     fixed_terms.append(bd_value)
        #                     # logger.info(
        #                     #     f"   [{member_id+1}.{bd_id}] "
        #                     #     f"{self.f.formatter.fraction_to_base(bd_value)} (bd:fixed)"
        #                     # )
                        
        #                 elif bd_type == 'gt':
        #                     bd_lower, bd_upper = bd_n_lhs['values']
        #                     bd_combo = bd_n_lhs['combo']
                            
        #                     gt_lower.append(bd_lower)
        #                     gt_upper.append(bd_upper)
        #                     combo_lower.append(bd_combo)
        #                     combo_upper.append(0)
        #                     gt_idx.append((member_id, bd_id))  # tuple 索引
                            
        #                     # logger.info(
        #                     #     f"   [{member_id+1}.{bd_id}] "
        #                     #     f"[{self.f.formatter.fraction_to_base(bd_lower)}, "
        #                     #     f"{self.f.formatter.fraction_to_base(bd_upper)}] "
        #                     #     f"s:[{bd_combo}] (bd:gt)"
        #                     # )
        #         else:
        #             # 不使用 breakdown，直接使用 equ 值
        #             equ_terms.append(equ_value)
                    # logger.info(
                    #     f" [{member_id+1}] {self.f.formatter.fraction_to_base(equ_value)} (equ)"
                    # )
        
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

    def optimize(self, p: Partition, n = 1, method = 'pulp', Breakdown: bool = True) -> Dict:
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
        
        # 遍历所有 member
        for member_id, member in enumerate(p.breakdowns):
            # if n not in member.get('n_LHS', {}):
            #     continue
            
            n_lhs_info = member['n_LHS'][n]
            type_val = n_lhs_info['type']
            
            if type_val == 'fixed':
                # 情况1: fixed 类型
                value = n_lhs_info['values'][0]
                fixed_terms.append(value)
                # logger.info(f" [{member_id+1}] {self.f.formatter.fraction_to_base(value)} (fixed)")
            
            elif type_val == 'gt':
                # 情况2: gt 类型
                lower, upper = n_lhs_info['values']
                combo = n_lhs_info['combo']
                
                gt_lower.append(lower)
                gt_upper.append(upper)
                combo_lower.append(combo)
                combo_upper.append(0)
                gt_idx.append(member_id)
                
                # logger.info(
                #     f" [{member_id+1}] [{self.f.formatter.fraction_to_base(lower)}, "
                #     f"{self.f.formatter.fraction_to_base(upper)}] s:[{combo}] (gt)"
                # )
            
            elif type_val == 'equ':
                # 情况3: equ 类型
                equ_value = n_lhs_info['values'][0]
                
                # 检查是否使用 breakdown
                use_breakdown = False
                if Breakdown and 'breakdown' in member:
                    # 计算 breakdown 各项之和
                    breakdown_sum = Fraction(0)
                    for bd_item in member['breakdown']:
                        # if n in bd_item.get('n_LHS', {}):
                        breakdown_sum += bd_item['n_LHS'][n]['values'][0]
                    
                    # 比较 equ 值与 breakdown 之和
                    if breakdown_sum < equ_value:
                        use_breakdown = True
                        logger.info(
                            f" [{member_id+1}] Using breakdown "
                            f"(breakdown={self.f.formatter.fraction_to_base(breakdown_sum)} "
                            f"< equ={self.f.formatter.fraction_to_base(equ_value)})"
                        )
                    else:
                        logger.info(
                            f" [{member_id+1}] Using equ value "
                            f"(breakdown={self.f.formatter.fraction_to_base(breakdown_sum)} "
                            f">= equ={self.f.formatter.fraction_to_base(equ_value)})" 
                        )
                
                if use_breakdown:
                    # 使用 breakdown，分别处理其中的 fixed 和 gt 项
                    for bd_id, bd_item in enumerate(member['breakdown']):
                        # if n not in bd_item.get('n_LHS', {}):
                        #     continue
                        
                        bd_n_lhs = bd_item['n_LHS'][n]
                        bd_type = bd_n_lhs['type']
                        
                        if bd_type == 'fixed':
                            bd_value = bd_n_lhs['values'][0]
                            fixed_terms.append(bd_value)
                            # logger.info(
                            #     f"   [{member_id+1}.{bd_id}] "
                            #     f"{self.f.formatter.fraction_to_base(bd_value)} (bd:fixed)"
                            # )
                        
                        elif bd_type == 'gt':
                            bd_lower, bd_upper = bd_n_lhs['values']
                            bd_combo = bd_n_lhs['combo']
                            
                            gt_lower.append(bd_lower)
                            gt_upper.append(bd_upper)
                            combo_lower.append(bd_combo)
                            combo_upper.append(0)
                            gt_idx.append((member_id, bd_id))  # tuple 索引
                            
                            # logger.info(
                            #     f"   [{member_id+1}.{bd_id}] "
                            #     f"[{self.f.formatter.fraction_to_base(bd_lower)}, "
                            #     f"{self.f.formatter.fraction_to_base(bd_upper)}] "
                            #     f"s:[{bd_combo}] (bd:gt)"
                            # )
                else:
                    # 不使用 breakdown，直接使用 equ 值
                    equ_terms.append(equ_value)
                    # logger.info(
                    #     f" [{member_id+1}] {self.f.formatter.fraction_to_base(equ_value)} (equ)"
                    # )
        
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
        logger.info(f" Scaling factor: {scale}")
        logger.info(f" lower: {gt_lower_int}, lower_combo: {combo_lower}")
        logger.info(f" upper: {gt_upper_int}, upper_combo: {combo_upper}")        
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
                # logger.debug(
                #     f"  Found better solution: "
                #     f"combo={combo}, "
                #     f"selection={selection}, "
                #     f"obj={obj_value}, "
                #     f"constraint={constraint_value}"
                # )
    
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
    # texts = [
    #     [["x6 = 2*x5", "x5 = 2*x4"], 4],
    #     [["x6 = 2*x5", "x5 = x4 + x3"], 4],
    #     [["x6 = 2*x5"], 5],
    #     [["x6 = x2 + x3"], 3],
    #     [["x6 = 2x3"], 3],
    # ]
    
    # from smt_tools import SMTAnalyzer
    # from pprint import pprint

    # txts = texts[1][0]  
    # an = SMTAnalyzer()
    # an.add_constraints_from_text(txts)
    # results, i_min = an.enumerate_decompositions()
    # partitions = an.classify_decompositions(results, i_min)
    # partition = partitions[1]
    
    # opt = Optimizer()
    # analysis_results = opt.analyze_partition(partition)
    # print(analysis_results)
    
    # print("Analysis Results:")
    # for i, (mem, res) in enumerate(zip(partition.members, analysis_results)):
    #     print(f"Member {i}:")
    #     pprint(mem)
    #     print("-------")
    #     pprint(res)
    #     print("=======")
    
    # # 测试优化选择
    # print("\n" + "="*50)
    # print("Optimization Selection:")
    # opt_result = opt.optimize_selection(analysis_results)
    # pprint(opt_result)