import logging
from pprint import pprint
# from typing import Dict, List, Optional, Tuple
# from smt import SMTSolver
# from itertools import combinations_with_replacement
# import jsonpickle
import json
from fractions import Fraction
from typing import Any
from z3 import (
    Reals, Real, Solver, SolverFor, And, Or, Not, sat, unsat, 
    simplify, substitute, is_eq, is_const, ArithRef, BoolRef
)

# 文件开头的导入部分
from typing import List, Dict, Optional
from z3 import BoolRef, Real
from itertools import combinations_with_replacement

from .smt import SMTSolver  # 注意：使用相对导入
from .logger import get_logger, get_sp_logger  # 导入 get_logger 函数
from .hex2 import FractionFormatter  # 导入 Fraction 类

from pprint import pprint

logger = get_logger("partition")
# ff = FractionFormatter()
# ...existing code...

class PartitionError(Exception):
    """Partition 相关的异常基类"""
    pass

class Partition:
    """
    分组对象（非 dataclass，便于后续扩展为大类）：
      - i_min: Optional[int]，来自 find_first_bounded_ratio 的值（若有则填入）
      - entailed: bool，表示该组是否为“无条件成立”的 entailed 组
      - expr: Optional[z3 BoolRef]，该组的代表表达式（非 entailed 组有代表式）
      - substituted_expr: Optional[z3 BoolRef]，该组中某个成员对应的 substituted_expr（用于后续复用）
      - members: List[Dict]，原始条目列表（来自 enumerate_decompositions 的条目）
    """
    def __init__(self, i_min: int,expr: BoolRef, members: List[Dict], solver: SMTSolver = None, id: Optional[str] = None):
        self.i_min = i_min
        self.expr = expr
        self.members = members
        self.solver = solver
        self.order()  # 初始化时对 members 排序
        self.n_sat: Dict[int, bool] = {}
        self.id = id  # 可选的标识符

    def set_id(self, id: str):
        """设置 partition ID 并创建专用日志"""
        self.id = id
        
        # 创建 partition 专用日志
        try:
            self._logger = get_sp_logger(id, "partition")
            # self._logger.info(f"Partition {id} initialized (i_min={self.i_min})")
        except ValueError:
            # 如果还没有设置约束，使用默认 logger
            self._logger = get_logger()
            # self._logger.debug(f"Partition {id} using default logger")
    
    def get_logger(self) -> logging.Logger:
        """获取 partition 的 logger"""
        if not hasattr(self, '_logger') or self._logger is None:
            self._logger = get_logger()
        return self._logger
    
    def order(self) -> None:
        """按 LHS 表达式的字符串形式对 members 就地排序，便于阅读和调试。"""
        self.members.sort(key=lambda item: tuple([item["coeffs"][f"x{i}"] for i in range(5, self.i_min-1, -1)]), 
                              reverse=True)

    def log_assertions(self):
        """记录约束到 partition 专用日志"""
        logger = self.get_logger()
        logger.info("=" * 40)
        logger.info(f"Partition {self.id} Solver Assertions:")
        logger.info("=" * 40)
        for idx, a in enumerate(self.solver.assertions(), 1):
            logger.info(f"  [{idx}] {a}")
        logger.info("=" * 40)
    
    def log_members(self) -> None:
        """记录所有 members 到 partition 专用日志"""     
        logger = self.get_logger()
        logger.info("=" * 40)
        logger.info(f"Partition {self.id} Members ({len(self.members)} total):")
        logger.info("=" * 40)
        for idx, member in enumerate(self.members, 1):
            logger.info(f"  [{idx}] {member.get('relation', '?')}: {member.get('expr', '')}")
        logger.info("=" * 40)
    
    def log_LHS(self, n=1, Breakdown=True, DEBUG=True) -> None:
        """打印该 Partition 的每个 member 的 LHS 和对应的 n_LHS 分析结果。"""
        logger = self.get_logger()
        logger.info(f"Partition {self.id}: When n = {n}, x_{self.i_min} > {n} * x_{self.i_min - 1} :")
        for i, member in enumerate(self.members, 1):
            LHS = member["LHS"]
            n_LHS_info = member['n_LHS'][n]
            n_LHS, op = n_LHS_info['n_lhs'], n_LHS_info['op']
            logger.info(f"  [{i}] : {LHS} {op} {n_LHS} * x_{self.i_min - 1}")
            if DEBUG:
                logger.info(f"      {member['n_LHS'][n]}") 
            if Breakdown and 'breakdown' in member:
                breakdown = member['breakdown']
                for bd_idx, bd in enumerate(breakdown, 1):
                    jLHS, j_i = bd['LHS'], bd['i']
                    j_n_LHS_info = bd['n_LHS'][n]
                    j_n_LHS, j_op = j_n_LHS_info['n_lhs'], j_n_LHS_info['op']
                    logger.info(f"    > [{bd_idx}] : {jLHS} {j_op} {j_n_LHS} * x_{j_i}")
                    if DEBUG:
                        logger.info(f"      {bd['n_LHS'][n]}")

        logger.info("-" * 40)

    def to_dict(self) -> Dict:
        """
        通用序列化：自动处理所有属性，无需预知结构。
        """
        self._seen_ids = set()  # 初始化循环引用追踪
        result = self._serialize(self.__dict__)
        del self._seen_ids  # 清理
        return result
    
    def _serialize(self, obj: Any) -> Any:
        """
        递归序列化任意对象，自动处理：
        - dict → 递归处理每个 value
        - list/tuple → 递归处理每个元素
        - Fraction → 转字符串
        - z3 表达式 → 转字符串
        - SMTSolver → 只取 solver 属性
        - 其他对象 → str()
        """
        # 处理字典
        if isinstance(obj, dict):
            return {k: self._serialize(v) for k, v in obj.items()}
        
        # 处理列表和元组
        elif isinstance(obj, (list, tuple)):
            return [self._serialize(item) for item in obj]
        
        # 处理 Fraction
        elif isinstance(obj, Fraction):
            return f"{obj.numerator}/{obj.denominator}"
        
        # 处理 z3 表达式
        elif hasattr(obj, 'sexpr'):  # z3 特有方法
            return str(obj)
        
        # 特殊处理 SMTSolver：只取 solver 属性
        elif type(obj).__name__ == 'SMTSolver':
            return {
                "__class__": "SMTSolver",
                "id": getattr(obj, 'id', None),
                "solver": str(obj.solver) if hasattr(obj, 'solver') else None
            }
        
        # 处理其他自定义对象
        elif hasattr(obj, '__dict__'):
            # 避免循环引用
            obj_id = id(obj)
            if obj_id in self._seen_ids:
                return f"<circular: {type(obj).__name__}>"
            
            self._seen_ids.add(obj_id)
            
            result = {
                "__class__": type(obj).__name__,
                **self._serialize(obj.__dict__)
            }
            
            self._seen_ids.discard(obj_id)
            return result
        
        # 基础类型（int, str, bool, None）
        elif isinstance(obj, (int, str, bool, type(None))):
            return obj
        
        # 其他类型转字符串
        else:
            return str(obj)
    
    def to_json(self, indent: int = 2) -> str:
        """转换为 JSON 字符串"""
        return json.dumps(self.to_dict(), indent=indent, ensure_ascii=False)
    
    def log_structure(self) -> None:
        """输出结构到日志"""
        logger = self.get_logger()
        logger.info("=" * 60)
        logger.info(f"Partition Structure (ID: {self.id})")
        logger.info("=" * 60)
        
        for line in self.to_json(indent=2).split('\n'):
            logger.info(line)
        
        logger.info("=" * 60)
    
    def save_to_file(self, filename: str) -> None:
        """保存到文件"""
        logger = self.get_logger()
        with open(filename, 'w', encoding='utf-8') as f:
            f.write(self.to_json())
        logger.info(f"Saved to {filename}")

    def calc_n_LHS(self, n: int = 1) -> None:
        """
        在x_i > n * x_{i-1}条件下，计算满足LHS >= k * x_{i-1} 的最大k(不同op分别处理)。
        并写入member["n_LHS"][n] = (k, op)
        """
        # 先确保每个 member 都有 n_LHS 容器
        for member in self.members:
            if "n_LHS" not in member:
                member["n_LHS"] = {}

        # xi = self.vars.get(f"x{self.i_min}")
        # xi_prev = self.vars.get(f"x{self.i_min - 1}")
        # if xi is None or xi_prev is None:
        #     for member in self.members:
        #         for n in range(1, int(self.nmax) + 1):
        #             member["n_LHS"][n] = (None, None)
        #     return

        # for n in range(1, int(self.nmax) + 1):
            # 对 n>1 先检查 x_i > n * x_{i-1} 的可满足性
        if n > 1:
            if not self.solver.exam_n_LHS(self.i_min, n):
                # 对当前 n，检查 x_i > n * x_{i-1} 是否可满足
                raise PartitionError("The method hit a breakpoint and cannot continue.")

        # 若可满足（或 n==1），对每个 member 执行分析
        for member in self.members:
            if member["relation"] == "=":
                n_lhs, op = 0, "="
            else:
                n_lhs, op = self.solver.calc_n_LHS(member["LHS"], self.i_min, n)
            member["n_LHS"][n] = {"n_lhs": n_lhs, "op": op}

    def gen_constraints(self, member_indices: List[int | tuple], n: int = 1) -> List[BoolRef]:
        """
        对给定的 member 索引列表和 n，生成所有可能的约束。
        
        算法：
        1. member_indices 中可能包含两种类型：
           - int: 表示 self.members[int] 的普通 member
           - tuple(member_id, breakdown_id): 表示 self.members[member_id]['breakdown'][breakdown_id]
        
        2. 对于普通 member (int 类型)：
           - 读取 member['LHS'] 和 member['n_LHS'][n]
           - var_list = [x1, ..., x_{i_min-1}]
           - 生成组合并构建约束 LHS == sum(组合)
        
        3. 对于 breakdown 成员 (tuple 类型)：
           - 读取 breakdown['LHS'], breakdown['i'], breakdown['n_LHS'][n]
           - var_list = [x1, ..., x_i]，其中 i = breakdown['i']
           - 生成组合并构建约束 LHS == sum(组合)
        
        4. 如果 n > 1，追加约束：x_i <= n*x_{i-1} AND Not(所有约束)
        
        参数:
            member_indices: 索引列表，元素可以是 int 或 tuple(member_id, breakdown_id)
            n: 用于读取 n_LHS[n] 的 n 值
        
        返回:
            List[BoolRef]: 所有生成的约束列表
        """
        all_constraints = []
        logger = self.get_logger()
        
        xi = self.solver.vars.get(f"x{self.i_min}")
        xi_prev = self.solver.vars.get(f"x{self.i_min - 1}")
        
        for idx in member_indices:
            if isinstance(idx, int):
                # 情况1：普通 member
                member = self.members[idx]
                LHS = member.get("LHS")
                n_lhs_info = member["n_LHS"][n]
                k_val = n_lhs_info["n_lhs"]
                
                # var_list = [x1, ..., x_{i_min-1}]
                var_list = [self.solver.vars[f"x{i}"] for i in range(1, self.i_min)]
                
                # logger.debug(f"Processing member [{idx}]: k_val={k_val}, var_list=x1..x{self.i_min-1}")
            
            elif isinstance(idx, tuple):
                # 情况2：breakdown 成员
                member_id, breakdown_id = idx
                member = self.members[member_id]
                
                # if 'breakdown' not in member:
                #     logger.warning(f"Member [{member_id}] has no breakdown, skipping")
                #     continue
                
                # if breakdown_id >= len(member['breakdown']):
                #     logger.warning(f"Invalid breakdown_id {breakdown_id} for member [{member_id}], skipping")
                #     continue
                
                bd_item = member['breakdown'][breakdown_id]
                LHS = bd_item.get("LHS")
                bd_i = bd_item.get("i")
                n_lhs_info = bd_item["n_LHS"][n]
                k_val = n_lhs_info["n_lhs"]
                
                # var_list = [x1, ..., x_i]，其中 i = breakdown['i']
                var_list = [self.solver.vars[f"x{i}"] for i in range(1, bd_i + 1)]
                
                # logger.debug(f"Processing breakdown [{member_id}.{breakdown_id}]: k_val={k_val}, var_list=x1..x{bd_i}")
            
            # else:
            #     logger.warning(f"Unknown index type: {type(idx)}, skipping")
            #     continue
            
            # 生成所有长度为 k_val+1 的组合
            # if k_val >= 0:
            for combo in combinations_with_replacement(var_list, k_val + 1):
                # 计算 sum(combo)
                sum_expr = simplify(sum(combo) if combo else 0)
                
                # 生成约束 LHS == sum_expr
                constraint = (LHS == sum_expr)
                all_constraints.append(constraint)
            # else:
            #     logger.warning(f"Invalid k_val={k_val} for index {idx}, skipping")
        
        # 如果 n > 1，追加额外约束
        if n > 1 and xi is not None and xi_prev is not None:
            # 约束：x_i <= n*x_{i-1} AND Not(所有已生成的约束)
            extra_constraint = And(
                xi <= n * xi_prev,
                *[Not(c) for c in all_constraints]
            )
            all_constraints.append(extra_constraint)
            logger.debug(f"Added extra constraint for n={n}: {extra_constraint}")
        
        logger.info(f"Partition {self.id}: Generated {len(all_constraints)} constraints.")
        for c in all_constraints:
            logger.info(f"constraint: {c}")
        logger.info("-" * 40)
        
        return all_constraints

    
    def filter(self, constraints: List[BoolRef]) -> List[SMTSolver]:
        """
        对给定的约束列表进行过滤和去重，返回满足条件的 Solver 列表。
        
        算法：
        1. 对每个 constraint，创建 new_solver = old_solver + constraint
        2. 剪枝条件 1：若 new_solver 不可满足（unsat），则排除
        3. 剪枝条件 2：若 new_solver 与已保留的某个 solver 等价，则排除
        
        等价性判断：
        - solver1 与 solver2 等价，当且仅当：
          solver1 ⊨ solver2 的所有断言 且 solver2 ⊨ solver1 的所有断言
        - 即：solver1.assertions ⊨ solver2.assertions 且反之
        
        参数:
            constraints: z3 BoolRef 约束列表
        
        返回:
            List[Solver]: 过滤后的 Solver 列表（每个都可满足且互不等价）
        """
        # if self.solver is None:
        #     raise ValueError("Partition._solver 未初始化")
        
        logger = self.get_logger()
        logger.info(f"Partition {self.id}: 开始过滤和去重 {len(constraints)} 个约束...")
        filtered_solvers: List[Solver] = []
        
        for constraint in constraints:
            # 创建新 solver：复制 old_solver 的断言并添加 constraint
            new_solver = SMTSolver(base_solver=self.solver, constraints=[constraint])
            # try:
            #     new_solver.add(*self.solver.assertions())
            # except Exception:
            #     pass
            # new_solver.add(constraint)
            
            # 剪枝 1：检查可满足性
            if new_solver.solver.check() == unsat:
                logger.info("Solver is unsat, skipping.")
                logger.info(f"constraint: {constraint}")
                # new_solver.log_assertions()
                continue  # 不可满足，跳过
            
            # 剪枝 2：检查是否与已保留的 solver 等价
            is_duplicate = False
            for existing_solver in filtered_solvers:
                if SMTSolver.are_solvers_equivalent(new_solver, existing_solver):
                # if self._are_solvers_equivalent(new_solver, existing_solver):
                    is_duplicate = True
                    logger.info("Found duplicate solver, skipping.")
                    logger.info(f"constraint: {constraint}")
                    # logger.info("New solver assertions:")
                    # new_solver.log_assertions()
                    # logger.info("Existing solver assertions:")
                    # existing_solver.log_assertions()
                    break
            
            if not is_duplicate:
                filtered_solvers.append(new_solver)
        logger.info(f"Partition {self.id}: {len(filtered_solvers)} unique solvers after filtering, "
                    f"{len(constraints)-len(filtered_solvers)} filtered out.")
        logger.info("-" * 40)
        
        return filtered_solvers

