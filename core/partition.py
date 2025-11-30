"""
Partition 模块：基于 BreakdownTree 的新分区结构

核心变化：
- 旧版：基于 Dict 列表 (breakdowns)
- 新版：基于 BreakdownNode 列表 (nodes)

主要类：
- Partition: 表示一个分区（包含 solver 和 nodes）
"""

import logging
import json
from typing import List, Dict, Optional, Any
from itertools import combinations_with_replacement
from z3 import BoolRef, ArithRef, And, Not, sat, unsat, simplify

from .smt import SMTSolver
from .breakdown import BreakdownNode
from .logger import get_logger, get_sp_logger


class PartitionError(Exception):
    """Partition 相关的异常基类"""
    pass


class Partition:
    """
    分区对象（新版：基于 BreakdownNode）
    
    属性:
        solver: SMTSolver，该分区的 solver
        nodes: List[BreakdownNode]，该分区包含的节点列表
        constraints: List[BoolRef]，该分区的约束条件（从第一个节点提取）
        i_min: int，该分区的 i_min（从第一个节点提取）
        id: Optional[str]，分区标识符
    
    与旧版的对应关系:
        旧版 self.breakdowns (List[Dict]) → 新版 self.nodes (List[BreakdownNode])
        旧版 self.expr (BoolRef) → 新版 self.constraints (List[BoolRef])
        旧版 member['LHS'] → 新版 node.LHS
        旧版 member['n_LHS'] → 新版 node.n_LHS
        旧版 member['breakdown'] → 新版 node.children
    """
    
    def __init__(
        self,
        solver: SMTSolver,
        nodes: List[BreakdownNode],
        constraints: List[BoolRef],
        id: Optional[str] = None
    ):
        """
        初始化分区。
        
        参数:
            solver: 该分区的 solver
            nodes: 该分区包含的节点列表
            id: 可选的标识符
        """
        self.solver = solver
        self.nodes = nodes
        # constraints: 主要在log上比较重要
        self.constraints = constraints
        # self.i_min = max([node.i_min for node in nodes])
        # self.id = id
        
        # 从第一个节点提取共同属性
        # if nodes:
        #     self.constraints = nodes[0].constraints
        #     self.i_min = nodes[0].i_min
        # else:
        #     self.constraints = []
        #     self.i_min = None
        
        # 初始化 logger
        self._logger = None
        if id:
            self.set_id(id)
        
        # 排序节点
        self.order()
    
    def set_id(self, id: str) -> None:
        """设置 partition ID 并创建专用日志"""
        self.id = id
        try:
            self._logger = get_sp_logger(id, "partition")
        except ValueError:
            self._logger = get_logger()
    
    def get_logger(self) -> logging.Logger:
        """获取 partition 的 logger"""
        if self._logger is None:
            self._logger = get_logger()
        return self._logger
    
    def order(self) -> None:
        """
        按节点的系数字典对 nodes 就地排序。
        
        排序规则：按 coeffs 字典中 x5, x4, ..., x_{i_min} 的值从大到小排序
        """
        # if not self.nodes or self.i_min is None:
        #     return
        
        def get_sort_key(node: BreakdownNode):
            # 提取 coeffs 中从 x5 到 x_{i_min} 的系数（降序）
            return tuple(
                node.coeffs.get(f"x{i}", 0) 
                for i in range(5, 0, -1)
            )
        
        self.nodes.sort(key=get_sort_key, reverse=True)
    
    def log_assertions(self) -> None:
        """记录 solver 的断言到日志"""
        logger = self.get_logger()
        logger.info("=" * 40)
        logger.info(f"Partition {self.id} Solver Assertions:")
        # logger.info("=" * 40)
        for idx, a in enumerate(self.solver.solver.assertions(), 1):
            logger.info(f"  [{idx}] {a}")
        logger.info("=" * 40)
    
    def log_nodes(self) -> None:
        """记录所有节点到日志"""
        logger = self.get_logger()
        logger.info("=" * 40)
        logger.info(f"Partition {self.id} Nodes ({len(self.nodes)} total):")
        # logger.info("=" * 40)
        for idx, node in enumerate(self.nodes, 1):
            # logger.info(f"  [{idx}] {node.relation}: {simplify(node.expr)}")
            logger.info(f"  [{idx}] {node}")
        logger.info("=" * 40)
    
    def log_LHS(self, n: int = 1, DEBUG: bool = True) -> None:
        """
        打印该 Partition 的每个节点的 LHS 和对应的 n_LHS 分析结果。
        
        参数:
            n: n 值（用于 n_LHS）
            Breakdown: 是否打印子节点（children）的信息
            DEBUG: 是否打印详细的 n_LHS 信息
        """
        logger = self.get_logger()
        
        # if self.i_min is None:
        #     logger.warning("Partition has no i_min, cannot log LHS")
        #     return
        
        logger.info(f"Partition {self.id} :")
        
        for i, node in enumerate(self.nodes, 1):
            LHS = node.LHS
            
            # 检查 n_LHS 是否存在
            # if n not in node.n_LHS:
            #     logger.warning(f"  [{i}] : Node missing n_LHS[{n}], skipping")
            #     continue
            
            n_LHS_info = node.n_LHS[n]
            n_lhs_val = n_LHS_info['n_lhs']
            op = n_LHS_info['op']
            if node.relation == "=":
                logger.info(f"  [{i}] : {simplify(LHS)} = 0, "
                            f"when []"
                           )
            else:
                logger.info(f"  [{i}] : {simplify(LHS)} {op} {n_lhs_val}*x_{node.i_min - 1}, "
                            f"when [n = {n},  x_{node.i_min} > {n}*x_{node.i_min - 1}, x_{node.i_min} != {n+1}*x_{{1-{node.i_min - 1}}}]"
                       )
            
            if DEBUG:
                logger.info(f"      {n_LHS_info}")
            
            # 打印子节点（breakdown）
            # if Breakdown and node.children:
            #     for bd_idx, child in enumerate(node.children, 1):
            #         child_LHS = child.LHS
            #         child_i = child.i_min
                    
            #         if n not in child.n_LHS:
            #             logger.warning(f"    > [{bd_idx}] : Child missing n_LHS[{n}]")
            #             continue
                    
            #         child_n_LHS_info = child.n_LHS[n]
            #         child_n_lhs = child_n_LHS_info['n_lhs']
            #         child_op = child_n_LHS_info['op']
                    
            #         logger.info(f"    > [{bd_idx}] : {simplify(child_LHS)} "
            #                    f"{child_op} {child_n_lhs} * x_{child_i}")
                    
            #         if DEBUG:
            #             logger.info(f"      {child_n_LHS_info}")
        
        logger.info("-" * 40)
    
    def calc_n_LHS(self, n: int = 1) -> None:
        """
        在 x_i > n * x_{i-1} 条件下，计算满足 LHS >= k * x_{i-1} 的最大 k。
        并写入 node.n_LHS[n] = {"n_lhs": k, "op": op}
        
        参数:
            n: n 值
        """
        logger = self.get_logger()
        
        # if self.i_min is None:
        #     logger.error("Partition has no i_min, cannot calculate n_LHS")
        #     return
        
        # 对 n > 1，先检查 x_i > n * x_{i-1} 的可满足性
        if n > 1:
            for node in self.nodes:
                if not self.solver.exam_n_LHS(node.i_min, n):
                    raise PartitionError(
                        f"Condition x_{node.i_min} > {n} * x_{node.i_min - 1} is not satisfiable"
                    )
        
        # 对每个节点计算 n_LHS
        for node in self.nodes:
            # 初始化 n_LHS 字典
            if not hasattr(node, 'n_LHS') or node.n_LHS is None:
                node.n_LHS = {}
            
            # 计算 n_LHS
            if node.relation == "=":
                n_lhs, op = 0, "="
            else:
                n_lhs, op = self.solver.calc_n_LHS(node.LHS, node.i_min, n)
            
            node.n_LHS[n] = {"n_lhs": n_lhs, "op": op}
            
            logger.debug(f"Node LHS={simplify(node.LHS)}: n_LHS[{n}] = ({n_lhs}, {op})")
        logger.debug("-" * 40)
    
    def new_gen_constraints(
        self,
        node_indices: List[int | tuple],
        n: int = 1
    ) -> List[BoolRef]:
        """
        对给定的节点索引列表和 n，生成所有可能的约束。
        
        算法：
        1. node_indices 中可能包含两种类型：
           - int: 表示 self.nodes[int] 的节点
           - tuple(node_id, child_id): 表示 self.nodes[node_id].children[child_id]
        
        2. 对于普通节点 (int 类型)：
           - 读取 node.LHS 和 node.n_LHS[n]
           - var_list = [x1, ..., x_{i_min-1}]
           - 生成组合并构建约束 LHS == sum(组合)
        
        3. 对于子节点 (tuple 类型)：
           - 读取 child.LHS, child.i_min, child.n_LHS[n]
           - var_list = [x1, ..., x_{child.i_min}]
           - 生成组合并构建约束 LHS == sum(组合)
        
        4. 如果 n > 1，追加约束：x_i <= n*x_{i-1} AND Not(所有约束)
        
        参数:
            node_indices: 索引列表，元素可以是 int 或 tuple(node_id, child_id)
            n: 用于读取 n_LHS[n] 的 n 值
        
        返回:
            List[BoolRef]: 所有生成的约束列表
        """
        all_constraints = []
        logger = self.get_logger()
        
        # if self.i_min is None:
        #     logger.error("Partition has no i_min, cannot generate constraints")
        #     return []
        
        
        for idx in node_indices:
            # if isinstance(idx, int):
                # 情况1：普通节点
            if idx >= len(self.nodes):
                logger.warning(f"Invalid node index {idx}, skipping")
                continue
            
            node = self.nodes[idx]
            LHS = node.LHS
            
            # if n not in node.n_LHS:
            #     logger.warning(f"Node [{idx}] missing n_LHS[{n}], skipping")
            #     continue
            
            n_lhs_info = node.n_LHS[n]
            k_val = n_lhs_info["n_lhs"]
            
            # var_list = [x1, ..., x_{i_min-1}]
            var_list = [
                self.solver.vars[f"x{i}"] 
                for i in range(1, node.i_min)
            ]
            
            # logger.debug(f"Processing node [{idx}]: k_val={k_val}, "
            #             f"var_list=x1..x{node.i_min-1}")
            
            # elif isinstance(idx, tuple):
            #     # 情况2：子节点
            #     node_id, child_id = idx
                
            #     if node_id >= len(self.nodes):
            #         logger.warning(f"Invalid node_id {node_id}, skipping")
            #         continue
                
            #     node = self.nodes[node_id]
                
            #     if child_id >= len(node.children):
            #         logger.warning(f"Invalid child_id {child_id} for node [{node_id}], skipping")
            #         continue
                
            #     child = node.children[child_id]
            #     LHS = child.LHS
            #     child_i_min = child.i_min
                
            #     if n not in child.n_LHS:
            #         logger.warning(f"Child [{node_id}.{child_id}] missing n_LHS[{n}], skipping")
            #         continue
                
            #     n_lhs_info = child.n_LHS[n]
            #     k_val = n_lhs_info["n_lhs"]
                
            #     # var_list = [x1, ..., x_{child_i_min}]
            #     var_list = [
            #         self.solver.vars[f"x{i}"] 
            #         for i in range(1, child_i_min + 1)
            #     ]
                
            #     logger.debug(f"Processing child [{node_id}.{child_id}]: k_val={k_val}, "
            #                f"var_list=x1..x{child_i_min}")
            
            # else:
            #     logger.warning(f"Unknown index type: {type(idx)}, skipping")
            #     continue
            
            # 生成所有长度为 k_val+1 的组合
            if k_val >= 0:
                for combo in combinations_with_replacement(var_list, k_val + 1):
                    # 计算 sum(combo)
                    sum_expr = simplify(sum(combo) if combo else 0)
                    
                    # 生成约束 LHS == sum_expr
                    constraint = (LHS == sum_expr)
                    all_constraints.append(constraint)
            else:
                logger.warning(f"Invalid k_val={k_val} for index {idx}, skipping")
        
        # 如果 n > 1，追加额外约束
        # if n > 1 and xi is not None and xi_prev is not None:
        #     extra_constraint = And(
        #         xi <= n * xi_prev,
        #         *[Not(c) for c in all_constraints]
        #     )
        #     all_constraints.append(extra_constraint)
        #     logger.debug(f"Added extra constraint for n={n}")
        
        logger.info(f"Partition {self.id}: Generated {len(all_constraints)} constraints.")
        for c in all_constraints:
            logger.debug(f"  constraint: {simplify(c)}")
        logger.info("-" * 40)
        
        return all_constraints
    

    def gen_constraints(
        self,
        node_indices: List[int | tuple],
        n: int = 1
    ) -> List[BoolRef]:
        """
        对给定的节点索引列表和 n，生成所有可能的约束。
        
        算法：
        1. node_indices 中可能包含两种类型：
           - int: 表示 self.nodes[int] 的节点
           - tuple(node_id, child_id): 表示 self.nodes[node_id].children[child_id]
        
        2. 对于普通节点 (int 类型)：
           - 读取 node.LHS 和 node.n_LHS[n]
           - var_list = [x1, ..., x_{i_min-1}]
           - 生成组合并构建约束 LHS == sum(组合)
        
        3. 对于子节点 (tuple 类型)：
           - 读取 child.LHS, child.i_min, child.n_LHS[n]
           - var_list = [x1, ..., x_{child.i_min}]
           - 生成组合并构建约束 LHS == sum(组合)
        
        4. 如果 n > 1，追加约束：x_i <= n*x_{i-1} AND Not(所有约束)
        
        参数:
            node_indices: 索引列表，元素可以是 int 或 tuple(node_id, child_id)
            n: 用于读取 n_LHS[n] 的 n 值
        
        返回:
            List[BoolRef]: 所有生成的约束列表
        """
        all_constraints = []
        logger = self.get_logger()
        
        if self.i_min is None:
            logger.error("Partition has no i_min, cannot generate constraints")
            return []
        
        xi = self.solver.vars.get(f"x{self.i_min}")
        xi_prev = self.solver.vars.get(f"x{self.i_min - 1}")
        
        for idx in node_indices:
            if isinstance(idx, int):
                # 情况1：普通节点
                if idx >= len(self.nodes):
                    logger.warning(f"Invalid node index {idx}, skipping")
                    continue
                
                node = self.nodes[idx]
                LHS = node.LHS
                
                if n not in node.n_LHS:
                    logger.warning(f"Node [{idx}] missing n_LHS[{n}], skipping")
                    continue
                
                n_lhs_info = node.n_LHS[n]
                k_val = n_lhs_info["n_lhs"]
                
                # var_list = [x1, ..., x_{i_min-1}]
                var_list = [
                    self.solver.vars[f"x{i}"] 
                    for i in range(1, self.i_min)
                ]
                
                logger.debug(f"Processing node [{idx}]: k_val={k_val}, "
                           f"var_list=x1..x{self.i_min-1}")
            
            elif isinstance(idx, tuple):
                # 情况2：子节点
                node_id, child_id = idx
                
                if node_id >= len(self.nodes):
                    logger.warning(f"Invalid node_id {node_id}, skipping")
                    continue
                
                node = self.nodes[node_id]
                
                if child_id >= len(node.children):
                    logger.warning(f"Invalid child_id {child_id} for node [{node_id}], skipping")
                    continue
                
                child = node.children[child_id]
                LHS = child.LHS
                child_i_min = child.i_min
                
                if n not in child.n_LHS:
                    logger.warning(f"Child [{node_id}.{child_id}] missing n_LHS[{n}], skipping")
                    continue
                
                n_lhs_info = child.n_LHS[n]
                k_val = n_lhs_info["n_lhs"]
                
                # var_list = [x1, ..., x_{child_i_min}]
                var_list = [
                    self.solver.vars[f"x{i}"] 
                    for i in range(1, child_i_min + 1)
                ]
                
                logger.debug(f"Processing child [{node_id}.{child_id}]: k_val={k_val}, "
                           f"var_list=x1..x{child_i_min}")
            
            else:
                logger.warning(f"Unknown index type: {type(idx)}, skipping")
                continue
            
            # 生成所有长度为 k_val+1 的组合
            if k_val >= 0:
                for combo in combinations_with_replacement(var_list, k_val + 1):
                    # 计算 sum(combo)
                    sum_expr = simplify(sum(combo) if combo else 0)
                    
                    # 生成约束 LHS == sum_expr
                    constraint = (LHS == sum_expr)
                    all_constraints.append(constraint)
            else:
                logger.warning(f"Invalid k_val={k_val} for index {idx}, skipping")
        
        # 如果 n > 1，追加额外约束
        if n > 1 and xi is not None and xi_prev is not None:
            extra_constraint = And(
                xi <= n * xi_prev,
                *[Not(c) for c in all_constraints]
            )
            all_constraints.append(extra_constraint)
            logger.debug(f"Added extra constraint for n={n}")
        
        logger.info(f"Partition {self.id}: Generated {len(all_constraints)} constraints.")
        for c in all_constraints:
            logger.debug(f"  constraint: {simplify(c)}")
        logger.info("-" * 40)
        
        return all_constraints
    
    def filter(self, constraints: List[BoolRef]) -> List[SMTSolver]:
        """
        对给定的约束列表进行过滤和去重，返回满足条件的 Solver 列表。
        
        算法：
        首先判断是否存在某个constraint是否已经蕴含，若蕴含则raise Exception
        1. 对每个 constraint，创建 new_solver = old_solver + constraint
        2. 剪枝条件 1：若 new_solver 不可满足（unsat），则排除
        3. 剪枝条件 2：若 new_solver 与已保留的某个 solver 等价，则排除
        
        参数:
            constraints: z3 BoolRef 约束列表
        
        返回:
            List[SMTSolver]: 过滤后的 Solver 列表（每个都可满足且互不等价）
        """
        logger = self.get_logger()
        logger.info(f"Partition {self.id}: 开始过滤 {len(constraints)} 个约束...")
        
        # 首先判断是否存在某个constraint是否已经蕴含，若蕴含则raise Exception
        for constraint in constraints:
            if self.solver.is_entailed(constraint):
                raise PartitionError(
                    f"Constraint {simplify(constraint)} is already entailed by the base solver."
                )

        filtered_solvers: List[SMTSolver] = []
        
        for idx, constraint in enumerate(constraints, 1):
            # 创建新 solver
            new_solver = SMTSolver(
                base_solver=self.solver,
                constraints=[constraint]
            )
            
            # 剪枝 1：检查可满足性
            if new_solver.solver.check() == unsat:
                logger.debug(f"  [{idx}] Constraint is unsat, skipping, constraint: {constraint}")
                continue
            
            # 剪枝 2：检查是否与已保留的 solver 等价
            is_duplicate = False
            for existing_solver in filtered_solvers:
                if SMTSolver.are_solvers_equivalent(new_solver, existing_solver):
                    is_duplicate = True
                    logger.debug(f"  [{idx}] Found duplicate solver, skipping, constraint: {constraint}")
                    break
            
            if not is_duplicate:
                filtered_solvers.append(new_solver)
                logger.debug(f"  [{idx}] Added solver with constraint {constraint} ")
        
        logger.info(f"Partition {self.id}: {len(filtered_solvers)} unique solvers after filtering, "
                   f"{len(constraints) - len(filtered_solvers)} filtered out.")
        logger.info("-" * 40)
        
        return filtered_solvers
    
    def to_dict(self) -> Dict:
        """
        序列化为字典。
        
        返回:
            Dict: 包含分区信息的字典
        """
        return {
            "id": self.id,
            "solver_id": self.solver.id if self.solver else None,
            "i_min": self.i_min,
            "num_nodes": len(self.nodes),
            "num_constraints": len(self.constraints),
            "constraints": [str(simplify(c)) for c in self.constraints],
            "nodes": [
                {
                    "LHS": str(simplify(node.LHS)),
                    "coeffs": node.coeffs,
                    "relation": node.relation,
                    "entailed": node.entailed,
                    "i_min": node.i_min,
                    "depth": node.depth(),
                    "num_children": len(node.children),
                    "n_LHS": {
                        str(k): v for k, v in node.n_LHS.items()
                    } if hasattr(node, 'n_LHS') and node.n_LHS else {}
                }
                for node in self.nodes
            ]
        }
    
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


# ==================== 工具函数 ====================

# def from_classification(
#     classification_results: List[Dict],
#     id_prefix: str = "p"
# ) -> List[Partition]:
#     """
#     从 new_classify 的结果创建 Partition 列表。
    
#     参数:
#         classification_results: new_classify 返回的结果
#             格式: [{"solver": SMTSolver, "nodes": List[BreakdownNode]}, ...]
#         id_prefix: 分区 ID 前缀
    
#     返回:
#         List[Partition]: 分区列表
#     """
#     partitions = []
    
#     for idx, result in enumerate(classification_results):
#         solver = result["solver"]
#         nodes = result["nodes"]
        
#         partition = Partition(
#             solver=solver,
#             nodes=nodes,
#             id=f"{id_prefix}{idx}"
#         )
#         partitions.append(partition)
    
#     return partitions