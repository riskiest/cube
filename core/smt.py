"""
SMT Solver 封装类：提供纯 SMT 求解功能，不涉及业务逻辑。

设计原则：
- 只包含通用的 SMT 求解操作（蕴含、可满足性、等价性判断等）
- 不依赖具体的变量定义或业务约束
- 可被 SMTAnalyzer、Partition 等类复用
"""

import logging
from typing import List, Dict, Optional, Any, Tuple, Union
from z3 import (Solver, BoolRef, ArithRef, sat, unsat, unknown, BoolVal,
                And, Not, substitute, simplify, Real, Reals, RealVal)
from copy import deepcopy
from itertools import product
from core.logger import get_sp_logger, get_logger, close_logger_handlers
from core.breakdown import BreakdownNode, BreakdownTree
from .constants import Constants


# 获取模块级 logger
# logger = get_logger("smt")

class SMTError(Exception):
    """SMT 模块的基础异常类（所有 SMT 相关异常的父类）"""
    pass

class Z3UnknownError(SMTError):
    """自定义异常：表示 Z3 返回 unknown 状态"""
    pass

class SMTSolver:
    """
    通用 SMT 求解器封装类。
    
    提供功能：
    1. 蕴含检查（entailment）
    2. 可满足性检查（satisfiability）
    3. 等价性判断（equivalence）
    4. 求解器状态管理（push/pop）
    5. 约束添加与查询
    """
    var_names = [f"x{i}" for i in range(1, Constants.VARIABLE_COUNT + 1)]
    vars: Dict[str, Real] = {name: Real(name) for name in var_names} 

    def __init__(self, base_solver: Optional[Union[Solver, "SMTSolver"]] = None, 
                 constraints: Optional[List[BoolRef]] = None, 
                 text_constraints: Optional[List[str]] = None,
                 id : Optional[str] = None, M : Optional[int] = None):
        """
        初始化 SMT 求解器。
        
        参数:
            base_solver: 可选的 z3.Solver 或 SMTSolver 实例。若为 None，创建新实例。
        """
        if M is None:
            M = Constants.SMT_M
        self.M = M  # 假设的常量 M，用于某些约束  
        self._push_count = 0  # 记录 push 的次数
        if id:
            self.set_id(id)  # 可选的标识符

        # 默认约束
        self.solver = Solver()
        if base_solver is not None:
            self.solver.add(*base_solver.assertions())
        
        if constraints is not None:
            if constraints:
                self.solver.add(*constraints)

        if text_constraints is not None:
            text_constraints = Constants.Constraints.base_constraints + text_constraints
            for text in text_constraints:
                self.solver.add(eval(text, {"__builtins__": {}}, self.vars))
    
    @staticmethod
    def text_to_constraint(text: str) -> BoolRef:
        """
        将单个约束字符串转换为 z3 BoolRef。
        
        参数:
            text: 约束字符串
        
        返回:
            BoolRef: 对应的 z3 约束对象
        """
        return eval(text, {"__builtins__": {}}, SMTSolver.vars)

    @staticmethod
    def constraints_to_id(text_constraints: List[str]) -> str:
        """
        将约束列表转换为可读的 ID（适合作为文件名）。
        
        规则：
        1. 移除空格
        2. == → eq, > → gt, >= → ge, < → lt, <= → le, != → ne
        3. * → m (multiply), + → p (plus), - → s (minus)
        4. 多个约束用 & 连接
        5. 限制总长度（避免文件名过长）
        
        示例：
            ["x6 == 2*x5"] → "x6eq2mx5"
            ["x6 == x5 + x3", "x5 == x3 + x2"] → "x6eqx5px3&x5eqx3px2"
            ["x6 > 2*x5 + 3*x4"] → "x6gt2mx5p3mx4"
        
        参数:
            text_constraints: 约束字符串列表
        
        返回:
            格式化的 ID 字符串
        """
        if not text_constraints:
            return "empty"
        
        formatted_parts = []
        
        for constraint in text_constraints:
            # 移除所有空格
            c = constraint.replace(" ", "")
            
            # 替换运算符
            c = c.replace("==", "eq")
            c = c.replace(">=", "ge")
            c = c.replace("<=", "le")
            c = c.replace("!=", "ne")
            c = c.replace(">", "gt")
            c = c.replace("<", "lt")
            c = c.replace("*", "m")
            c = c.replace("+", "p")
            c = c.replace("-", "s")  # 注意：这会把负号也替换
            
            formatted_parts.append(c)
        
        # 用 & 连接多个约束
        result = "&".join(formatted_parts)
        
        # 限制长度（避免文件名过长）
        max_len = 100
        if len(result) > max_len:
            # 截断并添加哈希值
            import hashlib
            hash_suffix = hashlib.md5(result.encode()).hexdigest()[:8]
            result = result[:max_len-9] + "_" + hash_suffix
        
        return result

    @staticmethod
    def get_var(name: str) -> Real:
        """获取变量对象"""
        return SMTSolver.vars[name]
    
    # ==================== 日志相关 ====================

    def set_id(self, id: str):
        """设置 solver ID 并创建专用日志"""
        self.id = id
        
        # 创建 solver 专用日志
        try:
            # ✅ 获取 solver 专用 logger（自动记录到 3 个地方）
            self._logger = get_sp_logger(id, "solver")
        except ValueError:
            # 如果还没有设置约束，使用默认 logger
            self._logger = get_logger()
    
    def get_logger(self) -> logging.Logger:
        """获取 solver 的 logger"""
        if not hasattr(self, '_logger') or self._logger is None:
            self._logger = get_logger()
        return self._logger
    
    def close_logger(self):
        close_logger_handlers(self.get_logger())

    def __del__(self):
        """析构时自动清理（可选）"""
        try:
            self.close_logger()
        except:
            pass

    def assertions(self) -> List[BoolRef]:
        """返回当前求解器的所有约束列表"""
        return self.solver.assertions()
    
    def log_assertions(self):
        """记录所有约束到 solver 专用日志"""
        logger = self.get_logger()
        logger.info("=" * 40)
        logger.info(f"Solver {self.id} Assertions:")
        logger.info("-" * 40)
        for idx, a in enumerate(self.assertions(), 1):
            logger.info(f"  [{idx}] {a}")
        # logger.info("=" * 40)
    

    
    # ==================== 基础求解操作 ====================
    def is_entailed(self, prop: BoolRef) -> bool:
        """
        判断当前约束是否蕴含 prop（即 C ⊨ prop）。
        
        算法：检查 C ∧ ¬prop 是否不可满足（unsat）
        
        参数:
            prop: 要检查的命题（z3 BoolRef）
        
        返回:
            bool: True 表示蕴含，False 表示不蕴含
        """
        self.solver.push()
        try:
            self.solver.add(Not(prop))
            result = self.solver.check()
            return result == unsat
        finally:
            self.solver.pop()
    
    def is_sat(self, prop: BoolRef) -> bool:
        """
        判断当前约束与 prop 是否可满足（即 C ∧ prop 是否 sat）。
        
        参数:
            prop: 要检查的命题（z3 BoolRef）
        
        返回:
            bool: True 表示可满足，False 表示不可满足
        """
        self.solver.push()
        try:
            self.solver.add(prop)
            result = self.solver.check()
            return result == sat
        finally:
            self.solver.pop()
    
    def check_with_model(self, prop: BoolRef) -> tuple[bool, Optional[Dict]]:
        """
        检查可满足性并返回模型。
        
        参数:
            prop: 要检查的命题
        
        返回:
            (is_sat, model_dict): 
            - is_sat: 是否可满足
            - model_dict: 若可满足，返回模型字典；否则为 None
        """
        self.solver.push()
        try:
            self.solver.add(prop)
            result = self.solver.check()
            if result == sat:
                model = self.solver.model()
                model_dict = {str(d): model[d] for d in model.decls()}
                return True, model_dict
            return False, None
        finally:
            self.solver.pop()
    
    # ==================== 等价性判断 ====================
    
    def are_equiv(self, prop1: BoolRef, prop2: BoolRef) -> bool:
        """
        判断两个命题在当前约束下是否等价（即 C ⊨ (prop1 ⟺ prop2)）。
        
        算法：检查 C ⊨ prop1 ⟹ prop2 且 C ⊨ prop2 ⟹ prop1
        
        参数:
            prop1, prop2: 两个命题
        
        返回:
            bool: True 表示等价，False 表示不等价
        """
        # 方法 1：检查 C ∧ (prop1 != prop2) 是否 unsat
        return self.is_entailed(prop1 == prop2)
    
    @staticmethod
    def are_solvers_equivalent(solver1: SMTSolver, solver2: SMTSolver) -> bool:
        """
        判断两个 Solver 的约束集是否逻辑等价。
        
        算法：
        - 快速路径：比较断言的字符串表示
        - 严格路径：双向蕴含检查
        - 如果任一检查失败，返回 False，认为是不等价的
        
        参数:
            solver1, solver2: 两个 z3.Solver 实例
        
        返回:
            bool: True 表示等价，False 表示不等价
        """

        # try:
        assertions1 = solver1.assertions()
        assertions2 = solver2.assertions()
        
        # 快速检查
        if len(assertions1) == len(assertions2):
            str1 = sorted(str(a) for a in assertions1)
            str2 = sorted(str(a) for a in assertions2)
            if str1 == str2:
                return True
        
        # 严格检查：solver1 ⊨ And(assertions2)
        temp_solver = Solver()
        temp_solver.add(*assertions1)
        temp_solver.add(Not(And(*assertions2)))
        forward = (temp_solver.check() == unsat)
        
        if not forward:
            return False
        
        # 反向检查：solver2 ⊨ And(assertions1)
        temp_solver = Solver()
        temp_solver.add(*assertions2)
        temp_solver.add(Not(And(*assertions1)))
        backward = (temp_solver.check() == unsat)
        
        return backward
        
        # except Exception:
        #     return False
    
    # ==================== 求解器状态管理 ====================
    
    def push(self):
        """保存当前求解器状态（压栈）"""
        self.solver.push()
        self._push_count += 1
    
    def pop(self, num: int = 1):
        """恢复之前的求解器状态（出栈）"""
        for _ in range(num):
            if self._push_count > 0:
                self.solver.pop()
                self._push_count -= 1
    
    def reset(self):
        """重置求解器到初始状态"""
        while self._push_count > 0:
            self.solver.pop()
            self._push_count -= 1
        self.solver.reset()
    
    # ==================== 约束管理 ====================
    
    def add(self, *constraints: BoolRef):
        """添加约束到求解器"""
        for c in constraints:
            self.solver.add(c)
    
    def get_assertions(self) -> List[BoolRef]:
        """获取当前所有约束"""
        return list(self.solver.assertions())
    
    def check(self):
        """
        检查当前约束的可满足性。
        
        返回:
            sat, unsat
        """
        result = self.solver.check()

        if result == unknown:
            raise Z3UnknownError("SMTSolver 检查时返回 unknown 状态")
        return result
    
    # ==================== 辅助功能 ====================
    
    def clone(self) -> 'SMTSolver':
        """
        克隆当前求解器（深拷贝约束）。
        
        返回:
            SMTSolver: 新的求解器实例，包含相同的约束
        """
        new_solver = Solver()
        try:
            new_solver.add(*self.solver.assertions())
        except Exception:
            pass
        return SMTSolver(base_solver=new_solver)
    
    def to_string(self, simplify_expr: bool = True) -> List[str]:
        """
        将当前约束转换为可读字符串列表。
        
        参数:
            simplify_expr: 是否先简化表达式
        
        返回:
            List[str]: 约束的字符串表示
        """
        assertions = self.solver.assertions()
        if simplify_expr:
            return [str(simplify(a)) for a in assertions]
        return [str(a) for a in assertions]
    
    # ==================== 高级功能 ====================
    
    def find_conflicting_core(self, assumptions: List[BoolRef]) -> Optional[List[BoolRef]]:
        """
        查找不可满足核心（unsat core）。
        
        参数:
            assumptions: 假设列表
        
        返回:
            Optional[List[BoolRef]]: 不可满足核心，若可满足则返回 None
        """
        self.solver.push()
        try:
            result = self.solver.check(*assumptions)
            if result == unsat:
                core = self.solver.unsat_core()
                return list(core)
            return None
        finally:
            self.solver.pop()
    
    def optimize_constraints(self, objective: ArithRef, maximize: bool = True) -> Optional[Any]:
        """
        优化目标函数（需要 z3.Optimize）。
        
        注意：这是一个占位方法，实际使用需要 z3.Optimize 而非 Solver
        
        参数:
            objective: 目标函数（z3 ArithRef）
            maximize: True 表示最大化，False 表示最小化
        
        返回:
            最优值（若可满足）或 None
        """
        # 此功能需要 z3.Optimize，这里仅作为接口预留
        raise NotImplementedError("优化功能需要使用 z3.Optimize，当前使用 z3.Solver")

    # ==================== breakdown ====================
    def new_decompose(self, recursive: bool) -> BreakdownTree:
        """
        分解 solver，生成 breakdown 树（统一流程）。
        
        参数:
            recursive: 是否递归分解（默认 True）
        
        返回:
            BreakdownTree: breakdown 树对象
            
        注意:
            - 第一层的 i_min 可通过 tree.roots[0].i_min 获取
            - 树的深度自然受限于 i_min 递减（最多 5 层）
        """
        logger = self.get_logger()
        logger.info(f"Solver {self.id} 开始分解 (recursive={recursive})...")
        logger.info('-'*40)
        
        # ✅ 创建虚拟根节点
        root = BreakdownNode.create_root(self.vars["x6"])
        
        # ✅ 统一调用递归分解
        self._break_recursive(root, recursive=recursive)
                
        # ✅ 构造树（以第一层节点为根）
        tree = BreakdownTree(root=root)
        
        tree.print_tree(logger)
        
        return tree

    def _break_recursive(
        self,
        parent: BreakdownNode,
        recursive: bool
    ) -> None:
        """
        递归分解节点（统一逻辑）。
        
        参数:
            parent: 父节点（可能是虚拟根节点）
            recursive: 是否递归分解子节点
        
        注意:
            - 无需 depth 参数，树深度由 i_min 递减自然控制
            - 终止条件：i_min == 1（无法继续分解）
        """
        # current_i_min = parent.i_min
        
        # ✅ 终止条件1：i_min == 1（最小变量）
        # ✅ 终止条件2：relation 为 '=' 时不继续分解
        if parent.i_min == 1 or parent.relation == '=':
            return
        
        # ✅ 调用统一的 _break
        child_nodes = self._break(
            LHS=parent.LHS,
            constraints=parent.constraints,
            upper_limit=parent.i_min
        )
        
        # ✅ 检查是否找到有效分解
        if not child_nodes:
            return
        
        # ✅ 更新子节点的 i_min 并添加到父节点
        for child in child_nodes:
            child.coeffs = {**parent.coeffs, **child.coeffs}
            # child.i_min = i_new
            parent.add_child(child)
        
        # ✅ 递归分解子节点
        if recursive:
            for child in child_nodes:
                self._break_recursive(child, recursive)

    def _break(
        self,
        LHS: ArithRef,
        constraints: List[BoolRef],
        upper_limit: int
    ) -> List[BreakdownNode]:
        """
        统一的分解逻辑（生成 BreakdownNode 列表）。
        
        参数:
            LHS: 左侧表达式
            context_expr: 上下文约束（None 表示无额外约束）
            upper_limit: 搜索上界（从 x_{upper_limit-1} 开始搜索）
        
        返回:
            (nodes, i_min): 
            - nodes: BreakdownNode 列表
            - i_min: 找到的有上界变量索引（若无则返回 None）
        """
        # ✅ 创建临时 solver
        node_solver = SMTSolver(base_solver=self, constraints=constraints)
        
        # 1️⃣ 查找 i_min（第一个有上界的变量）
        i_min = None
        for i in range(upper_limit - 1, 0, -1):
            xi = self.vars[f"x{i}"]
            test = LHS > self.M * xi
            
            # 如果 test 不可满足（无解），说明 LHS/xi 有界，记录 i_min
            if not node_solver.is_sat(test):
                i_min = i
            # 如果 test 满足，说明 LHS/xi 无界，那么LHS/x_{<i}自然也是无界，不再搜索
            else:
                break
        
        if i_min is None:
            return []
        
        # 2️⃣ 计算每个变量的最大 k
        indices = list(range(upper_limit - 1, i_min - 1, -1))
        var_names = [f"x{i}" for i in indices]
        
        max_ks = {}
        for vn in var_names:
            xi_var = self.vars[vn]
            k_max = None
            
            for k in range(0, self.M + 1):
                prop = LHS >= k * xi_var
                if node_solver.is_sat(prop):
                    k_max = k
                else:
                    break
            
            if k_max is None or k_max >= self.M:
                raise SMTError(f"LHS: {LHS} / {vn} < 0, 程序有bug")
            
            max_ks[vn] = k_max
        
        # 3️⃣ 枚举所有组合
        nodes = []
        ranges = [range(0, max_ks[vn] + 1) for vn in var_names]
        
        for ks in product(*ranges):
            coeff_map = {var_names[idx]: int(ks[idx]) for idx in range(len(var_names))}
            
            # 构造 sum_expr
            sum_expr = None
            for vn, k in coeff_map.items():
                if k == 0:
                    continue
                term = self.vars[vn] * k
                sum_expr = term if sum_expr is None else sum_expr + term
            
            if sum_expr is None:
                sum_expr = RealVal(0)
            
            new_LHS = LHS - sum_expr
            
            # 检查 >= 是否可满足
            prop_ge = new_LHS >= 0
            if not self.is_sat(prop_ge):
                # 如果combo的每一项都不小于this_comb的每一项，comb>=this_comb
                # 如果this_comb不满足>=，则comb也不满足
                # 但为了减少程序复杂性，不做比较
                continue

            # 检查 ">" 关系
            prop_gt = new_LHS > 0
            
            if node_solver.is_entailed(prop_gt):
                node = BreakdownNode(
                    LHS=new_LHS,
                    coeffs=coeff_map,
                    relation=">",
                    entailed=True,
                    expr=prop_gt,
                    i_min=i_min, 
                    constraints=deepcopy(constraints)
                )
                nodes.append(node)
            elif node_solver.is_sat(prop_gt):
                node = BreakdownNode(
                    LHS=new_LHS,
                    coeffs=coeff_map,
                    relation=">",
                    entailed=False,
                    expr=prop_gt,
                    i_min=i_min,
                    constraints=deepcopy(constraints) + [prop_gt]
                )
                nodes.append(node)
            
            # 检查 "=" 关系
            prop_eq = new_LHS == 0
            
            if node_solver.is_entailed(prop_eq):
                node = BreakdownNode(
                    LHS=new_LHS,
                    coeffs=coeff_map,
                    relation="=",
                    entailed=True,
                    expr=prop_eq,
                    i_min=i_min,
                    constraints=deepcopy(constraints)
                )
                nodes.append(node)
            elif node_solver.is_sat(prop_eq):
                node = BreakdownNode(
                            LHS=new_LHS,
                            coeffs=coeff_map,
                            relation="=",
                            entailed=False,
                            expr=prop_eq,
                            i_min=i_min,
                            constraints=deepcopy(constraints) + [prop_eq]
                        )
                nodes.append(node)
        
        return nodes


    def new_classify(self, tree: BreakdownTree) -> List[Dict]:
        """
        对 BreakdownTree 进行分类，生成 Partition 列表。
        
        算法步骤：
        1. 将树展平为节点列表 (递归替换：root → children → grandchildren → ...)
        2. 过滤掉无效节点（i_min==1 且 relation=='>'）
        3. 按 constraints 进行分组
        4. constraints=[] 的组（类似 entailed）单独处理
        5. 为每个组生成 solver，去掉不可满足的
        6. 返回 [{solver, nodes}, ...] 列表
        
        参数:
            tree: BreakdownTree 对象
        
        返回:
            List[Dict]: 每项为 {"solver": SMTSolver, "nodes": List[BreakdownNode]}
        """
        logger = self.get_logger()
        # logger.setLevel(logging.DEBUG)
        # logger.info(f"[Step 2] Solver {self.id} 开始分类...")
        
        # ==================== 步骤 1: 树展平为节点列表 ====================
        nodes_list = self._flatten_tree(tree)
        logger.debug(f"[Step 2.1]展平:")
        logger.debug(f" 展平后节点数: {len(nodes_list)}")
        for n in nodes_list:
            logger.debug(f"  {n}")
        logger.debug("-" * 40)

        
        # ==================== 步骤 2: 过滤无效节点 ====================
        # 舍弃 i_min==1 且 relation=='>' 的节点
        valid_nodes = [
            node for node in nodes_list 
            if not (node.i_min == 1 and node.relation == ">")
        ]
        logger.debug(f"[Step 2.2]过滤:")
        logger.debug(f" 过滤后有效节点数: {len(valid_nodes)}")
        for n in valid_nodes:
            logger.debug(f"  {n}")
        logger.debug("-" * 40)
        
        # ==================== 步骤 3: 按 constraints 分组 ====================
        groups = self._group_by_constraints(valid_nodes)
        # logger.debug(f"分组数: {len(groups)}")
        # for idx, group in enumerate(groups):
            # logger.debug(f"组 {idx}: {len(group['nodes'])} 个节点,")
            # logger.debug(f"constraints:")
            # for constraint in group["constraints"]:
            #     logger.debug(f"  constraint: {constraint}")
            # logger.debug("nodes:")
            # for n in group["nodes"]:
            #     logger.debug(f"  {n}")
            # logger.debug("-" * 40)
        
        # ==================== 步骤 4: 处理 constraints=[] 的组 ====================
        groups = self._handle_empty_constraints_group(groups)
        
        # logger.debug(f" 分组数: {len(groups)}")
        # for idx, group in enumerate(groups):
        #     logger.debug(f" 组 [{idx}/{len(groups)}]: {len(group['nodes'])} 个节点")
        #     logger.debug(f"  constraints:")
        #     for constraint in group["constraints"]:
        #         logger.debug(f"  {constraint}")
        #     logger.debug("nodes:")
        #     for n in group["nodes"]:
        #         logger.debug(f"  {n}")
        # logger.debug("-" * 40)
        
        # ==================== 步骤 5: 为每组生成 solver ====================
        partitions = []
        for group in groups:
            # constraints = group["constraints"]
            # nodes = group["nodes"]
            
            # 创建 solver
            group_solver = SMTSolver(
                base_solver=self,
                constraints=group["constraints"]
            )
            
            # 检查可满足性
            # try:
            if group_solver.check() == sat:
                partitions.append({
                    "solver": group_solver,
                    "constraints": group["constraints"],
                    "nodes": group["nodes"]
                })
        logger.debug(f"[Step 2.3]分组: ")
        logger.debug(f" 分组数: {len(partitions)}")
            #         logger.debug(f"  组 {idx}: 可满足, {len(nodes)} 个节点")
            #     else:
            #         logger.debug(f"  组 {idx}: 不可满足, 跳过")
            # except Z3UnknownError:
            #     logger.warning(f"  组 {idx}: solver 返回 unknown, 跳过")
        
        for idx, p in enumerate(partitions, 1):
            logger.debug(f"组 [{idx}/{len(partitions)}]: {len(p['nodes'])} 个节点")
            # logger.debug(f"Partition with constraints:")
            logger.debug(f"constraints:")
            for constraint in p["constraints"]:
                logger.debug(f"  {constraint}")
            logger.debug("nodes:")
            for n in p["nodes"]:
                logger.debug(f"  {n}")

            # for constraint in p['constraints']:
            #     logger.debug(f"  constraint: {constraint}")
            # logger.debug(f"Partition with {len(p['nodes'])} nodes:")
            # for n in p['nodes']:
            #     logger.debug(f"  {n}")
            logger.debug("-" * 40)
        logger.info(f"Solver {self.id} 分类完成: {len(partitions)} 个 Partitions")
        logger.debug("=" * 60)
        return partitions

    def _flatten_tree(self, tree: BreakdownTree) -> List[BreakdownNode]:
        """
        将树展平为节点列表（递归替换父节点为子节点）。
        
        算法：
        1. 初始化队列：[root]
        2. 从队列取出节点：
        - 如果是叶子节点 → 加入结果
        - 如果有子节点 → 将子节点加入队列（不加入当前节点）
        3. 重复直到队列为空
        
        参数:
            tree: BreakdownTree 对象
        
        返回:
            List[BreakdownNode]: 所有叶子和中间节点（但父节点被子节点替换）
        """
        if tree.root is None:
            return []
        
        result = []
        queue = [tree.root]
        
        while queue:
            node = queue.pop(0)
            
            if node.is_leaf():
                # 叶子节点：加入结果
                result.append(node)
            else:
                # 非叶子节点：将子节点加入队列（替换父节点）
                queue.extend(node.children)
        
        return result

    def _group_by_constraints(self, nodes: List[BreakdownNode]) -> List[Dict]:
        """
        按 constraints 分组（使用逻辑等价性判断）。
        
        算法：
        1. 对每个节点，查找是否存在等价的 constraints 组
        2. 等价性判断：And(*constraints1) ⟺ And(*constraints2)
        3. 若找到等价组，加入该组；否则创建新组
        
        参数:
            nodes: 节点列表
        
        返回:
            List[Dict]: 每项为 {"constraints": List[BoolRef], "nodes": List[BreakdownNode]}
        """
        groups = []
        
        for node in nodes:
            
            # 查找等价组
            found_group = None
            for group in groups:
                
                # 判断等价性
                if self._are_constraints_equiv(node.constraints, group["constraints"]):
                    found_group = group
                    break
            
            if found_group:
                # 加入已有组
                found_group["nodes"].append(node)
            else:
                # 创建新组
                groups.append({
                    "constraints": node.constraints,
                    "nodes": [node]
                })
        
        return groups

    def _are_constraints_equiv(self, constraints1: List[BoolRef], constraints2: List[BoolRef]) -> bool:
        """
        判断两个约束列表是否逻辑等价。
        
        算法：
        - 快速路径：长度不同 → 不等价
        - 快速路径：字符串相同 → 等价
        - 严格路径：检查 And(*c1) ⟺ And(*c2)
        
        参数:
            constraints1, constraints2: 约束列表
        
        返回:
            bool: 是否等价
        """
        # 快速路径：长度不同
        # if len(constraints1) != len(constraints2):
        #     return False
        
        # 空约束处理
        if len(constraints1) == 0 or len(constraints2) == 0:
            if len(constraints1) == len(constraints2):
                return True
            else:
                return False
        
        # 快速路径：字符串比较
        # str1 = sorted(str(simplify(c)) for c in constraints1)
        # str2 = sorted(str(simplify(c)) for c in constraints2)
        # if str1 == str2:
        #     return True
        
        # 严格路径：逻辑等价性
        and1 = And(*constraints1) if len(constraints1) > 1 else constraints1[0]
        and2 = And(*constraints2) if len(constraints2) > 1 else constraints2[0]
        
        return self.are_equiv(and1, and2)

    def _handle_empty_constraints_group(self, groups: List[Dict]) -> List[Dict]:
        """
        处理 constraints=[] 的组（类似 entailed）。
        
        算法：
        1. 找到 constraints=[] 的组（entailed 组）
        2. 计算其 expr = And(Not(c1), Not(c2), ...) 其中 c1, c2 是其他组的 constraints
        3. 将 entailed 组的节点添加到所有其他组（深拷贝）
        4. 更新 entailed 组的 constraints 为 [expr]
        5. 将 entailed 组移到列表首位
        
        参数:
            groups: 分组列表
        
        返回:
            List[Dict]: 处理后的分组列表
        """
        # 找到 constraints=[] 的组
        entailed_group = None
        satisfiable_groups = []
        
        for group in groups:
            if len(group["constraints"]) == 0:
                entailed_group = group
            else:
                satisfiable_groups.append(group)
        
        # 如果没有 entailed 组，直接返回
        if entailed_group is None:
            return groups
        
        # 如果有 entailed 组
        if satisfiable_groups:
            # 构造 entailed_expr = And(Not(c1), Not(c2), ...)
            other_exprs = []
            for g in satisfiable_groups:
                other_exprs.extend(g["constraints"])
                # if len(g["constraints"]) == 1:
                #     other_exprs.append(g["constraints"][0])
                # else:
                #     other_exprs.append(And(*g["constraints"]))
            
            # entailed_expr = And(*[Not(e) for e in other_exprs])
            
            # 更新 entailed 组的 constraints
            entailed_group["constraints"] = [Not(e) for e in other_exprs]
            
            # 将 entailed 组的节点添加到所有其他组（深拷贝）
            # entailed_nodes = deepcopy(entailed_group["nodes"])
            for g in satisfiable_groups:
                g["nodes"].extend(deepcopy(entailed_group["nodes"]))
        # else:
            # 如果没有其他组，entailed_expr = True
            # entailed_group["constraints"] = []
        
        # 将 entailed 组移到首位
        result = [entailed_group] + satisfiable_groups
        return result


    def calc_n_LHS(self, LHS: ArithRef, i_min: int, n: int) -> Tuple[int, str]:
        '''
        计算solver 一定蕴含着 LHS > n * x_{i-1} 与 LHS == n * x_{i-1} 的关系
        1. LHS > n * x_{i-1} 与 LHS == n * x_{i-1} 的蕴含关系可能同时成立
        实际上，如果约束集蕴含着 LHS == n * x_{i-1} 成立，那么蕴含 LHS > (n-1) * x_{i-1} 也成立
        2. 为了减少推理，首先在输入上排除了 LHS == 0 的情况， 因此 LHS > 0 * x_{i-1}
        假设LHS > n * x_{i-1}被蕴含，而 LHS > (n+1) * x_{i-1} 不被蕴含，
        则必有解在 (n+1) * x_{i-1} >= LHS > n * x_{i-1} 之间;
        因此若同时存在 LHS == k * x_{i-1}，必然有 k == n+1; 
        3. 程序我们先检查 LHS > k * x_{i-1} 的蕴含情况，若有k蕴含，k+1不蕴含，则记下 (k, '>');
        但如果直到上限 M， 都有LHS > M * x_{i-1}被蕴含，此时我们无法进行后续的计算，
        这时会返回错误信息，方便后面处理
        4. 如果找到这样的 k，我们再检查 LHS == (k+1) * x_{i-1} 是否被蕴含，
        '''

        xi = self.vars[f"x{i_min}"]
        xi_prev = self.vars[f"x{i_min - 1}"]
        # results = []

       # 1) 查找被蕴含的最大 k 使得 LHS > k * xi_prev
        last_k: int = 0
        for k in range(1, self.M + 1):
            self.solver.push()
            try:
                self.solver.add(xi > n * xi_prev)
                self.solver.add(Not(LHS > k * xi_prev))
                res = self.solver.check()
        
                if res == unsat:
                    # 说明 LHS > k * xi_prev 被蕴含
                    last_k = k
                else:
                    break
            finally:
                self.solver.pop()
               
        if last_k == self.M:
            # print("LHS:", LHS)
            raise SMTError(f"LHS > {self.M} * x{i_min - 1} 被蕴含，无法继续计算 n_LHS")
        # results.append((last_k, '>'))

        # 2) 优先检查是否存在被蕴含的等式 LHS == k * xi_prev
        self.solver.push()
        try:
            self.solver.add(xi > n * xi_prev)
            self.solver.add(Not(LHS == (last_k+1) * xi_prev))
            res = self.solver.check()
            if res == unsat:
                # 说明 LHS == (last_k+1) * xi_prev 被蕴含
                # 优先返回等式
                return last_k+1, '='
        finally:
            self.solver.pop()
       
        return last_k, '>'

    def exam_n_LHS(self, i_min: int, n: int) -> bool:
        """
        检查 x_{i_min} > n * x_{i_min - 1} 是否可满足
        """
        xi = self.vars[f"x{i_min}"]
        xi_prev = self.vars[f"x{i_min - 1}"]

        try:
            self.solver.push()
            self.solver.add(xi > n * xi_prev)
            return (self.solver.check() == sat)
        finally:
            self.solver.pop()
           
    def recursive_classify(self, breakdown_incompleteness: bool, max_depth: int) -> Tuple[List[Dict], int]:
        """
        递归分解和分类，直到所有节点的 constraints 都为空。
        
        算法流程：
        1. 初始化：对当前 solver 进行 new_decompose 生成树
        2. 对树进行 new_classify 得到分类结果
        3. 对每个分类结果：
        - 如果该组的所有节点 constraints 都为空 → 加入最终结果
        - 否则，对该组的 solver 递归调用 recursive_classify
        4. 返回所有 constraints 为空的分类结果
        
        参数:
            max_depth: 最大递归深度（防止无限递归）
        
        返回:
            List[Dict]: 每项为 {"solver": SMTSolver, "nodes": List[BreakdownNode]}
                    所有节点的 constraints 都为空
        """
        logger = self.get_logger()
        recursive = "递归" if not breakdown_incompleteness else "非递归"
        logger.info("=" * 60)
        logger.info(f"Solver {self.id} 开始{recursive}分类 (max_depth={max_depth})...")
        # logger.info("=" * 60)
        
        # 调用递归辅助函数
        results, total_generated = self._recursive_classify_helper(breakdown_incompleteness, depth=0, max_depth=max_depth)
        
        logger.info("=" * 60)
        logger.info(f"Solver {self.id} {recursive}分类完成:")
        logger.info(f"  总共生成 Partitions: {total_generated} 个")  # ✅ 输出总生成数
        logger.info(f"  最终返回 Partitions: {len(results)} 个")
        logger.info("=" * 60)
        
        return results, total_generated

    def _recursive_classify_helper(
        self,
        breakdown_incompleteness: bool,
        depth: int,
        max_depth: int,
    ) -> Tuple[List[Dict], int]:
        """
        递归分类的辅助函数。
        
        参数:
            depth: 当前递归深度
            max_depth: 最大递归深度
        
        返回:
            List[Dict]: constraints 为空的分类结果列表
        """
        logger = self.get_logger()
        # indent = "  " * depth
        indent = ''
        
        logger.info(f"{indent}{'='*40}")
        logger.info(f"{indent}深度 {depth}: Solver {self.id}")
        logger.info(f"{indent}{'='*40}")
        
        # ==================== 终止条件：达到最大深度 ====================
        if depth >= max_depth:
            raise SMTError(f"{indent}达到最大深度 {max_depth}，停止递归")
            # return []
        
        # ==================== 步骤 1: 生成 BreakdownTree ====================
        logger.info(f"{indent}[Step 1]: 生成 BreakdownTree...")
        tree = self.new_decompose(recursive=True)
        
        # ==================== 步骤 2: 分类 ====================
        logger.info(f"{indent}[Step 2]: Solver {self.id} 按constraints分类nodes...")
        partitions = self.new_classify(tree)
        total_generated = len(partitions)

        if breakdown_incompleteness:
            # 提前结束
            return partitions, total_generated

        
        # logger.info(f"{indent}分类完成: {len(partitions)} 个 Partitions")
        
        # ==================== 步骤 3: 处理每个 Partition ====================
        logger.info(f"{indent}[Step 3]: 递归获取constraints为空的partitions...")

        final_results = []
        
        for idx, partition in enumerate(partitions):
            solver = partition["solver"]
            nodes = partition["nodes"]
            constraints = partition["constraints"]
            
            # calc_solvers += 1
            logger.info(f"{indent}处理 Partition[{idx}/{len(partitions)}]:")
            
            # 检查所有节点的 constraints 是否为空
            all_empty = (len(constraints) == 0)
            # all_empty = all(len(node.constraints) == 0 for node in nodes)
            
            if all_empty:
                # ✅ 所有 constraints 为空 → 加入最终结果
                logger.info(f"{indent}  ✅ constraints = [], 加入结果集")
                final_results.append(partition)
                logger.info(f"{indent}     共递归生成 0 个结果，返回 1 个最终结果")
            else:
                # ❌ 存在非空 constraints → 递归处理
                # non_empty_count = sum(1 for node in nodes if len(node.constraints) > 0)
                # logger.info(f"{indent}  ❌ {non_empty_count}/{len(nodes)} 个节点 constraints 非空，递归处理")
                
                # 设置 solver ID（用于日志）
                solver.set_id(f"{self.id}_t{idx}")
                
                # 递归调用
                sub_results, sub_generated = solver._recursive_classify_helper(
                    breakdown_incompleteness=breakdown_incompleteness,
                    depth=depth + 1,
                    max_depth=max_depth
                )
                
                # 合并子结果
                final_results.extend(sub_results)
                total_generated += sub_generated
                logger.info(f"{indent}{indent}     共递归生成 {sub_generated} 个结果，返回 {len(sub_results)} 个最终结果")
                solver.close_logger()
        
        logger.info(f"{indent}深度 {depth} 完成: 生成 {total_generated} 个，返回 {len(final_results)} 个最终结果")
        # logger.info(f"{indent}{'='*40}")
    
        # del solver  # 清理递归层的 solver 实例
        # solver.close_logger()
        
        return final_results, total_generated

# ==================== 使用示例 ====================

if __name__ == "__main__":
    pass
