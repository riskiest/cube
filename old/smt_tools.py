from typing import List, Tuple, Dict, Union, Optional
import re
from dataclasses import dataclass
from pprint import pprint

from z3 import (
    Reals, Real, Solver, SolverFor, And, Or, Not, sat, unsat, 
    simplify, substitute, is_eq, is_const, ArithRef, BoolRef
)



# --- 新增：全局变量集合（module-level） ---
VAR_NAMES = [f"x{i}" for i in range(1, 7)]
# 全局 z3 变量字典，模块导入时创建
VARS: Dict[str, Real] = {name: Real(name) for name in VAR_NAMES}

class Partition:
    """
    分组对象（非 dataclass，便于后续扩展为大类）：
      - i_min: Optional[int]，来自 find_first_bounded_ratio 的值（若有则填入）
      - entailed: bool，表示该组是否为“无条件成立”的 entailed 组
      - expr: Optional[z3 BoolRef]，该组的代表表达式（非 entailed 组有代表式）
      - substituted_expr: Optional[z3 BoolRef]，该组中某个成员对应的 substituted_expr（用于后续复用）
      - members: List[Dict]，原始条目列表（来自 enumerate_decompositions 的条目）
    """

    def __init__(self, i_min: Optional[int] = None, entailed: bool = False,
                 expr: Optional[BoolRef] = None, members: Optional[List[Dict]] = None,
                 substituted_expr: Optional[BoolRef] = None, vars: Optional[Dict[str, Real]] = None,
                 M: Optional[int] = None):
        self.i_min = int(i_min) if i_min is not None else None
        self.entailed = bool(entailed)
        self.expr = expr
        self.substituted_expr = substituted_expr
        self.members = list(members) if members is not None else []
        self.nmax = 2  # 预留字段，后续可用
        self._solver: Optional[Solver] = None
        # 保存变量字典（优先使用传入 vars，否则回退到模块全局 VARS）
        self.vars = vars if vars is not None else VARS
        self.M = M  # 预留字段，后续可用
        

    def add_member(self, item: Dict):
        self.members.append(item)

    def extend_members(self, items: List[Dict]):
        self.members.extend(items)

    def to_dict(self) -> Dict:
        """若需要把 Partition 转为 dict 返回或序列化，可调用此方法。"""
        return {
            "i_min": self.i_min,
            "entailed": self.entailed,
            "expr": self.expr,
            "substituted_expr": self.substituted_expr,
            "members": self.members,
        }

    def solver(self, base_solver: Optional[Solver] = None, add_expr: Optional[BoolRef] = None) -> Solver:
        """
        为该 Partition 构造或附加一个 z3.Solver 并返回：
        - 如果该 Partition.entailed 为 True，则直接复用 base_solver（必须提供），并存入 self._solver。
        - 否则构造一个新的 Solver，拷贝 base_solver 中的断言（if base_solver provided），
          并在此基础上添加 add_expr（通常为该类的 expr），将结果存入 self._solver 并返回。

        注意：此方法只是构造 Solver 实例，不会 perform check()。调用方可直接使用返回的 solver。
        """
        s = Solver()
        try:
            s.add(*base_solver.assertions())
        except Exception:
            # 兼容性：若无法直接获取断言，则不拷贝
            pass
        if add_expr is not None:
            s.add(add_expr)
        self._solver = s
        return s

    def analyze_member_ratio(self, member: Dict, n: int, max_k: Optional[int] = None) -> Tuple[Optional[int], str]:
        """
        Partition 的实例方法版本（修订版）：
        - 使用 self._solver（应已由 classify_decompositions 初始化）
        - 使用 self.vars 作为变量字典（x{i} 名称映射到 z3 Real）
        - 约束变更为：x_i > n * x_{i-1}（而非之前的 x_{i+1} > n * x_i）
        - 检测 LHS == k * x_{i-1} 或 LHS > k * x_{i-1}（而非 k * x_i）
        - 若 i_min <= 1，直接返回 (None, None)
        """
        if not isinstance(n, int):
            raise TypeError("参数 n 必须是 int")
        if self._solver is None:
            raise ValueError("Partition._solver 未初始化")
        if self.i_min is None or self.i_min <= 1:
            return (None, None)

        xi_name = f"x{self.i_min}"
        xi_prev_name = f"x{self.i_min - 1}"
        if xi_name not in self.vars or xi_prev_name not in self.vars:
            raise ValueError(f"vars 中缺少 {xi_name} 或 {xi_prev_name}")

        xi = self.vars[xi_name]
        xi_prev = self.vars[xi_prev_name]
        LHS = member.get("LHS")
        if LHS is None:
            raise ValueError("member 必须包含 'LHS' 字段")

        if max_k is None:
            max_k = int(self.M) if (self.M is not None) else 40
        max_k = int(max_k)

        # 1) 优先检查是否存在被蕴含的等式 LHS == k * xi_prev
        for k in range(0, max_k + 1):
            self._solver.push()
            try:
                self._solver.add(xi > n * xi_prev)
                self._solver.add(Not(LHS == k * xi_prev))
                res = self._solver.check()
                if res == unsat:
                    return k, '='
            finally:
                try:
                    self._solver.pop()
                except Exception:
                    pass

        # 2) 查找被蕴含的最大 k 使得 LHS > k * xi_prev
        last_k: Optional[int] = None
        for k in range(0, max_k + 1):
            self._solver.push()
            try:
                self._solver.add(xi > n * xi_prev)
                self._solver.add(Not(LHS > k * xi_prev))
                # print(self._solver.assertions())
                # exit()
                res = self._solver.check()
                if res == unsat:
                    last_k = k
                else:
                    return last_k, '>'
            finally:
                try:
                    self._solver.pop()
                except Exception:
                    pass

        return last_k, '>'

    def compute_ratios_for_members(self) -> None:
        """
        对该 Partition 的每个 member，在 n = 1 .. self.nmax 范围内调用 analyze_member_ratio，
        并把返回值 v 写入 member["n_LHS"]（一个 dict），格式为:
            member["n_LHS"][n] = v

        变更：
        - 约束变为 x_i > n * x_{i-1}（而非 x_{i+1} > n * x_i）
        - 若 i_min <= 1，对所有 n 写入 (None, None)
        - 对于 n>1，先检查 x_i > n * x_{i-1} 是否可满足；若不可满足，该 n 对所有 member 均写入 (None, None)
        """
        max_k = self.M
        # 先确保每个 member 都有 n_LHS 容器
        for member in self.members:
            if "n_LHS" not in member or not isinstance(member["n_LHS"], dict):
                member["n_LHS"] = {}

        # 如果 i_min <= 1 或 solver 未初始化，直接为所有 n 写入 (None, None)
        if self.i_min is None or self.i_min <= 1 or self._solver is None:
            for member in self.members:
                for n in range(1, int(self.nmax) + 1):
                    member["n_LHS"][n] = (None, None)
            return

        xi = self.vars.get(f"x{self.i_min}")
        xi_prev = self.vars.get(f"x{self.i_min - 1}")
        if xi is None or xi_prev is None:
            for member in self.members:
                for n in range(1, int(self.nmax) + 1):
                    member["n_LHS"][n] = (None, None)
            return

        for n in range(1, int(self.nmax) + 1):
            # 对 n>1 先检查 x_i > n * x_{i-1} 的可满足性
            if n > 1:
                try:
                    self._solver.push()
                    self._solver.add(xi > n * xi_prev)
                    ok = (self._solver.check() == sat)
                finally:
                    try:
                        self._solver.pop()
                    except Exception:
                        pass

                if not ok:
                    # 对当前 n，所有 member 直接写入 (None, None)
                    for member in self.members:
                        member["n_LHS"][n] = (None, None)
                    continue

            # 若可满足（或 n==1），对每个 member 执行分析
            for member in self.members:
                try:
                    v = self.analyze_member_ratio(member, n, max_k=max_k)
                except Exception:
                    v = (None, None)
                member["n_LHS"][n] = v

    def generate_sum_constraints(self, member_indices: List[int], n: int = 1) -> List[BoolRef]:
        """
        对给定的 member 索引列表和 n，生成所有可能的约束。
        
        算法：
        1. 对每个 member_indices 中的索引，获取对应的 member
        2. 读取 member 的 LHS 和 n_LHS[n]，得到 (k_val, op)
        3. 使用 itertools.combinations_with_replacement 生成所有长度为 k_val+1 的 
           [x1, ..., x_{i_min-1}] 的组合
        4. 对每个组合，生成约束 LHS == sum(组合中的变量)
        5. 汇总所有 member 的约束到一个列表并返回
        
        参数:
            member_indices: member 在 self.members 中的索引列表
            n: 用于读取 n_LHS[n] 的 n 值
        
        返回:
            List[BoolRef]: 所有生成的约束列表
        """
        from itertools import combinations_with_replacement
        
        if self.i_min is None or self.i_min <= 1:
            return []
        
        # 准备变量列表 [x1, ..., x_{i_min-1}]
        var_list = [self.vars[f"x{i}"] for i in range(1, self.i_min)]
        
        all_constraints = []
        
        for idx in member_indices:
            if idx < 0 or idx >= len(self.members):
                continue  # 跳过无效索引
            
            member = self.members[idx]
            
            # 读取 LHS
            LHS = member.get("LHS")
            if LHS is None:
                continue
            
            # 读取 n_LHS[n]
            n_LHS = member.get("n_LHS", {})
            if n not in n_LHS:
                continue
            
            k_val, op = n_LHS[n]
            if k_val is None:
                continue
            
            # 生成所有长度为 k_val+1 的组合
            # combinations_with_replacement 生成可重复的组合
            for combo in combinations_with_replacement(var_list, k_val + 1):
                # 计算 sum(combo)
                sum_expr = sum(combo) if combo else 0
                
                # 生成约束 LHS == sum_expr
                constraint = (LHS == sum_expr)
                all_constraints.append(constraint)
        
        return all_constraints

    
    def filter_and_deduplicate_constraints(self, constraints: List[BoolRef]) -> List[Solver]:
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
        if self._solver is None:
            raise ValueError("Partition._solver 未初始化")
        
        filtered_solvers: List[Solver] = []
        
        for constraint in constraints:
            # 创建新 solver：复制 old_solver 的断言并添加 constraint
            new_solver = Solver()
            try:
                new_solver.add(*self._solver.assertions())
            except Exception:
                pass
            new_solver.add(constraint)
            
            # 剪枝 1：检查可满足性
            if new_solver.check() == unsat:
                continue  # 不可满足，跳过
            
            # 剪枝 2：检查是否与已保留的 solver 等价
            is_duplicate = False
            for existing_solver in filtered_solvers:
                if self._are_solvers_equivalent(new_solver, existing_solver):
                    is_duplicate = True
                    break
            
            if not is_duplicate:
                filtered_solvers.append(new_solver)
        
        return filtered_solvers
    
    def _are_solvers_equivalent(self, solver1: Solver, solver2: Solver) -> bool:
        """
        判断两个 Solver 是否等价（即它们的约束集合逻辑等价）。
        
        算法：
        - solver1 ⊨ solver2：检查 solver1 ∧ ¬(And(solver2.assertions)) 是否 unsat
        - solver2 ⊨ solver1：检查 solver2 ∧ ¬(And(solver1.assertions)) 是否 unsat
        - 若两者都成立，则等价
        
        参数:
            solver1, solver2: 两个 z3 Solver 实例
        
        返回:
            bool: True 表示等价，False 表示不等价
        """
        try:
            assertions1 = solver1.assertions()
            assertions2 = solver2.assertions()
            
            # 快速检查：如果断言数量相同且字符串表示相同（简单情况）
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
        
        except Exception:
            # 若检查过程出错（如超时），保守地认为不等价
            return False

class SMTTextInterface:
    """
    文本 <-> Z3 表达式 接口类。
    现在不再自己创建变量，而是通过构造函数接收一个 vars 字典。
    """

    _ALLOWED_TOKEN_RE = re.compile(r'[0-9a-zA-Z_\+\-\*\/\^\.\(\)\s<>=!]')

    def __init__(self, vars: Optional[Dict[str, Real]] = None):
        """
        vars: dict mapping variable name -> z3 Real. 若为 None，使用模块全局 VARS。
        """
        # 使用传入 vars 或模块全局 VARS
        self.vars = vars if vars is not None else VARS
        # 动态生成用于隐式乘法的正则（支持多位数），仅匹配传入的变量名
        var_alt = '|'.join(re.escape(v) for v in sorted(self.vars.keys(), reverse=True))
        self._IMPLICIT_MUL_RE = re.compile(r'(?P<num>\d+)(?P<var>' + var_alt + r')')
        self.VAR_NAMES = list(self.vars.keys())

    def _normalize(self, text: str) -> str:
        t = text.strip()
        # 标准化等号：把单独的赋值符号 = 转为 ==，但不要破坏 >=, <=, !=, == 等
        # 使用正则：将不被 <>!= 前后符号包围的单个 = 替换为 ==
        t = re.sub(r'(?<![<>=!])=(?!=)', '==', t)
        # 先将隐式乘法补上（依赖于构造时生成的正则）
        t = self._IMPLICIT_MUL_RE.sub(r"\g<num>*\g<var>", t)
        # 将 ^ 替换为 **（如果用户使用）
        t = t.replace("^", "**")
        return t

    def _validate_chars(self, text: str):
        # 简单检查：只允许有限字符集合（防止注入）
        for ch in text:
            if not self._ALLOWED_TOKEN_RE.match(ch):
                raise ValueError(f"不允许的字符: {ch!r}")

    def parse(self, text: Union[str, List[str]]) -> Tuple[List[BoolRef], Dict[str, ArithRef]]:
        """
        将文本或文本列表解析为 z3 约束列表。
        返回 (constraints_list, equalities_map)
          - constraints_list: list of z3 BoolRef
          - equalities_map: 若出现形如 xN == expr 的显式等式，会记录 mapping 'xN'->expr (z3 表达式)
        """
        if isinstance(text, str):
            lines = [t for t in text.splitlines() if t.strip()]
        else:
            lines = [t for t in text]
        constraints: List[BoolRef] = []
        equalities: Dict[str, ArithRef] = {}

        for line in lines:
            nl = self._normalize(line)
            self._validate_chars(nl)
            # 安全 eval：限定全局/局部变量为已知 z3 变量与内置算符
            loc = dict(self.vars)
            # also allow Python numeric literals naturally
            try:
                expr = eval(nl, {"__builtins__": None}, loc)
            except Exception as e:
                raise ValueError(f"无法解析表达式 {line!r}: {e}") from e

            # 单条可能是布尔约束（==, >, >=, <, <= 等）
            if isinstance(expr, BoolRef):
                constraints.append(expr)
                # 若是等式且左侧是变量名 xN，则记录等式映射
                if is_eq(expr):
                    a0 = expr.arg(0)
                    a1 = expr.arg(1)
                    # find if either side is a plain variable
                    for side_var, other in ((a0, a1), (a1, a0)):
                        if is_const(side_var) and str(side_var) in self.vars:
                            # store mapping varname -> other (other is z3 expression)
                            equalities[str(side_var)] = other
                            break
            else:
                # 如果用户直接写了表达式（非布尔），把它视为等于零的约束
                # 例如 "x6 - 2*x5" -> require == 0
                try:
                    # force to z3 arith and create equality to 0
                    zero_c = expr == 0
                    constraints.append(zero_c)
                except Exception as e:
                    raise ValueError(f"解析后无法转为约束: {line!r}: {e}") from e

        return constraints, equalities

    def exprs_to_text(self, exprs: Union[BoolRef, List[BoolRef]]) -> List[str]:
        """把 z3 的表达式或约束列表转换成可读文本（使用 z3.simplify 后的 str()）。"""
        if isinstance(exprs, (list, tuple)):
            lst = exprs
        else:
            lst = [exprs]
        out = []
        for e in lst:
            try:
                out.append(str(simplify(e)))
            except Exception:
                out.append(str(e))
        return out


class SMTAnalyzer:
    """
    主功能类：
    - 初始化时建立 Solver 并加入默认约束 x6>x5>x4>x3>x2>x1>0
    - 可通过 add_constraints_from_text(text) 加入由 SMTTextInterface 解析出来的约束
    - find_first_bounded_ratio(M=40) : 从 x5 开始向下查找第一个 xi (i from 5 down to 1)
         使得 x5/xi 被判定为有上界（采用阈值 M：若 x5/xi > M 仍可满足则判为无上界）。
         返回该 xi 的名字（如 'x3'）或 None（若从 x5..x1 都无上界）
    - enumerate_decompositions(i_min, max_k=6) :
         枚举 k5..k_{i_min}（自然数 0..max_k）的组合，判断约束下 x6 >= sum(kj*xj) 是否
         被蕴含 / 可满足，区分 '>' 或 '=' 情形，并返回结构化结果。
    """

    def __init__(self, M: int = 40):
        # 使用模块全局 VARS（并传给文本接口，若需要覆盖可传入自定义 vars）
        self.VAR_NAMES = VAR_NAMES
        self.vars = VARS
        self.interface = SMTTextInterface()  # 默认使用全局 VARS
        self.solver = Solver()
        self.M = M
        # 默认约束
        v = self.vars
        self.solver.add(v["x6"] > v["x5"], v["x5"] > v["x4"], v["x4"] > v["x3"],
                        v["x3"] > v["x2"], v["x2"] > v["x1"], v["x1"] > 0)
        # 记录解析到的等式，便于简化替换：varname -> z3 expr
        self.equalities: Dict[str, ArithRef] = {}

    def add_constraints_from_text(self, text: Union[str, List[str]]):
        constrs, eqs = self.interface.parse(text)
        for c in constrs:
            self.solver.add(c)
        # 合并等式记录；若冲突按后加入覆盖
        self.equalities.update(eqs)

    def add_constraints(self, constraints: List[BoolRef]):
        """直接将 z3 约束加入求解器（辅助用）"""
        for c in constraints:
            self.solver.add(c)
            # 若是等式且一边是变量，记录等式
            if is_eq(c):
                a0, a1 = c.arg(0), c.arg(1)
                for side_var, other in ((a0, a1), (a1, a0)):
                    if is_const(side_var) and str(side_var) in self.vars:
                        self.equalities[str(side_var)] = other
                        break

    def _is_entailed(self, prop: BoolRef) -> bool:
        """判断当前约束是否蕴含 prop（即 C ⊨ prop）"""
        self.solver.push()
        # 当且仅当 C ∧ ¬prop 不可满足时，C 蕴含 prop
        self.solver.add(Not(prop))
        res = self.solver.check()
        self.solver.pop()
        # True 表示蕴含, False 表示不蕴含
        return res == unsat

    def _is_satisfiable(self, prop: BoolRef) -> bool:
        """判断当前约束与 prop 是否可满足；若可满足返回 (True, model_as_dict)"""
        self.solver.push()
        # 检查 C ∧ prop 是否可满足
        self.solver.add(prop)
        res = self.solver.check()
        self.solver.pop()
        # True 表示可满足, False 表示不可满足
        return res == sat


    def find_first_bounded_ratio(self) -> Optional[int]:
        """
        从 x5 开始向下检查 x6/xi 是否有上界（按阈值 M 判断）。
        若对某 xi，C ∧ (x6/xi > M) 不可满足（unsat），则认为 x6/xi 有上界（<= M），返回该 xi 的索引 i（整数 5..1）。
        否则继续向下；若全部可满足（对所有 xi，x6/xi > M 都可满足），返回 None。
        """
        x6 = self.vars["x6"]
        for i in range(5, 0, -1):
            xi = self.vars[f"x{i}"]
            test = x6 > self.M * xi
            if self._is_satisfiable(test):
                return i + 1  # 返回上一个 i，因为当前 i 可满足无界
        return i

    def max_k_satisfiable(self, xi: str) -> Dict[str, Union[None,int,bool]]:
        """
        线性搜索在 [0, max_search] 范围内使 x6 <= k*xi 可满足的最大整数 k。
        返回：
          {"xi": xi, "found": True/False, "k_max_sat": int or None, "maybe_unbounded": bool}
        使用线性扫描（for k in range(0, max_search+1)），记录最大满足的 k。
        """
        xi_var = self.vars[xi]
        x6 = self.vars["x6"]
        max_search = self.M

        last_ok = None
        for k in range(0, max_search + 1):
            prop = x6 <= k * xi_var
            if self._is_satisfiable(prop):
                last_ok = k
        if last_ok is None:
            return {"xi": xi, "found": False, "k_max_sat": None, "maybe_unbounded": False}
        maybe_unbounded = (last_ok == max_search)
        return {"xi": xi, "found": True, "k_max_sat": last_ok, "maybe_unbounded": maybe_unbounded}

    def _substitute_equalities(self, expr):
        """
        用已记录的 equalities 进行安全替换并返回替换后的表达式。
        - 检测环，跳过环中变量；
        - 对无环子图按拓扑顺序展开 RHS，使 RHS 尽可能被完全展开；
        - 对输入 expr 进行多轮 substitute + simplify 直到收敛或达到最大轮数。
        返回 z3 表达式（已 simplify），并把检测到的环保存到 self._last_substitution_cycles。
        """
        if not self.equalities:
            return expr

        # 构建依赖关系： var -> set(vars it depends on)
        deps: Dict[str, set] = {}
        var_names = set(self.vars.keys())
        for var, rhs in self.equalities.items():
            deps[var] = set()
            s = str(rhs)
            for vn in var_names:
                if re.search(r'\b' + re.escape(vn) + r'\b', s):
                    deps[var].add(vn)

        # 环检测（DFS），收集 in_cycle
        visiting = set()
        visited = set()
        in_cycle = set()

        def dfs(u: str, stack: List[str]):
            if u in visited:
                return
            if u in visiting:
                idx = stack.index(u)
                in_cycle.update(stack[idx:])
                return
            visiting.add(u)
            stack.append(u)
            for v in deps.get(u, ()):
                if v in deps:
                    dfs(v, stack)
            stack.pop()
            visiting.remove(u)
            visited.add(u)

        for node in list(deps.keys()):
            if node not in visited:
                dfs(node, [])

        # 准备无环节点的拓扑序（Kahn），以便先展开依赖的变量
        acyclic = [n for n in deps.keys() if n not in in_cycle]
        indeg = {n: 0 for n in acyclic}
        for u in acyclic:
            for v in deps.get(u, ()):
                if v in indeg:
                    indeg[v] += 1
        queue = [n for n, d in indeg.items() if d == 0]
        topo: List[str] = []
        while queue:
            u = queue.pop(0)
            topo.append(u)
            for v in deps.get(u, ()):
                if v in indeg:
                    indeg[v] -= 1
                    if indeg[v] == 0:
                        queue.append(v)

        # 逐步展开 topo 中的每个 var 的 rhs（用已处理变量的最终 rhs 去替换）
        from z3 import substitute
        expanded_rhs: Dict[str, ArithRef] = {}
        for var in topo:
            rhs = self.equalities[var]
            if expanded_rhs:
                subs_pairs = [(self.vars[vn], expanded_rhs[vn]) for vn in expanded_rhs.keys()]
                try:
                    rhs_expanded = substitute(rhs, *subs_pairs)
                except Exception:
                    rhs_expanded = rhs
            else:
                rhs_expanded = rhs
            # 尝试简化一下 rhs
            try:
                rhs_expanded = simplify(rhs_expanded)
            except Exception:
                pass
            expanded_rhs[var] = rhs_expanded

        # 构造一次性替换对（仅对拓扑中无环变量）
        subs_final = [(self.vars[v], expanded_rhs[v]) for v in topo] if topo else []

        # 对 expr 做多轮替换直到收敛（或达到最大轮次），以确保嵌套引用被展开
        prev = expr
        max_iters = 8
        for _ in range(max_iters):
            try:
                if subs_final:
                    new = substitute(prev, *subs_final)
                else:
                    new = prev
                new_s = simplify(new)
            except Exception:
                new_s = prev
            # 比较 AST 的字符串表示判断是否收敛
            if str(new_s) == str(prev):
                prev = new_s
                break
            prev = new_s

        # 记录检测到的环（供外部查询），并返回最终结果
        self._last_substitution_cycles = list(in_cycle) if in_cycle else []
        return prev

    def enumerate_decompositions(self) -> List[Tuple[Dict[str,int], str, Union[bool,str]]]:
        """
        自动决定 i_min = find_first_bounded_ratio()，若没有找到有上界的 xi 则返回空列表。
        否则对 xi..x5（从 x5 降到 xi）调用 max_k_satisfiable 获取每个变量的最大可满足系数，
        在笛卡尔积 [0..max_k5] x [0..max_k4] x ... x [0..max_ki] 中枚举所有组合 (k5,...,ki)。

        对每个组合：
          - 若 x6 >= sum(kj*xj) 不可满足则跳过；
          - 否则先处理 ">"：
              - 若 C ⊨ x6 > sum(...) 则添加 (coeffs, '>', True)
              - 否则若 C ∧ (x6 > sum(...)) 可满足则添加 (coeffs, '>', str(simplified_cond))
          - 再处理 "="：
              - 若 C ⊨ x6 == sum(...) 则添加 (coeffs, '=', True)
              - 否则若 C ∧ (x6 == sum(...)) 可满足则添加 (coeffs, '=', str(simplified_cond))
        返回列表，元素为三元组 (coeff_map, relation, condition)：
          - coeff_map: {'x5':k5, 'x4':k4, ...}
          - relation: '>' 或 '='
          - condition: True 表示被蕴含；或为字符串形式的简化条件（如 "x5 + x4 - x3 > 0"）
        """
        from itertools import product
        results: List[Tuple[Dict[str,int], str, Union[bool,str]]] = []

        # 1) 先找 i_min（最小有上界的 xi）
        i_min = self.find_first_bounded_ratio()
        # # 解释兼容性：若 find_first_bounded_ratio 返回 None/False/6 表示无有界变量
        # 如果返回的是索引偏移异常（例如先前实现返回 i+1），尝试规范化到 1..5
        if isinstance(i_min, int) and not (1 <= i_min <= 5):
            # 若返回值为 6 或 >5，视作无满足
            return results

        # 2) 准备变量序列 x5, x4, ..., x_{i_min}
        indices = list(range(5, i_min - 1, -1))  # e.g. [5,4,3] when i_min=3
        var_names = [f"x{i}" for i in indices]

        # 3) 对每个变量调用 max_k_satisfiable，得到各自最大 k
        max_ks: Dict[str,int] = {}
        for vn in var_names:
            mts = self.max_k_satisfiable(vn)
            if not mts.get("found", False):
                # 如果某个变量在 [0..M] 内无可满足 k，则认为其上界为 0（仍可尝试 k=0）
                max_k = 0
            else:
                max_k = int(mts.get("k_max_sat", 0))
            max_ks[vn] = max_k

        # 4) 构造搜索空间并枚举
        ranges = [range(0, max_ks[vn] + 1) for vn in var_names]
        for ks in product(*ranges):
            coeff_map = {var_names[idx]: int(ks[idx]) for idx in range(len(var_names))}
            # 构造 sum_expr = k5*x5 + k4*x4 + ...
            sum_expr = None
            for vn, k in coeff_map.items():
                if k == 0:
                    continue
                term = self.vars[vn] * k
                sum_expr = term if sum_expr is None else sum_expr + term
            if sum_expr is None:
                from z3 import RealVal
                sum_expr = RealVal(0)

            # 先检查 >= 是否可满足，否则跳过
            prop_ge = self.vars["x6"] >= sum_expr
            if not self._is_satisfiable(prop_ge):
                # 该组合及所有在更高次维度（即增加某个后续 kj）的组合通常也不可满足，但不做复杂剪枝
                continue

            # 尝试简化表达式用于输出条件文字
            # simplified_diff = self._substitute_equalities(self.vars["x6"] - sum_expr)
            simplified_diff = self.vars["x6"] - sum_expr 
            
            # 处理 ">" 情形
            prop_gt = simplified_diff > 0
            if self._is_entailed(prop_gt):
                results.append({
                    "coeffs": coeff_map,
                    "relation": ">",
                    "entailed": True,
                    "expr": prop_gt,                     # z3 BoolRef，供后续直接复用
                    "substituted_expr": self._substitute_equalities(prop_gt),   # 替换后的表达式
                    "LHS":  simplified_diff,               # LHS 表达式，供后续直接复用
                })
            else:
                if self._is_satisfiable(prop_gt):
                    # 保留 z3 表达式，不做早期 str 化；同时保留可读字符串
                    results.append({
                        "coeffs": coeff_map,
                        "relation": ">",
                        "entailed": False,
                        "expr": prop_gt,
                        "substituted_expr": self._substitute_equalities(prop_gt),
                        "LHS":  simplified_diff,
                    })

            # 处理 "=" 情形
            prop_eq = self.vars["x6"] == sum_expr
            if self._is_entailed(prop_eq):
                results.append({
                    "coeffs": coeff_map,
                    "relation": "=",
                    "entailed": True,
                    "expr": prop_eq,
                    "substituted_expr": self._substitute_equalities(prop_eq),
                    "LHS":  simplified_diff,
                })
            else:
                if self._is_satisfiable(prop_eq):
                    results.append({
                        "coeffs": coeff_map,
                        "relation": "=",
                        "entailed": False,
                        "expr": prop_eq,
                        "substituted_expr": self._substitute_equalities(prop_eq),
                        "LHS":  simplified_diff,
                    })
        return results, i_min

    def classify_decompositions(self, results: List[Dict], i_min: Optional[int] = None) -> List[Partition]:
        """
        把 enumerate_decompositions 的结果分组并返回 Partition 列表。
        - classes[0] 为 entailed 类（无条件成立），其 members 为所有 entailed==True 的条目，entailed=True，expr=None。
        - 其余类按 expr 等价性分组（使用 self._is_entailed(expr == rep) 判定等价），
          每个类 entailed=False，expr 为该类代表式，members 为该类条目列表。
        - 每个 Partition 包含传入的 i_min（若提供），并为每个 Partition 附加 solver（通过 Partition.solver(...)）。
        返回值类型：List[Partition]
        """
        entailed = [r for r in results if r.get("entailed")]
        others = [r for r in results if not r.get("entailed")]

        groups: List[Dict] = []  # 临时：每项 {'expr': BoolRef, 'substituted_expr': BoolRef, 'members': [...]} 
        for item in others:
            expr = item.get("expr")
            if expr is None:
                groups.append({"expr": None, "substituted_expr": None, "members": [item]})
                continue

            placed = False
            for g in groups:
                g_expr = g["expr"]
                if g_expr is None:
                    continue
                try:
                    # 判等：C ⊨ (expr == g_expr)
                    if self._is_entailed(expr == g_expr):
                        g["members"].append(item)
                        # 若该组尚无 substituted_expr，则用当前成员的 substituted_expr（若有）
                        if g.get("substituted_expr") is None and item.get("substituted_expr") is not None:
                            g["substituted_expr"] = item.get("substituted_expr")
                        placed = True
                        break
                except Exception:
                    continue
            if not placed:
                # 创建新组时记录该成员的 substituted_expr（可能为 None）
                groups.append({"expr": expr, "substituted_expr": item.get("substituted_expr"), "members": [item]})

        # 把所有 entailed 条目加入到每个类的 members 中（深拷贝，避免共享）
        if entailed:
            import copy
            for g in groups:
                g["members"].extend(copy.deepcopy(entailed))  # ✅ 深拷贝

            # 在第 0 位插入 entailed 类（表示当且仅当其他所有类的 expr 都不成立时的情形）
            # entailed_group.expr = And(Not(expr1), Not(expr2), ...)
            # entailed_group.substituted_expr 同理基于 substituted_expr 列表
            other_exprs = [g["expr"] for g in groups if g.get("expr") is not None]
            other_subs = [g["substituted_expr"] for g in groups if g.get("substituted_expr") is not None]

            entailed_expr = And(*[Not(e) for e in other_exprs]) if other_exprs else None
            entailed_substituted = And(*[Not(s) for s in other_subs]) if other_subs else None

            entailed_group = {
                "expr": entailed_expr,
                "substituted_expr": entailed_substituted,
                "members": entailed,
                "entailed": True
            }
            groups.insert(0, entailed_group)

        # 归一化并构造 Partition 列表（统一使用 expr 字段），并把每组的 substituted_expr 传入 Partition
        # 构造 Partition 时传入当前 Analyzer 的 vars
        partitions = [
            Partition(
                i_min=int(i_min) if i_min is not None else None,
                entailed=bool(g.get("entailed", False)),
                expr=g.get("expr", None),
                members=g.get("members", []),
                substituted_expr=g.get("substituted_expr", None),
                vars=self.vars,
                M = self.M,
            )
            for g in groups
        ]

        # 为每个 Partition 附加 solver：统一用 add_expr=p.expr
        for p in partitions:
            p.solver(base_solver=self.solver, add_expr=p.expr)
        
        for i, p in enumerate(partitions):
            # print(p._solver.assertions())
            # print("-----")
            p.compute_ratios_for_members()

        return partitions

        


texts = [
    [["x6 = 2*x5", "x5 = 2*x4"], 4],
    [["x6 = 2*x5", "x5 = x4 + x3"], 4],
    [["x6 = 2*x5"], 5],
    [["x6 = x2 + x3"], 3],
    [["x6 = 2x3"], 3],
]

# 简单命令行演示（保留用于测试）
if __name__ == "__main__":
    an = SMTAnalyzer()
    # 演示：加入一些文本约束
    # 测试texts中的例子
    for txts, expected in texts[1:]:
        an = SMTAnalyzer()
        an.add_constraints_from_text(txts)
        # print(an.solver.assertions())
        # break

        results, i_min = an.enumerate_decompositions()
        partitions = an.classify_decompositions(results, i_min)
        # p = partitions[0]
        # pprint(p.to_dict())
        # for p in partitions:
        #     pprint(p.to_dict())
        #     print("=========")
        break
    p = partitions[1]
    all_constraints = p.generate_sum_constraints([0,4], 1)
    filtered_solvers = p.filter_and_deduplicate_constraints(all_constraints)
    print(len(filtered_solvers))


