"""
Breakdown 节点和树结构：用于递归分解 LHS 表达式。

设计思想：
1. BreakdownNode: 表示分解树中的一个节点
   - 包含 LHS 表达式、系数、关系、约束等信息
   - 支持递归结构（children 列表）
   
2. BreakdownTree: 管理整个分解树
   - 提供遍历、查询、统计等功能
   - 支持可视化输出
"""

from typing import List, Dict, Optional, Tuple, Union
from z3 import BoolRef, ArithRef, simplify
from dataclasses import dataclass, field
import logging
# from .smt import SMTSolver  # 假设 SmtSolver 在同一模块中

@dataclass
class BreakdownNode:
    """
    Breakdown 节点（递归结构）。
    
    属性:
        LHS: 左侧表达式（ArithRef）
        coeffs: 系数字典 {变量名: 系数}，例如 {"x5": 2, "x4": 1}
        relation: 关系符号（">" 或 "="）
        entailed: 是否被蕴含
        expr: z3 表达式（BoolRef）
        i_min: 当前 LHS 的 i_min（有上界的最小变量索引）
        constraints: 约束链（从根节点到当前节点的所有 expr）
        children: 子节点列表（List[BreakdownNode]）
        parent: 父节点引用（Optional[BreakdownNode]）
        
        # 可选字段（优化相关）
        n_LHS: 每个 n 的分析结果 {n: {"n_lhs": int, "op": str}}
        f_values: 优化计算的 f 值
    """
    
    # 必需字段
    LHS: ArithRef
    coeffs: Dict[str, int]
    relation: str  # ">" or "="
    entailed: bool
    expr: BoolRef
    i_min: int
    
    # 递归结构
    constraints: List[BoolRef] = field(default_factory=list)
    children: List['BreakdownNode'] = field(default_factory=list)
    parent: Optional['BreakdownNode'] = None
    
    # 可选字段
    n_LHS: Dict[int, Dict[str, Union[int, str]]] = field(default_factory=dict)
    f_values: Dict = field(default_factory=dict)
    
    # def __post_init__(self):
    #     """初始化后处理：确保 constraints 包含自己的 expr"""
    #     if self.expr not in self.constraints:
    #         self.constraints = self.constraints + [self.expr]
    
    def add_child(self, child: 'BreakdownNode') -> None:
        """添加子节点并设置父引用"""
        child.parent = self
        # child.constraints = self.constraints + [child.expr]
        self.children.append(child)
    
    def is_leaf(self) -> bool:
        """判断是否为叶子节点"""
        return len(self.children) == 0
    
    def is_root(self) -> bool:
        """判断是否为根节点"""
        return self.parent is None
    
    def depth(self) -> int:
        """计算当前节点的深度（根节点深度为 0）"""
        if self.is_root():
            return 0
        return self.parent.depth() + 1
    
    def get_path_from_root(self) -> List['BreakdownNode']:
        """获取从根节点到当前节点的路径"""
        path = []
        node = self
        while node is not None:
            path.append(node)
            node = node.parent
        return list(reversed(path))
    
    def get_index_path(self) -> Tuple[int, ...]:
        """
        获取从根节点到当前节点的索引路径。
        
        返回:
            例如 (0,) 表示根节点的第 0 个子节点
            (1, 2) 表示根节点的第 1 个子节点的第 2 个子节点
        """
        if self.is_root():
            return ()
        
        path = []
        node = self
        while node.parent is not None:
            # 找到当前节点在父节点 children 中的索引
            idx = node.parent.children.index(node)
            path.append(idx)
            node = node.parent
        
        return tuple(reversed(path))
    
    def to_dict(self) -> Dict:
        """
        转换为字典格式（兼容旧的 member/breakdown 结构）。
        
        返回:
            Dict: 包含所有字段的字典
        """
        return {
            "LHS": self.LHS,
            "coeffs": self.coeffs,
            "relation": self.relation,
            "entailed": self.entailed,
            "expr": self.expr,
            "i_min": self.i_min,
            "constraints": self.constraints,
            "n_LHS": self.n_LHS,
            "f_values": self.f_values,
            "breakdown": [child.to_dict() for child in self.children]
        }
    
    def __str__(self) -> str:
        """可读字符串表示"""
        tmp = f"\u03A3({self.i_min-1})"
        return f"{self.LHS} {self.relation} {0 if self.relation == '=' else tmp}, when {self.constraints}"
        # return f"BreakdownNode(LHS={simplify(self.LHS)}, relation={self.relation}, i_min={self.i_min}, depth={self.depth()}, children={len(self.children)})"
    
    def __repr__(self) -> str:
        return self.__str__()
    
    @staticmethod
    def create_root(x6: ArithRef) -> 'BreakdownNode':
        """
        创建虚拟根节点（用于统一第一层分解）。
        
        参数:
            x6: x6 变量（ArithRef）
        
        返回:
            BreakdownNode: 虚拟根节点
        """
        from z3 import BoolVal, Reals
        # x6 = Reals('x6')
        return BreakdownNode(
            LHS= x6 ,  # 虚拟根的 LHS 为 x6
            coeffs={},              # 空系数
            relation=">",           # 占位符
            entailed=False,         # 占位符
            expr=BoolVal(True),     # 恒真约束（无约束）
            i_min=6,                # 从 x5 开始搜索
            # constraints=[],         # 空约束链
            # children=[],
            parent=None
        )
    
    def is_virtual_root(self) -> bool:
        """判断是否为虚拟根节点"""
        from z3 import is_true
        return (
            self.is_root() and 
            len(self.coeffs) == 0 and 
            len(self.constraints) == 0 and
            is_true(self.expr)
        )


class BreakdownTree:
    """
    Breakdown 树：管理整个分解结构（单根树）。
    
    功能:
    1. 存储和管理所有节点（从单个根节点开始）
    2. 提供遍历（前序、后序、层序）
    3. 查询（根据路径、深度、条件）
    4. 统计信息
    5. 可视化输出
    """
    
    def __init__(self, root: Optional[BreakdownNode] = None):
        """
        初始化 Breakdown 树。
        
        参数:
            root: 根节点（单个）
        """
        self.root: Optional[BreakdownNode] = root
        self.logger = logging.getLogger("breakdown")
    
    def set_root(self, root: BreakdownNode) -> None:
        """设置根节点"""
        self.root = root
    
    def get_all_nodes(self) -> List[BreakdownNode]:
        """获取所有节点（深度优先遍历）"""
        if self.root is None:
            return []
        return self._dfs_collect(self.root)
    
    def _dfs_collect(self, node: BreakdownNode) -> List[BreakdownNode]:
        """深度优先收集节点"""
        result = [node]
        for child in node.children:
            result.extend(self._dfs_collect(child))
        return result
    
    def get_leaves(self) -> List[BreakdownNode]:
        """获取所有叶子节点"""
        return [node for node in self.get_all_nodes() if node.is_leaf()]
    
    def get_nodes_at_depth(self, depth: int) -> List[BreakdownNode]:
        """获取指定深度的所有节点"""
        return [node for node in self.get_all_nodes() if node.depth() == depth]
    
    def find_by_path(self, path: Tuple[int, ...]) -> Optional[BreakdownNode]:
        """
        根据索引路径查找节点。
        
        参数:
            path: 索引路径，例如 (0,) 表示根节点的第 0 个子节点
                  (1, 2) 表示根节点的第 1 个子节点的第 2 个子节点
        
        返回:
            BreakdownNode 或 None（如果路径无效）
        """
        if self.root is None or not path:
            return None
        
        node = self.root
        
        # 遍历路径
        for idx in path:
            if idx >= len(node.children):
                return None
            node = node.children[idx]
        
        return node
    
    def traverse_preorder(self) -> List[BreakdownNode]:
        """前序遍历（根 → 左 → 右）"""
        if self.root is None:
            return []
        return self._preorder(self.root)
    
    def _preorder(self, node: BreakdownNode) -> List[BreakdownNode]:
        """前序遍历辅助函数"""
        result = [node]
        for child in node.children:
            result.extend(self._preorder(child))
        return result
    
    def traverse_postorder(self) -> List[BreakdownNode]:
        """后序遍历（左 → 右 → 根）"""
        if self.root is None:
            return []
        return self._postorder(self.root)
    
    def _postorder(self, node: BreakdownNode) -> List[BreakdownNode]:
        """后序遍历辅助函数"""
        result = []
        for child in node.children:
            result.extend(self._postorder(child))
        result.append(node)
        return result
    
    def traverse_levelorder(self) -> List[List[BreakdownNode]]:
        """层序遍历（按深度分组）"""
        if self.root is None:
            return []
        
        from collections import defaultdict
        levels = defaultdict(list)
        
        for node in self.get_all_nodes():
            levels[node.depth()].append(node)
        
        max_depth = max(levels.keys()) if levels else -1
        return [levels[d] for d in range(max_depth + 1)]
    
    def get_statistics(self) -> Dict:
        """
        获取树的统计信息。
        
        返回:
            Dict: 包含节点数、深度、叶子数等信息
        """
        all_nodes = self.get_all_nodes()
        leaves = self.get_leaves()
        
        if not all_nodes:
            return {
                "total_nodes": 0,
                "num_leaves": 0,
                "max_depth": 0,
                "avg_depth": 0,
                "entailed_count": 0,
                "relation_gt_count": 0,
                "relation_eq_count": 0,
            }
        
        return {
            "total_nodes": len(all_nodes),
            "num_leaves": len(leaves),
            "max_depth": max((node.depth() for node in all_nodes), default=0),
            "avg_depth": sum(node.depth() for node in all_nodes) / len(all_nodes),
            "entailed_count": sum(1 for node in all_nodes if node.entailed),
            "relation_gt_count": sum(1 for node in all_nodes if node.relation == ">"),
            "relation_eq_count": sum(1 for node in all_nodes if node.relation == "="),
        }
    
    def print_tree(self, logger: Optional[logging.Logger] = None) -> None:
        """
        打印树结构（带缩进）。
        
        参数:
            logger: 可选的 logger，若为 None 则使用 self.logger
        """
        if self.root is None:
            (logger or self.logger).info("Empty tree")
            return
        
        log = logger if logger is not None else self.logger
        log.info("Root:")
        self._print_node(self.root, indent=1, logger=log)
        log.info("-" * 40)
    
    def _print_node(self, node: BreakdownNode, indent: int, logger: logging.Logger) -> None:
        """递归打印节点"""
        prefix = "  " * indent + ("> " if node.depth() != 0 else "")
        logger.info(f"{prefix}{node}")
        
        for child in node.children:
            self._print_node(child, indent + 1, logger)
    
    def to_dict(self) -> Optional[Dict]:
        """
        转换为字典格式（兼容旧格式）。
        
        返回:
            Dict 或 None（如果树为空）
        """
        if self.root is None:
            return None
        return self.root.to_dict()
    
    @staticmethod
    def from_dict(d: Dict) -> 'BreakdownTree':
        """
        从字典构造 BreakdownTree（兼容旧格式）。
        
        参数:
            d: 字典（根节点数据）
        
        返回:
            BreakdownTree: 构造的树
        """
        root = BreakdownTree._dict_to_node(d)
        return BreakdownTree(root)
    
    @staticmethod
    def _dict_to_node(d: Dict, parent: Optional[BreakdownNode] = None) -> BreakdownNode:
        """递归地从字典构造节点"""
        node = BreakdownNode(
            LHS=d["LHS"],
            coeffs=d["coeffs"],
            relation=d["relation"],
            entailed=d["entailed"],
            expr=d["expr"],
            i_min=d["i_min"],
            constraints=d.get("constraints", []),
            n_LHS=d.get("n_LHS", {}),
            f_values=d.get("f_values", {}),
            parent=parent
        )
        
        # 递归处理子节点
        for child_dict in d.get("breakdown", []):
            child = BreakdownTree._dict_to_node(child_dict, parent=node)
            node.children.append(child)
        
        return node
    
    def filter_nodes(self, predicate) -> List[BreakdownNode]:
        """
        根据条件过滤节点。
        
        参数:
            predicate: 判断函数，接受 BreakdownNode 返回 bool
        
        返回:
            List[BreakdownNode]: 满足条件的节点列表
        """
        return [node for node in self.get_all_nodes() if predicate(node)]
    
    def get_entailed_leaves(self) -> List[BreakdownNode]:
        """获取所有 entailed 的叶子节点"""
        return [node for node in self.get_leaves() if node.entailed]
    
    def get_non_entailed_leaves(self) -> List[BreakdownNode]:
        """获取所有非 entailed 的叶子节点"""
        return [node for node in self.get_leaves() if not node.entailed]


# ==================== 使用示例 ====================

if __name__ == "__main__":
    # 示例：构造一个简单的 breakdown 树
    pass