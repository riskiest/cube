# ...existing code...
from fractions import Fraction
from math import comb
from typing import List, Tuple, Union, Dict
from functools import lru_cache
from .hex import Base6ExprEvaluator, FractionFormatter

class F:
    def __init__(self, n_max: int = 10):
        # 六进制工具实例（你的项目中可能为 six.py / hex2）
        self.evaluator = Base6ExprEvaluator()
        self.formatter = FractionFormatter()
        # 预定义 theta(i)：key=i（1~6），value=Fraction
        self.theta = self._init_theta()
        # n 的计算范围：-2 到 10
        self.n_max = n_max
        self.n_range = list(range(-2, n_max + 1))
        # 缓存已计算的 (sorted_K, i) -> dict {n: Fraction}
        self.cache: Dict[Tuple[Tuple[int,...], int], Dict[int, Fraction]] = {}

    def _init_theta(self) -> dict:
        """初始化 theta(i)：从 6 进制字符串解析为 Fraction"""
        theta_def = {
            1: "0.1_6",
            2: "0.11_6",
            3: "0.121_6",
            4: "0.1331_6",
            5: "0.15041_6",
            6: "0.21052411_6"
        }
        return {i: self.evaluator.compute_expression(s) for i, s in theta_def.items()}

    def _sigma(self, K: Tuple[int, ...]) -> Fraction:
        """计算 sigma(K) = multinomial(sumK; K) * 6^{-sumK}。当 sumK==0 时返回 1."""
        sum_K = sum(K)
        # multinomial coefficient
        # 当 sum_K == 0 时，multinomial = 1，6^0 = 1 => sigma = 1
        if sum_K == 0:
            return Fraction(1, 1)
        # 计算多项式系数 sum_K!/(k1!*k2!*...)
        def factorial(n: int) -> int:
            res = 1
            for i in range(2, n+1):
                res *= i
            return res
        numerator = factorial(sum_K)
        denominator = 1
        for k in K:
            denominator *= factorial(k)
        multinom = Fraction(numerator, denominator)
        pow6 = Fraction(1, 6 ** sum_K)
        return multinom * pow6

    def _sorted_K(self, K: Union[List[int], Tuple[int, ...]]) -> Tuple[int, ...]:
        """将 K 转为排序后的元组（利用对称性，统一缓存 key）"""
        return tuple(sorted(tuple(K)))

    def _compute_if_needed(self, sorted_K: Tuple[int, ...], i: int) -> Dict[int, Fraction]:
        """
        确保缓存中存在 (sorted_K, i) 的计算结果，若没有则计算并写入缓存。
        返回一个 dict，键为 n (-2..10)，值为 Fraction。
        采用自顶向下的记忆化（但每个状态只计算一次，避免重复）。
        """
        key = (sorted_K, i)
        if key in self.cache:
            return self.cache[key]

        # 检查 i 合法性：根据公式分母 6-i，题意 i 应在 1..5（5 >= i >= 1）
        if i < 1 or i > 5:
            raise ValueError("i 必须满足 1 ≤ i ≤ 5（否则公式分母 6-i 将为 0 或不符合题意）")

        sum_K = sum(sorted_K)
        result: Dict[int, Fraction] = {}

        # 情况 K 全零（sum_K == 0）
        if sum_K == 0:
            # 初始化 -2 与 -1
            result[-2] = Fraction(1, 1)
            result[-1] = self.theta[i]
            # 递推 n>=0: F(n) = (i / 6) * F(n-1)
            for n in range(0, self.n_max + 1):
                result[n] = Fraction(i, 6) * result[n-1]
            # 写入缓存并返回
            self.cache[key] = result
            return result

        # 非空 K：先生成所有子 K（每个正的 k_j 减 1）
        sub_keys = []
        for idx in range(len(sorted_K)):
            if sorted_K[idx] <= 0:
                continue
            new_K = list(sorted_K)
            new_K[idx] -= 1
            sub_keys.append(self._sorted_K(new_K))

        # 确保所有子状态已计算（递归调用但借助缓存避免重复）
        sub_results = [self._compute_if_needed(sub_k, i) for sub_k in sub_keys]

        # 计算 F(-2) 和 F(-1)
        minus1_sum = sum(sub_res[-1] for sub_res in sub_results) if sub_results else Fraction(0)
        sigma_K = self._sigma(sorted_K)
        denom1 = 6 - i
        denom2 = 6 - i + 1

        candidate_case1 = minus1_sum / denom1
        candidate_case2 = (minus1_sum + sigma_K) / denom2

        result[-2] = max(candidate_case1, sigma_K)
        result[-1] = max(candidate_case1, candidate_case2)

        # 计算 n >= 0：F(n) = (sum_sub_F(n) + i * F(n-1)) / 6
        for n in range(0, self.n_max + 1):
            sum_sub_n = sum(sub_res[n] for sub_res in sub_results) if sub_results else Fraction(0)
            result[n] = (sum_sub_n + i * result[n-1]) / 6

        # 存入缓存并返回
        self.cache[key] = result
        return result

    def get(self, K1: Union[List[int], Tuple[int, ...]], i1: int, old=False) -> Tuple[List[Fraction], List[str]]:
        """
        对外接口：获取 F_{K1,i1} 的结果
        返回 (Fraction 列表, 6 进制字符串列表)，均按 n 从 -2 到 10 的顺序。
        """
        # 校验 i1 与 K1
        if i1 < 1 or i1 > 5:
            raise ValueError("i 必须满足 1 ≤ i ≤ 5。")
        for k in K1:
            if not isinstance(k, int) or k < 0:
                raise ValueError("K 的元素必须为非负整数。")

        sorted_K1 = self._sorted_K(K1)
        res_dict = self._compute_if_needed(sorted_K1, i1)
        if old:
            frac_list = [res_dict[n] for n in self.n_range]
            hex6_list = [self.formatter.fraction_to_base(f) for f in frac_list]
            return frac_list, hex6_list
        return res_dict
        # 构造按顺序的列表



if __name__ == "__main__":
    pass
# ...existing code...