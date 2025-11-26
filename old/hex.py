from fractions import Fraction
from typing import Union, List

class Hex6Tool:
    """六进制小数工具类：支持6进制字符串解析、Fraction与6进制互转"""
    @staticmethod
    def parse_hex6(hex6_str: str) -> Fraction:
        """将6进制小数字符串（如"0.121_6"、"0.11"）解析为Fraction"""
        # 去除可能的后缀"_6"
        hex6_str = hex6_str.strip().rstrip("_6").strip()
        if "." not in hex6_str:
            # 整数部分
            return Fraction(int(hex6_str, 6))
        # 分离整数和小数部分
        integer_part, fractional_part = hex6_str.split(".", 1)
        # 解析整数部分（支持空字符串，即"0."等价于"0.0"）
        int_val = int(integer_part, 6) if integer_part else 0
        # 解析小数部分：d1*6^-1 + d2*6^-2 + ... + dn*6^-n
        frac_val = Fraction(0)
        for idx, digit_char in enumerate(fractional_part):
            digit = int(digit_char, 6)  # 单个6进制字符转10进制数字
            frac_val += Fraction(digit, 6 ** (idx + 1))
        return Fraction(int_val) + frac_val

    @staticmethod
    def fraction_to_hex6(
        frac: Fraction, 
        precision: int = 10  # 小数部分保留位数
    ) -> str:
        """将Fraction转换为6进制字符串（格式："整数部分.小数部分"）"""
        if frac < 0:
            sign = "-"
            frac = -frac
        else:
            sign = ""
        
        # 处理整数部分
        integer_part = int(frac.numerator // frac.denominator)
        hex6_int = hex(integer_part)[2:] if integer_part != 0 else "0"
        # 转换为6进制（Python无直接6进制字符串函数，手动实现）
        hex6_int = Hex6Tool._decimal_to_base6(integer_part)
        
        # 处理小数部分
        frac_part = frac - Fraction(integer_part)
        hex6_frac = []
        remaining = frac_part
        for _ in range(precision):
            remaining *= 6
            digit = int(remaining.numerator // remaining.denominator)
            hex6_frac.append(str(digit))
            remaining -= Fraction(digit)
            if remaining == 0:
                break  # 小数部分终止，无需补0
        
        # 拼接结果
        if hex6_frac:
            return f"{sign}{hex6_int}.{''.join(hex6_frac)}_6"
        else:
            return f"{sign}{hex6_int}_6"

    @staticmethod
    def _decimal_to_base6(decimal: int) -> str:
        """将10进制非负整数转换为6进制字符串"""
        if decimal == 0:
            return "0"
        digits = []
        while decimal > 0:
            remainder = decimal % 6
            digits.append(str(remainder))
            decimal = decimal // 6
        return "".join(reversed(digits))

    @staticmethod
    def hex6_to_decimal(hex6_str: str) -> float:
        """6进制字符串转10进制浮点数（用于验证，不推荐精确计算）"""
        return float(Hex6Tool.parse_hex6(hex6_str))

if __name__ == "__main__":
    # 测试代码
    test_hex6 = "1.2_6"
    frac = Hex6Tool.parse_hex6(test_hex6)
    print(f"{test_hex6} 解析为 Fraction: {frac}")
    hex6_str = Hex6Tool.fraction_to_hex6(frac, precision=5)
    print(f"Fraction {frac} 转回 6进制字符串: {hex6_str}")