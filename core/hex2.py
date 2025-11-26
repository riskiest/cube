from fractions import Fraction
import re, ast, sys

class FractionFormatter:
    """处理 Fraction 的各种输出（十进制/6进制等）"""
    def __init__(self, base: int = 6, max_frac_digits: int = 60):
        self.base = base
        self.max_frac_digits = max_frac_digits

    def fraction_to_base(self, frac: Fraction) -> str:
        """把 Fraction 转成 base 进制字符串，重复节用 ( ) 表示"""
        base = self.base
        if frac == 0:
            return "0_{}".format(base)
        sign = "-" if frac < 0 else ""
        num = abs(frac.numerator)
        den = frac.denominator

        integer = num // den
        if integer == 0:
            int_str = "0"
        else:
            digits = []
            iv = integer
            while iv > 0:
                digits.append(str(iv % base))
                iv //= base
            int_str = "".join(reversed(digits))

        remainder = num % den
        if remainder == 0:
            return f"{sign}{int_str}_{base}"

        seen = {}
        frac_digits = []
        idx = 0
        repeat_index = None
        while remainder != 0 and idx < self.max_frac_digits:
            if remainder in seen:
                repeat_index = seen[remainder]
                break
            seen[remainder] = idx
            remainder *= base
            d = remainder // den
            frac_digits.append(str(d))
            remainder = remainder % den
            idx += 1

        if remainder == 0:
            frac_part = "".join(frac_digits)
        else:
            if repeat_index is not None:
                nonrep = "".join(frac_digits[:repeat_index])
                rep = "".join(frac_digits[repeat_index:])
                frac_part = f"{nonrep}({rep})"
            else:
                frac_part = "".join(frac_digits) + "..."

        return f"{sign}{int_str}.{frac_part}_{base}"

    def format_output(self, result: Fraction) -> str:
        if result.denominator == 1:
            base6 = self.fraction_to_base(result)
            return f"整数: {result.numerator}\n{self.base}进制: {base6}"
        else:
            dec = float(result)
            base6 = self.fraction_to_base(result)
            return f"十进制(浮点): {dec:.6f}\n十进制(分数): {result}\n{self.base}进制: {base6}"


class Base6ExprEvaluator:
    """
    工具类：解析并计算混合 6 进制/10 进制表达式，返回 Fraction。
    支持输入数字如:
      - 整数或小数（默认十进制），如 12 或 3.5
      - 后缀 _10 明确十进制: 3.5_10
      - 后缀 _6 表示 base-6 数字，整数部分和小数部分用 base-6 位表示。
        小数部分支持重复节用括号表示，例如 1.2(34)_6 或 0.(5)_6
    """
    # 匹配：整数或小数，允许小数部分包含可选的重复节 (...)，并可带后缀 _6 或 _10
    _NUM_RE = re.compile(r'[0-9]+(?:\.(?:[0-9]+(?:\([0-9]+\))?)?)?(?:_6|_10)?')

    def __init__(self, base: int = 6):
        self.base = base

    def parse_base6_to_fraction(self, s: str) -> Fraction:
        """解析一个 base-6 表示的字符串（小数可含重复节用括号）到 Fraction"""
        # s 例如 "123.45", "12.(34)", "0.(5)"
        if '(' in s:
            # 支持形式 int.nonrep(rep)
            int_part, frac_part = s.split('.', 1) if '.' in s else (s, "")
            # find '('
            if '(' not in frac_part or ')' not in frac_part:
                raise ValueError("不完整的重复节表示")
            nonrep, rep_with = frac_part.split('(', 1)
            rep = rep_with.rstrip(')')
            nonrep = nonrep  # may be ""
            # parse integer part
            int_val = 0 if int_part == "" else self._parse_base6_int(int_part)
            # compute fractional value:
            # value = int_val + nonrep/6^r + rep / (6^r * (6^len(rep)-1))
            r = len(nonrep)
            nonrep_val = 0
            for ch in nonrep:
                if not ch.isdigit() or int(ch) >= self.base:
                    raise ValueError("非法的 base-6 小数数字")
                nonrep_val = nonrep_val * self.base + int(ch)
            rep_val = 0
            for ch in rep:
                if not ch.isdigit() or int(ch) >= self.base:
                    raise ValueError("非法的 base-6 小数数字")
                rep_val = rep_val * self.base + int(ch)
            numer = int_val * (self.base ** r) * (self.base ** len(rep) - 1) + nonrep_val * (self.base ** len(rep) - 1) + rep_val
            denom = (self.base ** r) * (self.base ** len(rep) - 1)
            return Fraction(numer, denom)
        else:
            # no repeating parentheses
            if '.' in s:
                int_part, frac_part = s.split('.', 1)
            else:
                int_part, frac_part = s, ""
            int_val = 0 if int_part == "" else self._parse_base6_int(int_part)
            if frac_part == "":
                return Fraction(int_val, 1)
            k = len(frac_part)
            frac_val = 0
            for ch in frac_part:
                if not ch.isdigit() or int(ch) >= self.base:
                    raise ValueError("非法的 base-6 小数数字")
                frac_val = frac_val * self.base + int(ch)
            numer = int_val * (self.base ** k) + frac_val
            denom = self.base ** k
            return Fraction(numer, denom)

    def _parse_base6_int(self, s: str) -> int:
        v = 0
        for ch in s:
            if not ch.isdigit() or int(ch) >= self.base:
                raise ValueError("非法的 base-6 数字")
            v = v * self.base + int(ch)
        return v

    def tokenize_and_replace(self, expr: str):
        parts = []
        nums = {}
        last = 0
        idx = 0
        for m in self._NUM_RE.finditer(expr):
            start, end = m.span()
            parts.append(expr[last:start])
            tok = m.group(0)
            name = f"__N{idx}__"
            # compute Fraction value
            if tok.endswith("_6"):
                core = tok[:-2]
                val = self.parse_base6_to_fraction(core)
            elif tok.endswith("_10"):
                core = tok[:-3]
                val = Fraction(core)
            else:
                # plain decimal/integer — parse with Fraction to keep exactness
                if '.' in tok:
                    val = Fraction(tok)
                else:
                    val = Fraction(int(tok), 1)
            nums[name] = val
            parts.append(name)
            last = end
            idx += 1
        parts.append(expr[last:])
        new_expr = "".join(parts)
        return new_expr, nums

    class _Validator(ast.NodeVisitor):
        ALLOWED = (ast.Expression, ast.BinOp, ast.UnaryOp, ast.Name, ast.Load,
                   ast.Add, ast.Sub, ast.Mult, ast.Div, ast.UAdd, ast.USub,
                   ast.Constant, ast.Mod, ast.FloorDiv, ast.Pow, ast.Expr, ast.Tuple, ast.List)

        def visit(self, node):
            if not isinstance(node, self.ALLOWED):
                raise ValueError(f"不允许的表达式元素: {type(node).__name__}")
            super().visit(node)
        def visit_Name(self, node):
            # names validated elsewhere
            return

    def safe_eval(self, expr: str, names: dict) -> Fraction:
        node = ast.parse(expr, mode='eval')
        self._Validator().visit(node)
        # ensure all Name nodes are in names
        for n in [node for node in ast.walk(node) if isinstance(node, ast.Name)]:
            if n.id not in names:
                raise ValueError(f"不允许的变量: {n.id}")
        code = compile(node, '<expr>', 'eval')
        val = eval(code, {"__builtins__": None}, names)
        if not isinstance(val, Fraction):
            if isinstance(val, int):
                val = Fraction(val, 1)
            elif isinstance(val, float):
                val = Fraction(val).limit_denominator()
            else:
                raise ValueError("计算结果不是有理数")
        return val

    def compute_expression(self, expr: str) -> Fraction:
        expr = expr.replace(' ', '')
        new_expr, nums = self.tokenize_and_replace(expr)
        try:
            result = self.safe_eval(new_expr, nums)
        except Exception:
            raise
        return result


# 最后提供一个简单的命令行接口，保持向后兼容
if __name__ == "__main__":
    evaluator = Base6ExprEvaluator()
    formatter = FractionFormatter()
    s = input("输入表达式: ").strip()
    if not s:
        print("未输入表达式。")
        sys.exit(1)
    try:
        res = evaluator.compute_expression(s)
    except Exception as e:
        print("解析或计算出错：", e)
        sys.exit(1)
    # print(formatter.format_output(res))
    print(formatter.fraction_to_base(res))