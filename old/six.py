from fractions import Fraction
import re, ast, sys

def fraction_to_base6(frac: Fraction, base=6, max_frac_digits=60):
    if frac == 0:
        return "0_6"
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
        return f"{sign}{int_str}_6"

    seen = {}
    frac_digits = []
    idx = 0
    repeat_index = None
    while remainder != 0 and idx < max_frac_digits:
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

    return f"{sign}{int_str}.{frac_part}_6"

def parse_base6_to_fraction(s: str) -> Fraction:
    # s like "123.45" in base-6 (no suffix)
    if '.' in s:
        int_part, frac_part = s.split('.', 1)
    else:
        int_part, frac_part = s, ""
    if int_part == "":
        int_val = 0
    else:
        int_val = 0
        for ch in int_part:
            if not ch.isdigit():
                raise ValueError("非法的 base-6 数字")
            d = int(ch)
            if d >= 6:
                raise ValueError("非法的 base-6 数字")
            int_val = int_val * 6 + d
    if frac_part == "":
        return Fraction(int_val, 1)
    else:
        k = len(frac_part)
        frac_val = 0
        for i, ch in enumerate(frac_part, start=1):
            if not ch.isdigit():
                raise ValueError("非法的 base-6 小数数字")
            d = int(ch)
            if d >= 6:
                raise ValueError("非法的 base-6 小数数字")
            frac_val = frac_val * 6 + d
        numer = int_val * (6 ** k) + frac_val
        denom = 6 ** k
        return Fraction(numer, denom)

_NUM_RE = re.compile(r'[0-9]+(?:\.[0-9]+)?(?:_6|_10)?')

def tokenize_and_replace(expr: str):
    parts = []
    nums = {}
    last = 0
    idx = 0
    for m in _NUM_RE.finditer(expr):
        start, end = m.span()
        parts.append(expr[last:start])
        tok = m.group(0)
        name = f"__N{idx}__"
        # compute Fraction value
        if tok.endswith("_6"):
            core = tok[:-2]
            val = parse_base6_to_fraction(core)
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

class ValidateExpr(ast.NodeVisitor):
    def __init__(self, allowed_names):
        self.allowed_names = set(allowed_names)
    def generic_visit(self, node):
        # allow only specific node types
        allowed = (ast.Expression, ast.BinOp, ast.UnaryOp, ast.Name,
                   ast.Load, ast.Add, ast.Sub, ast.Mult, ast.Div,
                   ast.USub, ast.UAdd, ast.Pow, ast.Mod, ast.FloorDiv,
                   ast.Constant, ast.Call, ast.Tuple, ast.List, ast.Subscript)
        # explicitly disallow risky nodes
        if isinstance(node, ast.Call) or isinstance(node, ast.Attribute) or isinstance(node, ast.Assign):
            raise ValueError("不允许的表达式元素")
        super().generic_visit(node)
    def visit_Name(self, node):
        if node.id not in self.allowed_names:
            raise ValueError(f"不允许的变量: {node.id}")

def safe_eval(expr: str, names: dict) -> Fraction:
    # parse and validate AST allowing only arithmetic with provided names and unary +/-.
    node = ast.parse(expr, mode='eval')
    # simple validator: ensure no Names except our placeholders
    class Validator(ast.NodeVisitor):
        ALLOWED = (ast.Expression, ast.BinOp, ast.UnaryOp, ast.Name, ast.Load,
                   ast.Add, ast.Sub, ast.Mult, ast.Div, ast.UAdd, ast.USub,
                   ast.Constant, ast.Mod, ast.FloorDiv, ast.Pow, ast.Expr, ast.Tuple, ast.List)
        def visit(self, node):
            if not isinstance(node, self.ALLOWED):
                raise ValueError(f"不允许的表达式元素: {type(node).__name__}")
            return super().visit(node)
        def visit_Name(self, node):
            if node.id not in names:
                raise ValueError(f"不允许的变量: {node.id}")
    Validator().visit(node)
    code = compile(node, '<expr>', 'eval')
    # evaluate with names as locals, no builtins
    val = eval(code, {"__builtins__": None}, names)
    if not isinstance(val, Fraction):
        # convert int/float to Fraction
        if isinstance(val, int):
            val = Fraction(val, 1)
        elif isinstance(val, float):
            val = Fraction(val).limit_denominator()
        else:
            raise ValueError("计算结果不是有理数")
    return val

def compute_expression(expr: str) -> Fraction:
    expr = expr.replace(' ', '')
    new_expr, nums = tokenize_and_replace(expr)
    # names dict should map placeholder names to Fraction values
    # Ensure names are valid identifiers
    try:
        result = safe_eval(new_expr, nums)
    except Exception as e:
        raise
    return result

def format_output(result: Fraction):
    if result.denominator == 1:
        base6 = fraction_to_base6(result)
        return f"整数: {result.numerator}\n6进制: {base6}"
    else:
        dec = float(result)
        base6 = fraction_to_base6(result)
        return f"十进制(浮点): {dec:.6f}\n十进制(分数): {result}\n6进制: {base6}"

if __name__ == "__main__":
    s = input("输入表达式: ").strip()
    if not s:
        print("未输入表达式。")
        sys.exit(1)
    try:
        res = compute_expression(s)
    except Exception as e:
        print("解析或计算出错：", e)
        sys.exit(1)
    print(format_output(res))