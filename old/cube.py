from fractions import Fraction
import sys
from math import gcd
from functools import reduce
# /e:/vscode_workplace/cube/cube.py

def compute_f(xs, n=None):
    """
    xs: list of 整数 [x1,...,xk]
    返回 f(0..max(xs)) 的有理数列表，满足：
      f(0)=1, f(x<0)=0, k*f(n)=sum_i f(n-xi) for n>0，其中 k = len(xs)
    """
    if not xs:
        return [Fraction(1)]
    # xs = sorted(int(x) for x in xs)
    # k = len(xs)
    # if k == 0:
    #     return [Fraction(1)]
    nmax = n if n is not None else xs[-1]
    f = [Fraction(0)] * (nmax + 1)
    f[0] = Fraction(1)
    for i in range(1, nmax+1):
        s = Fraction(0)
        for xi in xs:
            idx = i - xi
            if idx >= 0:
                s += f[idx]
        f[i] = s / 6
    return f

def input_scaled_integers(parts):
    # parts = input("输入若干数（空格分隔）: ").strip().split()
    try:
        fracs = [Fraction(p) for p in parts]
    except Exception as e:
        print("无法解析输入为分数，请检查输入格式。例：1 2 3 或 0.5 1.25 3/4 ...")
        sys.exit(1)

    dens = [f.denominator for f in fracs]
    lcm = reduce(lambda a, b: a * b // gcd(a, b), dens, 1) if dens else 1
    ints = [int(f * lcm) for f in fracs]

    print("原始分数输入: ", " ".join(str(f) for f in fracs))
    print(f"统一乘以倍数: {lcm} -> 得到整数序列: ", " ".join(str(x) for x in ints))
    return ints, lcm, fracs

# ...existing code...
def fraction_to_base6(frac, base=6, max_frac_digits=60):
    """
    将 Fraction 转为 base-6 字符串，检测循环节。
    结果形如 "10.23(45)_6" 或 "3_6"（若为整数）。
    限制小数位数为 max_frac_digits，超过则以 "..." 结尾。
    """
    if frac == 0:
        return "0_6"
    sign = "-" if frac < 0 else ""
    num = abs(frac.numerator)
    den = frac.denominator

    integer = num // den
    # 整数部分转 base
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

def format_fraction_list(fracs, ints=None):
    # 返回每个 n 的字符串 "n: value"，value 优先以小数显示，若为整数显示整数
    # 若 ints 提供（整数化后的输入序列），在输出中为与序号相同的项标注 x1,x2,...
    labels_by_value = {}
    if ints is not None:
        for idx, val in enumerate(ints):
            labels_by_value.setdefault(int(val), []).append(f"x{idx+1}")

    out = []
    for i, v in enumerate(fracs):
        labels = labels_by_value.get(i, [])
        label_str = (" " + " ".join(labels)) if labels else ""
        if v.denominator == 1:
            out.append(f"{i}: {v.numerator}{label_str}")
        else:
            base6 = fraction_to_base6(v)
            out.append(f"{i}: {float(v):.6f} ({v}) {base6}{label_str}")
    return "\n".join(out)

if __name__ == "__main__":
    if len(sys.argv) > 1:
        parts = sys.argv[1:]
    else:
        parts = input("输入若干数（可为整数、小数或分数字符串，空格分隔）: ").strip().split()

    if len(parts) == 0:
        print("请至少输入一个数。")
        sys.exit(1)

    ints, lcm, fracs_in = input_scaled_integers(parts)

    fracs = compute_f(ints, n=None)
    print(format_fraction_list(fracs, ints))
# ...existing code...