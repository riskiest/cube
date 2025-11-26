from fractions import Fraction

def f(x, s=None):
    """
    计算 f(x, s) = (s + 2x) / 6
    :param x: 输入值
    :param s: 默认值为 7/36
    :return: 计算结果
    """
    s = s if s is not None else Fraction(7, 36)
    return (s + 2 * x) / 6

def f2(x, s=None):
    """
    计算 f(x, s) = (s + 2x) / 6
    :param x: 输入值
    :param s: 默认值为 7/36
    :return: 计算结果
    """
    s = Fraction(343, 1296)
    return (s + 4 * x) / 6

def f3(x, s=None):
    """
    计算 f(x) = 1 / 36((1.5^x-1))
    :param x: 输入值
    :param s: 默认值为 7/36
    :return: 计算结果
    """
    s =Fraction(3**x, 2**x)
    return 1/(36*(s-1))

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

# ...existing code...

def compute_f_sequence(x, s=None, n=5):
    """
    计算序列：先包含初始 x，然后依次计算 f，返回长度为 n+1 的列表
    返回 [x, f(x), f(f(x)), ..., n 次后的值]
    :param x: 初始值
    :param s: 参数 s，默认 7/36
    :param n: 迭代次数，默认 5
    """
    results = [x]  # 首项为初始值
    for _ in range(n):
        x = f2(x)
        results.append(x)
    return results

def format_results(results):
    """
    格式化输出结果，包括小数、分数和 6 进制表示
    第0项标为 "初始"，其余按次数编号（第1次、第2次...）
    """
    output = []
    for i, result in enumerate(results):
        base6 = fraction_to_base6(result)
        if i == 0:
            label = "初始"
        else:
            label = f"第 {i} 次"
        output.append(f"{label}: {float(result):.6f} ({result}) {base6}")
    return "\n".join(output)

# ...existing code...
if __name__ == "__main__":
    # parts = input("请输入 x 的值（可选 s 的值，空格分隔）: ").strip().split()
    
    # if len(parts) == 0:
    #     print("请至少输入一个数。")
    #     exit(1)

    # try:
    #     x = Fraction(parts[0])
    #     s = Fraction(parts[1]) if len(parts) > 1 else None
    # except ValueError:
    #     print("输入无效，请输入有效的数值。")
    #     exit(1)

    results = compute_f_sequence(Fraction(559, 3888))
    print(results)
    # results = [f3(i) for i in range(1, 6)]
    print(format_results(results))
    results2 = compute_f_sequence(559/3888)
    print(results2)
# ...existing code...