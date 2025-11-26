from z3 import Reals, Optimize, Int, solve, And, unsat, sat
from z3 import simplify, Or, Not, Real, set_option, Solver

x1, x2, x3, x4, x5, x6 = Reals('x1 x2 x3 x4 x5 x6')
y, x = Reals('y x')
s = Solver()
s.add((y==2*x,x==1))

prop = (y==2*x) == (y>x)
s.push()
try:
    s.add(Not(prop))
    result = s.check()
    print(result == unsat)
finally:
    s.pop()

exit()
s.add(x6 > x5,
    x5 > x4,
    x5 > x4,
    x4 > x3,
    x3 > x2,
    x2 > x1,
    x1 > 0,
    x6 == 2*x5,
    x5 == x4 + x3,
    And(Not(x6 - x4*3 > 0), Not(x6 == x4*3)),
    x4 > 1*x3
    )

print(s.assertions())
print(type(s.assertions()))

s.add(x6 > x5,
    x5 > x4,
    x5 > x4,
    x4 > x3,
    x3 > x2,
    x2 > x1,
    x1 > 0,
    x6 == 2*x5,
    x5 == x4 + x3,
    And(Not(x6 - x4*3 > 0), Not(x6 == x4*3)),
    x4 > 1*x3
    )

print(s.assertions())
print(type(s.assertions()))

# s.push()
# # 添加约束 x6 - 4*x3 != 0
# constr = eval("x6 - 4*x3 != 0")
# s.add(constr)

# s.push()
# s.add(Not(x6 - 5*x2 > 0))

# res = s.check()

# s.pop()
# s.pop()
# s.pop()

# 打印s的所有约束
# print(s.assertions())

# for i in range(0, 10):
#     s.push()
#     s.add(Not(x6 - i*x3 > 0))
#     res = s.check()
#     if res == unsat:
#         print("Found i =", i)
#     s.pop()

# for i in range(0, 10):
#     s.push()
#     s.add(Not(x6 - i*x3 == 0))
#     res = s.check()
#     if res == unsat:
#         print("Foundx i =", i)
#     s.pop()


