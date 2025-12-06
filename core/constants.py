class Constants:
    ''' 全局常量配置, 请勿更改 '''
    VARIABLE_COUNT = 6  # ✅ 添加变量数
    # RECURSIVE_CLASSIFY函数的最大递归深度，实际会超过10，因此设为30
    MAX_RECURSIVE_CLASSIFY_DEPTH = 30  
    # z3 SMT求解器无法处理无界变量，因此需要一个假设的常量M来约束枚举的上界；
    # 当 LHS > SMT_M * x_i 时，认为 LHS/x_i 无界; 
    SMT_M = 40  
    # F(K, i)(n) 函数的 n 最大值设置；不需要更改，实践会超过15，所以设置为36
    F_N_MAX = 36 
    # solve/batch_solve 函数的最大递归深度设置；不需要更改，必定不超过6
    PIPELINE_MAX_DEPTH = 10  
    # 只考虑 x_{i_min} > x_{i_min-1} 的情况, 其他的都不考虑
    NMAX_LHS = 2

    class Constraints:
        # 变量约束 x6 > x5 > x4 > x3 > x2 > x1 > 0， 所有solver的基础约束
        base_constraints = ["x6 > x5",
                            "x5 > x4",
                            "x4 > x3",
                            "x3 > x2",
                            "x2 > x1",
                            "x1 > 0"]
        # 预测的最优解 [1, 2, 3, 4, 5, 8]的约束
        pred_constraints = [
            "x6 == 8*x1",
            "x5 == 5*x1",
            "x4 == 4*x1",
            "x3 == 3*x1",
            "x2 == 2*x1"
        ]
        # 需要证明的约束列表（不在这列表中的均已数学证明）
        constraints_to_prove = [
            # when x6 == 2*x5
            ["x6 == 2*x5", "x5 == x1 + x1"],
            ["x6 == 2*x5", "x5 == x1 + x2"],
            ["x6 == 2*x5", "x5 == x1 + x3"],
            ["x6 == 2*x5", "x5 == x1 + x4"],    
            ["x6 == 2*x5", "x5 == x2 + x2"],
            ["x6 == 2*x5", "x5 == x2 + x3"],
            ["x6 == 2*x5", "x5 == x2 + x4"],
            ["x6 == 2*x5", "x5 == x3 + x3"],   
            ["x6 == 2*x5", "x5 == x3 + x4"],
            ["x6 == 2*x5", "x5 == x4 + x4"],   
            # when x6 != x_{1-4} + x_{1-4}
            ["x6 == x1 + x1"],
            ["x6 == x1 + x2"],
            ["x6 == x1 + x3"],
            ["x6 == x1 + x4"],
            ["x6 == x2 + x2"],
            ["x6 == x2 + x3"],
            ["x6 == x2 + x4"],
            ["x6 == x3 + x3"],
            ["x6 == x3 + x4"],
            ["x6 == x4 + x4"],
            # when x6 == x5 + x_{1-4}
            ["x6 == x5 + x1"],
            ["x6 == x5 + x2"],
            ["x6 == x5 + x4"],
            # Specailly, when x6 == x5 + x_3
            ["x6 == x5 + x3", "x5 == x1 + x1"],
            ["x6 == x5 + x3", "x5 == x1 + x2"],
            ["x6 == x5 + x3", "x5 == x1 + x3"],
            ["x6 == x5 + x3", "x5 == x1 + x4"],    
            ["x6 == x5 + x3", "x5 == x2 + x2"],
            ["x6 == x5 + x3", "x5 == x2 + x3"],
            ["x6 == x5 + x3", "x5 == x2 + x4"],
            ["x6 == x5 + x3", "x5 == x3 + x3"],   
            ["x6 == x5 + x3", "x5 == x3 + x4"],
            ["x6 == x5 + x3", "x5 == x4 + x4"],    
        ]

if __name__ == "__main__":
    print(Constants.Constraints.base_constraints)
    print(Constants.Constraints.constraints_to_prove)