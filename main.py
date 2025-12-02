from core.pipeline import prove, batch_prove, constraints_to_prove

if __name__ == "__main__":
    # prove(["x6 == x5 + x1", "x5 == 2*x1"])
    # print(len(constraints_to_prove))
    # batch_prove([
    #     ["x6 == x5 + x1", "x5 == 2*x1"],
    #     ["x6 == x5 + x3", "x5 == x1 + x4"]
    #     ])
    batch_prove(constraints_to_prove)
