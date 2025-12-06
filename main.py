from core import batch_prove, constraints_to_prove, prove

if __name__ == "__main__":
    # prove(["x6 == x5 + x1", "x5 == 2*x1"])
    # batch_prove([["x6 == x5 + x1", "x5 == 2*x1"],
    #              ["x6 == x5 + x3", "x5 == x2 + x3"]], 
    #             allow_breakdown_incompleteness=True)
    for c in constraints_to_prove:
        print(c)
    batch_prove(constraints_to_prove, 
                allow_breakdown_incompleteness=True)