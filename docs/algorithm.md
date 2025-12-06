# 算法原理

建议先查阅proof.md

## 核心代码

程序的关键代码是求约束下的 $`X`$ 下的值，我们以约束["x6 == 2*x5", "x5 == x3 + x4"]为例

### SMTSolver

我们用z3.solver来处理约束，代码smt.SMTSolver是在z3.solver基础上的封装；
solver = SMTSolver(text_constraints=["x6 == 2*x5", "x5 == x3 + x4"])，实际输出约束是

```
[1] x6 > x5  
[2] x5 > x4  
[3] x4 > x3  
[4] x3 > x2  
[5] x2 > x1  
[6] x1 > 0  
[7] x6 == 2*x5  
[8] x5 == x3 + x4  
```

### Breakdown

定义LHS=x6，j_min=6, 以 $`x_{j_{\min}-1},...,x_j,...,x_1`$ 为序，逐个寻找使得LHS/ $`x_j`$ 有界的最小的j，记下 $`i_{\min}:=j, i:=i_{\min}-1`$; 
注意z3.solver无法判断是否有界，因此我们定义了常数SMT_M=40, 若有LHS>SMT_M * $`x_j`$, 我们即认为 $`x_j`$ 无界；

然后对于每个 $`x_j`$ ($`j\ge i_{\min}`$), 计算最大 $`k_j`$, 使得 $`\text{LHS}\ge k_j \cdot x_j`$; 然后在 $`\prod_{j=i_{\min}}^{j_{\min}-1} [0, k_j]`$ 的系数空间中，计算 $`\text{LHS}-(\sum(k_j \cdot x_j))>0`$ 或 $`\text{LHS}-(\sum(k_j \cdot x_j))=0`$ 是否被蕴含(entailed)或可满足(satisfiable)；如果被蕴含，说明这条BreakdownNode无需额外约束，而如果是可满足，意味着这条BreakdownNode需要额外的约束，$`\text{LHS}-(\sum(k_j \cdot x_j))>0`$ 或 $`=0`$ 才能被满足，因此我们直接添加 $`\text{LHS}-(\sum(k_j \cdot x_j))>0`$ 或 $`=0`$ 为新的约束；

通过上面，我们可获得BreakdownNodes

```
[1]x6 - 0 > Σ(3), when []  
[2]x6 - x4*1 > Σ(3), when []  
[3]x6 - x4*2 > Σ(3), when []  
[4]x6 - x4*3 > Σ(3), when [x6 - x4*3 > 0]  
[5]x6 - x4*3 = 0, when [x6 - x4*3 == 0]  
[6]x6 - x5*1 > Σ(3), when []  
[7]x6 - (x5*1 + x4*1) > Σ(3), when []  
[8]x6 - x5*2 = 0, when []  
```

对于[3], 知道LHS=x6 - x4\*2 = 2\*x\*3, 可知LHS/x3=2有界，因此Breakdown可以继续进行，定义j_min=i_min, 重新代入上面的过程，分解成BreakdownTree

```
Root:
  x6 > Σ(5), when []
    > x6 - 0 > Σ(3), when []
    > x6 - x4*1 > Σ(3), when []
    > x6 - x4*2 > Σ(3), when []
      > x6 - x4*2 - 0 > Σ(2), when []
      > x6 - x4*2 - x3*1 > Σ(2), when []
      > x6 - x4*2 - x3*2 = 0, when []
    > x6 - x4*3 > Σ(3), when [x6 - x4*3 > 0]
      > x6 - x4*3 - 0 > Σ(2), when [x6 - x4*3 > 0]
    > x6 - x4*3 = 0, when [x6 - x4*3 == 0]
    > x6 - x5*1 > Σ(3), when []
    > x6 - (x5*1 + x4*1) > Σ(3), when []
      > x6 - (x5*1 + x4*1) - 0 > Σ(2), when []
      > x6 - (x5*1 + x4*1) - x3*1 = 0, when []
    > x6 - x5*2 = 0, when []

```

以上是smt.SMTSolver.new_decompose函数的内容；

将BreakdownTree用约束来分类，如上面的约束可以分成以下3类

```
[x6 - x4*3 > 0]
[x6 - x4*3 == 0]
[NOT(x6 - x4*3 > 0), NOT(x6 - x4*3 == 0)]
```

由此我们获得3个solver，以及它们的BreakdownNodes, 在程序中有专门的数据结构partition.Partition；

如果Breakdown到此为止，我们称作不完全分解（breakdown_incompleteness）；用此种分解的代码速度很快，因为后续的优化计算可以很快的砍掉不必要的约束，大大节省计算时间；但由于是不完全分解，它的上限较大，对于非常棘手的约束，程序会因为上限过于宽松而无法进行下去；

完全分解，在上面的过程中，新的约束，如[x6 - x4*3 == 0]，它只作用于BreakdownTree的有着相同约束的BreakdownNodes上，当它成为新的solver时，其他的BreakdownNodes也应受到约束而有了继续Breakdown的可能；因此，需要新solver需要递归上面的过程，重新生成BreakdownTree，重新分组生成新的solver；直到无法继续分解为止，此时BreakdownTree上的所有节点都没有引入新的约束；

如果程序全部使用完全分解，在我的电脑上运行时间是58397.61s\~16.2h，而如果我们只对[1,2,3,4,5,8]可满足的约束使用完全分解，则程序的运行时间为544.25s\~9.1min

### 计算 $`\theta(X)`$

F.py提供了BreakdownNode的 $`\mathcal{F}_{K, i}(n)`$-上限的实现；

对partition的所有BreakdownNodes计算，所有的BreakdownNodes都是"LHS=0"的样子，则 $`\theta(X)`$ 可计算；否则，可以计算BreakdownNodes的上限；lower上限是 $`\mathcal{F}_{K, i}(n)`$，使用它作为计算，会引入新的约束，约束的数量是BreakdownNode的深层属性combo；upper上限是 $`\mathcal{F}_{K, i}(n-1)`$, 使用它作为上限不会引入新的约束；

$`\theta(X)`$ 与基准值 $`\theta([1,2,3,4,5,8])`$ 进行比较

```
θ(X)计算值或上限小于基准值：✂️ Pruned, 剪枝
θ(X)可计算，大于等于基准值：✅ Success, 返回
θ(X)lower上限大于基准值：🔄 报错
θ(X)lower上限小于等于基准值，upper上限大于等于基准值：🌳 Split, 分蘖
    1. 通过每个BreakdownNode的lower或upper进行选择，尽可能的引入更少的约束，使用pulp实现；
    2. 每个约束都与该solver叠加，重新进入Breakdown过程（递归）;
```

### 程序运行结果

allow_breakdown_incompleteness==False

```
------------------------------------------------------------------------------------------------------------
No.   Solver ID                      Status     Partitions      Solvers    Success    Verified     Time(s)   
------------------------------------------------------------------------------------------------------------
1     x6eq2mx5&x5eqx1px1_0           failed     111/265         0          0          N/A          30.00     
2     x6eq2mx5&x5eqx1px2_0           failed     157/368         0          0          N/A          48.62     
3     x6eq2mx5&x5eqx1px3_0           failed     214/479         1          0          N/A          90.51     
4     x6eq2mx5&x5eqx1px4_0           failed     404/847         28         0          N/A          317.50    
5     x6eq2mx5&x5eqx2px2_0           failed     8378/17976      1265       0          N/A          4367.59   
6     x6eq2mx5&x5eqx2px3_0           failed     5209/10587      1572       0          N/A          2800.24   
7     x6eq2mx5&x5eqx2px4_0           failed     30679/62995     7346       0          N/A          42804.34  
8     x6eq2mx5&x5eqx3px3_0           failed     1143/2403       84         0          N/A          1321.94   
9     x6eq2mx5&x5eqx3px4_0           failed     862/1824        12         0          N/A          1618.40   
10    x6eq2mx5&x5eqx4px4_0           failed     1488/3144       73         0          N/A          2092.85   
11    x6eqx1px1_0                    failed     1/1             0          0          N/A          0.10      
12    x6eqx1px2_0                    failed     1/1             0          0          N/A          0.11      
13    x6eqx1px3_0                    failed     1/1             0          0          N/A          0.10      
14    x6eqx1px4_0                    failed     1/1             0          0          N/A          0.09      
15    x6eqx2px2_0                    failed     2/2             1          0          N/A          0.20      
16    x6eqx2px3_0                    failed     2/2             1          0          N/A          0.21      
17    x6eqx2px4_0                    failed     6/6             5          0          N/A          0.90      
18    x6eqx3px3_0                    failed     7/9             5          0          N/A          1.02      
19    x6eqx3px4_0                    failed     30/40           22         0          N/A          7.17      
20    x6eqx4px4_0                    success    977/2025        197        12         12/12        288.88    
21    x6eqx5px1_0                    failed     72/132          28         0          N/A          15.87     
22    x6eqx5px2_0                    failed     75/145          24         0          N/A          18.63     
23    x6eqx5px4_0                    failed     4454/9360       383        0          N/A          2473.45   
24    x6eqx5px3&x5eqx1px1_0          failed     8/19            0          0          N/A          1.83      
25    x6eqx5px3&x5eqx1px2_0          failed     19/46           0          0          N/A          5.00      
26    x6eqx5px3&x5eqx1px3_0          failed     19/36           6          0          N/A          4.68      
27    x6eqx5px3&x5eqx1px4_0          success    21/37           8          1          1/1          6.49      
28    x6eqx5px3&x5eqx2px2_0          failed     12/17           8          0          N/A          2.39      
29    x6eqx5px3&x5eqx2px3_0          success    13/19           8          2          2/2          3.12      
30    x6eqx5px3&x5eqx2px4_0          failed     91/176          30         0          N/A          30.45     
31    x6eqx5px3&x5eqx3px3_0          failed     123/241         31         0          N/A          38.90     
32    x6eqx5px3&x5eqx3px4_0          failed     13/23           5          0          N/A          3.50      
33    x6eqx5px3&x5eqx4px4_0          failed     1/1             0          0          N/A          0.16
------------------------------------------------------------------------------------------------------------
```

allow_breakdown_incompleteness==True

```
------------------------------------------------------------------------------------------------------------
No.   Solver ID                      Status     Partitions      Solvers    Success    Verified     Time(s)   
------------------------------------------------------------------------------------------------------------
1     x6eq2mx5&x5eqx1px1_0           failed     17/17           0          0          N/A          0.61      
2     x6eq2mx5&x5eqx1px2_0           failed     14/14           0          0          N/A          0.58      
3     x6eq2mx5&x5eqx1px3_0           failed     10/10           1          0          N/A          0.48      
4     x6eq2mx5&x5eqx1px4_0           failed     86/86           31         0          N/A          14.67     
5     x6eq2mx5&x5eqx2px2_0           failed     65/65           7          0          N/A          4.50      
6     x6eq2mx5&x5eqx2px3_0           failed     11/11           0          0          N/A          0.62      
7     x6eq2mx5&x5eqx2px4_0           failed     128/128         35         0          N/A          44.89     
8     x6eq2mx5&x5eqx3px3_0           failed     237/237         44         0          N/A          49.52     
9     x6eq2mx5&x5eqx3px4_0           failed     3/3             0          0          N/A          0.14      
10    x6eq2mx5&x5eqx4px4_0           failed     261/261         15         0          N/A          46.66     
11    x6eqx1px1_0                    failed     1/1             0          0          N/A          0.04      
12    x6eqx1px2_0                    failed     1/1             0          0          N/A          0.04      
13    x6eqx1px3_0                    failed     1/1             0          0          N/A          0.04      
14    x6eqx1px4_0                    failed     1/1             0          0          N/A          0.03      
15    x6eqx2px2_0                    failed     2/2             1          0          N/A          0.10      
16    x6eqx2px3_0                    failed     2/2             1          0          N/A          0.10      
17    x6eqx2px4_0                    failed     6/6             5          0          N/A          0.59      
18    x6eqx3px3_0                    failed     7/7             5          0          N/A          0.63      
19    x6eqx3px4_0                    failed     30/30           22         0          N/A          3.83      
20    x6eqx4px4_0                    success    977/2025        197        12         12/12        232.81    
21    x6eqx5px1_0                    failed     49/49           28         0          N/A          3.87      
22    x6eqx5px2_0                    failed     52/52           24         0          N/A          4.32      
23    x6eqx5px4_0                    failed     1039/1039       291        0          N/A          112.42    
24    x6eqx5px3&x5eqx1px1_0          failed     4/4             0          0          N/A          0.17      
25    x6eqx5px3&x5eqx1px2_0          failed     3/3             0          0          N/A          0.16      
26    x6eqx5px3&x5eqx1px3_0          failed     19/19           6          0          N/A          1.36      
27    x6eqx5px3&x5eqx1px4_0          success    21/37           8          1          1/1          5.47      
28    x6eqx5px3&x5eqx2px2_0          failed     12/12           8          0          N/A          1.26      
29    x6eqx5px3&x5eqx2px3_0          success    13/19           8          2          2/2          2.59      
30    x6eqx5px3&x5eqx2px4_0          failed     23/23           9          0          N/A          2.22      
31    x6eqx5px3&x5eqx3px3_0          failed     72/72           21         0          N/A          7.06      
32    x6eqx5px3&x5eqx3px4_0          failed     21/21           3          0          N/A          2.25      
33    x6eqx5px3&x5eqx4px4_0          failed     1/1             0          0          N/A          0.05
------------------------------------------------------------------------------------------------------------
```
