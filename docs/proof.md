# Proof

$$
\max_{X \in \mathbb{X}} \max_{x \in \mathbb{R}^+} f_X(x)
$$

$$
\text{s.t.}\quad \begin{cases}
\mathbb{X} = \left\\{ (x_1, x_2, \dots, x_6) \in \mathbb{R}^6 \mid 0 < x_1 < x_2 < \dots < x_6 \right\\}, \\
f_X(x) = \begin{cases} 
0, & x < 0, \\
1, & x = 0, \\
\displaystyle\frac{1}{6} \sum_{i=1}^6 f_X(x - x_i), & x > 0 
\end{cases}
\end{cases}
$$

## 定理1：Breakdown
define:

$$
K_X(x)=\{ (k_1, \dots, k_6) |x=\sum_{i=1}^{6}k_ix_i, \forall \, 1 \leq i \leq 6, k_i \in  \mathbb{N} \}
$$

then:

$$
f_X(x)|_{x>0}=\sum_{(k_1, \dots, k_6)\in K_X(x)}\frac{\binom{\sum_{i=1}^{6}{k_i}}{k_1, k_2, \dots, k_6} }{6^{\sum_{i=1}^{6}{k_i} } }
$$

显然。■

## 定理2：
对于 $`a>0`$，设 $`aX=\{ ax_1, \dots, ax_6 \}`$，则

$$
f_{aX}(ax)=f_X(x)
$$

显然。■

## 定理3：
$`\forall X, \forall x>0 \text{ (fixed)},\exist X' = \{ x_1, \dots, x_6 \in \mathbb{Q}^+ \bigm| \forall \, 1 \leq i \neq j \leq 6,\ x_i \neq x_j \}`$ 

有

$$
f_{X'}(1)\geq f_{X}(x)
$$

证明：
由定理2，$`f_{x^{-1}X}(1)=f_{X}(x)`$, 因此这里简化符号，直接设 $`x=1`$;

若 $`X`$ 的元素全为有理数，令 $`X'=X`$，成立；

否则对 $`(k_1, \dots, k_6)\in K_X(x)`$，列方程组 $`1=x=\sum_{i=1}^{6}k_ix_i`$，整理为 $`KX_c=1`$，其中 $`X_c=(x_1, \dots, x_6)^T`$.

如果 $`K`$ 满秩，则 $`X_c`$ 必然为有理解；
若 $`K`$ 不满秩，根据无理数的稠密性，必然存在有理解 $`X_c'=(x_1', \dots, x_6')^T`$ 使得 $`KX_c=1`$ 成立。事实上，设原解基为 $`(x_{i1},x_{i2},...)`$，令 $`x_{ij}'`$ 取为 $`x_{ij}`$ 邻域内的随机有理数，则得到的解便是有理解，缩小邻域，直到该有理解全为正。根据定理1，此时 $`f_{X'}(1)\ge f_{X}(1)`$; 得证。■

若 $`t=\arg\max_{x} f_X(x)`$, 则 $`\max f_{X'}\ge \max f_{X'}(1) \ge f_{X}(t)`$, 意味着无论 $`X`$, 均存在元素均为有理数的解的最值不小于 $`X`$，根据定理2，意味着存在均为整数的解。因此在后续的讨论中，设 $`x_1,\dots,x_6`$ 均为正整数。即重新定义
$`\mathbb{X} = \left\{ (x_1, x_2, \dots, x_6) \in \mathbb{Z}^6 \mid 0 < x_1 < x_2 < \dots < x_6 \right\}`$

## 定理4：
引理4.1
令 $`t=\min(\arg\max_{x} f_X(x))`$, 则 $`t\le x_6`$ 

证明：根据递推公式 $`f_X(t) = \frac{1}{6} \sum_{i=1}^{6} f(t - x_i)`$，若 $`t>x_6`$，则必然存在某 $`t - x_i>0`$，使得 $`f(t - x_i)\geq f(t)`$，矛盾，因此 $`t\le x_6`$

定理4：
如果 $`X`$ 有 $`t\ne x_6`$,则存在 $`X'`$,使得 $`\max(f_{X'})\ge \max(f_{X})`$;

证明：若 $`t<x_6`$,则定理1中的 $`k_6`$ 始终为0，令 $`x_6'=t/n`$，取 $`n`$ 使得 $`x_6'\notin \{x_1,\dots,x_5\}`$，则新的 $`X' = \{ x_1,\dots,x_5,x_6' \}`$ 满足 $`f_{X'}(t)>f_X(t)`$。得证。■

根据定理4，我们仅需考虑 $`t=x_6`$ 的情况。也就是 $`x_6`$ 是 $`X`$ 的最大值点。

## 定理5：

$$
x_6=x_i+x_j,\quad 1\leq i,j \leq 5
$$

此处省去了如果 $`X`$ 不满足 $`x_6=x_i+x_j`$, 则存在 $`X'`$, 使得 $`\max(f_{X'})\ge \max(f_{X})`$ 这样的描述；

证明：
$`f(x_6)=\frac{1}{6}(1+\sum_{i=1}^{5}f(x_6-x_i))`$; 其中 $`f(x_6-x_i)`$ 与 $`x_6`$ 无关，由于 $`f(x_6)`$ 最大，则若 $`x_1\sim x_5`$ 固定的话，$`x_6`$ 应该是 $`f'(t)=\frac{1}{6}\sum_{i=1}^{5}f'(t-x_i)`$ 中取最大值。

带入 $`t=x_6`$，可知至少有一个 $`f'(x_6-x_i)\gt f'(x_6)`$，如果 $`x_6-x_i\notin \{x_1,\dots,x_5\}`$ 则可由它取代 $`x_6`$. 因此 $`x_6-x_i\in \{x_1,\dots,x_5\}`$，得证。■

我们获得了第一个约束集 $`x_6=x_i+x_j,\quad 1\leq i,j \leq 5`$; 

为了简化，引入符号：

$$
\begin{align*}
x_{1-i}&=\{x_1,\dots,x_i \} \\
nx_{1-i}&=\{ \sum_{k=1}^{n}y_k|y_k\in \{x_1,\dots,x_i\} \} \\
x_6=nx_{1-i} &\Rightarrow \exist x \in nx_{1-i}, x_6 = x \\
x_6\le nx_{1-i} &\Rightarrow \exist x \in nx_{1-i}, x_6\le x \\
x_6\ne nx_{1-i} &\Rightarrow \nexists x \in nx_{1-i}, x_6= x
\end{align*}
$$

因此，这个约束集后面可以简写为 $`x_6=2x_{1-5}`$; 它实际包含了

> [$`x_6 = x_1 + x_1`$]  
> [$`x_6 = x_1 + x_2`$]  
> [$`x_6 = x_1 + x_3`$]  
> [$`x_6 = x_1 + x_4`$]  
> [$`x_6 = x_1 + x_5`$]  
> [$`x_6 = x_2 + x_2`$]  
> [$`x_6 = x_2 + x_3`$]  
> [$`x_6 = x_2 + x_4`$]  
> [$`x_6 = x_2 + x_5`$]  
> [$`x_6 = x_3 + x_3`$]  
> [$`x_6 = x_3 + x_4`$]  
> [$`x_6 = x_3 + x_5`$]  
> [$`x_6 = x_4 + x_4`$]  
> [$`x_6 = x_4 + x_5`$]  
> [$`x_6 = x_5 + x_5`$]

15个约束

## 关于 $`x_6<2x_5`$：
对于 $`x_6<2x_5`$, 将 $`x_6`$ 按定理1进行拆解：

$$
\begin{align*}
x_6&=x_6 \\
x_6&=x_5+\Sigma_{1-4} \\
x_6&=\Sigma_{1-4}
\end{align*}
$$

在继续讨论之前，先厘清一些概念
### Breakdown

程序中将拆解称作Breakdown，拆解后每一行是一个BreakdownNode，整个拆解结果称为Partition；上面的等式就是在约束constraints=[$`x_6<2x_5`$]下对 $`x_6`$ 进行的Breakdown，拆解生成一个Partition，它由3个BreakdownNode组成。

根据定理1，每个BreakdownNode贡献一个值 $`\sigma`$；$`\max_{x} (f_X(x))=f_X(x_6)\stackrel{\text{def}}{=} \theta(X)`$ 的值就等于这些值之和；比如

$`\sigma(1)=\sigma(x_6=x_6)=\frac{\binom{\sum_{i=1}^{6}{k_i}}{k_1, k_2, \dots, k_6} }{6^{\sum_{i=1}^{6}{k_i} } }=1/6=0.1_6`$

$`\theta(X)=\sigma(1)+\sigma(2)+\sigma(3)`$

其中 $`0.1_6`$ 为6进制，在这个问题上使用特别方便；
$`\Sigma_{1-4}`$ 是一个可以表达为 $`\sum_{j=1}^{4}{k_jx_j}`$, 它实际由许多BreakdownNode组成，但具体的表达在不同的约束下可能不一样；介于目前的约束，式子(2),(3)的Breakdown只能达到这个程度, 因此，我们无法计算 $`\sigma(2)`$ 和 $`\sigma(3)`$，但我们可以计算它的一个上限；

### 扩展 $`f_X`$

$`f`$ 可以定义在 $`\mathbb{R}^6`$, 也可以扩展定义在 $`\mathbb{R}^5,\dots,\mathbb{R}^1`$ 上，对于 $`\mathbb{R}^m`$, 有

$$
f_{x_{1-m}}(x)|_{x>0}=\frac{1}{6}\sum_{p=1}^{m}f_{x_{1-m}}(x-x_p)
$$

### 继续讨论

固定 $`x_{1-4} \cup \{x_6-x_5\}`$, 则上式1和2固定，因此 $`x_6=\arg\max_{x>x_4}f(x)`$, 定义 $`h=f_{x_{1-4}}`$, 由于

$`h(x_6)=\frac{1}{6}\sum_{p=1}^{4}h(x_6-x_p)`$

必然有 $`h(x_6-x_{1-4}>0)>h(x_6)`$, 说明必然有以下几种情况：

#### case0: 

$`x_6-x_{1-4} = x_{1-4} \Rightarrow x_6=2x_{1-4}`$，此时 $`x_6-x_{1-4}`$ 落在 $`x_{1-4}`$ 上，无法替代 $`x_6`$

#### case1:

$`x_5-x_{1-4} = x_{1-4} \Rightarrow x_5=2x_{1-4}`$，此时 $`x_5-x_{1-4}`$ 落在 $`x_{1-4}`$ 上，无法替代 $`x_5`$, 此时 $`x_6=x_{1-5}+x_{1-4}`$

因此获得2个新的约束集

> [$`x_6 = 2x_{1-4}`$]  
> [$`x_5 = 2x_{1-4}, x_6=x_5+x_{1-4}`$]  

### 表达式、约束、约束集

注意，一个约束constraints如[$`x_5 = x_2 + x_3, x_6= x_5 + x_1`$]通常由很多表达式expression组成，如上个约束便由2个表达式组成；而一个约束集就是由约束组成的list，比如：

[<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;[$`x_6 = 2x_5`$],<br>
&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;&nbsp;[$`x_5 = x_2 + x_3, x_6= x_5 + x_1`$]<br>
]

## 关于 $`x_6=2x_5`$：

Breakdown $`x_6`$

$$
\begin{align*}
x_6&=x_6, \quad \sigma(1)= 0.1_6  \\
x_6&=2x_5 , \quad \sigma(2)= 0.01_6\\
x_6&=x_5+\Sigma_{1-4}, \quad \sigma(3)= g_6\\
x_6&=\Sigma_{1-4}, \quad \sigma(4)= h_6
\end{align*}
$$

### (4)项

如果 $`s=\Sigma_{1-4}`$, 则

> $`f(s)\le 1`$, if $`[True]`$  
> $`f(s)\le \max_{X}\theta(X) = \theta([1, 2, 3, 4])\stackrel{\text{def}}{=} \theta_4`$, if $`[s\ne 0]`$; $`\max_{X}\theta(X) = \theta([1, 2, 3, 4])`$ can be proven;  
> $`f(s)=\frac{1}{6}\sum_{j=1}^{4} f(s-x_j)\le \frac{2}{3}f(s-x_{1-4}) \le \frac{2}{3}\theta_4`$, if $`[s>0, s\ne x_{1-4}]`$  
> $`f(s)\le \frac{2}{3}f(s-x_{1-4})\le \frac{4}{9}f(s-x_{2({1-4})}) \le \frac{4}{9}\theta_4`$, if $`[s>x_4, s\ne 2x_{1-4}]`$  
> $`\dots`$  

在不同条件下，定义上式的上限为 $`\mathcal{F}`$, 计算上限可以把不等式变成等式；但对于目前讨论的内容，$`\mathcal{F}`$-上限仍然不够用；需要寻找更低的上限；

仍然定义 $`h=f_{\{x_1,\dots,x_4\}}`$, 固定 $`x_{1-4} \cup \{x_6-x_5\}`$, 则(1),(3)固定，而 $`x_6`$ 减少时(2)被破坏, 因此有

$`\theta([x_1,\dots,x_6])\geq \theta([x_1,\dots,x_4,x_5-x_{1-4},x_6-x_{1-4}]) \Rightarrow h(x_6-x_{1-4})-h(x_6)\le 0.01_6`$, if $`[x_5\ne 2x_{1-4}]`$

而
$`h(x_6)\le \frac{2}{3}h(x_6-x_{1-4})`$

因此
$`0.5h(x_6)\le h(x_6-x_{1-4})-h(x_6) \le 0.01_6 \Rightarrow h(x_6)\le 0.02_6`$

### (3)项

引入新的简化符号，$`f_i := f(x_i)`$

$`x_6=x_5+\sum_{1-4}`$, 可以定义 $`x_{1-5}'=x_{1-4}\cup\{x_5'\},x_5'\in (\mathbb{R}^+-\mathbb{Q}^+)`$，令 $`x_6'-x_5'=x_6-x_5`$, 定义 $`g=f_{x_{1-5}'}`$  则 $`g_{6'}=g_6`$

设 $`t=\min(\arg\max_{x\in x_5'+\mathbb{Z}^+}(g'(x)))`$，现在证明 $`g(t)<g_{5'}=1/6`$

如果 $`g(t)\ge g_{5'}`$, 则 $`g(t)=\max_{x\in x_5'+\mathbb{Z}}(g(x))`$, 则

$`6g(t)=g(t-x_5')+\sum_{i=1}^{4}g(t-x_i)\Rightarrow 2g(t)<g(t-x_5')=h(t-x_5')\le \max(h)\le\theta([1,2,3,4])=0.1331_6\Rightarrow g(t)<0.04433_6`$

与 $`g(t)\ge g_{5'}=0.1_6`$,矛盾，因此 $`g(t)< g_{5'}=0.1_6`$

重新把 $`g(t)< g_{5'}=0.1_6`$ 代回去，则 $`g(t-x_i)`$ 中最多一个与 $`g_5'`$ 相同，则有 $`3g(t)-0.1_6<0.1331_6\Rightarrow g(t)\lt 0.05102_6`$

这可以作为 $`g_{6'}`$ 的估值起点；

$$
\begin{align*}
\text{when } &C_9(n) =\{x_6'-x_5'>nx_4, x_6'-x_5' \ne (n+1)x_{1-4} \} \cup \{x_6'-x_5'\ge nx_4, x_6'-x_5'\ne (n+1)x_{1-4} \}\\ 
& =\{x_6'-x_5'>nx_4, x_6'-x_5' \ne (n+1)x_{1-4} \}\\
\text{then } & g_{6'-k(1-4)} \le (g_{(6'-5')-k(1-4)}+3g_{6'-(k+1)(1-4)})/6  \\
& \le(1.5^{-(n+1-k)}h_{(6'-5')-(n+1)(1-4)}+3g_{6'-(k+1)(1-4)})/6,  (k=0,\dots,n) \\
&\implies \{x_6'>kx_4\}\cup \{x_6'-x_4'>nx_4, x_6'-x_4'\ne (n+1)x_{1-4} \} \\
\text{Bound: } &h_{(6'-5')-(n+1)(1-4)} \le \max(h), g_{6'-(n+1)x_{1-4}}\le \max(g); \\
&\implies \{x_6'-x_5'\ne (n+1)x_{1-4} \}\cup \{x_6'-x_5'\ne (n+1)x_{1-4} \}
\end{align*}
$$

### 和式

$`g_6 \le 0.0341344_6`$, if [$`x_6'-x_5'>x_4, x_6'-x_5'\neq 2x_{1-4}`$]

可知，当[$`x_5>x_4, x_5\ne 2x_{1-4}`$]时，$`\theta(X)\le 0.02_6+0.0341344_6+0.11_6=0.2041344_6<\theta([1,2,3,4,5,8])`$; 因此，为了使得能成为候选最优解，需要越是[$`x_5=2x_{1-4}`$] ($`x_5>x_4`$ 恒成立)。

## 总结

通过对2种情况的分析，我们可以将证明过程转化成以下几种约束下的 $`X`$ 的证明

> when $`x_6 = 2x_5`$  
> $`\left[ x_6 = 2x_5,\ x_5 = x_1 + x_1 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_1 + x_2 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_1 + x_3 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_1 + x_4 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_2 + x_2 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_2 + x_3 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_2 + x_4 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_3 + x_3 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_3 + x_4 \right]`$,  
> $`\left[ x_6 = 2x_5,\ x_5 = x_4 + x_4 \right]`$,  
> when $`x_6 \neq x_{1-4} + x_{1-4}`$  
> $`\left[ x_6 = x_1 + x_1 \right]`$,  
> $`\left[ x_6 = x_1 + x_2 \right]`$,  
> $`\left[ x_6 = x_1 + x_3 \right]`$,  
> $`\left[ x_6 = x_1 + x_4 \right]`$,  
> $`\left[ x_6 = x_2 + x_2 \right]`$,  
> $`\left[ x_6 = x_2 + x_3 \right]`$,  
> $`\left[ x_6 = x_2 + x_4 \right]`$,  
> $`\left[ x_6 = x_3 + x_3 \right]`$,  
> $`\left[ x_6 = x_3 + x_4 \right]`$,  
> $`\left[ x_6 = x_4 + x_4 \right]`$,  
> when $`x_6 = x_5 + x_{1-4}`$  
> $`\left[ x_6 = x_5 + x_1 \right]`$,  
> $`\left[ x_6 = x_5 + x_2 \right]`$,  
> $`\left[ x_6 = x_5 + x_4 \right]`$,  
> Specailly, when $`x_6 = x_5 + x_3`$  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_1 + x_1 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_1 + x_2 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_1 + x_3 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_1 + x_4 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_2 + x_2 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_2 + x_3 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_2 + x_4 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_3 + x_3 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_3 + x_4 \right]`$,  
> $`\left[ x_6 = x_5 + x_3,\ x_5 = x_4 + x_4 \right]`$,  

这就是程序需要证明的约束集

## $`\mathcal{F}`$
$`\mathcal{F}`$ 上限是针对下面公式给出的一种上限：

$$
x_6=k_5x_5+\dots+k_{i+1}x_{i+1}+\Sigma_{1-i}
$$

记作 $`\mathcal{F}_{K, i}(n),K=(k_5, k_4, \dots, k_{i+1})\in (\mathbb{Z}^{+})^{5-i},5\ge i\ge1`$, $`\mathcal{F}`$ 关于 $`K`$ 是对称函数，其中 $`n\ge-2`$, 以下是 $`n`$ 的含义


| n       | 解域 $`\mathbb{C}`$                                       |
| ------- | ------------------------------------------------------ |
| -2      | $`\{\text{True} \}`$                                     |
| -1      | $`\{\Sigma_{1-i}\ne 0 \}`$                               |
| $`\ge 0`$ | $`\{\Sigma_{1-i}>nx_i, \Sigma_{1-i}\ne (n+1)x_{1-i} \}`$ |

其中解域指的是 $`\mathbb{X} = \{ (x_1, x_2, \dots, x_6) \in (\mathbb{Z}^+)^6 \mid 0 < x_1 < x_2 < \dots < x_6\}`$ 的所有解集，如当 $`n=1`$ 时，解域为 $`\mathbb{C}=\{ (x_1, x_2, \dots, x_6) \in (\mathbb{Z}^+)^6 \mid 0 < x_1 < x_2 < \dots < x_6，x_6-(k_1x_5+\dots)>x_i,x_6-(k_1x_5+\dots)\ne 2x_{1-i})\}`$

当 $`\mathbb{S}`$ 不成立时，记为 $`\mathbb{D}=\bar{\mathbb{C}} =\mathbb{X}-\mathbb{C}=\{\Sigma_{1-i}\le nx_i\}\cup\{ \Sigma_{1-i}= (n+1)x_{1-i} \}`$

### $`\mathcal{F}`$ 的性质

记 $`\mathcal{F}_{K, i}(n),K=(k_5, k_4, \dots, k_{i+1})\in (\mathbb{Z}^{+})^{5-i},5\ge i\ge1`$, $`\mathcal{F}`$ 关于 $`K`$ 是对称函数，其中 $`n\ge-2`$, $`i,n\in \mathbb{Z}`$

先定义 $`\theta(i)`$ ($`\theta(1)`$~$`\theta(5)`$ 均可证明, $`\theta(6)`$ 不参与 $`\mathcal{F}`$ 的计算)

| i    | $`\theta(i)`$             | 值           |
| ---- | ----------------------- | ------------ |
| 1    | $`\theta([1])`$           | $`0.1_6`$        |
| 2    | $`\theta([1,2])`$         | $`0.11_6`$       |
| 3    | $`\theta([1,2,3])`$       | $`0.121_6`$      |
| 4    | $`\theta([1,2,3,4])`$     | $`0.1331_6`$     |
| 5    | $`\theta([1,2,3,4,5])`$   | $`0.15041_6`$    |
| 6    | $`\theta([1,2,3,4,5,8])`$ | $`0.21052411_6`$ |

### 递推公式

对 $`\mathcal{F}_{\mathbf{0},i}`$, 有 $`\mathcal{F}_{\mathbf{0},i}(-2)=1,\mathcal{F}_{\mathbf{0},i}(-1)=\theta(i),\mathcal{F}_{\mathbf{0},i}(n)=\frac{i}{6}\mathcal{F}_{\mathbf{0},i}(n-1)`$

引入 $`\sigma(K)=\binom{\sum K}{K}6^{-\sum K}`$

对 $`\mathcal{F}_{K,i}`$, $`\mathcal{F}_{K,i}(-2)`$ 和 $`\mathcal{F}_{K,i}(-1)`$ 做如下讨论, 有几种情况

1) 如果 $`\mathcal{F}_{K,i}(-1)\ge \sigma(K)`$, 则 $`(6-i)\mathcal{F}_{K,i}(-1)=\sum_{k_j>0}^{} \mathcal{F}_{K_{j\leftarrow k_j-1} ,i}(-1)\ge \sigma(K)`$, 此时 $`\mathcal{F}_{K,i}(-2)=\mathcal{F}_{K,i}(-1)=\frac{\sum_{k_j>0}^{} \mathcal{F}_{K_{j\leftarrow k_j-1} ,i}(-1)}{6-i}`$
2) 如果 $`\mathcal{F}_{K,i}(-1)< \sigma(K)`$, 则 $`(6-i+1)\mathcal{F}_{(1,\mathbf{0}),i}(-1)-\sigma(K)=\sum_{k_j>0}^{} \mathcal{F}_{K_{i\leftarrow k_i-1} ,i}(-1)`$, 此时 $`\mathcal{F}_{K,i}(-2)=\sigma(K),\mathcal{F}_{K,i}(-1)=\frac{\sum_{k_j>0}^{} \mathcal{F}_{K_{j\leftarrow k_j-1} ,i}(-1)+\sigma(K)}{6-i+1}`$

总结 $`\mathcal{F}_{K,i}(-2)=\max(\frac{\sum_{k_j>0}^{} \mathcal{F}_{K_{j\leftarrow k_j-1} ,i}(-1)}{6-i},\sigma(K)), \mathcal{F}_{K,i}(-1)=\max(\frac{\sum_{k_j>0}^{} \mathcal{F}_{K_{j\leftarrow k_j-1} ,i}(-1)}{6-i},\frac{\sum_{k_j>0}^{} \mathcal{F}_{K_{j\leftarrow k_j-1} ,i}(-1)+\sigma(K)}{6-i+1})`$

$`\mathcal{F}_{K,i}(0) = (\sum_{k_j>0}^{} \mathcal{F}_{K_{i\leftarrow k_i-1} ,i}(0)+i\mathcal{F}_{(1,\mathbf{0}),i}(-1))/6`$, 且 $`\mathcal{F}_{K,i}(n) = (\sum_{k_j>0}^{} \mathcal{F}_{K_{i\leftarrow k_i-1} ,i}(n)+i\mathcal{F}_{(1,\mathbf{0}),i}(n-1))/6`$

### 实现

程序F.py就是关于 $`\mathcal{F}`$ 函数的实现