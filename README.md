# 骰子优化问题求解器 (Dice Problem Solver)

基于 SMT 求解器的骰子优化问题的自动证明工具。

## 📋 目录

- [问题描述](#问题描述)
- [快速开始](#快速开始)
- [安装](#安装)
- [项目结构](#项目结构)
- [许可证](#许可证)

---

## 问题描述

### 问题背景

给定一枚骰子$X$，其各面标记的数字为互不相等的正实数，各面投掷概率均等。将棋子置于实数轴原点，通过多次投掷该骰子，每次投掷结果即为棋子的前进距离，累计前进后棋子会经过数轴上的一系列点。
定义函数$f_X(x)$为棋子在上述投掷过程中踩过数轴上点$x$的概率。需寻找满足条件的骰子$X$
，使得$\max_{x\in \R^{+}}f_X(x)$最大。

### 数学表达

> $$
\max_{X \in \mathbb{X}} \max_{x \in \mathbb{R}^+} f_X(x) \\
\text{s.t.}\quad
\begin{cases}
\mathbb{X} = \left\{ (x_1, x_2, \dots, x_6) \in \mathbb{R}^6 \mid 0 < x_1 < x_2 < \dots < x_6 \right\}, \\[6pt]
f_X(x) = 
\begin{cases} 
0, & x < 0, \\[3pt]
1, & x = 0, \\[3pt]
\displaystyle \frac{1}{6} \sum_{i=1}^6 f_X(x - x_i), & x > 0 
\end{cases}
\end{cases}
$$


### 优化问题求解

通过贪婪算法获得解$\tilde{X}=[1,2,3,4,5,8]$, 在这基础上寻找更大的解；事实上，它就是最大解；

存在性证明：整个寻找解的过程中，对于满足某种约束的$\mathcal{S} \in \mathbb{X}$中，递归的找到$\mathcal{S}' \subset \mathcal{S}$, $\mathcal{S}'$的元素满足更多约束，且对应的$\max_{x>0}f_X(x)$的取值更大；随着约束逐步强化，子集不断收缩；当最终子集仅包含最优解时，该最优解的存在性也随之得证；

寻找解：
1. 证明一定存在整数解；
2. 证明$f(x_6)=\max_{x>0}(f_X(x))$；
3. 证明$X$需要满足的初始约束集；
4. 对每组约束，对$x_6$数值拆解，即尽可能枚举满足$x_6=\sum_{i=1}^{5}{k_ix_i}$的所有表达，其中$k_i\in \N$;
5. 计算当前约束下$f_X$的最值的上限，与$f_{\tilde{X}}$对比；
5.1. 当前约束下，若$f_X$的最值恒小于$f_{\tilde{X}}$, 则✂️ 剪枝；
5.2. 当前约束下，若$f_X$的最值恒不小于$f_{\tilde{X}}$, 则✅ 判定该约束为潜在最优解候选，收集该约束；
5.3. 否则，🌾 计算$f_X$的最值不小于$\tilde{X}$所需增加的新约束集，对于每组新约束，在当前约束下叠加新约束，代入步骤4迭代求解；
6. 等价性验证：对所有收集到的候选约束，验证其与$\tilde{X}$等价

程序实现的是步骤4-6；

---

## 快速开始

```python
from core import batch_prove, constraints_to_prove

# 批量证明预定义的约束列表
for c in constraints_to_prove:
    print(c)
batch_prove(constraints_to_prove, 
            allow_breakdown_incompleteness=True)
```

### 运行示例

```bash
# 克隆仓库
git clone https://github.com/yourusername/cube.git
cd cube

# 安装依赖
pip install -r requirements.txt

# 运行主程序
python main.py
```

---

## 安装

### 依赖要求

- **Python**: 3.8 或更高版本
- **Z3 Solver**: 4.8 或更高版本
- **PuLP**: 2.7 或更高版本（用于线性规划）

### 安装步骤

#### 方法 1：使用 pip

```bash
pip install z3-solver pulp
```

#### 方法 2：使用 conda

```bash
conda create -n cube python=3.10
conda activate cube
conda install -c conda-forge z3-solver
pip install pulp
```

#### 方法 3：从源码安装

```bash
git clone https://github.com/yourusername/cube.git
cd cube
pip install -r requirements.txt
```

---

## 项目结构

```
cube/
├── core/                       # 核心模块
│   ├── __init__.py                 # 包初始化（暴露公共 API）
│   ├── smt.py                      # SMT 求解器封装
│   ├── partition.py                # 分解列表
│   ├── optim.py                    # 优化求解
│   ├── F.py                        # F 函数实现
│   ├── breakdown.py                # 分解树数据结构
│   ├── pipeline.py                 # 主流程控制
│   ├── logger.py                   # 日志系统
│   └── constants.py                # 常量定义
├── docs/                       # 文档
│   ├── algorithm.md                # 算法原理
│   └── proof.md                    # 数学证明
├── logs/                       # 日志输出目录
│   ├── {time_stamp}/               # 每次运行日志文件系统
│   │   ├── {constraint}/               # 约束名
│   │   │   ├── SP/                         # 约束下产生的solver和partition
│   │   │   │   ├── {solver.id}_solver          # 每个solver单独的日志
│   │   │   │   └── {partition.id}_partition    # 每个partition单独的日志
│   │   │   ├── summary.log                   # 约束下核心日志的总结
│   │   │   └── main.log                    # 约束下所有输出的汇总
│   │   ├── {constraint}/               # 约束名
│   │   └── batch_main.log              # 批处理相关的日志
│   └── {time_stamp}/               # 每次运行的时间戳
├── main.py                    # 主程序入口
├── requirements.txt           # Python 依赖
├── README.md                  # 项目说明（本文件）
└── LICENSE                    # 许可证
```


---

## 许可证

本项目采用 MIT 许可证 - 详见 [LICENSE](LICENSE) 文件。


---

## 更新日志

### v1.0.0 (2024-12-04)

- ✨ 首次发布
- ✅ 支持递归分解和分类
- ✅ 完整的日志系统
- ✅ 批量处理功能
- 📚 完整的算法文档

