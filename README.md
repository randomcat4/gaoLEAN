# Gao Lean

**广义二面体群 Gao 常数的精确公式与 Lean 形式化**
**The exact Gao constant of generalized dihedral groups, formalized in Lean**

> **[📄 阅读 13 页论文 / Read the 13-page paper (PDF)](paper/arxiv/main.pdf)**
>
> [LaTeX 源稿 / Sources](paper/arxiv/) ·
> [论文—Lean 逐段映射 / Evidence map](docs/manuscript-lean-map.md) ·
> [形式化状态 / Formalization status](docs/formalization-plan.md)

**本仓库是欧拉（Euler）第一批可公开成果中的形式化仓库之一。**
**This is one of the formalization repositories in Euler's first batch of
publicly releasable results.**

---

## 中文

### Gao 问题是什么？

对有限群 $G$，Gao 常数 $E(G)$ 是使下述性质成立的最小整数 $L$：
任意长度至少为 $L$ 的群元素序列，都包含一个**恰好由 $|G|$ 项组成**、
并且可以重新排序为乘积 $1$ 的子序列。

标准构造给出下界

$$
E(G)\ge |G|+d(G),
$$

其中 $d(G)$ 是 small Davenport 常数。Gao 问题的核心是：这个下界何时恰好取等？

### 哪一年解决了什么？

| 年份 | 进展 |
|---|---|
| **1996** | 高卫东证明了所有有限阿贝尔群的精确公式 $E(G)=\lvert G\rvert+D(G)-1=\lvert G\rvert+d(G)$。这是通常所说的 Gao 阿贝尔情形的解决。 |
| **2005** | Zhuang–Gao 猜想同一等式对每个有限群都成立。这个全体有限群猜想至今仍不是本仓库声称解决的问题。 |
| **2026** | 本仓库记录的结果解决了一个新的非阿贝尔无限族：核为任意有限阿贝尔奇 $p$ 群的广义二面体群。 |

历史来源：
[Gao 1996](https://doi.org/10.1006/jnth.1996.0067) ·
[Zhuang–Gao 2005](https://doi.org/10.1016/j.ejc.2004.06.014) ·
[Godara–Joshi–Mazumdar 2026](https://doi.org/10.1016/j.jnt.2025.11.011)

### 我们具体解决了什么？

设 $p$ 是奇素数，

$$
A=\bigoplus_{i=1}^{r} C_{p^{\lambda_i}},
\qquad
\operatorname{Dih}(A)=A\rtimes_{-1}C_2,
$$

其中 $C_2$ 通过取逆作用在 $A$ 上。本项目证明并形式化核验

$$
E\bigl(\operatorname{Dih}(A)\bigr)
 =2|A|+D(A)
 =2|A|+1+\sum_{i=1}^{r}\bigl(p^{\lambda_i}-1\bigr).
$$

结合 $d(\operatorname{Dih}(A))=D(A)$，这正是

$$
E\bigl(\operatorname{Dih}(A)\bigr)
 =|\operatorname{Dih}(A)|+d\bigl(\operatorname{Dih}(A)\bigr).
$$

它把普通二面体群的**循环核**公式推广到任意有限阿贝尔奇 $p$ 群核，包括非循环核。
例如，本结果给出

$$
E\bigl(\operatorname{Dih}(C_3^2)\bigr)=23.
$$

本项目不声称覆盖混合素数核、$2$ 群核、所有有限群或逆问题。

### 论文与形式化

仓库自包含保存：

- [可直接阅读的 13 页 PDF](paper/arxiv/main.pdf)；
- [完整 LaTeX 源文件、参考文献和构建说明](paper/arxiv/)；
- Lean 4 主证明、依赖定理与公理审计；
- [论文每一部分对应的 Lean 证据](docs/manuscript-lean-map.md)；
- [开放义务与发布门槛](docs/formalization-plan.md)。

当前认证状态：

| 范围 | 状态 |
|---|---|
| 上述广义二面体群 Gao 精确公式 | **已无条件通过 Lean 核验** |
| 主证明实际使用的 $W=\{1\}$、$W=\{\pm1\}$ GMO 特化 | **已核验** |
| 论文中任意非空整数权集 $W$ 的完整一般权重 GMO 定理 | **仍在形式化，PARTIALLY_VERIFIED** |

面向下游使用者的稳定数学名称是
`GaoLean.ConcreteGDihedral.gaoGeneralizedDihedralOddPGroup`；历史性的 PR/V1
名称仅保留用于来源追踪，不再作为仓库门面。

这里的 PARTIALLY_VERIFIED 只描述整篇逐命题覆盖尚有一般权重缺口，不表示最终
Gao 公式依赖隐藏前提。仓库不会把条件 engine、provider 或结论型参数冒充完成证明。

### 复现

Lean 工具链固定为 Lean v4.32.0 与 Mathlib v4.32.0。

~~~bash
lake update
lake exe cache get
lake build GaoLean GaoFormal.AxiomAudit
~~~

最近一次独立检出目录的服务器构建完成 **8854/8854 jobs**，退出码为 0
（[构建回执](docs/build-receipts/2026-08-30-8a87472.md)）。公开审计端点只使用
Lean/Mathlib 常规公理 propext、Classical.choice 与 Quot.sound（按定理实际需要）；
扫描未发现 sorry、admit、项目自定义顶层公理、unsafe、native_decide 或 sorryAx
逃逸。

重建论文：

~~~bash
cd paper/arxiv
make pdf
~~~

已提交的 PDF 由仓库内源稿重新构建，共 13 页；最终日志中的未解析引用、未解析文献、
overfull 与 underfull 警告扫描均为 0。

### 仓库导航

~~~text
paper/arxiv/       论文 PDF、LaTeX 源稿、参考文献与构建报告
GaoLean/           数学主线和一般权重 GMO 形式化
GaoFormal/         聚合入口与公理审计
docs/              当前计划、证据映射、覆盖表和构建记录
docs/milestones/   归档的开发里程碑
audit/             冻结陈述与独立复核材料
~~~

问题、复现失败和证明建议可以通过 GitHub Issues 提交。认证状态的任何提升都必须同步
更新逐段证据映射、公理审计和独立冷构建记录。

---

## English

### The problem

For a finite group $G$, the Gao constant $E(G)$ is the least $L$ such
that every sequence of length at least $L$ contains exactly $|G|$ terms
that can be reordered to have product one. The standard lower bound is

$$
E(G)\ge |G|+d(G),
$$

where $d(G)$ is the small Davenport constant. The central question is when
equality holds.

### Historical timeline

- **1996:** Weidong Gao proved
  $E(G)=|G|+D(G)-1=|G|+d(G)$ for every finite abelian group.
- **2005:** Zhuang and Gao conjectured the same equality for every finite
  group. This repository does not claim to settle that full conjecture.
- **2026:** The result recorded here settles a new nonabelian infinite family:
  generalized dihedral groups with an arbitrary finite abelian odd
  $p$-group kernel.

Primary references:
[Gao 1996](https://doi.org/10.1006/jnth.1996.0067) ·
[Zhuang–Gao 2005](https://doi.org/10.1016/j.ejc.2004.06.014) ·
[Godara–Joshi–Mazumdar 2026](https://doi.org/10.1016/j.jnt.2025.11.011)

### Our result

For an odd prime $p$, let

$$
A=\bigoplus_{i=1}^{r} C_{p^{\lambda_i}},
\qquad
\operatorname{Dih}(A)=A\rtimes_{-1}C_2.
$$

This project proves and formalizes

$$
E\bigl(\operatorname{Dih}(A)\bigr)
 =2|A|+D(A)
 =2|A|+1+\sum_{i=1}^{r}\bigl(p^{\lambda_i}-1\bigr).
$$

Equivalently,
$E(\operatorname{Dih}(A))
=|\operatorname{Dih}(A)|+d(\operatorname{Dih}(A))$.
This extends the cyclic-kernel dihedral formula to every finite abelian odd
$p$-group kernel, including noncyclic kernels. It does not cover mixed-prime
kernels, $2$-group kernels, all finite groups, or the inverse problem.

### Paper, Lean proof, and status

- [Read the 13-page PDF](paper/arxiv/main.pdf).
- [Build or inspect the complete manuscript source](paper/arxiv/).
- [Follow the manuscript-to-Lean evidence map](docs/manuscript-lean-map.md).
- [Read the current formalization plan](docs/formalization-plan.md).

The exact generalized-dihedral Gao formula is **unconditionally checked in
Lean**. The repository-wide verdict remains **PARTIALLY_VERIFIED** only because
the manuscript also states a full arbitrary-weight GMO theorem whose complete
source range is still being formalized. The $W=\{1\}$ and $W=\{\pm1\}$
instances actually used by the main Gao proof are checked.

The stable, mathematically named Lean entry point is
`GaoLean.ConcreteGDihedral.gaoGeneralizedDihedralOddPGroup`. Historical PR/V1
names remain only as provenance-preserving internal interfaces.

### Reproduction

~~~bash
lake update
lake exe cache get
lake build GaoLean GaoFormal.AxiomAudit
~~~

The latest server build from a separate checkout completed **8854/8854 jobs**
with exit code 0 ([build receipt](docs/build-receipts/2026-08-30-8a87472.md)).
The public audit surface reports only the standard Lean/Mathlib axioms
propext, Classical.choice, and Quot.sound as applicable, with no admitted or
project-defined axiom escape.

To rebuild the paper:

~~~bash
cd paper/arxiv
make pdf
~~~

The committed PDF has 13 pages and was rebuilt from the committed sources with
resolved references and citations. Detailed development records are organized
under [docs/](docs/) rather than exposed at repository root.
