# Gao Lean

**广义二面体群上的精确积一子序列：13 页论文与 Lean 形式化**

[中文](#中文说明) · [English](#english)

---

## 中文说明

### 项目简介

本仓库研究有限奇阶阿贝尔 \(p\) 群 \(A\) 的广义二面体群
\(\operatorname{Dih}(A)=A\rtimes_{-1}C_2\)，并形式化验证精确积一子序列阈值

\[
E\bigl(\operatorname{Dih}(A)\bigr)=2|A|+D(A).
\]

这里 \(D(A)\) 是阿贝尔群 \(A\) 的 Davenport 常数。仓库同时保存：

- 一份自包含、可独立编译的 13 页 arXiv 论文源稿；
- 对论文主定理及其依赖结果的 Lean 4 形式化；
- 逐段对应表、公理审计、负面反例和仍待完成的一般权重 GMO 路线。

**本仓库是欧拉（Euler）第一批可公开成果中的形式化仓库之一。**
它以公开、可复现、可审计的方式保存欧拉参与完成的数学证明形式化成果。

本项目是独立仓库。理解、编译或审计论文与 Lean 代码，不需要访问其他仓库、
历史分支或外部任务记录。

### 论文

完整论文源文件位于 [paper/arxiv/](paper/arxiv/)：

- [main.tex](paper/arxiv/main.tex)：主 LaTeX 入口；
- [sections/](paper/arxiv/sections/)：六个正文分节；
- [references.bib](paper/arxiv/references.bib)：参考文献；
- [PROOF-AUDIT.md](paper/arxiv/PROOF-AUDIT.md)：自然语言证明义务审计；
- [INDEPENDENT-VERIFICATION.md](paper/arxiv/INDEPENDENT-VERIFICATION.md)：独立核验说明；
- [BUILD-REPORT.md](paper/arxiv/BUILD-REPORT.md)：13 页 PDF 的可复现构建记录；
- [MANIFEST.sha256](paper/arxiv/MANIFEST.sha256)：论文交付文件校验清单。

使用标准 TeX Live 环境即可重建论文：

~~~bash
cd paper/arxiv
make pdf
~~~

等价的手动命令见 [paper/arxiv/README.md](paper/arxiv/README.md)。生成的 PDF
不是仓库的逻辑依赖；权威输入是 LaTeX 源文件、参考文献和 Lean 声明。

### 已经验证的结果

核心公开端点是：

~~~lean
GaoLean.ConcreteGDihedral.pr7ThirteenPageMain
~~~

该定理直接证明冻结的 13 页稿主陈述，不接收 remaining-input、provider 或递归结论
作为参数。现有 Lean 结果包括：

- occurrence-labelled 序列语义：重复群元素按位置区分；
- 广义二面体群的 rotation/reflection 分解；
- Olson 的奇素数群 Davenport 常数公式；
- 正负权重 Davenport 上界与 GJM small-Davenport 结果；
- 论文主证明实际使用的 \(W=\{1\}\) 与 \(W=\{\pm1\}\) GMO；
- 商群抽取、缺陷修正、平移保持和严格子群下降；
- 三个 reflection regimes 的上界、标准下界及最终等式；
- homocyclic、elementary-abelian 数值推论与 \(C_3^2\) 显式见证；
- 任意非空整数权集 GMO 所需的大量基础设施，包括 labelled Lemma 3.5、
  gcd–torsion 分层、Step 1 仿射扩张、Step 6 kernel/range 分叉，以及
  Theorem 1.1 式 (3)–(9) 的强递归状态和平凡 overgroup 基例。

逐段证据索引见 [pr7-13-page-map.md](pr7-13-page-map.md)，当前推进计划见
[formalization-plan.md](formalization-plan.md)。

### 当前认证边界

当前严格裁决是 **PARTIALLY_VERIFIED**，需要区分两件事：

1. **论文的最终 Gao 主结论已经无条件通过 Lean 核验。**
2. **论文中按任意非空 \(W\subseteq\mathbb Z\) 陈述的完整一般权重 GMO
   Theorem 2.2 尚未全部闭合。**

一般权重 GMO 目前仍缺非平凡递归支中的完整强状态构造，特别是实际产生：

- \(H\)-full core；
- 一个全程固定的中心 \(\beta\)；
- exact-spectrum 的 \(H\)-周期性；
- small carrier \(S_0\) 的精确谱等式；
- 跨商群类型、按 \(\operatorname{Nat.card}\) 良基的无条件递归闭合。

仓库不会把只覆盖 \(W=\{1\}\)、\(W=\{\pm1\}\) 的结果冒充任意权集定理，也不会把
条件 engine、provider 或结论型参数标记为完成证明。

### 复现 Lean 验证

工具链固定为 Lean v4.32.0 与 Mathlib v4.32.0。

~~~bash
lake update
lake exe cache get
lake build GaoLean GaoFormal.AxiomAudit
~~~

最近一次服务器集成构建完成 **8850/8850 jobs**，退出码为 0。关键端点的
#print axioms 只报告 Lean/Mathlib 常规公理 propext、Classical.choice、
Quot.sound（各定理使用其子集）。发布入口与审计扫描中没有 sorry、admit、
项目自定义顶层公理、unsafe、native_decide 或 sorryAx 逃逸。

历史独立冷克隆构建为 **8827 jobs**。它对应较早的已发布树，不能用来冒充当前
工作分支的独立冷审计；当前分支在升级认证状态前仍需重新进行冷克隆验收。

### 仓库结构

~~~text
GaoLean/                  论文数学主线与一般权重 GMO 形式化
GaoFormal/                聚合入口与公理审计
paper/arxiv/              自包含的 13 页论文 LaTeX 工程
math/.../                 冻结定理、审计记录与独立复核材料
pr7-13-page-map.md        论文段落到 Lean 端点的双向映射
formalization-plan.md     当前状态、开放义务与发布门槛
lakefile.toml             Lean 工程与依赖锁定
lean-toolchain            Lean 版本锁定
~~~

详细里程碑没有堆叠在本 README 中；首页只保留理解、构建和审计项目所需的信息。

### 反馈与贡献

问题、复现失败和形式化建议可以通过 GitHub Issues 提交。报告 Lean 问题时，请附上
工具链版本、失败目标和最小复现命令；报告数学问题时，请指明论文段落、对应 Lean
端点以及问题属于陈述偏差、证明缺口还是认证范围。任何提升认证等级的修改都必须同时
更新逐段映射和公理审计。

### 审计原则

- 构建成功只证明现有 Lean 声明通过内核检查，不自动证明论文每句话都已覆盖。
- 自然语言稿、模型审阅和 PDF 编译均不能替代 Lean 证明。
- 重复值必须保持 occurrence 标签，精确长度不能用集合去重或“至少”偷换。
- 已发现的错误接口与反例保留在仓库中，作为防止回归的负证据。
- 只有逐段映射、无逃逸公理扫描和独立冷构建同时通过，才会提升整篇认证状态。

---

## English

### Overview

This repository studies exact product-one subsequences in the generalized
dihedral group

\[
\operatorname{Dih}(A)=A\rtimes_{-1}C_2
\]

for a finite abelian \(p\)-group \(A\) with \(p\) odd. Its main formalized
identity is

\[
E\bigl(\operatorname{Dih}(A)\bigr)=2|A|+D(A),
\]

where \(D(A)\) is the Davenport constant of \(A\).

The repository contains both the self-contained 13-page arXiv manuscript and
its Lean 4 formalization, together with source-to-Lean maps, axiom audits,
counterexamples to invalid interfaces, and the active plan for the remaining
general-weight GMO theorem.

**This repository is one of Euler's first publicly releasable formalization
repositories.** It preserves mathematical formalization work completed with
Euler in a public, reproducible, and auditable form.

The project is self-contained: building or reviewing the manuscript and the
Lean development does not require another repository, a historical pull
request, or private task logs.

### Manuscript

The complete manuscript source is under [paper/arxiv/](paper/arxiv/).
It includes the master TeX file, six section files, bibliography, proof audit,
independent-verification instructions, build report, and SHA-256 manifest.

~~~bash
cd paper/arxiv
make pdf
~~~

See [paper/arxiv/README.md](paper/arxiv/README.md) for the equivalent manual
build. The generated PDF is not a logical dependency of the formalization; the
authoritative artifacts are the TeX sources, bibliography, and Lean statements.

### Formalized result

The principal public endpoint is:

~~~lean
GaoLean.ConcreteGDihedral.pr7ThirteenPageMain
~~~

It proves the frozen main statement directly, without a remaining-input
parameter, a provider premise, or a recursively assumed conclusion.

The development formalizes occurrence-labelled sequence semantics, the
rotation/reflection structure of generalized dihedral groups, Olson's
Davenport-constant formula, the plus-minus bound, the GMO specializations
actually used by the main proof, subgroup and quotient descent, the three
reflection regimes, the final equality, and the displayed numerical
consequences. It also contains substantial infrastructure toward the
arbitrary-weight GMO theorem.

See [pr7-13-page-map.md](pr7-13-page-map.md) for the paragraph-level evidence
map and [formalization-plan.md](formalization-plan.md) for the current proof
frontier.

### Certification boundary

The repository-wide verdict is **PARTIALLY_VERIFIED**:

- the final Gao theorem is unconditionally checked in Lean;
- the full arbitrary-nonempty-weight version of GMO Theorem 2.2 is not yet
  closed.

The remaining load-bearing obligations are the nontrivial strong recursive
state: a genuine \(H\)-full core, a fixed center \(\beta\), periodicity of the
exact spectrum, the small-carrier spectrum identity, and well-founded
cross-type recursion through quotient groups.

The repository does not promote the \(W=\{1\}\) and \(W=\{\pm1\}\)
specializations to a theorem about arbitrary \(W\), and it does not count a
conditional engine or provider as an unconditional proof.

### Reproducing the Lean build

The project is pinned to Lean v4.32.0 and Mathlib v4.32.0.

~~~bash
lake update
lake exe cache get
lake build GaoLean GaoFormal.AxiomAudit
~~~

The latest integrated server build completed **8850/8850 jobs** with exit code
0. Public endpoints use only the standard Lean/Mathlib axioms reported by
#print axioms: propext, Classical.choice, and Quot.sound (as applicable).
The release surface contains no sorry, admit, project-defined top-level axiom,
unsafe, native_decide, or sorryAx escape.

An earlier independent cold-clone build completed 8827 jobs. It belongs to an
older published tree and is not relabelled as a cold audit of the current
working branch.

### Repository layout

~~~text
GaoLean/                  Main formalization and general-weight GMO development
GaoFormal/                Aggregate entry point and axiom audit
paper/arxiv/              Self-contained 13-page LaTeX manuscript
math/.../                 Frozen statements and independent audit records
pr7-13-page-map.md        Bidirectional manuscript-to-Lean map
formalization-plan.md     Current status, open obligations, and release gates
lakefile.toml             Lean project and pinned dependencies
lean-toolchain            Pinned Lean version
~~~

### Feedback and contributions

Questions, reproduction failures, and formalization proposals can be reported
through GitHub Issues. Lean reports should include the toolchain version, the
failing target, and a minimal command. Mathematical reports should identify the
manuscript passage, the corresponding Lean endpoint, and whether the concern is
about statement fidelity, proof completeness, or certification scope. Any
change that upgrades certification must also update the paragraph map and the
axiom audit.

### Trust policy

A successful build certifies the declarations that Lean checked; it does not
by itself establish complete manuscript coverage. Natural-language review,
model review, and PDF compilation are not substitutes for kernel-checked
proof. Repository-wide certification is upgraded only after literal
source-to-Lean coverage, escape-hatch scans, and an independent cold build all
agree.
