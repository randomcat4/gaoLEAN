# Lean 机械核验

## 冻结对象与端点

- 正文：`randomcat4/gao0824#7@6d4ab81`，13 页。
- 形式核心：`GaoLean.PR7ThirteenPageMainStatement`。
- 当前无条件主端点：
  `GaoLean.ConcreteGDihedral.pr7ThirteenPageMain`，位于
  `GaoLean/PGGaoOrdinaryComplete.lean`。
- 历史条件装配：
  `GaoLean.ConcreteGDihedral.pr7ThirteenPageMain_of_remainingInputs`；该端点保留作
  分层 API，不是当前主结论的依赖。

## 工具链

- Lean 4.32.0，commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`；
- Lake 5.0.0；
- Mathlib `v4.32.0`；
- 核验位置：授权 SSH 服务器中的独立新克隆，而非复用原集成构建目录。

## 当前构建回执

独立冷审计对公开修订执行默认 `lake build`：**8827 jobs，退出码 0**。

较早的合并工作区曾记录：

1. 默认 `lake build`：8820 jobs，退出码 0；
2. `lake build GaoFormal.AxiomAudit`：8820 jobs，退出码 0。

这些 8820-job 数值是有效历史回执，但不能取代最新独立冷构建的 8827-job 记录。
任务数可随聚合入口和已跟踪模块改变；判定依据是对应修订、命令和退出码，而不是要求
不同构建永远产生相同 job 数。

## 声明与公理边界

已审计关键端点包括：

- `ordinaryGMOPrescribedLengthProvider_of_canonicalDStar`；
- `ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup`；
- `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction`；
- `ConcreteGDihedral.pgGaoOrdinaryRemainingInputs`；
- `ConcreteGDihedral.pr7ThirteenPageMain`；
- Corollary 6.1 与 `C₃²` 后果端点。

它们的 `#print axioms` 只涉及 Lean/Mathlib 常规的 `propext`、
`Classical.choice`、`Quot.sound`（各定理使用其子集）。禁用声明扫描未发现
`sorryAx` 或项目自设公理；发布审计还检查 `sorry`、`admit`、顶层 `axiom`、
`unsafe` 与 `native_decide` 等逃逸。

## 机械通过所能证明的事

无条件主端点保持冻结的奇阿贝尔 `p` 群量词、exact `2|A|` occurrence 目标和最终
Gao 等式。论文主证明实际调用的普通 `W={1}` 与 signed `W={±1}` GMO provider
均已由仓库内部定理构造，不再是最终端点参数。

因此，早期报告中“`PGGaoStructuralRemainingInputs` 尚未证明”及
“Proposition 3.1、Olson、GJM、GMO 均为最终承重缺口”的描述只适用于旧提交，不再
适用于当前主结论。

## 机械通过不能替代的覆盖审计

正文 Theorem 2.2 量化任意非空 `W : Set ℤ`，结构部分使用 `gcd(W)=1`。当前
Lean 端点没有逐字覆盖这一一般权重范围；已有无条件证明是主稿实际所需的
`W={1}`、`W={±1}` 特化。编译器只核验仓库中已经声明的命题，不能证明缺失的一般
源陈述已经被形式化。

## 裁决

- 主 Gao 结论：`LEAN_CHECKED`，无条件；
- 主证明使用的两个 GMO 特化：`LEAN_CHECKED`，无条件；
- Theorem 2.2 任意非空 `W` 与 `gcd(W)=1` 结构全范围：`PARTIAL`；
- 13 页稿整篇逐命题裁决：`PARTIALLY_VERIFIED`。
