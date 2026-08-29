# GAO Lean companion

本仓库是 `randomcat4/gao0824` PR #7 的 13 页 arXiv 稿的 Lean 4.32
形式化伴随工程。冻结来源为分支 `paper/arxiv-rewrite-2026-08-24`、提交
`6d4ab81b14f49aaa61d7aeb8c02182f1259a736b`；它不是 `gao0823` PR #8
的早期八页稿。正文与 Lean 的逐段对应见 [`pr7-13-page-map.md`](pr7-13-page-map.md)。

## 当前结论

当前整体裁决是 **`PARTIALLY_VERIFIED`**，需要区分两个层次：

- **主 Gao 结论已无条件验证。** 公开端点
  `GaoLean.ConcreteGDihedral.pr7ThirteenPageMain` 直接证明冻结的
  `PR7ThirteenPageMainStatement`，不接收 remaining-input、provider 或递归结论参数。
  论文主证明实际调用的普通权重 `W={1}` 与正负权重 `W={±1}` GMO 特化也已在
  Lean 内构造。
- **整篇尚不能称为逐命题完全验证。** 正文 Theorem 2.2 按原文量化任意非空
  `W : Set ℤ`，其结构部分还带 `gcd(W)=1` 条件。仓库现已冻结这一全权重范围的
  occurrence-labelled 统一接口，并完成通用 DGM、Davenport 常数、商群传递和群阶
  归纳驱动；但尚未构造该接口的无条件 inhabitant。因此不能把“主定理闭合”
  扩张成“整个 GMO 定理或整篇论文 `FULLY_CHECKED`”。

独立冷审计据此给出 `PARTIALLY_VERIFIED`，原因是覆盖范围尚有缺口，不是已完成
主端点构建失败或依赖了隐藏假设。

## 已机械核验的主线

- occurrence-labelled 序列、按位置选择、重复值保持与可重排积一语义；
- 广义二面体群的 rotation/reflection 分解及精确 `2|A|` 子块；
- Olson 的奇素数群 ordinary Davenport 常数公式；
- Proposition 3.1 的正负 Davenport 上界与 GJM small-Davenport 结论；
- 普通 `W={1}` prescribed-length/structural GMO，以及 `W={±1}` signed GMO；
- 任意（包括无限）非空 `W : Set ℤ` 的精确 GMO 陈述接口、weighted spectrum/DGM
  对接、精确 weighted Davenport 常数、子群—商群卷积、商群回升与群阶强归纳驱动；
- 任意非空 `W` 经整数闭包生成元归一化到本原权集、缩放像群中的 Davenport
  常数比较与 prescribed-length existence 回拉（含零生成元退化支）；
- occurrence 子序列上的选择、权函数与加权和无损提升回原序列，以及精确谱包含；
- 任意 `W` 的单点/非单点 occurrence 分层计数，以及非周期分支中
  “至少 `|A|-1` 个非单点层”强迫精确谱为全集；
- 权差与群指数生成的规范模数 `d`、`d`-torsion 核、`dA` 像、
  单点层判据、商层单点化及 `A/A[d] ≃ dA`；
- 单点层的真实 occurrence 选择、精确计数、`G[d]` 子类型序列与回源嵌入；
- Step 6 子群/商群临界长度的精确 `Nat.sub` 预算，并显式保留锋利预算所需的
  `H≠0` 与 `H<G` 条件；
- 原 GMO Lemma 3.5 的完整 labelled 证书：非平凡 `H≤K`、恰 `|H|-1`
  个核心层覆盖一个完整 `H`-陪集、保留层统一模 `H` 单点及精确遗漏界；
- 商群抽取、缺陷修正、平移保持、严格子群下降和同时归纳；
- 三个 reflection regimes 的上界、标准下界以及最终 Gao 等式；
- Corollary 6.1 的 homocyclic / elementary-abelian 数值式和 `C₃²` 显式见证。

最终阈值端点之外，完整正文显示式由独立的 Olson、GJM、Corollary 6.1 和
`C₃²` 端点共同覆盖；仓库不声称某个单一端点逐字包含这些全部结果。

## 尚未闭合的范围

下一条承重边界不是最终 Gao 装配，而是把 GMO 源定理按正文原量词补齐：

1. ~~定义并冻结 Theorem 2.2 对任意非空 `W : Set ℤ` 的统一 Lean 陈述~~（已完成）；
2. 闭合本原权集 aperiodic 分支中“单点层很多”的子群递归；
   “非单点层足够多则谱为全集”、稳定子商群分支和任意非空权集归一化已闭合；
3. 在 `gcd(W)=1` 下闭合 aperiodic structural alternative；共同陪集算术、Lemma 3.5
   完整证书、gcd--torsion 层、商群回升和归纳框架已完成；剩余是把这些证书
   组装进 Step 1/Step 6 的强 affine 递归包；
4. 用一般定理反推/对照已核验的 `W={1}`、`W={±1}` 特化，并重新逐段冷审计。

这部分完成前，准确表述始终是：**论文主结论及其实际调用的两个权重特化已无条件
验证；一般权重 GMO 和整篇逐命题覆盖仍在补齐。**

## 复现与信任边界

工具链固定为 Lean `v4.32.0`、Mathlib `v4.32.0`。发布聚合入口为
`GaoLean.lean`，并显式导入最终主定理与正文数值后果。

```text
lake update
lake exe cache get
lake build
lake build GaoFormal.AxiomAudit
```

在授权 SSH 服务器的新目录和新克隆中，独立冷构建完成 **8827 jobs**，退出码为 0。
较早的合并工作区记录为默认构建与 `GaoFormal.AxiomAudit` 各 **8820 jobs**、退出码
均为 0；8820 是历史回执，不应替代当前冷构建数值。

当前一般权重开发分支的服务器集成构建（含 capped-incidence、gcd--torsion、
任意权集归一化、occurrence 子序列运输与完整 Lemma 3.5）完成 **8839 jobs**，
退出码为 0。它是工作分支集成回执，不冒充独立冷克隆验收。

关键端点的 `#print axioms` 只报告 Lean/Mathlib 常规的 `propext`、
`Classical.choice`、`Quot.sound`（各定理使用其子集），没有 `sorryAx` 或项目自定义
公理。仓库同时扫描 `sorry`、`admit`、顶层 `axiom`、`unsafe`、`native_decide`
等禁用逃逸。构建成功与公理扫描只说明现有声明可信，不自动证明正文每一条陈述都已
建立对应关系。

## 主要形式化难点

- **标签而非集合。** 重复群元素必须按 occurrence 区分，所有抽取、补集、配对和
  回拉都要保持标签不交与精确基数。
- **精确长度。** 目标是 literal `2|A|`，不能用“至少”或去重后的集合基数替代；
  padding 与 `Nat.sub` 截断门槛均需单独核验。
- **GMO 的结构分支。** full spectrum 与共同陪集 concentration 必须保留源 occurrence、
  权重陪集及真子群下降，而不能只保留一个较弱的基数推论。
- **递归良基性。** rotation/reflection 两条通道共享严格真子群下降，商群与子群中的
  Davenport 数据必须同时传递。
- **源定理范围。** `W={1}`、`W={±1}` 足以闭合本稿主证明，但不能冒充 Theorem 2.2
  对任意非空整数权重集的全称结论；目前最后承重边界是原 GMO 证明 Step 6 的
  单点层子群递归与 Step 1 强 affine 递归包；Lemma 3.5 本身已经闭合。

仓库还保留了两个重要的负证据：无限循环族否证无条件 raw/padded capacity-entry
接口，`C₃` 例子否证错误的统一 gap 接口。最终证明没有恢复或改名使用这些错误接口。

## 审计材料

- 当前逐段覆盖：[`pr7-13-page-map.md`](pr7-13-page-map.md)
- 当前计划和完成边界：[`formalization-plan.md`](formalization-plan.md)
- 独立审计裁决：
  [`math/2026-08-26_gao0824-pr7-13p-audit/verdict.md`](math/2026-08-26_gao0824-pr7-13p-audit/verdict.md)
- Lean 构建与信任边界：
  [`math/2026-08-26_gao0824-pr7-13p-audit/verifications/lean.md`](math/2026-08-26_gao0824-pr7-13p-audit/verifications/lean.md)
- 两轮早期独立核查及主实例复核仍保留在同一审计目录；它们记录当时提交的事实，
  不能覆盖后来的冷审计范围裁决。

## 历史里程碑索引

README 不再复制 70 个时点的过程叙事。原始证据完整保留在
[`milestone-01.md`](milestone-01.md) 至 [`milestone-70.md`](milestone-70.md)：

- M1--M10：independent-difference matching、固定基数交换与 affine 证书；
- M11--M46：广义二面体序列语义、三通道 consumer、抽取、下降与反例；
- M47--M55：Olson、Proposition 3.1、GJM、主装配与数值推论；
- M56--M70：DGM/GMO 源证明拆解、signed provider 与普通结构链的阶段性记录；
- M70 之后：普通 `W={1}` canonical `d*` 路线、最终主端点与手稿后果闭合。

里程碑文件中的 `LEAN_CONDITIONAL`、“仍缺”等词描述各自提交时的边界，是审计轨迹，
不是当前主定理状态；同样，早期“完成”也不能越过当前一般权重 GMO 的未覆盖边界。
