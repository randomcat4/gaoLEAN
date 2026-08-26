# 主实例复查

## 核对材料

- 13 页原稿：`randomcat4/gao0824` PR #7，commit
  `6d4ab81b14f49aaa61d7aeb8c02182f1259a736b`。
- 两份相互独立的逐段源码审计。
- `gaoLEAN` theorem signatures、调用链、服务器构建与 axiom 输出。

## 三方一致结论

两位验证者与主实例一致判定：当前顶层是忠实、非循环的
`LEAN_CONDITIONAL`，不是 13 页论文的无条件完整 Lean 证明。

已机械闭合的是 occurrence 语义、exact `2|A|` 运输、广义二面群词计算、三反射区间、
中间容量、商群抽取、两个 defect、平移、两个 `K=0` 基例、严格同时子群下降和最终条件式装配。

仍阻止 `LEAN_FULLY_CHECKED` 的承重缺口是：

1. Proposition 3.1 正文群代数证明；
2. Lemma 5.2 Davenport 拼接及从精确子群/商群常数构造当前数值包；
3. Olson invariant-factor 公式、`D(A)` 奇性与一般 homocyclic 数值导出；
4. GJM small-Davenport 全称等号；
5. GMO existence/structural 文献定理本身。

`C_3^2=23` 是未单独导出的展示性特例，不参与主骨架闭合，但属于完整 13 页成稿覆盖要求。

## 主复查修正

独立报告共同指出两个非承重语义缺口。主实例没有改动冻结结论，而是补证：

- `ConcreteGDihedral.card_group`：`|Dih(A)| = 2|A|`；
- `isExactProductOneThreshold_iff_isAtLeast`：内部 exact-threshold 与论文“所有长度至少阈值”定义等价。

两项及 PR7 顶层在 Lean 4.32.0 / Mathlib v4.32.0 服务器构建通过；新增引理与最终条件定理的 axiom 输出均不含 `sorryAx` 或项目自设公理。

## 最终裁决

`CRITICAL_GAPS / LEAN_CONDITIONAL`。

没有发现偷偷缩窄量词、降低目标块长度、合并重复 occurrence，或把 controller/目标上界塞入 remaining inputs。也不能据此声称论文已被 Lean 完整证实：上述五类承重输入仍须逐一证明或以经过正式导入的外部定理闭合。
