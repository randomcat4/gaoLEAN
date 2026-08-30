# Lemma 5.2 形式化补充核查

本文件是两份独立审计之后的进展记录；两份原始报告保持不变，以便追溯当时裁决。

`GaoLean/PGDavenportConvolution.lean` 现已核验：

1. ordinary Davenport 上界从精确长度单调到更长序列；
2. 有限加法群的最小精确 ordinary Davenport 常数存在；
3. occurrence-labelled 前缀与后缀选取的标签、重数和和式精确对齐；
4. 对 `K ≤ A`，若长度 `D(K)-1` 的子群词与长度 `D(A/K)-1` 的商群词均零和自由，则选择商群代表后的拼接词在 `A` 中仍零和自由；
5. 因此得到 `D(K)+D(A/K) ≤ D(A)+1`。

`GAOARFinal` 已不再向调用者要求 `hconvolution`；子群、商群和 ambient 的精确常数均由统一定义提供，卷积不等式在终稿入口内部导出。

这一进展不改变冻结的论文命题，也不使 Proposition 3.1、Olson、GJM 或 GMO 自动成为已证。

服务器 Lean 4.32.0 / Mathlib v4.32.0 验收结果：目标模块 8688 jobs，
全库及统一公理审计 8737 jobs，均 exit 0。新定理只依赖
`propext`、`Classical.choice`、`Quot.sound`；禁用声明/占位符扫描无命中。
