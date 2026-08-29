# 当前裁决

- 整篇状态：`PARTIALLY_VERIFIED`。
- 冻结对象：13 页 `gao0824` PR #7，提交 `6d4ab81`。
- 主 Gao 结论：已无条件 Lean 验证。
- 论文实际调用的 GMO：`W={1}` 与 `W={±1}` 特化已无条件 Lean 验证。
- 整个 Theorem 2.2：尚未完整 Lean 验证。
- 是否发现循环假设、项目自设公理或偷偷改弱主 Gao 目标：否。
- 独立 SSH 冷构建：8827 jobs，退出码 0。

## 已通过部分

`GaoLean.ConcreteGDihedral.pr7ThirteenPageMain` 直接证明
`PR7ThirteenPageMainStatement`，没有 remaining-input、provider 或递归输出参数。
其量词保持有限非平凡奇素数阿贝尔 `p` 群、精确 ordinary Davenport 值及 literal
`2|A|` occurrence 目标。Olson、Proposition 3.1、GJM、Corollary 6.1 与 `C₃²`
数值见证也已有独立无条件端点。

原审计列出的 Proposition 3.1、Olson、GJM 以及主证明所需普通/正负 GMO provider
缺口，已经在后续提交中实质闭合。早期 `CRITICAL_GAPS / LEAN_CONDITIONAL` 是当时
提交的历史裁决，不再描述当前主定理。

## 尚未通过部分

正文 Theorem 2.2 按原文量化任意非空 `W : Set ℤ`；其结构结论还在
`gcd(W)=1` 假设下给出。当前仓库的无条件端点覆盖主证明实际使用的普通权重
`W={1}` 与正负权重 `W={±1}`，但没有一个逐字覆盖任意非空 `W` 及上述 gcd 条件的
统一定理。因此：

- 可以说“13 页稿的主 Gao 结论已由 Lean 证明”；
- 可以说“论文实际使用的两个 GMO 特化已由 Lean 证明”；
- 不能说“整个 GMO 定理已经形式化”；
- 不能说“13 页稿每个命题均已逐字 `FULLY_CHECKED`”。

## 审计依据

独立冷审计在授权 SSH 服务器的新目录中重新克隆并构建公开修订，默认构建完成
8827 jobs、退出码 0。覆盖性复核给出 `PARTIALLY_VERIFIED`；这是一项源陈述映射
缺口，而非内核构建失败。

早期逐项材料仍保留在 `verifications/agent-a.md`、`agent-b.md`、
`main-review.md` 与 `lemma52-addendum.md`，用于追踪当时发现和闭合的缺口。最新 Lean
构建与信任边界见 `verifications/lean.md`，当前逐段范围见仓库根目录
`pr7-13-page-map.md`。
