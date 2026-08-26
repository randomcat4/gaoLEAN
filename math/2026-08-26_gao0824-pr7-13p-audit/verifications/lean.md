# Lean 机械核验

## 冻结对象

- 正文：`randomcat4/gao0824#7@6d4ab81`，13 页。
- 形式核心：`GaoLean.PR7ThirteenPageMainStatement`。
- 条件式最终定理：
  `GaoLean.ConcreteGDihedral.pr7ThirteenPageMain_of_remainingInputs`。

## 工具链

- Lean 4.32.0，commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`。
- Lake 5.0.0。
- Mathlib 固定为 `v4.32.0`。
- 运行位置：授权服务器 `/workspace/gaoLEAN`。

## 实际命令与结果

1. `lake build GaoLean.PR7ThirteenPage`：8724 jobs，退出码 0。
2. `lake build`：8736 jobs，退出码 0。
3. `lake build GaoFormal.AxiomAudit`：8736 jobs，退出码 0。
4. 实际声明/占位符扫描：`FORBIDDEN_DECLARATION_SCAN_OK`。
5. `git diff --check`：退出码 0。

## 公理依赖

最终条件式定理只报告：

- `propext`；
- `Classical.choice`；
- `Quot.sound`。

未出现项目自设公理。

## 忠实性边界

Lean statement 保持全部奇阿贝尔 `p` 群量词和 exact `2|A|` occurrence 目标。
但 `PGGaoStructuralRemainingInputs` 尚未证明；其中既有外部 GMO/GJM/受限系数
输入，也有论文内部尚未逐行形式化的 Davenport 拼接和子群 bound 包。

## 裁决

`LEAN_CONDITIONAL`。构建与公理审计通过，但不满足 `LEAN_FULLY_CHECKED` 的
无条件前件闭包及整篇逐段覆盖要求。
