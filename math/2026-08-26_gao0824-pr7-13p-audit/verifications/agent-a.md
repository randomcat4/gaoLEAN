# 独立逐段审计 A

## 独立性

- 只读审计 `randomcat4/gao0824#7@6d4ab81` 与 `gaoLEAN` 源码。
- 未读取正文—Lean 映射、另一位验证者报告或主实例结论。
- 未修改任何文件。

## 裁决

`CRITICAL_GAPS`。

## 已确认

- 主量词保持任意非平凡有限奇素数阿贝尔 `p` 群，没有缩成固定秩或固定素数。
- 子序列按 occurrence 位置选择；重复值、互斥位置及 exact `2|A|` 均被保留。
- 广义二面群排序、三段反射计数、商群抽取、reflection/rotation defect、平移回拉、两个不同的 `K=0` 基例和严格同时下降均有实质 Lean 证明。
- `PGGaoStructuralRemainingInputs` 不含 controller、任一分支的 product-one 输出或目标 Gao 上界，未发现结论循环。

## 关键缺口

1. 顶层只有从 `PGGaoStructuralRemainingInputs` 推出的条件定理。
2. 正文 Proposition 3.1 的群代数证明没有重建；Lean 从
   `RestrictedCoefficientOutputAt` 接口推出 plus-minus 上界。
3. 正文 Lemma 5.2 的 Davenport 子群—商群拼接没有重建；当前为
   `Dker K + Dquot K ≤ D + 1` 输入。
4. 五次 GMO 使用保留了正确量词和 exact occurrence 运输，但 GMO 定理本身未形式化。
5. Olson invariant-factor 公式、`D(A)` 奇性、GJM small-Davenport 等号及一般
   homocyclic 数值推论未闭合。
6. `C_3^2=23` 的字面特例未单独形式化。

源码审计未找到自然语言证明的局部反例；致命问题是覆盖边界仍为条件式，而不是无条件完整 Lean。
