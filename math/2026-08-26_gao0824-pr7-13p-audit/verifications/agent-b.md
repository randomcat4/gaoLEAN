# 独立逐段审计 B

## 独立性

- 只读审计 `randomcat4/gao0824#7@6d4ab81` 与 `gaoLEAN` theorem signatures/call graph。
- 未读取正文—Lean 映射、验证者 A 报告或主实例结论。
- 未修改任何文件。

## 裁决

`CRITICAL_GAPS`。

## 已确认

- 最终调用链为条件式三分支装配和 residual controller；remaining-input 包没有目标输出循环。
- GMO providers 对源序列、目标长度、Davenport 界、full/concentration、source coset、weight
  coset 和 multiplicity bound 的量词足以覆盖正文实际调用。
- exact `2|A|`、位置互斥、重复值、两个 quotient defect、translation guard、same-position
  pullback 与 strict descent 均被忠实保留。

## 关键缺口

1. Proposition 3.1 的 ambient restricted-coefficient 输出及所有 proper subgroup 的
   plus-minus Davenport 界仍为参数。
2. Lemma 5.2 的 Davenport inequality 仍为 `hconvolution` 参数。
3. Olson 的公式、奇性和子群/商群 Davenport 数据没有统一的 Lean 构造。
4. GMO 与 GJM 只以证明所需接口出现，没有形式化所引用的全称文献定理。
5. 顶层核心 statement 不含 invariant-factor 展开、`dsmall` 等价、`C_3^2=23` 或一般
   homocyclic corollary。

验证者还指出原工作树缺少一般群阶定理及 exact-length/at-least 语义桥；主实例复查后已把这两项作为非承重展示层引理补入并在服务器编译通过。
