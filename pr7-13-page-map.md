# gao0824 PR #7（13 页）正文—Lean 映射

## 冻结来源

- 仓库：`randomcat4/gao0824`
- PR：[#7](https://github.com/randomcat4/gao0824/pull/7)
- 分支：`paper/arxiv-rewrite-2026-08-24`
- 提交：`6d4ab81b14f49aaa61d7aeb8c02182f1259a736b`
- 正文：`paper/arxiv/main.tex` 与 `paper/arxiv/sections/*.tex`
- 构建回执：13 页

状态词：

- `CHECKED`：正文对应的内部推导已由 Lean 核验；
- `CONDITIONAL`：consumer 与运输已核验，但承重存在性定理仍是显式参数；
- `PARTIAL`：只覆盖了正文结论的一部分或使用了不同证明边界；
- `NOT_MAPPED`：尚无忠实 Lean 定理。

## 逐段映射

| 正文位置 | 数学内容 | Lean 锚点 | 状态与边界 |
|---|---|---|---|
| Abstract, Introduction Theorem 1.1 | `E(Dih(A))=2|A|+D(A)`，奇阿贝尔 `p` 群核 | `PGStatements.PGGaoV1Statement`; `PR7ThirteenPage.PR7ThirteenPageMainStatement` | `CONDITIONAL`；完整量词与 exact `2|A|` 已冻结；exact/at-least 语义桥和 `|Dih(A)|=2|A|` 已证 |
| Introduction, explicit invariant-factor formula | `D(A)=1+sum(p^lambda_i-1)` | `PGOlson.exists_olsonInvariantProduct`; `PGOlson.isOrdinaryDavenportConstant_invariantProduct` | `CHECKED`；从有限阿贝尔 `p` 群分类构造有限循环直积，并在 Lean 内证明精确 ordinary Davenport 常数公式 |
| Introduction, `d(Dih(A))=D(A)` equivalence | GJM small Davenport identity | `PGGJM.smallDavenportProductOneFreeAtMost_of_ordinaryDavenport`; `PGDavenportBridge.smallDavenportWitness_of_isOrdinaryDavenportConstant` | `CHECKED`；长度 `D` 的 product-one-free 下界见证与任意长度至多 `D` 的上界均已 occurrence-faithfully 证明 |
| Introduction, `C_3^2` example | 五项积一自由见证与 17 个单位元补齐 | 通用 `PGDavenportBridge` 与 `PGLowerBound` | `PARTIAL`；通用构造已核验，正文的字面五项例子未单独命名 |
| §2 sequence semantics | 按位置选择、重复值保持、可重排积一 | `Sequence`, `Ordering`, `OccurrenceOrdering` | `CHECKED` |
| §2 group law | 广义二面体乘法、rotation/reflection | `GDihedral`, `ConcreteGDihedral` | `CHECKED` |
| Lemma 2.1 | 平衡反射符号与任意旋转符号的排序实现 | `PGReflectionOrdering`; `PGReflectionPairs` | `CHECKED`；保持 occurrence 标签与精确重数 |
| Theorem 2.2 existence clause | GMO prescribed-length existence | `OrdinaryGMOPrescribedLengthProvider`; `WeightedGMOPrescribedLengthProvider` | `CONDITIONAL`；运输与 consumer 已核验，GMO 本身未证明 |
| Theorem 2.2 structural clause | full spectrum / common-coset concentration | `OrdinaryGMOStructuralProvider`; `PlusMinusGMOStructuralProvider` | `CONDITIONAL`；共同陪集语义显式保留 |
| Proposition 2.3 | 标准下界与单位元 padding | `PGDavenportBridge`; `PGLowerBound`; `PGSynthesis` | `CHECKED`，由 ordinary Davenport witness 内部构造 |
| Lemma 2.4 | identity padding | `PGBase.exists_zeroCore_of_smallDavenport`; `PGGJM`; 两个 bot controller 基例 | `CHECKED`；GJM 上界已由 ordinary Davenport 常数内部供给 |
| Proposition 3.1 statement | `D_pm(B) <= (D(B)+1)/2` | `PGOlson.plusMinusDavenportAtMost_half_of_isPGroup` | `CHECKED`；对任意有限阿贝尔奇 `p` 群与其精确 ordinary Davenport 常数直接导出半界 |
| Proposition 3.1 proof | 群代数增广理想幂零证明 | `PGPlusMinusGroupAlgebra`; `PGOlson` | `CHECKED`；从分类、不变因子精确 Davenport 公式、增广理想幂零、乘积 support 与 `[0]` 系数矛盾闭合全文证明 |
| Proposition 4.1 | `a<=1` 低反射全旋转支 | `PGOrdinaryGMOBridge`; `PGLowReflection` | `CONDITIONAL` 于 ordinary GMO |
| Proposition 4.2 | `a>=D+1` 同类型配对、高反射支 | `PGPairReservoir`; `PGPairSelection`; `PGWeightedGMOTransport`; `PGHighReflection`; `PGOlson.restrictedCoefficientOutputAt_half_of_isPGroup` | `CONDITIONAL` 仅于 weighted GMO；restricted-coefficient 输出已内部导出 |
| (4.4)--(4.6) | 中间区间 `e,ell` 与 surplus 算术 | `PGCapacity`; `PGMiddleReflection` | `CHECKED` |
| Proposition 4.3 full branch | 平衡反射 + `ell` 个旋转闭合 | `PGMiddleReflection`; `PGSpectrum` | `CONDITIONAL` 于 signed full-spectrum 输出 |
| Proposition 4.3 non-full branch | 共同陪集推出真实 `K`-集中，`K=0` padding | `PGMiddleNonfull`; `PGMiddleAssembly`; `PGBase` | `CONDITIONAL` 于 structural GMO；奇阶商桥已检查 |
| §5 definitions `P_S(K), Q(K)` | 固定源 RC 与通用全旋转 ZR 同时控制 | `PGController`; `PGControllerClosure`; `PGInduction` | `CHECKED` |
| Lemma 5.2 | Davenport subgroup/quotient 拼接不等式 | `PGDavenportConvolution.ordinaryDavenport_subgroup_quotient` | `CHECKED`；从精确 ordinary Davenport 常数构造前缀/后缀 occurrence 分解，零和自由拼接及 `D(K)+D(A/K)≤D(A)+1` 已核验 |
| Lemma 5.3 | target-length estimate | `PGCapacity`; extraction 中的 target bounds | `CHECKED` |
| Lemma 5.4 | concentration transitivity | `PGCapacity.residual_capacity_composition*` | `CHECKED` |
| Lemma 5.5 | quotient defect correction | `PGReflectionOrdering`; `PGReflectionChannel` | `CHECKED` |
| Proposition 5.6 extraction | 含反射商核、自由余项、缺陷在 `K` | `PGReflectionExtraction`; `PGGJM` | `CHECKED`；商群 GJM 上界由其 canonical ordinary Davenport 常数内部供给 |
| Proposition 5.6 full branch | signed GMO 修正缺陷、精确 `2Q` | `PGReflectionChannel` | `CONDITIONAL` 于 signed structural GMO |
| Proposition 5.6 descent branch | strict `H<K` 与容量复合 | `PGReflectionChannel`; `GAOARResidualController` | `CONDITIONAL` 于 signed structural GMO |
| Lemma 5.7 | 平移保持 quotient obstruction | `PGGuard`; `PGTranslation` | `CHECKED` |
| Proposition 5.8 extraction | outside rotations 的 `B0/B'` 分解与缺陷 | `PGRotationExtraction`; `PGGJM` | `CHECKED`；商群 GJM 上界已内部供给 |
| Proposition 5.8 full branch | 补集和式、全旋转 exact `2Q` | `PGSpectrum`; `PGRotationChannel` | `CONDITIONAL` 于 ordinary structural GMO |
| Proposition 5.8 descent branch | 平移到 `H<K` 并进入通用 ZR | `PGTranslation`; `PGRotationChannel`; `GAOARResidualController` | `CONDITIONAL` 于 ordinary structural GMO |
| Lemma 5.9 | `2Q alpha=0` 的全旋转回拉 | `PGTranslation.hasAllRotationProductOneSubsequence_pullback_translatedSequence` | `CHECKED` |
| Theorem 5.1 base cases | `P_S(0)` 与 `Q(0)` 分别证明 | `PGBase`; `PGInduction.concreteControllerAt_bot_of_smallDavenport`; `PGGJM` | `CHECKED`；所需 small-Davenport 上界已内部供给 |
| Theorem 5.1 induction | 每次严格下降 `H<K`，同时强归纳 | `PGInduction`; `PGControllerClosure`; `GAOARResidualController` | `CHECKED` 的调度器，整体 `CONDITIONAL` 于 source providers |
| §6 main completion | 三个 reflection regimes 与上下界装配 | `PGReflectionRegimes`; `PGSynthesis`; `GAOARFinal` | `CONDITIONAL`；未把 desired upper bound 作为参数 |
| Corollary 6.1 | homocyclic / elementary-abelian 数值公式 | `PGHomocyclic.pgGao_homocyclic_display_of_structuralRemainingInputs`; `PGHomocyclic.pgGao_elementaryAbelian_display_of_structuralRemainingInputs` | `CHECKED`（条件仅继承主定理的 GMO 边界）；Lean 核验 `|C_(p^k)^r|=p^(kr)`、`D=1+r(p^k-1)` 及正文两条字面展示式 |

## 当前严格裁决

13 页稿的 occurrence 语义、广义二面体排序、三个反射区间、商群抽取、缺陷修正、
平移保持、严格同时下降和最终条件式装配已有实质 Lean 覆盖。以下内容仍阻止
`LEAN_FULLY_CHECKED`：

1. GMO 的 existence/structural 定理本身。

两个独立审计后，主实例另行补证了 `|Dih(A)|=2|A|`、exact-length/
at-least threshold 等价、Lemma 5.2、Olson 公式、Proposition 3.1 以及 GJM
small-Davenport 等号；它们不再列为缺口。当前唯一真正承重的数学边界是 GMO；
数值 corollary 已完成，并精确继承同一个 GMO 边界，没有另加数学假设。

因此当前不是该 13 页稿的无条件完整 Lean；准确状态是主证明骨架
`LEAN_CONDITIONAL`，并有上述逐段缺口账。
