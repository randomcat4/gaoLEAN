# 13 页正文—Lean 映射

## 冻结来源

- 自包含正文：[`paper/arxiv/main.tex`](../paper/arxiv/main.tex) 与
  [`paper/arxiv/sections/`](../paper/arxiv/sections/)
- 可读成稿：[`paper/arxiv/main.pdf`](../paper/arxiv/main.pdf)，13 页
- 完整性清单：[`paper/arxiv/MANIFEST.sha256`](../paper/arxiv/MANIFEST.sha256)
- 构建回执：[`paper/arxiv/BUILD-REPORT.md`](../paper/arxiv/BUILD-REPORT.md)

本映射只以本仓库内的冻结正文为审计基准，不依赖外部拉取请求、私有仓库或历史工作区。
上游提交 `6d4ab81b14f49aaa61d7aeb8c02182f1259a736b` 仅保留为导入溯源信息，
不是理解或复现本仓库的逻辑依赖。

当前整篇裁决：`PARTIALLY_VERIFIED`。下列状态词只评价所在行，不能把某个主定理行的
`FULLY_CHECKED` 提升为整篇逐命题完全覆盖。

状态词：

- `FULLY_CHECKED`：正文冻结结论由无条件 Lean 端点直接实现；
- `CHECKED`：正文对应的内部推导已由 Lean 核验；
- `CONDITIONAL`：consumer 与运输已核验，但承重存在性定理仍是显式参数；
- `PARTIAL`：只覆盖了正文结论的一部分或使用了不同证明边界；
- `NOT_MAPPED`：尚无忠实 Lean 定理。

## 逐段映射

| 正文位置 | 数学内容 | Lean 锚点 | 状态与边界 |
|---|---|---|---|
| Abstract, Introduction Theorem 1.1 | `E(Dih(A))=2\|A\|+D(A)`，奇阿贝尔 `p` 群核 | `ConcreteGDihedral.gaoGeneralizedDihedralOddPGroup`（稳定公开入口）；历史冻结类型 `PR7ThirteenPageMainStatement` | `FULLY_CHECKED`；无 remaining-input/provider 参数，完整量词、exact `2\|A\|`、exact/at-least 语义桥与 `\|Dih(A)\|=2\|A\|` 均已证 |
| Introduction, explicit invariant-factor formula | `D(A)=1+sum(p^lambda_i-1)` | `PGOlson.exists_olsonInvariantProduct`; `PGOlson.isOrdinaryDavenportConstant_invariantProduct` | `CHECKED`；从有限阿贝尔 `p` 群分类构造有限循环直积，并在 Lean 内证明精确 ordinary Davenport 常数公式 |
| Introduction, `d(Dih(A))=D(A)` equivalence | GJM small Davenport identity | `PGGJM.smallDavenportProductOneFreeAtMost_of_ordinaryDavenport`; `PGDavenportBridge.smallDavenportWitness_of_isOrdinaryDavenportConstant` | `CHECKED`；长度 `D` 的 product-one-free 下界见证与任意长度至多 `D` 的上界均已 occurrence-faithfully 证明 |
| Introduction, `C_3^2` example | 五项积一自由见证、17 个单位元补齐与 `E=23` | `PGManuscriptConsequences.c3SquaredDavenportWitness`; `c3SquaredDavenportWitnessOccurrenceEquiv`; `c3SquaredProductOneFreeWord_isProductOneFree`; `c3SquaredPaddedLowerWord_no_eighteenBlock`; `pgGao_c3Squared_threshold` | `CHECKED`；四个 additive occurrences 由 `Σ i : Fin 2, Fin 2` 标记，故是两坐标各两份生成元；再接一枚反射与 17 个单位元，长度 22 且无 18 项积一块。内部枚举顺序未冒充正文的字面排列，但 occurrence-labelled 多重集与数值阈值均已核验 |
| §2 sequence semantics | 按位置选择、重复值保持、可重排积一 | `Sequence`, `Ordering`, `OccurrenceOrdering` | `CHECKED` |
| §2 group law | 广义二面体乘法、rotation/reflection | `GDihedral`, `ConcreteGDihedral` | `CHECKED` |
| Lemma 2.1 | 平衡反射符号与任意旋转符号的排序实现 | `PGReflectionOrdering`; `PGReflectionPairs` | `CHECKED`；保持 occurrence 标签与精确重数 |
| Theorem 2.2 existence clause | 任意非空 `W : Set ℤ` 的 GMO prescribed-length existence | `GeneralWeightedGMOExistenceProvider`; `weightedDavenportValue_spec`; `weightedGMOExistenceConclusion_of_stabilizerQuotientProvider`; `generalWeightedGMOSourcePackage_of_aperiodicPackages`; `weightedExactSpectrum_card_eq_univ_or_manySingleton_of_bottomStabilizer`; `primitiveAperiodicExistence_or_kernelZeroCore_or_rangeCertificate`; `generalWeightedStrongRecursionAt_bot`; `generalWeightedGMOExistenceProvider_of_primitiveProviders` | `PARTIAL`；原文任意（包括无限）非空 `W` 的精确接口、DGM/Davenport/商群与归纳基础、非周期 full-spectrum、底/顶差分核、proper-kernel 零核或 Lemma-3.5 真实分叉、任意权集到本原权集的存在性归一化，以及式 (3)--(9) 的平凡 overgroup 强基例均已机械核验；仍缺跨商群类型的严格群阶归纳与非平凡强状态装配；`W={1}` 与 `W={±1}` 特化已无条件构造 |
| Theorem 2.2 structural clause | `gcd(W)=1` 下的 full spectrum / common-coset concentration | `GeneralWeightedGMOStructuralProvider`; `WeightedGMOConcentration`; `generalWeightedStep1EnlargementCertificate_exists`; `generalWeightedStep1_fullAffineCore_or_concentration`; `GeneralWeightedStrongRecursionState`; `generalWeightedStrongRecursionAt_bot`; `weightedGMOStructuralConclusion_of_stabilizerQuotientProvider`; `generalWeightedGMOSourcePackage_of_aperiodicPackages`; `generalWeightedLemma35Certificate_exists` | `PARTIAL`；逐字全范围接口、共同源/权值陪集、真子群商群回升、gcd--torsion、完整 weighted Lemma 3.5、Step 1 固定中心严格 affine 扩张、强返回值的全部字段定义及平凡 overgroup 无条件实例均已核验；尚缺非平凡支实际构造 `H`-full core、固定 `β`、exact-spectrum 周期性与 small carrier `S₀` 等式，并须以跨类型商群归纳闭合，不能用弱 corollary provider 冒充完整定理 |
| Proposition 2.3 | 标准下界与单位元 padding | `PGDavenportBridge`; `PGLowerBound`; `PGSynthesis` | `CHECKED`，由 ordinary Davenport witness 内部构造 |
| Lemma 2.4 | identity padding | `PGBase.exists_zeroCore_of_smallDavenport`; `PGGJM`; 两个 bot controller 基例 | `CHECKED`；GJM 上界已由 ordinary Davenport 常数内部供给 |
| Proposition 3.1 statement | `D_pm(B) <= (D(B)+1)/2` | `PGOlson.plusMinusDavenportAtMost_half_of_isPGroup` | `CHECKED`；对任意有限阿贝尔奇 `p` 群与其精确 ordinary Davenport 常数直接导出半界 |
| Proposition 3.1 proof | 群代数增广理想幂零证明 | `PGPlusMinusGroupAlgebra`; `PGOlson` | `CHECKED`；从分类、不变因子精确 Davenport 公式、增广理想幂零、乘积 support 与 `[0]` 系数矛盾闭合全文证明 |
| Proposition 4.1 | `a<=1` 低反射全旋转支 | `PGOrdinaryGMOBridge`; `PGLowReflection`; `ordinaryGMOPrescribedLengthProvider_of_canonicalDStar` | `CHECKED`；ordinary GMO 输入已内部构造 |
| Proposition 4.2 | `a>=D+1` 同类型配对、高反射支 | `PGPairReservoir`; `PGPairSelection`; `PGWeightedGMOTransport`; `PGHighReflection`; `PGOlson.restrictedCoefficientOutputAt_half_of_isPGroup`; `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction` | `CHECKED`；weighted GMO 与 restricted-coefficient 输出均已内部导出 |
| (4.4)--(4.6) | 中间区间 `e,ell` 与 surplus 算术 | `PGCapacity`; `PGMiddleReflection` | `CHECKED` |
| Proposition 4.3 full branch | 平衡反射 + `ell` 个旋转闭合 | `PGMiddleReflection`; `PGSpectrum`; `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction` | `CHECKED` |
| Proposition 4.3 non-full branch | 共同陪集推出真实 `K`-集中，`K=0` padding | `PGMiddleNonfull`; `PGMiddleAssembly`; `PGBase`; `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction` | `CHECKED`；奇阶商桥与 structural GMO 均已闭合 |
| §5 definitions `P_S(K), Q(K)` | 固定源 RC 与通用全旋转 ZR 同时控制 | `PGController`; `PGControllerClosure`; `PGInduction` | `CHECKED` |
| Lemma 5.2 | Davenport subgroup/quotient 拼接不等式 | `PGDavenportConvolution.ordinaryDavenport_subgroup_quotient` | `CHECKED`；从精确 ordinary Davenport 常数构造前缀/后缀 occurrence 分解，零和自由拼接及 `D(K)+D(A/K)≤D(A)+1` 已核验 |
| Lemma 5.3 | target-length estimate | `PGCapacity`; extraction 中的 target bounds | `CHECKED` |
| Lemma 5.4 | concentration transitivity | `PGCapacity.residual_capacity_composition*` | `CHECKED` |
| Lemma 5.5 | quotient defect correction | `PGReflectionOrdering`; `PGReflectionChannel` | `CHECKED` |
| Proposition 5.6 extraction | 含反射商核、自由余项、缺陷在 `K` | `PGReflectionExtraction`; `PGGJM` | `CHECKED`；商群 GJM 上界由其 canonical ordinary Davenport 常数内部供给 |
| Proposition 5.6 full branch | signed GMO 修正缺陷、精确 `2Q` | `PGReflectionChannel`; `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction` | `CHECKED` |
| Proposition 5.6 descent branch | strict `H<K` 与容量复合 | `PGReflectionChannel`; `GAOARResidualController`; `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction` | `CHECKED` |
| Lemma 5.7 | 平移保持 quotient obstruction | `PGGuard`; `PGTranslation` | `CHECKED` |
| Proposition 5.8 extraction | outside rotations 的 `B0/B'` 分解与缺陷 | `PGRotationExtraction`; `PGGJM` | `CHECKED`；商群 GJM 上界已内部供给 |
| Proposition 5.8 full branch | 补集和式、全旋转 exact `2Q` | `PGSpectrum`; `PGRotationChannel`; `ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup` | `CHECKED` |
| Proposition 5.8 descent branch | 平移到 `H<K` 并进入通用 ZR | `PGTranslation`; `PGRotationChannel`; `GAOARResidualController`; `ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup` | `CHECKED` |
| Lemma 5.9 | `2Q alpha=0` 的全旋转回拉 | `PGTranslation.hasAllRotationProductOneSubsequence_pullback_translatedSequence` | `CHECKED` |
| Theorem 5.1 base cases | `P_S(0)` 与 `Q(0)` 分别证明 | `PGBase`; `PGInduction.concreteControllerAt_bot_of_smallDavenport`; `PGGJM` | `CHECKED`；所需 small-Davenport 上界已内部供给 |
| Theorem 5.1 induction | 每次严格下降 `H<K`，同时强归纳 | `PGInduction`; `PGControllerClosure`; `GAOARResidualController`; `ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup` | `CHECKED`；source providers 已内部实现 |
| §6 main completion | 三个 reflection regimes 与上下界装配 | `PGReflectionRegimes`; `PGSynthesis`; `GAOARFinal`; `ConcreteGDihedral.gaoGeneralizedDihedralOddPGroup` | `FULLY_CHECKED`；未把 desired upper bound 作为参数 |
| Corollary 6.1 | homocyclic / elementary-abelian 数值公式 | `PGManuscriptConsequences.pgGao_homocyclic_display`; `PGManuscriptConsequences.pgGao_elementaryAbelian_display` | `FULLY_CHECKED`；无 remaining-input 参数，保持原来的 prime/odd/Nontrivial 量词；Lean 核验 `\|C_(p^k)^r\|=p^(kr)` 与 `D=1+r(p^k-1)` |

## 当前严格裁决

13 页稿的 occurrence 语义、广义二面体排序、三个反射区间、商群抽取、缺陷修正、
平移保持、严格同时下降、主证明所用 ordinary/signed GMO 特化与最终装配均有实质
Lean 覆盖。公开最终端点是
`GaoLean.ConcreteGDihedral.gaoGeneralizedDihedralOddPGroup`；它经由已核验的历史装配
端点直接证明冻结的 `PR7ThirteenPageMainStatement`，没有 remaining-input、provider 或递归
结论参数。因此**主 Gao 结论本身已无条件核验**。

此前两轮独立审计发现并保留的自然数截断、人工 padding、标签不交、错误 raw
capacity/gap 接口等证据没有删除；最终主结论闭合走的是 canonical `d*` target
induction、canonical subgroup extension 与已证明的 signed General-DGM provider
路线，不依赖那些被证否的接口。

但是，正文 Theorem 2.2 的量词是任意非空 `W : Set ℤ`，结构部分还要求
`gcd(W)=1`。现有端点只覆盖主证明实际需要的 `W={1}` 与 `W={±1}`，不能冒充这一
一般权重定理的完整形式化。故当前整篇准确裁决为 `PARTIALLY_VERIFIED`，而不是
`LEAN_FULLY_CHECKED`。
`gaoGeneralizedDihedralOddPGroup` 是稳定公开入口；正文的完整显示式由该入口、
Olson、GJM、无条件 Corollary 6.1 与 `C₃²` 独立端点共同覆盖，并不声称单一端点
逐字包含全部显示公式。历史核心冻结阈值端点 `pr7ThirteenPageMain` 仅保留用于
来源追踪。早期两名独立审计员对已实现主线没有给出 blocking/major 问题；后续
独立冷审计进一步检查正文全范围后，以一般权重 Theorem 2.2 未覆盖为由给出
`PARTIALLY_VERIFIED`。后者是当前整篇裁决。
