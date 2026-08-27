# 引理依赖账

| ID | 引理/接口 | 当前状态 | 相对主定理 | Lean/来源锚 |
|---|---|---|---|---|
| P7-L01 | occurrence-labelled sequence 与 ordering | PROVED_HERE | STRICTLY_WEAKER | `Sequence`, `OccurrenceOrdering` |
| P7-L02 | balanced sign realization | PROVED_HERE | STRICTLY_WEAKER | `PGReflectionOrdering` |
| P7-L03 | GMO existence/structural | OPEN_AS_PARAMETER | STRICTLY_WEAKER | `GAOARGMOInterfaces` |
| P7-L04 | GJM small Davenport | OPEN_AS_PARAMETER | STRICTLY_WEAKER | `SmallDavenportProductOneFreeAtMost` |
| P7-L05 | Olson ordinary Davenport formula | OPEN | STRICTLY_WEAKER | `IsOrdinaryDavenportConstant` parameter |
| P7-L06 | plus-minus half bound | CHECKED_FROM_INVARIANT_DATA | EXACT_CONDITIONAL | `PGPlusMinusGroupAlgebra`；增广幂零已闭合，只余 Olson 数据与 `D(B)` 公式的对接 |
| P7-L07 | low/high/middle reflection consumers | PROVED_HERE | STRICTLY_WEAKER | `PGLowReflection`, `PGHighReflection`, `PGMiddle*` |
| P7-L08 | quotient extraction and defect correction | PROVED_HERE | STRICTLY_WEAKER | `PGReflectionExtraction`, `PGRotationExtraction` |
| P7-L09 | Davenport concatenation inequality | PROVED_HERE | STRICTLY_WEAKER | `PGDavenportConvolution.ordinaryDavenport_subgroup_quotient` |
| P7-L10 | simultaneous strict subgroup controller | PROVED_HERE conditionally | STRICTLY_WEAKER | `GAOARResidualController` |
| P7-L11 | exact lower threshold | PROVED_HERE from ordinary Davenport | STRICTLY_WEAKER | `PGDavenportBridge`, `PGLowerBound` |
| P7-L12 | exact PR #7 main statement | PROVED_HERE conditionally | EQUIVALENT | `PR7ThirteenPage.pr7ThirteenPageMain_of_remainingInputs` |
| P7-L13 | invariant-factor/homocyclic numeric corollaries | OPEN | STRICTLY_WEAKER | no general exported bridge |
| P7-L14 | `|Dih(A)|=2|A|` | PROVED_HERE | STRICTLY_WEAKER | `ConcreteGDihedral.card_group` |
| P7-L15 | exact threshold 与 all-lengths-at-least threshold 等价 | PROVED_HERE | EQUIVALENT | `PGStatements.isExactProductOneThreshold_iff_isAtLeast` |
