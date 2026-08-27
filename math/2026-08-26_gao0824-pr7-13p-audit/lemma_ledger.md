# 引理依赖账

| ID | 引理/接口 | 当前状态 | 相对主定理 | Lean/来源锚 |
|---|---|---|---|---|
| P7-L01 | occurrence-labelled sequence 与 ordering | PROVED_HERE | STRICTLY_WEAKER | `Sequence`, `OccurrenceOrdering` |
| P7-L02 | balanced sign realization | PROVED_HERE | STRICTLY_WEAKER | `PGReflectionOrdering` |
| P7-L03 | GMO existence/structural | OPEN_AS_PARAMETER | STRICTLY_WEAKER | `GAOARGMOInterfaces` |
| P7-L04 | GJM small Davenport | PROVED_HERE | EXACT_NEEDED_PIECES | `PGGJM.smallDavenportProductOneFreeAtMost_of_ordinaryDavenport`; matching witness in `PGDavenportBridge` |
| P7-L05 | Olson ordinary Davenport formula | PROVED_HERE | EXACT_NEEDED_PIECE | `PGOlson.exists_olsonInvariantProduct`; `PGOlson.isOrdinaryDavenportConstant_invariantProduct` |
| P7-L06 | plus-minus half bound | PROVED_HERE | EXACT | `PGOlson.plusMinusDavenportAtMost_half_of_isPGroup`；分类、Olson 公式与增广幂零链全部内部闭合 |
| P7-L07 | low/high/middle reflection consumers | PROVED_HERE | STRICTLY_WEAKER | `PGLowReflection`, `PGHighReflection`, `PGMiddle*` |
| P7-L08 | quotient extraction and defect correction | PROVED_HERE | STRICTLY_WEAKER | `PGReflectionExtraction`, `PGRotationExtraction` |
| P7-L09 | Davenport concatenation inequality | PROVED_HERE | STRICTLY_WEAKER | `PGDavenportConvolution.ordinaryDavenport_subgroup_quotient` |
| P7-L10 | simultaneous strict subgroup controller | PROVED_HERE conditionally | STRICTLY_WEAKER | `GAOARResidualController` |
| P7-L11 | exact lower threshold | PROVED_HERE from ordinary Davenport | STRICTLY_WEAKER | `PGDavenportBridge`, `PGLowerBound` |
| P7-L12 | exact PR #7 main statement | PROVED_HERE conditionally | EQUIVALENT | `PR7ThirteenPage.pr7ThirteenPageMain_of_remainingInputs` |
| P7-L13 | invariant-factor/homocyclic numeric corollaries | PROVED_HERE conditionally | EXACT | `PGHomocyclic`: `|C_(p^k)^r|=p^(kr)`、`D=1+r(p^k-1)` 与 homocyclic/elementary-abelian 字面 Gao 展示式；唯一条件为主定理同一 GMO 输入包 |
| P7-L14 | `|Dih(A)|=2|A|` | PROVED_HERE | STRICTLY_WEAKER | `ConcreteGDihedral.card_group` |
| P7-L15 | exact threshold 与 all-lengths-at-least threshold 等价 | PROVED_HERE | EQUIVALENT | `PGStatements.isExactProductOneThreshold_iff_isAtLeast` |
