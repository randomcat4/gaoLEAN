# Milestone 33: weighted GMO high-reflection bridge

Status: `LEAN_PARTIALLY_CHECKED` overall; the specialization and routing in
this milestone are `LEAN_CHECKED`, while the weighted GMO provider is
`LEAN_CONDITIONAL`.

## Result

`GaoLean/PGWeightedGMOBridge.lean` replaces an arbitrary high-regime output for
each source by one uniform provider on the canonical occurrence-labelled
same-type pair reservoir. From `Odd D` and the frozen restricted-coefficient
output at `(D+1)/2`, Lean derives the plus-minus Davenport bound, checks the
exact pair-count threshold, and supplies the high-reflection target output.

`PGGaoExternalUpperInputs` now carries `Odd D`,
`RestrictedCoefficientOutputAt A ((D+1)/2)`, and
`WeightedGMOPrescribedPairProvider A`; it no longer carries a per-source
high-reflection output.

## Fidelity boundary

- Natural-language anchor: `A-R6/proof.md:218--243`.
- Pair labels are source occurrences, so repeated group values remain distinct.
- Pair endpoint non-reuse, the forced reflection pair, signed pair conversion,
  and exact `2Q` product-one conclusion are internal checked consumers.
- `WeightedGMOPrescribedPairProvider` is not an axiom and its existence is not
  proved here.
- Its conclusion is already specialized to four pair lists. The generic
  additive weighted-GMO selection and occurrence-faithful partition by pair
  type/sign are the next exact blocker.
- `Odd D`, middle signed GMO, and ambient/quotient small-Davenport provider
  existence also remain external.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- New-module build: exit 0, 8675 jobs.
- Full build: exit 0, 8703 jobs.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden declaration scan: no matches, normalized exit 0.
- Scoped whitespace check: exit 0.

## Exact next blocker

Freeze the generic additive weighted-GMO occurrence statement and prove its
injective transport to the canonical pair labels, then partition the selected
labels by pair type and sign while preserving exact cardinality and endpoint
non-reuse. This must replace `WeightedGMOPrescribedPairProvider`, not be added
as another source-specific final-output assumption.
