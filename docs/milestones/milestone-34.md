# Milestone 34: generic weighted-GMO occurrence transport

Status: `LEAN_PARTIALLY_CHECKED` overall; the occurrence transport and
high-reflection specialization in this milestone are `LEAN_CHECKED`, while
the generic weighted-GMO provider remains `LEAN_CONDITIONAL`.

## Result

`GaoLean/PGWeightedGMOTransport.lean` freezes the external theorem boundary as
`WeightedGMOPrescribedLengthProvider`, a generic prescribed-length weighted-GMO
statement on an arbitrary additive occurrence list. Its output consists of
disjoint positive and negative source positions, exact total cardinality, and
a weighted sum in the prescribed target.

For the canonical same-type pair-label sequence, Lean constructs the four
rotation/reflection and positive/negative pair lists, proves exact count and
weighted-sum preservation, and proves global endpoint non-reuse from the
canonical reservoir invariant. `PGWeightedGMOBridge.lean` and
`PGSourceAssembly.lean` now consume this generic provider rather than the old
source-specialized pair provider.

## Fidelity boundary

- Natural-language anchor: `A-R6/proof.md:218--243`.
- Selected objects are positions in the additive label list; repeated labels
  remain distinct occurrences.
- Pair type and sign partitioning, pair lookup injectivity, exact cardinality,
  weighted sum, and endpoint non-reuse are internal checked consumers.
- `WeightedGMOPrescribedLengthProvider` is not an axiom and its existence is
  not proved here.
- Ordinary GMO, middle signed GMO, ambient/quotient small-Davenport providers,
  and the parity source for `D` remain external.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Target build: exit 0, 8676 jobs.
- Full build: exit 0, 8704 jobs.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden declaration scan: no matches, normalized exit 0.
- Scoped whitespace check: exit 0.

## Exact next blocker

Formalize the published generic weighted-GMO theorem itself against
`WeightedGMOPrescribedLengthProvider`. The occurrence transport must remain
the checked consumer; the provider cannot be replaced by a source-specific
final-output assumption.
