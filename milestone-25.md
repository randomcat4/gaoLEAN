# Milestone 25: PG-O4 occurrence-count synthesis

Status: `LEAN_CHECKED / PG-GAO STILL CONDITIONAL`.

## Source fidelity

Source: `A-R6/proof.md`, Sections 4 and 6. The source computes the actual
reflection and rotation counts of an arbitrary length-`2Q+D` occurrence
sequence, dispatches through the three mutually exhaustive reflection-count
ranges, and requires the residual controller only in the middle range.

Lean file: `GaoLean/PGSynthesis.lean`.

- `rotationOccurrences_union_reflectionOccurrences` and
  `card_reflectionOccurrences_add_card_rotationOccurrences` prove that the
  two occurrence types partition every source label and their cards add to
  the literal list length.
- `ReflectionRegimeClosureInputs` requires low/high output only in the
  corresponding outer regime and requires the controller together with the
  spectrum alternative only in the middle regime.
- `hasExactProductOneBlockAtLength_of_pgGaoUpperInputs` closes the exact
  threshold upper property for every source list from this explicit package.
- `pgGaoV1_of_upperInputs_and_thresholdCounterexamples` is only a conditional
  composition theorem. It does not assert either input package.

## Build and audit

- Initial single-file check: exit 1. It exposed an explicit excluded-middle
  split for rotation type and the `Nat.card`/`Fintype.card` presentation
  boundary.
- Repaired single-file check: exit 0.
- Full build at this checkpoint: exit 0, `Build completed successfully (8696
  jobs)`.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.

The milestone closes internal PG-O4 bookkeeping only. GMO outputs, the middle
controller providers, and the lower bound were still explicit at this point.
