# Milestone 26: occurrence-faithful PG lower bound

Status: `LEAN_CHECKED / PG-GAO STILL CONDITIONAL`.

## Source fidelity

Source: `A-R6/proof.md`, equations (2.2)--(2.3). From a labelled
product-one-free sequence `W` of length `D`, append fewer than `2Q` identity
occurrences. Every selected `2Q`-block must use a nonempty part of `W`, and
deleting the appended identity labels preserves a product-one ordering.

Lean file: `GaoLean/PGLowerBound.lean`.

- `SmallDavenportWitness G D` is the exact external lower input: a
  product-one-free occurrence list of length `D`.
- `prefixOccurrences` and `prefixSelection` split the appended sequence by
  positions, not values. Thus an identity-valued occurrence already present
  in `W` is not confused with a padded identity.
- `IsProductOneSelection.sdiff_of_all_one` proves that deleting an explicitly
  labelled identity subset preserves product one.
- `noProductOneBlock_of_identityPadding` proves the padded counterexample for
  every target `k` and every identity suffix of length `<k`.
- `pgGaoThresholdCounterexamples_of_smallDavenportWitness` constructs a
  counterexample for every `n<2|A|+D`, including the vacuous `n<2|A|` range.
- `pgGaoV1_of_upperInputs_and_smallDavenportWitness` now derives the frozen
  threshold statement from the checked upper dispatcher and the exact
  small-Davenport witness.

## Build and audit

- Early single-file runs exited 1 on decidable filtering, `Fin` embedding
  extensionality, and two occurrence-nonempty normalization details. Each was
  repaired without weakening a statement.
- Final `lake env lean GaoLean\\PGLowerBound.lean`: exit 0.
- `lake build GaoLean.PGLowerBound GaoLean.PGSynthesis`: exit 0, 8681 target
  jobs.
- Final `lake build`: exit 0, `Build completed successfully (8697 jobs)`.
- Unified `#print axioms` audit: exit 0; only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Declaration scan for `sorry`, `admit`, declaration-level `axiom`, and
  `unsafe`: no matches, normalized exit 0.
- `git diff --check`: exit 0. `Scratch.lean`: absent.

## Remaining boundary

The lower-bound construction is internal, but existence of
`SmallDavenportWitness (A semidirect C2) D` is still the external GJM-facing
input. The upper package still requires actual ordinary/weighted GMO outputs,
the plus-minus bound source, quotient Davenport inputs, and the two narrow GMO
providers used by the checked residual controller. No Gao equality is asserted
without these inputs.
