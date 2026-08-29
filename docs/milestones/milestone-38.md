# Milestone 38: explicit `C₃` refutation of the raw A6 two-exit

Status: `LEAN_FULLY_DISPROVED` for frozen Claim A6-raw.

## Frozen labelled word

Lean encodes `(rot 1)^3 (refl 0)^6` over `(ZMod 3)⋊_{-1}C₂`. Equal values
retain six different reflection positions and three different rotation
positions.

## Checked conclusions

- The word has length `9 = 2·3+3` and exactly six reflection occurrences.
- It has only three rotation occurrences. An exact-six selection containing
  exactly a prescribed reflection pair would require four rotations, so
  `PairCompleteTarget6` is false.
- Every proper subgroup of `ZMod 3` excludes the generator `1`; its rotation
  capacity is zero while the raw gate is at least two. Thus
  `OriginEntryPlus2` is false.
- Nevertheless all six zero-coordinate reflections, ordered in three pairs,
  give an exact-six product-one selection. Thus `TargetFound` is true.

## Fidelity boundary

Sources: the frozen v1 and final verdict under
`gao0824/research/residual-a6-entry-2026-08-24/`. This disproves the original
unconditional two-exit without disproving the repaired v2 theorem, whose
exceptional-group classification remains a separate obligation.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Final single-file check: exit 0.
- Full build: 8708 jobs, exit 0.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan and scoped whitespace check: pass.
