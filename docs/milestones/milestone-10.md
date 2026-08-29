# Milestone P5b2d: explicit ordinary GMO alternative consumer

Date: 2026-08-24 (America/New_York).

Status: `LEAN_CONDITIONAL` on the explicit proposition
`OrdinarySpectrumAlternative`. The consumer theorem is `LEAN_CHECKED`; the
GMO theorem producing that proposition is `NOT_FORMALIZED`. PG-O3 and
PG-GAO-v1 remain `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:542-566`: ordinary GMO gives either a full prescribed
  spectrum or strict `H<K` plus a large affine-coset concentration; both
  routes must return the same exact `2Q` all-rotation conclusion.

## Compiled interface and closure

- `OrdinarySpectrumAlternative` is occurrence-labelled. Its full branch
  supplies `D⊆R`, exact cardinality, and the coordinate-sum equality. Its
  non-full branch supplies `H<K`, `alpha∈K`, `C⊆R`, affine-coset membership,
  and the exact `M-|K/H|+2` lower bound.
- `hasAllRotationProductOneSubsequence_of_ordinarySpectrumAlternative`
  consumes that disjunction. The full branch calls the checked complement
  theorem; the non-full branch calls the checked capacity/translation/smaller-
  `ZR` theorem. Both return the same exact `2Q` all-rotation block.
- The proposition is an ordinary theorem parameter. No axiom or theorem
  asserting GMO has been introduced.

## Mechanical audit

- `lake env lean GaoLean\PGGMO.lean`: exit 0 on the first implementation.
- Final `lake build`: exit 0, `Build completed successfully (8680 jobs)`.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` exit 1).

## Exact remaining boundary

The earliest external blocker for this channel is now the precise theorem
which derives `OrdinarySpectrumAlternative` from GMO Corollary 1.3 under the
paper's target/length/Davenport hypotheses. The prior construction of the
rotation reservoir `R`, the reflection channel, and the full positive-step
assembly remain separate internal obligations. No Gao equality is claimed.
