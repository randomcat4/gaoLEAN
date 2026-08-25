# Milestone P5b2c: occurrence-labelled full-spectrum complement

Date: 2026-08-24 (America/New_York).

Status: `LEAN_CHECKED` for the internal all-rotation full-spectrum closure in
A-R6 (5.14)-(5.15). The GMO existence output, PG-O3, and PG-GAO-v1 remain
`NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:514-526`: choose a labelled `D_0|C` with prescribed size
  and coordinate sum; its occurrence complement has exact size `2Q` and sum
  zero.
- `A-R6/proof.md:528-543`: occurrence complementation gives
  `Sigma_m(C)=sigma(C)-Sigma_d(C)` and converts full `m`-spectrum to the
  required `d`-selection.

## Compiled closure

- `coordinateSum` sums additive coordinates over source occurrence labels.
- `isProductOneSelection_of_allRotation_coordinateSum_eq_zero` builds an
  exact selected-multiset ordering and proves its product is one.
- `coordinateSum_sdiff` proves
  `sum(C\D)=sum(C)-sum(D)` for labelled selections with `D⊆C`.
- `hasAllRotationProductOneSubsequence_of_fullSpectrumComplement` consumes
  `D⊆C`, the two exact cardinalities, `M-d=2Q`, all-rotation membership, and
  equality of coordinate sums, then returns an exact `2Q` all-rotation
  product-one selection.

## Mechanical audit

- Initial single-file check: exit 1; `Finset.disjoint_sdiff` needed symmetry
  and the additive rearrangement needed `eq_sub_iff_add_eq` explicitly.
- Repaired `lake env lean GaoLean\PGSpectrum.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8679 jobs)`.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` exit 1).

## Exact remaining boundary

This module does not assert that the prescribed-length spectrum is full and
does not manufacture the required `D`. GMO must supply the existence and
cardinality/sum specification. The reflection-containing ordering interface
and reflection channel remain separate open work. No Gao equality is claimed.
