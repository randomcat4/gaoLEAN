# Milestone P5b2q: labelled rotation quotient extraction

Date: 2026-08-24 (America/New_York).

Status: the internal `B/B0/Bprime` extraction and its route into the PG-O3
controller are `LEAN_CHECKED`; quotient small-Davenport and ordinary GMO are
explicit providers. PG-GAO-v1 is `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:482-566`, especially (5.12)-(5.16).

## Compiled closure

- `exists_rotationQuotientExtraction` chooses a maximum labelled quotient-
  zero-sum `Bprime`; the exact complement `B0` is quotient-zero-sum-free.
- `coordinateSum_Bprime_mem` derives `sigma(Bprime) in K`.
- `reflection_union_B0_quotientProductOneFree` proves the quotient remainder
  is product-one-free by the exact reflection/rotation split.
- `exists_rotationChannelPreGMOData` constructs `C,B,B0,Bprime,M,d`, all
  occurrence typing/disjointness, and the exact (5.14) size identity.
- `defect_ge_of_davenport_split`, `reservoir_threshold`, and
  `target_ge_card_subgroup` check (5.13), the GMO length threshold, and (5.16).
- `rotationChannelPreparation_of_extraction` leaves only narrow quotient-
  small-Davenport and GMO providers; the expanded controller theorem no longer
  assumes a rotation preparation family.

The maximum-selection construction does not reproduce a particular procedural
greedy order, but it proves exactly the labelled postconditions used by the
source argument.

## Mechanical audit

- `lake env lean GaoLean\PGRotationExtraction.lean`: exit 0.
- `lake env lean GaoLean\PGControllerClosure.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8694 jobs)`.
- Unified axiom audit: exit 0; all new audited declarations use only
  `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` raw exit 1).

## Exact remaining boundary

The rotation channel still needs the external quotient small-Davenport/
Davenport-convolution facts and the formal ordinary GMO provider. The earliest
internal PG-O3 gap is now the reflection-channel labelled construction of
`R,U,tau,z`; its signed GMO output is external. Olson, GJM, GMO,
Troi-Zannier/CFS, PG-O4, and PG-GAO-v1 remain outside the complete certificate.
