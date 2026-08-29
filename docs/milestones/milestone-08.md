# Milestone P5b2b: strict-subgroup capacity composition

Date: 2026-08-24 (America/New_York).

Status: `LEAN_CHECKED` for A-R6 equations (5.10)-(5.11), including quotient
cardinalities, natural-number boundary cases, occurrence capacity, and the
combined non-full rotation-channel recursive closure. PG-O3 and PG-GAO-v1
remain `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:455-469`: a strict `H<K` and at least `M-|K/H|+2`
  concentrated occurrences imply the required `H`-capacity through
  `|A/H|=|A/K||K/H|` and `(I-1)(J-1)+1>0`.
- `A-R6/proof.md:545-566`: the rotation-only non-full branch translates the
  concentrated affine coset, invokes smaller `ZR`, and pulls back exactly
  `2Q` rotations.

## Compiled closure

- `natCard_quotient_eq_mul_quotient_subgroupOf` proves
  `|A/H|=|A/K||K/H|` from Mathlib's quotient-product equivalence.
- `two_le_natCard_quotient_of_lt_top` and
  `two_le_natCard_internal_quotient_of_lt` derive `I,J>=2` from properness and
  strictness; those inequalities are not caller assumptions.
- `residual_capacity_composition` proves the exact truncated-natural-number
  inequality. `residual_capacity_composition_of_strict` is its subgroup form.
- `translatedCapacity_of_strict_concentration` combines a labelled
  `alpha+H` set with the two source lower bounds.
- `hasAllRotationProductOneSubsequence_of_concentration_and_smallerZR`
  composes capacity, translated-list guard/count transport, the smaller `ZR`
  theorem, and the exact pullback to the original sequence.

## Mechanical audit

- First single-file check: exit 1 because the additive Mathlib name is
  `addSubgroupOf`, not `subgroupOf`.
- Second extension check: exit 1 because `Nat.card top` required an explicit
  simplification to `Nat.card A`.
- Repaired `lake env lean GaoLean\PGCapacity.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8678 jobs)`.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` exit 1).

## Exact remaining boundary

GMO must still produce its full/non-full alternative and, in the non-full
case, the strict subgroup, translation center, labelled concentrated set, and
lower bound consumed above. The full-spectrum closure and reflection channel
remain unassembled. No external theorem is asserted and no Gao equality is
claimed.
