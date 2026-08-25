# Milestone P5b2h: complete internal high-reflection consumer

Date: 2026-08-24 (America/New_York).

Status: the internal high-reflection route is `LEAN_CHECKED`; production of
the weighted prescribed-length output is `LEAN_CONDITIONAL`. PG-GAO-v1 remains
`NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:218-243`: pair by type, verify (4.1), apply weighted GMO to
  select exactly `Q` pairs with signed label sum in `Q A`, force a reflection
  pair using `b≤2Q-1`, reverse negative reflection pairs, and order exactly
  `2Q` occurrences to product one.

## Compiled closure

- `highReflection_pairThreshold` proves the exact (4.1) inequality from the
  odd-`D` arithmetic and the PG-PM bound.
- `highReflection_rotationCount_le` proves `b≤2Q-1` from the source counts.
- `canonicalSameTypePairReservoir_highReflection_ready` verifies both the
  weighted-GMO length threshold and that fewer than `Q` rotation pairs exist.
- `PrescribedSignedReservoirTargetOutput` freezes the occurrence-labelled GMO
  output without strengthening it: the selected signed sum equals `Q • z` for
  some `z`, i.e. belongs to `Q A`.
- `toZeroOutput` proves `Q A={0}` from `Q=Nat.card A`.
- `toSignedOccurrencePairSelection` proves selected rotation capacity and
  derives the presence of a reflection pair; it also derives pair typedness
  from canonical-reservoir membership.
- `hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput` composes the
  entire checked chain to an exact `2Q` occurrence-labelled product-one block.

## Mechanical audit

- `lake env lean GaoLean\PGHighReflection.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8685 jobs)`.
- Unified axiom audit: exit 0; declarations use only `propext`,
  `Classical.choice`, and `Quot.sound` (individual declarations use subsets).
- Forbidden-declaration scan: no matches (`rg` exit 1).
- No `Scratch.lean` is present; `.lake/` remains ignored.

## Exact remaining boundary

No theorem in this project asserts weighted GMO. The remaining high-reflection
obligation is a faithful theorem application translating the published
prescribed-length result, with all its hypotheses, into
`PrescribedSignedReservoirTargetOutput`. All downstream occurrence, capacity,
reflection-forcing, target-annihilation and ordering steps are checked. No Gao
equality is claimed.
