# Milestone P5b2n: source-faithful rotation-only channel

Date: 2026-08-24 (America/New_York).

Status: the Section 5.2 rotation-channel consumer and positive `ZR` step
construction are `LEAN_CHECKED`; the preparation theorem is
`LEAN_CONDITIONAL`. PG-GAO-v1 is `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:482-566`, especially (5.12)-(5.17).

## Compiled closure

- `RotationChannelAlternative` keeps `C` and `Bprime` separate. Its full
  branch forms the actual labelled selection `(C \ D0) ∪ Bprime`; its
  non-full count is measured against `M=|C|`.
- `RotationChannelPreparedData.hasAllRotationProductOneSubsequence` closes the
  full algebra or performs strict capacity descent, translated smaller `ZR`,
  and exact pullback.
- `concreteZRPositiveStep_of_rotationChannelPreparations` constructs the
  positive `ZR` step for arbitrary auxiliary sequences without assuming its
  conclusion.

The older `OrdinarySpectrumAlternative` is only an abstract single-reservoir
consumer and is not used as the faithful source interface when `Bprime` is
nonempty.

## Mechanical audit

- `lake build GaoLean.PGRotationChannel`: exit 0 (`8670` target jobs).
- Final `lake build`: exit 0, `Build completed successfully (8693 jobs)`.
- Unified axiom audit: exit 0; new theorems use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` raw exit 1).

## Exact remaining boundary

The labelled quotient greedy extraction of `B0`, `Bprime`, `z`, and `d`, and
the derivation of `RotationChannelAlternative` from ordinary GMO are not yet
formalized. No external theorem or desired controller conclusion is declared
as an axiom.
