# Milestone P5b2l: at-most-one-reflection branch

Date: 2026-08-24 (America/New_York).

Status: the internal `a≤1` route is `LEAN_CHECKED`; ordinary GMO output is
`LEAN_CONDITIONAL`. PG-GAO-v1 remains `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:205-216`: from `a≤1`, obtain `b≥2Q+D-1`; ordinary GMO
  selects `2Q` rotations with sum in `2Q • A`, and `2Q • A={0}`.

## Compiled closure

- `lowReflection_rotationCount_lower` proves the exact source threshold.
- `LowReflectionTargetOutput` records actual occurrence labels, rotation
  typing, exact cardinality, and the unstrengthened target equation
  `coordinateSum=(2Q)•z`.
- `coordinateSum_eq_zero` derives target annihilation from `Q=Nat.card A`.
- the two final consumers produce an exact all-rotation block and the ordinary
  exact-cardinality product-one conclusion.

## Mechanical audit

- `lake env lean GaoLean\PGLowReflection.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8689 jobs)`.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound` (individual declarations use subsets).
- Forbidden-declaration scan: no matches (`rg` exit 1).
- No `Scratch.lean` is present; `.lake/` remains ignored.

## Exact remaining boundary

The project does not formalize the ordinary GMO prescribed-length theorem or
derive `LowReflectionTargetOutput` from it.  No Gao equality is claimed.
