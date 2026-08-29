# Milestone P5b2j: middle non-full front end

Date: 2026-08-24 (America/New_York).

Status: the post-concentration middle non-full front end is `LEAN_CHECKED`.
Production of the GMO concentration and construction of the positive-subgroup
controller are explicit external predecessors. PG-GAO-v1 remains
`NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:281-291`: non-full GMO gives a proper `K<A`, at least
  `b-|A/K|+2` concentrated rotation occurrences, and weighted coset conditions
  placing `x,-x` in one `K`-coset; oddness forces `x∈K`.
- `A-R6/proof.md:293-312`: route `K=0` through identity padding and route
  `0<K<A` into the controller of Section 5.  Those controller internals were
  separated in earlier milestones; this milestone invokes their explicit
  combined interface.

## Compiled closure

- `MiddleNonfullConcentrationOutput` freezes the minimal downstream projection:
  a proper subgroup, actual labelled rotation occurrences, exact cardinality
  lower bound, and both weighted coset memberships for each coordinate.
- `odd_natCard_quotient_of_odd_natCard` derives oddness of `A/K` from oddness
  of the ambient finite group.
- `concentrated_subset_rotationOccurrencesIn` proves occurrence-wise that the
  concentrated rotations lie in `K`; repeated values remain distinct labels.
- `rotationCapacity` transfers the exact lower bound to the controller pool.
- `hasProductOneSubsequenceOfTwice_of_middleNonfullConcentration` applies the
  fixed-source component of an explicit `PGO3ControllerSkeleton` and returns
  the exact `2Q` product-one subsequence.

The source's additional ordinary-coset condition is not stored in the minimal
projection because this front end never consumes it. No stronger existence
claim is introduced.

## Mechanical audit

- `lake env lean GaoLean\PGMiddleNonfull.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8687 jobs)`.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` exit 1).
- No `Scratch.lean` is present; `.lake/` remains ignored.

## Exact remaining boundary

Lean does not yet derive `MiddleNonfullConcentrationOutput` from GMO Corollary
1.3, and it does not construct the nonzero positive `RC/ZR` steps required by
the controller skeleton.  The `K=0` base remains conditional on the explicit
GJM-style small-Davenport input already isolated in `PGBase.lean`.  No Gao
equality is claimed.
