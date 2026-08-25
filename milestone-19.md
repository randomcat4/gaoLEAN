# Milestone P5b2m: exhaustive reflection-count dispatch

Date: 2026-08-24 (America/New_York).

Status: the complete internal Section 4 numerical dispatch is
`LEAN_CHECKED`; prescribed-length outputs and the residual controller remain
explicit conditions. PG-GAO-v1 is `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:193-216`: the `a≤1` ordinary-rotation branch.
- `A-R6/proof.md:218-243`: the `a≥D+1` weighted same-type-pair branch.
- `A-R6/proof.md:245-312`: the middle full/non-full branch and first descent.

## Compiled closure

- `ReflectionRegimeOutputs` records one conditional occurrence-output
  interface for each of the three regimes.  A false regime creates no output
  obligation.
- `hasProductOneSubsequenceOfTwice_of_reflectionRegimeOutputs` applies the
  checked arithmetic trichotomy and dispatches to the low, high, or middle
  consumer, always obtaining an exact `2Q` product-one subsequence.

## Mechanical audit

- `lake env lean GaoLean\PGReflectionRegimes.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8690 jobs)`.
- Unified axiom audit: exit 0; the new theorem uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` exit 1).
- No `Scratch.lean` is present; `.lake/` remains ignored.

## Exact remaining boundary

The dispatcher does not derive any occurrence output from GMO.  The low and
high regimes require their ordinary/weighted prescribed-length output; the
middle regime requires its full/non-full output and, in the non-full case, an
actual controller.  Positive-subgroup `RC/ZR` construction, external GMO,
Troi–Zannier/CFS, Olson, and GJM inputs remain unformalized or explicit
parameters.  No Gao equality is claimed.
