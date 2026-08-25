# Milestone P5b2k: middle full/non-full assembly

Date: 2026-08-24 (America/New_York).

Status: the post-GMO middle-route case split is `LEAN_CHECKED`.  Its output
alternative and controller remain explicit inputs. PG-GAO-v1 is still
`NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:275-279`: full spectrum supplies signed rotation occurrences
  cancelling a balanced reflection choice.
- `A-R6/proof.md:281-312`: non-full spectrum supplies a proper-subgroup
  concentration and routes it through `K=0` or the residual controller.

## Compiled closure

- `MiddleSpectrumAlternative` is proposition-valued but carries actual output
  data: `Nonempty MiddleFullSpectrumOutput` on the left, or an existential
  proper-subgroup `MiddleNonfullConcentrationOutput` on the right.
- `hasProductOneSubsequenceOfTwice_of_middleSpectrumAlternative` eliminates
  the disjunction and invokes the separately audited full and non-full
  consumers, producing one exact `2Q` product-one subsequence conclusion.

The interface is deliberately the minimal downstream projection of the GMO
alternative.  It does not assert the published theorem or encode unused source
hypotheses as if they had been proved.

## Mechanical audit

- `lake env lean GaoLean\PGMiddleAssembly.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8688 jobs)`.
- Unified axiom audit: exit 0; the new theorem uses only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan: no matches (`rg` exit 1).
- No `Scratch.lean` is present; `.lake/` remains ignored.

## Exact remaining boundary

The project does not derive `MiddleSpectrumAlternative` from GMO Corollary 1.3
and does not inhabit the positive-subgroup `RC/ZR` steps needed to construct
the controller skeleton.  The `K=0` base is still conditional on the isolated
GJM small-Davenport input.  No Gao equality is claimed.
