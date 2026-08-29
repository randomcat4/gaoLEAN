# Milestone P5b2i: middle full-spectrum occurrence consumer

Date: 2026-08-24 (America/New_York).

Status: the internal middle full-spectrum route is `LEAN_CHECKED`; production
of its GMO full-spectrum output is `LEAN_CONDITIONAL`. PG-GAO-v1 remains
`NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:245-279`: for `2≤a≤D`, set
  `e=2⌊a/2⌋`, `ell=2Q-e`; choose `e` reflections with balanced signs, use the
  weighted full `ell`-spectrum to cancel their signed vector contribution, and
  order the exact `2Q` occurrences to product one.

## Compiled closure

- `exists_balancedReflectionOccurrenceChoice_middle` selects the actual `e`
  distinct reflection positions and splits them into equal nonempty sign
  classes. Repeated reflection values are not deduplicated.
- `MiddleFullSpectrumOutput` freezes the exact occurrence-labelled signed
  rotation/reflection data received after the full-spectrum choice.
- `map_occurrenceValue_eq_rot` and `map_occurrenceValue_eq_refl` prove concrete
  group-carrier fidelity for lists of source positions.
- `toBalancedSignedAssignment` proves exact selected-multiset equality and
  signed-sum fidelity.
- `card_selection` combines the certified `ell` and `e` counts with the middle
  arithmetic to prove exact cardinality `2Q`.
- `hasProductOneSubsequenceOfTwice_of_middleFullSpectrumOutput` composes the
  result with the checked balanced literal ordering.

## Mechanical audit

- `lake env lean GaoLean\PGMiddleReflection.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8686 jobs)`.
- Unified axiom audit: exit 0; declarations use only `propext`,
  `Classical.choice`, and `Quot.sound` (individual declarations use subsets).
- Forbidden-declaration scan: no matches (`rg` exit 1).
- No `Scratch.lean` is present; `.lake/` remains ignored.

## Exact remaining boundary

The project does not assert GMO Corollary 1.3. The remaining full-spectrum
obligation is its faithful application to the rotation label sequence with
target `ell`, yielding signed rotation occurrences whose contribution cancels
the internally constructed balanced reflection contribution. Once represented
as `MiddleFullSpectrumOutput`, every remaining occurrence, count, carrier and
ordering step is checked. No Gao equality is claimed.
