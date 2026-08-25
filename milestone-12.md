# Milestone P5b2f: signed pair output to exact `2q` product one

Date: 2026-08-24 (America/New_York).

Status: signed-pair post-processing `LEAN_CHECKED`. The GMO output,
same-type occurrence pairing, reflection-channel assembly, PG-O3, and
PG-GAO-v1 remain `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:228-243`: reflection pairs carry label `x-y`, rotation pairs
  carry `u+v`; GMO selects exactly `Q` signed pairs, at least one reflection
  pair; negative reflection pairs are reversed; Section 1 then gives an exact
  `2Q` product-one ordering.

## Compiled construction

- `pairCoordinates` flattens ordered pairs with multiplicity.
- `reflectionPlusCoordinates` / `reflectionMinusCoordinates` implement the
  positive orientation and negative-weight reversal.
- `signedCoordinateSum_eq_weightedPairSum` proves the coordinate sign sum is
  exactly the sum of weighted `u+v` and `x-y` labels.
- `BalancedSignedPairAssignment` records exactly `q` pairs, at least one
  reflection pair, the exact selected multiset, and weighted label sum zero.
- `hasProductOneSubsequenceOfTwice_of_balancedSignedPairAssignment` composes
  this data with P5b2e and proves an exact `2*q` product-one selection.

## Mechanical audit

- `lake env lean GaoLean\PGReflectionPairs.lean`: exit 0 after two local
  cardinality-normalization repairs.
- Final `lake build`: exit 0, `Build completed successfully (8682 jobs)`.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound` occur (some declarations use a subset).
- Forbidden-declaration scan: no matches (`rg` exit 1).

## Exact remaining boundary

The theorem is a consumer of exact signed-pair data. It does not pair the
original labelled reflection/rotation occurrences, prove the reservoir count,
or derive the weighted selection from GMO. The next internal leaf is that
disjoint same-type occurrence pairing and its carrier/count interface. GMO's
prescribed-length theorem remains external. No Gao equality is claimed.
