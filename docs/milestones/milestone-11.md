# Milestone P5b2e: balanced reflection/rotation literal ordering

Date: 2026-08-24 (America/New_York).

Status: elementary ordering implication `LEAN_CHECKED`. The reflection-channel
existence/assembly, PG-O3, and PG-GAO-v1 remain `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:29-36`: a positive even number of selected reflections,
  balanced plus/minus reflection signs, arbitrary rotation signs, and zero
  signed coordinate sum admit a product-one literal ordering. All selections
  are occurrence-labelled by lines 26-27.

## Compiled construction

- `pairedReflectionWord` alternates equal-length reflection sign classes.
- `balancedSignedWord` puts plus rotations in an even-parity gap and minus
  rotations in an odd-parity gap, then appends the remaining alternating
  reflection pairs.
- `prod_balancedSignedWord` proves the exact coordinate formula
  `sum R+ - sum R- + sum F+ - sum F-`; its zero case has product one.
- `multiset_balancedSignedWord` proves exact multiplicity preservation.
- `BalancedSignedAssignment.carrier_eq` partitions the selected multiset, not
  merely its value set. The final three theorems lift the explicit word to
  `HasProductOneOrdering`, `IsProductOneSelection`, and
  `HasProductOneSubsequenceOfCard`.

## Mechanical audit

- `lake env lean GaoLean\PGReflectionOrdering.lean`: exit 0 after local API and
  normalization repairs.
- Final `lake build`: exit 0, `Build completed successfully (8681 jobs)`.
- Unified axiom audit: exit 0. Audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound` (some use a subset).
- Forbidden-declaration scan: no matches (`rg` exit 1).

## Exact remaining boundary

This milestone proves the ordering implication once an exact balanced signed
assignment is supplied. It does not derive that assignment from the
high-reflection pair selection, the middle reflection reservoir, or GMO. The
earliest internal follow-on is the occurrence-labelled constructor connecting
those source selections to `BalancedSignedAssignment`; GMO's prescribed-
length output remains an external theorem blocker. No Gao equality is claimed.
