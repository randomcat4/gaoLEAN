# Milestone P5b2g: occurrence reservoir and signed-selection bridge

Date: 2026-08-24 (America/New_York).

Status: canonical same-type occurrence pairing and the explicit signed
selection consumer are `LEAN_CHECKED`. GMO prescribed-length existence,
remaining branch assembly, PG-O3, and PG-GAO-v1 remain `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:220-230`: pair the rotation occurrences and reflection
  occurrences separately; use the exact resulting number of pairs.
- `A-R6/proof.md:228-243`: apply prescribed-length GMO to weighted pair labels,
  select exactly `Q` pairs including a reflection pair, reverse negative
  reflection pairs, and obtain an exact `2Q` product-one word.

## Compiled construction

- `pairUp` and `unpairedSuffix` decompose any occurrence list into consecutive
  disjoint pairs plus at most one terminal occurrence.
- `canonicalSameTypePairReservoir` applies this construction separately to
  `rotationOccurrences` and `reflectionOccurrences`, proves type correctness,
  exact endpoint cover, global endpoint `Nodup`, and floor pair counts.
- `canonicalSameTypePairReservoir_pairCount_of_odd_total` proves the exact
  pair-count identity under the source odd-total hypothesis.
- `SignedOccurrencePairSelection` records actual reservoir pairs split by sign
  and type, exact pair count, a nonempty reflection part, occurrence endpoint
  disjointness, and zero weighted coordinate sum.
- `toBalancedSignedPairAssignment` normalizes actual group occurrences to the
  checked `u+v` and `x-y` pair-coordinate interface.
- `hasProductOneSubsequenceOfTwice_of_signedOccurrencePairSelection` produces
  the exact `2*q` occurrence-labelled product-one selection.

## Mechanical audit

- `lake env lean GaoLean\PGPairReservoir.lean`: exit 0.
- `lake env lean GaoLean\PGPairSelection.lean`: exit 0.
- Final `lake build`: exit 0, `Build completed successfully (8684 jobs)`.
- Unified axiom audit: exit 0; audited declarations use only `propext`,
  `Classical.choice`, and `Quot.sound` (individual declarations use subsets).
- Forbidden-declaration scan: no matches (`rg` exit 1).
- `Scratch.lean` is absent; no scratch file is part of the deliverable.

## Exact remaining boundary

The compiled code does not assert GMO. The first missing theorem must derive a
`SignedOccurrencePairSelection` of the canonical reservoir from the actual
published prescribed-length GMO output, including occurrence-labelled selected
indices and the forced presence of a reflection pair. Until that source theorem
and translation are formalized or supplied as an explicit audited parameter,
this branch remains conditional. No Gao equality is claimed.
