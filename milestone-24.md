# Milestone P5b2r: labelled reflection quotient extraction

Date: 2026-08-24 (America/New_York).

Status: the internal reflection-containing quotient extraction, lifted defect,
parity, and (5.6)--(5.9) arithmetic are `LEAN_CHECKED`. Quotient
small-Davenport and signed GMO remain explicit proposition parameters.
PG-GAO-v1 is `NOT_FORMALIZED`.

## Frozen source map

- `A-R6/proof.md:413-480`, especially (5.6)--(5.11).

## Compiled closure

- `exists_reflectionQuotientExtraction` chooses a maximum-cardinality
  occurrence-labelled quotient-product-one `U` containing a reflection; its
  exact complement `R` is quotient product-one-free.
- `exists_liftedQuotientOrdering` lifts a quotient ordering back to the
  original labelled multiset even when quotient images collide.
- `positive_even_selectedReflectionCount` proves that `U` has a positive even
  number of reflection occurrences; the lifted product has defect `z∈K`.
- `exists_reflectionChannelPreGMOData` constructs `C,B,U,R,M,c,tau,m,z`, proves
  all typing/disjointness, `tau=D-|R|`, and `|U|+m=2Q`.
- The Davenport lower bound, signed-GMO length threshold, and (5.5)/(5.8)
  target bound `m≥|K|` are checked with natural-number boundary cases.
- `reflectionChannelPreparation_of_extraction` leaves a narrow
  `ReflectionChannelGMOProvider`; the full output is forced to be
  `U∪Dsel` with `Dsel⊆C` and `|Dsel|=m`.
- `concretePGO3ControllerSkeleton_of_channelGMOProviders` eliminates both
  unrestricted channel-preparation families.

Maximum selection does not encode a particular procedural greedy order, but
proves exactly the labelled partition/maximality postconditions used later.

## Mechanical audit

- Direct module check: exit 0.
- Targeted extraction/controller build: exit 0, 8681 jobs.
- Final `lake build`: exit 0, 8695 jobs.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan over Lean sources: no matches (raw `rg` exit 1,
  normalized exit 0).
- `Scratch.lean`: absent. `.lake/` remains ignored.

## Exact remaining boundary

`ReflectionChannelGMOProvider` is not proved. Its full branch still requires
the published signed prescribed-length GMO theorem plus the exact
ordering/interleaving bridge producing a `BalancedSignedAssignment` on
`U∪Dsel`; its non-full branch requires the published weighted-coset output.
The quotient small-Davenport/Davenport identities (GJM/Olson-facing) also
remain external. PG-O4 and PG-GAO-v1 remain outside the certificate.
