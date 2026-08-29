# Milestone 31: finite Davenport cardinality bound

Status: `LEAN_PARTIALLY_CHECKED` overall; this milestone is `LEAN_CHECKED`.

## Result

`GaoLean/PGDavenportBound.lean` proves, without an external theorem parameter,
that every length-`|A|` list in a finite additive group has a nonempty
occurrence-labelled zero-sum selection. It uses two equal members among
`|A|+1` prefix sums and selects their exact half-open interval in the source.
Consequently
`ordinaryDavenportConstant_le_natCard : IsOrdinaryDavenportConstant A D →
D ≤ Nat.card A` is checked.

`PGSourceAssembly.lean` now derives this numerical fact internally.
`PGGaoRemainingInputs` has been narrowed to only
`PGGaoExternalUpperInputs`; no lower witness, oddness field, or `D≤|A|` field
remains.

## Fidelity boundary

- Natural-language anchor: `dossiers/2026-08-23/frozen_obligation_pg-v1.md:30`.
- Source selections are `Finset (Fin s.length)`, not sets of values.
- The Lean theorem is stronger in domain than needed: finite additive groups,
  rather than only finite abelian p-groups.
- The external upper package is still a proposition parameter. This milestone
  does not prove any ordinary/signed GMO, GJM/Olson, spectrum, or outer-regime
  existence theorem and does not prove PG-GAO-v1 unconditionally.

## Mechanical evidence

- Pinned toolchain: Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- New-module build: exit 0, 8660 jobs.
- Full build: exit 0, 8701 jobs.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`,
  `Quot.sound`.
- Forbidden declaration scan: no matches, normalized exit 0.
- Scoped whitespace check: exit 0.

## Exact next blocker

Construct `PGGaoExternalUpperInputs` from faithful formal statements of the
ambient/quotient small-Davenport facts, low/high prescribed-length outputs,
middle spectrum alternative, and ordinary/signed GMO providers. No purely
numerical residual field remains.
