# Milestone 29: odd-prime p-group cardinality bridge

Status: `LEAN_PARTIALLY_CHECKED` overall; this numerical edge is
`LEAN_CHECKED`.

`GaoLean/PGPGroupNumerics.lean` uses the pinned Mathlib theorem
`IsPGroup.iff_card` to write `Nat.card A = p^n`. For prime `p≠2`,
`Prime.odd_of_ne_two` makes `p` odd and `Odd.pow` makes the cardinality odd.

`pgGaoV1_of_externalUpperInputs_and_ordinaryDavenport_of_pgroup` therefore no
longer accepts `Odd (Nat.card A)` as a separate parameter. It still requires
the exact upper source package and `D≤|A|`.

- Single-file compile: exit 0.
- Targeted build: exit 0, 8689 jobs.
- Full build: exit 0, 8700 jobs.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden declaration scan: no matches, normalized exit 0.

The earliest numerical blocker is now `D≤|A|`; the remaining mathematical
blockers are the upper-side external theorem providers.
