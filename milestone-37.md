# Milestone 37: exact `C₃` plus-minus exception

Status: `LEAN_FULLY_DISPROVED` for the frozen uniform A5 gap-two claim and
for the raw A6 gap-three specialization at `C₃`.  The repaired exceptional
group classifications remain separate and are not claimed here.

## Checked conclusions

- Every two-occurrence sequence in `ZMod 3` has a nonempty labelled
  plus-minus zero sum.
- The one-occurrence sequence `[1]` has none.
- Hence the occurrence-sensitive plus-minus Davenport threshold of `C₃` is
  exactly two.
- In particular, a uniform A5 inequality that forces `D±(C₃) ≤ 1` is false,
  and a raw A6 inequality that forces `D±(C₃) ≤ 0` is false.

The positive proof supplies explicit source-position selections and sign
functions.  The negative proof also reasons on labelled positions; it does
not collapse repeated values into a set.

## Fidelity boundary

Natural-language sources:
`gao0824/research/residual-a5-entry-2026-08-24/` and
`gao0824/research/residual-a6-entry-2026-08-24/`.  This milestone checks the
common `C₃` obstruction only.  It does not prove the repaired A5/A6
classification theorems or the separate explicit A6 two-exit counterexample.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Final single-file check: exit 0.
- Full build: 8707 jobs, exit 0.
- Unified axiom audit: exit 0; the new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan and scoped whitespace check: pass.
