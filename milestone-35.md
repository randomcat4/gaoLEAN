# Milestone 35: sharp characteristic-two boundary

Status: `LEAN_FULLY_CHECKED` for the frozen `F₂²` boundary witness.  This does
not change the status of M10, GAO-AR-v1, or PG-GAO-v1.

## Result

`GaoFormal/Matching/CharacteristicTwoBoundary.lean` proves both halves of the
exact example:

- a one-edge independent-difference matching exists on all four points of
  `F₂²`;
- no two-edge independent-difference matching exists.

For the negative half, endpoint injectivity and equal finite cardinalities
make the four endpoints a permutation of the plane.  Their sum is zero, so in
characteristic two the two edge differences are equal, contradicting linear
independence.  `native_decide` is used only for the fixed finite cardinality
and the sum of all four explicit plane elements, not to decide the quantified
nonexistence theorem.

## Fidelity boundary

This is exactly the sharp characteristic-two boundary stated after Theorem
1.1 in `evidence/pr9-candidate/independent-difference-matching01.md`.  The
module proves the matching number is one; it does not claim the full defect
classification for every characteristic-two affine set.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Single-file check: exit 0.
- Full build, unified axiom audit, forbidden-declaration scan, and scoped
  whitespace check are recorded in `build-log.md`.
