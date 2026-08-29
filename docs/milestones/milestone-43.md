# M43: one-translation arithmetic, extraction, and pullback

Status: `LEAN_CHECKED` internally and `LEAN_CONDITIONAL` at the remaining
affine/reduction producer interfaces.

`GaoLean/GAOAROneTranslation.lean` proves the rank-uniform heavy-support and
availability inequalities, identifies exactly which labelled rotations enter
the translated residual subspace, and proves that no rotation outside the old
residual subspace can enter it.

The group layer now performs the second quotient extraction itself.  It
constructs the labelled maximum quotient-zero-sum part `Bprime`, obtains the
actual defect `d`, consumes a source-faithful `FullExactExchange`, builds the
exact `2Q` all-rotation product-one selection, and pulls the same occurrence
labels back through the single translation when `Q • α = 0`.  A subtype bridge
connects affine exchange on the residual subgroup to the list-facing
occurrence selection.

Verification receipt:

- target build `GaoLean.GAOAROneTranslation`: 8672 jobs, exit 0;
- full build: 8713 jobs, exit 0;
- unified axiom audit: exit 0, only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden declaration scan and scoped `git diff --check`: pass.

This closes the planned M10-B guard/arithmetic/extraction/completion/pullback
mechanics.  It does not prove the manuscript's rank-free residual-state
producer, the complete affine dichotomy, the rank-two/rank-three upper bounds,
or a top-level unconditional `GAO-AR-v1` declaration.
