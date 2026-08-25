# Verification rounds

## Round 1 — 2026-08-26

- Audited the final manuscript theorem and its proof DAG.
- Froze `GAOARV1Statement` without an upper-bound claim.
- Checked the represented group cardinality.
- Server build: `GaoLean.GAOARStatements`, 8660 jobs, successful.
- No paper-specific axiom or placeholder introduced.

## Round 2 — 2026-08-26

- Proved every below-threshold counterexample from an explicit Olson
  ordinary-Davenport equality input.
- Server build: `GaoLean.GAOARLowerBound`, 8689 jobs, successful.
- Axiom print contains only `propext`, `Classical.choice`, and `Quot.sound`.
- Froze the occurrence-labelled `{+1,-1}` specialization of GMO Corollary
  1.3, retaining both coset conditions and the exact concentration count.

## Round 3 — 2026-08-26

- Closed the rank-two low-reflection branch `a ≤ 1` from the explicit
  ordinary-GMO provider.
- Proved the manuscript-internal bound `D_±(F_q²) ≤ q`: binary subset-sum
  collision for `q ≥ 5`, and linear dependence over `F₃` for `q = 3`.
- Closed the rank-two high-reflection branch `a ≥ 2q` from the explicit
  weighted-GMO provider, with the internal plus-minus bound no longer an
  assumption.
- Server build: `GaoLean.GAOARRankTwo`, 8687 jobs, successful.
- Axiom prints contain only `propext`, `Classical.choice`, and `Quot.sound`;
  the middle range remains explicitly open.

## Round 4 — 2026-08-26

- Transported the exact structural GMO alternative from the labelled
  rotation-coordinate sequence back to original source occurrences.
- In the full-spectrum branch, combined the selected rotations with a
  balanced even reflection choice and closed the exact `2q²` ordering.
- In the non-full branch, preserved the proper subgroup and both weight-coset
  conditions, then derived the source-labelled subgroup concentration.
- Specialized all numerical gates for `2 ≤ a ≤ 2q-1`; the remaining rank-two
  obligation is exactly the `K=0`/line-completion part of the manuscript.

## Round 5 — 2026-08-26

- Closed the `K = 0` non-full middle leaf from the explicit generalized-
  dihedral small-Davenport provider and the existing checked identity-padding
  construction.
- Proved internally that every nonzero proper additive subgroup of `F_q²` is
  a one-dimensional `ZMod q` subspace, hence both it and its quotient have
  cardinality `q`.
- No classification assumption was added; the remaining rank-two branch is
  now literally the manuscript's one-dimensional line completion.
