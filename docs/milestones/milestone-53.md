# Milestone M53: Olson formula and unconditional Proposition 3.1

Status: `LEAN_CHECKED`; manuscript status remains `LEAN_CONDITIONAL` only at
the GJM and GMO source theorems.

`GaoLean/PGOlson.lean` proves the exact ordinary Davenport constant for a
finite product of cyclic `p`-groups. The upper bound is obtained from a
literal group-algebra product and augmentation-ideal nilpotence; the matching
lower bound is an occurrence-labelled zero-sum-free sequence with exactly
`p ^ mu_i - 1` copies of each coordinate generator.

Lean then applies Mathlib's finite-abelian-group classification and derives
from the `IsPGroup p` cardinality condition that every nontrivial cyclic
primary factor has prime `p`. This supplies the invariant-product equivalence
and proves the Olson formula for an arbitrary finite abelian p-group.

The exported theorem
`plusMinusDavenportAtMost_half_of_isPGroup` is the literal Proposition 3.1
needed by the 13-page manuscript: for odd prime `p`, any exact ordinary
Davenport value `D` yields `D_pm(A) <= (D + 1) / 2`. `GAOARFinal` now also
derives the parity of `D`, the restricted-coefficient output, and subgroup
plus-minus bounds internally.

Server verification used Lean 4.32.0 / Mathlib v4.32.0. The full build
completed 8739 jobs. Unified axiom output for the new declarations contains
only `propext`, `Classical.choice`, and `Quot.sound`; no theorem premise in the
final package now encodes Olson or Proposition 3.1. The remaining
load-bearing boundaries are GJM small-Davenport and GMO existence/structural
theorems.
