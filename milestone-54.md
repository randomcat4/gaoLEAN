# Milestone M54: GJM small-Davenport closure

Status: `LEAN_CHECKED`; the 13-page manuscript remains `LEAN_CONDITIONAL`
only at the GMO source theorem.

`GaoLean/PGGJM.lean` gives a direct occurrence-labelled proof of the
Godara--Joshi--Mazumdar small-Davenport bound for a generalized-dihedral group
with any finite abelian kernel. For a source of length `D + 1`, it lists the
adjacent coordinate differences along the canonical path of reflection
occurrences and appends all rotation coordinates. This additive list has
length at least `D`, so the ordinary Davenport property gives a nonempty zero
sum.

Selected adjacent edges are mapped back to their source endpoints. Endpoints
shared by consecutive selected edges cancel; the remaining positive and
negative boundary selections are disjoint, have equal cardinality, and retain
their original occurrence labels. Together with the selected rotations, the
existing balanced-sign ordering theorem gives an actual product-one
subselection. Hence every product-one-free selection has at most `D` terms.

The matching length-`D` lower witness was already constructed from an
ordinary zero-sum-free word plus one reflection, so the two directions supply
the manuscript's exact small-Davenport identity. `GAOARFinal` now derives the
ambient and all quotient versions internally; neither remains in the final
input package.

Server verification used Lean 4.32.0 / Mathlib v4.32.0. The full build
completed 8740 jobs. The new declarations depend only on `propext`,
`Classical.choice`, and `Quot.sound`. The sole remaining load-bearing source
boundary is GMO existence/structural theory.
