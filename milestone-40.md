# Milestone 40: occurrence-labelled exchange selection and fillers

Status: `LEAN_FULL` for the endpoint/toggle/filler mechanics used by the
fixed-cardinality exchange; M10 remains `LEAN_PARTIAL` pending coefficient
coverage and the affine reverse construction.

## Checked conclusions

For an occurrence reservoir with `k` directions and `t` pairs per direction:

- its left and right endpoint sets are disjoint and their union has exactly
  `2kt` source labels;
- toggling any labelled pair subset selects exactly one endpoint from every
  pair, hence exactly `kt` labels;
- the toggled sum is the all-left baseline plus the sum of the selected
  direction vectors, using the reservoir's actual occurrence equations;
- if `kt≤d` and `d+kt≤|Ω|`, the toggled selection admits `d-kt` fillers chosen
  outside every reservoir endpoint, producing an exact-`d` labelled set.

## Fidelity boundary

This closes the endpoint non-reuse and filler-capacity paragraph of Corollary
2.1 / Theorem 3.1 in `affine-exchange01.md`. It does not yet prove that the
`q-1` copies in each independent direction realize every field coefficient,
nor that a prescribed affine exceptional witness extends to the desired sum.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Final single-file check: exit 0.
- Full build: 8710 jobs, exit 0.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan and scoped whitespace check: pass.
