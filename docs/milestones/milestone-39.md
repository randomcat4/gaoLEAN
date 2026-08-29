# Milestone 39: labelled affine-failure residue identity

Status: `LEAN_FULL` for the algebraic occurrence identity underlying formula
(3.4); M10 remains `LEAN_PARTIAL` because the reverse exchange construction
and one-translation group integration are not yet complete.

## Checked conclusion

For a labelled source `C : Ω → V`, an additive quotient map `φ`, affine-fibre
value `β`, and a selected label set `I`, Lean defines the exceptional part by
filtering the actual labels with `φ(C ω) ≠ β` and proves

`Σ_{ω∈I} φ(Cω) - |I|·β = Σ_{ω∈I_exceptional} (φ(Cω)-β)`.

It also proves the fixed-cardinality specialization and the equivalence:
two selections of the same cardinality have equal quotient sums exactly when
their labelled exceptional-offset sums agree. Repeated values are never
deduplicated.

## Fidelity boundary

This is the forward algebraic core of Theorem 3.1(3.4) in
`evidence/pr9-candidate/affine-exchange01.md`. It does not yet prove that every
exceptional-offset witness can be extended, with disjoint reservoir endpoints
and fillers, to a fixed-cardinality selection in the desired fibre.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Final single-file check: exit 0.
- Full build: 8709 jobs, exit 0.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan and scoped whitespace check: pass.
