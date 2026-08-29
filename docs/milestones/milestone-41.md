# Milestone 41: finite-field coefficient coverage and full exchange completion

Status: `LEAN_FULL` for the fixed-cardinality exchange theorem from a
finrank-sized occurrence reservoir. The complete affine alternative and
one-translation group route remain `LEAN_PARTIAL`.

## Checked conclusions

Let `q` be prime. Lean proves directly, without an external additive theorem,
that `q-1` labelled copies of a direction realize every coefficient in
`ZMod q`: the canonical representative `a.val` selects that many copies.
Selections for distinct directions are combined without label collision.

Consequently, a reservoir whose independent direction family spans the
ambient `ZMod q`-space realizes every coefficient vector. Combined with M40,
if `kt≤d` and `d+kt≤|Ω|`, every target `y` has an exact-`d` labelled selection
with sum `y`. A finrank-sized independent reservoir automatically satisfies
the spanning hypothesis.

## Fidelity boundary

This mechanically closes the main fixed-cardinality conclusion of Corollary
2.1 in `affine-exchange01.md` once M9 supplies the advertised reservoir. The
remaining Theorem 3.1 work is to construct the hyperplane reservoir and prove
the reverse extension while preserving a preselected exceptional label set;
then the one-translation group pullback must be assembled.

## Mechanical evidence

- Pinned Lean 4.32.0 / Lake 5.0.0-src+8c9756b.
- Final single-file check: exit 0.
- Full build: 8711 jobs, exit 0.
- Unified axiom audit: exit 0; new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Forbidden-declaration scan and scoped whitespace check: pass.
