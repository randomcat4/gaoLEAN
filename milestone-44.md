# M44: automatic affine-hyperplane geometry and certificate

Status: `LEAN_CHECKED` for the raw-support-to-certificate bridge and
`LEAN_PARTIAL` for the complete affine dichotomy.

`GaoFormal/Matching/AffineReverse.lean` now derives the non-full affine branch
from the original finite support hypotheses.  If the heavy support spans the
ambient space linearly but its vector span is proper, Lean chooses a support
point `α`, proves that the vector span is a codimension-one submodule, proves
`α` lies outside it, and places every support point in the affine fibre
`α + W`.

The same file then chooses the canonical quotient `W.mkQ`, sets `β = mkQ α`,
constructs the exact finite set of exceptional occurrence labels, and invokes
the M42 reverse theorem.  Thus callers no longer supply `W`, `α`, `φ`, `β`, or
`E` in this branch.

Verification receipt:

- target `lake build GaoFormal.Matching.AffineReverse`: 8663 jobs, exit 0;
- unified `lake build GaoFormal.AxiomAudit`: 8713 jobs, exit 0;
- both new declarations depend only on `propext`, `Classical.choice`, and
  `Quot.sound`.

This does not close M10.  The remaining affine obligation is the constructive
`e ≥ q - 1` full-exchange branch and its top-level split from the exceptional
certificate.  The rank-free residual-state producer and the rank-two,
rank-three, lower-bound, and final GAO-AR assembly obligations also remain.
