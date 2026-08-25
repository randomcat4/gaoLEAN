# M42: labelled affine reverse certificate

Status: `LEAN_CHECKED` for the stated affine-exchange consumers.

`GaoFormal/Matching/AffineReverse.lean` now constructs the kernel reservoir
directly from the heavy support, preserves an arbitrary preselected subset of
exceptional occurrence labels, chooses all fillers outside both the
exceptional set and reservoir endpoints, and corrects the remaining error in
the kernel with `q-1` labelled copies of each independent direction.

The resulting theorem is the exact two-way labelled certificate used in
formula (3.4).  The same module also exposes a source-shaped full affine
exchange theorem: affine spanning plus the half-cardinality condition yields
every exact-`d` target without requiring the caller to supply a reservoir.

Verification receipt:

- target build `GaoFormal.Matching.AffineReverse`: exit 0;
- full build after M43: 8713 jobs, exit 0;
- unified axiom audit: exit 0, only `propext`, `Classical.choice`, and
  `Quot.sound`;
- forbidden declaration scan: no `sorry`, `admit`, `axiom`, `unsafe`, or
  `native_decide`.

This closes the reverse-certificate and full-exchange consumers.  It does not
yet package the complete geometric dichotomy which constructs the affine
hyperplane and proves the `e ≥ q-1` branch from the manuscript's raw residual
hypotheses.
