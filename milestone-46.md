# M45-B / M46: complete affine exchange dichotomy

Status: `LEAN_CHECKED` for the raw-support affine dichotomy and its
large-exceptional-set full-exchange branch.  Overall `GAO-AR-v1` remains
`LEAN_PARTIALLY_CHECKED` because later residual-state, low-rank, lower-bound,
and top-level assembly edges are separate obligations.

`GaoFormal/Matching/FullExchangeBranch.lean` now constructs the entire
`e ≥ q - 1` branch on occurrence labels:

- a maximum independent-difference matching supplies the kernel reservoir;
- strict half-cardinality leaves an unused heavy support value;
- `q - 1` exceptional labels are paired with distinct occurrences of that
  heavy value, disjointly from every kernel endpoint;
- their nonzero one-dimensional quotient increments cover every quotient
  target;
- kernel toggles correct the remaining error and fillers reach exact
  cardinality without endpoint reuse.

The theorem
`fullExchange_or_smallAffineHyperplaneCertificate` starts only from the raw
heavy-support hypotheses.  It returns full exact exchange when the affine span
is full or when the exceptional set has at least `q - 1` labels.  Otherwise it
returns a canonical codimension-one quotient certificate with
`E.card ≤ q - 2` and the exact labelled exceptional-subset equivalence.

Verification receipt:

- target `lake build GaoFormal.Matching.FullExchangeBranch`: 8665 jobs,
  exit 0;
- all new declarations report only `propext`, `Classical.choice`, and
  `Quot.sound` in the target build;
- the unified build, unified axiom audit, and forbidden-declaration scan are
  recorded in `build-log.md` after the final repository gate.

This closes the affine-dichotomy item frozen after M44/M45-A.  It does not by
itself prove the complete arbitrary-rank Gao constant.
