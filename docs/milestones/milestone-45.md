# M45-A: labelled variable-direction quotient coverage

Status: `LEAN_CHECKED` for the quotient-coverage lemma; M45-B occurrence
assembly remains open.

`GaoFormal/Matching/VariableDirectionCoverage.lean` defines subset sums on
the label powerset of a finite indexed family.  Repeated increment values are
therefore retained as distinct selectable occurrences.  By finite-set
induction and Mathlib's prime cyclic Cauchy--Davenport theorem, it proves that
`q - 1` labelled nonzero increments in `ZMod q` have every field element as a
labelled subset sum.

Verification receipt:

- target `lake build GaoFormal.Matching.VariableDirectionCoverage`: 8664
  jobs, exit 0;
- unified `lake build GaoFormal.AxiomAudit`: 8714 jobs, exit 0;
- the new theorem depends only on `propext`, `Classical.choice`, and
  `Quot.sound`.

This is exactly the quotient-direction coverage needed by the manuscript's
`e ≥ q - 1` cross-pair argument.  The next task is to construct the unused
heavy value, select disjoint heavy/exceptional occurrence endpoints, combine
their toggles with the kernel reservoir, and supply fillers.  Work is paused
at that boundary for migration to the server.
