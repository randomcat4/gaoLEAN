# Milestone R3-P/RF/Z: complete rank-three and final conditional assembly

Status: `LEAN_CONDITIONAL`.

`GaoLean/GAOARRankThreePlane.lean` closes the full plane-stabilizer descent,
including the second structural-GMO non-full branch and its zero/line split.
`GaoLean/GAOARRankThreeCompletion.lean` assembles the complete rank-three
upper bound.

`GaoLean/GAOARResidualController.lean` then constructs the arbitrary-rank
simultaneous `RC`/`ZR` controller directly from ordinary and signed structural
GMO, quotient small-Davenport bounds, and the ordinary Davenport convolution
inequality.  Every strict descent preserves original occurrence labels and
the ambient exact target `2|A|`.

Finally, `GaoLean/GAOARFinal.lean` proves the frozen fully quantified
`PGGaoV1Statement` from `PGGaoStructuralRemainingInputs`.  This remaining
input contains only recognizable cited-source theorem interfaces.  It does
not contain a residual controller, a branch output, or the desired Gao upper
bound.

The project must therefore be reported as conditionally formalized until the
cited literature inputs themselves are imported from audited Lean libraries
or proved locally.  No `sorry`, `admit`, project axiom, or hidden statement
strengthening is permitted in that upgrade.
