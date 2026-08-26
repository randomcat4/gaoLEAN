# Route registry

| Route | Role | Current state | Completion evidence |
|---|---|---|---|
| S | Frozen statement and semantics | verified | server build of `GAOARStatements` |
| L | Standard exact-threshold lower bound | verified | server build of `GAOARLowerBound` |
| R2 | Direct rank-two upper bound | verified | complete upper bound assembled and whole-repository checked |
| R3 | Rank-three and line completion | verified | complete upper bound, including plane-to-line second descent |
| RF | Rank-free residual-state producer | verified | structural ordinary/signed GMO translated into simultaneous `RC`/`ZR` induction |
| A | Affine dichotomy consumer | verified component | M46, not top-level proof |
| T | One-translation consumer | verified component | M43, not top-level proof |
| X | External theorem interfaces | frozen | final boundary lists only cited small-Davenport, restricted-coefficient, prescribed-length GMO, structural GMO, and Davenport-convolution inputs |
| Z | Three-way final assembly | verified conditionally | frozen `PGGaoV1Statement` follows from `PGGaoStructuralRemainingInputs` |

The internal Lean graph is complete.  Because the declarations in route X are
explicit proposition parameters rather than separately formalized proofs of
the cited literature, the final status is `LEAN_CONDITIONAL`, not an
unconditional `LEAN_FULLY_CHECKED` claim.
