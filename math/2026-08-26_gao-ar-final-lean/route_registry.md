# Route registry

| Route | Role | Current state | Completion evidence |
|---|---|---|---|
| S | Frozen statement and semantics | verified | server build of `GAOARStatements` |
| L | Standard exact-threshold lower bound | verified | server build of `GAOARLowerBound` |
| R2 | Direct rank-two upper bound | active | outer branches, internal `D_±(F_q²) ≤ q`, and first middle GMO split verified; concentrated line completion pending |
| R3 | Rank-three and line completion | pending | pending |
| RF | Rank-free residual-state producer | pending | pending |
| A | Affine dichotomy consumer | verified component | M46, not top-level proof |
| T | One-translation consumer | verified component | M43, not top-level proof |
| X | External theorem interfaces | active | GMO structural specialization frozen; remaining inputs pending |
| Z | Three-way final assembly | pending | pending |

Routes are not interchangeable.  In particular, A and T cannot be reported
as the GAO-AR theorem without RF, the low-rank routes, L, X, and Z.
