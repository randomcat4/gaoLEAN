# Route registry

| Route | Role | Current state | Completion evidence |
|---|---|---|---|
| S | Frozen statement and semantics | verified | server build of `GAOARStatements` |
| L | Standard exact-threshold lower bound | verified | server build of `GAOARLowerBound` |
| R2 | Direct rank-two upper bound | verified | complete upper bound assembled and whole-repository checked |
| R3 | Rank-three and line completion | active | outer ranges and first stabilizer descent verified; concentrated-subspace descent and line completion pending |
| RF | Rank-free residual-state producer | pending | pending |
| A | Affine dichotomy consumer | verified component | M46, not top-level proof |
| T | One-translation consumer | verified component | M43, not top-level proof |
| X | External theorem interfaces | active | GMO structural specialization frozen; remaining inputs pending |
| Z | Three-way final assembly | pending | pending |

Routes are not interchangeable.  In particular, A and T cannot be reported
as the GAO-AR theorem without RF, the low-rank routes, L, X, and Z.
