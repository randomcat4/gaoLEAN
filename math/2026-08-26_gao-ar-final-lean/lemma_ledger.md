# Lemma ledger

| Obligation | Mathematical source | Lean status | Boundary |
|---|---|---|---|
| Exact GAO-AR statement | main theorem | frozen/compiled | internal syntax |
| Group order `2 q^r` | preliminaries | proved | internal |
| Standard lower bound | lower-bound section | proved | Olson exact-D provider |
| Rank 2 low-reflection branch | rank-two section, `a ≤ 1` | proved | ordinary GMO provider |
| `D_±(F_q²) ≤ q` | rank-two preliminaries | proved | internal subset sums + `q=3` linear dependence |
| Rank 2 high-reflection branch | rank-two section, `a ≥ 2q` | proved | weighted GMO provider |
| Rank 2 middle branch | rank-two section, `2 ≤ a ≤ 2q-1` | open | internal + weighted GMO provider |
| Rank 3 upper bound | rank-three section | open | internal + named published inputs |
| Line completion | rank-three section | open | internal |
| Residual-state producer | residual-front-end | open | internal |
| Affine dichotomy | reduction | proved (M46) | internal |
| One-translation consumer | reduction | proved (M43) | internal |
| Weighted structural theorem | GMO Cor. 1.3 | exact specialized interface frozen | external |
| Final assembly | main theorem | open | depends on all rows above |

“Proved” here means a checked reusable Lean declaration, not a prose claim.
