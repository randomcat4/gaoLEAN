# Lemma ledger

| Obligation | Mathematical source | Lean status | Boundary |
|---|---|---|---|
| Exact GAO-AR statement | main theorem | frozen/compiled | internal syntax |
| Group order `2 q^r` | preliminaries | proved | internal |
| Standard lower bound | lower-bound section | proved | Olson exact-D provider |
| Rank 2 low-reflection branch | rank-two section, `a ≤ 1` | proved | ordinary GMO provider |
| `D_±(F_q²) ≤ q` | rank-two preliminaries | proved | internal subset sums + `q=3` linear dependence |
| Rank 2 high-reflection branch | rank-two section, `a ≥ 2q` | proved | weighted GMO provider |
| Rank 2 middle first GMO split | rank-two section, `2 ≤ a ≤ 2q-1` | proved | structural GMO provider |
| Rank 2 `K=0` middle leaf | rank-two section | proved | explicit small-Davenport provider |
| Rank 2 subgroup classification | rank-two section | proved | internal linear algebra |
| `D_±(K) ≤ |K|` | rank-two line branch | proved | internal ordinary zero-sum reduction |
| Rank 2 line, `s ≤ q` | rank-two section | proved | ordinary GMO provider on the line |
| Dihedral reflection block | preliminaries, Lemma `Dihedral blocks` (1) | proved | internal Cauchy--Davenport argument |
| `d(D₂q) ≤ q` | preliminaries, Lemma `Dihedral blocks` (2), upper half | proved | internal occurrence-labelled extraction |
| Dihedral block with complement `≤ q` | preliminaries, Lemma `Dihedral blocks` (3) | proved | internal maximum block + preceding bound |
| Dihedral lower witness `d(D₂q) ≥ q` | preliminaries, Lemma `Dihedral blocks` (2), lower half | open | explicit sequence witness |
| Rank 2 line, `s > q` | rank-two section | proved | structural GMO provider on the line + ambient small-Davenport provider |
| Rank 2 concentrated line completion | rank-two section | proved | internal dispatch to the two line leaves |
| Rank 2 complete upper bound | rank-two section | proved | named ordinary/weighted/structural GMO + ambient small-Davenport interfaces |
| Rank 3 upper bound | rank-three section | open | internal + named published inputs |
| Line completion | rank-three section | open | internal |
| Residual-state producer | residual-front-end | open | internal |
| Affine dichotomy | reduction | proved (M46) | internal |
| One-translation consumer | reduction | proved (M43) | internal |
| Weighted structural theorem | GMO Cor. 1.3 | exact specialized interface frozen | external |
| Final assembly | main theorem | open | depends on all rows above |

“Proved” here means a checked reusable Lean declaration, not a prose claim.
