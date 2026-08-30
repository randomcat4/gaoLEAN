# Cross-repository Gao Lean ledger

Snapshot date: 2026-08-28 (America/New_York).

This ledger deduplicates the substantive mathematical outputs in the GitHub
repositories `randomcat4/gao0822`, `randomcat4/gao0823`, `randomcat4/gao0824`,
and `randomcat4/zhuang-gao-cyclic-index-two`.  Historical route failures and
finite no-hit searches are retained in their source ledgers, but are not
promoted here to theorem-level rows.  `LEAN_FULL` means the frozen statement,
not merely an arithmetic shadow, has been kernel checked.  An open conjecture
is listed for scope control and is never counted as a Lean failure.

## Snapshot receipts

| Repository | Audited revision | Role |
|---|---|---|
| `gao0822` | `907513145a18eb3c496daea44cd21cd7791cee3f` | read-only historical archive |
| `gao0823` | `18cdc6ee95b90f380b8a848fc285e30a2cbf6fde` plus the scoped formalization worktree | maintained theorem and Lean source |
| `gao0824` | `711eefa35364ab9165cf354839904ae0321c0025` on the six-reflection branch | read-only method/source input |
| `zhuang-gao-cyclic-index-two` | `33de3f6d2f0cd15a947713aa6db20d3d1279ee80` | read-only C8/local-lemma source |
| `gaoLEAN` integration | `a1b055a0beea3db90556b57e9a06dfc9440064a1` | unconditional 13-page endpoint, manuscript consequences, and kernel-checked proof graph |

Merged-release receipt: default build and central `GaoFormal.AxiomAudit` both
completed 8820 jobs with exit 0.  Two fresh independent audits of `61906ee`
each found 0 blocking / 0 major issues; incremental review of `a1b055a` found
0 blocking / 0 major / 0 minor, and the main-agent review passed.  The single
`pr7ThirteenPageMain` endpoint carries the frozen core threshold; Olson, GJM,
the unconditional Corollary 6.1 displays, and the `C₃²` endpoints jointly
cover the remaining displayed consequences.

## Canonical theorem ledger

| Canonical result | Mathematical source status | Deduplication | Lean status | Next exact obligation |
|---|---|---|---|---|
| Odd-characteristic affine independent-difference matching formula | `VERIFIED` in `gao0823` | absorbs the matching ingredient in the arbitrary-rank route | `LEAN_FULL` (M8) | none |
| Occurrence-labelled heavy-support pair reservoir and fixed-cardinality exchange | `VERIFIED` in `gao0823` | Corollary 2.1 reservoir plus its exact-`d` sumset consequence | `LEAN_FULL` (M9, M40–M42) | none for the full-exchange consumer |
| Sharp characteristic-two boundary on `F₂²` | `VERIFIED` counterexample in `gao0823` | unique canonical boundary witness | `LEAN_FULL` (M35) | none |
| Affine exchange / labelled-hyperplane alternative | `VERIFIED` in `gao0823` | reusable front end for one-translation | `LEAN_FULL` (M39–M46, including the `e≥q-1` occurrence construction and raw-support split) | none for this theorem-level dichotomy |
| One-translation arbitrary-rank integration | `VERIFIED` after audit in `gao0823` | supersedes the incomplete standalone `range-proof03` route | `LEAN_FULL` as a reusable consumer (M43/M46) | none for the consumer; final theorem uses the direct structural controller |
| `GAO-AR-v1`: `E((C_q^r)⋊C₂)=2q^r+r(q-1)+1` | `VERIFIED` for odd prime `q`, `r≥2` | absorbed by the broader p-group statement; direct rank 2/3 proofs also compiled | `LEAN_CONDITIONAL` | formalize/import the explicit cited-source package |
| `HP-GAO-v1` homocyclic prime-power theorem | `VERIFIED` in `gao0823` | separate specialization, not implied by the prime-field M10 code | `NOT_FORMALIZED` | freeze exact source DAG and external zero-sum inputs |
| `PG-GAO-v1`: `E(A⋊_{-1}C₂)=2\|A\|+D(A)` for odd abelian p-groups | `VERIFIED` in `gao0823`; 13-page statement frozen from `gao0824` PR #7 | one canonical theorem across both repositories | `LEAN_FULL`; endpoint `GaoLean.ConcreteGDihedral.pr7ThirteenPageMain` | none |
| Fixed-target subgroup descent | `PROVED` in `gao0824` | realized by the checked simultaneous `RC`/`ZR` controller and canonical ordinary extension | `LEAN_FULL` for the final odd-prime p-group route | none for the frozen theorem |
| Capacity-flag surplus and stability theorem | `PROVED` in `gao0824` | independent reusable structure theorem | `LEAN_PARTIAL` arithmetic only | migrate full flag recurrence, equality, and near-equality classification |
| Low-reflection affine front end | `PROVED` in `gao0824`; final existence is standard GMO | overlaps PG low branch | `LEAN_PARTIAL` | formalize the precise affine/anchored output alternative |
| Exact `a=2,3,4,5,6` reflection origin-entry front ends | corrected versions `PROVED` in `gao0824` | `a=2,3` overlap the earlier front end; `a=4,5,6` are new sharpenings | `LEAN_PARTIAL` arithmetic/word fragments | formalize gap classifications, exceptional groups, labelled outputs, and GMO application |
| Charged-correction lifting iff | `PROVED` structural theorem in `gao0824` | used by the C8 periodic branch | `NOT_FORMALIZED` | encode sign-coherent labelled factors and correction spectrum |
| Pointed Liu / `C₃×C₁₅` / `D₃₃` / OA-F8 constructions | `VERIFIED` in `gao0823` Paper 2 | canonical construction family | `NOT_FORMALIZED` | freeze each construction and verify array/group conditions |
| OA-F9 reduction and covering-radius criterion | `VERIFIED` in `gao0823` | criterion is proved; the fixed-code radius claim lacks a proof trace | `NOT_FORMALIZED` | formalize equivalence/criterion; treat KCRIT as computation until certified |
| C8 local chain L06–L58 | `PROVED_HERE` / independently audited in the C8 repository | local lemmas only; does not prove the C8 mother theorem | `NOT_FORMALIZED` | split into stable structural and finite-certificate modules |
| C8 post-L58 Kneser dichotomy | independently checked but deliberately unnumbered | not yet part of the verified L-ledger | `NOT_QUEUED` | close the aperiodic-small-spectrum / periodic-quotient survivors first |

## Canonical falsification ledger

| False statement / route | Counterexample status | Lean status | Obligation |
|---|---|---|---|
| Characteristic-free independent-difference formula | disproved by `F₂²` | `LEAN_FULL` (M35) | none |
| Unconditional raw/padded sequence-level capacity entry | infinite cyclic family `X_{n,t}` in `gao0824` | `LEAN_FULLY_DISPROVED` (M36) | none for the frozen false assertions; replacement front end remains separate |
| Five-reflection raw gap `D±≤D-2` for every odd group | disproved exactly by `C₃`; repaired statement proved | raw claim `LEAN_FULLY_DISPROVED` (M37) | formalize the repaired classification separately |
| Six-reflection raw gap-3 | disproved at `C₃`; repaired statement proved | raw gap `LEAN_FULLY_DISPROVED` (M37) | formalize the repaired exceptional-group classification separately |
| Six-reflection raw two-exit theorem | explicit `C₃` sequence; repaired statement proved | raw claim `LEAN_FULLY_DISPROVED` (M38), including `TargetFound` | formalize the repaired theorem separately |
| Quotient-only charged lifting | explicit `C₆₃⋊C₈` T3 skeleton | `NOT_FORMALIZED` | encode and check the literal labelled certificate |
| `SUB(2,p,k)` and several extraspecial packing/extraction interfaces | explicit families in `gao0822` | `NOT_FORMALIZED` | prioritize theorem-level infinite families, not finite no-hit evidence |
| Strong intermediate C8/Gao routes L20, L27, L29, L31 and related diagnostics | explicit local countermodels in the C8 ledger | `NOT_FORMALIZED` | formalize only where the false interface remains load-bearing or reusable |

## Open statements, not Lean verdicts

- `E(C_m⋊_{-1}C₈)=12m` for odd `m≥3` is unresolved; L06–L58 do not imply it.
- The general mixed-prime OA-GAO formula and the stronger OA-F9 claim remain
  open/proposed.
- `MPV(2,p,k)` and `d(G^+_{2,p})=5(p-1)` remain unresolved in the historical
  extraspecial project.
- Priority and global novelty are separate from Lean truth checking.

## Frozen execution order

1. Close self-contained negative certificates and M10 internal mathematics.
2. Close the reusable `gao0824` structure theorems and repaired reflection
   front ends, preserving every exceptional group.
3. Formalize the ordinary/weighted zero-sum theorems needed by PG-GAO without
   replacing them by final-output assumptions. **Completed** by the canonical
   ordinary target/extension and signed General-DGM provider routes.
4. Formalize the Paper 2 constructions and the stable C8 L-lemma modules.
5. Issue theorem-level `LEAN_FULL`, `LEAN_DISPROVED`, or exact
   `OPEN/CONDITIONAL` verdicts per row.  The 13-page PG-GAO row is now
   `LEAN_FULL`; unrelated Paper 2, C8, and mixed-prime rows retain their prior
   status.
