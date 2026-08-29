# GAO-PUB-L-LEAN formalization plan

## Scope and status discipline

The project is pinned to Lean 4.32.0 and Mathlib v4.32.0. A result is marked
checked only after an actual build, a forbidden-declaration scan, an axiom
audit, and a natural-language/Lean statement comparison. Mathematics absent
from Mathlib may be exposed as an explicit theorem parameter, but such an
endpoint is conditional and is never reported as a completed proof.

The current manuscript-wide verdict for the frozen 13-page `gao0824` PR #7
source is **`PARTIALLY_VERIFIED`**. Two facts must remain separate:

1. `GaoLean.ConcreteGDihedral.pr7ThirteenPageMain` proves the main Gao
   statement unconditionally. It has the frozen p-group quantifiers and no
   remaining-input, provider, or recursive-output argument. The ordinary
   `W={1}` and signed `W={±1}` GMO specializations actually used by that proof
   are internally available.
2. Manuscript Theorem 2.2 is stated for an arbitrary nonempty `W : Set ℤ`,
   with its structural part under `gcd(W)=1`. The repository does not yet
   contain one source-literal theorem covering that entire weight range.
   Therefore the whole manuscript is not yet paragraph-by-paragraph
   `FULLY_CHECKED`.

The independent cold audit returned `PARTIALLY_VERIFIED` on this coverage
boundary. Its fresh SSH clone completed `lake build` in 8827 jobs with exit 0.
The earlier merged-worktree receipts of 8820 jobs for the default build and
central `GaoFormal.AxiomAudit` remain valid historical receipts, not the sole
current build count.

## Current dependency picture

```text
frozen 13-page main Gao statement
    ├── occurrence-labelled generalized-dihedral semantics       [CHECKED]
    ├── Olson ordinary Davenport formula                         [CHECKED]
    ├── Proposition 3.1 plus-minus Davenport bound               [CHECKED]
    ├── GJM small-Davenport identity                              [CHECKED]
    ├── GMO specialization W={1}
    │      ├── prescribed-length provider                         [CHECKED]
    │      └── structural provider for ambient/subgroups          [CHECKED]
    ├── GMO specialization W={±1}
    │      ├── prescribed-length provider                         [CHECKED]
    │      └── structural provider for ambient/subgroups          [CHECKED]
    ├── quotient extraction, channel consumers, strict descent    [CHECKED]
    ├── exact upper and lower bounds                              [CHECKED]
    └── pr7ThirteenPageMain                                       [CHECKED]

manuscript Theorem 2.2 in its full source range
    ├── arbitrary nonempty W : Set ℤ statement/interface          [CHECKED]
    ├── spectrum, DGM, Davenport, quotient and induction bridges   [CHECKED]
    ├── aperiodic many-nonsingleton/full-spectrum branch            [CHECKED]
    ├── gcd--torsion kernel/range and singleton-layer arithmetic    [CHECKED]
    ├── arbitrary-W to primitive-W existence normalization           [CHECKED]
    ├── occurrence-subsequence weighted-sum transport                 [CHECKED]
    ├── full labelled GMO Lemma 3.5 certificate                       [CHECKED]
    ├── singleton-occurrence kernel subsequence                        [CHECKED]
    ├── exact Step-6 subgroup/quotient length budgets                  [CHECKED]
    ├── singleton-kernel witness lift and selection convolution        [CHECKED]
    ├── Step-6 kernel/range occurrence-count dichotomy                 [CHECKED]
    ├── weighted-occurrence specialization of Lemma 3.5                [CHECKED]
    ├── prescribed-length singleton-layer recursive branch          [OPEN]
    ├── structural aperiodic/Lemma-3.5 branch under gcd(W)=1       [OPEN]
    └── literal source-statement and paragraph audit               [OPEN]
```

## Verified release endpoints

| Area | Representative Lean endpoint | State |
|---|---|---|
| Frozen main theorem | `ConcreteGDihedral.pr7ThirteenPageMain` | `CHECKED`, unconditional |
| Ordinary GMO used by the paper | `ordinaryGMOPrescribedLengthProvider_of_canonicalDStar` | `CHECKED`, `W={1}` specialization |
| Ordinary structural GMO | `ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup` | `CHECKED`, `W={1}` specialization |
| Signed GMO used by the paper | `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction` | `CHECKED`, `W={±1}` specialization |
| Olson formula | `PGOlson.isOrdinaryDavenportConstant_invariantProduct` | `CHECKED` |
| Proposition 3.1 | `PGOlson.plusMinusDavenportAtMost_half_of_isPGroup` | `CHECKED` |
| GJM bound | `PGGJM.smallDavenportProductOneFreeAtMost_of_ordinaryDavenport` | `CHECKED` |
| Corollary 6.1 | `PGManuscriptConsequences.pgGao_homocyclic_display`; `pgGao_elementaryAbelian_display` | `CHECKED`, unconditional |
| `C₃²` example | `PGManuscriptConsequences.pgGao_c3Squared_threshold` and witness lemmas | `CHECKED` |
| General Theorem 2.2 | no single source-literal full-range endpoint yet | `OPEN` |

The historical theorem
`pr7ThirteenPageMain_of_remainingInputs` remains as a layered API and audit
artifact. It is not a dependency of the unconditional main endpoint and must
not be mistaken for the current final boundary.

## Remaining plan: general-weight GMO

### G1 — Freeze the literal source theorem `[COMPLETED]`

- Introduce the exact weight-set carrier for arbitrary nonempty
  `W : Set ℤ` without silently replacing it by a finite list or by
  `{1}`/`{±1}`.
- Record every source hypothesis, including `gcd(W)=1` exactly where the
  structural clause uses it.
- State occurrence-labelled prescribed-length and structural conclusions
  with no conclusion-shaped provider premise.

Exit criterion: a source/Lean statement comparison shows identical
quantifier order, thresholds, target cosets, exception counts, and subgroup
properness.

### G2 — Prove arbitrary-weight prescribed length `[IN PROGRESS]`

- Generalize the existing DGM setpartition transport from the two used
  weight families to arbitrary nonempty integer weights.
- Preserve occurrence labels and exact cardinality through the weighted
  layer construction.
- Handle normalization and natural-number subtraction without assuming
  finiteness or symmetry of `W` unless present in the source.

Completed infrastructure: exact weighted Davenport constants, homomorphic
push/pull, subgroup--quotient convolution, stabilizer-quotient target lifting,
the cardinal strong-induction driver, and the DGM capped-incidence
full-spectrum branch.  The singleton-kernel subsequence, recursive-witness
lift, kernel/range count dichotomy, and occurrence-faithful selection
convolution are also complete.  Remaining boundary: assemble these checked
components into the primitive-weight unconditional existence provider.  The
nonprimitive normalization endpoint used by Corollary 1.2 is complete,
including the zero-generator branch.

Exit criterion: the G1 existence endpoint has an unconditional inhabitant
and specializes definitionally or by proved transport to the current
`W={1}` and `W={±1}` providers.

### G3 — Prove the `gcd(W)=1` structural alternative `[IN PROGRESS]`

- Formalize the common-coset conclusion for both source occurrences and
  their allowed weights.
- Retain the full-spectrum branch, exception bound, and strict proper-subgroup
  descent used by the source theorem.
- Prove subgroup/quotient inheritance for the general weight carrier rather
  than importing the specialized providers as assumptions.

Completed infrastructure: common weighted cosets imply a common source coset,
the exact quotient concentration lift, and the nontrivial-stabilizer recursive
branch.  The canonical gcd--torsion modulus, `G[d]`, `dG`, singleton-locus
equivalence, quotient singleton layers, and `G/G[d] ≃ dG` are also checked.
The complete labelled Lemma 3.5 certificate is now checked, including the
greedy full branch and strict-stabilizer recursive branch, and is specialized
to literal weighted occurrence cells without deduplicating repeated values.
Step 1's strong affine package and final assembly of the checked aperiodic
kernel/range branches are the core left.

Exit criterion: the G1 structural endpoint is unconditional and all
specialized structural providers are derived from it.

### G4 — Manuscript closure audit

- Update `pr7-13-page-map.md` so every Theorem 2.2 row points to the G1--G3
  endpoint and proof, not merely to its two specializations.
- Run a fresh default build and `GaoFormal.AxiomAudit` in a clean clone.
- Repeat forbidden-declaration scanning and two-way source/Lean review.
- Upgrade the manuscript-wide verdict only if no `PARTIAL`, `CONDITIONAL`, or
  unmapped source clause remains.

## Verification gates

Every release candidate must satisfy all of the following:

1. `lake build` succeeds from a clean checkout;
2. `lake build GaoFormal.AxiomAudit` succeeds;
3. the forbidden scan finds no `sorry`, `admit`, project `axiom`, `unsafe`,
   `native_decide`, or `sorryAx` escape;
4. all public endpoints print only accepted Lean/Mathlib axioms;
5. the source-to-Lean and Lean-to-source audits agree on scope;
6. README, paragraph map, verdict, and source comments state the same boundary.

Build success alone never promotes `PARTIALLY_VERIFIED` to
`FULLY_CHECKED`: the final gate is literal source coverage.

## Historical milestone index

The detailed milestone narratives remain immutable audit snapshots in
`milestone-01.md` through `milestone-70.md`. They are intentionally not copied
here as a running diary:

- M1--M10: independent-difference matching and affine exchange;
- M11--M46: product-one semantics, branch consumers, extraction, descent,
  and negative certificates;
- M47--M55: Olson, Proposition 3.1, GJM, Gao assembly, and manuscript
  numerical consequences;
- M56--M70: DGM/GMO source decomposition, signed closure, and ordinary
  structural proof infrastructure;
- post-M70 release: canonical ordinary providers, unconditional main endpoint,
  and manuscript consequences.

Statements such as “still missing” in an older milestone describe that
revision. Conversely, an older specialized “complete” label does not prove
the currently open arbitrary-weight Theorem 2.2. The current status is
defined only by this plan, `pr7-13-page-map.md`, and the latest audit verdict.
