# Independent adversarial audit of the PR7 13-page formalization

## Verdict

`PARTIALLY_VERIFIED`

The main mathematical conclusion of the frozen 13-page manuscript is fully
formalized and kernel-checked at the audited commit.  In particular, the final
endpoint proves, without provider or interface assumptions, the exact Gao
threshold for generalized dihedral groups over nontrivial finite abelian odd
prime-power kernels.

The stronger claim that every formally stated result in the manuscript is
represented with the same quantifier scope is not verified.  The manuscript's
Theorem 2.2 is stated for an arbitrary nonempty integer weight set `W` with
`gcd(W) = 1`.  The repository proves the ordinary (`W = {1}`) and signed
(`W = {+1, -1}`) specializations needed by the Gao proof, together with a more
general underlying DGM set-partition engine, but the audit did not find a final
Lean theorem exposing the manuscript's arbitrary-`W` statement verbatim.

Accordingly:

- **A. The Gao/GMO conclusion of the 13-page manuscript:** verified in full.
- **B. The whole GMO field or every generalized GMO statement:** not verified
  and must not be claimed.  Mixed-prime kernels, 2-groups, and arbitrary
  weighted GMO conclusions are outside the checked endpoint.

This report was produced from a new clone and does not inherit any earlier
completion assessment.

## Frozen inputs

### Manuscript

- Repository: `https://github.com/randomcat4/gao0824.git`
- Frozen checkout: `/workspace/gao0824-pr7`
- Audited HEAD: `6d4ab81b14f49aaa61d7aeb8c02182f1259a736b`
- Checkout state: detached and clean
- Delivery: `deliveries/gao-arxiv-rewrite-2026-08-24.zip`
- Delivered PDF pages: 13
- Delivered PDF SHA-256:
  `51ca4d4ca3fd56390451ecbcca78fdc85859ef1d4444457ef48f2e381de5a60f`
- The delivery's `MANIFEST.sha256` passed for every delivered file.

The tracked `main.tex` and all six section files are byte-identical to the
delivery.  The tracked `references.bib` differs only by a trailing blank line,
so the older manifest in the tracked tree fails for that file even though the
delivery manifest passes.

The host did not provide `pdflatex`, so the audit could not independently
recompile the PDF.  The 13-page finding is based on `pdfinfo`, the PDF digest,
and the verified delivery manifest.

### Lean repository

- Repository: `https://github.com/randomcat4/gaoLEAN`
- Audited branch: `work/gao0824-pr7-unconditional-complete-m114`
- Audited commit: `7b98d32a11e3417372d05697b83323a09ffa4906`
- Fresh checkout: `/workspace/gaoLEAN-independent-audit-LYJ5Xc`
- The local and remote branch heads matched exactly.
- `.lake` was absent before the audit build.
- The checkout was clean before and after all checks.
- `/workspace/gaoLEAN-integration` and its caches or untracked files were not
  inspected or reused.

## Toolchain and build

The repository's `lean-toolchain` contains:

```text
leanprover/lean4:v4.32.0
```

Observed versions:

```text
Lean (version 4.32.0, x86_64-unknown-linux-gnu,
      commit 8c9756b28d64dab099da31a4c09229a9e6a2ef35, Release)
Lake version 5.0.0-src+8c9756b (Lean version 4.32.0)
```

The manifest pins Mathlib at `81a5d257...` (the v4.32.0 line).

The cold `lake build` completed successfully:

```text
Build completed successfully (8827 jobs).
real 45m43.461s
```

The separate central audit target also completed successfully:

```text
lake build GaoFormal.AxiomAudit
Build completed successfully (8820 jobs).
```

## Manuscript-to-Lean coverage

| Manuscript obligation | Principal Lean evidence | Assessment |
| --- | --- | --- |
| Exact Gao threshold `E(Dih(A)) = 2|A| + D(A)` | `PGGaoV1Statement`, `ConcreteGDihedral.pr7ThirteenPageMain` | Unconditional and quantifier-faithful |
| Occurrence-sensitive exact-length selection | `HasProductOneSubsequenceOfCard`, `IsExactProductOneThreshold` | Repeated sequence entries are not collapsed into a set |
| Lower bound | `gaoAR_lowerThreshold_of_ordinaryDavenport` and the Davenport witness | Covered |
| Ordinary GMO input | `ordinaryGMOPrescribedLengthProvider_of_canonicalDStar` | Constructed by proof, not assumed as an interface |
| Structural/concentration alternative | `ordinaryGMOStructuralProvider_addSubgroup_of_oddPrimePGroup` | Unconditional for every relevant subgroup |
| Signed GMO input | `oddPlusMinusGMOProviders_for_finalAssembly_of_doubleInduction` | Derived without an external provider |
| Low, middle, and high reflection regimes | `GAOARRankTwo*`, `GAOARRankThree*`, `GAOARResidualController` | All enter the final assembly |
| Olson invariant-factor formula | `exists_olsonInvariantProduct`, `isOrdinaryDavenportConstant_invariantProduct` | Covered |
| GJM/small Davenport bound | `smallDavenportProductOneFreeAtMost_of_ordinaryDavenport` | Occurrence-faithful |
| Corollary 6.1, homocyclic case | `pgGao_homocyclic_display` | Unconditional |
| Corollary 6.1, elementary-abelian case | `pgGao_elementaryAbelian_display` | Unconditional |
| Explicit `C_3^2` Davenport witness | `c3SquaredDavenportWitness`, `c3SquaredProductOneFreeWord_isProductOneFree` | Covered by an explicit word |
| Length-22 lower word with no length-18 block | `c3SquaredPaddedLowerWord_no_eighteenBlock` | Covered |
| Exact `23/18` threshold | `pgGao_c3Squared_threshold` | Covered |
| Theorem 2.2 for arbitrary integer weights `W` | General DGM engine plus ordinary and signed specializations | No final theorem with the manuscript's full arbitrary-`W` quantifiers was located |

## Quantifier and assumption audit

The final statement quantifies over every type `A` carrying:

- `AddCommGroup A`,
- `Fintype A`,
- `Nontrivial A`,
- an odd prime `p`, and
- `IsPGroup p A`.

It then proves the exact threshold at `2 * Nat.card A + D`, with target length
`2 * Nat.card A`, whenever `D` is the exact ordinary Davenport constant.  The
separate Olson development supplies that Davenport value for the p-group.

No evidence was found of:

- secretly reducing the group quantifier of the final theorem;
- adding a final hypothesis absent from the manuscript;
- replacing an existential result by an assumed provider at the final endpoint;
- proving only an at-least-length result where the manuscript needs exact
  length; or
- ignoring occurrence labels when a sequence contains repeated values.

Historical conditional endpoints remain in the tree, including
`pr7ThirteenPageMain_of_remainingInputs`.  They do not weaken the actual final
endpoint: `pr7ThirteenPageMain` takes no remaining-input package and constructs
the ordinary and structural providers internally.

## Axiom and placeholder audit

The project-wide source scan found no active occurrence of:

- `sorry`
- `admit`
- a project-defined `axiom`
- `unsafe`
- `native_decide`
- `sorryAx`

The only lexical hits were explanatory comments saying that a construction is
not an axiom.

`GaoFormal/AxiomAudit.lean` contains 332 `#print axioms` checks.  Its final
section includes the ordinary prescribed-length provider, the structural
provider, the remaining-input constructor, the unconditional manuscript
endpoint, Corollary 6.1, and all `C_3^2` endpoints.

The load-bearing final declarations depend only on the standard Lean/Mathlib
axioms:

```text
propext
Classical.choice
Quot.sound
```

No `sorryAx` or additional project axiom was reported.

## Source size

- Lean source files: 169
- Principal proof modules after excluding aggregators and the audit file: 166
- Total Lean lines: 65,190
- Proof-source lines excluding aggregators and `AxiomAudit.lean`: 64,761
- Approximate nonblank, noncomment proof lines: 53,877

Approximate effective-line distribution:

| Module family | Effective lines |
| --- | ---: |
| DGM/GMO engine (`PGDGM*`, `PGGMO*`) | 35,710 |
| Other manuscript assembly modules | 9,383 |
| GAOAR reflection-regime modules | 5,207 |
| `GaoFormal` matching modules | 2,456 |
| Foundational `GaoLean` modules | 1,121 |

The effective-line count removes blank lines, line comments, and block comments;
it is an audit metric rather than a language-aware proof-term count.

## Findings by severity

### Blocking

None for the manuscript's final Gao theorem.

### Major

1. The arbitrary-weight form of manuscript Theorem 2.2 is not exposed as a
   final Lean theorem with the same quantifiers.  The two specializations needed
   downstream are proved, so this does not block the final Gao theorem, but it
   blocks a claim of literal proposition-by-proposition coverage of the entire
   manuscript.

### Minor

1. The latter part of `README.md` is dominated by a long historical milestone
   log containing obsolete `PARTIAL`, `CONDITIONAL`, and `NOT_FORMALIZED`
   statuses.  Although it labels these as history, it is harder to use as a
   reader-facing project introduction.
2. The README reports 8,820 build tasks, while this cold default build contained
   8,827 jobs.
3. The module documentation in `PR7ThirteenPage.lean` still emphasizes the
   historical conditional endpoint.  The unconditional endpoint lives in
   `PGGaoOrdinaryComplete.lean`.
4. The tracked manuscript `references.bib` has a trailing-newline discrepancy
   relative to the verified delivery archive.

## Reproduction commands

```bash
ssh root@36.150.116.220 -p 32128

git -C /workspace/gao0824-pr7 rev-parse HEAD
git -C /workspace/gao0824-pr7 status --short

cd /workspace
git clone --branch work/gao0824-pr7-unconditional-complete-m114 \
  --single-branch https://github.com/randomcat4/gaoLEAN \
  gaoLEAN-independent-audit-LYJ5Xc

cd /workspace/gaoLEAN-independent-audit-LYJ5Xc
git rev-parse HEAD
git ls-remote origin \
  refs/heads/work/gao0824-pr7-unconditional-complete-m114
git status --short --branch
test ! -e .lake

export ELAN_HOME=/workspace/.elan
export PATH=/workspace/.elan/bin:$PATH
lean --version
lake --version

time lake build
lake build GaoFormal.AxiomAudit

rg -n -i '\b(sorryAx|sorry|admit|axiom|unsafe|native_decide)\b' \
  --glob '*.lean' .

lake env lean GaoLean/PGGaoOrdinaryComplete.lean
lake env lean GaoLean/PGManuscriptConsequences.lean
git status --short --branch
```

## Evidence boundary

This verdict is limited to the two frozen commits above, acceptance of the
generated proof objects by the specified Lean kernel, and a manual semantic
comparison between the manuscript and the principal Lean statements.  It is
not an independent re-proof of every Mathlib dependency, and it must not be
extrapolated to all GMO variants or to the whole research area.
