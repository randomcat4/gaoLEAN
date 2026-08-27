# Mechanical build and audit log

Date: 2026-08-24, America/New_York.

## Commands and final exits

Working directory: repository root.

```powershell
elan --version                                  # exit 0
lean --version                                  # exit 0
lake --version                                  # exit 0
lake build                                      # exit 0; 8690 jobs
lake env lean GaoFormal\AxiomAudit.lean         # exit 0
rg -n -i "\bsorry\b|\badmit\b|^\s*axiom\b|^\s*unsafe\b" `
  GaoFormal GaoLean GaoFormal.lean GaoLean.lean -g '*.lean' # exit 1; no matches
git check-ignore -v <a file below .lake/build>  # exit 0; matched /.lake/
```

Actual versions:

- elan `4.2.3 (b6cec7e10 2026-06-08)`;
- Lean `4.32.0`, commit `8c9756b28d64dab099da31a4c09229a9e6a2ef35`;
- Lake `5.0.0-src+8c9756b`.

## Build history

- Initial project build: exit 1.  The endpoint-disjoint proof had two
  elaboration mismatches in the new-left/old-right cases.  They were repaired
  by supplying the exact tagged endpoint equalities.
- Endpoint-only milestone rebuild: exit 0 (`8658` jobs).
- Quotient-glue implementation first rebuild: exit 1 due to an omitted
  `difference` unfolding and an under-specified quotient submodule; after
  explicit annotations and a function extensionality bridge, exit 0.
- Maximum-cardinality layer first rebuild: exit 1 because the subtype
  `Fintype` instance was absent/then selected incompatibly.  A single canonical
  `Remaining` instance fixed the sum-cardinality computation.
- Final build after importing the full R2 add-one/unused-coset layer: exit 0,
  `Build completed successfully (8659 jobs)`.
- M6 coordinate bridge, quotient-pair independence, and matched-endpoint
  containment: single-file Lean check exit 0.
- M7 endpoint-complement counting and affine `vectorSpan`/`finrank` boundary:
  single-file Lean check exit 0.
- M8 finite maximum construction and exact formula existence theorem: final
  `lake build` exit 0, `Build completed successfully (8660 jobs)`.
- M9 threshold support and occurrence-labelled capacity lift: single-file
  Lean check exit 0; final `lake build` exit 0,
  `Build completed successfully (8661 jobs)`; audit exit 0.
- P1 front-end import plus new concrete PG quotient projection: final
  `lake build` exit 0, `Build completed successfully (8673 jobs)`; unified
  audit exit 0.
- P5a exact quotient guard and recursive transport: `PGQuotient.lean` and
  `PGGuard.lean` single-file checks exit 0; final `lake build` exit 0,
  `Build completed successfully (8674 jobs)`.  Unified axiom audit exit 0.
  The forbidden-declaration scan over both `GaoFormal` and `GaoLean` returned
  exit 1 with no matches, which is the expected no-match status from `rg`.
- P5b1 zero-layer and induction closure: `PGBase.lean`, `PGInduction.lean`,
  and `PGTranslation.lean` each passed an actual single-file check after their
  dependencies were built.  Final `lake build` exit 0,
  `Build completed successfully (8677 jobs)`.  The new coverage comprises the
  maximum product-one core/free-remainder construction, both conditional zero
  bases, finite strict-subgroup simultaneous scheduler, and exact all-rotation
  translation pullback.
- P5b2a translated-list recursive wiring: the first augmented single-file
  check exited 1 because `Equiv.toEmbedding` and nested `Multiset.map`
  coercions required explicit normalization.  After repair,
  `lake env lean GaoLean\PGTranslation.lean` exited 0.  Final `lake build`
  exited 0, `Build completed successfully (8677 jobs)`; unified audit exited
  0; forbidden-declaration scan returned exit 1 with no matches.
- P5b2b capacity composition: the first `PGCapacity.lean` check exited 1 on
  the additive Mathlib identifier `addSubgroupOf`; a later extension check
  exited 1 until `Nat.card top` was explicitly simplified.  After repair the
  single-file check exited 0.  Final `lake build` exited 0,
  `Build completed successfully (8678 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan again had no matches.
- P5b2c full-spectrum complement: the first `PGSpectrum.lean` check exited 1
  until the orientation of `Finset.disjoint_sdiff` and the additive
  rearrangement were made explicit.  After repair, the single-file check
  exited 0.  Final `lake build` exited 0,
  `Build completed successfully (8679 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches.
- P5b2d explicit GMO output consumer: `PGGMO.lean` passed its first
  single-file check. Final `lake build` exited 0,
  `Build completed successfully (8680 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches.
- P5b2e balanced reflection/rotation ordering: the first single-file check
  exposed only Lean 4.32 API names and list/multiset normalization shapes.
  After replacing them with explicit multiset normalization and the concrete
  group multiplication chain, `lake env lean
  GaoLean\PGReflectionOrdering.lean` exited 0. Final `lake build` exited 0,
  `Build completed successfully (8681 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches.
- P5b2f signed same-type pair post-processing: the first single-file check
  exited 1 only because the multiset/list cardinality lemma was named
  `Multiset.coe_card`; a second check exposed the missing explicit use of
  `pairCount_eq`. After those local repairs,
  `lake env lean GaoLean\PGReflectionPairs.lean` exited 0. Final `lake build`
  exited 0, `Build completed successfully (8682 jobs)`; unified audit exited
  0 and the forbidden-declaration scan had no matches.
- P5b2g occurrence reservoir and signed-selection bridge:
  `PGPairReservoir.lean` and `PGPairSelection.lean` each passed an actual
  single-file check. Final `lake build` exited 0,
  `Build completed successfully (8684 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches (`rg` exit 1).
- P5b2h high-reflection branch consumer: the first single-file check exposed
  one `Nodup` API shape; after explicit `List.nodup_cons` decomposition it
  exited 0. The subsequent source-faithful `Q • A` layer first exposed Lean's
  Prop-to-data elimination restriction; replacing it with explicit
  `Classical.choose` made the single-file check exit 0. Final `lake build`
  exited 0, `Build completed successfully (8685 jobs)`; unified audit exited
  0 and the forbidden-declaration scan had no matches (`rg` exit 1).
- P5b2i middle full-spectrum occurrence consumer: the first two single-file
  checks exposed only an `endpointList` unfolding and an addition-association
  rewrite; after explicit normalization the file exited 0. The balanced
  reflection occurrence-choice extension also exited 0 on its first check.
  Final `lake build` exited 0,
  `Build completed successfully (8686 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches (`rg` exit 1).
- P5b2j middle non-full front end: the first single-file check exited 1 because
  the quotient notation had the wrong Unicode code point; the second exposed
  the need for a local quotient `Fintype` instance.  After those local repairs,
  `lake env lean GaoLean\PGMiddleNonfull.lean` exited 0. Final `lake build`
  exited 0, `Build completed successfully (8687 jobs)`; unified audit exited
  0 and the forbidden-declaration scan had no matches (`rg` exit 1).
- P5b2k middle full/non-full assembly: the first two single-file checks exposed
  only the need to wrap structure-valued witnesses in `Nonempty` and eliminate
  them explicitly.  After repair, `lake env lean
  GaoLean\PGMiddleAssembly.lean` exited 0. Final `lake build` exited 0,
  `Build completed successfully (8688 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches (`rg` exit 1).
- P5b2l at-most-one-reflection branch: `lake env lean
  GaoLean\PGLowReflection.lean` exited 0 on its first check. Final `lake build`
  exited 0, `Build completed successfully (8689 jobs)`; unified audit exited
  0 and the forbidden-declaration scan had no matches (`rg` exit 1).
- P5b2m exhaustive reflection-regime dispatch: `lake env lean
  GaoLean\PGReflectionRegimes.lean` exited 0 on its first check. Final
  `lake build` exited 0, `Build completed successfully (8690 jobs)`; unified
  audit exited 0 and the forbidden-declaration scan had no matches
  (`rg` exit 1).
- P5b2n source-faithful rotation-only channel: `lake build
  GaoLean.PGRotationChannel` exited 0 (`8670` target jobs). The final full
  build below includes this module and its exact `C/Bprime` separation.
- P5b2o reflection-containing channel: the first single-file invocation found
  only that the new rotation dependency had not yet produced its `.olean`;
  after building that dependency, `lake build GaoLean.PGReflectionChannel`
  exited 0 (`8678` target jobs). Linter suggestions were non-fatal.
- P5b2p controller closure: the first single-file check exposed an ambiguous
  `Group` name after opening the concrete namespace; qualifying it as
  `ConcreteGDihedral.Group` repaired the statement. The next single-file
  check exited 0. Final `lake build` exited 0,
  `Build completed successfully (8693 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches (`rg` raw exit 1, normalized
  harness exit 0).
- P5b2q rotation quotient extraction: the first compile exposed only dependent
  rewriting, finset membership projections, and the need to record `d≤M` for
  natural subtraction. A later strengthening of (5.16) exposed that the
  source capacity and `a+|B0|≤D` facts had to be retained explicitly. After
  those statement-faithful repairs, `lake env lean
  GaoLean\PGRotationExtraction.lean` exited 0. The expanded controller theorem
  in `PGControllerClosure.lean` also exited 0. Final `lake build` exited 0,
  `Build completed successfully (8694 jobs)`; unified audit exited 0 and the
  forbidden-declaration scan had no matches (`rg` raw exit 1, normalized
  harness exit 0).
- P5b2r reflection quotient extraction: initial local checks exposed only
  concrete Lean API details (quotient-order lifting, `ZMod 2` parity, and
  truncated-natural subtraction). After explicit occurrence/multiset and
  cardinality proofs, `lake env lean GaoLean\PGReflectionExtraction.lean`
  exited 0. `lake build GaoLean.PGReflectionExtraction
  GaoLean.PGControllerClosure` exited 0 (`8681` target jobs). Final
  `lake build` exited 0, `Build completed successfully (8695 jobs)`; unified
  axiom audit exited 0 and every new declaration reports only `propext`,
  `Classical.choice`, and `Quot.sound`. The forbidden-declaration scan over
  Lean sources had no matches (`rg` raw exit 1, normalized exit 0),
  `git diff --check` exited 0, and `Scratch.lean` is absent.

Failed runs are diagnostic only and are not counted as verification.

## Axiom audit

`#print axioms` was run on the R2 augmentation/coset theorems, endpoint
constructor, surviving-span independence, quotient glue, both R1 determinant
theorems, crossed-index cardinality, the one-of-two matching theorem, the
maximum contradiction theorem, both quotient-coordinate bridge theorems,
the quotient-pair independence theorem, endpoint containment, unused-point
counting, affine-dimension equality, reindexing, finite maximum construction,
the final exact-formula existence theorem, threshold fiber selection, global
occurrence endpoint injectivity, and Corollary 2.1.

The unified audit now also covers quotient identity characterization,
factorization `G(A/H)→G(A/K)`, product-one identity deletion, the exact quotient
carrier, list/generic guard fidelity, reflection-preserving quotient descent,
kernel-translation invariance, and the combined occurrence-labelled recursive
guard transfer.

It further covers the maximum-core construction, zero-guard rotation-only
lemma, both small-Davenport-conditional zero bases, strict subgroup cardinal
descent, simultaneous induction scheduler, inverse rotation translation, and
same-selection exact-`2Q` pullback.  The latest audit also covers translated
list occurrence/multiset reindexing, actual-list quotient-guard descent,
rotation/reflection count invariance, affine-coset capacity inclusion, and the
complete conditional recursive `ZR` invocation/pullback.
The capacity audit adds quotient-card factorization, the two strict quotient
lower bounds, exact truncated-natural (5.10)-(5.11), and the combined
labelled-concentration/smaller-`ZR` closure.
The spectrum audit adds selected coordinate sums, exact occurrence-complement
subtraction, all-rotation zero-sum product ordering, and the exact `2Q`
full-spectrum complement theorem.
The GMO-interface audit adds the full/non-full occurrence-labelled disjunction
and its consumer; it does not assert the external disjunction.
The reflection-ordering audit adds the explicit balanced-sign word, its exact
multiset and product formulas, the zero-signed-sum closure, and both
occurrence-labelled exact-cardinality lifts.
The signed-pair audit adds positive/negative reflection orientation, weighted
pair-label to coordinate-sum conversion, exact occurrence carrier accounting,
and the prescribed-`q`-pairs to exact-`2q`-term product-one conclusion.
The reservoir/selection audit adds canonical consecutive pairing within the
rotation and reflection occurrence lists, exact cover up to a suffix of length
at most one, endpoint `Nodup`, the floor pair count, actual occurrence-to-
coordinate normalization, and the conversion of an explicit signed selection
to the previously checked balanced-pair consumer.
The high-reflection audit adds the exact (4.1) threshold inequality, the
`b≤2Q-1` rotation bound, selected-pair capacity, forced presence of a
reflection pair, the raw target conclusion “weighted sum lies in `Q • A`”,
the internal `Q=|A| ⇒ Q • A={0}` reduction, and the complete conditional
high-reflection consumer to an exact `2Q` product-one block.
The middle-reflection audit adds an actual choice of
`e=2⌊a/2⌋` distinct reflection occurrences, an equal nonempty plus/minus split,
individual occurrence-to-coordinate normalization, exact `ell+e=2Q`
cardinality, and the complete consumer from a labelled full-spectrum output to
the balanced literal ordering and exact product-one block.
The middle non-full audit adds quotient oddness inherited from the odd ambient
group, the occurrence-labelled implication from two weighted coset conditions
to membership in `K`, exact preservation of the lower bound
`b-|A/K|+2`, and the conditional call to the fixed-source controller.
The middle assembly audit adds the proposition-valued full/non-full output
split and its exact branchwise composition to the common `2Q` conclusion.
The low-reflection audit adds the source threshold, the raw `2Q • A` target,
its internal annihilation from `Q=|A|`, and the exact all-rotation occurrence
consumer.
The regime-dispatch audit adds the exhaustive numerical trichotomy and exact
composition of all three conditional occurrence-output consumers.
The rotation-channel audit adds the source-faithful `C/Bprime` split, full
occurrence union and coordinate cancellation, non-full strict smaller-`ZR`
descent, prepared-data consumer, and actual positive `ZR` step construction.
The reflection-channel audit adds the balanced full consumer, weighted-coset
non-full descent to smaller fixed-source `RC`, and the quotient-guard split
constructing the positive fixed-source `RC` step.
The controller-closure audit adds the middle zero-base arithmetic and the
assembly of both preparation families, GJM-conditional bases, and strict
simultaneous induction into `PGO3ControllerSkeleton`.
The rotation-extraction audit adds maximum labelled quotient-zero-sum
selection, free complement, quotient-to-kernel sum, the guarded proof that
reflections plus `B0` are quotient product-one-free, exact reservoir
partition/counting, (5.13)-(5.16) arithmetic, rotation preparation from narrow
providers, and controller assembly without an assumed rotation preparation
family.

Every audited declaration reports no axioms beyond:

```text
[propext, Classical.choice, Quot.sound]
```

Individual declarations may use a strict subset. There is no `sorryAx` and no
newly declared axiom.  The forbidden-declaration
scan has zero matches (`rg` exit 1).

## Statement fidelity and true status

The compiled certificate now closes the complete independent-difference
matching Theorem 1.1: occurrence-faithful matching semantics, crossed
replacement, quotient coordinates, `c,d` independence, maximality, two-unused
counting, affine-span dimension, finite maximum existence, and the exact
minimum formula.  That theorem is `LEAN_FULLY_CHECKED`.

The companion project remains `LEAN_PARTIALLY_CHECKED`: affine-exchange,
one-translation, GAO-AR-v1, PG-GAO-v1, and their external inputs are not fully
formalized. PG-O3's post-preparation positive steps, induction scheduler, and
zero bases are covered; the rotation quotient extraction is also covered.
Reflection-channel extraction, GMO providers, and GJM/Olson inputs remain
explicit. No Gao equality is claimed by this build.

P5b2r updates the last boundary: reflection-channel extraction is now covered,
including quotient-order lifting, positive-even parity, kernel defect, and
(5.6)--(5.9). Both channel preparations are derived from narrow providers.
The remaining PG-O3 inputs are the actual signed/ordinary GMO provider
theorems and GJM/Olson-facing quotient Davenport facts. PG-GAO-v1 remains
unproved, and no Gao equality is claimed by this build.

## M25--M26: synthesis and lower-bound build

Toolchain remained pinned to `leanprover/lean4:v4.32.0` (Lean 4.32.0, Lake
5.0.0-src+8c9756b, elan 4.2.3).

- Initial `PGSynthesis.lean` check: exit 1, exposing an explicit
  excluded-middle split and a `Nat.card`/`Fintype.card` presentation mismatch.
  Both were repaired without changing the theorem boundary.
- Rechecked `PGSynthesis.lean`: exit 0.
- M25 full `lake build`: exit 0, 8696 jobs.
- Early `PGLowerBound.lean` checks: exit 1 on decidable filtering, `Fin`
  embedding extensionality, and occurrence-nonempty normalization. These were
  repaired without weakening the statements.
- Final `lake env lean GaoLean\\PGLowerBound.lean`: exit 0.
- `lake build GaoLean.PGLowerBound GaoLean.PGSynthesis`: exit 0, 8681 target
  jobs.
- Final full `lake build`: exit 0, `Build completed successfully (8697 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0. New declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`, or a subset.
- Declaration-level scan for `sorry`, `admit`, `axiom`, and `unsafe`: no
  matches, normalized exit 0. An earlier broad text scan matched explanatory
  comments containing the word “axiom”; it was a documented false positive.
- `git diff --check`: exit 0. `Scratch.lean`: absent.

True status is still `LEAN_PARTIALLY_CHECKED`: the build proves the conditional
composition and its internal constructions, not the existence of the external
upper package or the small-Davenport witness.

## M27: source-level upper assembly

- First `lake env lean GaoLean\\PGSourceAssembly.lean`: exit 0; one unused
  presentation parameter was reported and removed.
- Recheck after cleanup: exit 0, with no warning in the new module.
- Full `lake build`: exit 0, `Build completed successfully (8698 jobs)`.
- First unified-audit launch: not executed because the permission review timed
  out. The single allowed retry executed and exited 0.
- Unified audit for both new theorems: only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Declaration-level forbidden scan: `FORBIDDEN_DECLARATION_SCAN_NO_MATCHES`,
  normalized exit 0.

M27 replaces a coarse upper-output assumption by exact low/high/middle source
outputs and narrow channel providers, then constructs the residual controller
internally. The provider existence theorems remain external.

## M28: ordinary Davenport lower-witness bridge

- Several development `lake env lean GaoLean\\PGDavenportBridge.lean` runs:
  exit 1 while repairing filter cardinality, reflection parity transport,
  mapped occurrence equivalence, and append-source type alignment.
- Final single-file check: exit 0, with no warning in the new module.
- `lake build GaoLean.PGDavenportBridge GaoLean.PGSourceAssembly`: exit 0,
  `Build completed successfully (8688 jobs)`.
- Full `lake build`: exit 0, `Build completed successfully (8699 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0; new declarations
  use only `propext`, `Classical.choice`, and `Quot.sound`.
- Declaration-level forbidden scan:
  `FORBIDDEN_DECLARATION_SCAN_NO_MATCHES`, normalized exit 0.

M28 proves the lower witness from `IsOrdinaryDavenportConstant A D`; the final
source-level conditional theorem no longer accepts an independent lower
witness. This does not affect the still-external upper providers.

## M29: odd-prime p-group cardinality

- `lake env lean GaoLean\\PGPGroupNumerics.lean`: exit 0.
- `lake build GaoLean.PGPGroupNumerics GaoLean.PGSourceAssembly`: exit 0,
  8689 target jobs.
- Full `lake build`: exit 0, `Build completed successfully (8700 jobs)`.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound` for the new declarations.
- Forbidden declaration scan: no matches, normalized exit 0.

The p-group hypotheses now supply odd cardinality internally.

## M30: exact frozen-statement residual boundary

- First `PGSourceAssembly.lean` check: exit 1 on a universe mismatch.
- Recheck with explicit matching universe parameters: exit 0.
- Full `lake build`: exit 0, `Build completed successfully (8700 jobs)`.
- Unified axiom audit: exit 0; only `propext`, `Classical.choice`, and
  `Quot.sound` for the new top-level theorem.
- Forbidden declaration scan: no matches, normalized exit 0.

`PGGaoRemainingInputs → PGGaoV1Statement` is checked; the premise is not.

## M31: finite Davenport cardinality bound

- `lake env lean GaoLean\\PGDavenportBound.lean`: exit 0. Development
  warnings about unused section variables/simp arguments were removed; the
  final source has no new warning.
- The first sandboxed `lake build GaoLean.PGDavenportBound` reached the new
  target but exited 1 because it could not write a `.lake` setup cache file.
  This was a filesystem permission boundary, not a Lean elaboration failure.
- Authorized rerun `lake build GaoLean.PGDavenportBound`: exit 0,
  `Build completed successfully (8660 jobs)`.
- `lake env lean GaoLean\\PGSourceAssembly.lean`: exit 0 after rewiring
  `D≤|A|` internally.
- Full `lake build`: exit 0, `Build completed successfully (8701 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0. All five new
  prefix-sum/Davenport declarations and both rewired top-level declarations
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Declaration-level forbidden scan over `*.lean`: no `sorry`, `admit`, new
  `axiom`, or `unsafe`; raw `rg` exit 1, normalized exit 0.
- Scoped `git diff --check -- projects/gao-ci2/arbitrary-rank/formalization/lean`:
  exit 0. A repository-wide check separately encountered pre-existing
  whitespace in another team's `B-R3` JSON; that file was not modified.

M31 proves `D≤|A|` from the frozen ordinary Davenport definition with an
occurrence-labelled prefix-sum argument. `PGGaoRemainingInputs` is now exactly
the external upper provider package. Overall status remains
`LEAN_PARTIALLY_CHECKED` because that package is not proved.

## M32: ordinary GMO low-reflection bridge

- Development `lake env lean GaoLean\\PGOrdinaryGMOBridge.lean` first exited
  1 while correcting the direction of a `Finset.sum_bij` transport and the
  source/coordinate occurrence types. No theorem was weakened.
- Final single-file check: exit 0, with no new linter warning after cleanup.
- `lake build GaoLean.PGOrdinaryGMOBridge`: exit 0,
  `Build completed successfully (8670 jobs)`.
- `lake env lean GaoLean\\PGSourceAssembly.lean`: exit 0 after replacing the
  arbitrary low-output field by `OrdinaryGMOPrescribedLengthProvider`.
- Full `lake build`: exit 0, `Build completed successfully (8702 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0. New bridge and
  rewired top-level declarations use only `propext`, `Classical.choice`, and
  `Quot.sound`.
- Forbidden declaration scan: no matches, raw exit 1 / normalized exit 0.
- Scoped `git diff --check`: exit 0.

M32 mechanically covers the occurrence-faithful specialization of ordinary
GMO to the low-reflection source. The provider theorem remains external, so
overall status remains `LEAN_PARTIALLY_CHECKED`.

## M33: weighted GMO high-reflection source bridge

- `lake env lean GaoLean\\PGWeightedGMOBridge.lean`: exit 0; the new theorem
  reports only `propext`, `Classical.choice`, and `Quot.sound`.
- `lake build GaoLean.PGWeightedGMOBridge`: exit 0,
  `Build completed successfully (8675 jobs)`.
- `lake env lean GaoLean\\PGSourceAssembly.lean`: exit 0 after replacing the
  arbitrary high-output field by `Odd D`, restricted-coefficient output, and
  `WeightedGMOPrescribedPairProvider`.
- Full `lake build`: exit 0,
  `Build completed successfully (8703 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0. The new bridge
  and rewired top-level declarations use only `propext`, `Classical.choice`,
  and `Quot.sound`.
- Forbidden declaration scan over `*.lean`: no `sorry`, `admit`, new `axiom`,
  or `unsafe`; raw `rg` exit 1 / normalized exit 0.
- Scoped `git diff --check`: exit 0.

M33 checks the threshold specialization and high-branch source routing. The
uniform provider is still a conditional interface whose output includes the
generic signed selection-to-four-pair-list partition. Weighted GMO and
PG-GAO-v1 are therefore not claimed as proved; overall status remains
`LEAN_PARTIALLY_CHECKED`.

## M34: generic weighted-GMO occurrence transport

- The first dependency-order check compiled the transport and bridge source,
  but checking `PGSourceAssembly.lean` then exited 1 because direct
  `lake env lean` had not emitted the bridge `.olean`. This was a build-order
  error, not an elaboration or theorem failure.
- `lake build GaoLean.PGWeightedGMOTransport
  GaoLean.PGWeightedGMOBridge`: exit 0, 8676 jobs.
- `lake env lean GaoLean\\PGSourceAssembly.lean`: exit 0 after replacing the
  specialized pair provider by `WeightedGMOPrescribedLengthProvider`.
- Full `lake build`: exit 0, `Build completed successfully (8704 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0. The new
  transport, rewired bridge, and top-level declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`.
- Declaration-level forbidden scan over `*.lean`: no `sorry`, `admit`, new
  `axiom`, or `unsafe`; raw `rg` exit 1 / normalized exit 0.
- Scoped `git diff --check`: exit 0.

M34 proves the occurrence-faithful partition and transport from a generic
weighted-GMO output to the four canonical pair lists, including exact count,
weighted sum, and endpoint non-reuse. It does not prove existence of the
generic weighted-GMO provider. PG-GAO-v1 therefore remains
`LEAN_PARTIALLY_CHECKED`.

## M35: sharp characteristic-two boundary

- Initial single-file development exposed only proof-shape issues in finite
  sum normalization and the explicit endpoint injection; no statement was
  weakened.
- Final `lake env lean
  GaoFormal\\Matching\\CharacteristicTwoBoundary.lean`: exit 0.
- Full `lake build`: exit 0, `Build completed successfully (8705 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0.  The new
  declarations introduce no project axiom; the project-wide audit remains
  within `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: no `sorry`, `admit`, new `axiom`, or `unsafe`;
  normalized exit 0.
- Scoped `git diff --check`: exit 0.

M35 proves that the four-point affine plane over `ZMod 2` has an
independent-difference matching of size one and none of size two.  The
characteristic-not-two hypothesis in M8 is therefore mechanically shown to
be necessary on the frozen sharp example.

## M36: cyclic raw/padded capacity-entry falsification

- Development first promoted the existing arithmetic-only sketch to exact
  occurrence selections, then added same-cardinality pullback through a
  single reflection, cyclic target avoidance, exact proper-subgroup counts,
  and raw/padded gate inequalities.  Intermediate failures were elaboration
  and finite-count normalization issues; the frozen family was not weakened.
- Final `lake env lean GaoLean\\SequenceEntryCounterexample.lean`: exit 0
  with no diagnostics.
- Full `lake build`: exit 0, `Build completed successfully (8706 jobs)`.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0.  Every new
  declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: no `sorry`, `admit`, new `axiom`, or `unsafe`;
  normalized exit 0.
- Scoped `git diff --check`: exit 0.

M36 proves the full infinite family from the `gao0824` result ledger, not only
its displayed integer identities.  It is a theorem-level falsification of
the unconditional entry interfaces, not a counterexample to PG-GAO.

## M37: exact `C₃` plus-minus exception

- Early attempts to decide the quantified proposition wholesale failed
  because it contains a sign function witness.  The final proof supplies the
  occurrence selection and sign function explicitly; no statement was
  weakened and no computational oracle proves the quantified theorem.
- Final `lake env lean GaoLean\SmallGroupExceptions.lean`: exit 0.
- Full `lake build`: exit 0, `Build completed successfully (8707 jobs)`.
- Unified `lake env lean GaoFormal\AxiomAudit.lean`: exit 0.  Every new
  declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: no `sorry`, `admit`, new `axiom`, or `unsafe`;
  raw `rg` exit 1 / normalized pass.
- Scoped `git diff --check`: exit 0.

M37 establishes `D±(C₃)=2` in the project’s occurrence-sensitive semantics.
It fully disproves the frozen uniform A5 gap-two claim and the raw A6
gap-three specialization at `C₃`; it does not assert either repaired
exceptional-group classification or the separate A6 two-exit refutation.

## M38: explicit `C₃` raw A6 two-exit refutation

- `GaoLean/A6RawCounterexample.lean` freezes the source word, labelled
  pair-complete quantifier, and origin-centred capacity gate.
- Final `lake env lean GaoLean\A6RawCounterexample.lean`: exit 0.
- Full `lake build`: exit 0, `Build completed successfully (8708 jobs)`.
- Unified `lake env lean GaoFormal\AxiomAudit.lean`: exit 0. Every new
  declaration reports only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: no `sorry`, `admit`, new `axiom`, or `unsafe`;
  raw `rg` exit 1 / normalized pass.
- Scoped `git diff --check`: exit 0.

M38 proves both raw exits false on the advertised length-nine/six-reflection
input and independently proves that the same word has an exact-six
product-one target. It does not claim the repaired v2 classification.

## M39: labelled affine-failure residue identity

- Final `lake env lean GaoFormal\Matching\AffineFailure.lean`: exit 0.
- Full `lake build`: exit 0, `Build completed successfully (8709 jobs)`.
- Unified `lake env lean GaoFormal\AxiomAudit.lean`: exit 0. New declarations
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: no `sorry`, `admit`, new `axiom`, or `unsafe`;
  raw `rg` exit 1 / normalized pass.
- Scoped `git diff --check`: exit 0.

M39 checks the occurrence-labelled quotient accounting in frozen formula
(3.4), but not yet the reverse fixed-cardinality extension. M10 therefore
advances from `NOT_FORMALIZED` to `LEAN_PARTIAL`, not to full.

## M40: occurrence-labelled toggle and filler mechanics

- Final `lake env lean GaoFormal\Matching\ExchangeSelection.lean`: exit 0.
- Full `lake build`: exit 0, `Build completed successfully (8710 jobs)`.
- Unified `lake env lean GaoFormal\AxiomAudit.lean`: exit 0. New declarations
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: no `sorry`, `admit`, new `axiom`, or `unsafe`;
  raw `rg` exit 1 / normalized pass.
- Scoped `git diff --check`: exit 0.

M40 proves global endpoint disjointness, exact toggle cardinality and sum,
and exact filler capacity entirely on source labels. Finite-field coefficient
coverage and the affine reverse construction remain, so M10 stays partial.

## M41: finite-field coefficient coverage and full exchange

- Final `lake env lean GaoFormal\Matching\FiniteFieldCoverage.lean`: exit 0.
- Full `lake build`: exit 0, `Build completed successfully (8711 jobs)`.
- Unified `lake env lean GaoFormal\AxiomAudit.lean`: exit 0. New declarations
  report only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan: no `sorry`, `admit`, new `axiom`, or `unsafe`;
  raw `rg` exit 1 / normalized pass.
- Scoped `git diff --check`: exit 0.

M41 proves coefficient coverage from `q-1` labelled copies directly and
combines it with M40 to obtain every exact-`d` target sum from a spanning
reservoir. Corollary 2.1's exchange conclusion is now checked; the labelled
hyperplane reverse branch keeps M10 partial.

## M42: affine reverse and source-shaped full exchange

- Target `lake build GaoFormal.Matching.AffineReverse`: exit 0.
- The kernel reservoir, exceptional-label preservation, disjoint fillers,
  reverse implication, exact equivalence, and no-reservoir full-exchange
  consumer are checked.
- The raw-hypothesis geometric dichotomy and its `e ≥ q-1` branch remain open.

## M43: one-translation extraction and pullback

- Target `lake build GaoLean.GAOAROneTranslation`: 8672 jobs, exit 0.
- Full `lake build`: 8713 jobs, exit 0.
- Unified `lake env lean GaoFormal\\AxiomAudit.lean`: exit 0; all audited
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`.
- Forbidden declaration scan includes `native_decide` and passes; scoped
  `git diff --check` passes.

M43 checks the uniform heavy-support and availability arithmetic, exact
translated residual membership, no-outside-entry lemma, subtype-to-list
exchange bridge, automatic labelled quotient extraction, exact completion,
and same-label translation pullback. `GAO-AR-v1` remains `LEAN_PARTIAL`
because no theorem yet produces the complete residual/affine input or joins
the rank-two, rank-three, lower-bound, and rank-at-least-four branches.

## M44: automatic affine-hyperplane certificate

- Target `lake build GaoFormal.Matching.AffineReverse`: 8663 jobs, exit 0.
- Unified `lake build GaoFormal.AxiomAudit`: 8713 jobs, exit 0.
- `exists_affineHyperplaneGeometry_of_linearSpan_eq_top` and
  `exists_affineHyperplaneCertificate_of_linearSpan_eq_top` report only
  `propext`, `Classical.choice`, and `Quot.sound`.

M44 derives the codimension-one affine geometry, canonical quotient, fibre
value, and exact exceptional occurrence set from raw heavy-support hypotheses.
The constructive `e ≥ q - 1` alternative and the final affine split remain,
so M10 and `GAO-AR-v1` stay partial.

## M45-A: variable-direction quotient coverage

- Target `lake build GaoFormal.Matching.VariableDirectionCoverage`: 8664
  jobs, exit 0.
- Unified `lake build GaoFormal.AxiomAudit`: 8714 jobs, exit 0.
- `exists_labelled_subset_sum_eq_of_nonzero` reports only `propext`,
  `Classical.choice`, and `Quot.sound`.

M45-A proves the labelled Cauchy--Davenport coverage used by the cross-pair
quotient layer.  The occurrence-disjoint cross-pair construction and its
combination with the kernel reservoir remain M45-B.

## M45-B / M46: complete affine exchange dichotomy

- Target `lake build GaoFormal.Matching.FullExchangeBranch`: 8665 jobs,
  exit 0.
- The new cross-pair, unused-heavy, large-exceptional, and top-level dichotomy
  declarations report only `propext`, `Classical.choice`, and `Quot.sound`.
- Full `lake build`: 8715 jobs, exit 0.
- Unified `lake build GaoFormal.AxiomAudit`: 8715 jobs, exit 0; the audited
  declarations use only the same three standard axioms.
- Forbidden scan over `GaoFormal` and `GaoLean`: no `sorry`, `admit`,
  declaration `axiom`, `unsafe`, or `native_decide` match.

M46 constructs the complete occurrence-labelled `e≥q-1` exchange and joins
it with the full-affine and small-exceptional branches.  Thus the affine
dichotomy is `LEAN_FULL`; `GAO-AR-v1` remains `LEAN_PARTIAL` at the later
residual producer, low-rank/lower-bound, and top-level assembly boundaries.
## R3-L: complete line completion

The rank-three line route now derives the quotient small-Davenport bound by
complement lifting, closes both quotient alternatives and the few-nonzero
identity leaf, and exposes `rankThree_line_upper` with the manuscript's stated
hypotheses.  The whole remote build completed successfully with 8730 jobs;
the new axiom prints contain no `sorryAx` or paper-specific axiom.

## M48: rank-three plane descent, rank-free controller, and final assembly

- `rankThree_plane_upper`, `rankThree_middle_upper`, and `rankThree_upper`
  compile with only `propext`, `Classical.choice`, and `Quot.sound`.
- `concretePGO3ControllerSkeleton_of_structuralGMO` constructs the complete
  simultaneous residual controller from named source inputs.
- `pgGaoV1Statement_of_structuralRemainingInputs` realizes the exact frozen
  p-group statement conditionally on the explicit cited-source package.
- Full remote `lake build`: 8735 jobs, exit 0.
- No project-specific axiom or `sorryAx` appears in the new theorem audits.
## 2026-08-26: gao0824 PR #7 13-page source freeze (M49)

- Corrected the manuscript identity to `randomcat4/gao0824#7@6d4ab81`, the
  13-page arXiv rewrite.
- Added `GaoLean/PR7ThirteenPage.lean` and compiled the exact conditional
  statement alias `PR7ThirteenPageMainStatement`.
- `lake build GaoLean.PR7ThirteenPage`: 8724 jobs, exit 0.
- Full `lake build`: 8736 jobs, exit 0.
- `lake build GaoFormal.AxiomAudit`: 8736 jobs, exit 0.
- Final conditional theorem axioms: `propext`, `Classical.choice`,
  `Quot.sound` only.
- Declaration-level `sorry`/`admit`/`axiom`/`unsafe`/`native_decide` scan:
  no matches.
- Status remains `LEAN_CONDITIONAL`; the remaining package includes both
  cited inputs and paper-internal Davenport statements not yet formalized.

## 2026-08-26: independent paragraph audits and main review

- Two independent read-only paragraph audits both returned `CRITICAL_GAPS`.
- Main review confirmed no circular target/controller field in the remaining-input package.
- Added and compiled the general group-cardinality theorem and the exact-length/
  all-lengths-at-least threshold equivalence.
- `lake build GaoLean.PGStatements GaoLean.PR7ThirteenPage`: 8724 jobs, exit 0.
- Final status remains `CRITICAL_GAPS / LEAN_CONDITIONAL`; Proposition 3.1,
  Lemma 5.2, Olson, GJM, and GMO are the remaining load-bearing boundaries.

## 2026-08-26: internal Davenport convolution (M50)

- Added `GaoLean.PGDavenportConvolution`, including exact ordinary Davenport
  values, occurrence-labelled prefix/suffix mechanics, and the subgroup--
  quotient zero-sum-free concatenation argument.
- Proved `ordinaryDavenport_subgroup_quotient`:
  `D(K) + D(A/K) <= D(A) + 1` from the three exact constants.
- Refactored `GAOARFinal` so the final structural input package no longer
  contains an arbitrary convolution inequality; the theorem derives it
  internally from canonical exact Davenport constants.
- Target module build: 8688 jobs, exit 0; full build and unified axiom audit:
  8737 jobs, exit 0.  The new declarations use only `propext`,
  `Classical.choice`, and `Quot.sound`; the forbidden-declaration scan and
  `git diff --check` pass.
- The overall status remains `CRITICAL_GAPS / LEAN_CONDITIONAL`; the remaining
  load-bearing boundaries are Proposition 3.1, Olson, GJM, and GMO.

## 2026-08-26: Proposition 3.1 group-algebra core (M51)

- Added literal `ZMod p` additive group-algebra factors and an
  occurrence-faithful support expansion.
- Proved the `[0]` coefficient is `(-2)^m` under absence of a nonzero
  restricted relation, and derived the relation from product vanishing.
- Proved the paper's square-factor identity and reduced product vanishing to
  generator-level augmentation nilpotence at degree `D`.
- Full server build and unified axiom audit: 8738 jobs, exit 0.  New audited
  declarations use only `propext`, `Classical.choice`, and `Quot.sound`;
  forbidden-declaration scan and `git diff --check` pass.
- Proposition 3.1 remains partial only at the invariant-factor-to-`I^D=0`
  layer; the top-level manuscript status is unchanged.
