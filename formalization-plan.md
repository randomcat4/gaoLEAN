# GAO-PUB-L-LEAN formalization plan

## Scope and status discipline

The project is pinned to Lean 4.32.0.  A milestone is checked only after an
actual build, a forbidden-declaration scan, an axiom audit, and a
natural-language/Lean statement comparison.  External mathematics absent from
Mathlib may appear only as an explicit theorem parameter; it must then be
reported as `LEAN_CONDITIONAL`, never as an axiom or a completed Gao proof.

Current overall status for the frozen 13-page `gao0824` PR #7 theorem:
`LEAN_FULLY_CHECKED`.  The endpoint
`GaoLean.ConcreteGDihedral.pr7ThirteenPageMain` has the exact frozen
quantifiers and no remaining-input, provider, or recursive-output argument.
The older conditional interfaces and the milestone text below are retained as
an audit trail of how the boundary was reduced; they are not dependencies of
the final endpoint.

Merged release receipt: default `lake build` and central
`lake build GaoFormal.AxiomAudit` both completed 8820 jobs with exit 0.  Two
fresh independent paragraph audits of revision `61906ee` each reported
0 blocking / 0 major findings; incremental review of patch `a1b055a` reported
0 blocking / 0 major / 0 minor, and the main-agent review passed.
`pr7ThirteenPageMain` is the core frozen-threshold endpoint.  Full manuscript
display coverage is joint: the core theorem plus the separate Olson, GJM,
unconditional Corollary 6.1, and `C₃²` endpoints.  It is not attributed
literally to one oversized endpoint.

## Dependency DAG

```text
AR-C11: matching structure + add-one augmentation + unmatched-coset difference
    ├── AR-C10: characteristic-not-two two-vector determinant leaf
    └── delete-one/add-two endpoint constructor
             └── quotient gluing of surviving old differences
                    └── one-of-two crossed replacement
                           └── maximum-cardinality contradiction       [CHECKED]
                                  └── affine coordinate bridge          [CHECKED]
                                         ├── c,d independent in V/W_i
                                         └── four quotient identities
                                                └── every matched endpoint in u₀+W [CHECKED]
                                                       ├── unmatched-count boundary [CHECKED]
                                                       ├── affdim(A) ≤ dim(W)=k       [CHECKED]
                                                       └── maximum existence          [CHECKED]
                                                              └── IDM Theorem 1.1      [CHECKED]
                                                                     ├── char ≠ 2 theorem
                                                                     └── char 2 boundary witness [CHECKED]
                                                                            └── Corollary 2.1 occurrence lift
                                                                                   └── affine-exchange Theorem 3.1
                                                                                          └── arbitrary-rank one-translation route

PG-GAO-v1 (separate paper branch; it does not depend on affine matching)
    ├── occurrence-sensitive sequence/product-one semantics
    ├── concrete A ⋊_{-1} C₂ and exact E/d statements
    ├── PG-O1 lower bound
    │      ├── Olson D(A) formula                         [CHECKED]
    │      └── GJM d(A⋊C₂)=D(A)                         [CHECKED]
    ├── PG-PM: D±(A) ≤ (D(A)+1)/2                       [CHECKED]
    │      └── restricted-coefficient group-algebra proof [CHECKED]
    ├── PG-O2 reflection-count front end
    │      ├── balanced-sign literal ordering            [CHECKED]
    │      └── ordinary/signed GMO providers             [CHECKED internally]
    ├── PG-O3 RC_S(K)/ZR_A(X,K)
    │      ├── quotient projection and kernel deletion  [CHECKED]
    │      ├── labelled occurrence preservation         [CHECKED]
    │      ├── kernel translation + guard descent        [CHECKED]
    │      ├── zero-layer maximum core + identity padding [CHECKED conditional
    │      │                                                on GJM bound]
    │      ├── all-rotation translation pullback          [group/selection layer
    │      │                                                CHECKED]
    │      ├── strict simultaneous subgroup induction     [scheduler CHECKED]
    │      ├── nonzero positive RC/ZR branch consumers     [CHECKED from preparations]
    │      └── quotient extraction + GMO preparations      [CHECKED]
    └── PG-O4 exact 2|A| synthesis
           └── PG-GAO-v1                                [LEAN_FULLY_CHECKED]
```

## Milestones

| ID | Mechanical deliverable | Current state |
|---|---|---|
| M0 | Version-controlled Lake project, pinned toolchain and manifest | `LEAN_CHECKED` |
| M1 | R2 structure, add-one augmentation, maximum and unused-coset interface | `LEAN_CHECKED` |
| M2 | R1 crossed determinant leaf | `LEAN_CHECKED` |
| M3 | Delete one edge, add two; prove all endpoints remain globally distinct | `LEAN_CHECKED` |
| M4 | Glue quotient independence of two inserted differences to surviving old differences | `LEAN_CHECKED` |
| M5 | Characteristic-not-two one-of-two replacement and cardinal maximum contradiction | `LEAN_CHECKED` |
| M6 | Derive the four quotient formulas and `c,d` independence from `a_i-u₀ ∉ W` | `LEAN_CHECKED` |
| M7 | Close all counting, affine-span and dimension boundary branches | `LEAN_CHECKED` |
| M8 | State and prove the exact independent-difference matching closed formula | `LEAN_FULLY_CHECKED` |
| M9 | Occurrence-labelled capacity Corollary 2.1 | `LEAN_FULLY_CHECKED` |
| M35 | Sharp `F₂²` characteristic-two counterexample and exact maximum one | `LEAN_FULLY_CHECKED` |
| M36 | Infinite cyclic counterexample to unconditional raw/padded capacity entry | `LEAN_FULLY_DISPROVED` |
| M10 | Affine exchange and arbitrary-rank integration | `LEAN_CHECKED` components; the final p-group route is closed independently by the structural residual controller |
| M46 | Disjoint cross-pair construction, `e≥q-1` full exchange, and raw-support affine dichotomy | `LEAN_CHECKED` |
| P1 | Occurrence/product-one semantics and concrete generalized-dihedral model | `LEAN_CHECKED` |
| P2 | PG-PM restricted-coefficient deletion bridge and odd arithmetic | `LEAN_CHECKED`; restricted-coefficient output is now internal |
| P3 | Middle-regime arithmetic, odd-quotient descent leaf, padding and translation pullback | `LEAN_CHECKED` |
| P4 | Concrete quotient projection `G(A)→G(A/K)` and rotation-coordinate formulas | `LEAN_CHECKED` |
| P5a | Exact quotient guard, identity deletion, label preservation, kernel translation and `H≤K` guard descent | `LEAN_CHECKED` |
| P5b1 | Maximum product-one core, both `K=0` bases, finite strict-subgroup scheduler, exact all-rotation pullback | `LEAN_CHECKED`; GJM bound is now internal |
| P5b2a | Actual translated-list occurrence reindex, guard/count transport, recursive `ZR` invocation and pullback | `LEAN_CHECKED` |
| P5b2b | Strict quotient cardinality and (5.10)-(5.11) capacity composition through a labelled affine-coset set | `LEAN_CHECKED` |
| P5b2c | Occurrence complement (5.15), all-rotation zero-sum ordering, and exact `2Q` full-spectrum closure | `LEAN_CHECKED` |
| P5b2d | Abstract single-reservoir ordinary GMO full/non-full consumer | consumer `LEAN_CHECKED`; not the exact Section 5.2 `C/Bprime` interface |
| P5b2e | Positive balanced reflection signs plus arbitrary rotation signs: explicit literal ordering and occurrence lift | `LEAN_CHECKED` |
| P5b2f | Signed same-type pair output: reverse negative reflection pairs and close exact `q` pairs to `2q` occurrences | `LEAN_CHECKED` |
| P5b2g | Canonical occurrence-labelled same-type reservoir and explicit signed-selection-to-balanced-assignment bridge | `LEAN_CHECKED`; signed GMO existence is now supplied internally |
| P5b2h | Source-shaped high-reflection branch: (4.1), forced reflection, `Q • A={0}`, and exact `2Q` consumer | `LEAN_CHECKED`; weighted GMO output is now internal |
| P5b2i | Middle full-spectrum branch: balanced reflection occurrence choice, signed carrier, exact `ell+e=2Q` consumer | `LEAN_CHECKED`; signed full-spectrum output is now internal |
| P5b2j | Middle non-full front end: odd quotient, weighted-coset descent, labelled capacity, and `RC_S(K)` invocation | `LEAN_CHECKED`; concentration and controller inputs are now internally supplied |
| P5b2k | Middle full/non-full assembly from a minimal post-GMO disjunction | `LEAN_CHECKED`; alternative and controller are now internally supplied |
| P5b2l | At-most-one-reflection branch: threshold, raw `2Q • A` target, annihilation, exact all-rotation block | `LEAN_CHECKED`; ordinary GMO output is now internal |
| P5b2m | Exhaustive reflection-count dispatch across low, high, and middle outputs | `LEAN_CHECKED`; all outputs/controllers are now internally supplied |
| P5b2n | Source-faithful rotation-only channel with separate `C` and `Bprime`, full complement, non-full descent, and positive `ZR` step | `LEAN_CHECKED`; preparation is now internal |
| P5b2o | Reflection-containing full/non-full consumers and positive fixed-source `RC` step | `LEAN_CHECKED`; preparation is now internal |
| P5b2p | Channel preparations, zero bases, and strict simultaneous induction assembled into `PGO3ControllerSkeleton` | `LEAN_CHECKED`; GJM and preparation families are now internal |
| P5b2q | Labelled `B=B0⊔Bprime` quotient extraction, free remainder, (5.12)-(5.16) arithmetic, and rotation preparation from narrow providers | `LEAN_CHECKED`; quotient and ordinary GMO inputs are now internal |
| P5b2r | Labelled reflection quotient extraction `T=U⊔R`, lifted defect/parity, (5.6)-(5.9) arithmetic, and reflection preparation from a narrow provider | `LEAN_CHECKED`; quotient and signed GMO inputs are now internal |
| P5b2 | Nonzero proper-subgroup RC/ZR branch proofs and controller assembly | `LEAN_CHECKED`; labelled extractions, consumers, scheduler, and source providers are closed |
| P5c | PG-O4 occurrence split, exact upper synthesis, PG-O1c lower-bound construction, and PG-GAO composition | `LEAN_FULLY_CHECKED`; final equality has no external provider |
| R3-P | Rank-three plane descent and complete rank-three upper bound | `LEAN_CHECKED` |
| RF | Direct ordinary/signed structural-GMO residual producer and simultaneous controller | `LEAN_CHECKED`; former named source inputs now have internal producers |
| Z | Fully quantified frozen 13-page main statement | `LEAN_FULLY_CHECKED`; endpoint `GaoLean.ConcreteGDihedral.pr7ThirteenPageMain` |

The 2026-08-28 ordinary completion supersedes the historical open-boundary
narrative below.  `PGGaoOrdinaryComplete.lean` constructs the last ordinary
prescribed-length and all-subgroup structural providers from the canonical
`d*` target induction and canonical subgroup extension, then combines them
with the already checked signed providers.  The historical M48 conditional
endpoint remains available, but the frozen final theorem is now unconditional.

M9 is closed. M39–M46 close the labelled affine reverse/full-exchange
consumers, the full raw-support affine dichotomy, and the one-translation
guard, arithmetic, extraction, exact completion, and pullback. M10 remains
partial because the rank-free residual-state producer and final GAO-AR
assembly have not been built as Lean theorems. The independent PG-GAO branch still starts
with exact occurrence semantics and explicit external-theorem interfaces.
P1–P5b1 now have the coverage recorded above.  Well-founded scheduling, both
zero bases modulo GJM, and group-level exact pullback are closed. The
elementary reflection-ordering endpoint is now checked. The canonical
occurrence-labelled same-type reservoir, its exact carrier/count boundary, and
the bridge from an explicit signed selection of its pairs to
`BalancedSignedPairAssignment` are now checked. P5b2h additionally derives the
forced reflection pair, verifies the precise weighted-GMO threshold, and
reduces the published target `Q • A` to zero using `Q=|A|`. The high-reflection
route is therefore internally closed conditional only on a
`PrescribedSignedReservoirTargetOutput`. The earliest remaining edge is the
formal theorem producing that occurrence-labelled output from the published
weighted GMO theorem. Middle-channel assembly remains a separate blocker.
For the middle full-spectrum branch, the balanced reflection choice and every
post-output occurrence/order step are now checked; the remaining edge is the
formal Corollary 1.3 application producing `MiddleFullSpectrumOutput`.
The actual translated-list recursive `ZR` invocation and the capacity
inequalities (5.10)-(5.11) are checked; so are the occurrence-complement and
all-rotation full-spectrum consequences (5.14)-(5.15).  GMO/Troi–Zannier/
Olson/GJM remain external blockers.
The older `OrdinarySpectrumAlternative` theorem remains a checked abstract
single-reservoir consumer.  It is not the exact Section 5.2 rotation channel
when the already extracted outside-`K` reservoir `Bprime` is nonempty: its
non-full count would otherwise be measured against the wrong reservoir.
`PGRotationChannel.lean` repairs this fidelity boundary by keeping `C` and
`Bprime` separate, forming `(C \ D0) ∪ Bprime` only in the full branch, and
measuring non-full concentration against `M=|C|`.
The middle non-full front end is now also checked: a minimal occurrence-labelled
projection of GMO's output yields the exact `RC_S(K)` capacity after deriving
oddness of `A/K` and proving every concentrated `x` lies in `K`.  Its earliest
remaining predecessors are the theorem producing that projection from GMO
Corollary 1.3 and the nonzero positive `RC/ZR` steps needed to inhabit the
controller skeleton.
The two middle outputs are now joined by a checked `MiddleSpectrumAlternative`
consumer.  Consequently no internal case split remains after the explicit
post-GMO disjunction; the remaining work lies before that disjunction or inside
the controller's positive subgroup steps.
The `a≤1` route is internally closed as well: the exact ordinary GMO length
threshold and raw target membership in `2Q • A` are retained, while target
annihilation and occurrence-labelled product-one ordering are checked in Lean.
The entire Section 4 reflection-count split is now mechanically assembled:
given the exact caller-supplied output in whichever regime holds, all counts
lead to the same exact `2Q` product-one conclusion.  No external existence
claim is hidden in the dispatcher.

The Section 5.2 post-preparation layer is now also mechanically assembled.
`RotationChannelPreparedData` produces an actual positive `ZR` step using only
strict smaller `ZR`; `ReflectionChannelPreparedData` closes a balanced full
output or descends to strict smaller fixed-source `RC`; the guard split builds
the actual positive `RC` step.  Finally,
`concretePGO3ControllerSkeleton_of_channelPreparations` combines those steps
with the checked zero bases and simultaneous induction.  The precise earliest
remaining source obligations at P5b2p were the construction of the two
preparation families from labelled quotient extraction and published GMO
outputs, plus the explicit GJM small-Davenport bound. No positive controller
conclusion was assumed directly.

P5b2q removes the quotient-extraction portion of that sentence for the
rotation-only channel. `PGRotationExtraction.lean` chooses a maximum labelled
quotient-zero-sum `Bprime`; its exact complement `B0` is quotient-zero-sum-free,
and all partition, kernel-sum, product-one-free, defect, target-size and
capacity consequences are checked. This is statement-faithful at the level
used by the proof, although the source's procedural greedy order is not
encoded. `concretePGO3ControllerSkeleton_of_rotationGMOProviders` now replaces
the entire rotation preparation family by only a quotient small-Davenport
bound and `RotationChannelGMOProvider`. The earliest internal PG-O3 gap is
therefore the analogous labelled extraction/defect construction for the
reflection-containing channel; the earliest external rotation gap is the
published ordinary GMO provider (with GJM/Olson supplying quotient bounds).

P5b2r supersedes that routing sentence. `PGReflectionExtraction.lean` now
constructs the labelled reflection-channel carrier, maximum
reflection-containing quotient-product-one core `U`, product-one-free
remainder `R`, lifted source ordering, positive-even reflection count, kernel
defect `z`, and all `tau/m` count and capacity consequences. The controller
theorem now assumes neither channel-preparation family. The earliest remaining
reflection edge is external: produce `ReflectionChannelExtractedAlternative`
from signed GMO, including the exact interleaving/balanced-assignment output in
the full branch. Quotient GJM/Olson inputs remain independent parameters.

P5c is now split at its actual trust boundary. `PGSynthesis.lean` computes the
rotation/reflection occurrence partition from each concrete source, dispatches
the low/high/middle reflection regimes, and asks for the residual controller
only in the middle regime. `PGLowerBound.lean` converts an occurrence-labelled
length-`D` product-one-free witness into counterexamples at every threshold
`n < 2|A| + D` by prefix-preserving identity padding. Both constructions are
compiled. The theorem `pgGaoV1_of_upperInputs_and_smallDavenportWitness` is a
conditional composition theorem: the small-Davenport witness and the external
upper-output package are parameters, not conclusions or axioms. The earliest
remaining closure is therefore the faithful production of those parameters
from Troi--Zannier/GJM/Olson and ordinary/signed GMO statements.

M27 removes the coarse middle-controller field from that boundary.
`PGSourceAssembly.lean` constructs the controller from the already checked
quotient extractions, channel preparations, positive branch consumers, zero
bases, and simultaneous induction. Its `PGGaoExternalUpperInputs` exposes the
remaining source obligations directly: ambient/quotient small-Davenport
bounds, low/high prescribed-length outputs, the middle spectrum alternative,
and the ordinary/signed GMO providers. The next closure must prove one of
these interfaces from its frozen source theorem; merely repackaging the whole
upper conclusion is no longer accepted as progress.

M28 closes the lower-witness edge back to the frozen paper premise.
`PGDavenportBridge.lean` proves that a length-`D-1` ordinary zero-sum-free word
in `A`, followed by one reflection after rotation embedding, is a length-`D`
product-one-free word in `A ⋊_{-1} C₂`. The proof is occurrence-sensitive and
uses reflection parity plus explicit prefix/map pullback. Consequently
`pgGaoV1_of_externalUpperInputs_and_isOrdinaryDavenportConstant` requires no
separate lower package. The remaining dependency DAG is now entirely on the
upper side and the numerical consequences `D≤|A|` and `Odd |A|`.

M29 discharges `Odd |A|` directly from the frozen `p.Prime`, `p≠2`, and
`IsPGroup p (Multiplicative A)` hypotheses using pinned Mathlib's cardinality
characterization. The only remaining standalone numerical edge is `D≤|A|`.

M30 closes the dependency DAG syntactically against the exact frozen theorem.
`PGGaoRemainingInputs` contains only `D≤|A|` and the refined external upper
package; `pgGaoV1Statement_of_remainingInputs` proves that this interface
implies `PGGaoV1Statement`. The interface itself remains unproved.

M31 removes the final standalone numerical edge. `PGDavenportBound.lean`
maps `|A|+1` prefix sums into `A`, obtains two equal prefixes by finite
pigeonhole, and turns their half-open interval into an explicit nonempty
`Fin s.length` selection. This proves every length-`|A|` source has a
nonempty occurrence-labelled zero sum and hence derives `D≤|A|` from the
lower-counterexample clause of `IsOrdinaryDavenportConstant`. The strongest
p-group closure now derives that inequality internally, and
`PGGaoRemainingInputs` contains only `PGGaoExternalUpperInputs`. The next DAG
edge is therefore genuinely theorem-facing: populate the low/high/middle,
ambient/quotient small-Davenport, and ordinary/signed GMO provider package.

M32 opens the first theorem-facing field rather than accepting its final
source-specific output. `OrdinaryGMOPrescribedLengthProvider` freezes the
ordinary GMO statement on an additive occurrence sequence: length at least
`k+D-1`, target length `k≥|A|`, and an exact `k`-selection whose sum lies in
`k • A`. `PGOrdinaryGMOBridge.lean` constructs the rotation-coordinate list,
proves its position map back to the generalized-dihedral source injective,
and transports the exact selection, count, rotation typing, and sum. Thus the
low-reflection `LowReflectionTargetOutput` is now built internally. The
ordinary GMO theorem remains external; the arbitrary low-branch output field
does not.

M33 performs the analogous source-level rewiring for the high-reflection
branch without claiming the weighted theorem itself.  The upper package now
supplies oddness of `D`, the frozen restricted-coefficient output at
`(D+1)/2`, and one uniform weighted-GMO provider.  Lean derives
the plus-minus Davenport bound, checks the canonical same-type pair reservoir
meets the exact `Q + D_pm - 1` threshold, and constructs the high-regime target
output.  The arbitrary high-output field has therefore disappeared.

M34 replaces the specialized provider by
`WeightedGMOPrescribedLengthProvider`, a generic statement on an additive
occurrence list. `PGWeightedGMOTransport.lean` proves the complete injective
transport from its disjoint positive/negative selections to the four canonical
pair lists, including pair-type partition, exact cardinality, weighted-sum
identity, and global endpoint non-reuse. The next high-reflection edge is now
only the published generic weighted-GMO theorem itself; its existence remains
an explicit proposition input, not an axiom. Middle signed GMO,
ambient/quotient small-Davenport providers, ordinary GMO, and the parity source
for `D` remain external in parallel.

M35–M37 execute the frozen negative-certificate priority before opening more
external theorem providers. M35 proves the sharp `F₂²` matching boundary;
M36 proves the full infinite cyclic obstruction to unconditional raw/padded
capacity entry; M37 proves the occurrence-sensitive plus-minus threshold of
`C₃` is exactly two. Thus the A5 uniform gap-two and A6 raw gap-three claims
are now theorem-level Lean disproofs. The next item is the separate explicit
six-reflection `C₃` counterexample to the raw A6 two-exit interface; repaired
exceptional-group theorems remain distinct obligations.

M38 closes that explicit six-reflection obligation. The labelled word with
three `rot 1` occurrences and six `refl 0` occurrences has neither frozen raw
exit: a prescribed two-reflection exact-six witness would require four
rotations, and every proper subgroup has zero qualifying rotations against a
gate of at least two. Lean also verifies that all six reflections themselves
form an exact-six product-one target. Thus the raw two-exit is false without
turning this example into a counterexample to the final Gao target.

M39 resumes M10 at formula (3.4). `AffineFailure.lean` defines the exceptional
part on source labels and proves that every fixed-cardinality selection's
quotient defect is exactly its exceptional-offset sum, together with the
two-selection equality equivalence. The remaining M10 edge is constructive:
extend an arbitrary exceptional witness with disjoint exchange endpoints and
fillers, then transport the result through the one-translation group route.

M40 closes the next constructive layer. `ExchangeSelection.lean` proves the
reservoir has exactly `2kt` globally distinct endpoint labels, every toggle
chooses exactly `kt` labels, its sum is the left baseline plus the toggled
directions, and `d+kt≤|Ω|` supplies `d-kt` fillers outside all endpoints. The
next precise edge is finite-field coefficient coverage using `q-1` copies per
direction, followed by the reverse implication in the affine certificate.

M41 closes that coefficient edge. For prime `q`, `FiniteFieldCoverage.lean`
selects `a.val` of the `q-1` labelled copies to realize every scalar
`a : ZMod q`, combines choices over independent directions, and uses M40's
outside-endpoint fillers. A finrank-sized independent reservoir therefore
produces an exact-`d` occurrence selection of every target sum under the
source inequalities. Corollary 2.1's fixed-cardinality exchange content is
now checked; M10 next requires the hyperplane exceptional-set reverse branch.

M42 closes that reverse branch as a source-labelled certificate.
`AffineReverse.lean` constructs the kernel reservoir from the heavy support,
preserves the chosen exceptional labels, supplies disjoint fillers, and proves
the exact equivalence. It also packages full affine exchange without a
caller-supplied reservoir. The complete raw-hypothesis geometric dichotomy,
including construction of the hyperplane and the `e≥q-1` alternative, remains.

M43 closes the planned one-translation consumer mechanics.
`GAOAROneTranslation.lean` proves the uniform heavy-support/availability
arithmetic, the exact translated-residual membership statement, quotient
guard reuse, automatic labelled quotient extraction, exact completion, and
same-label pullback. A subtype bridge connects residual-space exchange to the
list-facing consumer. This is not a top-level GAO-AR proof: the rank-free
residual producer, the full affine dichotomy, and the rank-two/rank-three
upper-bound declarations remain outside the compiled theorem graph.

M44 closes the raw-support geometry edge in the proper affine-span branch.
`AffineReverse.lean` now chooses `α` from the heavy support, proves its vector
span is a hyperplane, constructs the canonical quotient and fibre value, and
constructs the exact exceptional occurrence set before invoking the checked
M42 equivalence.  The caller no longer supplies any of this geometric data.
The next earliest M10 edge is now precisely the constructive `e ≥ q - 1`
full-exchange branch and the top-level split that joins it to this certificate.
The rank-free residual producer and rank-two/rank-three/lower/top-level
GAO-AR declarations remain later independent obligations.

M45-A checks the Cauchy--Davenport quotient-coverage ingredient for the
remaining `e ≥ q - 1` branch.  For `q - 1` labelled nonzero increments in
`ZMod q`, even with repeated values, every quotient target is a labelled
subset sum.  M45-B must still build the disjoint cross-pair occurrence family,
join it to the kernel reservoir, and perform filler bookkeeping.  This is the
frozen server-migration restart point.

M45-B/M46 closes that restart point.  The code constructs an unused heavy
value, globally disjoint heavy/exceptional cross pairs, quotient and kernel
toggles, and outside-endpoint fillers.  The resulting raw-support theorem
splits into full exact exchange or a canonical hyperplane certificate with
at most `q-2` exceptional labels.  The remaining GAO-AR work begins after this
affine theorem: residual-state production, low-rank/lower-bound imports, and
top-level assembly.
