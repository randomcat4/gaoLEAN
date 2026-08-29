# PG-GAO faithful mechanical coverage

## Frozen statement

`GaoLean.PGGaoV1Statement` encodes the frozen p-group claim using finite
occurrence-labelled lists:

- `A` is a nontrivial finite abelian `p`-group with `p ≠ 2`;
- `D` is certified by `IsOrdinaryDavenportConstant A D`;
- the target generalized-dihedral group is the concrete semidirect product
  `A ⋊_{-1} C₂`;
- the exact product-one threshold is `2|A|+D`, with block size `2|A|`.

This declaration is `STATEMENT_ONLY`: compiling a proposition definition is
not a proof of it.

## Mechanically checked unconditional closure

- occurrence-sensitive selections, multiplicities, arbitrary literal product
  orderings, and exact-cardinality product-one subsequences;
- abstract generalized-dihedral multiplication and the concrete
  `Multiplicative A ⋊ Multiplicative (ZMod 2)` realization;
- the occurrence-labelled bridge deleting zero restricted coefficients and
  converting coefficients in `{-1,0,1}` to a nonempty plus-minus zero sum;
- odd-`D` arithmetic for `m=(D+1)/2`;
- odd-quotient two-torsion elimination and the dangerous implication
  `{x,-x}⊆β+K ⇒ x∈K` in difference form;
- complete middle-regime numerical bookkeeping, surplus inequality,
  reflection-count trichotomy, same-type pair count, identity-padding label
  choice, and the `2|A|` translation-pullback sum identity;
- exact `RC_S(K)` / `ZR_A(X,K)` quantifier skeletons, explicitly marked as
  statement-only;
- the concrete quotient homomorphism `G(A) → G(A/K)`, including its action on
  rotations/reflections, preservation of the rotation coset, and the quotient
  formula for additive coordinates.
- the exact PG-O3 quotient guard on original occurrence labels, its list/generic
  semantic equivalence, quotient factorization through `H≤K`, deletion of
  precisely the identities created by projection, and survival of a reflection;
- translation of rotation values by a kernel element, invariance of the guard
  modulo `K`, and the combined strict-subgroup guard transfer on the unchanged
  source occurrence type.
- maximum occurrence-labelled product-one core extraction, proof that its
  complement is product-one-free, exact identity padding, and the zero-guard
  implication that the auxiliary core is rotation-only;
- both `K=0` controller bases conditional on the explicit
  `SmallDavenportProductOneFreeAtMost` interface, finite strict-subgroup
  well-founded scheduling, and the exact all-rotation translation pullback on
  the same selected occurrences.
- the actual translated auxiliary list, canonical occurrence reindexing,
  length/rotation/reflection count invariance, quotient-guard descent on that
  list, affine-coset-to-`H` capacity inclusion, and the complete recursive
  `ZR_A(Y^alpha,H)` invocation/pullback once its numerical capacity premise is
  supplied.
- the strict-subgroup quotient-card factorization, automatic `I,J>=2`, exact
  truncated-natural form of (5.10)-(5.11), and its composition with a labelled
  affine-coset concentration set and the smaller `ZR` theorem.
- occurrence-labelled coordinate sums and complements, zero-sum-to-product-one
  for all rotations, and the exact-cardinality ordinary full-spectrum
  consequence (5.14)-(5.15), conditional only on receiving the specified
  labelled subselection.
- an abstract single-reservoir `OrdinarySpectrumAlternative` parameter and a
  checked consumer. This interface is not used as the faithful Section 5.2
  encoding when the outside-`K` reservoir `Bprime` is nonempty.
- the elementary positive-even-reflection ordering interface: balanced plus
  and minus reflection-coordinate lists, arbitrary signed rotation lists, an
  explicit literal word, exact selected-multiset preservation, the signed-sum
  product formula, and occurrence-labelled exact-cardinality product-one
  lifts.
- the high-reflection signed-pair post-processing: rotation-pair label `u+v`,
  reflection-pair label `x-y`, reversal of negative reflection pairs, exact
  occurrence carrier preservation, and the implication from exactly `q`
  weighted pairs with a reflection pair to an exact `2q` product-one block.
- canonical consecutive pairing of the actual rotation/reflection occurrence
  positions, separately by type: exact cover up to one terminal occurrence,
  global endpoint `Nodup`, exact floor pair counts, and the odd-total count
  identity used by the high-reflection branch;
- an occurrence-level signed pair-selection interface whose pairs must belong
  to that reservoir, together with the checked conversion to the balanced
  coordinate consumer and its exact `2q` product-one conclusion.
- the full internal high-reflection branch after weighted GMO: exact (4.1)
  threshold arithmetic, the `b≤2Q-1` capacity bound, forced selection of a
  reflection pair, faithful target membership in `Q • A`, the
  `Q=|A| ⇒ Q • A={0}` reduction, and the final exact `2Q` product-one block.
- the middle full-spectrum post-output branch: constructive selection of the
  positive even `e` reflection occurrences, equal nonempty sign classes,
  occurrence-to-coordinate carrier fidelity, exact `ell+e=2Q` counting, and
  the final balanced-sign product-one ordering.
- the middle non-full post-concentration front end: oddness of `A/K`, the
  occurrence-wise weighted-coset implication `{x,-x}⊆β+K ⇒ x∈K`, exact
  labelled capacity `b-|A/K|+2`, and invocation of the fixed-source `RC_S(K)`
  conclusion from an explicit controller skeleton.
- a unified middle-route consumer from the explicit full/non-full occurrence-
  data disjunction to the same exact `2Q` product-one conclusion.
- the complete internal `a≤1` branch after ordinary GMO: exact rotation-count
  threshold, source-faithful target membership in `2Q • A`, target annihilation
  from `Q=|A|`, and an exact all-rotation `2Q` product-one block.
- exhaustive all-reflection-count dispatch: the checked trichotomy sends low,
  high, and middle inputs to their audited occurrence-sensitive consumers and
  yields one exact `2Q` conclusion.
- the source-faithful rotation-only Section 5.2 channel with separate labelled
  reservoirs `C` and `Bprime`: the full branch constructs
  `(C \ D0) ∪ Bprime`, while the non-full lower bound is measured only against
  `M=|C|`; both branches close through exact occurrence/cardinality algebra and
  strict smaller-`ZR` descent from an explicit preparation.
- the reflection-containing Section 5.2 channel after preparation: a balanced
  full certificate closes by literal ordering, while a non-full weighted-coset
  certificate yields actual `H`-membership, exact residual capacity, and a
  strict smaller fixed-source `RC_S(H)` call.
- construction of the actual positive `ZR` and positive fixed-source `RC`
  steps from their preparation families, followed by assembly with the checked
  zero bases and strict simultaneous induction into a full
  `PGO3ControllerSkeleton`.
- maximum labelled quotient-zero-sum extraction of the outside-`K` rotation
  reservoir into `B0` and `Bprime`, including exact partition/disjointness,
  quotient-zero-sum-free remainder, `σ(Bprime)∈K`, and the proof that all
  reflections together with `B0` are quotient product-one-free under the
  rotation-channel guard;
- construction of `RotationChannelPreGMOData`, including exact `d`, the
  (5.14) size identity, (5.13) from an explicit Davenport convolution,
  the GMO reservoir threshold, and (5.16) `M-d≥|K|`;
- controller assembly in which the entire rotation preparation family has
  been replaced by the narrow quotient small-Davenport and ordinary-GMO
  providers. The labelled extraction is now internal for every auxiliary `X`.

## Conditional boundary

`pg_pm_v1_of_restrictedCoefficientOutput` is a compiled implication from the
explicit proposition parameter `RestrictedCoefficientOutputAt`; it does not
assert that parameter.  Thus PG-PM is `LEAN_CONDITIONAL`, with the earliest
external blocker the required Troi–Zannier/CFS restricted-coefficient theorem.

Olson's `D(A)` formula, GJM's generalized-dihedral small Davenport theorem,
GMO prescribed-length output, its full-spectrum/non-full-spectrum routing,
and the provider translations from those external theorems remain
`NOT_FORMALIZED`. Both labelled channel extractions are now internal. Both
threshold conjuncts of PG-GAO also remain outside the
certificate.  The simultaneous induction
scheduler, translated recursive-call plumbing, and (5.10)-(5.11) capacity
composition are checked.  The internal ordinary full-spectrum complement is
also checked; its GMO existence premise is not.  No new axiom is used to stand
in for any external theorem.

In particular, the checked reflection-ordering theorem is an implication from
an exact `BalancedSignedAssignment`; it does not construct that assignment
from the reflection-pair/GMO output. The post-selection occurrence-sensitive
construction is now checked; GMO-to-selection existence and the enclosing
branch assembly remain obligations.
For the high-reflection route, the disjoint occurrence-labelled same-type
reservoir and every post-output step are now checked. The remaining predecessor
is precisely the theorem translating the published weighted prescribed-length
GMO result into `PrescribedSignedReservoirTargetOutput`. That interface retains
the published conclusion “weighted sum belongs to `Q • A`”; reflection forcing
and `Q • A={0}` are no longer external assumptions. The interface itself is not
asserted.

For the middle full-spectrum route, `MiddleFullSpectrumOutput` is likewise an
explicit caller parameter, not an assertion. Producing its signed rotation
lists from GMO Corollary 1.3 remains external; choosing and balancing the
reflection occurrences and every downstream occurrence/cardinality/ordering
step are now internal checked theorems.

For the middle non-full route, `MiddleNonfullConcentrationOutput` is a minimal
projection, not an asserted GMO theorem.  It retains the proper subgroup,
actual occurrence selection, exact count, rotation typing, and the two weighted
coset memberships used downstream; the unused ordinary-coset condition is not
claimed.  Once this projection and an actual controller skeleton are supplied,
all steps through `x∈K`, the `RC_S(K)` capacity premise, and the exact `2Q`
conclusion are checked.  Producing the projection from GMO and proving the
nonzero positive controller steps remain `NOT_FORMALIZED`.

`MiddleSpectrumAlternative` now joins the two middle outputs without adding
any conclusion to either one.  Its consumer is checked, but the proposition is
only a caller parameter.  The earliest source boundary is therefore the
faithful application of GMO Corollary 1.3 producing this occurrence-labelled
disjunction; the controller parameter independently requires the positive
`RC/ZR` step proofs.

For `a≤1`, `LowReflectionTargetOutput` is likewise an explicit caller-provided
ordinary-GMO output.  Its checked consumer does not strengthen the target to
zero: that fact is derived internally from `Q=Nat.card A`.  The remaining
blocker in this regime is only the formal GMO application producing the
occurrence-labelled output.

`ReflectionRegimeOutputs` is the current Section 4 boundary.  It does not
assert all three outputs unconditionally; each is required only as an
implication from its true numerical regime.  Its dispatcher is fully checked.
What remains external is precisely the theorem-level production of those
outputs from ordinary/weighted GMO and, in the middle non-full branch, the
actual positive-subgroup controller construction.

For Section 5.2, the old `OrdinarySpectrumAlternative` is deliberately
classified only as an abstract consumer.  `RotationChannelAlternative` is the
faithful interface: it prevents `Bprime` from inflating the non-full GMO count
while still adjoining it in the full closing selection.
`RotationChannelPreparation` and `ReflectionChannelPreparation` are explicit
source obligations, not axioms. Given them, Lean builds both positive
controller steps and the whole PG-O3 controller skeleton. At P5b2p the
remaining work was to derive both preparations. P5b2q now constructs the
rotation preparation from labelled extraction; the reflection preparation and
both channels' external GMO/GJM premises remain.

For the rotation-only channel, the labelled extraction is no longer external.
The implementation uses a maximum zero-sum subselection rather than recording
a particular greedy removal order; it proves the exact source postconditions
and is therefore sufficient for every downstream use. The remaining rotation
inputs are `QuotientSmallDavenportProductOneFreeAtMost`, the relevant
Davenport-number comparison/convolution, and `RotationChannelGMOProvider`.
The reflection preparation still contains the unformalized labelled
`R,U,τ,z` construction and signed GMO application.

P5b2r supersedes that final sentence. The labelled `R,U,τ,z` construction is
now internal and checked in `PGReflectionExtraction.lean`: maximum
reflection-containing quotient-product-one extraction, free remainder,
ordering lift through quotient collisions, positive-even reflection parity,
kernel defect, exact (5.6)--(5.9) counts, the signed-GMO threshold, and
`m≥|K|` are all compiled. `ReflectionChannelExtractedAlternative` narrows the
remaining full output to `U∪Dsel` with `Dsel⊆C` and `|Dsel|=m`; the non-full
output remains measured against unchanged `C`. The controller now compiles
from the two narrow GMO providers without either preparation family.

The exact remaining reflection blocker is external: formalize the published
signed prescribed-length GMO theorem and its ordering/interleaving bridge to
produce the balanced occurrence assignment required by
`ReflectionChannelGMOProvider`; formalize the weighted-coset output for its
non-full branch. Quotient small-Davenport/Davenport values remain explicit
GJM/Olson-facing parameters. No such provider is asserted as an axiom.

## M25--M26: PG-O4 synthesis and PG-O1c lower bound

`PGSynthesis.lean` now performs the concrete occurrence split for each source,
proves that rotation and reflection labels are disjoint and exhaustive, and
routes the actual low/high/middle regime. The residual controller is requested
only in the middle branch. Given explicit branch outputs, this yields the exact
upper property at length `2|A|+D`.

`PGLowerBound.lean` independently closes the occurrence-sensitive identity
padding argument. From `SmallDavenportWitness G D` it constructs, for every
`n<2|A|+D`, a length-`n` word with no product-one subsequence of length
`2|A|`. The proof separates the original prefix and the identity suffix by
occurrence indices and is valid even if the original witness itself contains
identity-valued terms.

The final declaration is deliberately conditional:
`pgGaoV1_of_upperInputs_and_smallDavenportWitness` consumes
`PGGaoUpperInputs` and `SmallDavenportWitness`; it does not manufacture them.
Thus PG-O4 internal bookkeeping and PG-O1c's transformation are
`LEAN_CHECKED`, while unconditional PG-GAO-v1 remains outside the mechanical
closure until the external theorem providers are faithfully formalized.

M27 further narrows the upper boundary. `PGGaoExternalUpperInputs` no longer
contains a residual-controller conclusion. In the middle regime,
`pgGaoUpperInputs_of_externalUpperInputs` builds that controller from the two
narrow GMO providers, quotient small-Davenport values, the ambient
product-one-free bound, and the fully checked PG-O3 stack. The outer regimes
retain only their prescribed-length occurrence outputs. This composition is
`LEAN_CHECKED`; existence of the source package remains `LEAN_CONDITIONAL`.

M28 closes the lower source edge. The zero-sum-free length-`D-1` word supplied
by `IsOrdinaryDavenportConstant A D` is embedded as rotations and extended by
one reflection. Reflection parity, selected-occurrence counting, prefix
selection, and mapped-list occurrence equivalence prove the lifted length-`D`
word product-one-free. Therefore the identity-padding counterexamples now
follow from the frozen ordinary Davenport premise itself. Only upper-side
external providers and the numerical p-group consequences remain.

M29 closes the odd-cardinality consequence of the frozen odd-prime p-group
hypotheses. `Odd (Nat.card A)` is no longer an external field in the strongest
conditional theorem. `D≤|A|` and the upper source providers remain.

M30 packages exactly those remaining obligations as `PGGaoRemainingInputs`
and compiles their implication to the fully quantified `PGGaoV1Statement`.
This makes the residual trust boundary explicit; it does not discharge it.

M31 discharges the remaining numerical obligation `D≤|A|`. The new
`PGDavenportBound.lean` proof uses occurrence-labelled half-open intervals
between equal prefix sums, so multiplicities are preserved. It proves the
bound for every finite additive group directly from
`IsOrdinaryDavenportConstant`, then rewires the strongest p-group closure.
Accordingly `PGGaoRemainingInputs` now means only
`PGGaoExternalUpperInputs`. This is a real reduction of the conditional
boundary, but the external upper package itself remains `LEAN_CONDITIONAL`;
PG-GAO-v1 remains `NOT_FORMALIZED` unconditionally.

M32 replaces the low-reflection arbitrary output field by the actual ordinary
GMO theorem interface. The external input is now
`OrdinaryGMOPrescribedLengthProvider A D`; Lean specializes it to the list of
rotation coordinates and injectively transports selected positions back to
the original generalized-dihedral source. The exact `2|A|` count, rotation
typing, repeated-coordinate semantics, and target sum are checked. The
ordinary GMO theorem itself is not in Mathlib and remains an explicit
provider, while high/middle signed GMO and small-Davenport inputs remain.
Overall status is unchanged: `LEAN_PARTIALLY_CHECKED`.

M33 removes the corresponding arbitrary source-specific output field from the
high-reflection branch. `WeightedGMOPrescribedPairProvider` is uniform over the
canonical occurrence-labelled same-type pair reservoir. From `Odd D` and the
restricted-coefficient source output, Lean derives the plus-minus Davenport
bound and checks the exact reservoir threshold before invoking that provider.
All later pair reversal, endpoint disjointness, exact `2|A|` count, and
product-one ordering remain internal and checked. The provider is nevertheless
still specialized to the required four signed pair lists. A generic additive
weighted-GMO selection and its occurrence-faithful partition/transport have
not been formalized. Thus the new wiring is `LEAN_CHECKED`, provider existence
is `LEAN_CONDITIONAL`, and overall status remains `LEAN_PARTIALLY_CHECKED`.

M34 supersedes the specialized-provider boundary above.
`WeightedGMOPrescribedLengthProvider` is now stated on an arbitrary additive
occurrence list and returns disjoint positive/negative source positions with
the exact prescribed cardinality and weighted target sum.
`PGWeightedGMOTransport.lean` maps those positions to the canonical
same-type-pair reservoir, partitions them by rotation/reflection type and sign,
proves exact cardinality and sum preservation, and derives endpoint non-reuse
from the global reservoir invariant. `PGWeightedGMOBridge.lean` and
`PGSourceAssembly.lean` now consume this generic provider. The transport and
routing are `LEAN_CHECKED`; only existence of the published generic weighted
GMO provider remains `LEAN_CONDITIONAL`. Overall status remains
`LEAN_PARTIALLY_CHECKED` because weighted GMO and the other external provider
families are not yet proved.

## M48 superseding final boundary

`GAOARResidualController.lean` now translates the published ordinary and
signed structural GMO alternatives directly into the rotation and reflection
channels.  It maps every internal subgroup back into the ambient group,
checks the internal quotient cardinality, preserves occurrence labels, and
constructs the simultaneous strict-subgroup `RC`/`ZR` controller.  The former
custom `RotationChannelGMOProvider` and `ReflectionChannelGMOProvider` fields
are absent from the new final boundary.

`GAOARFinal.lean` constructs all three reflection regimes, the residual
controller, the exact upper threshold, and the lower counterexample family,
then proves the fully quantified frozen `PGGaoV1Statement` from
`PGGaoStructuralRemainingInputs`.  Hence the internal proof graph is complete.
The exact status is `LEAN_CONDITIONAL`, since the remaining package consists
of explicit cited literature inputs not currently proved in Mathlib or this
repository.
