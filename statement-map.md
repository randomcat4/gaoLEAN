# Natural-language to Lean statement map

## Frozen sources

- `evidence/pr9-candidate/independent-difference-matching01.md`, Theorem 1.1
  and Corollary 2.1.
- `evidence/pr9-candidate/affine-exchange01.md`, Theorems 1.1 and 3.1.
- prior mechanical evidence `dossiers/2026-08-23/LEAN/` and `LEAN-R2/`.
- PG branch: `dossiers/2026-08-23/frozen_theorem_pg-v1.md` and
  `A-R6/proof.md`.

## Checked matching map

| Natural-language object or step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Oriented matching with globally distinct endpoints and independent differences | `IndependentDifferenceMatching` | `Sum.elim left right` injective distinguishes every endpoint; orientation affects only the sign of differences. Checked. |
| Add an edge through two unused points if its difference is outside the old span | `extend` | Exact R2 construction on `Option ι`. Checked. |
| Maximum matching forces every two unused-point difference into `W` | `sub_mem_span_of_maximum` | Exact maximum-cardinality contradiction. Checked. |
| All unused points lie in one affine coset, in difference form | `all_unused_sub_mem_span` | Fixes `u₀` and proves `u-u₀∈W`. Checked; not yet wrapped as `AffineSubspace`. |
| R1 determinant: one of the two crossed vector pairs is independent when `2≠0` | `oneReplacement_independent_of_two_ne_zero` | Exact coefficient pairs `(-1,t),(-1,s-1)` and `(-1,s),(-1,t-1)`. Checked. |
| Delete edge `i`, preserve all other edges, add `(a_i,u)` and `(b_i,v)` | `crossedReplacement` | New index is `{j // j≠i} ⊕ Fin 2`; membership and all left/right/cross endpoint collisions are discharged. Checked. |
| Independence in `V/W_i` glues to surviving old differences | `crossedDifference_independent_of_quotient` | Uses Mathlib's quotient gluing theorem and the restricted old independent family. Checked. |
| Either crossed pairing gives a genuine larger matching | `oneOfTwoCrossedReplacements` | Composes the R1 determinant, quotient formulas, endpoint bookkeeping and quotient glue. Checked conditional only on the four explicit quotient-coordinate equalities and `c,d` independence. |
| A maximum matching rules out that coordinate configuration | `not_crossedCoordinateConfiguration_of_maximum` | Proves the replacement index has cardinality `card ι+1` and contradicts `IsMaximum`. Checked. |
| `δᵢ` is outside the span of the other occurrence-labelled differences | `difference_not_mem_deletedSpan` | Uses linear independence and proves equality between the subtype range and the image of the label complement. Checked. |
| `aᵢ-u₀∉W` implies `c=[aᵢ-u₀]`, `d=[δᵢ]` are independent modulo `Wᵢ` | `quotient_pair_independent_of_left_outside` | Exact source implication; no quotient independence remains as a hypothesis. Checked. |
| Write unused-point classes as `tδᵢ,sδᵢ` and obtain the four crossed formulas | `exists_quotient_eq_smul_of_mem_fullSpan`, `exists_crossed_quotient_coordinates` | Derives all four displayed coefficient pairs from membership in `W`. Checked. |
| Every matched endpoint lies in `u₀+W` | `left_sub_mem_fullSpan_of_maximum`, `right_sub_mem_fullSpan_of_maximum` | Composes the quotient bridge, determinant, crossed replacement, and maximum contradiction. Checked. |
| Strictly below `⌊|A|/2⌋` leaves two distinct unmatched vertices | `card_usedVertices`, `exists_two_unused_of_card_lt_half` | Counts the injective tagged endpoint image and extracts two elements from the finite complement. Checked. |
| All of `A` lies in one affine coset of `W` | `exists_base_all_sub_mem_fullSpan` | Handles both unused and matched occurrence-labelled vertices. Checked. |
| `affdim A≤dim W=k` | `card_eq_min_finrank_vectorSpan_half_of_maximum` | Uses Mathlib `vectorSpan`, `finrank_mono`, and `finrank_span_eq_card`; also proves both immediate upper bounds. Checked. |
| Choose a maximum matching in a finite search space | `exists_maximum_matching` | Bounds sizes by `|A|/2`, transports arbitrary finite labels to `Fin n`, and selects the maximum achievable `n`. Checked. |
| Theorem 1.1: `νΔ(A)=min(affdim A,⌊|A|/2⌋)` for `char F≠2` | `exists_maximum_matching_at_formula` together with `card_eq_min_finrank_vectorSpan_half_of_maximum` | `2≠0` is the field-level characteristic hypothesis; `finrank (vectorSpan F A)` is the affine dimension. A maximum matching of exactly the formula size exists and every maximum has that size. `LEAN_FULLY_CHECKED` for this theorem statement. |
| Threshold support `A_t={x:v_x(C)≥t}` for an occurrence-labelled sequence | `thresholdSupport` | A sequence is a finite occurrence type `Ω` with value map `C : Ω → V`; fiber cardinality is multiplicity. Checked. |
| Choose `t` distinct copies of every selected support value | `chooseCopies`, `chooseCopies_value`, `chooseCopies_injective` | Uses an explicit injection `Fin t` into the occurrence fiber; labels, not values, are the disjointness objects. Checked. |
| Corollary 2.1: `k` independent directions, `t` pairs per direction, all `2tk` endpoints disjoint | `OccurrenceReservoir`, `toOccurrenceReservoir`, `exists_occurrenceReservoir_at_threshold` | The tagged endpoint map on `(Fin k×Fin t)⊕(Fin k×Fin t)` is injective and every row has its stated direction. `k` is the exact threshold-support formula. `LEAN_FULLY_CHECKED`. |
| Full affine exchange exact-`d` consumer | `OccurrenceReservoir.exists_fixedCardinality_sum_of_fullHeavySupport` | Constructs its own finrank-sized reservoir from the heavy support and returns labelled exact-cardinality selections for every target. Checked under the exact affine-span, half-cardinality, base, and capacity hypotheses. |
| Labelled affine-hyperplane equivalence, including reverse direction | `OccurrenceReservoir.fixedCardinality_sum_iff_exceptionalOffsetSubset_of_heavySupport` | Exceptional labels and repeated values are preserved; fillers avoid both exceptional labels and every reservoir endpoint. Checked once the affine fibre/kernel certificate is supplied. |
| One-translation residual membership and no outside entry | `mem_rotationOccurrencesIn_translatedSequence_iff_affineCoset`, `source_coordinate_mem_of_translated_mem` | Exact source-position equivalence for the actual translated list. Checked. |
| Second quotient extraction, exact completion, and same-label pullback | `hasAllRotationProductOneSubsequence_of_oneTranslationExtraction` | The quotient extraction constructs `Bprime` and `d`; a residual `FullExactExchange` supplies the only internal selection input. Exact `2Q` cardinality and pullback under `Q • α=0` are checked. |

## Exact boundary after Theorem 1.1

All five formerly exposed gaps are now compiled.  The formal theorem uses an
occurrence-label structure rather than introducing a separate numeric `νΔ`
definition: `exists_maximum_matching_at_formula` supplies a maximum matching
at the formula size, while `card_eq_min_finrank_vectorSpan_half_of_maximum`
shows every maximum matching has that size.  This pair is statement-faithful
to Theorem 1.1.

The affine reverse/full-exchange consumers, complete raw-support dichotomy,
one-translation mechanics, rank-two/rank-three upper branches, rank-free
residual controller, lower construction, and final frozen-statement assembly
are now inside the checked graph.  The companion project is
`LEAN_CONDITIONAL` because the cited literature inputs remain explicit
parameters.

## PG-GAO statement boundary

`PG-GAO-v1` is the exact equality `E(A⋊_{-1}C₂)=2|A|+D(A)` for nontrivial
finite odd abelian `p`-groups.  The declaration
`pgGaoV1Statement_of_structuralRemainingInputs` now proves the fully
quantified frozen statement from a source-theorem package. Olson, GJM,
Troi–Zannier/CFS, and GMO are not present
in Mathlib under the required statements; future use must be explicit
parameters and reported `LEAN_CONDITIONAL` until those inputs themselves are
formalized or imported from an audited library.

## Final structural boundary (M48)

| Natural-language step | Lean declaration | Fidelity / remaining boundary |
|---|---|---|
| Ordinary GMO full spectrum or affine concentration | `OrdinaryGMOStructuralProvider` | Exact occurrence-labelled source interface; explicit literature parameter |
| Rotation channel from ordinary structural GMO | `hasAllRotationProductOneSubsequence_of_rotationPreGMO_structural` | Full branch uses the literal `Bprime`; non-full branch preserves labels and translates to strict `H<K` |
| Reflection channel from signed structural GMO | `hasProductOneSubsequence_of_reflectionPreGMO_structural` | Cancels the actual lifted defect; non-full concentration maps back to the ambient subgroup |
| Simultaneous arbitrary-rank controller | `concretePGO3ControllerSkeleton_of_structuralGMO` | Both zero bases and every strict recursive call are internal |
| Exact upper package from source theorems | `pgGaoUpperInputs_of_structuralUpperInputs` | Low/high/middle split and first concentration are constructed internally |
| Fully quantified frozen theorem | `pgGaoV1Statement_of_structuralRemainingInputs` | `LEAN_CONDITIONAL`; sole input is the explicit cited-source package |

The target repository now contains the frozen statement and its largest safe
front-end closure; see `pg-coverage.md`.  In particular, the restricted-
coefficient-to-plus-minus bridge is checked only as an implication from an
explicit parameter, the dangerous odd-quotient subgroup leaf is checked, and
the actual generalized-dihedral quotient homomorphism is checked.  The PG-O3
guard at `A-R6/proof.md:332-344` is now represented exactly by
`QuotientNoReflection`; the equivalence theorem
`quotientNoReflection_iff_on` connects the list statement to its unchanged
occurrence-label type.  The projection/deletion argument at lines 551-554 is
checked by `hasReflectionContainingQuotientProductOne_mono` and
`quotientNoReflection_anti`.  Kernel translation and descent are checked by
`quotientNoReflection_translate_occurrences_anti`.  This does not assemble
the simultaneous induction and does not change PG-GAO-v1 from
`NOT_FORMALIZED`.

The zero-layer source at `A-R6/proof.md:568-601` is now split faithfully.
`exists_productOne_core_with_free_remainder` mechanically realizes greedy
maximal extraction; `exists_large_productOne_core` uses only the explicit
`SmallDavenportProductOneFreeAtMost` input.  The two resulting controller bases
are `rcStatement_bot_of_smallDavenport` and
`concreteZRStatement_bot_of_smallDavenport`.  Thus their remaining external
claim is precisely the GJM small-Davenport bound, not an assumed zero-base
conclusion.  `concretePGO3ControllerSkeleton_of_positiveSteps` checks the
simultaneous strict-subgroup scheduler and isolates only the nonzero RC/ZR
steps.  `isProductOneSelection_of_translated_allRotation` checks the exact
same-selection pullback from lines 557-566.  The actual-list layer is now also
closed: `translatedOccurrenceEquiv` preserves positions,
`quotientNoReflection_translatedSequence_anti` proves the translated quotient
guard, the two `card_*Occurrences_translatedSequence` theorems preserve
`a,b`, and `card_le_rotationOccurrencesIn_translatedSequence` turns a labelled
`alpha+H` concentration into translated `H`-capacity.  Finally,
`hasAllRotationProductOneSubsequence_of_concreteZR_translatedSequence` invokes
the strict-subgroup `ConcreteZRStatement` and pulls its exact `2Q`
all-rotation result back.  The source-specific GMO alternative, its labelled
concentration lower bound, and (5.10)-(5.11) remain outside this theorem.

The finite capacity layer is now separately closed in `PGCapacity.lean`.
`natCard_quotient_eq_mul_quotient_subgroupOf` proves the exact quotient-card
factorization; strictness supplies both factors' lower bound `>=2`; and
`residual_capacity_composition_of_strict` proves (5.10)-(5.11) with Lean's
truncated natural subtraction.  The composite theorem
`hasAllRotationProductOneSubsequence_of_concentration_and_smallerZR` consumes
exactly a strict `H<K`, an `alpha+H` labelled occurrence set and its GMO lower
bound, then closes capacity, recursive `ZR`, and pullback.  Thus the remaining
rotation-channel blocker is the GMO alternative/output itself, not its finite
bookkeeping.

The internal ordinary full-spectrum consequence is also checked in
`PGSpectrum.lean`.  `coordinateSum_sdiff` is the exact occurrence-labelled
identity (5.15), and
`hasAllRotationProductOneSubsequence_of_fullSpectrumComplement` turns a GMO-
specified labelled `D⊆C` with the stated size and sum into the exact `2Q`
all-rotation product-one block of (5.14).  Repeated equal values do not collapse.
The existence of `D` and the assertion that the spectrum is full remain the
external GMO output; the Lean theorem does not assume the desired Gao
conclusion.

`PGGMO.lean` contains an abstract single-reservoir full/non-full consumer named
`OrdinarySpectrumAlternative`.  It is mechanically correct for its stated
input, but it is not the exact encoding of `A-R6/proof.md:482-566` when
`Bprime` is nonempty: the source applies GMO only to `C`, while the full
selection later adjoins `Bprime`.  Treating `C ∪ Bprime` as the GMO reservoir
would demand the unsupported stronger non-full count
`|C|+|Bprime|-|K/H|+2`.  The source-faithful replacement is
`RotationChannelAlternative` in `PGRotationChannel.lean`.

The elementary reflection ordering at `A-R6/proof.md:29-36` is now closed in
`PGReflectionOrdering.lean`. `balancedSignedWord` is an explicit literal word:
all plus rotations precede the first plus reflection, all minus rotations lie
between the first plus and first minus reflections, and the remaining
reflection coordinates alternate by sign class. The hypotheses
`reflectionLengthEq` and `reflectionPlusNonempty` are exactly a positive even
reflection selection with balanced signs. `carrier_eq` is an equality of
multisets, so repeated group values retain their selected multiplicities, and
`signedSum_eq_zero` is exactly the source's vector condition.
`hasProductOneOrdering_of_balancedSignedAssignment` proves the resulting word
has the exact selected multiset and product one;
`isProductOneSelection_of_balancedSignedAssignment` and
`hasProductOneSubsequenceOfCard_of_balancedSignedAssignment` lift this to the
existing occurrence selection and exact-cardinality interfaces. This closes
only the ordering implication. Producing a `BalancedSignedAssignment` from
the pair/GMO selections in the high-reflection and middle reflection channels
remains unformalized; no such existence is assumed or asserted.

The high-reflection post-processing at `A-R6/proof.md:228-243` is now closed in
`PGReflectionPairs.lean`. `BalancedSignedPairAssignment` separates selected
rotation/reflection pairs by their GMO weight. Rotation labels are `u+v`;
reflection labels are `x-y`. Positive reflection pairs contribute `(x,y)` to
the plus/minus classes, while negative pairs contribute `(y,x)`, mechanically
realizing the source's reversal. `carrier_eq` accounts for every selected
group occurrence exactly once, `pairCount_eq` freezes the prescribed number
of selected pairs, and `reflectionPairsNonempty` is the source's “at least one
selected reflection pair” condition. The final theorem derives an exact
`2*q`-term product-one subsequence from the zero weighted label sum. This is a
checked consumer: at that milestone, constructing the disjoint same-type pair
reservoir from the original sequence and deriving the weighted selection from
GMO were not asserted. The reservoir part is closed by the next milestone.

The preceding occurrence pairing at `A-R6/proof.md:220-230` is now represented
in `PGPairReservoir.lean`. `canonicalSameTypePairReservoir` pairs the actual
rotation and reflection occurrence positions separately, covers each typed
position exactly once except for a terminal suffix of length at most one, and
proves global endpoint `Nodup`. Its pair counts are the exact floors of the two
typed occurrence counts; `canonicalSameTypePairReservoir_pairCount_of_odd_total`
records the source odd-total formula. No value-level deduplication occurs.

`PGPairSelection.lean` freezes the next internal interface as
`SignedOccurrencePairSelection`: its four lists contain actual reservoir pairs,
their endpoints are occurrence-disjoint, exactly `q` pairs are selected, at
least one is a reflection pair, and their weighted coordinate sum is zero.
`toBalancedSignedPairAssignment` proves that these occurrence pairs normalize
to the `u+v` / `x-y` coordinate data expected by the checked P5b2f consumer;
`hasProductOneSubsequenceOfTwice_of_signedOccurrencePairSelection` then gives
the exact `2*q` occurrence-labelled product-one block. This is faithful to the
post-selection portion of lines 228-243. It deliberately does not assert the
GMO theorem or prove that GMO selects such lists from the canonical reservoir.
At P5b2g that source-to-interface existence theorem was the first remaining
blocker; P5b2h below closes all of its internal post-output consequences.

`PGHighReflection.lean` now closes the remaining internal content of
`A-R6/proof.md:218-243`. `highReflection_pairThreshold` is exactly (4.1) after
the PG-PM bound; `highReflection_rotationCount_le` derives `b≤2Q-1` from
`a≥D+1` and `a+b=2Q+D`.
`canonicalSameTypePairReservoir_highReflection_ready` combines these with the
actual reservoir count, proving both the GMO length threshold and fewer than
`Q` rotation pairs.

The external boundary is frozen without strengthening the source:
`PrescribedSignedReservoirTargetOutput` supplies exactly `Q` occurrence-
disjoint canonical reservoir pairs, partitioned by type and sign, whose
weighted `u+v` / `x-y` label sum equals `Q • z` for some `z`. Thus it encodes
membership in `QA`, not equality with zero.
`PrescribedSignedReservoirTargetOutput.toZeroOutput` proves `QA={0}` from
`Q=Nat.card A`; `toSignedOccurrencePairSelection` then derives, rather than
assumes, that a reflection pair was selected. Finally,
`hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput` composes all
checked layers to the exact `2Q` occurrence-labelled product-one block.

Consequently Section 4.2 is internally `LEAN_CHECKED` and externally
`LEAN_CONDITIONAL`. The remaining high-reflection blocker is now only the
formal application/translation of the published weighted prescribed-length
GMO theorem to produce `PrescribedSignedReservoirTargetOutput`; no arithmetic,
capacity, reflection-forcing, target-annihilation, or ordering obligation is
left hidden in that interface.

The full-spectrum half of the middle regime at `A-R6/proof.md:245-279` is now
closed internally in `PGMiddleReflection.lean`.
`exists_balancedReflectionOccurrenceChoice_middle` constructs the source's
“choose any `e` reflections, give them balanced signs” step from the actual
reflection occurrence set: it selects
`e=pairedReflectionCount a=2⌊a/2⌋` distinct positions, divides them into equal
nonempty plus/minus lists, and proves both lists contain only reflections.

`MiddleFullSpectrumOutput` is the exact remaining full-spectrum output: four
occurrence lists (signed rotations and the balanced reflections), global
position `Nodup`, exact rotation count `ell`, exact reflection count `e`, and
zero combined signed coordinate sum. `map_occurrenceValue_eq_rot` and
`map_occurrenceValue_eq_refl` turn these actual source positions into the
concrete generalized-dihedral carrier without collapsing repeated values.
`toBalancedSignedAssignment` proves exact selected-multiset fidelity, while
`card_selection` derives `ell+e=2Q` from the already checked middle arithmetic.
`hasProductOneSubsequenceOfTwice_of_middleFullSpectrumOutput` therefore closes
the exact product-one ordering.

This is `LEAN_CONDITIONAL` only at the source theorem boundary: the project
does not assert that GMO Corollary 1.3's full spectrum produces the signed
rotation occurrences cancelling the internally constructed reflection choice.
All reflection selection, multiplicity, cardinality, carrier and ordering
obligations after that output are checked.

The non-full half at `A-R6/proof.md:281-312` is now represented by the minimal
consumer projection `MiddleNonfullConcentrationOutput`.  Its selection consists
of actual source occurrences, carries the exact lower bound
`b-Nat.card (A ⧸ K)+2`, records `K<⊤`, and records for each selected rotation
coordinate `x` a center `β` with `x-β∈K` and `-x-β∈K`.  The source also
mentions an ordinary-coset condition; it is deliberately omitted from this
projection because the subsequent descent does not use it.

`odd_natCard_quotient_of_odd_natCard` derives oddness of `A/K` from oddness of
`A`.  `concentrated_subset_rotationOccurrencesIn` then checks the dangerous
source step: the two difference-form coset memberships give `2x∈K`, and odd
quotient cardinality gives `x∈K`.  `rotationCapacity` preserves the exact
truncated-natural lower bound, and
`hasProductOneSubsequenceOfTwice_of_middleNonfullConcentration` invokes the
fixed-source `RC_S(K)` component of an explicit `PGO3ControllerSkeleton` to
obtain the exact `2Q` block.  Thus the post-concentration front end is
`LEAN_CHECKED`; GMO production of the projection and the controller's positive
subgroup steps remain explicit unproved predecessors.  The theorem does not
assert the controller or any Gao equality.

`PGMiddleAssembly.lean` now freezes the minimal post-GMO split as
`MiddleSpectrumAlternative`: either there is actual full-spectrum occurrence
data, or there is a proper-subgroup concentration witness.  It uses `Nonempty`
and an existential subgroup so both branches carry data while the interface
itself remains a proposition.  The theorem
`hasProductOneSubsequenceOfTwice_of_middleSpectrumAlternative` performs exactly
the source case split at lines 275-312 and invokes the two independently
audited consumers.  This assembly is `LEAN_CHECKED`, conditional on the
explicit alternative and controller parameters.  It does not derive the
alternative from GMO, inhabit the controller, or assert PG-GAO-v1.

The at-most-one-reflection branch at `A-R6/proof.md:205-216` is now closed
internally in `PGLowReflection.lean`.  `lowReflection_rotationCount_lower`
derives the exact threshold `b≥2Q+D-1` from `a≤1` and
`a+b=2Q+D`.  `LowReflectionTargetOutput` keeps actual source occurrence labels,
requires exactly `2Q` selected rotations, and retains GMO's published target
form `coordinateSum=(2Q)•z`; it does not assume zero sum.  Lean proves
`(2Q)•A={0}` from `Q=Nat.card A` and then invokes the audited all-rotation
zero-sum ordering.  The consumer is `LEAN_CHECKED`; the ordinary GMO theorem
producing `LowReflectionTargetOutput` remains an explicit predecessor.

`PGReflectionRegimes.lean` now covers the exhaustive source split at
`A-R6/proof.md:193-312`.  `ReflectionRegimeOutputs` requires only the output
corresponding to a true numerical regime: low ordinary-GMO output under
`a≤1`, high weighted-pair output under `D+1≤a`, or the middle full/non-full
alternative under `2≤a≤D`.  The theorem
`hasProductOneSubsequenceOfTwice_of_reflectionRegimeOutputs` invokes the already
checked `reflection_count_trichotomy` and dispatches to the three audited
consumers.  The unified exact `2Q` conclusion is `LEAN_CHECKED`; each GMO
output and the middle controller remain explicit parameters, so this is not a
proof of those predecessors or of PG-GAO-v1.

## PG-O3 Section 5.2 channel map

| Natural-language step | Lean declaration | Fidelity / remaining boundary |
|---|---|---|
| Rotation channel `C`, outside reservoir `Bprime`, full selection `(C\\D0)∪Bprime`, and exact (5.14) size/sum | `RotationChannelAlternative`; `hasAllRotationProductOneSubsequence_of_rotationChannelAlternative` | `C` and `Bprime` remain occurrence-disjoint and separate. Full complement algebra and exact `2Q` closure checked. The alternative is an explicit preparation output, not GMO. |
| Non-full ordinary GMO concentration measured by `M=|C|`, strict `H<K`, translation, (5.10)-(5.11), smaller `ZR`, pullback | non-full branch of `RotationChannelAlternative`; `RotationChannelPreparedData.hasAllRotationProductOneSubsequence` | Checked after the labelled concentration output. No stronger count involving `Bprime` is assumed. |
| Arbitrary-auxiliary positive `ZR` step | `RotationChannelPreparation`; `concreteZRPositiveStep_of_rotationChannelPreparations` | The conclusion is constructed from preparations for every eligible `X,K`; smaller fixed-source `RC` is intentionally unused, matching lines 556-566. |
| Reflection channel full output after signed GMO and exact `2Q` ordering | `ReflectionChannelFullOutput`; `.hasProductOneSubsequence` | Checked consumer of a balanced occurrence certificate. The source construction of `U`, defect `z`, and the signed GMO output is still hidden inside the explicit preparation and is not formalized. |
| Reflection non-full weighted cosets, `x∈H`, capacity composition, and smaller fixed-source `RC_S(H)` | `ReflectionChannelAlternative`; `ReflectionChannelPreparedData.hasProductOneSubsequence` | Lines 455-480 checked after the labelled alternative. The provisional `U,z` are not carried through descent. |
| Guard split for a positive fixed-source `RC` step | `concreteRCPositiveStep_of_channelPreparations` | `QuotientNoReflection` selects the rotation channel; its negation selects the reflection channel. The theorem constructs, rather than assumes, the positive `RC` conclusion. |
| Middle arithmetic, zero bases, positive steps, and strict simultaneous induction | `middle_controller_base_bound`; `concretePGO3ControllerSkeleton_of_channelPreparations` | Lines 568-616 assembled into the actual controller skeleton, conditional on GJM and both preparation families. |

The earliest remaining PG-O3 closure is now before the channel consumers:
formalize labelled quotient block extraction (`R,U,τ,z` in the reflection
channel and `B0,Bprime,z,d` in the rotation channel), then prove the two
preparation families from the appropriate published GMO theorems.  GJM remains
an independent explicit input.  This is `LEAN_CONDITIONAL`, not a proof of
PG-GAO-v1.

## Rotation quotient extraction map

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Greedily remove quotient zero-sum blocks from outside rotations `B`, leaving zero-sum-free `B0`, and set `Bprime=B\\B0` | `exists_rotationQuotientExtraction`; `RotationQuotientExtraction` | Lean chooses a maximum-cardinality labelled zero-sum `Bprime` and defines its complement `B0`. This is not the same procedural order, but it proves exactly the partition, disjointness, zero-sum, and zero-sum-free postconditions used later. Repeated values retain distinct labels. |
| `z=σ(Bprime)∈K` | `RotationQuotientExtraction.coordinateSum_Bprime_mem`; `RotationChannelPreGMOData.coordinateSum_Bprime_mem` | Derived from the quotient coordinate sum being zero; not assumed. |
| Reflections together with `B0` are product-one-free in `G(A/K)` | `reflection_union_B0_quotientProductOneFree` | Reflection-containing selections contradict `QuotientNoReflection`; rotation-only selections contradict `B0` quotient-zero-sum-freeness. Checked. |
| `a+r0≤D(A/K)` from the quotient small-Davenport theorem | `QuotientSmallDavenportProductOneFreeAtMost`; `exists_rotationChannelPreGMOData` | The implication and labelled carrier are checked; the numerical quotient bound is an explicit GJM/Olson-facing parameter. |
| `d=D-a-r0`, exact (5.14) size, (5.13), GMO length threshold, and (5.16) `m≥|K|` | `RotationChannelPreGMOData`; `.defect_ge_of_davenport_split`; `.reservoir_threshold`; `.target_ge_card_subgroup` | Exact natural-subtraction and quotient-cardinality arithmetic checked. The Davenport convolution identity remains explicit where used. |
| Produce `RotationChannelPreparation` after extraction | `rotationChannelPreparation_of_extraction` | Only the quotient small-Davenport bound, its comparison with `D`, controller capacity, and `RotationChannelGMOProvider` remain parameters. |
| Assemble the controller without assuming a rotation preparation family | `concretePGO3ControllerSkeleton_of_rotationGMOProviders` | The arbitrary-`X` extraction is constructed internally. Reflection preparation, ambient/quotient GJM inputs, and GMO remain explicit. |

Thus `B0,Bprime,z,d` are no longer part of the rotation-channel blocker.  The
remaining rotation boundary is the actual formal translation of the published
ordinary GMO theorem and the external small-Davenport/Davenport-constant
identities.  The reflection channel still lacks the labelled construction of
`R,U,τ,z` and its signed GMO provider. PG-GAO-v1 remains `NOT_FORMALIZED`.

## Reflection quotient extraction map (P5b2r; supersedes the last sentence)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| `T` is all reflections plus outside-`K` rotations | `reflectionQuotientCarrier`; `reflectionQuotientCarrier_eq_quotientCarrierOccurrences` | Exact equality with the audited nonidentity quotient carrier; occurrence labels and multiplicities retained. |
| Start with a reflection-containing quotient-product-one block, add disjoint blocks, leave product-one-free `R`, put `U=T\R` | `exists_reflectionQuotientExtraction`; `ReflectionQuotientExtraction` | Lean chooses a maximum-cardinality reflection-containing quotient-product-one labelled selection and takes its exact complement. It does not encode one procedural greedy order, but proves exactly the partition, reflection, product-one, and free-remainder postconditions used by the source. |
| Lift the quotient ordering to `G`; obtain defect `z∈K` | `exists_liftedQuotientOrdering`; `LiftedQuotientOrdering.product_isRotation_and_coordinate_mem` | The lift is multiplicity-faithful even when quotient images collide. Kernel membership is derived from the quotient product, not assumed. |
| `U` contains a positive even number of reflections | `even_reflectionCount_of_word_prod_one`; `positive_even_selectedReflectionCount` | Checked through the `C₂` right coordinate and `ZMod 2`; count is on the selected source multiset. |
| `τ=D-|R|`, `m=M-τ`, (5.7) threshold, (5.8) `m≥|K|`, and (5.9) `|U|+m=2Q` | `ReflectionChannelPreGMOData`; `.tau_ge_of_davenport_split`; `.signed_reservoir_threshold`; `.target_ge_card_subgroup`; `exists_reflectionChannelPreGMOData` | Exact truncated-natural arithmetic and quotient-cardinality factorization checked. Quotient small-Davenport and the Davenport split remain explicit inputs where used. |
| Full signed-GMO output uses exactly `U` plus `m` occurrences from `C`; non-full output uses unchanged `C` | `ReflectionChannelExtractedFullOutput`; `ReflectionChannelExtractedAlternative`; `ReflectionChannelGMOProvider` | The provider is a proposition parameter, not an axiom. Full carrier/count linkage is checked; producing the balanced assignment from the published signed theorem and lifted ordering is still external. |
| Produce reflection preparation and assemble the controller without either preparation family | `reflectionChannelPreparation_of_extraction`; `concretePGO3ControllerSkeleton_of_channelGMOProviders` | Both extraction families are internal. Remaining channel assumptions are explicit GMO and quotient small-Davenport providers. |

The reflection-channel `R,U,τ,z` construction is therefore no longer an
internal blocker. The earliest exact full-branch blocker is the theorem
turning the published signed prescribed-length GMO output, together with the
lifted ordering of `U`, into the required occurrence-labelled balanced
assignment on `U∪Dsel`. GJM/Olson-facing numerical inputs, PG-O4, and PG-GAO-v1
remain unformalized.

## PG-O1c lower bound and PG-O4 synthesis map (M25--M26)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Split every source occurrence into rotations and reflections | `rotationOccurrences`; `reflectionOccurrences`; `rotationOccurrences_union_reflectionOccurrences`; `card_reflectionOccurrences_add_card_rotationOccurrences` | Exact partition on source indices. Equal-valued repeated terms remain distinct occurrences. Checked. |
| Invoke low/high output only in its numerical regime and the residual controller only in the middle regime | `ReflectionRegimeClosureInputs`; `hasProductOneSubsequenceOfTwice_of_reflectionRegimeClosureInputs` | The three-way route uses the actual reflection count `a` and checked cardinality identity `a+b=|source|`. No global controller is assumed outside the middle branch. Checked. |
| Obtain the exact upper threshold `2|A|+D` | `PGGaoUpperInputs`; `hasExactProductOneBlockAtLength_of_pgGaoUpperInputs` | Internal PG-O4 dispatch is checked. The branch outputs and external theorem bridges are still explicit proposition fields. Conditional, not a proof of their existence. |
| Pad a length-`D` product-one-free word by identities without losing occurrence labels | `SmallDavenportWitness`; `noProductOneBlock_of_identityPadding` | Prefix/suffix separation is by `Fin` occurrence embeddings, not by value. Identity-valued entries already in the witness are preserved. Checked. |
| Produce a counterexample for every `n<2|A|+D` | `pgGaoThresholdCounterexamples_of_smallDavenportWitness` | Handles `n<2|A|` by the cardinality obstruction and `2|A|≤n` by exact identity padding. Checked. |
| Conclude the frozen threshold equality | `pgGaoV1_of_upperInputs_and_smallDavenportWitness` | Checked only as implication from `PGGaoUpperInputs` and `SmallDavenportWitness`. It neither constructs those inputs nor asserts PG-GAO-v1 unconditionally. |

Consequently the occurrence bookkeeping and lower-bound transformation are no
longer blockers. The exact remaining boundary is external: construct the
small-Davenport witness and every upper-output field from the cited
Troi--Zannier/GJM/Olson and ordinary/signed GMO results, including the faithful
balanced-assignment bridge. Overall status remains `LEAN_PARTIALLY_CHECKED`.

## Source-level upper assembly map (M27)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Keep only the actual external data for a middle source | `PGMiddleExternalInputs` | Separates the fixed-source spectrum/reflection channel from the arbitrary auxiliary sources required by the rotation `ZR` channel. Checked as an interface; no provider is proved. |
| State the upper theorem boundary without assuming a residual controller | `PGGaoExternalUpperInputs` | Quantifies ambient and quotient small-Davenport bounds, low/high outputs in their regimes, middle spectrum output, and both narrow GMO providers. It contains no `PGO3ControllerSkeleton` field. |
| Build the middle controller and recover the exact upper package | `pgGaoUpperInputs_of_externalUpperInputs` | Quotient extraction, channel preparation, strict-subgroup induction, and regime routing are all invoked internally. Checked. |
| Compose the refined upper boundary with the occurrence-sensitive lower witness | `pgGaoV1_of_externalUpperInputs_and_smallDavenportWitness` | Conditional theorem only. External upper fields and the lower witness remain explicit inputs. |

This refinement prevents the checked PG-O3 machinery from being hidden behind
one arbitrary top-level output package. It does not formalize the published
theorems that must populate the remaining fields.

## High-reflection weighted GMO source bridge (M33)

Natural-language anchor: `A-R6/proof.md:218--243`.

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Theorem 3.1 gives `D_pm(A) ≤ (D+1)/2` | `plusMinusDavenportAtMost_of_restrictedCoefficientOutput`; `exists_highReflectionTargetOutput_of_weightedGMO` | The restricted-coefficient relation-to-occurrence bridge and the arithmetic specialization are checked. Existence of that source output and `Odd D` remain explicit inputs. |
| Pair rotations and reflections separately and obtain at least `Q+D_pm(A)-1` pair labels | `canonicalSameTypePairReservoir_highReflection_ready` | The canonical pair reservoir, endpoint disjointness, odd-total floor count, `b≤2Q-1`, and threshold arithmetic are already checked and are invoked here. |
| Weighted GMO selects exactly `Q` labels with signed sum in `Q A={0}` | `WeightedGMOPrescribedLengthProvider`; `WeightedGMOTargetOutput` | The external interface is now the generic occurrence-labelled additive statement. It receives the exact threshold and plus-minus bound and returns disjoint positive/negative source positions. It is a proposition parameter, not an axiom. |
| Partition the selected labels by pair type and sign without reusing endpoints | `PrescribedSignedReservoirTargetOutput.ofWeightedGMOTargetOutput` | `LEAN_CHECKED`: the position-to-pair map is injective, rotation/reflection filters preserve the weighted sum and exact cardinality, and all four pair lists have globally nodup endpoints. |
| Reverse negative reflection pairs and sign both rotations; obtain exactly `2Q` distinct source occurrences with product one | `PrescribedSignedReservoirTargetOutput.toZeroOutput`; `hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput` | Already checked occurrence-wise: selected pair endpoints are not reused and the exact count/product-one consumer is internal. |
| Populate the high branch of the source-level upper package | `pgGaoUpperInputs_of_externalUpperInputs` | Checked from `Odd D`, restricted-coefficient output, and the uniform weighted provider. No arbitrary per-source high output remains. |

M33 is `LEAN_CHECKED` as an interface specialization and routing theorem. M34
closes the previously missing generic occurrence transport and replaces the
specialized provider by `WeightedGMOPrescribedLengthProvider`. The earliest
exact blocker is now existence of that published generic weighted-GMO theorem
itself. It remains `LEAN_CONDITIONAL`; neither M33 nor M34 proves weighted GMO
or PG-GAO-v1.

## Ordinary Davenport to group lower witness (M28)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Choose a zero-sum-free additive word of length `D-1` | `smallDavenportWitness_of_isOrdinaryDavenportConstant` | Derived from the lower conjunct of the frozen `IsOrdinaryDavenportConstant`; `D>0` is proved from its upper conjunct. Checked. |
| Embed the word as rotations and append one reflection | `davenportLiftWord` | Literal source is `w.map rot ++ [refl 0]`, of exact length `D`. Checked. |
| A product-one subselection cannot use the unique reflection | `selectedReflectionCount_le_reflectionOccurrences_card`; `even_selectedReflectionCount_of_productOneSelection`; `allRotation_of_productOneSelection_of_reflection_card_le_one` | Counts source occurrences, not values. Product-one parity forces the selected count to be zero. Checked. |
| Pull selected rotations back to the original additive occurrences | `mapOccurrenceEquiv`; `pullbackMapSelection`; `selectedMultiset_pullbackMapSelection`; `hasNonemptyZeroSum_of_productOneSelection_davenportLiftWord` | Explicit `Fin` equivalence preserves repeated values and exact multiplicity; coordinate sum zero yields the forbidden nonempty additive zero sum. Checked. |
| Remove the separate lower-witness input from the final conditional theorem | `pgGaoV1_of_externalUpperInputs_and_isOrdinaryDavenportConstant` | Consumes the frozen ordinary Davenport premise directly. Upper source providers and numerical p-group consequences remain parameters. |

M26's statement that `SmallDavenportWitness` was an external GJM-facing input
is superseded: its existence is now internal under the frozen ordinary
Davenport hypothesis.

## Odd p-group cardinality map (M29)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| A finite `p`-group has cardinality `p^n` | `odd_natCard_of_odd_prime_pgroup` via `IsPGroup.iff_card` | Uses the frozen `IsPGroup p (Multiplicative A)` hypothesis and pinned Mathlib. Checked. |
| An odd prime power is odd | `odd_natCard_of_odd_prime_pgroup` via `Prime.odd_of_ne_two` and `Odd.pow` | Exact numerical implication, checked. |
| Remove the separate odd-cardinality parameter | `pgGaoV1_of_externalUpperInputs_and_ordinaryDavenport_of_pgroup` | Conditional on the upper source package and `D≤|A|`; no longer conditional on an independently supplied oddness fact. |

## Exact frozen-statement residual map (M30)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| List every remaining obligation under the exact frozen quantifiers | `PGGaoRemainingInputs` | Contains only `D≤|A|` and `PGGaoExternalUpperInputs`; lower witness and oddness are no longer fields. |
| Close the fully quantified frozen theorem from those obligations | `pgGaoV1Statement_of_remainingInputs` | Universe-matched to `PGGaoV1Statement`; mechanically checked. The residual interface is not proved. |

## Finite Davenport cardinality bound (M31; supersedes M29--M30 residual descriptions)

Natural-language anchor: `frozen_obligation_pg-v1.md:30`, which requires
`D(A)≤|A|`. The Lean proof is stronger in domain: it uses only a finite
additive group, not the p-group hypotheses.

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Among `|A|+1` prefix sums, two are equal | `hasNonemptyZeroSum_of_length_natCard`; `finitePrefixSum` | Finite pigeonhole is proved from `Fintype.card_le_of_injective`; no external combinatorial theorem parameter. Checked. |
| Equal prefixes select a nonempty zero-sum block | `intervalSelection`; `sum_intervalSelection_eq_sum_Ico`; `hasNonemptyZeroSum_of_equal_prefixes` | The block is a `Finset (Fin s.length)` on the half-open source interval. Equal values at different positions remain different occurrences. Checked. |
| The exact ordinary Davenport value satisfies `D≤|A|` | `ordinaryDavenportConstant_le_natCard` | Contradicts the defining length-`|A|` zero-sum-free counterexample if `|A|<D`. This relies on the frozen exact definition, not a new axiom. Checked. |
| Remove the numerical residual field | `pgGaoV1_of_externalUpperInputs_and_ordinaryDavenport_of_pgroup`; `PGGaoRemainingInputs` | Both oddness and `D≤|A|` are now internal. The only residual input is `PGGaoExternalUpperInputs`; its existence is still unproved. |

## Ordinary GMO to low-reflection transport (M32)

Natural-language anchor: `A-R6/proof.md:205--216` (Section 4.1).

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Ordinary prescribed-length GMO: `|S|≥k+D-1`, `k≥|A|`, exact `k` terms, sum in `kA` | `OrdinaryGMOTargetOutput`; `OrdinaryGMOPrescribedLengthProvider` | Exact occurrence-labelled theorem interface. It is a proposition parameter, not proved or declared as an axiom. |
| Form the additive sequence of all rotation coordinates | `rotationCoordinateSequence`; `rotationSourceOccurrence` | Uses the canonical `Finset.toList` of source rotation positions. Equal coordinates are retained as separate list occurrences. |
| Pull an additive selection back to the original source | `rotationSourceOccurrence_injective`; `rotationSourceOccurrence_mem`; `LowReflectionTargetOutput.ofOrdinaryGMOTargetOutput` | Proves injectivity from nodup source positions, exact cardinality preservation, rotation membership, and coordinate-sum equality. Checked. |
| Close the `a≤1` source field from ordinary GMO | `exists_lowReflectionTargetOutput_of_ordinaryGMO`; `pgGaoUpperInputs_of_externalUpperInputs` | The checked count `2Q+D-1≤b` supplies the theorem threshold. `PGGaoExternalUpperInputs` now asks for the natural GMO provider, not an arbitrary `LowReflectionTargetOutput` for each source. |

The existence of `OrdinaryGMOPrescribedLengthProvider` is still
`LEAN_CONDITIONAL`; M32 checks only the statement-faithful specialization and
occurrence transport.

## Automatic affine-hyperplane map (M44)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| A linearly spanning finite support with proper affine direction has codimension-one direction | `OccurrenceReservoir.exists_affineHyperplaneGeometry_of_linearSpan_eq_top` | Chooses `α` from the support, proves `α ∉ W`, `finrank W + 1 = finrank V`, and `x - α ∈ W` for every support point. Checked. |
| Form the quotient fibre and exact exceptional labels without caller data | `OccurrenceReservoir.exists_affineHyperplaneCertificate_of_linearSpan_eq_top` | Uses `W.mkQ`, `β = mkQ α`, and a constructed `E` with `ω ∈ E ↔ mkQ (C ω) ≠ β`; then invokes the M42 exact equivalence. Checked. |
| Complete the affine dichotomy | `OccurrenceReservoir.fullExchange_or_smallAffineHyperplaneCertificate` | Checked in M46: full affine span or `E.card≥q-1` yields full exact exchange; otherwise the canonical certificate has `E.card≤q-2`. |

## Variable-direction quotient coverage (M45-A)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Preserve repeated quotient increments as separate labels | `labelledSubsetSums`; `labelledSubsetSums_insert` | The powerset is taken on the index set, not the value support. Checked. |
| `q-1` nonzero cross-pair increments cover the prime cyclic quotient | `exists_labelled_subset_sum_eq_of_nonzero` | Finite-set induction plus `ZMod.cauchy_davenport`; every quotient target has an actual labelled toggle subset. Checked. |
| Combine quotient toggles with kernel toggles and fillers | `OccurrenceReservoir.exists_fixedCardinality_sum_of_kernel_and_crossPairs` | Checked: quotient selection, kernel correction, endpoint-disjoint fillers, exact cardinality, and exact target sum. |

## Complete large-exceptional affine branch (M45-B/M46)

| Natural-language step | Lean declaration | Fidelity / coverage |
|---|---|---|
| Leave a heavy value outside the kernel matching | `OccurrenceReservoir.exists_kernel_reservoir_with_unusedHeavyValue` | Strict half-cardinality produces two unused support vertices; one is retained and proved absent from every occurrence-reservoir endpoint. Checked. |
| Pair `q-1` exceptional labels with disjoint copies of the unused heavy value | `OccurrenceReservoir.exists_disjoint_quotientCrossPairReservoir` | All labels are globally distinct, kernel-disjoint, and every quotient increment is nonzero. Checked occurrence-wise. |
| Close the `E.card≥q-1` source-shaped branch | `OccurrenceReservoir.exists_fixedCardinality_sum_of_largeExceptionalSet` | Internally constructs both reservoirs, performs quotient and kernel correction, and supplies exact-cardinality fillers. Checked. |
| Split the raw heavy-support hypotheses | `OccurrenceReservoir.fullExchange_or_smallAffineHyperplaneCertificate` | Returns full exact exchange in both full-affine and large-exceptional cases; otherwise returns the exact labelled certificate with `E.card≤q-2`. `LEAN_FULL` for the affine-dichotomy statement. |
