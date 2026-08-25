import GaoLean.PGGuard

/-!
# PG-O3 zero-layer padding

The zero-layer arguments first build a disjoint product-one core and then pad
it with unused identity rotations to exact cardinality `2Q`.  This file closes
the occurrence-sensitive union and padding part of that argument.  It does not
assert the preceding greedy core-extraction lemma.
-/

namespace GaoLean

section SelectionUnion

variable {G : Type*} [Monoid G]

/-- Disjoint labelled selections become multiset addition after forgetting
their labels.  Equal values in the two selections retain both multiplicities. -/
theorem selectedMultiset_union_of_disjoint
    (s : List G) (I J : Selection s) (hdis : Disjoint I J) :
    selectedMultiset s (I ∪ J) =
      selectedMultiset s I + selectedMultiset s J := by
  have hval : (I ∪ J).1 = I.1 + J.1 := by
    rw [Finset.union_val]
    exact (Multiset.add_eq_union_iff_disjoint.mpr
      ((Finset.disjoint_val).2 hdis)).symm
  simp only [selectedMultiset, hval, Multiset.map_add]

/-- Concatenating witnesses for two disjoint occurrence selections proves
that their union is product one. -/
theorem IsProductOneSelection.union
    {s : List G} {I J : Selection s} (hdis : Disjoint I J)
    (hI : IsProductOneSelection s I) (hJ : IsProductOneSelection s J) :
    IsProductOneSelection s (I ∪ J) := by
  rcases hI with ⟨wordI, hwordI, hprodI⟩
  rcases hJ with ⟨wordJ, hwordJ, hprodJ⟩
  refine ⟨wordI ++ wordJ, ?_, ?_⟩
  · calc
      Multiset.ofList (wordI ++ wordJ) =
          Multiset.ofList wordI + Multiset.ofList wordJ := by simp
      _ = selectedMultiset s I + selectedMultiset s J := by
        rw [hwordI, hwordJ]
      _ = selectedMultiset s (I ∪ J) :=
        (selectedMultiset_union_of_disjoint s I J hdis).symm
  · simp [hprodI, hprodJ]

/-- Any labelled selection all of whose values are the group identity is
product one. -/
theorem isProductOneSelection_of_all_one
    (s : List G) (I : Selection s)
    (hone : ∀ i ∈ I, occurrenceValue s i = 1) :
    IsProductOneSelection s I := by
  let word : List G := I.toList.map (occurrenceValue s)
  refine ⟨word, ?_, ?_⟩
  · change Multiset.map (occurrenceValue s) (Multiset.ofList I.toList) =
      Multiset.map (occurrenceValue s) I.1
    exact congrArg (Multiset.map (occurrenceValue s)) (Finset.coe_toList I)
  · apply List.prod_eq_one
    intro g hg
    rcases List.mem_map.mp hg with ⟨i, hi, rfl⟩
    exact hone i (Finset.mem_toList.mp hi)

/-- The exact identity-padding operation used in both zero-layer bases. -/
theorem exists_productOne_identity_padding
    (s : List G) (P identities : Selection s) {Q m0 : ℕ}
    (hP : IsProductOneSelection s P)
    (hone : ∀ i ∈ identities, occurrenceValue s i = 1)
    (hidentities : identities.card = m0) (hdis : Disjoint P identities)
    (hlower : 2 * Q - m0 ≤ P.card) (hupper : P.card ≤ 2 * Q) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  obtain ⟨J, hJ, hPJ, hcard⟩ :=
    exists_disjoint_identity_padding P identities hidentities hdis hlower hupper
  have hJone : ∀ i ∈ J, occurrenceValue s i = 1 := by
    exact fun i hi => hone i (hJ hi)
  refine ⟨P ∪ J, hcard, ?_⟩
  exact hP.union hPJ (isProductOneSelection_of_all_one s J hJone)

/-- A labelled remainder is product-one-free when none of its nonempty
subselections admits a product-one ordering. -/
def IsProductOneFreeSelection (s : List G) (R : Selection s) : Prop :=
  ∀ I : Selection s, I ⊆ R → I.Nonempty → ¬IsProductOneSelection s I

/-- Explicit small-Davenport interface: every product-one-free labelled
selection, in every source list, has at most `D` occurrences. -/
def SmallDavenportProductOneFreeAtMost (G : Type*) [Monoid G] (D : ℕ) : Prop :=
  ∀ (s : List G) (R : Selection s),
    IsProductOneFreeSelection s R → R.card ≤ D

/-- Greedy extraction without an algorithm: choose a maximum-cardinality
product-one selection in `R`; its labelled complement is product-one-free. -/
theorem exists_productOne_core_with_free_remainder
    (s : List G) (R : Selection s) :
    ∃ P : Selection s,
      P ⊆ R ∧ IsProductOneSelection s P ∧
      IsProductOneFreeSelection s (R \ P) := by
  classical
  let candidates : Finset (Selection s) :=
    R.powerset.filter fun I => IsProductOneSelection s I
  have hemptyProd : IsProductOneSelection s ∅ :=
    isProductOneSelection_of_all_one s ∅ (by simp)
  have hcandidates : candidates.Nonempty := by
    refine ⟨∅, ?_⟩
    simp [candidates, hemptyProd]
  obtain ⟨P, hPcand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hPsub : P ⊆ R := by
    exact Finset.mem_powerset.mp (Finset.mem_filter.mp hPcand).1
  have hPprod : IsProductOneSelection s P :=
    (Finset.mem_filter.mp hPcand).2
  refine ⟨P, hPsub, hPprod, ?_⟩
  intro J hJsub hJne hJprod
  have hPJ : Disjoint P J := by
    rw [Finset.disjoint_left]
    intro i hiP hiJ
    exact (Finset.mem_sdiff.mp (hJsub hiJ)).2 hiP
  have hJsubR : J ⊆ R := by
    exact fun i hi => (Finset.mem_sdiff.mp (hJsub hi)).1
  have hunionSub : P ∪ J ⊆ R := Finset.union_subset hPsub hJsubR
  have hunionProd : IsProductOneSelection s (P ∪ J) :=
    hPprod.union hPJ hJprod
  have hunionCand : P ∪ J ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hunionSub, hunionProd⟩
  have hle : (P ∪ J).card ≤ P.card := hmax (P ∪ J) hunionCand
  have hcard := Finset.card_union_of_disjoint hPJ
  have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
  omega

/-- Under the explicit small-Davenport bound, the maximum extracted core
loses at most `D` labels to its product-one-free remainder. -/
theorem exists_large_productOne_core
    (s : List G) (R : Selection s) {D : ℕ}
    (hsmall : SmallDavenportProductOneFreeAtMost G D) :
    ∃ P : Selection s,
      P ⊆ R ∧ IsProductOneSelection s P ∧
      Disjoint P (R \ P) ∧ R.card ≤ P.card + D := by
  classical
  obtain ⟨P, hPsub, hPprod, hfree⟩ :=
    exists_productOne_core_with_free_remainder s R
  have hrem : (R \ P).card ≤ D := hsmall s (R \ P) hfree
  have hsum : (R \ P).card + P.card = R.card := by
    rw [Finset.card_sdiff_add_card, Finset.union_eq_left.mpr hPsub]
  refine ⟨P, hPsub, hPprod, Finset.disjoint_sdiff, ?_⟩
  omega

end SelectionUnion

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- In the concrete generalized-dihedral group, rotation type plus zero
coordinate characterizes the identity. -/
theorem isRotation_and_coordinate_eq_zero_iff_eq_one (g : Group A) :
    IsRotation g ∧ coordinate g = 0 ↔ g = 1 := by
  constructor
  · rintro ⟨hright, hleft⟩
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd (coordinate g) = 1
      rw [hleft]
      rfl
    · exact hright
  · rintro rfl
    simp [IsRotation, coordinate]

/-- The rotations whose coordinates lie in the zero subgroup are exactly the
identity occurrences. -/
theorem mem_rotationOccurrencesIn_bot_iff_eq_one
    (s : List (Group A)) (i : Occurrence s) :
    i ∈ rotationOccurrencesIn s ⊥ ↔ occurrenceValue s i = 1 := by
  classical
  rw [rotationOccurrencesIn]
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    AddSubgroup.mem_bot]
  exact isRotation_and_coordinate_eq_zero_iff_eq_one _

/-- All nonidentity positions, still labelled by their source occurrences. -/
noncomputable def nonidentityOccurrences
    (s : List (Group A)) : Selection s := by
  classical
  exact Finset.univ.filter fun i => occurrenceValue s i ≠ 1

theorem mem_nonidentityOccurrences_iff
    (s : List (Group A)) (i : Occurrence s) :
    i ∈ nonidentityOccurrences s ↔ occurrenceValue s i ≠ 1 := by
  classical
  simp [nonidentityOccurrences]

/-- Identity rotations and nonidentity occurrences partition all source
labels, including repeated equal values. -/
theorem card_nonidentity_add_card_identity
    (s : List (Group A)) :
    (nonidentityOccurrences s).card +
        (rotationOccurrencesIn s ⊥).card = s.length := by
  classical
  have hcomp :
      nonidentityOccurrences s = Finset.univ \ rotationOccurrencesIn s ⊥ := by
    ext i
    simp only [mem_nonidentityOccurrences_iff, Finset.mem_sdiff,
      Finset.mem_univ, true_and, mem_rotationOccurrencesIn_bot_iff_eq_one]
  rw [hcomp, Finset.card_sdiff_of_subset (Finset.subset_univ _)]
  have hidLe : (rotationOccurrencesIn s ⊥).card ≤ Finset.univ.card :=
    Finset.card_le_card (Finset.subset_univ _)
  have huniv : (Finset.univ : Selection s).card = s.length := by simp
  omega

/-- At the zero quotient, the concrete quotient carrier is exactly the set of
nonidentity occurrence labels. -/
theorem mem_quotientCarrierOccurrences_bot_iff_ne_one
    (s : List (Group A)) (i : Occurrence s) :
    i ∈ quotientCarrierOccurrences s ⊥ ↔ occurrenceValue s i ≠ 1 := by
  rw [mem_quotientCarrierOccurrences_iff]
  rw [Ne, quotientMap_eq_one_iff]
  simp only [AddSubgroup.mem_bot]
  rw [isRotation_and_coordinate_eq_zero_iff_eq_one]

/-- The zero-quotient guard forces every product-one block drawn from the
nonidentity carrier to contain rotations only. -/
theorem all_rotation_of_productOne_nonidentity_of_guard_bot
    (s : List (Group A)) (P : Selection s)
    (hPsub : P ⊆ nonidentityOccurrences s)
    (hP : IsProductOneSelection s P)
    (hguard : QuotientNoReflection s ⊥) :
    ∀ i ∈ P, IsRotation (occurrenceValue s i) := by
  intro i hiP
  by_contra hiRefl
  apply hguard
  refine ⟨P, ?_, ⟨i, hiP, hiRefl⟩, ?_⟩
  · intro j hj
    apply (mem_quotientCarrierOccurrences_bot_iff_ne_one s j).2
    exact (mem_nonidentityOccurrences_iff s j).1 (hPsub hj)
  · exact hasProductOneOrdering_map (quotientMap ⊥) hP

theorem natCard_quotient_bot :
    Nat.card (A ⧸ (⊥ : AddSubgroup A)) = Nat.card A := by
  exact Nat.card_congr QuotientAddGroup.quotientBot.toEquiv

/-- The maximum-core construction plus the small-Davenport bound supplies
all cardinal and disjointness facts needed before identity padding. -/
theorem exists_zeroCore_of_smallDavenport
    (s : List (Group A)) (Q D : ℕ)
    (hlen : s.length = 2 * Q + D)
    (hsmall : SmallDavenportProductOneFreeAtMost (Group A) D)
    (hDidentity : D ≤ (rotationOccurrencesIn s ⊥).card) :
    ∃ P : Selection s,
      P ⊆ nonidentityOccurrences s ∧
      IsProductOneSelection s P ∧
      Disjoint P (rotationOccurrencesIn s ⊥) ∧
      2 * Q - (rotationOccurrencesIn s ⊥).card ≤ P.card ∧
      P.card ≤ 2 * Q := by
  classical
  obtain ⟨P, hPsub, hP, -, hlarge⟩ :=
    exists_large_productOne_core s (nonidentityOccurrences s) hsmall
  have hdis : Disjoint P (rotationOccurrencesIn s ⊥) := by
    rw [Finset.disjoint_left]
    intro i hiP hiIdentity
    have hne : occurrenceValue s i ≠ 1 :=
      (mem_nonidentityOccurrences_iff s i).1 (hPsub hiP)
    exact hne ((mem_rotationOccurrencesIn_bot_iff_eq_one s i).1 hiIdentity)
  have hpartition := card_nonidentity_add_card_identity s
  have hPcard : P.card ≤ (nonidentityOccurrences s).card :=
    Finset.card_le_card hPsub
  refine ⟨P, hPsub, hP, hdis, ?_, ?_⟩ <;> omega

/-- All-rotation form of exact identity padding, used by `ZR_A(X,0)`. -/
theorem exists_allRotation_productOne_identity_padding
    (s : List (Group A)) (P identities : Selection s) {Q m0 : ℕ}
    (hP : IsProductOneSelection s P)
    (hProt : ∀ i ∈ P, IsRotation (occurrenceValue s i))
    (hone : ∀ i ∈ identities, occurrenceValue s i = 1)
    (hidentities : identities.card = m0) (hdis : Disjoint P identities)
    (hlower : 2 * Q - m0 ≤ P.card) (hupper : P.card ≤ 2 * Q) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  obtain ⟨J, hJ, hPJ, hcard⟩ :=
    exists_disjoint_identity_padding P identities hidentities hdis hlower hupper
  have hJone : ∀ i ∈ J, occurrenceValue s i = 1 := by
    exact fun i hi => hone i (hJ hi)
  refine ⟨P ∪ J, hcard, hP.union hPJ
    (isProductOneSelection_of_all_one s J hJone), ?_⟩
  intro i hi
  rcases Finset.mem_union.mp hi with hiP | hiJ
  · exact hProt i hiP
  · rw [hJone i hiJ]
    simp [IsRotation]

/-- The fixed-source `K=0` base is conditional only on the explicit GJM-style
small-Davenport bound and the source numerical inequalities. -/
theorem rcStatement_bot_of_smallDavenport
    (S : List (Group A)) (Q D b : ℕ)
    (hlen : S.length = 2 * Q + D)
    (hQ : Q = Nat.card A) (hDb : D ≤ b - Q + 2)
    (hsmall : SmallDavenportProductOneFreeAtMost (Group A) D) :
    RCStatement S Q b ⊥ := by
  intro hcapacity
  have hDidentity : D ≤ (rotationOccurrencesIn S ⊥).card := by
    have hthreshold : b - Q + 2 ≤ (rotationOccurrencesIn S ⊥).card := by
      simpa [natCard_quotient_bot, hQ] using hcapacity
    exact hDb.trans hthreshold
  obtain ⟨P, -, hP, hdis, hlower, hupper⟩ :=
    exists_zeroCore_of_smallDavenport S Q D hlen hsmall hDidentity
  apply exists_productOne_identity_padding S P (rotationOccurrencesIn S ⊥) hP
  · intro i hi
    exact (mem_rotationOccurrencesIn_bot_iff_eq_one S i).1 hi
  · rfl
  · exact hdis
  · exact hlower
  · exact hupper

/-- The arbitrary-sequence `K=0` base: the quotient guard turns the same
maximum product-one core into an all-rotation core before identity padding. -/
theorem concreteZRStatement_bot_of_smallDavenport
    (X : List (Group A)) (Q D a b : ℕ)
    (hQ : Q = Nat.card A) (hDb : D ≤ b - Q + 2)
    (hsmall : SmallDavenportProductOneFreeAtMost (Group A) D) :
    ConcreteZRStatement X Q D a b ⊥ := by
  intro hlen _href _hrot hcapacity hguard
  have hDidentity : D ≤ (rotationOccurrencesIn X ⊥).card := by
    have hthreshold : b - Q + 2 ≤ (rotationOccurrencesIn X ⊥).card := by
      simpa [natCard_quotient_bot, hQ] using hcapacity
    exact hDb.trans hthreshold
  obtain ⟨P, hPsub, hP, hdis, hlower, hupper⟩ :=
    exists_zeroCore_of_smallDavenport X Q D hlen hsmall hDidentity
  have hProt : ∀ i ∈ P, IsRotation (occurrenceValue X i) :=
    all_rotation_of_productOne_nonidentity_of_guard_bot X P hPsub hP hguard
  apply exists_allRotation_productOne_identity_padding X P
      (rotationOccurrencesIn X ⊥) hP hProt
  · intro i hi
    exact (mem_rotationOccurrencesIn_bot_iff_eq_one X i).1 hi
  · rfl
  · exact hdis
  · exact hlower
  · exact hupper

/-- Exact unformalized input left by the paper's greedy extraction in the
fixed-source zero-layer base.  It asks only for the pre-padding core `P`. -/
def RCZeroCoreCondition
    (S : List (Group A)) (Q b : ℕ) : Prop :=
  b - Nat.card (A ⧸ (⊥ : AddSubgroup A)) + 2 ≤
      (rotationOccurrencesIn S ⊥).card →
    ∃ P : Selection S,
      IsProductOneSelection S P ∧
      Disjoint P (rotationOccurrencesIn S ⊥) ∧
      2 * Q - (rotationOccurrencesIn S ⊥).card ≤ P.card ∧
      P.card ≤ 2 * Q

/-- Once the greedy core is supplied, the fixed-source zero-layer controller
is completely discharged by occurrence-faithful identity padding. -/
theorem rcStatement_bot_of_zeroCore
    (S : List (Group A)) (Q b : ℕ)
    (hcore : RCZeroCoreCondition S Q b) :
    RCStatement S Q b ⊥ := by
  intro hcapacity
  obtain ⟨P, hP, hdis, hlower, hupper⟩ := hcore hcapacity
  apply exists_productOne_identity_padding S P (rotationOccurrencesIn S ⊥)
      hP
  · intro i hi
    exact (mem_rotationOccurrencesIn_bot_iff_eq_one S i).1 hi
  · rfl
  · exact hdis
  · exact hlower
  · exact hupper

/-- Exact unformalized input left by the zero-layer arbitrary-sequence greedy
extraction.  In contrast with `RCZeroCoreCondition`, the extracted core must
already be rotation-only; this is where the quotient guard is used. -/
def ZRZeroCoreCondition
    (X : List (Group A)) (Q D a b : ℕ) : Prop :=
  X.length = 2 * Q + D →
  (reflectionOccurrences X).card = a →
  (rotationOccurrences X).card = b →
  b - Nat.card (A ⧸ (⊥ : AddSubgroup A)) + 2 ≤
      (rotationOccurrencesIn X ⊥).card →
  QuotientNoReflection X ⊥ →
    ∃ P : Selection X,
      IsProductOneSelection X P ∧
      (∀ i ∈ P, IsRotation (occurrenceValue X i)) ∧
      Disjoint P (rotationOccurrencesIn X ⊥) ∧
      2 * Q - (rotationOccurrencesIn X ⊥).card ≤ P.card ∧
      P.card ≤ 2 * Q

/-- Once the rotation-only greedy core is supplied, the arbitrary-sequence
zero-layer controller is completely discharged. -/
theorem concreteZRStatement_bot_of_zeroCore
    (X : List (Group A)) (Q D a b : ℕ)
    (hcore : ZRZeroCoreCondition X Q D a b) :
    ConcreteZRStatement X Q D a b ⊥ := by
  intro hlen href hrot hcapacity hguard
  obtain ⟨P, hP, hProt, hdis, hlower, hupper⟩ :=
    hcore hlen href hrot hcapacity hguard
  apply exists_allRotation_productOne_identity_padding X P
      (rotationOccurrencesIn X ⊥) hP hProt
  · intro i hi
    exact (mem_rotationOccurrencesIn_bot_iff_eq_one X i).1 hi
  · rfl
  · exact hdis
  · exact hlower
  · exact hupper

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.selectedMultiset_union_of_disjoint
#print axioms GaoLean.IsProductOneSelection.union
#print axioms GaoLean.isProductOneSelection_of_all_one
#print axioms GaoLean.exists_productOne_identity_padding
#print axioms GaoLean.ConcreteGDihedral.mem_rotationOccurrencesIn_bot_iff_eq_one
#print axioms GaoLean.exists_productOne_core_with_free_remainder
#print axioms GaoLean.exists_large_productOne_core
#print axioms GaoLean.ConcreteGDihedral.all_rotation_of_productOne_nonidentity_of_guard_bot
#print axioms GaoLean.ConcreteGDihedral.exists_zeroCore_of_smallDavenport
#print axioms GaoLean.ConcreteGDihedral.exists_allRotation_productOne_identity_padding
#print axioms GaoLean.ConcreteGDihedral.rcStatement_bot_of_zeroCore
#print axioms GaoLean.ConcreteGDihedral.concreteZRStatement_bot_of_zeroCore
#print axioms GaoLean.ConcreteGDihedral.rcStatement_bot_of_smallDavenport
#print axioms GaoLean.ConcreteGDihedral.concreteZRStatement_bot_of_smallDavenport
