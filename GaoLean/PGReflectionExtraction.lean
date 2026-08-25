import GaoLean.PGRotationExtraction
import GaoLean.PGReflectionChannel

/-!
# Occurrence-labelled extraction for the reflection-containing quotient channel

This module formalizes the internal extraction in A-R6, Section 5.2,
equations (5.6)--(5.7).  Rather than recording a procedural order of greedy
removals, it chooses a maximum-cardinality quotient-product-one selection
which contains a reflection.  Its labelled complement is product-one-free.
These are exactly the postconditions used after the source's greedy step.

It also lifts a quotient ordering back to the original labelled multiset,
proves that its number of reflections is positive and even, and identifies
the lifted product coordinate as a defect in `K`.  No GJM, GMO, or Davenport
identity is asserted here.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The source carrier `T`: all reflections together with all rotations
outside `K`. -/
noncomputable def reflectionQuotientCarrier
    (s : List (Group A)) (K : AddSubgroup A) : Selection s :=
  reflectionOccurrences s ∪ rotationOccurrencesOutside s K

theorem reflectionQuotientCarrier_eq_quotientCarrierOccurrences
    (s : List (Group A)) (K : AddSubgroup A) :
    reflectionQuotientCarrier s K = quotientCarrierOccurrences s K := by
  classical
  ext i
  rw [mem_quotientCarrierOccurrences_iff_reflection_or_rotation_outside]
  simp only [reflectionQuotientCarrier, Finset.mem_union]
  constructor
  · rintro (hi | hi)
    · exact Or.inl (by simpa [reflectionOccurrences] using hi)
    · exact Or.inr ((mem_rotationOccurrencesOutside_iff s K i).1 hi).2
  · rintro (hi | hi)
    · exact Or.inl (by simpa [reflectionOccurrences] using hi)
    · by_cases hrot : IsRotation (occurrenceValue s i)
      · exact Or.inr ((mem_rotationOccurrencesOutside_iff s K i).2
          ⟨hrot, hi⟩)
      · exact Or.inl (by simpa [reflectionOccurrences] using hrot)

/-- Quotient product-one, still indexed by original source occurrences. -/
def IsQuotientProductOneSelection
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s) : Prop :=
  HasProductOneOrdering ((selectedMultiset s I).map (quotientMap K))

/-- Concatenating two quotient orderings preserves all source labels and
multiplicities. -/
theorem IsQuotientProductOneSelection.union
    {s : List (Group A)} {K : AddSubgroup A} {I J : Selection s}
    (hdis : Disjoint I J)
    (hI : IsQuotientProductOneSelection s K I)
    (hJ : IsQuotientProductOneSelection s K J) :
    IsQuotientProductOneSelection s K (I ∪ J) := by
  rcases hI with ⟨wordI, hwordI, hprodI⟩
  rcases hJ with ⟨wordJ, hwordJ, hprodJ⟩
  refine ⟨wordI ++ wordJ, ?_, ?_⟩
  · calc
      Multiset.ofList (wordI ++ wordJ) =
          Multiset.ofList wordI + Multiset.ofList wordJ := by simp
      _ = (selectedMultiset s I).map (quotientMap K) +
          (selectedMultiset s J).map (quotientMap K) := by
            rw [hwordI, hwordJ]
      _ = (selectedMultiset s (I ∪ J)).map (quotientMap K) := by
            rw [selectedMultiset_union_of_disjoint s I J hdis,
              Multiset.map_add]
  · simp [hprodI, hprodJ]

/-- The exact labelled partition needed by the reflection-containing channel. -/
structure ReflectionQuotientExtraction
    (s : List (Group A)) (K : AddSubgroup A) where
  U : Selection s
  R : Selection s
  U_subset : U ⊆ reflectionQuotientCarrier s K
  R_subset : R ⊆ reflectionQuotientCarrier s K
  disjoint : Disjoint U R
  partition : U ∪ R = reflectionQuotientCarrier s K
  U_productOne : IsQuotientProductOneSelection s K U
  U_hasReflection : ∃ i ∈ U, ¬IsRotation (occurrenceValue s i)
  R_free : IsQuotientProductOneFreeSelection s K R

/-- A maximum-cardinality reflection-containing quotient-product-one
selection has product-one-free complement.  This is the precise
postcondition of the source's greedy accumulation of disjoint blocks. -/
theorem exists_reflectionQuotientExtraction
    (s : List (Group A)) (K : AddSubgroup A)
    (hchannel : HasReflectionContainingQuotientProductOne s K) :
    Nonempty (ReflectionQuotientExtraction s K) := by
  classical
  let T := reflectionQuotientCarrier s K
  let candidates : Finset (Selection s) :=
    T.powerset.filter fun I =>
      IsQuotientProductOneSelection s K I ∧
        ∃ i ∈ I, ¬IsRotation (occurrenceValue s i)
  rcases hchannel with ⟨I0, hI0carrier, hI0refl, hI0prod⟩
  have hI0T : I0 ⊆ T := by
    simpa [T, reflectionQuotientCarrier_eq_quotientCarrierOccurrences]
      using hI0carrier
  have hI0cand : I0 ∈ candidates := by
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_powerset.mpr hI0T, hI0prod, hI0refl⟩
  have hcandidates : candidates.Nonempty := ⟨I0, hI0cand⟩
  obtain ⟨U, hUcand, hmax⟩ :=
    Finset.exists_max_image candidates Finset.card hcandidates
  have hUsub : U ⊆ T :=
    Finset.mem_powerset.mp (Finset.mem_filter.mp hUcand).1
  have hUprod : IsQuotientProductOneSelection s K U :=
    (Finset.mem_filter.mp hUcand).2.1
  have hUrefl : ∃ i ∈ U, ¬IsRotation (occurrenceValue s i) :=
    (Finset.mem_filter.mp hUcand).2.2
  let R : Selection s := T \ U
  have hRsub : R ⊆ T := Finset.sdiff_subset
  have hdis : Disjoint U R := Finset.disjoint_sdiff
  have hpartition : U ∪ R = T := Finset.union_sdiff_of_subset hUsub
  have hRfree : IsQuotientProductOneFreeSelection s K R := by
    intro J hJsub hJne hJprod
    have hUJ : Disjoint U J := by
      rw [Finset.disjoint_left]
      intro i hiU hiJ
      exact (Finset.mem_sdiff.mp (hJsub hiJ)).2 hiU
    have hJsubT : J ⊆ T := by
      exact fun i hi => (Finset.mem_sdiff.mp (hJsub hi)).1
    have hunionSub : U ∪ J ⊆ T := Finset.union_subset hUsub hJsubT
    have hunionProd : IsQuotientProductOneSelection s K (U ∪ J) :=
      hUprod.union hUJ hJprod
    have hunionRefl : ∃ i ∈ U ∪ J,
        ¬IsRotation (occurrenceValue s i) := by
      rcases hUrefl with ⟨i, hiU, href⟩
      exact ⟨i, Finset.mem_union_left J hiU, href⟩
    have hunionCand : U ∪ J ∈ candidates := by
      exact Finset.mem_filter.mpr
        ⟨Finset.mem_powerset.mpr hunionSub, hunionProd, hunionRefl⟩
    have hle : (U ∪ J).card ≤ U.card := hmax (U ∪ J) hunionCand
    have hcard := Finset.card_union_of_disjoint hUJ
    have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
    omega
  exact ⟨{
    U := U
    R := R
    U_subset := by simpa [T] using hUsub
    R_subset := by simpa [T] using hRsub
    disjoint := hdis
    partition := by simpa [T] using hpartition
    U_productOne := hUprod
    U_hasReflection := hUrefl
    R_free := hRfree
  }⟩

theorem ReflectionQuotientExtraction.card_partition
    {s : List (Group A)} {K : AddSubgroup A}
    (h : ReflectionQuotientExtraction s K) :
    h.U.card + h.R.card = (reflectionQuotientCarrier s K).card := by
  calc
    h.U.card + h.R.card = (h.U ∪ h.R).card :=
      (Finset.card_union_of_disjoint h.disjoint).symm
    _ = (reflectionQuotientCarrier s K).card :=
      congrArg Finset.card h.partition

/-- Occurrence-sensitive number of reflections in a labelled selection. -/
noncomputable def selectedReflectionCount
    (s : List (Group A)) (I : Selection s) : ℕ := by
  classical
  exact (selectedMultiset s I).countP fun g => ¬IsRotation g

/-- Reflection multiplicity in an arbitrary multiset. -/
noncomputable def reflectionMultiplicity (S : Multiset (Group A)) : ℕ := by
  classical
  exact S.countP fun g => ¬IsRotation g

private theorem zmod_two_eq_zero_or_one (x : ZMod 2) : x = 0 ∨ x = 1 := by
  fin_cases x
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- The product of the `C₂` coordinates records reflection parity. -/
theorem multiset_right_prod_eq_reflectionParity
    (S : Multiset (Group A)) :
    (S.map SemidirectProduct.right).prod =
      Multiplicative.ofAdd
        ((reflectionMultiplicity S : ℕ) : ZMod 2) := by
  classical
  induction S using Multiset.induction_on with
  | empty => simp [reflectionMultiplicity]
  | @cons g S ih =>
      by_cases hg : IsRotation g
      · have hright : g.right = 1 := hg
        rw [Multiset.map_cons, Multiset.prod_cons, hright, one_mul]
        rw [reflectionMultiplicity, Multiset.countP_cons_of_neg S]
        · simpa [reflectionMultiplicity] using ih
        · exact not_not.mpr hg
      · have hrightAdd : Multiplicative.toAdd g.right = (1 : ZMod 2) := by
          rcases zmod_two_eq_zero_or_one (Multiplicative.toAdd g.right) with hzero | hone
          · exfalso
            apply hg
            change Multiplicative.toAdd g.right = 0
            exact hzero
          · exact hone
        have hright : g.right = Multiplicative.ofAdd (1 : ZMod 2) := by
          change Multiplicative.toAdd g.right = 1
          exact hrightAdd
        rw [Multiset.map_cons, Multiset.prod_cons, hright]
        rw [reflectionMultiplicity, Multiset.countP_cons_of_pos S hg]
        change Multiplicative.ofAdd (1 : ZMod 2) *
            (S.map SemidirectProduct.right).prod =
          Multiplicative.ofAdd
            (((reflectionMultiplicity S + 1 : ℕ) : ZMod 2))
        rw [ih]
        simp [mul_comm]

/-- Every literal product-one word in a generalized dihedral group has an
even number of reflections. -/
theorem even_reflectionCount_of_word_prod_one
    (word : List (Group A)) (hprod : word.prod = 1) :
    Even (reflectionMultiplicity (Multiset.ofList word)) := by
  classical
  have hright : (word.map SemidirectProduct.right).prod = 1 := by
    calc
      (word.map SemidirectProduct.right).prod =
          SemidirectProduct.rightHom word.prod :=
        (map_list_prod SemidirectProduct.rightHom word).symm
      _ = 1 := by rw [hprod]; simp
  have hparity := multiset_right_prod_eq_reflectionParity
    (A := A) (Multiset.ofList word)
  have hcast :
      ((reflectionMultiplicity (Multiset.ofList word) : ℕ) : ZMod 2) = 0 := by
    change Multiplicative.ofAdd
        ((reflectionMultiplicity (Multiset.ofList word) : ℕ) : ZMod 2) = 1
    exact hparity.symm.trans hright
  exact ZMod.natCast_eq_zero_iff_even.mp hcast

/-- An ordering in the quotient can be lifted to an ordering of the original
selected multiset, even when distinct occurrences have equal quotient image. -/
structure LiftedQuotientOrdering
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s) where
  word : List (Group A)
  word_multiset : Multiset.ofList word = selectedMultiset s I
  quotient_product : (word.map (quotientMap K)).prod = 1

theorem exists_liftedQuotientOrdering
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s)
    (hprod : IsQuotientProductOneSelection s K I) :
    Nonempty (LiftedQuotientOrdering s K I) := by
  rcases hprod with ⟨qword, hqword, hqprod⟩
  let source : List (Group A) := (selectedMultiset s I).toList
  have hperm : qword.Perm (source.map (quotientMap K)) := by
    have hmult : Multiset.ofList qword =
        Multiset.ofList (source.map (quotientMap K)) := by
      calc
        Multiset.ofList qword =
            (selectedMultiset s I).map (quotientMap K) := hqword
        _ = Multiset.ofList (source.map (quotientMap K)) := by
          change (selectedMultiset s I).map (quotientMap K) =
            (Multiset.ofList source).map (quotientMap K)
          exact congrArg (Multiset.map (quotientMap K))
            (Multiset.coe_toList (selectedMultiset s I)).symm
    exact Multiset.coe_eq_coe.mp hmult
  have hcomp : Relation.Comp
      (fun q : List (Group (A ⧸ K)) => fun w : List (Group A) =>
        q = w.map (quotientMap K))
      List.Perm qword source := by
    rw [List.eq_map_comp_perm]
    exact hperm
  rcases hcomp with ⟨word, hmap, hwordPerm⟩
  refine ⟨{
    word := word
    word_multiset := ?_
    quotient_product := ?_
  }⟩
  · calc
      Multiset.ofList word = Multiset.ofList source :=
        Multiset.coe_eq_coe.mpr hwordPerm
      _ = selectedMultiset s I := by simp [source]
  · rw [← hmap]
    exact hqprod

/-- The lifted literal product is a rotation whose coordinate lies in `K`;
this coordinate is exactly the source's defect `z`. -/
theorem LiftedQuotientOrdering.product_isRotation_and_coordinate_mem
    {s : List (Group A)} {K : AddSubgroup A} {I : Selection s}
    (h : LiftedQuotientOrdering s K I) :
    IsRotation h.word.prod ∧ coordinate h.word.prod ∈ K := by
  apply (quotientMap_eq_one_iff K h.word.prod).1
  calc
    quotientMap K h.word.prod = (h.word.map (quotientMap K)).prod :=
      map_list_prod (quotientMap K) h.word
    _ = 1 := h.quotient_product

/-- Quotient product-one already forces even reflection multiplicity in the
original labelled selection. -/
theorem even_selectedReflectionCount_of_quotientProductOne
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s)
    (hprod : IsQuotientProductOneSelection s K I) :
    Even (selectedReflectionCount s I) := by
  classical
  rcases exists_liftedQuotientOrdering s K I hprod with ⟨hword⟩
  have hevenQ := even_reflectionCount_of_word_prod_one
    (A := A ⧸ K) (hword.word.map (quotientMap K))
      hword.quotient_product
  have hcountMap :
      reflectionMultiplicity
          (Multiset.ofList (hword.word.map (quotientMap K))) =
        reflectionMultiplicity (Multiset.ofList hword.word) := by
    unfold reflectionMultiplicity
    change ((Multiset.ofList hword.word).map (quotientMap K)).countP
        (fun g => ¬IsRotation g) =
      (Multiset.ofList hword.word).countP (fun g => ¬IsRotation g)
    rw [Multiset.countP_map, Multiset.countP_eq_card_filter]
    apply congrArg Multiset.card
    apply Multiset.filter_congr
    intro g _hg
    exact not_congr (quotientMap_isRotation_iff K g)
  have hcountWord :
      reflectionMultiplicity (Multiset.ofList hword.word) =
        selectedReflectionCount s I := by
    unfold reflectionMultiplicity selectedReflectionCount
    exact congrArg (fun M : Multiset (Group A) =>
      M.countP fun g => ¬IsRotation g) hword.word_multiset
  rw [hcountMap, hcountWord] at hevenQ
  exact hevenQ

/-- A reflection-containing quotient block has a positive even number of
reflection occurrences, as required immediately after (5.7). -/
theorem positive_even_selectedReflectionCount
    (s : List (Group A)) (K : AddSubgroup A) (I : Selection s)
    (hprod : IsQuotientProductOneSelection s K I)
    (href : ∃ i ∈ I, ¬IsRotation (occurrenceValue s i)) :
    0 < selectedReflectionCount s I ∧ Even (selectedReflectionCount s I) := by
  classical
  refine ⟨?_, even_selectedReflectionCount_of_quotientProductOne s K I hprod⟩
  rcases href with ⟨i, hi, hrefi⟩
  apply Multiset.countP_pos.mpr
  refine ⟨occurrenceValue s i, ?_, hrefi⟩
  rw [selectedMultiset]
  exact Multiset.mem_map.mpr ⟨i, hi, rfl⟩

/-- GJM's small-Davenport conclusion is kept as an explicit provider. -/
theorem ReflectionQuotientExtraction.free_remainder_bound
    {s : List (Group A)} {K : AddSubgroup A} {Dq : ℕ}
    (h : ReflectionQuotientExtraction s K)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq) :
    h.R.card ≤ Dq :=
  hsmall s h.R h.R_free

/-- Source inequality (5.5), isolated from all sequence bookkeeping. -/
theorem reflection_target_base_ge_card_subgroup
    (Q D : ℕ) (K : AddSubgroup A)
    (hQ : Q = Nat.card A) (hDQ : D ≤ Q)
    (hKpos : ⊥ < K) (hKtop : K < ⊤) :
    Nat.card K ≤ 2 * Q - D - Nat.card (A ⧸ K) + 2 := by
  have hI : 2 ≤ Nat.card (A ⧸ K) :=
    two_le_natCard_quotient_of_lt_top K hKtop
  have hKcard : 2 ≤ Nat.card K := by
    have hlt : Nat.card (⊥ : AddSubgroup A) < Nat.card K :=
      natCard_lt_of_addSubgroup_lt hKpos
    have hlt' : 1 < Nat.card K := by simpa using hlt
    omega
  have hfactor : Q = Nat.card (A ⧸ K) * Nat.card K := by
    calc
      Q = Nat.card A := hQ
      _ = Nat.card (A ⧸ K) * Nat.card K :=
        K.card_eq_card_quotient_mul_card_addSubgroup
  have hsum := quotient_factor_sum_le_product_add_two
    (Nat.card (A ⧸ K)) (Nat.card K) hI hKcard
  omega

/-- All internally extractable data before the signed GMO call in the
reflection-containing channel.  The structure retains the literal lifted
ordering and defect, rather than replacing them by an unlabelled value set. -/
structure ReflectionChannelPreGMOData
    (s : List (Group A)) (Q D a b : ℕ) (K : AddSubgroup A) where
  M : ℕ
  c : ℕ
  tau : ℕ
  m : ℕ
  z : A
  C : Selection s
  B : Selection s
  U : Selection s
  R : Selection s
  C_eq : C = rotationOccurrencesIn s K
  B_eq : B = rotationOccurrencesOutside s K
  Ccard : C.card = M
  Bcard : B.card = c
  U_subset : U ⊆ reflectionQuotientCarrier s K
  R_subset : R ⊆ reflectionQuotientCarrier s K
  UR_disjoint : Disjoint U R
  T_partition : U ∪ R = reflectionQuotientCarrier s K
  U_productOne : IsQuotientProductOneSelection s K U
  U_hasReflection : ∃ i ∈ U, ¬IsRotation (occurrenceValue s i)
  R_free : IsQuotientProductOneFreeSelection s K R
  R_bound : R.card ≤ D
  lifted : LiftedQuotientOrdering s K U
  z_eq : z = coordinate lifted.word.prod
  z_mem : z ∈ K
  U_reflectionCount :
    0 < selectedReflectionCount s U ∧ Even (selectedReflectionCount s U)
  CU_disjoint : Disjoint C U
  allC : ∀ i ∈ C, IsRotation (occurrenceValue s i)
  tau_eq : tau = D - R.card
  m_eq : m = M - tau
  tau_le_D : tau ≤ D
  tau_le_M : tau ≤ M
  exactSize : U.card + m = 2 * Q

theorem ReflectionChannelPreGMOData.defect_mem
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K) : h.z ∈ K :=
  h.z_mem

/-- Equation (5.7) from the explicit Davenport convolution identity and the
GJM remainder bound. -/
theorem ReflectionChannelPreGMOData.tau_ge_of_davenport_split
    {s : List (Group A)} {Q D a b Dk Dq : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K)
    (hsplit : D + 1 = Dk + Dq) (hRsmall : h.R.card ≤ Dq) :
    Dk - 1 ≤ h.tau := by
  rw [h.tau_eq]
  omega

/-- The GMO threshold `M ≥ m + (Dpm-1)` follows once the external
`Dpm≤Dk` comparison is supplied. -/
theorem ReflectionChannelPreGMOData.signed_reservoir_threshold
    {s : List (Group A)} {Q D a b Dpm : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K)
    (htau : Dpm - 1 ≤ h.tau) :
    h.m + (Dpm - 1) ≤ h.M := by
  rw [h.m_eq]
  calc
    h.M - h.tau + (Dpm - 1) ≤ h.M - h.tau + h.tau :=
      Nat.add_le_add_left htau _
    _ = h.M := Nat.sub_add_cancel h.tau_le_M

/-- The lower bound in (5.8), including its final `|K|` consequence. -/
theorem ReflectionChannelPreGMOData.target_ge_card_subgroup
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K)
    (hQ : Q = Nat.card A) (hDQ : D ≤ Q)
    (hKpos : ⊥ < K) (hKtop : K < ⊤)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (haD : a ≤ D) (htotal : a + b = 2 * Q + D) :
    Nat.card K ≤ h.m := by
  have hcapM : b - Nat.card (A ⧸ K) + 2 ≤ h.M := by
    rw [← h.Ccard, h.C_eq]
    exact hcapacity
  have hbase : Nat.card K ≤
      2 * Q - D - Nat.card (A ⧸ K) + 2 :=
    reflection_target_base_ge_card_subgroup Q D K hQ hDQ hKpos hKtop
  have hquotientLeA : Nat.card (A ⧸ K) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos K.card_quotient_dvd_card
  have hquotientLeQ : Nat.card (A ⧸ K) ≤ Q := by
    simpa [hQ] using hquotientLeA
  rw [h.m_eq]
  apply hbase.trans
  apply Nat.le_sub_of_add_le
  calc
    (2 * Q - D - Nat.card (A ⧸ K) + 2) + h.tau ≤
        (2 * Q - D - Nat.card (A ⧸ K) + 2) + D :=
      Nat.add_le_add_left h.tau_le_D _
    _ ≤ b - Nat.card (A ⧸ K) + 2 := by omega
    _ ≤ h.M := hcapM

/-- Construct (5.6)--(5.9) from maximum labelled extraction, the explicit
quotient small-Davenport provider, and the source's finite count hypotheses. -/
theorem exists_reflectionChannelPreGMOData
    (s : List (Group A)) (Q D a b Dq : ℕ) (K : AddSubgroup A)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (hQ : Q = Nat.card A)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq)
    (hDqD : Dq ≤ D)
    (hchannel : ¬QuotientNoReflection s K) :
    Nonempty (ReflectionChannelPreGMOData s Q D a b K) := by
  classical
  have hchannel' : HasReflectionContainingQuotientProductOne s K :=
    not_not.mp hchannel
  rcases exists_reflectionQuotientExtraction s K hchannel' with ⟨hex⟩
  rcases exists_liftedQuotientOrdering s K hex.U hex.U_productOne with
    ⟨hlift⟩
  let C := rotationOccurrencesIn s K
  let B := rotationOccurrencesOutside s K
  let M := C.card
  let c := B.card
  let tau := D - hex.R.card
  let m := M - tau
  let z := coordinate hlift.word.prod
  have hRleDq : hex.R.card ≤ Dq := hex.free_remainder_bound hsmall
  have hRleD : hex.R.card ≤ D := hRleDq.trans hDqD
  have hCplusB : C.card + B.card = b := by
    simpa [C, B, hrot] using card_rotationOccurrencesIn_add_outside s K
  have hreflBdis : Disjoint (reflectionOccurrences s) B := by
    rw [Finset.disjoint_left]
    intro i hiRefl hiB
    have hnrot : ¬IsRotation (occurrenceValue s i) := by
      simpa [reflectionOccurrences] using hiRefl
    exact hnrot ((mem_rotationOccurrencesOutside_iff s K i).1 hiB).1
  have hTcard : (reflectionQuotientCarrier s K).card = a + c := by
    calc
      (reflectionQuotientCarrier s K).card =
          (reflectionOccurrences s ∪ B).card := by rfl
      _ = (reflectionOccurrences s).card + B.card :=
        Finset.card_union_of_disjoint hreflBdis
      _ = a + c := by rw [href]
  have hURcard : hex.U.card + hex.R.card = a + c := by
    rw [hex.card_partition, hTcard]
  have hquotientLeA : Nat.card (A ⧸ K) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos K.card_quotient_dvd_card
  have hquotientLeQ : Nat.card (A ⧸ K) ≤ Q := by
    simpa [hQ] using hquotientLeA
  have hDb : D ≤ b - Q + 2 := by omega
  have hDleM : D ≤ M := by
    have hcapM : b - Nat.card (A ⧸ K) + 2 ≤ M := by
      simpa [C, M] using hcapacity
    omega
  have htauD : tau ≤ D := by simp [tau]
  have htauM : tau ≤ M := htauD.trans hDleM
  have hexact : hex.U.card + m = 2 * Q := by
    dsimp only [m, tau, M, c] at hURcard hCplusB ⊢
    omega
  have hzdata := hlift.product_isRotation_and_coordinate_mem
  have hCU : Disjoint C hex.U := by
    rw [Finset.disjoint_left]
    intro i hiC hiU
    have hiC' : IsRotation (occurrenceValue s i) ∧
        coordinate (occurrenceValue s i) ∈ K := by
      simpa [C, rotationOccurrencesIn] using hiC
    have hiCarrier : i ∈ quotientCarrierOccurrences s K := by
      rw [← reflectionQuotientCarrier_eq_quotientCarrierOccurrences]
      exact hex.U_subset hiU
    have hne := (mem_quotientCarrierOccurrences_iff s K i).1 hiCarrier
    apply hne
    exact (quotientMap_eq_one_iff K _).2 hiC'
  refine ⟨{
    M := M
    c := c
    tau := tau
    m := m
    z := z
    C := C
    B := B
    U := hex.U
    R := hex.R
    C_eq := rfl
    B_eq := rfl
    Ccard := rfl
    Bcard := rfl
    U_subset := hex.U_subset
    R_subset := hex.R_subset
    UR_disjoint := hex.disjoint
    T_partition := hex.partition
    U_productOne := hex.U_productOne
    U_hasReflection := hex.U_hasReflection
    R_free := hex.R_free
    R_bound := hRleD
    lifted := hlift
    z_eq := rfl
    z_mem := hzdata.2
    U_reflectionCount := positive_even_selectedReflectionCount
      s K hex.U hex.U_productOne hex.U_hasReflection
    CU_disjoint := hCU
    allC := by
      intro i hi
      have hi' : IsRotation (occurrenceValue s i) ∧
          coordinate (occurrenceValue s i) ∈ K := by
        simpa [C, rotationOccurrencesIn] using hi
      exact hi'.1
    tau_eq := rfl
    m_eq := rfl
    tau_le_D := htauD
    tau_le_M := htauM
    exactSize := hexact
  }⟩

/-- Exact full-branch certificate after the external signed GMO theorem and
the ordering/interleaving interface have been applied.  Unlike the older
`ReflectionChannelFullOutput`, its selected block is forced to be the
extracted `U` plus exactly `m` occurrences from the actual reservoir `C`. -/
structure ReflectionChannelExtractedFullOutput
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K) where
  Dsel : Selection s
  Dsel_subset : Dsel ⊆ h.C
  Dsel_card : Dsel.card = h.m
  assignment : BalancedSignedAssignment
    (selectedMultiset s (h.U ∪ Dsel))

def ReflectionChannelExtractedFullOutput.toFullOutput
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    {h : ReflectionChannelPreGMOData s Q D a b K}
    (hout : ReflectionChannelExtractedFullOutput h) :
    ReflectionChannelFullOutput s Q := by
  have hdis : Disjoint h.U hout.Dsel :=
    h.CU_disjoint.symm.mono_right hout.Dsel_subset
  refine {
    selected := h.U ∪ hout.Dsel
    card_selected := ?_
    assignment := hout.assignment
  }
  calc
    (h.U ∪ hout.Dsel).card = h.U.card + hout.Dsel.card :=
      Finset.card_union_of_disjoint hdis
    _ = h.U.card + h.m := by rw [hout.Dsel_card]
    _ = 2 * Q := h.exactSize

/-- Exact external boundary for the signed GMO call.  The full branch is tied
to `U`, `C`, and `m`; the non-full branch is the source's weighted-coset
output on the unchanged reservoir `C`. -/
def ReflectionChannelExtractedAlternative
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K) : Prop :=
  Nonempty (ReflectionChannelExtractedFullOutput h) ∨
  (∃ (H : AddSubgroup A), H < K ∧
    ∃ X : Selection s,
      X ⊆ h.C ∧
      h.M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ X.card ∧
      ∀ i ∈ X, ∃ β : A,
        coordinate (occurrenceValue s i) - β ∈ H ∧
        -coordinate (occurrenceValue s i) - β ∈ H)

def ReflectionChannelPreGMOData.toPrepared
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K)
    (hAlt : ReflectionChannelExtractedAlternative h) :
    ReflectionChannelPreparedData s Q K where
  M := h.M
  C := h.C
  C_eq := h.C_eq
  Ccard := h.Ccard
  allC := h.allC
  alternative := by
    rcases hAlt with hfull | hnonfull
    · exact Or.inl ⟨hfull.some.toFullOutput⟩
    · exact Or.inr hnonfull

/-- The only remaining reflection-channel input at this layer: signed GMO
plus its exact ordering interface, quantified over mechanically extracted
data.  This is a proposition parameter, not an axiom or a proved theorem. -/
def ReflectionChannelGMOProvider
    (s : List (Group A)) (Q D a b : ℕ) (K : AddSubgroup A) : Prop :=
  ∀ h : ReflectionChannelPreGMOData s Q D a b K,
    ReflectionChannelExtractedAlternative h

/-- Replace the former unrestricted reflection preparation assumption by the
maximum extraction, GJM remainder bound, exact arithmetic, and the narrow
external signed-GMO provider. -/
theorem reflectionChannelPreparation_of_extraction
    (s : List (Group A)) (Q D a b Dq : ℕ) (K : AddSubgroup A)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (hQ : Q = Nat.card A)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq)
    (hDqD : Dq ≤ D)
    (hchannel : ¬QuotientNoReflection s K)
    (hGMO : ReflectionChannelGMOProvider s Q D a b K) :
    ReflectionChannelPreparation s Q K := by
  rcases exists_reflectionChannelPreGMOData
      s Q D a b Dq K href hrot htotal hDQ haD hQ hcapacity
      hsmall hDqD hchannel with ⟨hdata⟩
  exact ⟨hdata.toPrepared (hGMO hdata)⟩

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.reflectionQuotientCarrier_eq_quotientCarrierOccurrences
#print axioms GaoLean.ConcreteGDihedral.exists_reflectionQuotientExtraction
#print axioms GaoLean.ConcreteGDihedral.even_reflectionCount_of_word_prod_one
#print axioms GaoLean.ConcreteGDihedral.exists_liftedQuotientOrdering
#print axioms GaoLean.ConcreteGDihedral.LiftedQuotientOrdering.product_isRotation_and_coordinate_mem
#print axioms GaoLean.ConcreteGDihedral.positive_even_selectedReflectionCount
#print axioms GaoLean.ConcreteGDihedral.ReflectionQuotientExtraction.free_remainder_bound
#print axioms GaoLean.ConcreteGDihedral.reflection_target_base_ge_card_subgroup
#print axioms GaoLean.ConcreteGDihedral.exists_reflectionChannelPreGMOData
#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelPreGMOData.tau_ge_of_davenport_split
#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelPreGMOData.signed_reservoir_threshold
#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelPreGMOData.target_ge_card_subgroup
#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelExtractedFullOutput.toFullOutput
#print axioms GaoLean.ConcreteGDihedral.reflectionChannelPreparation_of_extraction
