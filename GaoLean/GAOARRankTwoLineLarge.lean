import GaoLean.GAOARRankTwoLine

/-!
# Rank-two large-special line completion

This module closes the `s > q` concentrated-line leaf.  It keeps the lifted
quotient-product-one word literal, inserts the signed rotations selected by
the second GMO call around its first reflection, and proves both the exact
occurrence multiset and product identity.  The non-full rank-one outcome is
forced to the zero subgroup by primality and closes through the checked
identity-padding base.
-/

namespace GaoLean.ConcreteGDihedral

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

omit [Fintype A] in
theorem exists_first_reflection_split
    (word : List (Group A))
    (href : ∃ g ∈ word, ¬IsRotation g) :
    ∃ pre r post, word = pre ++ r :: post ∧
      (∀ g ∈ pre, IsRotation g) ∧ ¬IsRotation r := by
  induction word with
  | nil => simp at href
  | cons g word ih =>
      by_cases hg : IsRotation g
      · have href' : ∃ x ∈ word, ¬IsRotation x := by
          obtain ⟨x, hx, hxr⟩ := href
          refine ⟨x, ?_, hxr⟩
          rcases List.mem_cons.mp hx with h | h
          · subst x
            exact False.elim (hxr hg)
          · exact h
        obtain ⟨pre, r, post, hsplit, hpre, hr⟩ := ih href'
        refine ⟨g :: pre, r, post, ?_, ?_, hr⟩
        · simp [hsplit]
        · intro x hx
          rcases List.mem_cons.mp hx with rfl | hx
          · exact hg
          · exact hpre x hx
      · exact ⟨[], g, word, by simp, by simp, hg⟩

theorem hasProductOneOrdering_insert_signed_rotations
    (word positive negative : List (Group A)) (z : A)
    (hpositive : ∀ g ∈ positive, IsRotation g)
    (hnegative : ∀ g ∈ negative, IsRotation g)
    (href : ∃ g ∈ word, ¬IsRotation g)
    (hwordprod : word.prod = (data A).rot z)
    (hsum : (positive.map coordinate).sum -
        (negative.map coordinate).sum + z = 0) :
    HasProductOneOrdering
      (Multiset.ofList word + Multiset.ofList positive +
        Multiset.ofList negative) := by
  obtain ⟨pre, r, post, hsplit, hpre, hr⟩ :=
    exists_first_reflection_split word href
  let out := positive ++ pre ++ r :: negative ++ post
  refine ⟨out, ?_, ?_⟩
  · dsimp [out]
    rw [hsplit]
    simp
    have hswapTail :
        (positive ++ pre ++ [r] ++ negative ++ post).Perm
          (positive ++ pre ++ [r] ++ post ++ negative) := by
      have hcomm : (negative ++ post).Perm (post ++ negative) :=
        List.perm_append_comm
      simpa [List.append_assoc] using
        hcomm.append_left (positive ++ pre ++ [r])
    have hswapHead :
        (positive ++ pre ++ [r] ++ post ++ negative).Perm
          (pre ++ [r] ++ post ++ positive ++ negative) := by
      have hcomm :
          (positive ++ (pre ++ [r] ++ post)).Perm
            ((pre ++ [r] ++ post) ++ positive) :=
        List.perm_append_comm
      simpa [List.append_assoc] using
        hcomm.append_right negative
    simpa [List.append_assoc] using hswapTail.trans hswapHead
  · have hpreprod := prod_eq_rotation_sum_of_all_rotation pre hpre
    have hpositiveprod :=
      prod_eq_rotation_sum_of_all_rotation positive hpositive
    have hnegativeprod :=
      prod_eq_rotation_sum_of_all_rotation negative hnegative
    have hrcoord := eq_refl_coordinate_of_not_isRotation r hr
    rw [hsplit] at hwordprod
    simp only [List.prod_append, List.prod_cons] at hwordprod
    rw [hpreprod, hrcoord] at hwordprod
    change (data A).rot (pre.map coordinate).sum *
      ((data A).refl (coordinate r) * post.prod) = (data A).rot z at hwordprod
    dsimp [out]
    simp only [List.prod_append, List.prod_cons]
    have hpositiveprod' : positive.prod =
        (data A).rot (positive.map coordinate).sum := by
      exact hpositiveprod
    have hpreprod' : pre.prod =
        (data A).rot (pre.map coordinate).sum := by
      exact hpreprod
    have hnegativeprod' : negative.prod =
        (data A).rot (negative.map coordinate).sum := by
      exact hnegativeprod
    rw [hpositiveprod', hpreprod', hrcoord, hnegativeprod']
    calc
      ((data A).rot (positive.map coordinate).sum *
              (data A).rot (pre.map coordinate).sum) *
            ((data A).refl (coordinate r) *
              (data A).rot (negative.map coordinate).sum) * post.prod =
          ((data A).rot (positive.map coordinate).sum *
              (data A).rot (pre.map coordinate).sum) *
            ((data A).refl (coordinate r) *
              (data A).rot (negative.map coordinate).sum) * post.prod := rfl
      _ = (data A).rot
              ((positive.map coordinate).sum +
                (pre.map coordinate).sum) *
            (data A).refl
              (coordinate r - (negative.map coordinate).sum) * post.prod := by
            rw [← (data A).rot_add, (data A).refl_mul_rot]
      _ = (data A).refl
              ((positive.map coordinate).sum +
                (pre.map coordinate).sum +
                (coordinate r - (negative.map coordinate).sum)) * post.prod := by
            rw [(data A).rot_mul_refl]
      _ = (data A).rot
              ((positive.map coordinate).sum -
                (negative.map coordinate).sum) *
            ((data A).rot (pre.map coordinate).sum *
              ((data A).refl (coordinate r) * post.prod)) := by
            symm
            calc
              (data A).rot
                    ((positive.map coordinate).sum -
                      (negative.map coordinate).sum) *
                  ((data A).rot (pre.map coordinate).sum *
                    ((data A).refl (coordinate r) * post.prod)) =
                  (((data A).rot
                        ((positive.map coordinate).sum -
                          (negative.map coordinate).sum) *
                      (data A).rot (pre.map coordinate).sum) *
                    (data A).refl (coordinate r)) * post.prod := by
                      simp only [mul_assoc]
              _ = (data A).refl
                    ((positive.map coordinate).sum -
                      (negative.map coordinate).sum +
                      (pre.map coordinate).sum + coordinate r) * post.prod := by
                      rw [← (data A).rot_add, (data A).rot_mul_refl]
              _ = (data A).refl
                    ((positive.map coordinate).sum +
                      (pre.map coordinate).sum +
                      (coordinate r - (negative.map coordinate).sum)) *
                    post.prod := by
                      congr 2
                      abel
      _ = (data A).rot
              ((positive.map coordinate).sum -
                (negative.map coordinate).sum) * (data A).rot z := by
            rw [hwordprod]
      _ = 1 := by
            rw [← (data A).rot_add, hsum, (data A).rot_zero]

/-- Source selection corresponding to occurrences chosen from the list of
coordinates of rotations lying in `K`. -/
noncomputable def rotationInSourceSelection
    (s : List (Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) : Selection s := by
  classical
  exact I.image (rotationInSourceOccurrence s K)

noncomputable def rotationInSourceList
    (s : List (Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) : List (Occurrence s) :=
  (rotationInSourceSelection s K I).toList

omit [Fintype A] in
theorem card_rotationInSourceSelection
    (s : List (Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) :
    (rotationInSourceSelection s K I).card = I.card := by
  classical
  rw [rotationInSourceSelection,
    Finset.card_image_of_injective _
      (rotationInSourceOccurrence_injective s K)]

omit [Fintype A] in
theorem rotationInSourceSelection_subset
    (s : List (Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) :
    rotationInSourceSelection s K I ⊆ rotationOccurrencesIn s K := by
  classical
  intro i hi
  rcases Finset.mem_image.mp hi with ⟨j, _hj, rfl⟩
  exact rotationInSourceOccurrence_mem s K j

omit [Fintype A] in
theorem disjoint_rotationInSourceSelection
    (s : List (Group A)) (K : AddSubgroup A)
    (I J : Selection (rotationInCoordinateSequence s K))
    (hIJ : Disjoint I J) :
    Disjoint (rotationInSourceSelection s K I)
      (rotationInSourceSelection s K J) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiI hiJ
  rcases Finset.mem_image.mp hiI with ⟨u, hu, hui⟩
  rcases Finset.mem_image.mp hiJ with ⟨v, hv, hvi⟩
  have huv : u = v :=
    rotationInSourceOccurrence_injective s K (hui.trans hvi.symm)
  subst v
  exact Finset.disjoint_left.mp hIJ hu hv

omit [Fintype A] in
theorem rotationInSourceList_typed
    (s : List (Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) :
    ∀ i ∈ rotationInSourceList s K I,
      IsRotation (occurrenceValue s i) := by
  classical
  intro i hi
  have hi' : i ∈ rotationInSourceSelection s K I :=
    Finset.mem_toList.mp (by simpa [rotationInSourceList] using hi)
  exact (Finset.mem_filter.mp
    (rotationInSourceSelection_subset s K I hi')).2.1

omit [Fintype A] in
private theorem sum_map_finset_toList_line
    {X : Type*} (F : Finset X) (f : X → A) :
    (F.toList.map f).sum = ∑ x ∈ F, f x := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert x F hx ih => simp [hx]

omit [Fintype A] in
theorem sum_occurrenceCoordinates_rotationInSourceList
    (s : List (Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) :
    (occurrenceCoordinates s (rotationInSourceList s K I)).sum =
      ((∑ i ∈ I,
        occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) := by
  classical
  unfold occurrenceCoordinates rotationInSourceList
  rw [sum_map_finset_toList_line]
  rw [rotationInSourceSelection, Finset.sum_image]
  · calc
      (∑ i ∈ I,
          coordinate (occurrenceValue s
            (rotationInSourceOccurrence s K i))) =
          ∑ i ∈ I,
            ((occurrenceValue
              (rotationInCoordinateSequence s K) i : K) : A) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact (occurrenceValue_rotationInCoordinateSequence s K i).symm
      _ = ((∑ i ∈ I,
          occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) := by
        simp
  · intro i hi j hj hij
    exact rotationInSourceOccurrence_injective s K hij

omit [Fintype A] in
theorem multiset_occurrenceValue_rotationInSourceList
    (s : List (Group A)) (K : AddSubgroup A)
    (I : Selection (rotationInCoordinateSequence s K)) :
    Multiset.ofList
        ((rotationInSourceList s K I).map (occurrenceValue s)) =
      selectedMultiset s (rotationInSourceSelection s K I) := by
  classical
  change Multiset.map (occurrenceValue s)
      (Multiset.ofList (rotationInSourceSelection s K I).toList) =
    Multiset.map (occurrenceValue s)
      (rotationInSourceSelection s K I).1
  rw [Finset.coe_toList]

/-- A proper subgroup of an additive group of prime cardinality is trivial. -/
theorem addSubgroup_eq_bot_of_lt_top_of_prime_natCard
    {B : Type*} [AddCommGroup B] [Fintype B]
    (q : ℕ) (hq : Nat.Prime q) (hBcard : Nat.card B = q)
    (H : AddSubgroup B) (hH : H < ⊤) : H = ⊥ := by
  have hlt : Nat.card H < q := by
    rw [← hBcard]
    simpa using natCard_lt_of_addSubgroup_lt hH
  have hfactor :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup H
  have hdvd : Nat.card H ∣ q := by
    refine ⟨Nat.card (B ⧸ H), ?_⟩
    rw [← hBcard, hfactor]
    ac_rfl
  have hone : Nat.card H = 1 := by
    rcases (Nat.dvd_prime hq).mp hdvd with hone | heq
    · exact hone
    · omega
  apply le_antisymm
  · intro x hx
    have hsub : Subsingleton H :=
      (Nat.card_eq_one_iff_unique.mp hone).1
    have heq : (⟨x, hx⟩ : H) = 0 := hsub.elim _ _
    simpa using congrArg Subtype.val heq
  · exact bot_le

/-- Direct full-branch certificate.  It retains the already extracted
quotient word and proves product one after inserting the signed rotations. -/
structure ReflectionChannelDirectFullOutput
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K) where
  Dsel : Selection s
  Dsel_subset : Dsel ⊆ h.C
  Dsel_card : Dsel.card = h.m
  productOne : IsProductOneSelection s (h.U ∪ Dsel)

noncomputable def ReflectionChannelDirectFullOutput.ofSpectrum
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    (h : ReflectionChannelPreGMOData s Q D a b K)
    (hout : HasPlusMinusSumOfCard (rotationInCoordinateSequence s K)
      h.m (-⟨h.z, h.z_mem⟩ : K)) :
    ReflectionChannelDirectFullOutput h := by
  classical
  let P := rotationInSourceSelection s K hout.positive
  let N := rotationInSourceSelection s K hout.negative
  let Dsel := P ∪ N
  have hPN : Disjoint P N :=
    disjoint_rotationInSourceSelection s K hout.positive hout.negative
      hout.disjoint
  have hPsub : P ⊆ h.C := by
    rw [h.C_eq]
    exact rotationInSourceSelection_subset s K hout.positive
  have hNsub : N ⊆ h.C := by
    rw [h.C_eq]
    exact rotationInSourceSelection_subset s K hout.negative
  have hDsub : Dsel ⊆ h.C := Finset.union_subset hPsub hNsub
  have hDcard : Dsel.card = h.m := by
    dsimp [Dsel]
    rw [Finset.card_union_of_disjoint hPN,
      card_rotationInSourceSelection, card_rotationInSourceSelection,
      hout.card_selected]
  have hUD : Disjoint h.U Dsel := h.CU_disjoint.symm.mono_right hDsub
  let positive := (rotationInSourceList s K hout.positive).map
    (occurrenceValue s)
  let negative := (rotationInSourceList s K hout.negative).map
    (occurrenceValue s)
  have hpositive : ∀ g ∈ positive, IsRotation g := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨i, hi, rfl⟩
    exact rotationInSourceList_typed s K hout.positive i hi
  have hnegative : ∀ g ∈ negative, IsRotation g := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨i, hi, rfl⟩
    exact rotationInSourceList_typed s K hout.negative i hi
  have hrefword : ∃ g ∈ h.lifted.word, ¬IsRotation g := by
    obtain ⟨i, hiU, hiref⟩ := h.U_hasReflection
    refine ⟨occurrenceValue s i, ?_, hiref⟩
    have himem : occurrenceValue s i ∈ selectedMultiset s h.U := by
      exact Multiset.mem_map.mpr ⟨i, hiU, rfl⟩
    rw [← h.lifted.word_multiset] at himem
    simpa using himem
  have hwordprod : h.lifted.word.prod = (data A).rot h.z := by
    have hrot := h.lifted.product_isRotation_and_coordinate_mem.1
    rw [eq_rotation_coordinate_of_isRotation _ hrot]
    congr 1
    exact h.z_eq.symm
  have hsum : (positive.map coordinate).sum -
      (negative.map coordinate).sum + h.z = 0 := by
    have hweighted := congrArg (fun x : K => (x : A)) hout.weighted_sum
    have hPsum :=
      sum_occurrenceCoordinates_rotationInSourceList s K hout.positive
    have hNsum :=
      sum_occurrenceCoordinates_rotationInSourceList s K hout.negative
    dsimp [positive, negative]
    simp only [List.map_map]
    change (occurrenceCoordinates s
          (rotationInSourceList s K hout.positive)).sum -
        (occurrenceCoordinates s
          (rotationInSourceList s K hout.negative)).sum + h.z = 0
    rw [hPsum, hNsum]
    have hweighted' :
        (∑ i ∈ hout.positive,
            ((occurrenceValue
              (rotationInCoordinateSequence s K) i : K) : A)) -
          (∑ i ∈ hout.negative,
            ((occurrenceValue
              (rotationInCoordinateSequence s K) i : K) : A)) = -h.z := by
      simpa using hweighted
    have hcoeP :
        ((∑ i ∈ hout.positive,
          occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) =
          ∑ i ∈ hout.positive,
            ((occurrenceValue
              (rotationInCoordinateSequence s K) i : K) : A) := by
      simp
    have hcoeN :
        ((∑ i ∈ hout.negative,
          occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) =
          ∑ i ∈ hout.negative,
            ((occurrenceValue
              (rotationInCoordinateSequence s K) i : K) : A) := by
      simp
    rw [hcoeP, hcoeN, hweighted']
    abel
  have horder := hasProductOneOrdering_insert_signed_rotations
    h.lifted.word positive negative h.z hpositive hnegative hrefword
      hwordprod hsum
  refine {
    Dsel := Dsel
    Dsel_subset := hDsub
    Dsel_card := hDcard
    productOne := ?_
  }
  change HasProductOneOrdering (selectedMultiset s (h.U ∪ Dsel))
  rw [selectedMultiset_union_of_disjoint s h.U Dsel hUD]
  rw [selectedMultiset_union_of_disjoint s P N hPN]
  rw [← multiset_occurrenceValue_rotationInSourceList s K hout.positive]
  rw [← multiset_occurrenceValue_rotationInSourceList s K hout.negative]
  rw [← h.lifted.word_multiset]
  simpa [positive, negative] using horder

theorem ReflectionChannelDirectFullOutput.hasProductOneSubsequence
    {s : List (Group A)} {Q D a b : ℕ} {K : AddSubgroup A}
    {h : ReflectionChannelPreGMOData s Q D a b K}
    (hout : ReflectionChannelDirectFullOutput h) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  refine ⟨h.U ∪ hout.Dsel, ?_, hout.productOne⟩
  have hdis : Disjoint h.U hout.Dsel :=
    h.CU_disjoint.symm.mono_right hout.Dsel_subset
  rw [Finset.card_union_of_disjoint hdis, hout.Dsel_card, h.exactSize]

/-- The second signed-GMO call in the large-special line branch.  The full
case cancels the lifted defect literally.  In the non-full case, primality of
`K` forces the concentrated subgroup to be zero and the existing checked
identity-padding base closes the source. -/
theorem hasProductOneSubsequence_of_reflectionPreGMO_rankOne
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (K : AddSubgroup A) [Fintype K] (hKcard : Nat.card K = q)
    (hGMO : PlusMinusGMOStructuralProvider K)
    (s : List (Group A)) (Q D a b : ℕ)
    (hlen : s.length = 2 * Q + D)
    (hQ : Q = Nat.card A) (hQrank : Q = q ^ 2)
    (hDb : D ≤ b - Q + 2)
    (hsmall : SmallDavenportProductOneFreeAtMost (Group A) D)
    (hcapacity : b - q + 2 ≤ (rotationOccurrencesIn s K).card)
    (h : ReflectionChannelPreGMOData s Q D a b K)
    (htarget : Nat.card K ≤ h.m)
    (hthreshold : h.m + (q - 1) ≤ h.M) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  classical
  let xs := rotationInCoordinateSequence s K
  have hxslen : xs.length = h.M := by
    calc
      xs.length = (rotationOccurrencesIn s K).card := by
        simp [xs, rotationInCoordinateSequence]
      _ = h.C.card := by rw [h.C_eq]
      _ = h.M := h.Ccard
  have hpm : PlusMinusDavenportAtMost K q := by
    rw [← hKcard]
    exact plusMinusDavenportAtMost_natCard
  have hthreshold' : h.m + q - 1 ≤ xs.length := by
    rw [hxslen]
    omega
  rcases hGMO xs h.m q htarget hpm hthreshold' with hfull | hnonfull
  · obtain ⟨hout⟩ := hfull (-⟨h.z, h.z_mem⟩ : K)
    exact (ReflectionChannelDirectFullOutput.ofSpectrum h hout).hasProductOneSubsequence
  · obtain ⟨hc⟩ := hnonfull
    have hHbot : hc.K = ⊥ :=
      addSubgroup_eq_bot_of_lt_top_of_prime_natCard
        q hqPrime hKcard hc.K hc.strict
    let X := rotationInSourceSelection s K hc.selected
    have hXcard : X.card = hc.selected.card :=
      card_rotationInSourceSelection s K hc.selected
    have hoddK : Odd (Nat.card K) := by
      rw [hKcard]
      exact hqodd
    have hXsub : X ⊆ rotationOccurrencesIn s (⊥ : AddSubgroup A) := by
      intro i hi
      rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
      have hjmem : occurrenceValue xs j ∈ hc.K :=
        hc.value_mem_subgroup
          (odd_natCard_quotient_of_odd_natCard hc.K hoddK) j hj
      have hjzero : occurrenceValue xs j = 0 := by
        rw [hHbot] at hjmem
        simpa using hjmem
      have hcoord :
          coordinate
              (occurrenceValue s (rotationInSourceOccurrence s K j)) = 0 := by
        have hval := occurrenceValue_rotationInCoordinateSequence s K j
        change ((occurrenceValue xs j : K) : A) = _ at hval
        rw [hjzero] at hval
        simpa using hval.symm
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_, ?_⟩
      · exact (Finset.mem_filter.mp
          (rotationInSourceOccurrence_mem s K j)).2.1
      · simpa using hcoord
    have hxsM : xs.length = h.M := hxslen
    have hquotcard : Nat.card (K ⧸ hc.K) = q := by
      rw [hHbot]
      calc
        Nat.card (K ⧸ (⊥ : AddSubgroup K)) = Nat.card K :=
          Nat.card_congr
            (QuotientAddGroup.quotientBot (G := K)).toEquiv
        _ = q := hKcard
    have hClower : b - q + 2 ≤ h.M := by
      rw [← h.Ccard, h.C_eq]
      exact hcapacity
    have hXlower : h.M - q + 2 ≤ X.card := by
      rw [hXcard]
      have hcLower := hc.card_lower
      rw [hquotcard, hxsM] at hcLower
      exact hcLower
    have hquad : 2 * q ≤ q ^ 2 + 2 := by
      nlinarith [sq_nonneg (q - 1)]
    have hbotCapacity : b - Q + 2 ≤
        (rotationOccurrencesIn s (⊥ : AddSubgroup A)).card := by
      apply (show b - Q + 2 ≤ X.card by
        rw [hQrank]
        omega).trans
      exact Finset.card_le_card hXsub
    have hAbot : Nat.card (A ⧸ (⊥ : AddSubgroup A)) = Q := by
      calc
        Nat.card (A ⧸ (⊥ : AddSubgroup A)) = Nat.card A :=
          Nat.card_congr
            (QuotientAddGroup.quotientBot (G := A)).toEquiv
        _ = Q := hQ.symm
    apply rcStatement_bot_of_smallDavenport s Q D b hlen hQ hDb hsmall
    rw [hAbot]
    exact hbotCapacity

theorem lineSpecialOccurrences_eq_reflectionQuotientCarrier
    (s : List (Group A)) (K : AddSubgroup A) :
    lineSpecialOccurrences s K = reflectionQuotientCarrier s K := by
  classical
  ext i
  by_cases hrot : IsRotation (occurrenceValue s i)
  · by_cases hmem : coordinate (occurrenceValue s i) ∈ K
    · simp [lineSpecialOccurrences, reflectionQuotientCarrier,
        rotationOccurrencesIn, rotationOccurrencesOutside,
        reflectionOccurrences, hrot, hmem]
    · have hiRot : i ∈ rotationOccurrences s := by
        simpa [rotationOccurrences] using hrot
      simp [lineSpecialOccurrences, reflectionQuotientCarrier,
        rotationOccurrencesIn, rotationOccurrencesOutside,
        reflectionOccurrences, hrot, hmem, hiRot]
  · simp [lineSpecialOccurrences, reflectionQuotientCarrier,
      rotationOccurrencesIn, rotationOccurrencesOutside,
      reflectionOccurrences, hrot]

/-- A genuine small-Davenport bound in the quotient group supplies the
source-occurrence-shaped quotient interface used by maximum extraction. -/
theorem quotientSmallDavenportProductOneFreeAtMost_of_smallDavenport
    (K : AddSubgroup A) (d : ℕ)
    (hsmall : SmallDavenportProductOneFreeAtMost (Group (A ⧸ K)) d) :
    QuotientSmallDavenportProductOneFreeAtMost K d := by
  classical
  intro s R hfree
  let t : List (Group A) := occurrenceSubsequence s R
  let qt : List (Group (A ⧸ K)) := t.map (quotientMap K)
  have hqtfree : IsProductOneFreeSelection qt Finset.univ := by
    intro J hJuniv hJne hJprod
    let Jt : Selection t := pullbackMapSelection (quotientMap K) t J
    let I : Selection s := liftOccurrenceSubsequenceSelection s R Jt
    have hIsub : I ⊆ R :=
      liftOccurrenceSubsequenceSelection_subset s R Jt
    have hJtcard : Jt.card = J.card := Finset.card_map _
    have hIcard : I.card = Jt.card :=
      card_liftOccurrenceSubsequenceSelection s R Jt
    have hIne : I.Nonempty := by
      apply Finset.card_pos.mp
      rw [hIcard, hJtcard]
      exact Finset.card_pos.mpr hJne
    apply hfree I hIsub hIne
    rw [selectedMultiset_liftOccurrenceSubsequenceSelection]
    rw [selectedMultiset_pullbackMapSelection]
    exact hJprod
  have hbound := hsmall qt Finset.univ hqtfree
  have htlen : t.length = R.card := by
    simp [t, occurrenceSubsequence]
  have hqtlen : qt.length = R.card := by simp [qt, htlen]
  simpa [hqtlen] using hbound

/-- The `s > q` leaf for a nonzero concentrated line in rank two. -/
theorem rankTwo_line_largeSpecial_upper
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hlineGMO : ∀ (K : AddSubgroup (PrimeVectorSpace q 2)) [Fintype K],
      PlusMinusGMOStructuralProvider K)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 2) (2 * (q - 1) + 1))
    (s : List (PrimeVectorDihedral q 2))
    (hlen : s.length = 2 * q ^ 2 + 2 * (q - 1) + 1)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 2 * (q - 1) + 1)
    (K : AddSubgroup (PrimeVectorSpace q 2))
    (hKne : K ≠ ⊥)
    (hconc : MiddleNonfullConcentrationOutput s
      (rotationOccurrences s).card K)
    (hspecial : q < (lineSpecialOccurrences s K).card) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 2) := by
  classical
  letI : Fact (Nat.Prime q) := ⟨hqPrime⟩
  let A := PrimeVectorSpace q 2
  let Q := q ^ 2
  let D := 2 * (q - 1) + 1
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hqpos : 0 < q := hqPrime.pos
  have hQcard : Q = Nat.card A := by
    simp [Q, A, PrimeVectorSpace]
  have hQrank : Q = q ^ 2 := rfl
  have hAodd : Odd (Nat.card A) := by
    rw [← hQcard]
    exact hqodd.pow
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    simp [Q, D, Nat.add_assoc]
  have hKtop : K < ⊤ := hconc.proper
  have hKcard : Nat.card K = q :=
    natCard_eq_prime_of_ne_bot_of_lt_top_rankTwo
      q hqPrime K hKne hKtop
  have hquotcard : Nat.card (A ⧸ K) = q :=
    natCard_quotient_eq_prime_of_ne_bot_of_lt_top_rankTwo
      q hqPrime K hKne hKtop
  have hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card := by
    exact hconc.rotationCapacity hAodd
  have hcapacityq : b - q + 2 ≤
      (rotationOccurrencesIn s K).card := by
    simpa only [hquotcard] using hcapacity
  have hspecial' : q < (reflectionOccurrences s).card +
      (rotationOccurrencesOutside s K).card := by
    have hdis : Disjoint (reflectionOccurrences s)
        (rotationOccurrencesOutside s K) := by
      rw [Finset.disjoint_left]
      intro i hiref hiout
      have hnrot : ¬IsRotation (occurrenceValue s i) := by
        simpa [reflectionOccurrences] using hiref
      exact hnrot ((mem_rotationOccurrencesOutside_iff s K i).1 hiout).1
    have hcardSpecial :
        (lineSpecialOccurrences s K).card =
          (reflectionOccurrences s).card +
            (rotationOccurrencesOutside s K).card := by
      rw [lineSpecialOccurrences_eq_reflectionQuotientCarrier]
      exact Finset.card_union_of_disjoint hdis
    rwa [hcardSpecial] at hspecial
  have hchannel : ¬QuotientNoReflection s K := by
    intro hno
    exact hno (hasReflectionContainingQuotientProductOne_of_prime_card
      hqodd K hquotcard s ha2 hspecial')
  have hsmallQuot : QuotientSmallDavenportProductOneFreeAtMost K q := by
    exact quotientSmallDavenportProductOneFreeAtMost_of_smallDavenport K q
      (smallDavenportProductOneFreeAtMost_of_prime_card hqodd hquotcard)
  have hDQ : D ≤ Q := by
    have hqm1 : q - 1 + 1 = q := Nat.sub_add_cancel hqpos
    dsimp only [D, Q]
    nlinarith [sq_nonneg (q - 1)]
  have hDqD : q ≤ D := by
    dsimp only [D]
    omega
  obtain ⟨hpre⟩ := exists_reflectionChannelPreGMOData
    s Q D a b q K rfl rfl htotal hDQ (by simpa [a, D] using haD)
      hQcard hcapacity hsmallQuot hDqD hchannel
  have hRsmall : hpre.R.card ≤ q := hsmallQuot s hpre.R hpre.R_free
  have hsplit : D + 1 = q + q := by
    dsimp only [D]
    omega
  have htau : q - 1 ≤ hpre.tau :=
    hpre.tau_ge_of_davenport_split hsplit hRsmall
  have hthreshold : hpre.m + (q - 1) ≤ hpre.M :=
    hpre.signed_reservoir_threshold htau
  have hKpos : (⊥ : AddSubgroup A) < K := bot_lt_iff_ne_bot.mpr hKne
  have htarget : Nat.card K ≤ hpre.m :=
    hpre.target_ge_card_subgroup hQcard hDQ hKpos hKtop hcapacity
      (by simpa [a, D] using haD) htotal
  have hDb : D ≤ b - Q + 2 := by
    omega
  exact hasProductOneSubsequence_of_reflectionPreGMO_rankOne
    q hqPrime hqodd K hKcard (hlineGMO K) s Q D a b
      (by
        calc
          s.length = 2 * q ^ 2 + 2 * (q - 1) + 1 := hlen
          _ = 2 * Q + D := by simp [Q, D, Nat.add_assoc])
      hQcard hQrank hDb hsmallAmbient
      hcapacityq hpre htarget hthreshold

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.hasProductOneOrdering_insert_signed_rotations
#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelDirectFullOutput.ofSpectrum
#print axioms GaoLean.ConcreteGDihedral.ReflectionChannelDirectFullOutput.hasProductOneSubsequence
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequence_of_reflectionPreGMO_rankOne
#print axioms GaoLean.ConcreteGDihedral.rankTwo_line_largeSpecial_upper
