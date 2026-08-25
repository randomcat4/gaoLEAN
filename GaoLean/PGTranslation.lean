import GaoLean.PGInduction

/-!
# All-rotation translation pullback

The residual controller translates every rotation coordinate by `-α`.  A
recursive `ZR` call returns exactly `2Q` rotations.  This file proves that the
same labelled selection is product one before translation whenever `Q • α=0`.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem eq_rotation_coordinate_of_isRotation (g : Group A)
    (hg : IsRotation g) :
    g = rotation A (Multiplicative.ofAdd (coordinate g)) := by
  apply SemidirectProduct.ext
  · rfl
  · change g.right = 1
    exact hg

theorem eq_of_isRotation_of_coordinate_eq {g h : Group A}
    (hg : IsRotation g) (hh : IsRotation h)
    (hcoord : coordinate g = coordinate h) : g = h := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd (coordinate g) =
      Multiplicative.ofAdd (coordinate h)
    rw [hcoord]
  · change g.right = h.right
    rw [hg, hh]

theorem coordinate_translateRotations (α : A) (g : Group A)
    (hg : IsRotation g) :
    coordinate (translateRotations α g) = coordinate g - α := by
  rw [translateRotations, if_pos hg]
  simp [coordinate, rotation, SemidirectProduct.mul_left]
  abel

/-- Translation by `-α` is the inverse of translation by `α` on rotations. -/
theorem translateRotations_neg_leftInverse (α : A) (g : Group A)
    (hg : IsRotation g) :
    translateRotations (-α) (translateRotations α g) = g := by
  have hgt : IsRotation (translateRotations α g) :=
    (isRotation_translateRotations_iff α g).2 hg
  apply eq_of_isRotation_of_coordinate_eq
      ((isRotation_translateRotations_iff (-α) _).2 hgt) hg
  rw [coordinate_translateRotations (-α) _ hgt,
    coordinate_translateRotations α g hg]
  abel

/-- A literal word of rotations multiplies to the rotation of the sum of its
additive coordinates. -/
theorem prod_eq_rotation_sum_of_all_rotation
    (word : List (Group A)) (hall : ∀ g ∈ word, IsRotation g) :
    word.prod =
      rotation A (Multiplicative.ofAdd (word.map coordinate).sum) := by
  induction word with
  | nil => simp [rotation]
  | cons g word ih =>
      have hg : IsRotation g := hall g (by simp)
      have htail : ∀ x ∈ word, IsRotation x := by
        intro x hx
        exact hall x (by simp [hx])
      rw [List.prod_cons, eq_rotation_coordinate_of_isRotation g hg, ih htail]
      rw [← map_mul]
      rfl

theorem sum_coordinate_eq_zero_of_prod_one
    (word : List (Group A)) (hall : ∀ g ∈ word, IsRotation g)
    (hprod : word.prod = 1) :
    (word.map coordinate).sum = 0 := by
  have hp := prod_eq_rotation_sum_of_all_rotation word hall
  have hc := congrArg coordinate (hprod.symm.trans hp)
  change 0 = (word.map coordinate).sum at hc
  have : 0 = (word.map coordinate).sum := hc
  exact this.symm

/-- Pull a literal exact-`2Q` all-rotation product-one word back through the
coordinate translation. -/
theorem prod_map_translateRotations_neg_eq_one
    (word : List (Group A)) (α : A) (Q : ℕ)
    (hall : ∀ g ∈ word, IsRotation g)
    (hprod : word.prod = 1) (hlen : word.length = 2 * Q)
    (hQα : Q • α = 0) :
    (word.map (translateRotations (-α))).prod = 1 := by
  have hallBack : ∀ g ∈ word.map (translateRotations (-α)), IsRotation g := by
    intro g hg
    rcases List.mem_map.mp hg with ⟨x, hx, rfl⟩
    exact (isRotation_translateRotations_iff (-α) x).2 (hall x hx)
  rw [prod_eq_rotation_sum_of_all_rotation _ hallBack]
  have hcoordList :
      (word.map (translateRotations (-α))).map coordinate =
        (word.map coordinate).map (fun x => x + α) := by
    simp only [List.map_map]
    apply List.map_congr_left
    intro g hg
    change coordinate (translateRotations (-α) g) = coordinate g + α
    rw [coordinate_translateRotations (-α) g (hall g hg)]
    abel
  rw [hcoordList]
  have hsum := sum_map_add_const_of_twice_card
    (s := word.map coordinate) (Q := Q) (α := α) (by simpa using hlen) hQα
  rw [hsum, sum_coordinate_eq_zero_of_prod_one word hall hprod]
  exact map_one (rotation A)

/-- Occurrence-faithful controller pullback: the output uses the exact same
selection `I`; only its realizing word is mapped through the inverse
translation. -/
theorem isProductOneSelection_of_translated_allRotation
    (s : List (Group A)) (I : Selection s) (α : A) (Q : ℕ)
    (hcard : I.card = 2 * Q)
    (hall : ∀ i ∈ I, IsRotation (occurrenceValue s i))
    (htranslated : HasProductOneOrdering
      ((selectedMultiset s I).map (translateRotations α)))
    (hQα : Q • α = 0) :
    IsProductOneSelection s I := by
  rcases htranslated with ⟨word, hword, hprod⟩
  have hallSelected : ∀ g ∈ selectedMultiset s I, IsRotation g := by
    intro g hg
    rw [selectedMultiset] at hg
    rcases Multiset.mem_map.mp hg with ⟨i, hi, rfl⟩
    exact hall i hi
  have hallWord : ∀ g ∈ word, IsRotation g := by
    intro g hg
    have hgm : g ∈ (selectedMultiset s I).map (translateRotations α) := by
      rw [← hword]
      exact hg
    rcases Multiset.mem_map.mp hgm with ⟨x, hx, rfl⟩
    exact (isRotation_translateRotations_iff α x).2 (hallSelected x hx)
  have hlen : word.length = 2 * Q := by
    have hc := congrArg Multiset.card hword
    simpa [hcard] using hc
  refine ⟨word.map (translateRotations (-α)), ?_, ?_⟩
  · calc
      Multiset.ofList (word.map (translateRotations (-α))) =
          (Multiset.ofList word).map (translateRotations (-α)) := by simp
      _ = ((selectedMultiset s I).map (translateRotations α)).map
          (translateRotations (-α)) := congrArg _ hword
      _ = (selectedMultiset s I).map
          (translateRotations (-α) ∘ translateRotations α) := by
            rw [Multiset.map_map]
      _ = (selectedMultiset s I).map id := by
            apply Multiset.map_congr rfl
            intro g hg
            exact translateRotations_neg_leftInverse α g (hallSelected g hg)
      _ = selectedMultiset s I := by simp
  · exact prod_map_translateRotations_neg_eq_one
      word α Q hallWord hprod hlen hQα

/-- The actual translated auxiliary list used by a recursive `ZR` call. -/
noncomputable def translatedSequence (α : A) (s : List (Group A)) :
    List (Group A) :=
  s.map (translateRotations α)

/-- Position-preserving equivalence between a source list and its translated
list.  It changes only the length proof carried by `Fin`, never the index. -/
noncomputable def translatedOccurrenceEquiv (α : A) (s : List (Group A)) :
    Occurrence s ≃ Occurrence (translatedSequence α s) :=
  finCongr (by simp [translatedSequence])

theorem occurrenceValue_translatedSequence
    (α : A) (s : List (Group A)) (i : Occurrence s) :
    occurrenceValue (translatedSequence α s)
        (translatedOccurrenceEquiv α s i) =
      translateRotations α (occurrenceValue s i) := by
  simp only [occurrenceValue, translatedSequence, List.get_eq_getElem,
    List.getElem_map]
  congr 1

/-- Pull a selection of translated-list positions back to the exact source
positions. -/
noncomputable def pullbackTranslatedSelection
    (α : A) (s : List (Group A))
    (J : Selection (translatedSequence α s)) : Selection s :=
  J.map (translatedOccurrenceEquiv α s).symm.toEmbedding

@[simp]
theorem card_pullbackTranslatedSelection
    (α : A) (s : List (Group A))
    (J : Selection (translatedSequence α s)) :
    (pullbackTranslatedSelection α s J).card = J.card := by
  simp [pullbackTranslatedSelection]

/-- Selected multiplicities commute with the position-preserving list
translation, even when several source occurrences carry equal values. -/
theorem map_selectedMultiset_pullbackTranslatedSelection
    (α : A) (s : List (Group A))
    (J : Selection (translatedSequence α s)) :
    (selectedMultiset s (pullbackTranslatedSelection α s J)).map
        (translateRotations α) =
      selectedMultiset (translatedSequence α s) J := by
  unfold selectedMultiset pullbackTranslatedSelection
  rw [Finset.map_val, Multiset.map_map, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro j _hj
  change translateRotations α
      (occurrenceValue s ((translatedOccurrenceEquiv α s).symm j)) =
    occurrenceValue (translatedSequence α s) j
  rw [← occurrenceValue_translatedSequence α s
    ((translatedOccurrenceEquiv α s).symm j)]
  simp

/-- The occurrence-labelled quotient guard survives both the rotation
translation and the canonical reindexing from the source list to the actual
translated auxiliary list. -/
theorem quotientNoReflection_translatedSequence_anti
    (s : List (Group A)) (H K : AddSubgroup A) (hHK : H ≤ K)
    {α : A} (hα : α ∈ K) (hguard : QuotientNoReflection s K) :
    QuotientNoReflection (translatedSequence α s) H := by
  rw [quotientNoReflection_iff_on]
  have hsource : QuotientNoReflectionOn
      (fun i : Occurrence s =>
        translateRotations α (occurrenceValue s i)) H :=
    quotientNoReflection_translate_occurrences_anti s H K hHK hα hguard
  intro htarget
  apply hsource
  rcases htarget with ⟨J, hcarrier, ⟨j, hj, href⟩, hprod⟩
  let I : Selection s := pullbackTranslatedSelection α s J
  have hvalues :
      I.1.map (fun i => translateRotations α (occurrenceValue s i)) =
        J.1.map (occurrenceValue (translatedSequence α s)) := by
    simpa [selectedMultiset, Multiset.map_map] using
      map_selectedMultiset_pullbackTranslatedSelection α s J
  refine ⟨I, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, hji⟩
    subst i
    have hvalue := occurrenceValue_translatedSequence α s
      ((translatedOccurrenceEquiv α s).symm j)
    have hvalue' : occurrenceValue (translatedSequence α s) j =
        translateRotations α
          (occurrenceValue s ((translatedOccurrenceEquiv α s).symm j)) := by
      simpa using hvalue
    have hcarrierJ := hcarrier j hj
    rw [hvalue'] at hcarrierJ
    exact hcarrierJ
  · refine ⟨(translatedOccurrenceEquiv α s).symm j, ?_, ?_⟩
    · exact Finset.mem_map.mpr ⟨j, hj, rfl⟩
    · have hvalue := occurrenceValue_translatedSequence α s
        ((translatedOccurrenceEquiv α s).symm j)
      have hvalue' : occurrenceValue (translatedSequence α s) j =
          translateRotations α
            (occurrenceValue s ((translatedOccurrenceEquiv α s).symm j)) := by
        simpa using hvalue
      rw [hvalue'] at href
      simpa using href
  · rw [hvalues]
    exact hprod

/-- Translation does not change the number of labelled positions. -/
@[simp]
theorem length_translatedSequence (α : A) (s : List (Group A)) :
    (translatedSequence α s).length = s.length := by
  simp [translatedSequence]

/-- The translated list has exactly the image of the source rotation
occurrences under the canonical position equivalence. -/
theorem map_rotationOccurrences_translatedSequence
    (α : A) (s : List (Group A)) :
    (rotationOccurrences s).map (translatedOccurrenceEquiv α s).toEmbedding =
      rotationOccurrences (translatedSequence α s) := by
  classical
  ext j
  simp only [Finset.mem_map, rotationOccurrences, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    change IsRotation (occurrenceValue (translatedSequence α s)
      (translatedOccurrenceEquiv α s i))
    rw [occurrenceValue_translatedSequence]
    exact (isRotation_translateRotations_iff α _).2 hi
  · intro hj
    refine ⟨(translatedOccurrenceEquiv α s).symm j, ?_, ?_⟩
    · have hvalue := occurrenceValue_translatedSequence α s
        ((translatedOccurrenceEquiv α s).symm j)
      have hvalue' : occurrenceValue (translatedSequence α s) j =
          translateRotations α
            (occurrenceValue s ((translatedOccurrenceEquiv α s).symm j)) := by
        simpa using hvalue
      rw [hvalue'] at hj
      exact (isRotation_translateRotations_iff α _).1 hj
    · simp

@[simp]
theorem card_rotationOccurrences_translatedSequence
    (α : A) (s : List (Group A)) :
    (rotationOccurrences (translatedSequence α s)).card =
      (rotationOccurrences s).card := by
  rw [← map_rotationOccurrences_translatedSequence α s, Finset.card_map]

/-- Reflections are the complementary labelled positions, so their exact
occurrence count is also translation invariant. -/
theorem map_reflectionOccurrences_translatedSequence
    (α : A) (s : List (Group A)) :
    (reflectionOccurrences s).map
        (translatedOccurrenceEquiv α s).toEmbedding =
      reflectionOccurrences (translatedSequence α s) := by
  classical
  ext j
  simp only [Finset.mem_map, reflectionOccurrences, Finset.mem_filter,
    Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩
    change ¬IsRotation (occurrenceValue (translatedSequence α s)
      (translatedOccurrenceEquiv α s i))
    rw [occurrenceValue_translatedSequence]
    exact fun hrot => hi ((isRotation_translateRotations_iff α _).1 hrot)
  · intro hj
    refine ⟨(translatedOccurrenceEquiv α s).symm j, ?_, ?_⟩
    · intro hrot
      apply hj
      have hvalue := occurrenceValue_translatedSequence α s
        ((translatedOccurrenceEquiv α s).symm j)
      have hvalue' : occurrenceValue (translatedSequence α s) j =
          translateRotations α
            (occurrenceValue s ((translatedOccurrenceEquiv α s).symm j)) := by
        simpa using hvalue
      rw [hvalue']
      exact (isRotation_translateRotations_iff α _).2 hrot
    · simp

@[simp]
theorem card_reflectionOccurrences_translatedSequence
    (α : A) (s : List (Group A)) :
    (reflectionOccurrences (translatedSequence α s)).card =
      (reflectionOccurrences s).card := by
  rw [← map_reflectionOccurrences_translatedSequence α s, Finset.card_map]

/-- Exact occurrence-capacity bridge for the non-full GMO branch.  If a
labelled source set consists of rotations in the affine coset `α + H`, its
canonical image is contained in the rotations of the translated list whose
coordinates lie in `H`. -/
theorem card_le_rotationOccurrencesIn_translatedSequence
    (α : A) (s : List (Group A)) (H : AddSubgroup A) (C : Selection s)
    (hC : ∀ i ∈ C,
      IsRotation (occurrenceValue s i) ∧
        coordinate (occurrenceValue s i) - α ∈ H) :
    C.card ≤ (rotationOccurrencesIn (translatedSequence α s) H).card := by
  classical
  have hsubset :
      C.map (translatedOccurrenceEquiv α s).toEmbedding ⊆
        rotationOccurrencesIn (translatedSequence α s) H := by
    intro j hj
    rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
    rw [rotationOccurrencesIn]
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    change IsRotation (occurrenceValue (translatedSequence α s)
        (translatedOccurrenceEquiv α s i)) ∧
      coordinate (occurrenceValue (translatedSequence α s)
        (translatedOccurrenceEquiv α s i)) ∈ H
    rw [occurrenceValue_translatedSequence]
    refine ⟨(isRotation_translateRotations_iff α _).2 (hC i hi).1, ?_⟩
    rw [coordinate_translateRotations α _ (hC i hi).1]
    exact (hC i hi).2
  calc
    C.card = (C.map (translatedOccurrenceEquiv α s).toEmbedding).card :=
      (Finset.card_map _).symm
    _ ≤ (rotationOccurrencesIn (translatedSequence α s) H).card :=
      Finset.card_le_card hsubset

/-- Fully list-facing recursive pullback.  A `ZR` result on the translated
auxiliary list yields an exact all-rotation product-one selection in the
original list, with positions transported by the canonical `Fin` equivalence. -/
theorem hasAllRotationProductOneSubsequence_pullback_translatedSequence
    (α : A) (s : List (Group A)) (Q : ℕ)
    (htranslated : HasAllRotationProductOneSubsequenceOfCard
      (translatedSequence α s) (2 * Q))
    (hQα : Q • α = 0) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  rcases htranslated with ⟨J, hJcard, hJprod, hJrot⟩
  let I : Selection s := pullbackTranslatedSelection α s J
  have hIcard : I.card = 2 * Q := by
    simp [I, hJcard]
  have hIrot : ∀ i ∈ I, IsRotation (occurrenceValue s i) := by
    intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, hji⟩
    have hjrot := hJrot j hj
    have hvalue := occurrenceValue_translatedSequence α s
      ((translatedOccurrenceEquiv α s).symm j)
    have hvalue' : occurrenceValue (translatedSequence α s) j =
        translateRotations α
          (occurrenceValue s ((translatedOccurrenceEquiv α s).symm j)) := by
      simpa using hvalue
    rw [hvalue'] at hjrot
    have horig : IsRotation
        (occurrenceValue s ((translatedOccurrenceEquiv α s).symm j)) := by
      exact (isRotation_translateRotations_iff α _).1 hjrot
    rw [← hji]
    exact horig
  have hmapped : HasProductOneOrdering
      ((selectedMultiset s I).map (translateRotations α)) := by
    rw [map_selectedMultiset_pullbackTranslatedSelection α s J]
    exact hJprod
  refine ⟨I, hIcard, ?_, hIrot⟩
  exact isProductOneSelection_of_translated_allRotation
    s I α Q hIcard hIrot hmapped hQα

/-- One complete strict-subgroup `ZR` invocation and pullback.  The only
branch-specific premise left explicit is the translated `H`-capacity; length,
rotation/reflection counts, quotient guard, and the `2Qα=0` correction are all
derived here. -/
theorem hasAllRotationProductOneSubsequence_of_concreteZR_translatedSequence
    (α : A) (s : List (Group A)) (Q D a b : ℕ)
    (H K : AddSubgroup A)
    (hZR : ConcreteZRStatement (translatedSequence α s) Q D a b H)
    (hlen : s.length = 2 * Q + D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hcapacity : b - Nat.card (A ⧸ H) + 2 ≤
      (rotationOccurrencesIn (translatedSequence α s) H).card)
    (hHK : H ≤ K) (hα : α ∈ K)
    (hguard : QuotientNoReflection s K)
    (hQ : Q = Nat.card A) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  have htranslated : HasAllRotationProductOneSubsequenceOfCard
      (translatedSequence α s) (2 * Q) := by
    apply hZR
    · simpa using hlen
    · simpa using href
    · simpa using hrot
    · exact hcapacity
    · exact quotientNoReflection_translatedSequence_anti
        s H K hHK hα hguard
  apply hasAllRotationProductOneSubsequence_pullback_translatedSequence
    α s Q htranslated
  simpa [hQ] using (card_nsmul_eq_zero' α)

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.translateRotations_neg_leftInverse
#print axioms GaoLean.ConcreteGDihedral.prod_map_translateRotations_neg_eq_one
#print axioms GaoLean.ConcreteGDihedral.isProductOneSelection_of_translated_allRotation
#print axioms GaoLean.ConcreteGDihedral.map_selectedMultiset_pullbackTranslatedSelection
#print axioms GaoLean.ConcreteGDihedral.quotientNoReflection_translatedSequence_anti
#print axioms GaoLean.ConcreteGDihedral.card_rotationOccurrences_translatedSequence
#print axioms GaoLean.ConcreteGDihedral.card_reflectionOccurrences_translatedSequence
#print axioms GaoLean.ConcreteGDihedral.card_le_rotationOccurrencesIn_translatedSequence
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_pullback_translatedSequence
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_concreteZR_translatedSequence
