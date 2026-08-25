import GaoLean.PGPairReservoir

/-!
# Signed occurrence-pair selection bridge

This file turns a genuinely occurrence-labelled signed selection of same-type
pairs into the coordinate-level `BalancedSignedPairAssignment` consumed by the
explicit product-one ordering theorem.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem eq_refl_coordinate_of_not_isRotation (g : Group A)
    (hg : ¬IsRotation g) :
    g = (data A).refl (coordinate g) := by
  apply SemidirectProduct.ext
  · rw [data_refl_left]
    rfl
  · simp only [data_refl_right]
    change g.right = Multiplicative.ofAdd (1 : ZMod 2)
    have hright : g.right ≠ 1 := hg
    let z : ZMod 2 := Multiplicative.toAdd g.right
    have hz0 : z ≠ 0 := by simpa [z] using hright
    have hzval : z.val = 1 := by
      have hlt := ZMod.val_lt z
      have hne : z.val ≠ 0 := fun hzero =>
        hz0 ((ZMod.val_eq_zero z).mp hzero)
      omega
    have hz : z = 1 := by
      apply ZMod.val_injective
      simpa [ZMod.val_one_eq_one_mod] using hzval
    exact congrArg Multiplicative.ofAdd hz

@[simp]
theorem coordinate_data_rot (a : A) :
    coordinate ((data A).rot a) = a := by
  rfl

@[simp]
theorem coordinate_data_refl (a : A) :
    coordinate ((data A).refl a) = a := by
  simp [coordinate]

def occurrenceCoordinatePairs (s : List (Group A))
    (pairs : List (Occurrence s × Occurrence s)) : List (A × A) :=
  pairs.map fun p =>
    (coordinate (occurrenceValue s p.1),
      coordinate (occurrenceValue s p.2))

/-- Exact signed pair data after selecting from a same-type occurrence
reservoir.  Endpoint no-duplication is stated on source positions. -/
structure SignedOccurrencePairSelection
    (s : List (Group A)) (q : ℕ) where
  rotationPositive : List (Occurrence s × Occurrence s)
  rotationNegative : List (Occurrence s × Occurrence s)
  reflectionPositive : List (Occurrence s × Occurrence s)
  reflectionNegative : List (Occurrence s × Occurrence s)
  rotationPositiveFromReservoir : ∀ p ∈ rotationPositive,
    p ∈ (canonicalSameTypePairReservoir s).rotationPairs
  rotationNegativeFromReservoir : ∀ p ∈ rotationNegative,
    p ∈ (canonicalSameTypePairReservoir s).rotationPairs
  reflectionPositiveFromReservoir : ∀ p ∈ reflectionPositive,
    p ∈ (canonicalSameTypePairReservoir s).reflectionPairs
  reflectionNegativeFromReservoir : ∀ p ∈ reflectionNegative,
    p ∈ (canonicalSameTypePairReservoir s).reflectionPairs
  pairCount_eq :
    rotationPositive.length + rotationNegative.length +
      reflectionPositive.length + reflectionNegative.length = q
  reflectionPairsNonempty :
    reflectionPositive ≠ [] ∨ reflectionNegative ≠ []
  rotationPositiveTyped : ∀ p ∈ rotationPositive,
    IsRotation (occurrenceValue s p.1) ∧
      IsRotation (occurrenceValue s p.2)
  rotationNegativeTyped : ∀ p ∈ rotationNegative,
    IsRotation (occurrenceValue s p.1) ∧
      IsRotation (occurrenceValue s p.2)
  reflectionPositiveTyped : ∀ p ∈ reflectionPositive,
    ¬IsRotation (occurrenceValue s p.1) ∧
      ¬IsRotation (occurrenceValue s p.2)
  reflectionNegativeTyped : ∀ p ∈ reflectionNegative,
    ¬IsRotation (occurrenceValue s p.1) ∧
      ¬IsRotation (occurrenceValue s p.2)
  endpointsNodup :
    (pairCoordinates rotationPositive ++
      pairCoordinates rotationNegative ++
      pairCoordinates reflectionPositive ++
      pairCoordinates reflectionNegative).Nodup
  weightedPairSum_eq_zero :
    ((occurrenceCoordinatePairs s rotationPositive).map
        fun pair => pair.1 + pair.2).sum -
      ((occurrenceCoordinatePairs s rotationNegative).map
        fun pair => pair.1 + pair.2).sum +
      ((occurrenceCoordinatePairs s reflectionPositive).map
        fun pair => pair.1 - pair.2).sum -
      ((occurrenceCoordinatePairs s reflectionNegative).map
        fun pair => pair.1 - pair.2).sum = 0

def SignedOccurrencePairSelection.endpointList
    {s : List (Group A)} {q : ℕ}
    (h : SignedOccurrencePairSelection s q) : List (Occurrence s) :=
  pairCoordinates h.rotationPositive ++
    pairCoordinates h.rotationNegative ++
    pairCoordinates h.reflectionPositive ++
    pairCoordinates h.reflectionNegative

noncomputable def SignedOccurrencePairSelection.selection
    {s : List (Group A)} {q : ℕ}
    (h : SignedOccurrencePairSelection s q) : Selection s := by
  classical
  exact h.endpointList.toFinset

theorem selectedMultiset_toFinset_of_nodup
    (s : List (Group A)) (xs : List (Occurrence s)) (hxs : xs.Nodup) :
    selectedMultiset s xs.toFinset =
      Multiset.ofList (xs.map (occurrenceValue s)) := by
  classical
  unfold selectedMultiset
  rw [List.toFinset_val, List.dedup_eq_self.mpr hxs]
  rfl

theorem multiset_pairCoordinates_eq_first_add_second
    (pairs : List (A × A)) :
    Multiset.ofList (pairCoordinates pairs) =
      Multiset.ofList (pairs.map Prod.fst) +
        Multiset.ofList (pairs.map Prod.snd) := by
  induction pairs with
  | nil => simp [pairCoordinates]
  | cons p pairs ih =>
      rcases p with ⟨x, y⟩
      change (x ::ₘ y ::ₘ Multiset.ofList (pairCoordinates pairs)) =
        (x ::ₘ Multiset.ofList (pairs.map Prod.fst)) +
          (y ::ₘ Multiset.ofList (pairs.map Prod.snd))
      rw [ih]
      simp only [← Multiset.singleton_add]
      ac_rfl

theorem multiset_reflectionPairCoordinates_eq_signed
    (positive negative : List (A × A)) :
    Multiset.ofList ((pairCoordinates positive).map (data A).refl) +
        Multiset.ofList ((pairCoordinates negative).map (data A).refl) =
      Multiset.ofList
          ((reflectionPlusCoordinates positive negative).map (data A).refl) +
        Multiset.ofList
          ((reflectionMinusCoordinates positive negative).map (data A).refl) := by
  have hpositive := congrArg (Multiset.map (data A).refl)
    (multiset_pairCoordinates_eq_first_add_second positive)
  have hnegative := congrArg (Multiset.map (data A).refl)
    (multiset_pairCoordinates_eq_first_add_second negative)
  simp only [Multiset.map_coe, Multiset.map_add, List.map_map] at hpositive hnegative
  rw [hpositive, hnegative]
  simp only [reflectionPlusCoordinates, reflectionMinusCoordinates,
    List.map_append, ← Multiset.coe_add]
  simp only [List.map_map, Function.comp_def]
  ac_rfl

theorem map_occurrenceValue_pairCoordinates_eq_rot
    (s : List (Group A))
    (pairs : List (Occurrence s × Occurrence s))
    (htyped : ∀ p ∈ pairs,
      IsRotation (occurrenceValue s p.1) ∧
        IsRotation (occurrenceValue s p.2)) :
    (pairCoordinates pairs).map (occurrenceValue s) =
      (pairCoordinates (occurrenceCoordinatePairs s pairs)).map (data A).rot := by
  induction pairs with
  | nil => simp [pairCoordinates, occurrenceCoordinatePairs]
  | cons p pairs ih =>
      have hp := htyped p (by simp)
      have htail : ∀ q ∈ pairs,
          IsRotation (occurrenceValue s q.1) ∧
            IsRotation (occurrenceValue s q.2) := by
        intro q hq
        exact htyped q (by simp [hq])
      rcases p with ⟨i, j⟩
      have hi : occurrenceValue s i =
          (data A).rot (coordinate (occurrenceValue s i)) :=
        eq_rotation_coordinate_of_isRotation _ hp.1
      have hj : occurrenceValue s j =
          (data A).rot (coordinate (occurrenceValue s j)) :=
        eq_rotation_coordinate_of_isRotation _ hp.2
      calc
        (pairCoordinates ((i, j) :: pairs)).map (occurrenceValue s) =
            occurrenceValue s i :: occurrenceValue s j ::
              (pairCoordinates pairs).map (occurrenceValue s) := rfl
        _ = (data A).rot (coordinate (occurrenceValue s i)) ::
              (data A).rot (coordinate (occurrenceValue s j)) ::
              (pairCoordinates (occurrenceCoordinatePairs s pairs)).map
                (data A).rot := by
              exact congrArg₂ List.cons hi
                (congrArg₂ List.cons hj (ih htail))
        _ = (pairCoordinates
              (occurrenceCoordinatePairs s ((i, j) :: pairs))).map
                (data A).rot := by
              simp [occurrenceCoordinatePairs, pairCoordinates]

theorem map_occurrenceValue_pairCoordinates_eq_refl
    (s : List (Group A))
    (pairs : List (Occurrence s × Occurrence s))
    (htyped : ∀ p ∈ pairs,
      ¬IsRotation (occurrenceValue s p.1) ∧
        ¬IsRotation (occurrenceValue s p.2)) :
    (pairCoordinates pairs).map (occurrenceValue s) =
      (pairCoordinates (occurrenceCoordinatePairs s pairs)).map (data A).refl := by
  induction pairs with
  | nil => simp [pairCoordinates, occurrenceCoordinatePairs]
  | cons p pairs ih =>
      have hp := htyped p (by simp)
      have htail : ∀ q ∈ pairs,
          ¬IsRotation (occurrenceValue s q.1) ∧
            ¬IsRotation (occurrenceValue s q.2) := by
        intro q hq
        exact htyped q (by simp [hq])
      rcases p with ⟨i, j⟩
      have hi : occurrenceValue s i =
          (data A).refl (coordinate (occurrenceValue s i)) :=
        eq_refl_coordinate_of_not_isRotation _ hp.1
      have hj : occurrenceValue s j =
          (data A).refl (coordinate (occurrenceValue s j)) :=
        eq_refl_coordinate_of_not_isRotation _ hp.2
      calc
        (pairCoordinates ((i, j) :: pairs)).map (occurrenceValue s) =
            occurrenceValue s i :: occurrenceValue s j ::
              (pairCoordinates pairs).map (occurrenceValue s) := rfl
        _ = (data A).refl (coordinate (occurrenceValue s i)) ::
              (data A).refl (coordinate (occurrenceValue s j)) ::
              (pairCoordinates (occurrenceCoordinatePairs s pairs)).map
                (data A).refl := by
              exact congrArg₂ List.cons hi
                (congrArg₂ List.cons hj (ih htail))
        _ = (pairCoordinates
              (occurrenceCoordinatePairs s ((i, j) :: pairs))).map
                (data A).refl := by
              simp [occurrenceCoordinatePairs, pairCoordinates]

def SignedOccurrencePairSelection.toBalancedSignedPairAssignment
    {s : List (Group A)} {q : ℕ}
    (h : SignedOccurrencePairSelection s q) :
    BalancedSignedPairAssignment (selectedMultiset s h.selection) q where
  rotationPositive := occurrenceCoordinatePairs s h.rotationPositive
  rotationNegative := occurrenceCoordinatePairs s h.rotationNegative
  reflectionPositive := occurrenceCoordinatePairs s h.reflectionPositive
  reflectionNegative := occurrenceCoordinatePairs s h.reflectionNegative
  pairCount_eq := by simpa [occurrenceCoordinatePairs] using h.pairCount_eq
  reflectionPairsNonempty := by
    simpa [occurrenceCoordinatePairs] using h.reflectionPairsNonempty
  carrier_eq := by
    classical
    change selectedMultiset s h.endpointList.toFinset = _
    rw [selectedMultiset_toFinset_of_nodup s h.endpointList h.endpointsNodup]
    simp only [SignedOccurrencePairSelection.endpointList, List.map_append]
    rw [map_occurrenceValue_pairCoordinates_eq_rot s h.rotationPositive
        h.rotationPositiveTyped,
      map_occurrenceValue_pairCoordinates_eq_rot s h.rotationNegative
        h.rotationNegativeTyped,
      map_occurrenceValue_pairCoordinates_eq_refl s h.reflectionPositive
        h.reflectionPositiveTyped,
      map_occurrenceValue_pairCoordinates_eq_refl s h.reflectionNegative
        h.reflectionNegativeTyped]
    simp only [← Multiset.coe_add]
    let rp : Multiset (Group A) := Multiset.ofList
      ((pairCoordinates (occurrenceCoordinatePairs s h.rotationPositive)).map
        (data A).rot)
    let rn : Multiset (Group A) := Multiset.ofList
      ((pairCoordinates (occurrenceCoordinatePairs s h.rotationNegative)).map
        (data A).rot)
    let fp : Multiset (Group A) := Multiset.ofList
      ((pairCoordinates (occurrenceCoordinatePairs s h.reflectionPositive)).map
        (data A).refl)
    let fn : Multiset (Group A) := Multiset.ofList
      ((pairCoordinates (occurrenceCoordinatePairs s h.reflectionNegative)).map
        (data A).refl)
    let fsPlus : Multiset (Group A) := Multiset.ofList
      ((reflectionPlusCoordinates
        (occurrenceCoordinatePairs s h.reflectionPositive)
        (occurrenceCoordinatePairs s h.reflectionNegative)).map (data A).refl)
    let fsMinus : Multiset (Group A) := Multiset.ofList
      ((reflectionMinusCoordinates
        (occurrenceCoordinatePairs s h.reflectionPositive)
        (occurrenceCoordinatePairs s h.reflectionNegative)).map (data A).refl)
    change rp + rn + fp + fn = rp + rn + fsPlus + fsMinus
    have hreflect : fp + fn = fsPlus + fsMinus :=
      multiset_reflectionPairCoordinates_eq_signed _ _
    calc
      rp + rn + fp + fn = (rp + rn) + (fp + fn) := by ac_rfl
      _ = (rp + rn) + (fsPlus + fsMinus) := by rw [hreflect]
      _ = rp + rn + fsPlus + fsMinus := by ac_rfl
  weightedPairSum_eq_zero := h.weightedPairSum_eq_zero

/-- The occurrence-labelled high-reflection endpoint: signed selection of
exactly `q` disjoint same-type pairs gives an exact `2q` product-one block. -/
theorem hasProductOneSubsequenceOfTwice_of_signedOccurrencePairSelection
    (s : List (Group A)) (q : ℕ)
    (h : SignedOccurrencePairSelection s q) :
    HasProductOneSubsequenceOfCard s (2 * q) :=
  hasProductOneSubsequenceOfTwice_of_balancedSignedPairAssignment
    s h.selection q h.toBalancedSignedPairAssignment

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.eq_refl_coordinate_of_not_isRotation
#print axioms GaoLean.ConcreteGDihedral.selectedMultiset_toFinset_of_nodup
#print axioms GaoLean.ConcreteGDihedral.SignedOccurrencePairSelection.toBalancedSignedPairAssignment
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_signedOccurrencePairSelection
