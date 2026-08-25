import GaoLean.PGHighReflection

/-!
# Middle-reflection full-spectrum consumer

This file closes the occurrence and ordering obligations in A-R6 Section 4.3
after the weighted full-spectrum branch has supplied signed rotations that
cancel a positive even balanced reflection selection.  It does not assert the
GMO full-spectrum output.
-/

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Coordinates of a list of actual source positions. -/
def occurrenceCoordinates (s : List (Group A))
    (xs : List (Occurrence s)) : List A :=
  xs.map fun i => coordinate (occurrenceValue s i)

theorem map_occurrenceValue_eq_rot
    (s : List (Group A)) (xs : List (Occurrence s))
    (htyped : ∀ i ∈ xs, IsRotation (occurrenceValue s i)) :
    xs.map (occurrenceValue s) =
      (occurrenceCoordinates s xs).map (data A).rot := by
  induction xs with
  | nil => simp [occurrenceCoordinates]
  | cons i xs ih =>
      have hi : occurrenceValue s i =
          (data A).rot (coordinate (occurrenceValue s i)) :=
        eq_rotation_coordinate_of_isRotation _ (htyped i (by simp))
      have htail : ∀ j ∈ xs, IsRotation (occurrenceValue s j) := by
        intro j hj
        exact htyped j (by simp [hj])
      simp only [List.map_cons, occurrenceCoordinates]
      exact congrArg₂ List.cons hi (ih htail)

theorem map_occurrenceValue_eq_refl
    (s : List (Group A)) (xs : List (Occurrence s))
    (htyped : ∀ i ∈ xs, ¬IsRotation (occurrenceValue s i)) :
    xs.map (occurrenceValue s) =
      (occurrenceCoordinates s xs).map (data A).refl := by
  induction xs with
  | nil => simp [occurrenceCoordinates]
  | cons i xs ih =>
      have hi : occurrenceValue s i =
          (data A).refl (coordinate (occurrenceValue s i)) :=
        eq_refl_coordinate_of_not_isRotation _ (htyped i (by simp))
      have htail : ∀ j ∈ xs, ¬IsRotation (occurrenceValue s j) := by
        intro j hj
        exact htyped j (by simp [hj])
      simp only [List.map_cons, occurrenceCoordinates]
      exact congrArg₂ List.cons hi (ih htail)

/-- A balanced occurrence-labelled reflection choice, before the rotation
full-spectrum output is applied. -/
structure BalancedReflectionOccurrenceChoice
    (s : List (Group A)) (e : ℕ) where
  reflectionPlus : List (Occurrence s)
  reflectionMinus : List (Occurrence s)
  reflectionPlusLength : reflectionPlus.length = e / 2
  reflectionMinusLength : reflectionMinus.length = e / 2
  endpointsNodup : (reflectionPlus ++ reflectionMinus).Nodup
  reflectionPlusTyped : ∀ i ∈ reflectionPlus,
    ¬IsRotation (occurrenceValue s i)
  reflectionMinusTyped : ∀ i ∈ reflectionMinus,
    ¬IsRotation (occurrenceValue s i)

/-- Any available positive even number of reflection occurrences can be
chosen and split into equal plus/minus sign classes without reusing a source
position. -/
theorem exists_balancedReflectionOccurrenceChoice
    (s : List (Group A)) (e : ℕ)
    (heven : Even e) (he2 : 2 ≤ e)
    (hcapacity : e ≤ (reflectionOccurrences s).card) :
    ∃ c : BalancedReflectionOccurrenceChoice s e,
      c.reflectionPlus ≠ [] := by
  classical
  obtain ⟨J, hJ, hJcard⟩ := Finset.exists_subset_card_eq hcapacity
  let xs : List (Occurrence s) := J.toList
  let plus : List (Occurrence s) := xs.take (e / 2)
  let minus : List (Occurrence s) := xs.drop (e / 2)
  have hxsLength : xs.length = e := by
    simpa [xs] using hJcard
  have hsplit : plus ++ minus = xs := by
    simpa [plus, minus] using List.take_append_drop (e / 2) xs
  have hplusLength : plus.length = e / 2 := by
    simp [plus, hxsLength]
    omega
  have hminusLength : minus.length = e / 2 := by
    rcases heven with ⟨k, hk⟩
    simp [minus, hxsLength]
    omega
  have htyped : ∀ i ∈ xs,
      ¬IsRotation (occurrenceValue s i) := by
    intro i hi
    have hiJ : i ∈ J := Finset.mem_toList.mp (by simpa [xs] using hi)
    have hiReflection : i ∈ reflectionOccurrences s := hJ hiJ
    simpa [reflectionOccurrences] using hiReflection
  let c : BalancedReflectionOccurrenceChoice s e := {
    reflectionPlus := plus
    reflectionMinus := minus
    reflectionPlusLength := hplusLength
    reflectionMinusLength := hminusLength
    endpointsNodup := by
      rw [hsplit]
      exact J.nodup_toList
    reflectionPlusTyped := by
      intro i hi
      apply htyped i
      rw [← hsplit]
      exact List.mem_append_left _ hi
    reflectionMinusTyped := by
      intro i hi
      apply htyped i
      rw [← hsplit]
      exact List.mem_append_right _ hi
  }
  refine ⟨c, ?_⟩
  intro hnil
  have hzero : plus.length = 0 := by simp [c] at hnil; simp [hnil]
  omega

/-- In the middle regime, `e=pairedReflectionCount a` always admits the
balanced occurrence choice required by the full-spectrum branch. -/
theorem exists_balancedReflectionOccurrenceChoice_middle
    (s : List (Group A)) (a : ℕ)
    (ha2 : 2 ≤ a)
    (hreflectionCount : (reflectionOccurrences s).card = a) :
    ∃ c : BalancedReflectionOccurrenceChoice s (pairedReflectionCount a),
      c.reflectionPlus ≠ [] := by
  apply exists_balancedReflectionOccurrenceChoice
  · exact pairedReflectionCount_even a
  · exact (pairedReflectionCount_bounds ha2).1
  · rw [hreflectionCount]
    exact (pairedReflectionCount_bounds ha2).2.1

/-- Exact occurrence-labelled output consumed from the middle full-spectrum
branch.  Repeated group values remain distinct because all four lists contain
source positions and their concatenation is `Nodup`. -/
structure MiddleFullSpectrumOutput
    (s : List (Group A)) (Q D a : ℕ) where
  rotationPlus : List (Occurrence s)
  rotationMinus : List (Occurrence s)
  reflectionPlus : List (Occurrence s)
  reflectionMinus : List (Occurrence s)
  endpointsNodup :
    (rotationPlus ++ rotationMinus ++
      reflectionPlus ++ reflectionMinus).Nodup
  rotationPlusTyped : ∀ i ∈ rotationPlus,
    IsRotation (occurrenceValue s i)
  rotationMinusTyped : ∀ i ∈ rotationMinus,
    IsRotation (occurrenceValue s i)
  reflectionPlusTyped : ∀ i ∈ reflectionPlus,
    ¬IsRotation (occurrenceValue s i)
  reflectionMinusTyped : ∀ i ∈ reflectionMinus,
    ¬IsRotation (occurrenceValue s i)
  reflectionLengthEq : reflectionPlus.length = reflectionMinus.length
  reflectionPlusNonempty : reflectionPlus ≠ []
  rotationCount_eq :
    rotationPlus.length + rotationMinus.length = middleRotationTarget Q a
  reflectionCount_eq :
    reflectionPlus.length + reflectionMinus.length = pairedReflectionCount a
  signedSum_eq_zero :
    (occurrenceCoordinates s rotationPlus).sum -
        (occurrenceCoordinates s rotationMinus).sum +
      (occurrenceCoordinates s reflectionPlus).sum -
        (occurrenceCoordinates s reflectionMinus).sum = 0

def MiddleFullSpectrumOutput.endpointList
    {s : List (Group A)} {Q D a : ℕ}
    (h : MiddleFullSpectrumOutput s Q D a) : List (Occurrence s) :=
  h.rotationPlus ++ h.rotationMinus ++
    h.reflectionPlus ++ h.reflectionMinus

noncomputable def MiddleFullSpectrumOutput.selection
    {s : List (Group A)} {Q D a : ℕ}
    (h : MiddleFullSpectrumOutput s Q D a) : Selection s := by
  classical
  exact h.endpointList.toFinset

/-- The full-spectrum occurrence output is an exact instance of the checked
balanced literal-ordering interface. -/
def MiddleFullSpectrumOutput.toBalancedSignedAssignment
    {s : List (Group A)} {Q D a : ℕ}
    (h : MiddleFullSpectrumOutput s Q D a) :
    BalancedSignedAssignment (selectedMultiset s h.selection) where
  rotationPlus := occurrenceCoordinates s h.rotationPlus
  rotationMinus := occurrenceCoordinates s h.rotationMinus
  reflectionPlus := occurrenceCoordinates s h.reflectionPlus
  reflectionMinus := occurrenceCoordinates s h.reflectionMinus
  reflectionLengthEq := by
    simpa [occurrenceCoordinates] using h.reflectionLengthEq
  reflectionPlusNonempty := by
    simpa [occurrenceCoordinates] using h.reflectionPlusNonempty
  carrier_eq := by
    classical
    change selectedMultiset s h.endpointList.toFinset = _
    rw [selectedMultiset_toFinset_of_nodup s h.endpointList h.endpointsNodup]
    simp only [MiddleFullSpectrumOutput.endpointList, List.map_append]
    rw [map_occurrenceValue_eq_rot s h.rotationPlus h.rotationPlusTyped,
      map_occurrenceValue_eq_rot s h.rotationMinus h.rotationMinusTyped,
      map_occurrenceValue_eq_refl s h.reflectionPlus h.reflectionPlusTyped,
      map_occurrenceValue_eq_refl s h.reflectionMinus h.reflectionMinusTyped]
    simp only [← Multiset.coe_add]
  signedSum_eq_zero := h.signedSum_eq_zero

/-- The middle arithmetic package gives the exact cardinality of the selected
occurrence set. -/
theorem MiddleFullSpectrumOutput.card_selection
    {s : List (Group A)} {Q D a : ℕ}
    (h : MiddleFullSpectrumOutput s Q D a)
    (hDQ : D ≤ Q) (ha2 : 2 ≤ a) (haD : a ≤ D) :
    h.selection.card = 2 * Q := by
  classical
  have hbook := middle_target_bookkeeping hDQ ha2 haD
  dsimp only at hbook
  change (h.rotationPlus ++ h.rotationMinus ++
    h.reflectionPlus ++ h.reflectionMinus).toFinset.card = 2 * Q
  rw [List.toFinset_card_of_nodup h.endpointsNodup]
  simp only [List.length_append]
  rw [h.rotationCount_eq]
  have hrefCount := h.reflectionCount_eq
  omega

/-- Complete internal middle full-spectrum closure to an exact `2Q`
product-one occurrence block. -/
theorem hasProductOneSubsequenceOfTwice_of_middleFullSpectrumOutput
    (s : List (Group A)) (Q D a : ℕ)
    (hDQ : D ≤ Q) (ha2 : 2 ≤ a) (haD : a ≤ D)
    (h : MiddleFullSpectrumOutput s Q D a) :
    HasProductOneSubsequenceOfCard s (2 * Q) :=
  hasProductOneSubsequenceOfCard_of_balancedSignedAssignment
    s h.selection (2 * Q) (h.card_selection hDQ ha2 haD)
      h.toBalancedSignedAssignment

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.map_occurrenceValue_eq_rot
#print axioms GaoLean.ConcreteGDihedral.map_occurrenceValue_eq_refl
#print axioms GaoLean.ConcreteGDihedral.exists_balancedReflectionOccurrenceChoice
#print axioms GaoLean.ConcreteGDihedral.exists_balancedReflectionOccurrenceChoice_middle
#print axioms GaoLean.ConcreteGDihedral.MiddleFullSpectrumOutput.toBalancedSignedAssignment
#print axioms GaoLean.ConcreteGDihedral.MiddleFullSpectrumOutput.card_selection
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_middleFullSpectrumOutput
