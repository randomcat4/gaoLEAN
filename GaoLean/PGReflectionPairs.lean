import GaoLean.PGReflectionOrdering

/-!
# Signed pair output to balanced literal ordering

This file formalizes the elementary post-processing in the high-reflection
branch of A-R6 Section 4.2.  A positive-weight reflection pair `(x,y)`
contributes `x` to the plus class and `y` to the minus class; a negative-weight
pair is reversed.  Rotation pairs put both coordinates in their weight class.
All carrier equalities are multiset equalities, so occurrences are not reused.
-/

namespace GaoLean
namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A]

/-- Flatten ordered coordinate pairs without forgetting multiplicity. -/
def pairCoordinates : List (A × A) → List A
  | [] => []
  | (x, y) :: pairs => x :: y :: pairCoordinates pairs

def reflectionPlusCoordinates
    (positivePairs negativePairs : List (A × A)) : List A :=
  positivePairs.map Prod.fst ++ negativePairs.map Prod.snd

def reflectionMinusCoordinates
    (positivePairs negativePairs : List (A × A)) : List A :=
  positivePairs.map Prod.snd ++ negativePairs.map Prod.fst

@[simp]
theorem length_pairCoordinates (pairs : List (A × A)) :
    (pairCoordinates pairs).length = 2 * pairs.length := by
  induction pairs with
  | nil => simp [pairCoordinates]
  | cons pair pairs ih =>
      rcases pair with ⟨x, y⟩
      simp [pairCoordinates, ih, Nat.mul_add]

theorem sum_pairCoordinates (pairs : List (A × A)) :
    (pairCoordinates pairs).sum =
      (pairs.map fun pair => pair.1 + pair.2).sum := by
  induction pairs with
  | nil => simp [pairCoordinates]
  | cons pair pairs ih =>
      rcases pair with ⟨x, y⟩
      simp [pairCoordinates, ih, add_assoc]

theorem sum_first_sub_sum_second (pairs : List (A × A)) :
    (pairs.map Prod.fst).sum - (pairs.map Prod.snd).sum =
      (pairs.map fun pair => pair.1 - pair.2).sum := by
  induction pairs with
  | nil => simp
  | cons pair pairs ih =>
      rcases pair with ⟨x, y⟩
      simp only [List.map_cons, List.sum_cons]
      rw [← ih]
      abel

theorem length_reflectionPlusCoordinates
    (positivePairs negativePairs : List (A × A)) :
    (reflectionPlusCoordinates positivePairs negativePairs).length =
      positivePairs.length + negativePairs.length := by
  simp [reflectionPlusCoordinates]

theorem length_reflectionMinusCoordinates
    (positivePairs negativePairs : List (A × A)) :
    (reflectionMinusCoordinates positivePairs negativePairs).length =
      positivePairs.length + negativePairs.length := by
  simp [reflectionMinusCoordinates]

theorem reflectionPlusCoordinates_ne_nil
    (positivePairs negativePairs : List (A × A))
    (hnonempty : positivePairs ≠ [] ∨ negativePairs ≠ []) :
    reflectionPlusCoordinates positivePairs negativePairs ≠ [] := by
  rcases hnonempty with hpositive | hnegative
  · cases positivePairs with
    | nil => exact False.elim (hpositive rfl)
    | cons pair pairs =>
        rcases pair with ⟨x, y⟩
        simp [reflectionPlusCoordinates]
  · cases negativePairs with
    | nil => exact False.elim (hnegative rfl)
    | cons pair pairs =>
        rcases pair with ⟨x, y⟩
        simp [reflectionPlusCoordinates]

theorem signedCoordinateSum_eq_weightedPairSum
    (rotationPositive rotationNegative reflectionPositive reflectionNegative :
      List (A × A)) :
    (pairCoordinates rotationPositive).sum -
        (pairCoordinates rotationNegative).sum +
        (reflectionPlusCoordinates reflectionPositive reflectionNegative).sum -
        (reflectionMinusCoordinates reflectionPositive reflectionNegative).sum =
      (rotationPositive.map fun pair => pair.1 + pair.2).sum -
        (rotationNegative.map fun pair => pair.1 + pair.2).sum +
        (reflectionPositive.map fun pair => pair.1 - pair.2).sum -
        (reflectionNegative.map fun pair => pair.1 - pair.2).sum := by
  rw [sum_pairCoordinates, sum_pairCoordinates]
  simp only [reflectionPlusCoordinates, reflectionMinusCoordinates,
    List.sum_append]
  rw [← sum_first_sub_sum_second reflectionPositive,
    ← sum_first_sub_sum_second reflectionNegative]
  abel

/-- Exact occurrence-sensitive signed-pair output of the high-reflection GMO
step.  `pairCount_eq` freezes the prescribed number of selected pairs. -/
structure BalancedSignedPairAssignment
    (S : Multiset (Group A)) (q : ℕ) where
  rotationPositive : List (A × A)
  rotationNegative : List (A × A)
  reflectionPositive : List (A × A)
  reflectionNegative : List (A × A)
  pairCount_eq :
    rotationPositive.length + rotationNegative.length +
      reflectionPositive.length + reflectionNegative.length = q
  reflectionPairsNonempty :
    reflectionPositive ≠ [] ∨ reflectionNegative ≠ []
  carrier_eq :
    S = Multiset.ofList
          ((pairCoordinates rotationPositive).map (data A).rot) +
        Multiset.ofList
          ((pairCoordinates rotationNegative).map (data A).rot) +
        Multiset.ofList
          ((reflectionPlusCoordinates reflectionPositive reflectionNegative).map
            (data A).refl) +
        Multiset.ofList
          ((reflectionMinusCoordinates reflectionPositive reflectionNegative).map
            (data A).refl)
  weightedPairSum_eq_zero :
    (rotationPositive.map fun pair => pair.1 + pair.2).sum -
        (rotationNegative.map fun pair => pair.1 + pair.2).sum +
        (reflectionPositive.map fun pair => pair.1 - pair.2).sum -
        (reflectionNegative.map fun pair => pair.1 - pair.2).sum = 0

def BalancedSignedPairAssignment.toBalancedSignedAssignment
    {S : Multiset (Group A)} {q : ℕ}
    (h : BalancedSignedPairAssignment S q) : BalancedSignedAssignment S where
  rotationPlus := pairCoordinates h.rotationPositive
  rotationMinus := pairCoordinates h.rotationNegative
  reflectionPlus :=
    reflectionPlusCoordinates h.reflectionPositive h.reflectionNegative
  reflectionMinus :=
    reflectionMinusCoordinates h.reflectionPositive h.reflectionNegative
  reflectionLengthEq := by
    rw [length_reflectionPlusCoordinates, length_reflectionMinusCoordinates]
  reflectionPlusNonempty :=
    reflectionPlusCoordinates_ne_nil _ _ h.reflectionPairsNonempty
  carrier_eq := h.carrier_eq
  signedSum_eq_zero := by
    rw [signedCoordinateSum_eq_weightedPairSum]
    exact h.weightedPairSum_eq_zero

theorem isProductOneSelection_of_balancedSignedPairAssignment
    (s : List (Group A)) (I : Selection s) (q : ℕ)
    (h : BalancedSignedPairAssignment (selectedMultiset s I) q) :
    IsProductOneSelection s I :=
  isProductOneSelection_of_balancedSignedAssignment s I
    h.toBalancedSignedAssignment

theorem card_selection_of_balancedSignedPairAssignment
    (s : List (Group A)) (I : Selection s) (q : ℕ)
    (h : BalancedSignedPairAssignment (selectedMultiset s I) q) :
    I.card = 2 * q := by
  rw [← card_selectedMultiset s I, h.carrier_eq]
  simp only [Multiset.card_add, Multiset.coe_card, List.length_map,
    length_pairCoordinates, length_reflectionPlusCoordinates,
    length_reflectionMinusCoordinates]
  have hcount := h.pairCount_eq
  omega

/-- A prescribed selection of `q` signed pairs, including a reflection pair,
gives an exact `2q`-term product-one subsequence. -/
theorem hasProductOneSubsequenceOfTwice_of_balancedSignedPairAssignment
    (s : List (Group A)) (I : Selection s) (q : ℕ)
    (h : BalancedSignedPairAssignment (selectedMultiset s I) q) :
    HasProductOneSubsequenceOfCard s (2 * q) := by
  exact ⟨I, card_selection_of_balancedSignedPairAssignment s I q h,
    isProductOneSelection_of_balancedSignedPairAssignment s I q h⟩

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.ConcreteGDihedral.signedCoordinateSum_eq_weightedPairSum
#print axioms GaoLean.ConcreteGDihedral.isProductOneSelection_of_balancedSignedPairAssignment
#print axioms GaoLean.ConcreteGDihedral.card_selection_of_balancedSignedPairAssignment
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_balancedSignedPairAssignment
