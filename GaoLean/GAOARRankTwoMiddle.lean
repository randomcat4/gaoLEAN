import GaoLean.GAOARGMOInterfaces
import GaoLean.GAOARPlusMinusBounds
import GaoLean.PGMiddleAssembly
import GaoLean.PGOrdinaryGMOBridge
import GaoLean.PGSynthesis

/-!
# Rank-two middle-reflection GMO transport

This module transports the exact source-shaped `{+1,-1}` GMO alternative on
the rotation-coordinate list back to labelled occurrences of the original
generalized-dihedral sequence.  It does not assume the residual line
controller needed by the non-full branch.
-/

namespace GaoLean

open scoped BigOperators

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

omit [Fintype A] in
private theorem sum_map_finset_toList
    {X : Type*} (F : Finset X) (f : X → A) :
    (F.toList.map f).sum = ∑ x ∈ F, f x := by
  classical
  induction F using Finset.induction_on with
  | empty => simp
  | @insert x F hx ih => simp [hx]

/-- Image in the original source of a selection of the rotation-coordinate
sequence. -/
noncomputable def rotationSourceSelection
    (s : List (Group A))
    (I : Selection (rotationCoordinateSequence s)) : Selection s := by
  classical
  exact I.image (rotationSourceOccurrence s)

/-- The corresponding source occurrences, in the canonical finset order. -/
noncomputable def rotationSourceList
    (s : List (Group A))
    (I : Selection (rotationCoordinateSequence s)) : List (Occurrence s) :=
  (rotationSourceSelection s I).toList

omit [Fintype A] in
theorem card_rotationSourceSelection
    (s : List (Group A))
    (I : Selection (rotationCoordinateSequence s)) :
    (rotationSourceSelection s I).card = I.card := by
  classical
  rw [rotationSourceSelection,
    Finset.card_image_of_injective _ (rotationSourceOccurrence_injective s)]

omit [Fintype A] in
theorem length_rotationSourceList
    (s : List (Group A))
    (I : Selection (rotationCoordinateSequence s)) :
    (rotationSourceList s I).length = I.card := by
  classical
  simp [rotationSourceList, card_rotationSourceSelection]

omit [Fintype A] in
theorem rotationSourceList_typed
    (s : List (Group A))
    (I : Selection (rotationCoordinateSequence s)) :
    ∀ i ∈ rotationSourceList s I, IsRotation (occurrenceValue s i) := by
  classical
  intro i hi
  have hi' : i ∈ rotationSourceSelection s I :=
    Finset.mem_toList.mp (by simpa [rotationSourceList] using hi)
  rcases Finset.mem_image.mp hi' with ⟨j, hj, rfl⟩
  simpa [rotationOccurrences] using rotationSourceOccurrence_mem s j

omit [Fintype A] in
theorem sum_occurrenceCoordinates_rotationSourceList
    (s : List (Group A))
    (I : Selection (rotationCoordinateSequence s)) :
    (occurrenceCoordinates s (rotationSourceList s I)).sum =
      ∑ i ∈ I, occurrenceValue (rotationCoordinateSequence s) i := by
  classical
  unfold occurrenceCoordinates rotationSourceList rotationSourceSelection
  rw [sum_map_finset_toList]
  rw [Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro i hi
    exact (occurrenceValue_rotationCoordinateSequence s i).symm
  · intro i hi j hj hij
    exact rotationSourceOccurrence_injective s hij

omit [Fintype A] in
theorem disjoint_rotationSourceSelection
    (s : List (Group A))
    (I J : Selection (rotationCoordinateSequence s))
    (hIJ : Disjoint I J) :
    Disjoint (rotationSourceSelection s I) (rotationSourceSelection s J) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiI hiJ
  rcases Finset.mem_image.mp hiI with ⟨u, hu, hui⟩
  rcases Finset.mem_image.mp hiJ with ⟨v, hv, hvi⟩
  have huv : u = v := rotationSourceOccurrence_injective s (hui.trans hvi.symm)
  subst v
  exact Finset.disjoint_left.mp hIJ hu hv

omit [Fintype A] in
theorem middleSourceLists_endpoints_nodup
    (s : List (Group A)) (e : ℕ)
    (positive negative : Selection (rotationCoordinateSequence s))
    (hdisjoint : Disjoint positive negative)
    (c : BalancedReflectionOccurrenceChoice s e) :
    (rotationSourceList s positive ++ rotationSourceList s negative ++
      c.reflectionPlus ++ c.reflectionMinus).Nodup := by
  classical
  have hsourceDisjoint :=
    disjoint_rotationSourceSelection s positive negative hdisjoint
  have hlistDisjoint :
      (rotationSourceList s positive).Disjoint
        (rotationSourceList s negative) := by
    rw [List.disjoint_left]
    intro i hiP hiN
    exact Finset.disjoint_left.mp hsourceDisjoint
      (Finset.mem_toList.mp (by simpa [rotationSourceList] using hiP))
      (Finset.mem_toList.mp (by simpa [rotationSourceList] using hiN))
  have hrotNodup :
      (rotationSourceList s positive ++
        rotationSourceList s negative).Nodup :=
    (rotationSourceSelection s positive).nodup_toList.append
      (rotationSourceSelection s negative).nodup_toList hlistDisjoint
  have hcross :
      (rotationSourceList s positive ++ rotationSourceList s negative).Disjoint
        (c.reflectionPlus ++ c.reflectionMinus) := by
    rw [List.disjoint_left]
    intro i hiRot hiRef
    have hiRot' : IsRotation (occurrenceValue s i) := by
      rcases List.mem_append.mp hiRot with hi | hi
      · exact rotationSourceList_typed s positive i hi
      · exact rotationSourceList_typed s negative i hi
    have hiRef' : ¬ IsRotation (occurrenceValue s i) := by
      rcases List.mem_append.mp hiRef with hi | hi
      · exact c.reflectionPlusTyped i hi
      · exact c.reflectionMinusTyped i hi
    exact hiRef' hiRot'
  simpa [List.append_assoc] using
    hrotNodup.append c.endpointsNodup hcross

/-- Checked transport of the full-spectrum GMO witness, joined with a fixed
balanced reflection choice whose signed coordinate target it cancels. -/
noncomputable def MiddleFullSpectrumOutput.ofRotationSpectrum
    {s : List (Group A)} {Q D a : ℕ}
    (c : BalancedReflectionOccurrenceChoice s (pairedReflectionCount a))
    (hc : c.reflectionPlus ≠ [])
    (h : HasPlusMinusSumOfCard (rotationCoordinateSequence s)
      (middleRotationTarget Q a)
      (-((occurrenceCoordinates s c.reflectionPlus).sum -
        (occurrenceCoordinates s c.reflectionMinus).sum))) :
    MiddleFullSpectrumOutput s Q D a := by
  classical
  refine {
    rotationPlus := rotationSourceList s h.positive
    rotationMinus := rotationSourceList s h.negative
    reflectionPlus := c.reflectionPlus
    reflectionMinus := c.reflectionMinus
    endpointsNodup :=
      middleSourceLists_endpoints_nodup s (pairedReflectionCount a)
        h.positive h.negative h.disjoint c
    rotationPlusTyped := rotationSourceList_typed s h.positive
    rotationMinusTyped := rotationSourceList_typed s h.negative
    reflectionPlusTyped := c.reflectionPlusTyped
    reflectionMinusTyped := c.reflectionMinusTyped
    reflectionLengthEq := by
      rw [c.reflectionPlusLength, c.reflectionMinusLength]
    reflectionPlusNonempty := hc
    rotationCount_eq := ?_
    reflectionCount_eq := ?_
    signedSum_eq_zero := ?_
  }
  · rw [length_rotationSourceList, length_rotationSourceList]
    exact h.card_selected
  · rw [c.reflectionPlusLength, c.reflectionMinusLength]
    rcases pairedReflectionCount_even a with ⟨k, hk⟩
    omega
  · rw [sum_occurrenceCoordinates_rotationSourceList,
      sum_occurrenceCoordinates_rotationSourceList, h.weighted_sum]
    abel

/-- Checked transport of the non-full GMO concentration on the additive
rotation-coordinate list back to labelled rotations of the original source. -/
noncomputable def MiddleNonfullConcentrationOutput.ofRotationConcentration
    {s : List (Group A)} {b : ℕ}
    (hrotationCount : (rotationOccurrences s).card = b)
    (h : PlusMinusGMOConcentration (rotationCoordinateSequence s)) :
    MiddleNonfullConcentrationOutput s b h.K := by
  classical
  refine {
    concentrated := rotationSourceSelection s h.selected
    proper := h.strict
    card_lower := ?_
    rotations := ?_
    posNegSameCoset := ?_
  }
  · rw [card_rotationSourceSelection]
    simpa [rotationCoordinateSequence, hrotationCount] using h.card_lower
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    simpa [rotationOccurrences] using rotationSourceOccurrence_mem s j
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    refine ⟨h.beta, ?_, ?_⟩
    · rw [← occurrenceValue_rotationCoordinateSequence s j]
      exact h.positiveWeightCoset j hj
    · rw [← occurrenceValue_rotationCoordinateSequence s j]
      exact h.negativeWeightCoset j hj

/-- The exact structural GMO interface supplies precisely the full/non-full
alternative consumed by the existing middle-reflection assembly. -/
theorem middleSpectrumAlternative_of_plusMinusGMO
    (s : List (Group A)) (Q D a b d : ℕ)
    (ha2 : 2 ≤ a)
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (hcard : Nat.card A ≤ middleRotationTarget Q a)
    (hthreshold : middleRotationTarget Q a + d - 1 ≤ b)
    (hpm : PlusMinusDavenportAtMost A d)
    (hGMO : PlusMinusGMOStructuralProvider A) :
    MiddleSpectrumAlternative s Q D a b := by
  obtain ⟨c, hc⟩ :=
    exists_balancedReflectionOccurrenceChoice_middle
      s a ha2 hreflectionCount
  have hthreshold' : middleRotationTarget Q a + d - 1 ≤
      (rotationCoordinateSequence s).length := by
    simpa [rotationCoordinateSequence, hrotationCount] using hthreshold
  rcases hGMO (rotationCoordinateSequence s) (middleRotationTarget Q a) d
      hcard hpm hthreshold' with hfull | hnonfull
  · left
    let y : A :=
      -((occurrenceCoordinates s c.reflectionPlus).sum -
        (occurrenceCoordinates s c.reflectionMinus).sum)
    obtain ⟨hout⟩ := hfull y
    exact ⟨MiddleFullSpectrumOutput.ofRotationSpectrum c hc hout⟩
  · right
    rcases hnonfull with ⟨hout⟩
    exact ⟨hout.K,
      ⟨MiddleNonfullConcentrationOutput.ofRotationConcentration
        hrotationCount hout⟩⟩

/-- Rank-two numerical specialization of the exact middle GMO alternative.
The only remaining mathematical input is the named structural GMO provider;
the plus-minus Davenport bound and all occurrence transport are internal. -/
theorem rankTwo_middleSpectrumAlternative
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hGMO : PlusMinusGMOStructuralProvider (PrimeVectorSpace q 2))
    (s : List (PrimeVectorDihedral q 2))
    (hlen : s.length = 2 * q ^ 2 + 2 * (q - 1) + 1)
    (ha2 : 2 ≤ (reflectionOccurrences s).card)
    (haD : (reflectionOccurrences s).card ≤ 2 * (q - 1) + 1) :
    MiddleSpectrumAlternative s (q ^ 2) (2 * (q - 1) + 1)
      (reflectionOccurrences s).card (rotationOccurrences s).card := by
  let A := PrimeVectorSpace q 2
  let Q := q ^ 2
  let D := 2 * (q - 1) + 1
  let a := (reflectionOccurrences s).card
  let b := (rotationOccurrences s).card
  have hqpos : 0 < q := hqPrime.pos
  have hDQ : D ≤ Q := by
    have hq1 : 1 ≤ q := by omega
    have hsquare :
        2 * (q - 1) + 1 ≤ ((q - 1) + 1) ^ 2 := by
      nlinarith [sq_nonneg (q - 1)]
    simpa [D, Q, Nat.sub_add_cancel hq1] using hsquare
  have htotal : a + b = 2 * Q + D := by
    dsimp only [a, b]
    rw [card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
    simp [Q, D, Nat.add_assoc]
  have hbook := middle_target_bookkeeping hDQ ha2 haD
  dsimp only at hbook
  have hcardA : Nat.card A = Q := by
    simp [A, Q, PrimeVectorSpace]
  have hcard : Nat.card A ≤ middleRotationTarget Q a := by
    rw [hcardA]
    exact hbook.2.2.2.2.1
  have hthreshold : middleRotationTarget Q a + q - 1 ≤ b := by
    have haele : a ≤ pairedReflectionCount a + 1 :=
      hbook.2.2.2.1
    have heell : pairedReflectionCount a + middleRotationTarget Q a =
        2 * Q := hbook.2.2.2.2.2
    dsimp only [D] at htotal
    omega
  have hpm : PlusMinusDavenportAtMost A q :=
    primeRankTwo_plusMinusDavenportAtMost q hqPrime hqodd
  simpa only [A, Q, D, a, b] using
    middleSpectrumAlternative_of_plusMinusGMO
      s Q D a b q ha2 rfl rfl hcard hthreshold hpm hGMO

/-- The `K = 0` leaf of the non-full middle branch, using exactly the
manuscript's small-Davenport input and checked identity-padding theorem. -/
theorem hasProductOneSubsequenceOfTwice_of_middleNonfull_bot
    (s : List (Group A)) (Q D a b : ℕ)
    (hlen : s.length = 2 * Q + D)
    (hQ : Q = Nat.card A)
    (hDQ : D ≤ Q) (haD : a ≤ D)
    (htotal : a + b = 2 * Q + D)
    (hAodd : Odd (Nat.card A))
    (hsmall : SmallDavenportProductOneFreeAtMost (Group A) D)
    (h : MiddleNonfullConcentrationOutput s b ⊥) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  have hDb : D ≤ b - Q + 2 :=
    by omega
  exact rcStatement_bot_of_smallDavenport s Q D b hlen hQ hDb hsmall
    (h.rotationCapacity hAodd)

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.ConcreteGDihedral.sum_occurrenceCoordinates_rotationSourceList
#print axioms GaoLean.ConcreteGDihedral.MiddleFullSpectrumOutput.ofRotationSpectrum
#print axioms GaoLean.ConcreteGDihedral.MiddleNonfullConcentrationOutput.ofRotationConcentration
#print axioms GaoLean.ConcreteGDihedral.middleSpectrumAlternative_of_plusMinusGMO
#print axioms GaoLean.ConcreteGDihedral.rankTwo_middleSpectrumAlternative
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_middleNonfull_bot
