import GaoLean.PGPairSelection

/-!
# High-reflection prescribed-pair consumer

This file closes the internal part of A-R6 Section 4.2 after a prescribed-
length weighted selection has been supplied.  The selection is occurrence-
labelled and must come from the canonical same-type reservoir.  Its existence
is an explicit proposition parameter; no GMO theorem is asserted here.
-/

namespace GaoLean.ConcreteGDihedral

section GenericPairSelection

variable {α : Type*}

@[simp]
theorem pairCoordinates_append (xs ys : List (α × α)) :
    pairCoordinates (xs ++ ys) =
      pairCoordinates xs ++ pairCoordinates ys := by
  induction xs with
  | nil => simp [pairCoordinates]
  | cons p xs ih =>
      rcases p with ⟨x, y⟩
      simp [pairCoordinates, ih]

/-- Distinct flattened endpoints imply that the ordered pairs themselves are
distinct. -/
theorem nodup_pairs_of_pairCoordinates_nodup :
    ∀ pairs : List (α × α),
      (pairCoordinates pairs).Nodup → pairs.Nodup
  | [], _ => by simp
  | (x, y) :: pairs, h => by
      have h' : (x :: y :: pairCoordinates pairs).Nodup := by
        simpa [pairCoordinates] using h
      have hxNot : x ∉ y :: pairCoordinates pairs :=
        (List.nodup_cons.mp h').1
      have hrest : (pairCoordinates pairs).Nodup :=
        (List.nodup_cons.mp (List.nodup_cons.mp h').2).2
      apply List.nodup_cons.mpr
      refine ⟨?_, nodup_pairs_of_pairCoordinates_nodup pairs hrest⟩
      intro hp
      have hx : x ∈ pairCoordinates pairs :=
        fst_mem_pairCoordinates_of_mem hp
      exact hxNot (List.mem_cons_of_mem y hx)

/-- An occurrence-disjoint selection of pairs drawn from `source` cannot use
more pairs than the source reservoir contains.  Membership is on pairs of
source positions, not on their possibly repeated group values. -/
theorem length_pairLists_le_source
    (source xs ys : List (α × α))
    (hselected :
      (pairCoordinates xs ++ pairCoordinates ys).Nodup)
    (hxs : ∀ p ∈ xs, p ∈ source)
    (hys : ∀ p ∈ ys, p ∈ source) :
    xs.length + ys.length ≤ source.length := by
  classical
  have hpairs : (xs ++ ys).Nodup :=
    nodup_pairs_of_pairCoordinates_nodup _ (by
      simpa using hselected)
  have hsubset : (xs ++ ys).toFinset ⊆ source.toFinset := by
    intro p hp
    have hpList : p ∈ xs ++ ys := by simpa using hp
    rcases List.mem_append.mp hpList with hpx | hpy
    · simpa using hxs p hpx
    · simpa using hys p hpy
  have hcard := Finset.card_le_card hsubset
  calc
    xs.length + ys.length = (xs ++ ys).length := by simp
    _ = (xs ++ ys).toFinset.card :=
      (List.toFinset_card_of_nodup hpairs).symm
    _ ≤ source.toFinset.card := hcard
    _ ≤ source.length := List.toFinset_card_le source

end GenericPairSelection

section HighReflectionArithmetic

/-- The high-reflection hypothesis leaves at most `2Q-1` rotation
occurrences. -/
theorem highReflection_rotationCount_le {Q D a b : ℕ}
    (hQ : 0 < Q) (ha : D + 1 ≤ a)
    (htotal : a + b = 2 * Q + D) :
    b ≤ 2 * Q - 1 := by
  omega

/-- The plus-minus Davenport bound is exactly enough for the weighted GMO
length threshold in (4.1). -/
theorem highReflection_pairThreshold {Q D m : ℕ}
    (hD : Odd D) (hm : m ≤ (D + 1) / 2) :
    Q + m - 1 ≤ Q + (D - 1) / 2 := by
  rcases hD with ⟨k, hk⟩
  omega

end HighReflectionArithmetic

section PrescribedOutput

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact occurrence-labelled output expected from the weighted
prescribed-length theorem in the high-reflection branch.

The four lists are the selected canonical reservoir pairs, partitioned by
type and sign.  `endpointsNodup` is the selected-index condition: it prevents
reuse of a source occurrence.  This structure deliberately does not assert
that a reflection pair was selected; that fact is derived from the rotation
capacity bound below. -/
structure PrescribedSignedReservoirOutput
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

/-- The selection/index part of the weighted GMO output, separated from the
target-coset conclusion. -/
structure SignedReservoirSelectionData
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
  endpointsNodup :
    (pairCoordinates rotationPositive ++
      pairCoordinates rotationNegative ++
      pairCoordinates reflectionPositive ++
      pairCoordinates reflectionNegative).Nodup

/-- Statement-faithful raw weighted output: the selected signed pair-label sum
belongs to `q • A`.  Membership is encoded by an explicit witness `z` with
sum `= q • z`; it is not prematurely strengthened to sum zero. -/
structure PrescribedSignedReservoirTargetOutput
    (s : List (Group A)) (q : ℕ) where
  selection : SignedReservoirSelectionData s q
  weightedPairSum_mem_target : ∃ z : A,
    ((occurrenceCoordinatePairs s selection.rotationPositive).map
        fun pair => pair.1 + pair.2).sum -
      ((occurrenceCoordinatePairs s selection.rotationNegative).map
        fun pair => pair.1 + pair.2).sum +
      ((occurrenceCoordinatePairs s selection.reflectionPositive).map
        fun pair => pair.1 - pair.2).sum -
      ((occurrenceCoordinatePairs s selection.reflectionNegative).map
        fun pair => pair.1 - pair.2).sum = q • z

/-- When `q=|A|`, the target set `q • A` is `{0}`.  This is the internal
translation from GMO's target-coset conclusion to the zero-sum interface. -/
noncomputable def PrescribedSignedReservoirTargetOutput.toZeroOutput
    {s : List (Group A)} {q : ℕ}
    (h : PrescribedSignedReservoirTargetOutput s q)
    (hq : q = Nat.card A) :
    PrescribedSignedReservoirOutput s q := by
  classical
  let z : A := Classical.choose h.weightedPairSum_mem_target
  have hz := Classical.choose_spec h.weightedPairSum_mem_target
  refine {
    rotationPositive := h.selection.rotationPositive
    rotationNegative := h.selection.rotationNegative
    reflectionPositive := h.selection.reflectionPositive
    reflectionNegative := h.selection.reflectionNegative
    rotationPositiveFromReservoir :=
      h.selection.rotationPositiveFromReservoir
    rotationNegativeFromReservoir :=
      h.selection.rotationNegativeFromReservoir
    reflectionPositiveFromReservoir :=
      h.selection.reflectionPositiveFromReservoir
    reflectionNegativeFromReservoir :=
      h.selection.reflectionNegativeFromReservoir
    pairCount_eq := h.selection.pairCount_eq
    endpointsNodup := h.selection.endpointsNodup
    weightedPairSum_eq_zero := ?_
  }
  calc
    ((occurrenceCoordinatePairs s h.selection.rotationPositive).map
          fun pair => pair.1 + pair.2).sum -
        ((occurrenceCoordinatePairs s h.selection.rotationNegative).map
          fun pair => pair.1 + pair.2).sum +
        ((occurrenceCoordinatePairs s h.selection.reflectionPositive).map
          fun pair => pair.1 - pair.2).sum -
        ((occurrenceCoordinatePairs s h.selection.reflectionNegative).map
          fun pair => pair.1 - pair.2).sum = q • z := hz
    _ = 0 := by simpa [hq] using (card_nsmul_eq_zero' z)

/-- All internal obligations between the occurrence-labelled weighted GMO
output and `SignedOccurrencePairSelection` are discharged here.  In
particular, a reflection pair is forced rather than assumed. -/
noncomputable def PrescribedSignedReservoirOutput.toSignedOccurrencePairSelection
    {s : List (Group A)} {q : ℕ}
    (h : PrescribedSignedReservoirOutput s q)
    (hQ : 0 < q)
    (hrotationOccurrences :
      (rotationOccurrences s).card ≤ 2 * q - 1) :
    SignedOccurrencePairSelection s q := by
  classical
  let R := canonicalSameTypePairReservoir s
  have hrotEndpoints :
      (pairCoordinates h.rotationPositive ++
        pairCoordinates h.rotationNegative).Nodup := by
    have hall :
        ((pairCoordinates h.rotationPositive ++
            pairCoordinates h.rotationNegative) ++
          (pairCoordinates h.reflectionPositive ++
            pairCoordinates h.reflectionNegative)).Nodup := by
      simpa only [List.append_assoc] using h.endpointsNodup
    exact hall.of_append_left
  have hselectedRotationBound :
      h.rotationPositive.length + h.rotationNegative.length ≤
        R.rotationPairs.length := by
    exact length_pairLists_le_source R.rotationPairs
      h.rotationPositive h.rotationNegative hrotEndpoints
      h.rotationPositiveFromReservoir h.rotationNegativeFromReservoir
  have hreservoirRotationBound : R.rotationPairs.length ≤ q - 1 := by
    rw [R.rotationPairCount]
    omega
  refine {
    rotationPositive := h.rotationPositive
    rotationNegative := h.rotationNegative
    reflectionPositive := h.reflectionPositive
    reflectionNegative := h.reflectionNegative
    rotationPositiveFromReservoir := h.rotationPositiveFromReservoir
    rotationNegativeFromReservoir := h.rotationNegativeFromReservoir
    reflectionPositiveFromReservoir := h.reflectionPositiveFromReservoir
    reflectionNegativeFromReservoir := h.reflectionNegativeFromReservoir
    pairCount_eq := h.pairCount_eq
    reflectionPairsNonempty := ?_
    rotationPositiveTyped := ?_
    rotationNegativeTyped := ?_
    reflectionPositiveTyped := ?_
    reflectionNegativeTyped := ?_
    endpointsNodup := h.endpointsNodup
    weightedPairSum_eq_zero := h.weightedPairSum_eq_zero
  }
  · by_contra hnone
    simp only [not_or, not_not] at hnone
    rcases hnone with ⟨hpos, hneg⟩
    have hselectedCount :
        h.rotationPositive.length + h.rotationNegative.length = q := by
      simpa [hpos, hneg] using h.pairCount_eq
    omega
  · intro p hp
    exact R.rotationTyped p (h.rotationPositiveFromReservoir p hp)
  · intro p hp
    exact R.rotationTyped p (h.rotationNegativeFromReservoir p hp)
  · intro p hp
    exact R.reflectionTyped p (h.reflectionPositiveFromReservoir p hp)
  · intro p hp
    exact R.reflectionTyped p (h.reflectionNegativeFromReservoir p hp)

/-- Conditional high-reflection endpoint directly from the explicit weighted
reservoir output. -/
theorem hasProductOneSubsequenceOfTwice_of_prescribedSignedReservoirOutput
    (s : List (Group A)) (q : ℕ)
    (hQ : 0 < q)
    (hrotationOccurrences :
      (rotationOccurrences s).card ≤ 2 * q - 1)
    (h : PrescribedSignedReservoirOutput s q) :
    HasProductOneSubsequenceOfCard s (2 * q) :=
  hasProductOneSubsequenceOfTwice_of_signedOccurrencePairSelection s q
    (h.toSignedOccurrencePairSelection hQ hrotationOccurrences)

/-- Source-shaped high-reflection consumer.  The numerical hypothesis
`a ≥ D+1` supplies the forced-reflection bound; the only non-internal input is
the explicit prescribed signed reservoir output. -/
theorem hasProductOneSubsequenceOfTwice_of_highReflectionOutput
    (s : List (Group A)) (Q D a b : ℕ)
    (hQ : 0 < Q)
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hhigh : D + 1 ≤ a)
    (h : PrescribedSignedReservoirOutput s Q) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  have hhighActual : D + 1 ≤ (reflectionOccurrences s).card := by
    rw [hreflectionCount]
    exact hhigh
  have htotalActual :
      (reflectionOccurrences s).card + (rotationOccurrences s).card =
        2 * Q + D := by
    rw [hreflectionCount, hrotationCount]
    exact htotal
  have hrot : (rotationOccurrences s).card ≤ 2 * Q - 1 :=
    highReflection_rotationCount_le hQ hhighActual htotalActual
  exact hasProductOneSubsequenceOfTwice_of_prescribedSignedReservoirOutput
    s Q hQ hrot h

/-- Source-faithful high-reflection endpoint from GMO's actual `Q • A` target
output.  The annihilation `Q • A = {0}` is proved internally from
`Q = |A|`. -/
theorem hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput
    (s : List (Group A)) (Q D a b : ℕ)
    (hQ : 0 < Q)
    (hQcard : Q = Nat.card A)
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hhigh : D + 1 ≤ a)
    (h : PrescribedSignedReservoirTargetOutput s Q) :
    HasProductOneSubsequenceOfCard s (2 * Q) :=
  hasProductOneSubsequenceOfTwice_of_highReflectionOutput
    s Q D a b hQ hreflectionCount hrotationCount htotal hhigh
      (h.toZeroOutput hQcard)

/-- The complete internal readiness package for applying weighted GMO in the
high-reflection regime: enough reservoir pairs for the prescribed threshold,
and fewer than `Q` rotation pairs. -/
theorem canonicalSameTypePairReservoir_highReflection_ready
    (s : List (Group A)) (Q D a b m : ℕ)
    (hQ : 0 < Q)
    (hD : Odd D)
    (hreflectionCount : (reflectionOccurrences s).card = a)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hhigh : D + 1 ≤ a)
    (hpm : m ≤ (D + 1) / 2) :
    Q + m - 1 ≤
        (canonicalSameTypePairReservoir s).rotationPairs.length +
          (canonicalSameTypePairReservoir s).reflectionPairs.length ∧
      (canonicalSameTypePairReservoir s).rotationPairs.length ≤ Q - 1 := by
  have hcount := canonicalSameTypePairReservoir_pairCount_of_odd_total
    s hD hreflectionCount hrotationCount htotal
  have hb : b ≤ 2 * Q - 1 :=
    highReflection_rotationCount_le hQ hhigh htotal
  constructor
  · rw [hcount]
    exact highReflection_pairThreshold hD hpm
  · rw [(canonicalSameTypePairReservoir s).rotationPairCount,
      hrotationCount]
    omega

end PrescribedOutput

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.nodup_pairs_of_pairCoordinates_nodup
#print axioms GaoLean.ConcreteGDihedral.length_pairLists_le_source
#print axioms GaoLean.ConcreteGDihedral.highReflection_rotationCount_le
#print axioms GaoLean.ConcreteGDihedral.highReflection_pairThreshold
#print axioms GaoLean.ConcreteGDihedral.PrescribedSignedReservoirTargetOutput.toZeroOutput
#print axioms GaoLean.ConcreteGDihedral.PrescribedSignedReservoirOutput.toSignedOccurrencePairSelection
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_highReflectionOutput
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfTwice_of_highReflectionTargetOutput
#print axioms GaoLean.ConcreteGDihedral.canonicalSameTypePairReservoir_highReflection_ready
