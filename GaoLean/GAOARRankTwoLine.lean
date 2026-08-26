import GaoLean.GAOARRankTwoMiddle
import GaoLean.GAOARRankTwoSubgroups
import GaoLean.GAOARDihedralBlocks

/-!
# Rank-two concentrated-line completion

This file develops the occurrence transport for rotations whose coordinates
lie in a fixed line `K`.  It starts with the manuscript's `s ≤ q` ordinary-GMO
leaf; the complementary rank-one quotient leaf is kept separate.
-/

namespace GaoLean

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Coordinates of the source rotations lying in `K`, valued in the subtype
group `K`. -/
noncomputable def rotationInCoordinateSequence
    (s : List (Group A)) (K : AddSubgroup A) : List K := by
  classical
  exact (rotationOccurrencesIn s K).attach.toList.map fun i =>
    ⟨coordinate (occurrenceValue s i.1),
      (Finset.mem_filter.mp i.2).2.2⟩

/-- Map a coordinate-list occurrence back to its exact source occurrence. -/
noncomputable def rotationInSourceOccurrence
    (s : List (Group A)) (K : AddSubgroup A) :
  Occurrence (rotationInCoordinateSequence s K) → Occurrence s := fun i =>
  ((rotationOccurrencesIn s K).attach.toList.get
    ⟨i.1, by simpa [rotationInCoordinateSequence] using i.2⟩).1

omit [Fintype A] in
theorem rotationInSourceOccurrence_injective
    (s : List (Group A)) (K : AddSubgroup A) :
    Function.Injective (rotationInSourceOccurrence s K) := by
  intro i j hij
  apply Fin.ext
  have hget :
      ((rotationOccurrencesIn s K).attach.toList.get
          ⟨i.1, by simpa [rotationInCoordinateSequence] using i.2⟩ =
        (rotationOccurrencesIn s K).attach.toList.get
          ⟨j.1, by simpa [rotationInCoordinateSequence] using j.2⟩) := by
    apply Subtype.ext
    exact hij
  have hidx := (rotationOccurrencesIn s K).attach.nodup_toList.injective_get hget
  exact congrArg
    (fun k : Fin (rotationOccurrencesIn s K).attach.toList.length => k.val)
    hidx

omit [Fintype A] in
theorem rotationInSourceOccurrence_mem
    (s : List (Group A)) (K : AddSubgroup A)
    (i : Occurrence (rotationInCoordinateSequence s K)) :
    rotationInSourceOccurrence s K i ∈ rotationOccurrencesIn s K := by
  exact ((rotationOccurrencesIn s K).attach.toList.get _).2

omit [Fintype A] in
theorem occurrenceValue_rotationInCoordinateSequence
    (s : List (Group A)) (K : AddSubgroup A)
    (i : Occurrence (rotationInCoordinateSequence s K)) :
    ((occurrenceValue (rotationInCoordinateSequence s K) i : K) : A) =
      coordinate (occurrenceValue s (rotationInSourceOccurrence s K i)) := by
  simp [rotationInCoordinateSequence, rotationInSourceOccurrence,
    occurrenceValue, List.get_eq_getElem]

/-- Transport an ordinary prescribed-length GMO output on the line back to
the original source as the existing low-reflection target certificate. -/
noncomputable def LowReflectionTargetOutput.ofLineOrdinaryGMOTargetOutput
    {s : List (Group A)} {K : AddSubgroup A} {Q : ℕ}
    (h : OrdinaryGMOTargetOutput (rotationInCoordinateSequence s K) (2 * Q)) :
    LowReflectionTargetOutput s Q := by
  classical
  let selected : Selection s :=
    h.selected.image (rotationInSourceOccurrence s K)
  refine {
    selected := selected
    selectedRotations := ?_
    card_selected := ?_
    coordinateSum_mem_target := ?_
  }
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    simpa [rotationOccurrences] using
      (Finset.mem_filter.mp (rotationInSourceOccurrence_mem s K j)).2.1
  · rw [Finset.card_image_of_injective _
      (rotationInSourceOccurrence_injective s K), h.card_selected]
  · obtain ⟨z, hz⟩ := h.sum_mem_target
    refine ⟨(z : A), ?_⟩
    unfold coordinateSum
    have hsum :
        (∑ j ∈ h.selected,
            ((occurrenceValue (rotationInCoordinateSequence s K) j : K) : A)) =
          ∑ i ∈ selected, coordinate (occurrenceValue s i) := by
      refine Finset.sum_bij (fun j _ => rotationInSourceOccurrence s K j)
        ?_ ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · intro i hi j hj heq
        exact rotationInSourceOccurrence_injective s K heq
      · intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
      · intro j hj
        exact occurrenceValue_rotationInCoordinateSequence s K j
    rw [← hsum, ← AddSubmonoidClass.coe_finsetSum, hz]
    rfl

/-- Occurrences not belonging to the `K`-rotation pool: exactly the
manuscript's special sequence (all reflections and all rotations outside
`K`). -/
noncomputable def lineSpecialOccurrences
    (s : List (Group A)) (K : AddSubgroup A) : Selection s :=
  Finset.univ \ rotationOccurrencesIn s K

/-- The `s ≤ q` leaf of rank-two line completion. -/
theorem rankTwo_line_smallSpecial_upper
    (q : ℕ) [NeZero q]
    (K : AddSubgroup (PrimeVectorSpace q 2)) [Fintype K]
    (hKcard : Nat.card K = q)
    (hordinary : OrdinaryGMOPrescribedLengthProvider K q)
    (s : List (PrimeVectorDihedral q 2))
    (hlen : s.length = 2 * q ^ 2 + 2 * (q - 1) + 1)
    (hspecial : (lineSpecialOccurrences s K).card ≤ q) :
    HasProductOneSubsequenceOfCard s (2 * q ^ 2) := by
  have hinside : 2 * q ^ 2 + q - 1 ≤
      (rotationOccurrencesIn s K).card := by
    have hpartition := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (rotationOccurrencesIn s K))
    have hpartition' :
        (Finset.univ \ rotationOccurrencesIn s K).card +
          (rotationOccurrencesIn s K).card = s.length := by
      calc
        _ = (Finset.univ : Selection s).card := hpartition
        _ = s.length := by simp
    have hspecial' :
        (Finset.univ \ rotationOccurrencesIn s K).card ≤ q := by
      simpa [lineSpecialOccurrences] using hspecial
    omega
  have hlength : (rotationInCoordinateSequence s K).length =
      (rotationOccurrencesIn s K).card := by
    simp [rotationInCoordinateSequence]
  have hQle : Nat.card K ≤ 2 * q ^ 2 := by
    rw [hKcard]
    nlinarith
  have hthreshold : 2 * q ^ 2 + q - 1 ≤
      (rotationInCoordinateSequence s K).length := by
    rwa [hlength]
  obtain ⟨hout⟩ := hordinary (rotationInCoordinateSequence s K)
    (2 * q ^ 2) hQle hthreshold
  have htarget :=
    LowReflectionTargetOutput.ofLineOrdinaryGMOTargetOutput
      (Q := q ^ 2) hout
  have hQambient : q ^ 2 = Nat.card (PrimeVectorSpace q 2) := by
    simp [PrimeVectorSpace]
  exact hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
    s (q ^ 2) hQambient htarget

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.ConcreteGDihedral.rankTwo_line_smallSpecial_upper
