import GaoLean.PGLowReflection

/-!
# Ordinary prescribed-length GMO bridge

The external theorem is stated on an additive occurrence sequence.  This file
proves the nontrivial transport from that output to the rotation occurrences
of a generalized-dihedral source.  The transport is injective on source
positions and retains repeated coordinate values.
-/

namespace GaoLean

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact target-set output of the ordinary prescribed-length theorem. -/
structure OrdinaryGMOTargetOutput (xs : List A) (k : ℕ) where
  selected : Selection xs
  card_selected : selected.card = k
  sum_mem_target : ∃ z : A,
    (∑ i ∈ selected, occurrenceValue xs i) = k • z

/-- Source-shaped external ordinary GMO interface.  This is a proposition
parameter, not an axiom: for every length at least `k + D - 1`, with
`k ≥ |A|`, it returns exactly `k` labelled terms whose sum lies in `k • A`. -/
def OrdinaryGMOPrescribedLengthProvider
    (A : Type*) [AddCommGroup A] [Fintype A] (D : ℕ) : Prop :=
  ∀ (xs : List A) (k : ℕ), Nat.card A ≤ k →
    k + D - 1 ≤ xs.length → Nonempty (OrdinaryGMOTargetOutput xs k)

namespace ConcreteGDihedral

/-- The additive coordinate sequence of the canonical list of rotation
occurrences. -/
noncomputable def rotationCoordinateSequence (s : List (Group A)) : List A :=
  (rotationOccurrences s).toList.map fun i =>
    coordinate (occurrenceValue s i)

/-- Embed an occurrence of the rotation-coordinate list back into the exact
source occurrence that generated it. -/
noncomputable def rotationSourceOccurrence (s : List (Group A)) :
    Occurrence (rotationCoordinateSequence s) → Occurrence s := fun i =>
  (rotationOccurrences s).toList.get
    ⟨i.1, by simpa [rotationCoordinateSequence] using i.2⟩

omit [Fintype A] in
theorem rotationSourceOccurrence_injective (s : List (Group A)) :
    Function.Injective (rotationSourceOccurrence s) := by
  intro i j hij
  let i' : Fin (rotationOccurrences s).toList.length :=
    ⟨i.1, by simpa [rotationCoordinateSequence] using i.2⟩
  let j' : Fin (rotationOccurrences s).toList.length :=
    ⟨j.1, by simpa [rotationCoordinateSequence] using j.2⟩
  have hij' : i' = j' :=
    (rotationOccurrences s).nodup_toList.injective_get (by
      simpa [rotationSourceOccurrence, i', j'] using hij)
  apply Fin.ext
  exact congrArg
    (fun x : Fin (rotationOccurrences s).toList.length => x.1) hij'

omit [Fintype A] in
theorem rotationSourceOccurrence_mem (s : List (Group A))
    (i : Occurrence (rotationCoordinateSequence s)) :
    rotationSourceOccurrence s i ∈ rotationOccurrences s := by
  apply Finset.mem_toList.mp
  exact (rotationOccurrences s).toList.get_mem _

omit [Fintype A] in
theorem occurrenceValue_rotationCoordinateSequence
    (s : List (Group A))
    (i : Occurrence (rotationCoordinateSequence s)) :
    occurrenceValue (rotationCoordinateSequence s) i =
      coordinate (occurrenceValue s (rotationSourceOccurrence s i)) := by
  simp [rotationCoordinateSequence, rotationSourceOccurrence,
    occurrenceValue, List.get_eq_getElem]

/-- Transport the exact additive GMO output back to source rotation
occurrences. -/
noncomputable def LowReflectionTargetOutput.ofOrdinaryGMOTargetOutput
    {s : List (Group A)} {q : ℕ}
    (h : OrdinaryGMOTargetOutput (rotationCoordinateSequence s) (2 * q)) :
    LowReflectionTargetOutput s q := by
  classical
  let selected : Selection s :=
    h.selected.image (rotationSourceOccurrence s)
  refine {
    selected := selected
    selectedRotations := ?_
    card_selected := ?_
    coordinateSum_mem_target := ?_
  }
  · intro i hi
    rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
    exact rotationSourceOccurrence_mem s j
  · rw [Finset.card_image_of_injective _
      (rotationSourceOccurrence_injective s), h.card_selected]
  · obtain ⟨z, hz⟩ := h.sum_mem_target
    refine ⟨z, ?_⟩
    unfold coordinateSum
    have hsumForward :
        (∑ j ∈ h.selected,
            occurrenceValue (rotationCoordinateSequence s) j) =
          ∑ i ∈ selected, coordinate (occurrenceValue s i) := by
      refine Finset.sum_bij (fun j _ => rotationSourceOccurrence s j)
        ?_ ?_ ?_ ?_
      · intro j hj
        exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
      · intro i hi j hj heq
        exact rotationSourceOccurrence_injective s heq
      · intro i hi
        rcases Finset.mem_image.mp hi with ⟨j, hj, rfl⟩
        exact ⟨j, hj, rfl⟩
      · intro j hj
        exact occurrenceValue_rotationCoordinateSequence s j
    have hsum := hsumForward.symm
    rw [hsum, hz]

/-- The ordinary GMO provider supplies the low-reflection output after the
checked rotation-count bound and occurrence transport. -/
theorem exists_lowReflectionTargetOutput_of_ordinaryGMO
    (s : List (Group A)) (Q D a b : ℕ)
    (hQcard : Q = Nat.card A)
    (hrotationCount : (rotationOccurrences s).card = b)
    (htotal : a + b = 2 * Q + D)
    (hlow : a ≤ 1)
    (hGMO : OrdinaryGMOPrescribedLengthProvider A D) :
    Nonempty (LowReflectionTargetOutput s Q) := by
  have hQle : Nat.card A ≤ 2 * Q := by omega
  have hthreshold : 2 * Q + D - 1 ≤
      (rotationCoordinateSequence s).length := by
    simpa [rotationCoordinateSequence, hrotationCount] using
      lowReflection_rotationCount_lower hlow htotal
  obtain ⟨h⟩ := hGMO (rotationCoordinateSequence s) (2 * Q) hQle hthreshold
  exact ⟨LowReflectionTargetOutput.ofOrdinaryGMOTargetOutput h⟩

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.ConcreteGDihedral.rotationSourceOccurrence_injective
#print axioms GaoLean.ConcreteGDihedral.occurrenceValue_rotationCoordinateSequence
#print axioms GaoLean.ConcreteGDihedral.LowReflectionTargetOutput.ofOrdinaryGMOTargetOutput
#print axioms GaoLean.ConcreteGDihedral.exists_lowReflectionTargetOutput_of_ordinaryGMO
