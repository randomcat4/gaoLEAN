import GaoLean.PGSynthesis
import GaoLean.SequenceEntryCounterexample

/-!
# The explicit `C₃` counterexample to the frozen raw six-reflection two-exit

The source has three nonzero rotations and six zero-coordinate reflections.
Definitions below preserve source labels and freeze the original
`PairCompleteTarget6` / `OriginEntryPlus2` quantifiers.
-/

namespace GaoLean.ConcreteGDihedral

/-- The frozen raw pair-complete output: every pair of reflection labels can
be extended to an exact `2Q` product-one labelled selection containing no
other reflection labels. -/
def PairCompleteTarget6 (s : List (Group (ZMod 3))) (Q : ℕ) : Prop :=
  ∀ P : Selection s,
    P ⊆ reflectionOccurrences s → P.card = 2 →
      ∃ J : Selection s,
        J.card = 2 * Q ∧
        J ∩ reflectionOccurrences s = P ∧
        IsProductOneSelection s J

/-- The frozen origin-centred `+2` capacity exit.  Taking all qualifying
rotation labels is equivalent to the source formulation with an auxiliary
subset `C`. -/
def OriginEntryPlus2 (s : List (Group (ZMod 3))) (b : ℕ) : Prop :=
  ∃ K : AddSubgroup (ZMod 3), K < ⊤ ∧
    b - Nat.card (ZMod 3 ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card

/-- Three copies of the nonzero rotation followed by six copies of the
zero-coordinate reflection. -/
def a6RawCounterexample : List (Group (ZMod 3)) :=
  List.replicate 3 ((data (ZMod 3)).rot 1) ++
    List.replicate 6 ((data (ZMod 3)).refl 0)

theorem a6RawCounterexample_length : a6RawCounterexample.length = 9 := by
  simp [a6RawCounterexample]

theorem card_rotationOccurrences_a6RawCounterexample :
    (rotationOccurrences a6RawCounterexample).card = 3 := by
  classical
  change
    (Finset.univ.filter fun i =>
      IsRotation (occurrenceValue a6RawCounterexample i)).card = 3
  calc
    _ = (Multiset.ofList a6RawCounterexample).countP IsRotation :=
      card_occurrences_satisfying a6RawCounterexample IsRotation
    _ = 3 := by simp [a6RawCounterexample, IsRotation]

theorem card_reflectionOccurrences_a6RawCounterexample :
    (reflectionOccurrences a6RawCounterexample).card = 6 := by
  have hpartition :=
    card_reflectionOccurrences_add_card_rotationOccurrences
      a6RawCounterexample
  rw [card_rotationOccurrences_a6RawCounterexample,
    a6RawCounterexample_length] at hpartition
  omega

private theorem selection_partition (J : Selection a6RawCounterexample) :
    (J ∩ rotationOccurrences a6RawCounterexample) ∪
        (J ∩ reflectionOccurrences a6RawCounterexample) = J := by
  ext i
  have htypes :
      i ∈ rotationOccurrences a6RawCounterexample ∨
        i ∈ reflectionOccurrences a6RawCounterexample := by
    have hu := congrArg (fun U : Selection a6RawCounterexample => i ∈ U)
      (rotationOccurrences_union_reflectionOccurrences a6RawCounterexample)
    simpa using hu
  simp only [Finset.mem_union, Finset.mem_inter]
  aesop

/-- The pair-complete exit is impossible: an exact-six witness with exactly
two reflections would require four rotations, but the source has only three. -/
theorem a6RawCounterexample_not_pairCompleteTarget6 :
    ¬ PairCompleteTarget6 a6RawCounterexample 3 := by
  intro hpair
  obtain ⟨P, hPsub, hPcard⟩ :=
    Finset.exists_subset_card_eq
      (show 2 ≤ (reflectionOccurrences a6RawCounterexample).card by
        rw [card_reflectionOccurrences_a6RawCounterexample]
        norm_num)
  obtain ⟨J, hJcard, hJreflection, _hJprod⟩ :=
    hpair P hPsub hPcard
  have hJreflectionCard :
      (J ∩ reflectionOccurrences a6RawCounterexample).card = 2 := by
    rw [hJreflection, hPcard]
  have hJrotationCard :
      (J ∩ rotationOccurrences a6RawCounterexample).card ≤ 3 := by
    calc
      (J ∩ rotationOccurrences a6RawCounterexample).card ≤
          (rotationOccurrences a6RawCounterexample).card :=
        Finset.card_le_card Finset.inter_subset_right
      _ = 3 := card_rotationOccurrences_a6RawCounterexample
  have hunionCard := Finset.card_union_le
    (J ∩ rotationOccurrences a6RawCounterexample)
    (J ∩ reflectionOccurrences a6RawCounterexample)
  rw [selection_partition J, hJcard] at hunionCard
  omega

theorem card_rotationOccurrencesIn_a6RawCounterexample
    (K : AddSubgroup (ZMod 3)) (hK : K < ⊤) :
    (rotationOccurrencesIn a6RawCounterexample K).card = 0 := by
  classical
  have h1 : (1 : ZMod 3) ∉ K :=
    one_not_mem_proper_addSubgroup_zmod 3 K hK
  let p : Group (ZMod 3) → Prop := fun g =>
    IsRotation g ∧ coordinate g ∈ K
  have hpRotation : ¬p ((data (ZMod 3)).rot 1) := by
    simpa [p, IsRotation, coordinate, GaoLean.GDihedralData.rot,
      data, rotation] using h1
  have hpReflection : ¬p ((data (ZMod 3)).refl 0) := by
    simp [p, IsRotation]
  have hpRotation' :
      ¬p (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod 3))) := by
    simpa [GaoLean.GDihedralData.rot, data, rotation] using hpRotation
  have hpReflection' :
      ¬p (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := by
    simpa [GaoLean.GDihedralData.refl, GaoLean.GDihedralData.rot,
      data, rotation, flip] using hpReflection
  change
    (Finset.univ.filter fun i => p (occurrenceValue a6RawCounterexample i)).card = 0
  calc
    _ = (Multiset.ofList a6RawCounterexample).countP p :=
      card_occurrences_satisfying a6RawCounterexample p
    _ = 0 := by simp [a6RawCounterexample, hpRotation', hpReflection']

/-- No proper subgroup reaches the raw `b-[A:K]+2` gate. -/
theorem a6RawCounterexample_not_originEntryPlus2 :
    ¬ OriginEntryPlus2 a6RawCounterexample 3 := by
  rintro ⟨K, hK, hgate⟩
  have hcount := card_rotationOccurrencesIn_a6RawCounterexample K hK
  have hquotientLe : Nat.card (ZMod 3 ⧸ K) ≤ 3 := by
    have hle : Nat.card (ZMod 3 ⧸ K) ≤ Nat.card (ZMod 3) :=
      Nat.le_of_dvd Nat.card_pos K.card_quotient_dvd_card
    simpa using hle
  omega

private theorem selectedMultiset_reflections_a6RawCounterexample :
    selectedMultiset a6RawCounterexample
        (reflectionOccurrences a6RawCounterexample) =
      Multiset.ofList
        (List.replicate 6 ((data (ZMod 3)).refl 0)) := by
  classical
  rw [reflectionOccurrences]
  calc
    _ = (Multiset.ofList a6RawCounterexample).filter
          (fun g => ¬IsRotation g) :=
      selectedMultiset_filter_univ a6RawCounterexample
        (fun g => ¬IsRotation g)
    _ = _ := by simp [a6RawCounterexample, IsRotation]

/-- The same word nevertheless has the original exact-six target: take all
six zero-coordinate reflections and order them in three adjacent pairs. -/
theorem a6RawCounterexample_targetFound :
    HasProductOneSubsequenceOfCard a6RawCounterexample 6 := by
  let F := reflectionOccurrences a6RawCounterexample
  refine ⟨F, ?_, ?_⟩
  · exact card_reflectionOccurrences_a6RawCounterexample
  · refine ⟨List.replicate 6 ((data (ZMod 3)).refl 0), ?_, ?_⟩
    · exact selectedMultiset_reflections_a6RawCounterexample.symm
    · have hflip := flip_sq (ZMod 3)
      change SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) *
          SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2)) = 1 at hflip
      simpa only [GaoLean.GDihedralData.refl, GaoLean.GDihedralData.rot,
        data, rotation, flip, List.prod_replicate, hflip, mul_one]

/-- Complete theorem-level refutation of frozen Claim A6-raw on its advertised
input shape. -/
theorem a6RawCounterexample_disproves_twoExit :
    a6RawCounterexample.length = 2 * 3 + 3 ∧
    (reflectionOccurrences a6RawCounterexample).card = 6 ∧
    ¬PairCompleteTarget6 a6RawCounterexample 3 ∧
    ¬OriginEntryPlus2 a6RawCounterexample 3 ∧
    HasProductOneSubsequenceOfCard a6RawCounterexample 6 :=
  ⟨a6RawCounterexample_length,
    card_reflectionOccurrences_a6RawCounterexample,
    a6RawCounterexample_not_pairCompleteTarget6,
    a6RawCounterexample_not_originEntryPlus2,
    a6RawCounterexample_targetFound⟩

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.one_not_mem_proper_addSubgroup_zmod
#print axioms GaoLean.ConcreteGDihedral.a6RawCounterexample_length
#print axioms GaoLean.ConcreteGDihedral.card_rotationOccurrences_a6RawCounterexample
#print axioms GaoLean.ConcreteGDihedral.card_reflectionOccurrences_a6RawCounterexample
#print axioms GaoLean.ConcreteGDihedral.a6RawCounterexample_not_pairCompleteTarget6
#print axioms GaoLean.ConcreteGDihedral.card_rotationOccurrencesIn_a6RawCounterexample
#print axioms GaoLean.ConcreteGDihedral.a6RawCounterexample_not_originEntryPlus2
#print axioms GaoLean.ConcreteGDihedral.a6RawCounterexample_targetFound
#print axioms GaoLean.ConcreteGDihedral.a6RawCounterexample_disproves_twoExit
