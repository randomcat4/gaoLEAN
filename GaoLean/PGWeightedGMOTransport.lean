import GaoLean.PGHighReflection

/-!
# Generic weighted GMO occurrence transport

The weighted prescribed-length theorem naturally returns a signed selection
of positions in an additive list.  This module freezes that generic output and
transports it to the canonical occurrence-labelled same-type pair reservoir.
The four pair lists used by the generalized-dihedral consumer are constructed
here; they are not part of the external theorem interface.
-/

namespace GaoLean

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Generic occurrence-labelled output of a weighted prescribed-length GMO
theorem with weights in `{+1,-1}`. -/
structure WeightedGMOTargetOutput (xs : List A) (q : ℕ) where
  positive : Selection xs
  negative : Selection xs
  disjoint : Disjoint positive negative
  card_selected : positive.card + negative.card = q
  weightedSum_mem_target : ∃ z : A,
    (∑ i ∈ positive, occurrenceValue xs i) -
      (∑ i ∈ negative, occurrenceValue xs i) = q • z

/-- Generic additive-list weighted GMO interface.  This is a proposition
parameter, not a project axiom. -/
def WeightedGMOPrescribedLengthProvider
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (xs : List A) (q m : ℕ),
    Nat.card A ≤ q →
    PlusMinusDavenportAtMost A m →
    q + m - 1 ≤ xs.length →
    Nonempty (WeightedGMOTargetOutput xs q)

namespace ConcreteGDihedral

section GenericListLemmas

variable {α : Type*}

theorem pairCoordinates_eq_flatMap (pairs : List (α × α)) :
    pairCoordinates pairs = pairs.flatMap fun p => [p.1, p.2] := by
  induction pairs with
  | nil => rfl
  | cons p pairs ih =>
      rcases p with ⟨x, y⟩
      simp [pairCoordinates, ih]

theorem pairCoordinates_subperm {xs ys : List (α × α)}
    (h : xs.Subperm ys) :
    (pairCoordinates xs).Subperm (pairCoordinates ys) := by
  rcases List.subperm_iff.mp h with ⟨middle, hperm, hsub⟩
  apply List.subperm_iff.mpr
  refine ⟨pairCoordinates middle, ?_, ?_⟩
  · simpa [pairCoordinates_eq_flatMap] using
      hperm.flatMap (fun _ _ => List.Perm.refl _)
  · simpa [pairCoordinates_eq_flatMap] using
      hsub.flatMap (fun p => [p.1, p.2])

theorem nodup_of_subperm {xs ys : List α}
    (h : xs.Subperm ys) (hys : ys.Nodup) : xs.Nodup := by
  rcases List.subperm_iff.mp h with ⟨middle, hperm, hsub⟩
  exact hsub.nodup (hperm.nodup_iff.mpr hys)

theorem four_filter_toList_nodup
    (positive negative : Finset α) (p : α → Prop)
    [DecidableEq α] [DecidablePred p] [DecidablePred fun x => ¬p x]
    (hdisjoint : Disjoint positive negative) :
    ((positive.filter p).toList ++
      (negative.filter p).toList ++
      (positive.filter fun x => ¬p x).toList ++
      (negative.filter fun x => ¬p x).toList).Nodup := by
  let pp := positive.filter p
  let np := negative.filter p
  let pn := positive.filter fun x => ¬p x
  let nn := negative.filter fun x => ¬p x
  have hppnp : Disjoint pp np :=
    Finset.disjoint_filter_filter hdisjoint
  have hpppn : Disjoint pp pn := by
    simpa [pp, pn] using
      Finset.disjoint_filter_filter_not positive positive p
  have hppnn : Disjoint pp nn :=
    Finset.disjoint_filter_filter hdisjoint
  have hnpnn : Disjoint np nn := by
    simpa [np, nn] using
      Finset.disjoint_filter_filter_not negative negative p
  have hnppn : Disjoint np pn :=
    Finset.disjoint_filter_filter hdisjoint.symm
  have hpnnn : Disjoint pn nn :=
    Finset.disjoint_filter_filter hdisjoint
  have toListDisjoint : ∀ {u v : Finset α}, Disjoint u v →
      u.toList.Disjoint v.toList := by
    intro u v huv
    rw [List.disjoint_left]
    intro x hxu hxv
    exact (Finset.disjoint_left.mp huv)
      (Finset.mem_toList.mp hxu) (Finset.mem_toList.mp hxv)
  have hleft : (pp.toList ++ np.toList).Nodup :=
    pp.nodup_toList.append np.nodup_toList (toListDisjoint hppnp)
  have hright : (pn.toList ++ nn.toList).Nodup :=
    pn.nodup_toList.append nn.nodup_toList (toListDisjoint hpnnn)
  have hbetween :
      (pp.toList ++ np.toList).Disjoint (pn.toList ++ nn.toList) := by
    rw [List.disjoint_left]
    intro x hxleft hxright
    rcases List.mem_append.mp hxleft with hxpp | hxnp
    · rcases List.mem_append.mp hxright with hxpn | hxnn
      · exact (List.disjoint_left.mp (toListDisjoint hpppn)) hxpp hxpn
      · exact (List.disjoint_left.mp (toListDisjoint hppnn)) hxpp hxnn
    · rcases List.mem_append.mp hxright with hxpn | hxnn
      · exact (List.disjoint_left.mp (toListDisjoint hnppn)) hxnp hxpn
      · exact (List.disjoint_left.mp (toListDisjoint hnpnn)) hxnp hxnn
  simpa [pp, np, pn, nn, List.append_assoc] using
    hleft.append hright hbetween

end GenericListLemmas

section PairLabels

noncomputable def canonicalPairList (s : List (Group A)) :
    List (Occurrence s × Occurrence s) :=
  (canonicalSameTypePairReservoir s).rotationPairs ++
    (canonicalSameTypePairReservoir s).reflectionPairs

def rotationPairLabel (s : List (Group A))
    (p : Occurrence s × Occurrence s) : A :=
  coordinate (occurrenceValue s p.1) +
    coordinate (occurrenceValue s p.2)

def reflectionPairLabel (s : List (Group A))
    (p : Occurrence s × Occurrence s) : A :=
  coordinate (occurrenceValue s p.1) -
    coordinate (occurrenceValue s p.2)

/-- The additive label list to which the generic weighted GMO theorem is
applied.  Its positions, rather than its possibly repeated values, remember
the exact canonical source pair. -/
noncomputable def canonicalPairLabelSequence (s : List (Group A)) : List A :=
  (canonicalSameTypePairReservoir s).rotationPairs.map
      (rotationPairLabel s) ++
    (canonicalSameTypePairReservoir s).reflectionPairs.map
      (reflectionPairLabel s)

omit [Fintype A] in
@[simp]
theorem length_canonicalPairLabelSequence (s : List (Group A)) :
    (canonicalPairLabelSequence s).length = (canonicalPairList s).length := by
  simp [canonicalPairLabelSequence, canonicalPairList]

def pairListOccurrence (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s)) :
    Occurrence (canonicalPairList s) :=
  ⟨i.1, by simpa using i.2⟩

noncomputable def canonicalPairAt (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s)) :
    Occurrence s × Occurrence s :=
  (canonicalPairList s).get (pairListOccurrence s i)

def IsRotationPairOccurrence (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s)) : Prop :=
  i.1 < (canonicalSameTypePairReservoir s).rotationPairs.length

noncomputable instance instDecidablePredIsRotationPairOccurrence
    (s : List (Group A)) :
    DecidablePred (IsRotationPairOccurrence s) := fun i =>
  Nat.decLt i.1 (canonicalSameTypePairReservoir s).rotationPairs.length

omit [Fintype A] in
theorem canonicalPairList_endpoints_nodup (s : List (Group A)) :
    (pairCoordinates (canonicalPairList s)).Nodup := by
  simpa [canonicalPairList, pairCoordinates_append] using
    (canonicalSameTypePairReservoir s).endpointsNodup

omit [Fintype A] in
theorem canonicalPairList_nodup (s : List (Group A)) :
    (canonicalPairList s).Nodup :=
  nodup_pairs_of_pairCoordinates_nodup _
    (canonicalPairList_endpoints_nodup s)

omit [Fintype A] in
theorem canonicalPairAt_injective (s : List (Group A)) :
    Function.Injective (canonicalPairAt s) := by
  intro i j hij
  have hocc : pairListOccurrence s i = pairListOccurrence s j :=
    (canonicalPairList_nodup s).injective_get hij
  apply Fin.ext
  exact congrArg
    (fun k : Occurrence (canonicalPairList s) => k.val) hocc

omit [Fintype A] in
theorem canonicalPairAt_mem (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s)) :
    canonicalPairAt s i ∈ canonicalPairList s := by
  exact (canonicalPairList s).get_mem _

omit [Fintype A] in
theorem canonicalPairAt_mem_rotation (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s))
    (hi : IsRotationPairOccurrence s i) :
    canonicalPairAt s i ∈
      (canonicalSameTypePairReservoir s).rotationPairs := by
  simp [canonicalPairAt, pairListOccurrence, canonicalPairList,
    List.get_eq_getElem,
    List.getElem_append_left hi]

omit [Fintype A] in
theorem canonicalPairAt_mem_reflection (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s))
    (hi : ¬IsRotationPairOccurrence s i) :
    canonicalPairAt s i ∈
      (canonicalSameTypePairReservoir s).reflectionPairs := by
  have hge :
      (canonicalSameTypePairReservoir s).rotationPairs.length ≤ i.1 := by
    simpa [IsRotationPairOccurrence] using hi
  simp [canonicalPairAt, pairListOccurrence, canonicalPairList,
    List.get_eq_getElem, List.getElem_append_right hge]

omit [Fintype A] in
theorem occurrenceValue_canonicalPairLabelSequence_of_rotation
    (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s))
    (hi : IsRotationPairOccurrence s i) :
    occurrenceValue (canonicalPairLabelSequence s) i =
      rotationPairLabel s (canonicalPairAt s i) := by
  have hi' : i.1 <
      ((canonicalSameTypePairReservoir s).rotationPairs.map
        (rotationPairLabel s)).length := by
    simpa [IsRotationPairOccurrence] using hi
  simp [canonicalPairLabelSequence, occurrenceValue, canonicalPairAt,
    pairListOccurrence, canonicalPairList, List.get_eq_getElem,
    List.getElem_append_left hi', List.getElem_append_left hi]
  all_goals rfl

omit [Fintype A] in
theorem occurrenceValue_canonicalPairLabelSequence_of_reflection
    (s : List (Group A))
    (i : Occurrence (canonicalPairLabelSequence s))
    (hi : ¬IsRotationPairOccurrence s i) :
    occurrenceValue (canonicalPairLabelSequence s) i =
      reflectionPairLabel s (canonicalPairAt s i) := by
  have hge :
      (canonicalSameTypePairReservoir s).rotationPairs.length ≤ i.1 := by
    simpa [IsRotationPairOccurrence] using hi
  have hge' :
      ((canonicalSameTypePairReservoir s).rotationPairs.map
        (rotationPairLabel s)).length ≤ i.1 := by simpa using hge
  simp [canonicalPairLabelSequence, occurrenceValue, canonicalPairAt,
    pairListOccurrence, canonicalPairList, List.get_eq_getElem,
    List.getElem_append_right hge', List.getElem_append_right hge]

end PairLabels

section SelectionTransport

noncomputable def selectedRotationPairs
    (s : List (Group A))
    (I : Selection (canonicalPairLabelSequence s)) :
    List (Occurrence s × Occurrence s) := by
  classical
  exact ((I.filter (IsRotationPairOccurrence s)).toList).map
    (canonicalPairAt s)

noncomputable def selectedReflectionPairs
    (s : List (Group A))
    (I : Selection (canonicalPairLabelSequence s)) :
    List (Occurrence s × Occurrence s) := by
  classical
  exact ((I.filter fun i => ¬IsRotationPairOccurrence s i).toList).map
    (canonicalPairAt s)

omit [Fintype A] in
theorem selectedRotationPairs_fromReservoir
    (s : List (Group A))
    (I : Selection (canonicalPairLabelSequence s)) :
    ∀ p ∈ selectedRotationPairs s I,
      p ∈ (canonicalSameTypePairReservoir s).rotationPairs := by
  classical
  intro p hp
  rw [selectedRotationPairs] at hp
  rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
  exact canonicalPairAt_mem_rotation s i (Finset.mem_filter.mp
    (Finset.mem_toList.mp hi)).2

omit [Fintype A] in
theorem selectedReflectionPairs_fromReservoir
    (s : List (Group A))
    (I : Selection (canonicalPairLabelSequence s)) :
    ∀ p ∈ selectedReflectionPairs s I,
      p ∈ (canonicalSameTypePairReservoir s).reflectionPairs := by
  classical
  intro p hp
  rw [selectedReflectionPairs] at hp
  rcases List.mem_map.mp hp with ⟨i, hi, rfl⟩
  exact canonicalPairAt_mem_reflection s i (Finset.mem_filter.mp
    (Finset.mem_toList.mp hi)).2

omit [Fintype A] in
theorem sum_selectedRotationPairs
    (s : List (Group A))
    (I : Selection (canonicalPairLabelSequence s)) :
    ((occurrenceCoordinatePairs s (selectedRotationPairs s I)).map
        fun p => p.1 + p.2).sum =
      ∑ i ∈ I.filter (IsRotationPairOccurrence s),
        occurrenceValue (canonicalPairLabelSequence s) i := by
  classical
  let F := I.filter (IsRotationPairOccurrence s)
  calc
    ((occurrenceCoordinatePairs s (selectedRotationPairs s I)).map
          fun p => p.1 + p.2).sum =
        ∑ i ∈ F, rotationPairLabel s (canonicalPairAt s i) := by
          simp [selectedRotationPairs, occurrenceCoordinatePairs,
            rotationPairLabel, F, List.map_map]
    _ = ∑ i ∈ F, occurrenceValue (canonicalPairLabelSequence s) i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (occurrenceValue_canonicalPairLabelSequence_of_rotation s i
        (Finset.mem_filter.mp hi).2).symm
    _ = ∑ i ∈ I.filter (IsRotationPairOccurrence s),
          occurrenceValue (canonicalPairLabelSequence s) i := by rfl

omit [Fintype A] in
theorem sum_selectedReflectionPairs
    (s : List (Group A))
    (I : Selection (canonicalPairLabelSequence s)) :
    ((occurrenceCoordinatePairs s (selectedReflectionPairs s I)).map
        fun p => p.1 - p.2).sum =
      ∑ i ∈ I.filter (fun i => ¬IsRotationPairOccurrence s i),
        occurrenceValue (canonicalPairLabelSequence s) i := by
  classical
  let F := I.filter fun i => ¬IsRotationPairOccurrence s i
  calc
    ((occurrenceCoordinatePairs s (selectedReflectionPairs s I)).map
          fun p => p.1 - p.2).sum =
        ∑ i ∈ F, reflectionPairLabel s (canonicalPairAt s i) := by
          simp [selectedReflectionPairs, occurrenceCoordinatePairs,
            reflectionPairLabel, F, List.map_map]
    _ = ∑ i ∈ F, occurrenceValue (canonicalPairLabelSequence s) i := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (occurrenceValue_canonicalPairLabelSequence_of_reflection s i
        (Finset.mem_filter.mp hi).2).symm
    _ = ∑ i ∈ I.filter (fun i => ¬IsRotationPairOccurrence s i),
          occurrenceValue (canonicalPairLabelSequence s) i := by rfl

omit [Fintype A] in
theorem selectedPairLists_endpoints_nodup
    (s : List (Group A))
    (positive negative : Selection (canonicalPairLabelSequence s))
    (hdisjoint : Disjoint positive negative) :
    (pairCoordinates (selectedRotationPairs s positive) ++
      pairCoordinates (selectedRotationPairs s negative) ++
      pairCoordinates (selectedReflectionPairs s positive) ++
      pairCoordinates (selectedReflectionPairs s negative)).Nodup := by
  classical
  let p := IsRotationPairOccurrence s
  let indices :=
    (positive.filter p).toList ++
      (negative.filter p).toList ++
      (positive.filter fun i => ¬p i).toList ++
      (negative.filter fun i => ¬p i).toList
  have hindices : indices.Nodup := by
    exact four_filter_toList_nodup positive negative p hdisjoint
  let pairs := indices.map (canonicalPairAt s)
  have hpairsNodup : pairs.Nodup :=
    hindices.map (canonicalPairAt_injective s)
  have hpairsSubset : pairs ⊆ canonicalPairList s := by
    intro pair hpair
    rcases List.mem_map.mp hpair with ⟨i, hi, rfl⟩
    exact canonicalPairAt_mem s i
  have hsubperm : pairs.Subperm (canonicalPairList s) :=
    hpairsNodup.subperm hpairsSubset
  have hflat : (pairCoordinates pairs).Nodup :=
    nodup_of_subperm (pairCoordinates_subperm hsubperm)
      (canonicalPairList_endpoints_nodup s)
  simpa [pairs, indices, p, selectedRotationPairs,
    selectedReflectionPairs, pairCoordinates_append, List.map_append,
    List.append_assoc] using hflat

/-- Complete occurrence transport from the generic additive weighted-GMO
output to the four canonical pair lists expected by the high-reflection
consumer. -/
noncomputable def PrescribedSignedReservoirTargetOutput.ofWeightedGMOTargetOutput
    {s : List (Group A)} {q : ℕ}
    (h : WeightedGMOTargetOutput (canonicalPairLabelSequence s) q) :
    PrescribedSignedReservoirTargetOutput s q := by
  classical
  refine {
    selection := {
      rotationPositive := selectedRotationPairs s h.positive
      rotationNegative := selectedRotationPairs s h.negative
      reflectionPositive := selectedReflectionPairs s h.positive
      reflectionNegative := selectedReflectionPairs s h.negative
      rotationPositiveFromReservoir :=
        selectedRotationPairs_fromReservoir s h.positive
      rotationNegativeFromReservoir :=
        selectedRotationPairs_fromReservoir s h.negative
      reflectionPositiveFromReservoir :=
        selectedReflectionPairs_fromReservoir s h.positive
      reflectionNegativeFromReservoir :=
        selectedReflectionPairs_fromReservoir s h.negative
      pairCount_eq := ?_
      endpointsNodup :=
        selectedPairLists_endpoints_nodup s h.positive h.negative h.disjoint
    }
    weightedPairSum_mem_target := ?_
  }
  · have hp := Finset.card_filter_add_card_filter_not
      (s := h.positive) (IsRotationPairOccurrence s)
    have hn := Finset.card_filter_add_card_filter_not
      (s := h.negative) (IsRotationPairOccurrence s)
    simp only [selectedRotationPairs, selectedReflectionPairs,
      List.length_map, Finset.length_toList]
    calc
      (h.positive.filter (IsRotationPairOccurrence s)).card +
            (h.negative.filter (IsRotationPairOccurrence s)).card +
            (h.positive.filter fun i =>
              ¬IsRotationPairOccurrence s i).card +
            (h.negative.filter fun i =>
              ¬IsRotationPairOccurrence s i).card =
          ((h.positive.filter (IsRotationPairOccurrence s)).card +
            (h.positive.filter fun i =>
              ¬IsRotationPairOccurrence s i).card) +
          ((h.negative.filter (IsRotationPairOccurrence s)).card +
            (h.negative.filter fun i =>
              ¬IsRotationPairOccurrence s i).card) := by omega
      _ = h.positive.card + h.negative.card := by rw [hp, hn]
      _ = q := h.card_selected
  · obtain ⟨z, hz⟩ := h.weightedSum_mem_target
    refine ⟨z, ?_⟩
    rw [sum_selectedRotationPairs, sum_selectedRotationPairs,
      sum_selectedReflectionPairs, sum_selectedReflectionPairs]
    have hp := Finset.sum_filter_add_sum_filter_not h.positive
      (IsRotationPairOccurrence s)
      (fun i => occurrenceValue (canonicalPairLabelSequence s) i)
    have hn := Finset.sum_filter_add_sum_filter_not h.negative
      (IsRotationPairOccurrence s)
      (fun i => occurrenceValue (canonicalPairLabelSequence s) i)
    calc
      (∑ i ∈ h.positive.filter (IsRotationPairOccurrence s),
          occurrenceValue (canonicalPairLabelSequence s) i) -
          (∑ i ∈ h.negative.filter (IsRotationPairOccurrence s),
            occurrenceValue (canonicalPairLabelSequence s) i) +
          (∑ i ∈ h.positive.filter (fun i =>
            ¬IsRotationPairOccurrence s i),
            occurrenceValue (canonicalPairLabelSequence s) i) -
          (∑ i ∈ h.negative.filter (fun i =>
            ¬IsRotationPairOccurrence s i),
            occurrenceValue (canonicalPairLabelSequence s) i) =
        (∑ i ∈ h.positive,
            occurrenceValue (canonicalPairLabelSequence s) i) -
          (∑ i ∈ h.negative,
            occurrenceValue (canonicalPairLabelSequence s) i) := by
              rw [← hp, ← hn]
              abel
      _ = q • z := hz

end SelectionTransport

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.ConcreteGDihedral.PrescribedSignedReservoirTargetOutput.ofWeightedGMOTargetOutput
