import GaoLean.PGReflectionPairs

/-!
# Occurrence-labelled same-type pair reservoir

A-R6 Section 4.2 pairs rotation and reflection occurrences separately.  This
file supplies the actual occurrence construction behind the previously checked
numerical pair count.  Pair endpoints are source positions, not group values.
-/

namespace GaoLean.ConcreteGDihedral

section GenericPairing

variable {α : Type*}

/-- Pair consecutive occurrences and leave at most one terminal occurrence. -/
def pairUp : List α → List (α × α)
  | x :: y :: rest => (x, y) :: pairUp rest
  | _ => []

/-- The occurrence not used by `pairUp`, if the input length is odd. -/
def unpairedSuffix : List α → List α
  | _ :: _ :: rest => unpairedSuffix rest
  | rest => rest

theorem pairCoordinates_pairUp_append_unpairedSuffix :
    ∀ xs : List α,
      pairCoordinates (pairUp xs) ++ unpairedSuffix xs = xs
  | [] => by simp [pairUp, unpairedSuffix, pairCoordinates]
  | [x] => by simp [pairUp, unpairedSuffix, pairCoordinates]
  | x :: y :: rest => by
      simp [pairUp, unpairedSuffix, pairCoordinates,
        pairCoordinates_pairUp_append_unpairedSuffix rest]

@[simp]
theorem length_pairUp : ∀ xs : List α, (pairUp xs).length = xs.length / 2
  | [] => by simp [pairUp]
  | [x] => by simp [pairUp]
  | x :: y :: rest => by
      simp [pairUp, length_pairUp rest]
      omega

theorem length_unpairedSuffix_le_one :
    ∀ xs : List α, (unpairedSuffix xs).length ≤ 1
  | [] => by simp [unpairedSuffix]
  | [x] => by simp [unpairedSuffix]
  | _ :: _ :: rest => by
      simpa [unpairedSuffix] using length_unpairedSuffix_le_one rest

theorem nodup_pairCoordinates_pairUp (xs : List α) (hxs : xs.Nodup) :
    (pairCoordinates (pairUp xs)).Nodup := by
  have hall :
      (pairCoordinates (pairUp xs) ++ unpairedSuffix xs).Nodup := by
    rw [pairCoordinates_pairUp_append_unpairedSuffix]
    exact hxs
  exact hall.of_append_left

theorem fst_mem_pairCoordinates_of_mem {pairs : List (α × α)} {p : α × α}
    (hp : p ∈ pairs) : p.1 ∈ pairCoordinates pairs := by
  induction pairs with
  | nil => simp at hp
  | cons q pairs ih =>
      rcases q with ⟨x, y⟩
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [pairCoordinates]
      · simp [pairCoordinates, ih hp]

theorem snd_mem_pairCoordinates_of_mem {pairs : List (α × α)} {p : α × α}
    (hp : p ∈ pairs) : p.2 ∈ pairCoordinates pairs := by
  induction pairs with
  | nil => simp at hp
  | cons q pairs ih =>
      rcases q with ⟨x, y⟩
      simp only [List.mem_cons] at hp
      rcases hp with rfl | hp
      · simp [pairCoordinates]
      · simp [pairCoordinates, ih hp]

theorem pairUp_fst_mem_source {xs : List α} {p : α × α}
    (hp : p ∈ pairUp xs) : p.1 ∈ xs := by
  rw [← pairCoordinates_pairUp_append_unpairedSuffix xs]
  exact List.mem_append_left _ (fst_mem_pairCoordinates_of_mem hp)

theorem pairUp_snd_mem_source {xs : List α} {p : α × α}
    (hp : p ∈ pairUp xs) : p.2 ∈ xs := by
  rw [← pairCoordinates_pairUp_append_unpairedSuffix xs]
  exact List.mem_append_left _ (snd_mem_pairCoordinates_of_mem hp)

end GenericPairing

section ConcreteReservoir

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- The canonical same-type pairing of all source occurrences, with at most
one unused occurrence in each type. -/
structure SameTypePairReservoir (s : List (Group A)) where
  rotationPairs : List (Occurrence s × Occurrence s)
  reflectionPairs : List (Occurrence s × Occurrence s)
  rotationCover :
    pairCoordinates rotationPairs ++
        unpairedSuffix (rotationOccurrences s).toList =
      (rotationOccurrences s).toList
  reflectionCover :
    pairCoordinates reflectionPairs ++
        unpairedSuffix (reflectionOccurrences s).toList =
      (reflectionOccurrences s).toList
  rotationPairCount :
    rotationPairs.length = (rotationOccurrences s).card / 2
  reflectionPairCount :
    reflectionPairs.length = (reflectionOccurrences s).card / 2
  rotationTyped : ∀ p ∈ rotationPairs,
    IsRotation (occurrenceValue s p.1) ∧
      IsRotation (occurrenceValue s p.2)
  reflectionTyped : ∀ p ∈ reflectionPairs,
    ¬IsRotation (occurrenceValue s p.1) ∧
      ¬IsRotation (occurrenceValue s p.2)
  endpointsNodup :
    (pairCoordinates rotationPairs ++
      pairCoordinates reflectionPairs).Nodup

noncomputable def canonicalSameTypePairReservoir
    (s : List (Group A)) : SameTypePairReservoir s := by
  classical
  let rotationPairs := pairUp (rotationOccurrences s).toList
  let reflectionPairs := pairUp (reflectionOccurrences s).toList
  refine {
    rotationPairs := rotationPairs
    reflectionPairs := reflectionPairs
    rotationCover := ?_
    reflectionCover := ?_
    rotationPairCount := ?_
    reflectionPairCount := ?_
    rotationTyped := ?_
    reflectionTyped := ?_
    endpointsNodup := ?_
  }
  · exact pairCoordinates_pairUp_append_unpairedSuffix _
  · exact pairCoordinates_pairUp_append_unpairedSuffix _
  · simp [rotationPairs, length_pairUp, Finset.length_toList]
  · simp [reflectionPairs, length_pairUp, Finset.length_toList]
  · intro p hp
    have hp1 : p.1 ∈ (rotationOccurrences s).toList :=
      pairUp_fst_mem_source hp
    have hp2 : p.2 ∈ (rotationOccurrences s).toList :=
      pairUp_snd_mem_source hp
    have hm1 : p.1 ∈ rotationOccurrences s := Finset.mem_toList.mp hp1
    have hm2 : p.2 ∈ rotationOccurrences s := Finset.mem_toList.mp hp2
    simpa [rotationOccurrences] using And.intro hm1 hm2
  · intro p hp
    have hp1 : p.1 ∈ (reflectionOccurrences s).toList :=
      pairUp_fst_mem_source hp
    have hp2 : p.2 ∈ (reflectionOccurrences s).toList :=
      pairUp_snd_mem_source hp
    have hm1 : p.1 ∈ reflectionOccurrences s := Finset.mem_toList.mp hp1
    have hm2 : p.2 ∈ reflectionOccurrences s := Finset.mem_toList.mp hp2
    simpa [reflectionOccurrences] using And.intro hm1 hm2
  · have hrot :
        (pairCoordinates rotationPairs).Nodup := by
      exact nodup_pairCoordinates_pairUp _ (rotationOccurrences s).nodup_toList
    have href :
        (pairCoordinates reflectionPairs).Nodup := by
      exact nodup_pairCoordinates_pairUp _ (reflectionOccurrences s).nodup_toList
    apply hrot.append href
    rw [List.disjoint_left]
    intro i hiRot hiRef
    have hiRotList : i ∈ (rotationOccurrences s).toList := by
      rw [← pairCoordinates_pairUp_append_unpairedSuffix
        (rotationOccurrences s).toList]
      exact List.mem_append_left _ hiRot
    have hiRefList : i ∈ (reflectionOccurrences s).toList := by
      rw [← pairCoordinates_pairUp_append_unpairedSuffix
        (reflectionOccurrences s).toList]
      exact List.mem_append_left _ hiRef
    have hiRotFin : i ∈ rotationOccurrences s := Finset.mem_toList.mp hiRotList
    have hiRefFin : i ∈ reflectionOccurrences s := Finset.mem_toList.mp hiRefList
    simp [rotationOccurrences] at hiRotFin
    simp [reflectionOccurrences, hiRotFin] at hiRefFin

theorem canonicalSameTypePairReservoir_totalPairCount
    (s : List (Group A)) :
    (canonicalSameTypePairReservoir s).rotationPairs.length +
        (canonicalSameTypePairReservoir s).reflectionPairs.length =
      (rotationOccurrences s).card / 2 +
        (reflectionOccurrences s).card / 2 := by
  rw [(canonicalSameTypePairReservoir s).rotationPairCount,
    (canonicalSameTypePairReservoir s).reflectionPairCount]

theorem canonicalSameTypePairReservoir_pairCount_of_odd_total
    (s : List (Group A)) {Q D a b : ℕ}
    (hD : Odd D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hab : a + b = 2 * Q + D) :
    (canonicalSameTypePairReservoir s).rotationPairs.length +
        (canonicalSameTypePairReservoir s).reflectionPairs.length =
      Q + (D - 1) / 2 := by
  rw [canonicalSameTypePairReservoir_totalPairCount, hrot, href,
    Nat.add_comm]
  exact same_type_pair_count hD hab

end ConcreteReservoir

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.pairCoordinates_pairUp_append_unpairedSuffix
#print axioms GaoLean.ConcreteGDihedral.nodup_pairCoordinates_pairUp
#print axioms GaoLean.ConcreteGDihedral.canonicalSameTypePairReservoir
#print axioms GaoLean.ConcreteGDihedral.canonicalSameTypePairReservoir_pairCount_of_odd_total
