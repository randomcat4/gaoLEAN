import GaoLean.PGGMOOrdinarySeed
import GaoLean.PGGMOTheorem11

/-!
# Literal singleton occurrence layers for ordinary DGM

Each labelled occurrence is retained as its own singleton layer.  Repeated
source values therefore remain repeated layers.  The exact-layer spectrum is
identified with the ordinary exact occurrence spectrum by explicit head/tail
reindexing of selections.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]
noncomputable local instance ordinarySingletonDecidableEq :
    DecidableEq A := Classical.decEq A


/-- One singleton value layer for every literal source occurrence, in source
order.  Equal source values remain distinct list entries. -/
noncomputable def ordinaryOccurrenceSetpartition (xs : List A) :
    List (Finset A) := by
  classical
  exact xs.map fun x ↦ {x}

@[simp]
theorem length_ordinaryOccurrenceSetpartition (xs : List A) :
    (ordinaryOccurrenceSetpartition xs).length = xs.length := by
  classical
  simp [ordinaryOccurrenceSetpartition]

@[simp]
theorem ordinaryOccurrenceSetpartition_nil :
    ordinaryOccurrenceSetpartition ([] : List A) = [] := by
  classical
  simp [ordinaryOccurrenceSetpartition]

@[simp]
theorem ordinaryOccurrenceSetpartition_cons (x : A) (xs : List A) :
    ordinaryOccurrenceSetpartition (x :: xs) =
      {x} :: ordinaryOccurrenceSetpartition xs := by
  classical
  simp [ordinaryOccurrenceSetpartition]

/-- Every literal singleton occurrence layer is nonempty. -/
theorem ordinaryOccurrenceSetpartition_nonempty (xs : List A) :
    IsNonemptySetPartition (ordinaryOccurrenceSetpartition xs) := by
  classical
  intro B hB
  obtain ⟨x, _hx, rfl⟩ := List.mem_map.mp hB
  exact ⟨x, by simp⟩

/-! ## Occurrence-faithful head/tail selection transport -/

/-- Remove the head occurrence and reindex every selected tail occurrence. -/
noncomputable def ordinaryTailSelection {x : A} {xs : List A}
    (I : Selection (x :: xs)) : Selection xs := by
  classical
  exact Finset.univ.filter fun j ↦ j.succ ∈ I

/-- Reindex a tail selection after adjoining one new source head. -/
def ordinaryLiftTailSelection {x : A} {xs : List A}
    (I : Selection xs) : Selection (x :: xs) :=
  I.map ⟨Fin.succ, Fin.succ_injective _⟩

@[simp]
theorem mem_ordinaryTailSelection_iff {x : A} {xs : List A}
    (I : Selection (x :: xs)) (j : Occurrence xs) :
    j ∈ ordinaryTailSelection I ↔ j.succ ∈ I := by
  classical
  simp [ordinaryTailSelection]

@[simp]
theorem mem_ordinaryLiftTailSelection_iff {x : A} {xs : List A}
    (I : Selection xs) (j : Occurrence xs) :
    j.succ ∈ ordinaryLiftTailSelection (x := x) I ↔ j ∈ I := by
  classical
  simp [ordinaryLiftTailSelection]

@[simp]
theorem zero_not_mem_ordinaryLiftTailSelection {x : A} {xs : List A}
    (I : Selection xs) :
    (0 : Occurrence (x :: xs)) ∉ ordinaryLiftTailSelection (x := x) I := by
  classical
  simp [ordinaryLiftTailSelection]

@[simp]
theorem card_ordinaryLiftTailSelection {x : A} {xs : List A}
    (I : Selection xs) :
    (ordinaryLiftTailSelection (x := x) I).card = I.card :=
  Finset.card_map _

theorem ordinaryLift_tailSelection_eq_erase_zero {x : A} {xs : List A}
    (I : Selection (x :: xs)) :
    ordinaryLiftTailSelection (x := x) (ordinaryTailSelection I) =
      I.erase 0 := by
  classical
  ext i
  refine Fin.cases ?_ (fun j ↦ ?_) i
  · simp
  · simp

theorem card_ordinaryTailSelection_of_not_mem_zero
    {x : A} {xs : List A} (I : Selection (x :: xs))
    (hzero : (0 : Occurrence (x :: xs)) ∉ I) :
    (ordinaryTailSelection I).card = I.card := by
  rw [← card_ordinaryLiftTailSelection (x := x),
    ordinaryLift_tailSelection_eq_erase_zero,
    Finset.erase_eq_of_notMem hzero]

theorem card_ordinaryTailSelection_of_mem_zero
    {x : A} {xs : List A} (I : Selection (x :: xs))
    (hzero : (0 : Occurrence (x :: xs)) ∈ I) :
    (ordinaryTailSelection I).card + 1 = I.card := by
  rw [← card_ordinaryLiftTailSelection (x := x),
    ordinaryLift_tailSelection_eq_erase_zero,
    Finset.card_erase_of_mem hzero]
  have hpos : 0 < I.card := Finset.card_pos.mpr ⟨0, hzero⟩
  omega

/-- Tail reindexing preserves the literal selected sum. -/
theorem sum_ordinaryTailSelection {x : A} {xs : List A}
    (I : Selection (x :: xs)) (f : Occurrence (x :: xs) → A) :
    (∑ j ∈ ordinaryTailSelection I, f j.succ) =
      ∑ i ∈ I.erase 0, f i := by
  classical
  rw [← ordinaryLift_tailSelection_eq_erase_zero (x := x) I]
  simp [ordinaryLiftTailSelection]

@[simp]
theorem ordinaryExactSpectrum_zero (xs : List A) :
    ordinaryExactSpectrum xs 0 = {0} := by
  classical
  ext y
  rw [mem_ordinaryExactSpectrum_iff, Finset.mem_singleton]
  constructor
  · rintro ⟨I, hIcard, hIsum⟩
    have hI : I = ∅ := Finset.card_eq_zero.mp hIcard
    simpa [hI] using hIsum.symm
  · rintro rfl
    exact ⟨∅, by simp, by simp⟩

@[simp]
theorem ordinaryExactSpectrum_nil_succ (n : ℕ) :
    ordinaryExactSpectrum ([] : List A) (n + 1) = ∅ := by
  classical
  ext y
  rw [mem_ordinaryExactSpectrum_iff]
  constructor
  · rintro ⟨I, hIcard, _hIsum⟩
    have hI : I = ∅ := by
      ext i
      exact Fin.elim0 i
    have : 0 = n + 1 := by simpa [hI] using hIcard
    omega
  · simp

/-- Exact ordinary occurrence spectra obey the same skip/take recursion as
singleton DGM layers.  Both directions explicitly transport the selected
occurrence finset. -/
theorem ordinaryExactSpectrum_cons_succ
    (x : A) (xs : List A) (n : ℕ) :
    ordinaryExactSpectrum (x :: xs) (n + 1) =
      ordinaryExactSpectrum xs (n + 1) ∪
        ({x} + ordinaryExactSpectrum xs n) := by
  classical
  ext y
  simp only [mem_ordinaryExactSpectrum_iff, Finset.mem_union]
  constructor
  · rintro ⟨I, hIcard, hIsum⟩
    by_cases hzero : (0 : Occurrence (x :: xs)) ∈ I
    · right
      let J := ordinaryTailSelection I
      let w : A := ∑ j ∈ J, occurrenceValue xs j
      have hJcard : J.card = n := by
        have hc := card_ordinaryTailSelection_of_mem_zero I hzero
        change J.card + 1 = I.card at hc
        rw [hIcard] at hc
        omega
      have hw : w ∈ ordinaryExactSpectrum xs n :=
        (mem_ordinaryExactSpectrum_iff xs n w).2 ⟨J, hJcard, rfl⟩
      have htail :
          w = ∑ i ∈ I.erase 0, occurrenceValue (x :: xs) i := by
        dsimp only [w, J]
        exact sum_ordinaryTailSelection I (occurrenceValue (x :: xs))
      have hy : x + w = y := by
        calc
          x + w =
              occurrenceValue (x :: xs) 0 +
                ∑ i ∈ I.erase 0, occurrenceValue (x :: xs) i := by
                  rw [htail]
                  simp [occurrenceValue]
          _ = ∑ i ∈ I, occurrenceValue (x :: xs) i := by
                rw [add_comm]
                exact I.sum_erase_add (occurrenceValue (x :: xs)) hzero
          _ = y := hIsum
      exact Finset.mem_add.mpr ⟨x, by simp, w, hw, hy⟩
    · left
      let J := ordinaryTailSelection I
      have hJcard : J.card = n + 1 := by
        rw [card_ordinaryTailSelection_of_not_mem_zero I hzero]
        exact hIcard
      have hJsum :
          (∑ j ∈ J, occurrenceValue xs j) = y := by
        calc
          (∑ j ∈ J, occurrenceValue xs j) =
              ∑ i ∈ I.erase 0, occurrenceValue (x :: xs) i := by
                exact sum_ordinaryTailSelection I
                  (occurrenceValue (x :: xs))
          _ = ∑ i ∈ I, occurrenceValue (x :: xs) i := by
                rw [Finset.erase_eq_of_notMem hzero]
          _ = y := hIsum
      exact ⟨J, hJcard, hJsum⟩
  · rintro (htail | htake)
    · obtain ⟨J, hJcard, hJsum⟩ := htail
      let I := ordinaryLiftTailSelection (x := x) J
      refine ⟨I, ?_, ?_⟩
      · simpa [I] using hJcard
      · simpa [I, ordinaryLiftTailSelection, occurrenceValue] using hJsum
    · rcases Finset.mem_add.mp htake with ⟨a, ha, w, hw, haw⟩
      have haeq : a = x := by simpa using ha
      subst a
      obtain ⟨J, hJcard, hJsum⟩ :=
        (mem_ordinaryExactSpectrum_iff xs n w).1 hw
      let J' := ordinaryLiftTailSelection (x := x) J
      let I : Selection (x :: xs) :=
        Finset.cons 0 J' (zero_not_mem_ordinaryLiftTailSelection
          (x := x) J)
      refine ⟨I, ?_, ?_⟩
      · simp [I, J', hJcard]
      · calc
          (∑ i ∈ I, occurrenceValue (x :: xs) i) =
              x + ∑ j ∈ J, occurrenceValue xs j := by
                simp [I, J', ordinaryLiftTailSelection, occurrenceValue]
          _ = x + w := by rw [hJsum]
          _ = y := haw

/-- The literal singleton-layer spectrum is exactly the labelled ordinary
exact spectrum. -/
theorem layerSubsumSpectrum_ordinaryOccurrenceSetpartition
    (xs : List A) (r : ℕ) :
    layerSubsumSpectrum (ordinaryOccurrenceSetpartition xs) r =
      ordinaryExactSpectrum xs r := by
  classical
  induction xs generalizing r with
  | nil =>
      cases r with
      | zero => simp
      | succ r => simp [Nat.succ_eq_add_one]
  | cons x xs ih =>
      cases r with
      | zero => simp
      | succ r =>
          rw [ordinaryOccurrenceSetpartition_cons,
            layerSubsumSpectrum_cons_succ,
            ordinaryExactSpectrum_cons_succ,
            ih, ih]

/-! ## Literal raw multiplicity ledger -/

/-- Adding a source head changes one value fiber by one exactly when that head
has the requested value. -/
theorem card_occurrenceFiber_cons
    (x : A) (xs : List A) (a : A) :
    (occurrenceFiber (x :: xs) a).card =
      (if x = a then 1 else 0) + (occurrenceFiber xs a).card := by
  classical
  let p : Fin (xs.length + 1) → Prop := fun i ↦
    occurrenceValue (x :: xs) i = a
  have hwhole : occurrenceFiber (x :: xs) a =
      Finset.univ.filter p := by
    ext i
    simp [occurrenceFiber, p]
  have htail : (Finset.univ.filter fun i : Fin xs.length ↦ p i.succ) =
      occurrenceFiber xs a := by
    ext i
    simp [occurrenceFiber, p, occurrenceValue]
  rw [hwhole, Fin.card_filter_univ_succ', htail]
  by_cases hx : x = a <;> simp [p, occurrenceValue, hx]

/-- Raw singleton-layer multiplicity is literal source occurrence
multiplicity, not support membership. -/
theorem rawLayerMultiplicity_ordinaryOccurrenceSetpartition
    (xs : List A) (a : A) :
    rawLayerMultiplicity (ordinaryOccurrenceSetpartition xs) a =
      (occurrenceFiber xs a).card := by
  classical
  induction xs with
  | nil =>
      have hempty : occurrenceFiber ([] : List A) a = ∅ := by
        ext i
        exact Fin.elim0 i
      rw [ordinaryOccurrenceSetpartition_nil, hempty]
      simp [rawLayerMultiplicity]
  | cons x xs ih =>
      rw [ordinaryOccurrenceSetpartition_cons, card_occurrenceFiber_cons]
      by_cases hxa : x = a
      · rw [rawLayerMultiplicity_cons_of_mem
          ({x} : Finset A) (ordinaryOccurrenceSetpartition xs) a (by
            simp [hxa]), ih]
        simp [hxa, Nat.add_comm]
      · rw [rawLayerMultiplicity_cons_of_not_mem
          ({x} : Finset A) (ordinaryOccurrenceSetpartition xs) a (by
            simpa [eq_comm] using hxa), ih]
        simp [hxa]

/-- Consequently the raw DGM capped incidence mass is exactly the capped
labelled fiber mass used by ordinary seed preparation. -/
theorem rawDgmCappedMultiplicitySum_ordinaryOccurrenceSetpartition
    (xs : List A) (r : ℕ) :
    rawDgmCappedMultiplicitySum (ordinaryOccurrenceSetpartition xs) r =
      cappedFiberMass xs r := by
  classical
  unfold rawDgmCappedMultiplicitySum cappedFiberMass
  apply Finset.sum_congr rfl
  intro a _ha
  rw [rawLayerMultiplicity_ordinaryOccurrenceSetpartition]

/-! ## DGM connectors -/

/-- The DGM bound for the literal ordinary singleton occurrence layers. -/
noncomputable def OrdinaryOccurrenceDGMSetpartitionBound
    (xs : List A) (r : ℕ) : Prop := by
  classical
  exact DGMSetpartitionBound (ordinaryOccurrenceSetpartition xs) r

/-- Direct specialization of a General DGM input to the ordinary singleton
occurrence layers. -/
theorem dgmSetpartitionBound_ordinaryOccurrenceSetpartition_of_generalDGM
    [instA : DecidableEq A] (hDGM : GeneralDGMSetpartitionTheorem A)
    (xs : List A) (r : ℕ) (hrpos : 1 ≤ r) (hr : r ≤ xs.length) :
    OrdinaryOccurrenceDGMSetpartitionBound xs r := by
  have hinst : instA = ordinarySingletonDecidableEq :=
    Subsingleton.elim _ _
  cases hinst
  unfold OrdinaryOccurrenceDGMSetpartitionBound
  exact hDGM (ordinaryOccurrenceSetpartition xs) r
    (ordinaryOccurrenceSetpartition_nonempty xs) hrpos (by simpa using hr)

/-- The same connector through the finite-type wrapper which hides the
classical equality decision. -/
theorem dgmSetpartitionBound_ordinaryOccurrenceSetpartition
    (hDGM : FiniteDGMSetpartitionInput A)
    (xs : List A) (r : ℕ) (hrpos : 1 ≤ r) (hr : r ≤ xs.length) :
    OrdinaryOccurrenceDGMSetpartitionBound xs r := by
  classical
  exact dgmSetpartitionBound_ordinaryOccurrenceSetpartition_of_generalDGM
    hDGM xs r hrpos hr

/-- If the ordinary target spectrum has trivial subgroup stabilizer, its
stabilizer-quotient capped sum is exactly the raw singleton-layer sum. -/
theorem stabilizerDgmCappedMultiplicitySum_ordinary_eq_raw_of_stabilizer_eq_bot
    (xs : List A) (r : ℕ) (hr : r ≤ xs.length)
    (hstab : AddAction.stabilizer A
      (ordinaryExactSpectrum xs r : Set A) = ⊥) :
    stabilizerDgmCappedMultiplicitySum
        (ordinaryExactSpectrum xs r)
        (ordinaryOccurrenceSetpartition xs) r =
      rawDgmCappedMultiplicitySum
        (ordinaryOccurrenceSetpartition xs) r := by
  classical
  let T := ordinaryExactSpectrum xs r
  have hT : T.Nonempty := by
    simpa [T] using ordinaryExactSpectrum_nonempty xs r hr
  have hadd : T.addStab = {0} := by
    ext a
    rw [← Finset.mem_coe, Finset.coe_addStab hT]
    change a ∈ AddAction.stabilizer A
      (ordinaryExactSpectrum xs r : Set A) ↔ a ∈ ({0} : Finset A)
    rw [hstab]
    simp
  exact dgmStabilizerCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
    T hT hadd (ordinaryOccurrenceSetpartition xs) r

end GaoLean

#print axioms GaoLean.length_ordinaryOccurrenceSetpartition
#print axioms GaoLean.ordinaryOccurrenceSetpartition_nonempty
#print axioms GaoLean.ordinaryExactSpectrum_cons_succ
#print axioms GaoLean.layerSubsumSpectrum_ordinaryOccurrenceSetpartition
#print axioms GaoLean.rawLayerMultiplicity_ordinaryOccurrenceSetpartition
#print axioms GaoLean.rawDgmCappedMultiplicitySum_ordinaryOccurrenceSetpartition
#print axioms GaoLean.dgmSetpartitionBound_ordinaryOccurrenceSetpartition_of_generalDGM
#print axioms GaoLean.dgmSetpartitionBound_ordinaryOccurrenceSetpartition
#print axioms GaoLean.stabilizerDgmCappedMultiplicitySum_ordinary_eq_raw_of_stabilizer_eq_bot
