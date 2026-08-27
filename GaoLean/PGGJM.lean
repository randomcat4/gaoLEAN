import GaoLean.GAOARDihedralBlocks
import GaoLean.PGDavenportConvolution
import GaoLean.PGOlson
import GaoLean.PGOrdinaryGMOBridge

/-!
# Small Davenport bound for generalized dihedral groups

This file proves the Godara--Joshi--Mazumdar bound needed by the frozen
13-page manuscript.  The proof is occurrence-labelled and does not import
the invariant-theoretic Noether-number argument.

For the reflection occurrences in their canonical order, form the path of
adjacent coordinate differences.  Together with all rotation coordinates,
this gives `a - 1 + b` additive terms.  A zero-sum selection of path edges
has a signed boundary: common endpoints cancel, while the remaining positive
and negative reflection endpoints are disjoint and balanced.  The existing
balanced-ordering theorem then lifts that boundary, and the selected
rotations, to a literal product-one ordering.
-/

namespace GaoLean.ConcreteGDihedral

open scoped BigOperators

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Canonical list of all reflection occurrences of a source. -/
noncomputable def reflectionOccurrenceList (s : List (Group A)) :
    List (Occurrence s) :=
  (reflectionOccurrences s).toList

/-- Coordinate differences on the consecutive edges of the canonical
reflection-occurrence path. -/
noncomputable def adjacentReflectionDifferences
    (s : List (Group A)) : List A :=
  List.ofFn fun i : Fin ((reflectionOccurrences s).card - 1) =>
    coordinate (occurrenceValue s
      ((reflectionOccurrenceList s).get
        ⟨i.1, by
          have hi := i.2
          simp [reflectionOccurrenceList]
          omega⟩)) -
    coordinate (occurrenceValue s
      ((reflectionOccurrenceList s).get
        ⟨i.1 + 1, by
          have hi := i.2
          simp [reflectionOccurrenceList]
          omega⟩))

@[simp]
theorem length_adjacentReflectionDifferences (s : List (Group A)) :
    (adjacentReflectionDifferences s).length =
      (reflectionOccurrences s).card - 1 := by
  simp [adjacentReflectionDifferences]

/-- Source endpoint at the start of a selected reflection-path edge. -/
noncomputable def reflectionEdgeStart
    (s : List (Group A))
    (i : Occurrence (adjacentReflectionDifferences s)) : Occurrence s :=
  (reflectionOccurrenceList s).get
    ⟨i.1, by
      have hi := i.2
      have hi' : i.1 < (reflectionOccurrences s).card - 1 := by
        simpa only [length_adjacentReflectionDifferences] using hi
      simpa [reflectionOccurrenceList] using
        (show i.1 < (reflectionOccurrences s).card by omega)⟩

/-- Source endpoint at the end of a selected reflection-path edge. -/
noncomputable def reflectionEdgeEnd
    (s : List (Group A))
    (i : Occurrence (adjacentReflectionDifferences s)) : Occurrence s :=
  (reflectionOccurrenceList s).get
    ⟨i.1 + 1, by
      have hi := i.2
      have hi' : i.1 < (reflectionOccurrences s).card - 1 := by
        simpa only [length_adjacentReflectionDifferences] using hi
      simpa [reflectionOccurrenceList] using (show
        i.1 + 1 < (reflectionOccurrences s).card by omega)⟩

theorem reflectionEdgeStart_injective (s : List (Group A)) :
    Function.Injective (reflectionEdgeStart s) := by
  intro i j hij
  have hget :
      (⟨i.1, by
        have hi := i.2
        have hi' : i.1 < (reflectionOccurrences s).card - 1 := by
          simpa only [length_adjacentReflectionDifferences] using hi
        simpa [reflectionOccurrenceList] using (show
          i.1 < (reflectionOccurrences s).card by omega)⟩ :
          Fin (reflectionOccurrenceList s).length) =
      ⟨j.1, by
        have hj := j.2
        have hj' : j.1 < (reflectionOccurrences s).card - 1 := by
          simpa only [length_adjacentReflectionDifferences] using hj
        simpa [reflectionOccurrenceList] using (show
          j.1 < (reflectionOccurrences s).card by omega)⟩ :=
    (reflectionOccurrences s).nodup_toList.injective_get hij
  apply Fin.ext
  exact congrArg
    (fun x : Fin (reflectionOccurrenceList s).length => x.val) hget

theorem reflectionEdgeEnd_injective (s : List (Group A)) :
    Function.Injective (reflectionEdgeEnd s) := by
  intro i j hij
  have hget :
      (⟨i.1 + 1, by
        have hi := i.2
        have hi' : i.1 < (reflectionOccurrences s).card - 1 := by
          simpa only [length_adjacentReflectionDifferences] using hi
        simpa [reflectionOccurrenceList] using (show
          i.1 + 1 < (reflectionOccurrences s).card by omega)⟩ :
          Fin (reflectionOccurrenceList s).length) =
      ⟨j.1 + 1, by
        have hj := j.2
        have hj' : j.1 < (reflectionOccurrences s).card - 1 := by
          simpa only [length_adjacentReflectionDifferences] using hj
        simpa [reflectionOccurrenceList] using (show
          j.1 + 1 < (reflectionOccurrences s).card by omega)⟩ :=
    (reflectionOccurrences s).nodup_toList.injective_get hij
  apply Fin.ext
  have hval := congrArg
    (fun x : Fin (reflectionOccurrenceList s).length => x.val) hget
  have hval' : i.1 + 1 = j.1 + 1 := hval
  omega

noncomputable def reflectionEdgeStartEmbedding (s : List (Group A)) :
    Occurrence (adjacentReflectionDifferences s) ↪ Occurrence s :=
  ⟨reflectionEdgeStart s, reflectionEdgeStart_injective s⟩

noncomputable def reflectionEdgeEndEmbedding (s : List (Group A)) :
    Occurrence (adjacentReflectionDifferences s) ↪ Occurrence s :=
  ⟨reflectionEdgeEnd s, reflectionEdgeEnd_injective s⟩

@[simp]
theorem occurrenceValue_adjacentReflectionDifferences
    (s : List (Group A))
    (i : Occurrence (adjacentReflectionDifferences s)) :
    occurrenceValue (adjacentReflectionDifferences s) i =
      coordinate (occurrenceValue s (reflectionEdgeStart s i)) -
        coordinate (occurrenceValue s (reflectionEdgeEnd s i)) := by
  simp [adjacentReflectionDifferences, reflectionEdgeStart,
    reflectionEdgeEnd, occurrenceValue, List.get_eq_getElem]

theorem reflectionEdgeStart_mem (s : List (Group A))
    (i : Occurrence (adjacentReflectionDifferences s)) :
    reflectionEdgeStart s i ∈ reflectionOccurrences s := by
  apply Finset.mem_toList.mp
  exact (reflectionOccurrenceList s).get_mem _

theorem reflectionEdgeEnd_mem (s : List (Group A))
    (i : Occurrence (adjacentReflectionDifferences s)) :
    reflectionEdgeEnd s i ∈ reflectionOccurrences s := by
  apply Finset.mem_toList.mp
  exact (reflectionOccurrenceList s).get_mem _

/-- Starts and ends of a selected set of reflection-path edges. -/
noncomputable def reflectionEdgeStarts (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) : Selection s :=
  E.map (reflectionEdgeStartEmbedding s)

noncomputable def reflectionEdgeEnds (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) : Selection s :=
  E.map (reflectionEdgeEndEmbedding s)

/-- Positive and negative boundary vertices after cancelling common
endpoints of consecutive selected path edges. -/
noncomputable def reflectionBoundaryPlus (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) : Selection s :=
  reflectionEdgeStarts s E \ reflectionEdgeEnds s E

noncomputable def reflectionBoundaryMinus (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) : Selection s :=
  reflectionEdgeEnds s E \ reflectionEdgeStarts s E

theorem reflectionBoundary_disjoint (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) :
    Disjoint (reflectionBoundaryPlus s E) (reflectionBoundaryMinus s E) := by
  rw [Finset.disjoint_left]
  intro i hiPlus hiMinus
  exact (Finset.mem_sdiff.mp hiPlus).2 (Finset.mem_sdiff.mp hiMinus).1

theorem card_reflectionBoundaryPlus_eq_minus (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) :
    (reflectionBoundaryPlus s E).card =
      (reflectionBoundaryMinus s E).card := by
  classical
  simp [reflectionBoundaryPlus, reflectionBoundaryMinus,
    reflectionEdgeStarts, reflectionEdgeEnds, Finset.card_sdiff,
    Finset.inter_comm]

theorem reflectionBoundary_typed (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) :
    (∀ i ∈ reflectionBoundaryPlus s E,
      ¬IsRotation (occurrenceValue s i)) ∧
    (∀ i ∈ reflectionBoundaryMinus s E,
      ¬IsRotation (occurrenceValue s i)) := by
  constructor
  · intro i hi
    have hiStart : i ∈ reflectionEdgeStarts s E :=
      (Finset.mem_sdiff.mp hi).1
    rcases Finset.mem_map.mp hiStart with ⟨j, hj, rfl⟩
    change ¬IsRotation (occurrenceValue s (reflectionEdgeStart s j))
    simpa [reflectionOccurrences] using reflectionEdgeStart_mem s j
  · intro i hi
    have hiEnd : i ∈ reflectionEdgeEnds s E :=
      (Finset.mem_sdiff.mp hi).1
    rcases Finset.mem_map.mp hiEnd with ⟨j, hj, rfl⟩
    change ¬IsRotation (occurrenceValue s (reflectionEdgeEnd s j))
    simpa [reflectionOccurrences] using reflectionEdgeEnd_mem s j

theorem reflectionBoundaryPlus_nonempty (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) (hE : E.Nonempty) :
    (reflectionBoundaryPlus s E).Nonempty := by
  classical
  let e := E.min' hE
  have he : e ∈ E := Finset.min'_mem E hE
  have hstart : reflectionEdgeStart s e ∈ reflectionEdgeStarts s E := by
    exact Finset.mem_map.mpr ⟨e, he, rfl⟩
  refine ⟨reflectionEdgeStart s e,
    Finset.mem_sdiff.mpr ⟨hstart, ?_⟩⟩
  intro hend
  rcases Finset.mem_map.mp hend with ⟨j, hj, hje⟩
  change reflectionEdgeEnd s j = reflectionEdgeStart s e at hje
  have hindices : j.1 + 1 = e.1 := by
    have hget :
        (⟨j.1 + 1, by
          have hjlt := j.2
          have hjlt' : j.1 < (reflectionOccurrences s).card - 1 := by
            simpa only [length_adjacentReflectionDifferences] using hjlt
          simpa [reflectionOccurrenceList] using (show
            j.1 + 1 < (reflectionOccurrences s).card by omega)⟩ :
            Fin (reflectionOccurrenceList s).length) =
        ⟨e.1, by
          have helt := e.2
          have helt' : e.1 < (reflectionOccurrences s).card - 1 := by
            simpa only [length_adjacentReflectionDifferences] using helt
          simpa [reflectionOccurrenceList] using (show
            e.1 < (reflectionOccurrences s).card by omega)⟩ :=
      (reflectionOccurrences s).nodup_toList.injective_get hje
    exact congrArg Fin.val hget
  have hmin : e ≤ j := Finset.min'_le E j hj
  have : j.1 < e.1 := by omega
  exact (not_lt_of_ge hmin) this

theorem sum_reflectionBoundary_eq_edgeSum (s : List (Group A))
    (E : Selection (adjacentReflectionDifferences s)) :
    (∑ i ∈ reflectionBoundaryPlus s E,
        coordinate (occurrenceValue s i)) -
      (∑ i ∈ reflectionBoundaryMinus s E,
        coordinate (occurrenceValue s i)) =
      ∑ e ∈ E, occurrenceValue (adjacentReflectionDifferences s) e := by
  classical
  let S := reflectionEdgeStarts s E
  let T := reflectionEdgeEnds s E
  have hstart :
      (∑ i ∈ S, coordinate (occurrenceValue s i)) =
        ∑ e ∈ E, coordinate (occurrenceValue s (reflectionEdgeStart s e)) := by
    simp [S, reflectionEdgeStarts, reflectionEdgeStartEmbedding]
  have hend :
      (∑ i ∈ T, coordinate (occurrenceValue s i)) =
        ∑ e ∈ E, coordinate (occurrenceValue s (reflectionEdgeEnd s e)) := by
    simp [T, reflectionEdgeEnds, reflectionEdgeEndEmbedding]
  have hplus :
      (∑ i ∈ S \ T, coordinate (occurrenceValue s i)) +
          ∑ i ∈ S ∩ T, coordinate (occurrenceValue s i) =
        ∑ i ∈ S, coordinate (occurrenceValue s i) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S T)]
    congr 2
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hminus :
      (∑ i ∈ T \ S, coordinate (occurrenceValue s i)) +
          ∑ i ∈ T ∩ S, coordinate (occurrenceValue s i) =
        ∑ i ∈ T, coordinate (occurrenceValue s i) := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter T S)]
    congr 2
    ext i
    simp only [Finset.mem_union, Finset.mem_sdiff, Finset.mem_inter]
    tauto
  have hinter :
      (∑ i ∈ S ∩ T, coordinate (occurrenceValue s i)) =
        ∑ i ∈ T ∩ S, coordinate (occurrenceValue s i) := by
    rw [Finset.inter_comm]
  change (∑ i ∈ S \ T, coordinate (occurrenceValue s i)) -
      (∑ i ∈ T \ S, coordinate (occurrenceValue s i)) = _
  calc
    (∑ i ∈ S \ T, coordinate (occurrenceValue s i)) -
        (∑ i ∈ T \ S, coordinate (occurrenceValue s i)) =
      ((∑ i ∈ S \ T, coordinate (occurrenceValue s i)) +
        ∑ i ∈ S ∩ T, coordinate (occurrenceValue s i)) -
      ((∑ i ∈ T \ S, coordinate (occurrenceValue s i)) +
        ∑ i ∈ T ∩ S, coordinate (occurrenceValue s i)) := by
          rw [hinter]
          abel
    _ = (∑ i ∈ S, coordinate (occurrenceValue s i)) -
        (∑ i ∈ T, coordinate (occurrenceValue s i)) := by
          rw [hplus, hminus]
    _ = (∑ e ∈ E, coordinate (occurrenceValue s
          (reflectionEdgeStart s e))) -
        (∑ e ∈ E, coordinate (occurrenceValue s
          (reflectionEdgeEnd s e))) := by rw [hstart, hend]
    _ = ∑ e ∈ E, occurrenceValue
        (adjacentReflectionDifferences s) e := by
          simp_rw [occurrenceValue_adjacentReflectionDifferences]
          rw [Finset.sum_sub_distrib]

/-- Image of selected rotation-coordinate occurrences in the source. -/
noncomputable def gjmRotationSourceSelection (s : List (Group A))
    (X : Selection (rotationCoordinateSequence s)) : Selection s :=
  X.image (rotationSourceOccurrence s)

theorem card_gjmRotationSourceSelection (s : List (Group A))
    (X : Selection (rotationCoordinateSequence s)) :
    (gjmRotationSourceSelection s X).card = X.card := by
  classical
  rw [gjmRotationSourceSelection,
    Finset.card_image_of_injective _ (rotationSourceOccurrence_injective s)]

/-- A source one term longer than an ordinary Davenport threshold has a
nonempty product-one subselection in its generalized-dihedral lift. -/
theorem exists_nonempty_productOne_of_davenport_add_one
    (s : List (Group A)) (D : ℕ)
    (hD : OrdinaryDavenportAtMost A D)
    (hlen : s.length = D + 1) :
    ∃ I : Selection s, I.Nonempty ∧ IsProductOneSelection s I := by
  classical
  let edges := adjacentReflectionDifferences s
  let rotations := rotationCoordinateSequence s
  have hpartition :=
    card_reflectionOccurrences_add_card_rotationOccurrences s
  have hvirtual : D ≤ (edges ++ rotations).length := by
    have hedge : edges.length = (reflectionOccurrences s).card - 1 := by
      simp [edges]
    have hrot : rotations.length = (rotationOccurrences s).card := by
      simp [rotations, rotationCoordinateSequence]
    rw [List.length_append, hedge, hrot]
    omega
  obtain ⟨I, hIne, hIsum⟩ :=
    ordinaryDavenportAtLeast_of_atMost hD (edges ++ rotations) hvirtual
  let E := prefixSelection edges rotations I
  let X := suffixSelection edges rotations I
  have hcardSplit : E.card + X.card = I.card := by
    have hmulti := selectedMultiset_prefix_add_suffix edges rotations I
    have := congrArg Multiset.card hmulti
    simpa [E, X] using this
  have hsumSplit :
      (∑ e ∈ E, occurrenceValue edges e) +
        (∑ x ∈ X, occurrenceValue rotations x) = 0 := by
    have hsum := sum_prefixSelection_add_sum_suffixSelection edges rotations I
    rw [show (selectedMultiset (edges ++ rotations) I).sum = 0 by
      simpa [selectedMultiset] using hIsum] at hsum
    simpa [selectedMultiset, E, X] using hsum
  let RX := gjmRotationSourceSelection s X
  have hRXcard : RX.card = X.card :=
    card_gjmRotationSourceSelection s X
  have hRXtyped : ∀ i ∈ RX, IsRotation (occurrenceValue s i) := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨x, hx, rfl⟩
    simpa [rotationOccurrences] using rotationSourceOccurrence_mem s x
  have hRXsum :
      (∑ i ∈ RX, coordinate (occurrenceValue s i)) =
        ∑ x ∈ X, occurrenceValue rotations x := by
    unfold RX gjmRotationSourceSelection
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro x hx
      simpa [rotations] using
        (occurrenceValue_rotationCoordinateSequence s x).symm
    · intro x hx y hy hxy
      exact rotationSourceOccurrence_injective s hxy
  by_cases hEempty : E = ∅
  · have hXne : X.Nonempty := by
      rw [hEempty] at hcardSplit hsumSplit
      simp only [Finset.card_empty, zero_add] at hcardSplit
      have hIpos := Finset.card_pos.mpr hIne
      exact Finset.card_pos.mp (by omega)
    have hRXne : RX.Nonempty :=
      Finset.card_pos.mp (by rw [hRXcard]; exact Finset.card_pos.mpr hXne)
    have hRXzero : coordinateSum s RX = 0 := by
      unfold coordinateSum
      rw [hRXsum]
      simpa [hEempty] using hsumSplit
    exact ⟨RX, hRXne,
      isProductOneSelection_of_allRotation_coordinateSum_eq_zero
        s RX hRXtyped hRXzero⟩
  · have hEne : E.Nonempty := Finset.nonempty_iff_ne_empty.mpr hEempty
    let P := reflectionBoundaryPlus s E
    let N := reflectionBoundaryMinus s E
    have hPN : Disjoint P N := reflectionBoundary_disjoint s E
    have hPtyped : ∀ i ∈ P, ¬IsRotation (occurrenceValue s i) :=
      (reflectionBoundary_typed s E).1
    have hNtyped : ∀ i ∈ N, ¬IsRotation (occurrenceValue s i) :=
      (reflectionBoundary_typed s E).2
    have hPne : P.Nonempty := reflectionBoundaryPlus_nonempty s E hEne
    have hPcardN : P.card = N.card :=
      card_reflectionBoundaryPlus_eq_minus s E
    have hRXP : Disjoint RX P := by
      rw [Finset.disjoint_left]
      intro i hiRX hiP
      exact hPtyped i hiP (hRXtyped i hiRX)
    have hRXN : Disjoint RX N := by
      rw [Finset.disjoint_left]
      intro i hiRX hiN
      exact hNtyped i hiN (hRXtyped i hiRX)
    have hRXPN : Disjoint RX (P ∪ N) :=
      Finset.disjoint_union_right.mpr ⟨hRXP, hRXN⟩
    let J : Selection s := RX ∪ (P ∪ N)
    have hJne : J.Nonempty := by
      obtain ⟨i, hi⟩ := hPne
      exact ⟨i, by simp [J, hi]⟩
    let rotationPlus := occurrenceCoordinates s RX.toList
    let reflectionPlus := occurrenceCoordinates s P.toList
    let reflectionMinus := occurrenceCoordinates s N.toList
    have hrotationCarrier :
        selectedMultiset s RX =
          Multiset.ofList (rotationPlus.map (data A).rot) := by
      rw [← map_occurrenceValue_eq_rot s RX.toList]
      · change Multiset.map (occurrenceValue s) RX.1 =
          Multiset.map (occurrenceValue s) (Multiset.ofList RX.toList)
        exact congrArg (Multiset.map (occurrenceValue s))
          (Finset.coe_toList RX).symm
      · intro i hi
        exact hRXtyped i (Finset.mem_toList.mp hi)
    have hreflectionPlusCarrier :
        selectedMultiset s P =
          Multiset.ofList (reflectionPlus.map (data A).refl) := by
      rw [← map_occurrenceValue_eq_refl s P.toList]
      · change Multiset.map (occurrenceValue s) P.1 =
          Multiset.map (occurrenceValue s) (Multiset.ofList P.toList)
        exact congrArg (Multiset.map (occurrenceValue s))
          (Finset.coe_toList P).symm
      · intro i hi
        exact hPtyped i (Finset.mem_toList.mp hi)
    have hreflectionMinusCarrier :
        selectedMultiset s N =
          Multiset.ofList (reflectionMinus.map (data A).refl) := by
      rw [← map_occurrenceValue_eq_refl s N.toList]
      · change Multiset.map (occurrenceValue s) N.1 =
          Multiset.map (occurrenceValue s) (Multiset.ofList N.toList)
        exact congrArg (Multiset.map (occurrenceValue s))
          (Finset.coe_toList N).symm
      · intro i hi
        exact hNtyped i (Finset.mem_toList.mp hi)
    have hcarrier :
        selectedMultiset s J =
          Multiset.ofList (rotationPlus.map (data A).rot) +
          Multiset.ofList (([] : List A).map (data A).rot) +
          Multiset.ofList (reflectionPlus.map (data A).refl) +
          Multiset.ofList (reflectionMinus.map (data A).refl) := by
      rw [show selectedMultiset s J =
          selectedMultiset s RX + selectedMultiset s (P ∪ N) by
        exact selectedMultiset_union_of_disjoint_any s RX (P ∪ N) hRXPN]
      rw [show selectedMultiset s (P ∪ N) =
          selectedMultiset s P + selectedMultiset s N by
        exact selectedMultiset_union_of_disjoint_any s P N hPN]
      rw [hrotationCarrier, hreflectionPlusCarrier,
        hreflectionMinusCarrier]
      simp
    have hrotationSum : rotationPlus.sum =
        ∑ x ∈ X, occurrenceValue rotations x := by
      rw [show rotationPlus.sum =
          ∑ i ∈ RX, coordinate (occurrenceValue s i) by
        simp [rotationPlus, occurrenceCoordinates]]
      exact hRXsum
    have hreflectionSum : reflectionPlus.sum - reflectionMinus.sum =
        ∑ e ∈ E, occurrenceValue edges e := by
      rw [show reflectionPlus.sum =
          ∑ i ∈ P, coordinate (occurrenceValue s i) by
        simp [reflectionPlus, occurrenceCoordinates]]
      rw [show reflectionMinus.sum =
          ∑ i ∈ N, coordinate (occurrenceValue s i) by
        simp [reflectionMinus, occurrenceCoordinates]]
      simpa [P, N, edges] using sum_reflectionBoundary_eq_edgeSum s E
    have hsigned : rotationPlus.sum - ([] : List A).sum +
        reflectionPlus.sum - reflectionMinus.sum = 0 := by
      rw [List.sum_nil, sub_zero, hrotationSum]
      calc
        (∑ x ∈ X, occurrenceValue rotations x) +
            reflectionPlus.sum - reflectionMinus.sum =
          (reflectionPlus.sum - reflectionMinus.sum) +
            ∑ x ∈ X, occurrenceValue rotations x := by abel
        _ = (∑ e ∈ E, occurrenceValue edges e) +
            ∑ x ∈ X, occurrenceValue rotations x := by rw [hreflectionSum]
        _ = 0 := hsumSplit
    have hassignment : BalancedSignedAssignment (selectedMultiset s J) := {
      rotationPlus := rotationPlus
      rotationMinus := []
      reflectionPlus := reflectionPlus
      reflectionMinus := reflectionMinus
      reflectionLengthEq := by
        simp only [reflectionPlus, reflectionMinus, occurrenceCoordinates,
          List.length_map, Finset.length_toList]
        exact hPcardN
      reflectionPlusNonempty := by
        intro hempty
        have hzero : P.card = 0 := by
          have := congrArg List.length hempty
          simpa [reflectionPlus, occurrenceCoordinates] using this
        exact (Finset.card_pos.mpr hPne).ne' hzero
      carrier_eq := hcarrier
      signedSum_eq_zero := hsigned
    }
    exact ⟨J, hJne,
      isProductOneSelection_of_balancedSignedAssignment s J hassignment⟩

/-- GJM's small-Davenport upper bound, in the exact occurrence-labelled
interface consumed by the 13-page Gao proof. -/
theorem smallDavenportProductOneFreeAtMost_of_ordinaryDavenport
    (D : ℕ) (hD : IsOrdinaryDavenportConstant A D) :
    SmallDavenportProductOneFreeAtMost (Group A) D := by
  intro s R hfree
  by_contra hle
  have hlarge : D + 1 ≤ R.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hlarge
  let t : List (Group A) := occurrenceSubsequence s T
  have htlen : t.length = D + 1 := by
    simp [t, occurrenceSubsequence, hTcard]
  obtain ⟨J, hJne, hJprod⟩ :=
    exists_nonempty_productOne_of_davenport_add_one t D hD.1 htlen
  let I := liftOccurrenceSubsequenceSelection s T J
  have hIsub : I ⊆ R :=
    (liftOccurrenceSubsequenceSelection_subset s T J).trans hTsub
  have hIne : I.Nonempty := by
    have hcard := card_liftOccurrenceSubsequenceSelection s T J
    exact Finset.card_pos.mp (by
      rw [hcard]
      exact Finset.card_pos.mpr hJne)
  have hIprod : IsProductOneSelection s I :=
    isProductOneSelection_liftOccurrenceSubsequence s T J hJprod
  exact hfree I hIsub hIne hIprod

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.exists_nonempty_productOne_of_davenport_add_one
#print axioms GaoLean.ConcreteGDihedral.smallDavenportProductOneFreeAtMost_of_ordinaryDavenport
