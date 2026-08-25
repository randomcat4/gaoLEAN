import GaoFormal.Matching.AffineFailure

/-!
# Labelled exchange-reservoir selection bookkeeping

This module proves the endpoint and filler mechanics used in Corollary 2.1
and the reverse direction of the affine-failure certificate.  It works only
with source labels: equal values do not affect disjointness or cardinality.
-/

namespace GaoFormal

namespace OccurrenceReservoir

variable {F V Ω : Type*} [Field F] [AddCommGroup V] [Module F V]
variable [Fintype Ω] [DecidableEq Ω] {C : Ω → V} {k t : ℕ}

def leftEndpoints (R : OccurrenceReservoir (F := F) C k t) : Finset Ω :=
  Finset.univ.image R.left

def rightEndpoints (R : OccurrenceReservoir (F := F) C k t) : Finset Ω :=
  Finset.univ.image R.right

def endpoints (R : OccurrenceReservoir (F := F) C k t) : Finset Ω :=
  leftEndpoints R ∪ rightEndpoints R

omit [DecidableEq Ω] in theorem left_injective
    (R : OccurrenceReservoir (F := F) C k t) :
    Function.Injective R.left := by
  intro a b hab
  exact Sum.inl.inj (R.endpoint_injective hab)

omit [DecidableEq Ω] in theorem right_injective
    (R : OccurrenceReservoir (F := F) C k t) :
    Function.Injective R.right := by
  intro a b hab
  exact Sum.inr.inj (R.endpoint_injective hab)

theorem card_leftEndpoints (R : OccurrenceReservoir (F := F) C k t) :
    (leftEndpoints R).card = k * t := by
  classical
  rw [leftEndpoints, Finset.card_image_iff.mpr (left_injective R).injOn]
  simp

theorem card_rightEndpoints (R : OccurrenceReservoir (F := F) C k t) :
    (rightEndpoints R).card = k * t := by
  classical
  rw [rightEndpoints, Finset.card_image_iff.mpr (right_injective R).injOn]
  simp

theorem disjoint_leftEndpoints_rightEndpoints
    (R : OccurrenceReservoir (F := F) C k t) :
    Disjoint (leftEndpoints R) (rightEndpoints R) := by
  classical
  rw [Finset.disjoint_left]
  rintro x hxL hxR
  rcases Finset.mem_image.mp hxL with ⟨p, _hp, rfl⟩
  rcases Finset.mem_image.mp hxR with ⟨q, _hq, heq⟩
  have htag : Sum.inl p = Sum.inr q :=
    R.endpoint_injective heq.symm
  exact Sum.inl_ne_inr htag

theorem card_endpoints (R : OccurrenceReservoir (F := F) C k t) :
    (endpoints R).card = 2 * (k * t) := by
  rw [endpoints,
    Finset.card_union_of_disjoint (disjoint_leftEndpoints_rightEndpoints R),
    card_leftEndpoints R, card_rightEndpoints R]
  omega

/-- Select the right endpoint on toggled pairs and the left endpoint on every
other pair. -/
def toggledSelection (R : OccurrenceReservoir (F := F) C k t)
    (T : Finset (Fin k × Fin t)) : Finset Ω :=
  (leftEndpoints R \ T.image R.left) ∪ T.image R.right

theorem toggledSelection_subset_endpoints
    (R : OccurrenceReservoir (F := F) C k t)
    (T : Finset (Fin k × Fin t)) :
    toggledSelection R T ⊆ endpoints R := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
  · exact Finset.mem_union_right _
      (Finset.mem_image.mpr (by
        rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
        exact ⟨p, Finset.mem_univ p, rfl⟩))

theorem card_toggledSelection
    (R : OccurrenceReservoir (F := F) C k t)
    (T : Finset (Fin k × Fin t)) :
    (toggledSelection R T).card = k * t := by
  classical
  have hTL : T.image R.left ⊆ leftEndpoints R := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  have hTR : T.image R.right ⊆ rightEndpoints R := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  have hdis : Disjoint (leftEndpoints R \ T.image R.left)
      (T.image R.right) :=
    (disjoint_leftEndpoints_rightEndpoints R).mono
      Finset.sdiff_subset hTR
  have hTleft : (T.image R.left).card = T.card :=
    Finset.card_image_iff.mpr (left_injective R).injOn
  have hTright : (T.image R.right).card = T.card :=
    Finset.card_image_iff.mpr (right_injective R).injOn
  have hTle : T.card ≤ k * t := by
    have := Finset.card_le_card (Finset.subset_univ T)
    simpa using this
  rw [toggledSelection, Finset.card_union_of_disjoint hdis,
    Finset.card_sdiff_of_subset hTL, card_leftEndpoints R,
    hTleft, hTright]
  omega

/-- Toggling replaces the selected left endpoint by the right endpoint on
exactly the labelled pairs in `T`. -/
theorem sum_toggledSelection
    (R : OccurrenceReservoir (F := F) C k t)
    (T : Finset (Fin k × Fin t)) :
    (∑ ω ∈ toggledSelection R T, C ω) =
      (∑ p : Fin k × Fin t, C (R.left p)) +
        ∑ p ∈ T, (C (R.right p) - C (R.left p)) := by
  classical
  have hTL : T.image R.left ⊆ leftEndpoints R := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  have hTR : T.image R.right ⊆ rightEndpoints R := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨p, hp, rfl⟩
    exact Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩
  have hdis : Disjoint (leftEndpoints R \ T.image R.left)
      (T.image R.right) :=
    (disjoint_leftEndpoints_rightEndpoints R).mono
      Finset.sdiff_subset hTR
  have hleft :
      (∑ ω ∈ leftEndpoints R, C ω) =
        ∑ p : Fin k × Fin t, C (R.left p) := by
    rw [leftEndpoints, Finset.sum_image]
    exact fun a _ha b _hb hab => left_injective R hab
  have htoggleLeft :
      (∑ ω ∈ T.image R.left, C ω) = ∑ p ∈ T, C (R.left p) := by
    rw [Finset.sum_image]
    exact fun a _ha b _hb hab => left_injective R hab
  have htoggleRight :
      (∑ ω ∈ T.image R.right, C ω) = ∑ p ∈ T, C (R.right p) := by
    rw [Finset.sum_image]
    exact fun a _ha b _hb hab => right_injective R hab
  have hsplit := Finset.sum_sdiff (f := C) hTL
  rw [htoggleLeft, hleft] at hsplit
  have hdiff := eq_sub_of_add_eq hsplit
  rw [toggledSelection, Finset.sum_union hdis, htoggleRight]
  rw [Finset.sum_sub_distrib]
  rw [hdiff]
  abel

theorem sum_toggledSelection_eq_directions
    (R : OccurrenceReservoir (F := F) C k t)
    (T : Finset (Fin k × Fin t)) :
    (∑ ω ∈ toggledSelection R T, C ω) =
      (∑ p : Fin k × Fin t, C (R.left p)) +
        ∑ p ∈ T, R.direction p.1 := by
  rw [sum_toggledSelection R T]
  apply congrArg ((∑ p : Fin k × Fin t, C (R.left p)) + ·)
  apply Finset.sum_congr rfl
  intro p hp
  exact R.difference_eq p.1 p.2

/-- Under the exact source-length surplus `d+k*t ≤ |Ω|`, every toggled
baseline can be padded outside all reservoir endpoints to cardinality `d`. -/
theorem exists_disjoint_fillers
    (R : OccurrenceReservoir (F := F) C k t)
    (T : Finset (Fin k × Fin t)) (d : ℕ)
    (hbase : k * t ≤ d) (hcapacity : d + k * t ≤ Fintype.card Ω) :
    ∃ fillers : Finset Ω,
      fillers ⊆ Finset.univ \ endpoints R ∧
      fillers.card = d - k * t ∧
      Disjoint (toggledSelection R T) fillers ∧
      (toggledSelection R T ∪ fillers).card = d := by
  classical
  have hcompCard : (Finset.univ \ endpoints R).card =
      Fintype.card Ω - 2 * (k * t) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _),
      card_endpoints R]
    simp
  have hneed : d - k * t ≤ (Finset.univ \ endpoints R).card := by
    rw [hcompCard]
    omega
  obtain ⟨fillers, hfillSub, hfillCard⟩ :=
    Finset.exists_subset_card_eq hneed
  have hdis : Disjoint (toggledSelection R T) fillers := by
    rw [Finset.disjoint_left]
    intro x hxT hxF
    have hxEndpoint := toggledSelection_subset_endpoints R T hxT
    have hxComp := Finset.mem_sdiff.mp (hfillSub hxF)
    exact hxComp.2 hxEndpoint
  refine ⟨fillers, hfillSub, hfillCard, hdis, ?_⟩
  rw [Finset.card_union_of_disjoint hdis, card_toggledSelection R T,
    hfillCard]
  omega

end OccurrenceReservoir

end GaoFormal

#print axioms GaoFormal.OccurrenceReservoir.card_endpoints
#print axioms GaoFormal.OccurrenceReservoir.card_toggledSelection
#print axioms GaoFormal.OccurrenceReservoir.sum_toggledSelection
#print axioms GaoFormal.OccurrenceReservoir.sum_toggledSelection_eq_directions
#print axioms GaoFormal.OccurrenceReservoir.exists_disjoint_fillers
