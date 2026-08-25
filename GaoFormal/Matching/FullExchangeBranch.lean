import GaoFormal.Matching.VariableDirectionCoverage

/-!
# The large-exceptional-set full-exchange branch

This file assembles the remaining branch of the affine exchange argument.
Besides the independent kernel reservoir, it uses `q - 1` disjoint cross
pairs whose quotient increments are merely nonzero (and may repeat).  The
labelled Cauchy--Davenport theorem chooses the cross toggles, the kernel
reservoir corrects the remaining error, and fillers are kept outside every
endpoint.
-/

namespace GaoFormal

open scoped BigOperators

variable {q : ℕ} [NeZero q] [Fact q.Prime]
variable {Ω V Q : Type*} [Fintype Ω] [DecidableEq Ω]
variable [AddCommGroup V] [Module (ZMod q) V]
variable [AddCommGroup Q] [Module (ZMod q) Q]
variable {C : Ω → V} {k : ℕ}

/-- `q - 1` occurrence-disjoint cross pairs.  Their left endpoints lie in
the distinguished quotient fibre and their right endpoints lie outside it.
No independence or equality of the quotient increments is assumed. -/
structure QuotientCrossPairReservoir
    (C : Ω → V) (φ : V →ₗ[ZMod q] Q) (β : Q) where
  left : Fin (q - 1) → Ω
  right : Fin (q - 1) → Ω
  endpoint_injective : Function.Injective (Sum.elim left right)
  left_fibre : ∀ j, φ (C (left j)) = β
  right_exceptional : ∀ j, φ (C (right j)) ≠ β

namespace QuotientCrossPairReservoir

variable {φ : V →ₗ[ZMod q] Q} {β : Q}

def leftEndpoints (P : QuotientCrossPairReservoir C φ β) : Finset Ω :=
  Finset.univ.image P.left

def rightEndpoints (P : QuotientCrossPairReservoir C φ β) : Finset Ω :=
  Finset.univ.image P.right

def endpoints (P : QuotientCrossPairReservoir C φ β) : Finset Ω :=
  leftEndpoints P ∪ rightEndpoints P

omit [DecidableEq Ω] in theorem left_injective
    (P : QuotientCrossPairReservoir C φ β) : Function.Injective P.left := by
  intro a b hab
  exact Sum.inl.inj (P.endpoint_injective hab)

omit [DecidableEq Ω] in theorem right_injective
    (P : QuotientCrossPairReservoir C φ β) : Function.Injective P.right := by
  intro a b hab
  exact Sum.inr.inj (P.endpoint_injective hab)

theorem disjoint_leftEndpoints_rightEndpoints
    (P : QuotientCrossPairReservoir C φ β) :
    Disjoint (leftEndpoints P) (rightEndpoints P) := by
  classical
  rw [Finset.disjoint_left]
  rintro x hxL hxR
  rcases Finset.mem_image.mp hxL with ⟨i, _hi, rfl⟩
  rcases Finset.mem_image.mp hxR with ⟨j, _hj, h⟩
  exact P.right_exceptional j (h ▸ P.left_fibre i)

theorem card_endpoints (P : QuotientCrossPairReservoir C φ β) :
    (endpoints P).card = 2 * (q - 1) := by
  classical
  rw [endpoints,
    Finset.card_union_of_disjoint (disjoint_leftEndpoints_rightEndpoints P),
    leftEndpoints, rightEndpoints,
    Finset.card_image_iff.mpr (left_injective P).injOn,
    Finset.card_image_iff.mpr (right_injective P).injOn]
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- Select the right endpoint on the labelled cross pairs in `T` and the
left endpoint on all other cross pairs. -/
def toggledSelection (P : QuotientCrossPairReservoir C φ β)
    (T : Finset (Fin (q - 1))) : Finset Ω :=
  (leftEndpoints P \ T.image P.left) ∪ T.image P.right

theorem toggledSelection_subset_endpoints
    (P : QuotientCrossPairReservoir C φ β)
    (T : Finset (Fin (q - 1))) :
    toggledSelection P T ⊆ endpoints P := by
  intro x hx
  rcases Finset.mem_union.mp hx with hx | hx
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp hx).1
  · exact Finset.mem_union_right _
      (Finset.mem_image.mpr (by
        rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
        exact ⟨i, Finset.mem_univ i, rfl⟩))

theorem card_toggledSelection
    (P : QuotientCrossPairReservoir C φ β)
    (T : Finset (Fin (q - 1))) :
    (toggledSelection P T).card = q - 1 := by
  classical
  have hTL : T.image P.left ⊆ leftEndpoints P := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hTR : T.image P.right ⊆ rightEndpoints P := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hdis : Disjoint (leftEndpoints P \ T.image P.left)
      (T.image P.right) :=
    (disjoint_leftEndpoints_rightEndpoints P).mono Finset.sdiff_subset hTR
  have hTleft : (T.image P.left).card = T.card :=
    Finset.card_image_iff.mpr (left_injective P).injOn
  have hTright : (T.image P.right).card = T.card :=
    Finset.card_image_iff.mpr (right_injective P).injOn
  rw [toggledSelection, Finset.card_union_of_disjoint hdis,
    Finset.card_sdiff_of_subset hTL, leftEndpoints,
    Finset.card_image_iff.mpr (left_injective P).injOn,
    hTleft, hTright]
  have hTle := Finset.card_le_card (Finset.subset_univ T)
  simp only [Finset.card_univ, Fintype.card_fin] at hTle ⊢
  omega

theorem sum_toggledSelection
    (P : QuotientCrossPairReservoir C φ β)
    (T : Finset (Fin (q - 1))) :
    (∑ ω ∈ toggledSelection P T, C ω) =
      (∑ j : Fin (q - 1), C (P.left j)) +
        ∑ j ∈ T, (C (P.right j) - C (P.left j)) := by
  classical
  have hTL : T.image P.left ⊆ leftEndpoints P := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hTR : T.image P.right ⊆ rightEndpoints P := by
    intro x hx
    rcases Finset.mem_image.mp hx with ⟨i, hi, rfl⟩
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hdis : Disjoint (leftEndpoints P \ T.image P.left)
      (T.image P.right) :=
    (disjoint_leftEndpoints_rightEndpoints P).mono Finset.sdiff_subset hTR
  have hleft : (∑ ω ∈ leftEndpoints P, C ω) =
      ∑ j : Fin (q - 1), C (P.left j) := by
    rw [leftEndpoints, Finset.sum_image]
    exact fun a _ha b _hb hab => left_injective P hab
  have htoggleLeft : (∑ ω ∈ T.image P.left, C ω) =
      ∑ j ∈ T, C (P.left j) := by
    rw [Finset.sum_image]
    exact fun a _ha b _hb hab => left_injective P hab
  have htoggleRight : (∑ ω ∈ T.image P.right, C ω) =
      ∑ j ∈ T, C (P.right j) := by
    rw [Finset.sum_image]
    exact fun a _ha b _hb hab => right_injective P hab
  have hsplit := Finset.sum_sdiff (f := C) hTL
  rw [htoggleLeft, hleft] at hsplit
  have hdiff := eq_sub_of_add_eq hsplit
  rw [toggledSelection, Finset.sum_union hdis, htoggleRight,
    Finset.sum_sub_distrib, hdiff]
  abel

/-- The quotient image of a cross selection is its all-left baseline plus
the labelled sum of the selected nonzero increments. -/
theorem map_sum_toggledSelection
    (P : QuotientCrossPairReservoir C φ β)
    (T : Finset (Fin (q - 1))) :
    φ (∑ ω ∈ toggledSelection P T, C ω) =
      (q - 1) • β +
        ∑ j ∈ T, (φ (C (P.right j)) - β) := by
  rw [sum_toggledSelection, map_add, map_sum]
  have hleft : (∑ j : Fin (q - 1), φ (C (P.left j))) = (q - 1) • β := by
    simp_rw [P.left_fibre]
    simp
  rw [hleft]
  congr 1
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j hj
  rw [map_sub, P.left_fibre]

end QuotientCrossPairReservoir

namespace OccurrenceReservoir

open QuotientCrossPairReservoir

/-- Choose `q - 1` heavy occurrences and `q - 1` exceptional occurrences
as disjoint cross pairs.  The heavy value is required to be unused by the
kernel reservoir at the value level; the exceptional classification then
separates every other possible endpoint collision. -/
theorem exists_disjoint_quotientCrossPairReservoir
    (R : OccurrenceReservoir (F := ZMod q) C k (q - 1))
    (φ : V →ₗ[ZMod q] Q) (β : Q) (E : Finset Ω)
    (hExceptional : ∀ ω, ω ∈ E ↔ φ (C ω) ≠ β)
    (hEndpoint : ∀ ω ∈ OccurrenceReservoir.endpoints R, φ (C ω) = β)
    (x : V) (hxHeavy : x ∈ thresholdSupport C (q - 1))
    (hxFibre : φ x = β)
    (hxUnused : ∀ ω ∈ OccurrenceReservoir.endpoints R, C ω ≠ x)
    (hEcard : q - 1 ≤ E.card) :
    ∃ P : QuotientCrossPairReservoir C φ β,
      Disjoint (OccurrenceReservoir.endpoints R) P.endpoints := by
  classical
  let hxCount : q - 1 ≤ Fintype.card {ω : Ω // C ω = x} :=
    thresholdSupport_card_fiber C (q - 1) hxHeavy
  let L : Fin (q - 1) → Ω := chooseCopies C (q - 1) x hxCount
  have hLvalue : ∀ j, C (L j) = x := by
    intro j
    exact chooseCopies_value C (q - 1) x hxCount j
  have hLinjective : Function.Injective L :=
    chooseCopies_injective C (q - 1) x hxCount
  have hEcount : q - 1 ≤ Fintype.card {ω : Ω // ω ∈ E} := by
    simpa using hEcard
  let X : Fin (q - 1) → Ω := fun j ↦
    ((Fintype.equivFin {ω : Ω // ω ∈ E}).symm (Fin.castLE hEcount j)).1
  have hXmem : ∀ j, X j ∈ E := by
    intro j
    exact ((Fintype.equivFin {ω : Ω // ω ∈ E}).symm
      (Fin.castLE hEcount j)).2
  have hXinjective : Function.Injective X := by
    intro a b hab
    have hsub :
        (Fintype.equivFin {ω : Ω // ω ∈ E}).symm (Fin.castLE hEcount a) =
          (Fintype.equivFin {ω : Ω // ω ∈ E}).symm (Fin.castLE hEcount b) := by
      apply Subtype.ext
      exact hab
    have hfin := (Fintype.equivFin {ω : Ω // ω ∈ E}).symm.injective hsub
    exact Fin.castLE_injective hEcount hfin
  have hLX : ∀ i j, L i ≠ X j := by
    intro i j hij
    have hright : φ (C (X j)) ≠ β := (hExceptional (X j)).mp (hXmem j)
    apply hright
    rw [← hij, hLvalue, hxFibre]
  let P : QuotientCrossPairReservoir C φ β :=
    { left := L
      right := X
      endpoint_injective := by
        apply hLinjective.sumElim hXinjective
        intro i j hij
        exact hLX i j hij
      left_fibre := by
        intro j
        rw [hLvalue, hxFibre]
      right_exceptional := by
        intro j
        exact (hExceptional (X j)).mp (hXmem j) }
  refine ⟨P, ?_⟩
  rw [Finset.disjoint_left]
  intro ω hωR hωP
  rcases Finset.mem_union.mp hωP with hωL | hωX
  · rcases Finset.mem_image.mp hωL with ⟨j, _hj, hω⟩
    change L j = ω at hω
    apply hxUnused ω hωR
    rw [← hω, hLvalue]
  · rcases Finset.mem_image.mp hωX with ⟨j, _hj, hω⟩
    change X j = ω at hω
    apply (hExceptional (X j)).mp (hXmem j)
    rw [hω]
    exact hEndpoint ω hωR

/-- Under the strict half-cardinality inequality, construct the full kernel
reservoir together with a heavy support value not used by any of its endpoint
values.  This is the strengthened form of the M42 reservoir construction
needed to reserve `q - 1` fresh copies for the cross pairs. -/
theorem exists_kernel_reservoir_with_unusedHeavyValue
    [FiniteDimensional (ZMod q) V]
    (C : Ω → V) (φ : V →ₗ[ZMod q] Q) (β : Q)
    (hvectorSpan :
      vectorSpan (ZMod q)
        ((thresholdSupport C (q - 1) : Finset V) : Set V) = LinearMap.ker φ)
    (hstrict : Module.finrank (ZMod q) (LinearMap.ker φ) <
      (thresholdSupport C (q - 1)).card / 2)
    (hfibre : ∀ x ∈ thresholdSupport C (q - 1), φ x = β)
    (htwo : (2 : ZMod q) ≠ 0) :
    ∃ R : OccurrenceReservoir (F := ZMod q) C
        (Module.finrank (ZMod q) (LinearMap.ker φ)) (q - 1),
      ∃ x ∈ thresholdSupport C (q - 1),
        Submodule.span (ZMod q) (Set.range R.direction) = LinearMap.ker φ ∧
        (∀ ω ∈ OccurrenceReservoir.endpoints R, φ (C ω) = β) ∧
        ∀ ω ∈ OccurrenceReservoir.endpoints R, C ω ≠ x := by
  classical
  have hmatch := IndependentDifferenceMatching.exists_maximum_matching_at_formula
    (F := ZMod q) (A := thresholdSupport C (q - 1)) htwo
  rw [hvectorSpan, min_eq_left (Nat.le_of_lt hstrict)] at hmatch
  rcases hmatch with ⟨M, hmax⟩
  rcases IndependentDifferenceMatching.exists_two_unused_of_card_lt_half M (by simpa using hstrict) with
    ⟨x, hxHeavy, hxUnused, _x', _hx'Heavy, _hx'Unused, _hxx'⟩
  let R := M.toOccurrenceReservoir C (q - 1)
  have hleftValue : ∀ p, C (R.left p) = M.left p.1 := by
    intro p
    exact M.toOccurrenceReservoir_left_value C (q - 1) p.1 p.2
  have hrightValue : ∀ p, C (R.right p) = M.right p.1 := by
    intro p
    exact M.toOccurrenceReservoir_right_value C (q - 1) p.1 p.2
  have hleftFibre : ∀ p, φ (C (R.left p)) = β := by
    intro p
    rw [hleftValue p]
    exact hfibre (M.left p.1) (M.left_mem p.1)
  have hrightFibre : ∀ p, φ (C (R.right p)) = β := by
    intro p
    rw [hrightValue p]
    exact hfibre (M.right p.1) (M.right_mem p.1)
  have hqpos : 0 < q - 1 := by
    have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    omega
  let j : Fin (q - 1) := ⟨0, hqpos⟩
  have hspanle :
      Submodule.span (ZMod q) (Set.range R.direction) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change φ (R.direction i) = 0
    rw [← R.difference_eq i j, map_sub, hrightFibre (i, j),
      hleftFibre (i, j), sub_self]
  have hfinrank :
      Module.finrank (ZMod q)
          (Submodule.span (ZMod q) (Set.range R.direction)) =
        Module.finrank (ZMod q) (LinearMap.ker φ) := by
    rw [finrank_span_eq_card R.independent]
    simp
  have hspanExact :
      Submodule.span (ZMod q) (Set.range R.direction) = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_eq hspanle hfinrank
  have hEndpoint : ∀ ω ∈ OccurrenceReservoir.endpoints R, φ (C ω) = β := by
    intro ω hω
    rcases Finset.mem_union.mp hω with hω | hω
    · rcases Finset.mem_image.mp hω with ⟨p, _hp, rfl⟩
      exact hleftFibre p
    · rcases Finset.mem_image.mp hω with ⟨p, _hp, rfl⟩
      exact hrightFibre p
  have hUnusedEndpoints :
      ∀ ω ∈ OccurrenceReservoir.endpoints R, C ω ≠ x := by
    intro ω hω
    rcases Finset.mem_union.mp hω with hω | hω
    · rcases Finset.mem_image.mp hω with ⟨p, _hp, rfl⟩
      rw [hleftValue p]
      exact (hxUnused (Sum.inl p.1)).symm
    · rcases Finset.mem_image.mp hω with ⟨p, _hp, rfl⟩
      rw [hrightValue p]
      exact (hxUnused (Sum.inr p.1)).symm
  exact ⟨R, x, hxHeavy, hspanExact, hEndpoint, hUnusedEndpoints⟩

/-- Combine the independent kernel toggles, `q - 1` variable quotient
toggles, and outside-endpoint fillers.  This is the occurrence-level core of
the large-exceptional-set branch. -/
theorem exists_fixedCardinality_sum_of_kernel_and_crossPairs
    (R : OccurrenceReservoir (F := ZMod q) C k (q - 1))
    (φ : V →ₗ[ZMod q] Q) (β : Q)
    (ψ : Q ≃ₗ[ZMod q] ZMod q)
    (hspan : Submodule.span (ZMod q) (Set.range R.direction) = LinearMap.ker φ)
    (P : QuotientCrossPairReservoir C φ β)
    (hdisjoint : Disjoint (OccurrenceReservoir.endpoints R) P.endpoints)
    (d : ℕ)
    (hbase : (k + 1) * (q - 1) ≤ d)
    (hcapacity : d + (k + 1) * (q - 1) ≤ Fintype.card Ω)
    (y : V) :
    ∃ I : Finset Ω, I.card = d ∧ (∑ ω ∈ I, C ω) = y := by
  classical
  let forbidden := OccurrenceReservoir.endpoints R ∪ P.endpoints
  have hforbiddenCard : forbidden.card = 2 * ((k + 1) * (q - 1)) := by
    dsimp only [forbidden]
    rw [Finset.card_union_of_disjoint hdisjoint,
      OccurrenceReservoir.card_endpoints R, P.card_endpoints]
    ring
  have hcompCard : ((Finset.univ : Finset Ω) \ forbidden).card =
      Fintype.card Ω - 2 * ((k + 1) * (q - 1)) := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), hforbiddenCard]
    simp
  have hneed : d - (k + 1) * (q - 1) ≤
      ((Finset.univ : Finset Ω) \ forbidden).card := by
    rw [hcompCard]
    omega
  obtain ⟨fillers, hfillSub, hfillCard⟩ :=
    Finset.exists_subset_card_eq hneed
  let kernelBaseline : V :=
    ∑ p : Fin k × Fin (q - 1), C (R.left p)
  let crossBaseline : V :=
    ∑ j : Fin (q - 1), C (P.left j)
  let fillerSum : V := ∑ ω ∈ fillers, C ω
  let inc : Fin (q - 1) → ZMod q :=
    fun j ↦ ψ (φ (C (P.right j)) - β)
  have hinc : ∀ j, inc j ≠ 0 := by
    intro j hj
    apply P.right_exceptional j
    rw [← sub_eq_zero]
    apply ψ.injective
    simpa [inc] using hj
  let quotientTarget : ZMod q :=
    ψ (φ y - φ kernelBaseline - φ crossBaseline - φ fillerSum)
  obtain ⟨T, hT⟩ :=
    exists_labelled_subset_sum_eq_of_nonzero inc hinc quotientTarget
  let crossSelection := P.toggledSelection T
  have hmapCrossBaseline : φ crossBaseline = (q - 1) • β := by
    dsimp only [crossBaseline]
    rw [map_sum]
    simp_rw [P.left_fibre]
    simp
  have hpsiCross :
      ψ (φ (∑ ω ∈ crossSelection, C ω) - φ crossBaseline) =
        ψ (φ y - φ kernelBaseline - φ crossBaseline - φ fillerSum) := by
    calc
      ψ (φ (∑ ω ∈ crossSelection, C ω) - φ crossBaseline) =
          ∑ j ∈ T, inc j := by
        dsimp only [crossSelection]
        rw [P.map_sum_toggledSelection T, hmapCrossBaseline,
          add_sub_cancel_left, map_sum]
      _ = quotientTarget := hT
      _ = ψ (φ y - φ kernelBaseline - φ crossBaseline - φ fillerSum) := rfl
  have hcrossDelta :
      φ (∑ ω ∈ crossSelection, C ω) - φ crossBaseline =
        φ y - φ kernelBaseline - φ crossBaseline - φ fillerSum :=
    ψ.injective hpsiCross
  let z : V :=
    y - kernelBaseline - (∑ ω ∈ crossSelection, C ω) - fillerSum
  have hzKer : z ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    dsimp only [z]
    rw [map_sub, map_sub, map_sub]
    rw [show φ (∑ ω ∈ crossSelection, C ω) =
        (φ (∑ ω ∈ crossSelection, C ω) - φ crossBaseline) +
          φ crossBaseline by abel,
      hcrossDelta]
    abel
  have hzSpan : z ∈ Submodule.span (ZMod q) (Set.range R.direction) := by
    rw [hspan]
    exact hzKer
  rcases (Submodule.mem_span_range_iff_exists_fun (ZMod q)).1 hzSpan with
    ⟨a, ha⟩
  obtain ⟨K, hK⟩ := exists_directionToggleSet_sum_eq R.direction a
  let kernelSelection := OccurrenceReservoir.toggledSelection R K
  have hkernelSum :
      (∑ ω ∈ kernelSelection, C ω) = kernelBaseline + z := by
    dsimp only [kernelSelection]
    rw [OccurrenceReservoir.sum_toggledSelection_eq_directions R K, hK, ha]
  have hkernelCross : Disjoint kernelSelection crossSelection := by
    exact hdisjoint.mono
      (OccurrenceReservoir.toggledSelection_subset_endpoints R K)
      (P.toggledSelection_subset_endpoints T)
  have hfillKernelEndpoints :
      Disjoint (OccurrenceReservoir.endpoints R) fillers := by
    rw [Finset.disjoint_left]
    intro ω hωR hωF
    have hcomp := Finset.mem_sdiff.mp (hfillSub hωF)
    exact hcomp.2 (Finset.mem_union_left P.endpoints hωR)
  have hfillCrossEndpoints : Disjoint P.endpoints fillers := by
    rw [Finset.disjoint_left]
    intro ω hωP hωF
    have hcomp := Finset.mem_sdiff.mp (hfillSub hωF)
    exact hcomp.2 (Finset.mem_union_right (OccurrenceReservoir.endpoints R) hωP)
  have hkernelFillers : Disjoint kernelSelection fillers :=
    hfillKernelEndpoints.mono_left
      (OccurrenceReservoir.toggledSelection_subset_endpoints R K)
  have hcrossFillers : Disjoint crossSelection fillers :=
    hfillCrossEndpoints.mono_left (P.toggledSelection_subset_endpoints T)
  have hkernelRest : Disjoint kernelSelection (crossSelection ∪ fillers) :=
    Finset.disjoint_union_right.mpr ⟨hkernelCross, hkernelFillers⟩
  refine ⟨kernelSelection ∪ (crossSelection ∪ fillers), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hkernelRest,
      Finset.card_union_of_disjoint hcrossFillers,
      OccurrenceReservoir.card_toggledSelection R K,
      P.card_toggledSelection T, hfillCard]
    rw [← Nat.add_assoc,
      show k * (q - 1) + (q - 1) = (k + 1) * (q - 1) by ring]
    omega
  · rw [Finset.sum_union hkernelRest, Finset.sum_union hcrossFillers,
      hkernelSum]
    change kernelBaseline + z +
      ((∑ ω ∈ crossSelection, C ω) + fillerSum) = y
    dsimp only [z]
    abel

/-- Source-shaped large-exceptional-set branch.  The kernel reservoir, unused
heavy value, cross pairs, quotient toggles, kernel correction, and fillers are
all constructed internally. -/
theorem exists_fixedCardinality_sum_of_largeExceptionalSet
    [FiniteDimensional (ZMod q) V]
    (C : Ω → V) (φ : V →ₗ[ZMod q] Q) (β : Q)
    (ψ : Q ≃ₗ[ZMod q] ZMod q) (E : Finset Ω)
    (hvectorSpan :
      vectorSpan (ZMod q)
        ((thresholdSupport C (q - 1) : Finset V) : Set V) = LinearMap.ker φ)
    (hstrict : Module.finrank (ZMod q) (LinearMap.ker φ) <
      (thresholdSupport C (q - 1)).card / 2)
    (hfibre : ∀ x ∈ thresholdSupport C (q - 1), φ x = β)
    (htwo : (2 : ZMod q) ≠ 0)
    (hExceptional : ∀ ω, ω ∈ E ↔ φ (C ω) ≠ β)
    (hEcard : q - 1 ≤ E.card)
    (d : ℕ)
    (hbase : (Module.finrank (ZMod q) (LinearMap.ker φ) + 1) * (q - 1) ≤ d)
    (hcapacity : d +
      (Module.finrank (ZMod q) (LinearMap.ker φ) + 1) * (q - 1) ≤
        Fintype.card Ω)
    (y : V) :
    ∃ I : Finset Ω, I.card = d ∧ (∑ ω ∈ I, C ω) = y := by
  rcases exists_kernel_reservoir_with_unusedHeavyValue C φ β hvectorSpan
      hstrict hfibre htwo with
    ⟨R, x, hxHeavy, hspan, hEndpoint, hxUnused⟩
  have hxFibre : φ x = β := hfibre x hxHeavy
  rcases exists_disjoint_quotientCrossPairReservoir R φ β E hExceptional
      hEndpoint x hxHeavy hxFibre hxUnused hEcard with ⟨P, hdisjoint⟩
  exact exists_fixedCardinality_sum_of_kernel_and_crossPairs R φ β ψ hspan
    P hdisjoint d hbase hcapacity y

end OccurrenceReservoir

end GaoFormal

#print axioms GaoFormal.OccurrenceReservoir.exists_fixedCardinality_sum_of_kernel_and_crossPairs
#print axioms GaoFormal.OccurrenceReservoir.exists_disjoint_quotientCrossPairReservoir
#print axioms GaoFormal.OccurrenceReservoir.exists_kernel_reservoir_with_unusedHeavyValue
#print axioms GaoFormal.OccurrenceReservoir.exists_fixedCardinality_sum_of_largeExceptionalSet
