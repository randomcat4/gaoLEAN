import GaoFormal.Matching.ExchangeSelection

/-!
# Finite-field coefficient coverage by repeated direction toggles

This is the elementary `q-1`-copies step behind the Cauchy--Davenport phrase
in the frozen exchange proof.  For each `ZMod q` coefficient, its canonical
representative chooses that many of the `q-1` labelled copies.
-/

namespace GaoFormal

open scoped BigOperators

variable {q : ℕ} [NeZero q] [Fact q.Prime]
variable {V : Type*} [AddCommGroup V] [Module (ZMod q) V]

theorem exists_repeatedDirection_sum_eq_smul
    (v : V) (a : ZMod q) :
    ∃ T : Finset (Fin (q - 1)), (∑ _j ∈ T, v) = a • v := by
  classical
  have haval : a.val ≤ q - 1 := by
    have := a.val_lt
    omega
  let emb : Fin a.val ↪ Fin (q - 1) :=
    ⟨Fin.castLE haval, Fin.castLE_injective haval⟩
  let T : Finset (Fin (q - 1)) := Finset.univ.map emb
  have hcard : T.card = a.val := by
    simp [T]
  refine ⟨T, ?_⟩
  rw [Finset.sum_const, hcard]
  rw [← Nat.cast_smul_eq_nsmul (ZMod q), a.natCast_zmod_val]

/-- Choose labelled copies independently in every direction, realizing an
arbitrary coefficient vector. -/
theorem exists_directionToggleSet_sum_eq
    {k : ℕ} (direction : Fin k → V) (a : Fin k → ZMod q) :
    ∃ T : Finset (Fin k × Fin (q - 1)),
      (∑ p ∈ T, direction p.1) = ∑ i, a i • direction i := by
  classical
  choose Ti hTi using fun i =>
    exists_repeatedDirection_sum_eq_smul (direction i) (a i)
  let T : Finset (Fin k × Fin (q - 1)) :=
    Finset.univ.biUnion fun i => (Ti i).image fun j => (i, j)
  refine ⟨T, ?_⟩
  change (∑ p ∈ Finset.univ.biUnion
      (fun i => (Ti i).image fun j => (i, j)), direction p.1) = _
  rw [Finset.sum_biUnion]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.sum_image]
    · exact hTi i
    · intro x _hx y _hy hxy
      exact congrArg Prod.snd hxy
  · intro i _hi j _hj hij
    change Disjoint ((Ti i).image fun u => (i, u))
      ((Ti j).image fun v => (j, v))
    rw [Finset.disjoint_left]
    rintro p hpI hpJ
    rcases Finset.mem_image.mp hpI with ⟨u, _hu, rfl⟩
    rcases Finset.mem_image.mp hpJ with ⟨v, _hv, hp⟩
    exact hij (congrArg Prod.fst hp.symm)

namespace OccurrenceReservoir

variable {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {C : Ω → V} {k : ℕ}

/-- A `q-1`-copy reservoir realizes every coefficient vector by an actual
labelled toggle selection. -/
theorem exists_toggledSelection_sum_eq_coefficients
    (R : OccurrenceReservoir (F := ZMod q) C k (q - 1))
    (a : Fin k → ZMod q) :
    ∃ S : Finset Ω,
      S.card = k * (q - 1) ∧
      (∑ ω ∈ S, C ω) =
        (∑ p : Fin k × Fin (q - 1), C (R.left p)) +
          ∑ i, a i • R.direction i := by
  obtain ⟨T, hT⟩ := exists_directionToggleSet_sum_eq R.direction a
  refine ⟨toggledSelection R T, card_toggledSelection R T, ?_⟩
  rw [sum_toggledSelection_eq_directions R T, hT]

/-- Full fixed-cardinality exchange completion once the reservoir directions
span the ambient space. Fillers are chosen outside every reservoir endpoint
before the coefficient toggles are selected. -/
theorem exists_fixedCardinality_sum_of_span_eq_top
    (R : OccurrenceReservoir (F := ZMod q) C k (q - 1))
    (hspan : Submodule.span (ZMod q) (Set.range R.direction) = ⊤)
    (d : ℕ) (hbase : k * (q - 1) ≤ d)
    (hcapacity : d + k * (q - 1) ≤ Fintype.card Ω)
    (y : V) :
    ∃ S : Finset Ω, S.card = d ∧ (∑ ω ∈ S, C ω) = y := by
  classical
  obtain ⟨fillers, hfillSub, hfillCard, _hdis0, _hcard0⟩ :=
    exists_disjoint_fillers R ∅ d hbase hcapacity
  let baseline : V := ∑ p : Fin k × Fin (q - 1), C (R.left p)
  let fillerSum : V := ∑ ω ∈ fillers, C ω
  have htargetMem : y - fillerSum - baseline ∈
      Submodule.span (ZMod q) (Set.range R.direction) := by
    rw [hspan]
    exact Submodule.mem_top
  rcases (Submodule.mem_span_range_iff_exists_fun (ZMod q)).1 htargetMem with
    ⟨a, ha⟩
  obtain ⟨T, hT⟩ := exists_directionToggleSet_sum_eq R.direction a
  have htoggleSum :
      (∑ ω ∈ toggledSelection R T, C ω) = y - fillerSum := by
    rw [sum_toggledSelection_eq_directions R T, hT, ha]
    simp [baseline]
  have hdis : Disjoint (toggledSelection R T) fillers := by
    rw [Finset.disjoint_left]
    intro x hxT hxF
    have hxEndpoint := toggledSelection_subset_endpoints R T hxT
    have hxComp := Finset.mem_sdiff.mp (hfillSub hxF)
    exact hxComp.2 hxEndpoint
  refine ⟨toggledSelection R T ∪ fillers, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hdis, card_toggledSelection R T,
      hfillCard]
    omega
  · rw [Finset.sum_union hdis, htoggleSum]
    simp [fillerSum]

/-- Finrank-sized independent reservoir specialization: its direction family
automatically spans, so every target has an exact-`d` labelled preimage. -/
theorem exists_fixedCardinality_sum_of_card_eq_finrank
    [FiniteDimensional (ZMod q) V]
    (R : OccurrenceReservoir (F := ZMod q) C k (q - 1))
    (hk : k = Module.finrank (ZMod q) V)
    (d : ℕ) (hbase : k * (q - 1) ≤ d)
    (hcapacity : d + k * (q - 1) ≤ Fintype.card Ω)
    (y : V) :
    ∃ S : Finset Ω, S.card = d ∧ (∑ ω ∈ S, C ω) = y := by
  have hcard : Fintype.card (Fin k) = Module.finrank (ZMod q) V := by
    simpa using hk
  have hspan := R.independent.span_eq_top_of_card_eq_finrank' hcard
  exact exists_fixedCardinality_sum_of_span_eq_top
    R hspan d hbase hcapacity y

end OccurrenceReservoir

end GaoFormal

#print axioms GaoFormal.exists_repeatedDirection_sum_eq_smul
#print axioms GaoFormal.exists_directionToggleSet_sum_eq
#print axioms GaoFormal.OccurrenceReservoir.exists_toggledSelection_sum_eq_coefficients
#print axioms GaoFormal.OccurrenceReservoir.exists_fixedCardinality_sum_of_span_eq_top
#print axioms GaoFormal.OccurrenceReservoir.exists_fixedCardinality_sum_of_card_eq_finrank
