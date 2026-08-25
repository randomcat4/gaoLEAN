import GaoFormal.Matching.LocalExchange

/-!
# Affine-coset coordinates in the deleted-edge quotient

This file removes four explicit coordinate hypotheses from the first crossed
replacement milestone.  Every vector in the full old-difference span becomes
a scalar multiple of the deleted edge difference modulo the span of all other
edge differences.
-/

namespace GaoFormal.IndependentDifferenceMatching

open Set Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {A : Finset V} {ι : Type*}

/-- The span of the differences left after deleting edge `i` is contained in
the span of all old differences. -/
theorem deletedSpan_le_fullSpan [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    deletedSpan M i ≤ Submodule.span F (Set.range M.difference) := by
  change Submodule.span F
      (Set.range fun j : Remaining i => M.difference j.1) ≤
    Submodule.span F (Set.range M.difference)
  rw [Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  exact Submodule.subset_span ⟨j.1, rfl⟩

/-- Deleting one member of an independent family leaves that member outside
the span of the remaining family.  This explicit finite-index proof avoids
silently replacing occurrence labels by values. -/
theorem difference_not_mem_deletedSpan
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    M.difference i ∉ deletedSpan M i := by
  have hrange :
      Set.range (fun j : Remaining i => M.difference j.1) =
        M.difference '' ({i}ᶜ : Set ι) := by
    ext x
    constructor
    · rintro ⟨j, rfl⟩
      exact ⟨j.1, by simpa using j.2, rfl⟩
    · rintro ⟨j, hj, rfl⟩
      exact ⟨⟨j, by simpa using hj⟩, rfl⟩
  rw [deletedSpan, hrange]
  exact M.independent.notMem_span i

/-- The exact independence bridge required by the affine exchange: if the
left endpoint direction lies outside the full old-difference span, its class
and the deleted edge difference form an independent pair in the quotient by
the other differences. -/
theorem quotient_pair_independent_of_left_outside [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) {u₀ : V}
    (hout : M.left i - u₀ ∉ Submodule.span F (Set.range M.difference)) :
    LinearIndependent F
      ![Submodule.Quotient.mk (p := deletedSpan M i) (M.left i - u₀),
        Submodule.Quotient.mk (p := deletedSpan M i) (M.difference i)] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  let c : V := M.left i - u₀
  let d : V := M.difference i
  have hmk : Submodule.Quotient.mk (p := deletedSpan M i) (a • c + b • d) = 0 := by
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul,
      Submodule.Quotient.mk_smul]
    exact hab
  have hzdel : a • c + b • d ∈ deletedSpan M i :=
    (Submodule.Quotient.mk_eq_zero (deletedSpan M i)).1 hmk
  have hzfull : a • c + b • d ∈
      Submodule.span F (Set.range M.difference) :=
    deletedSpan_le_fullSpan M i hzdel
  have hdfull : d ∈ Submodule.span F (Set.range M.difference) :=
    Submodule.subset_span ⟨i, rfl⟩
  have ha : a = 0 := by
    by_contra hane
    apply hout
    change c ∈ Submodule.span F (Set.range M.difference)
    rw [← (Submodule.smul_mem_iff
      (Submodule.span F (Set.range M.difference)) hane)]
    rw [show a • c = (a • c + b • d) - b • d by abel]
    exact Submodule.sub_mem _ hzfull (Submodule.smul_mem _ b hdfull)
  have hdq : Submodule.Quotient.mk (p := deletedSpan M i) d ≠ 0 := by
    intro hdq
    exact difference_not_mem_deletedSpan M i
      ((Submodule.Quotient.mk_eq_zero (deletedSpan M i)).1 hdq)
  rw [ha, zero_smul, zero_add] at hab
  exact ⟨ha, (smul_eq_zero.mp hab).resolve_right hdq⟩

theorem exists_quotient_eq_smul_of_mem_fullSpan [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) {x : V}
    (hx : x ∈ Submodule.span F (Set.range M.difference)) :
    ∃ t : F, Submodule.Quotient.mk (p := deletedSpan M i) x =
      t • Submodule.Quotient.mk (p := deletedSpan M i) (M.difference i) := by
  classical
  rcases (Submodule.mem_span_range_iff_exists_fun F).1 hx with ⟨a, ha⟩
  let rest : V := ∑ j ∈ Finset.univ.erase i, a j • M.difference j
  have hrest : rest ∈ deletedSpan M i := by
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨⟨j, ?_⟩, rfl⟩
    exact Finset.ne_of_mem_erase hj
  have hsplit : rest + a i • M.difference i = x := by
    calc
      rest + a i • M.difference i = ∑ j, a j • M.difference j := by
        exact Finset.sum_erase_add Finset.univ _ (Finset.mem_univ i)
      _ = x := ha
  refine ⟨a i, ?_⟩
  rw [← hsplit, Submodule.Quotient.mk_add, Submodule.Quotient.mk_smul]
  rw [(Submodule.Quotient.mk_eq_zero (deletedSpan M i)).2 hrest, zero_add]

/-- Exact four quotient-coordinate identities used by the two crossed
replacements.  No choice of representatives or hidden occurrence step remains. -/
theorem exists_crossed_quotient_coordinates [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι)
    {u₀ u v : V}
    (hu : u - u₀ ∈ Submodule.span F (Set.range M.difference))
    (hv : v - u₀ ∈ Submodule.span F (Set.range M.difference)) :
    ∃ t s : F,
      let c := Submodule.Quotient.mk (p := deletedSpan M i) (M.left i - u₀)
      let d := Submodule.Quotient.mk (p := deletedSpan M i) (M.difference i)
      Submodule.Quotient.mk (p := deletedSpan M i) (u - M.left i) = -c + t • d ∧
      Submodule.Quotient.mk (p := deletedSpan M i) (v - M.right i) =
        -c + (s - 1) • d ∧
      Submodule.Quotient.mk (p := deletedSpan M i) (v - M.left i) = -c + s • d ∧
      Submodule.Quotient.mk (p := deletedSpan M i) (u - M.right i) =
        -c + (t - 1) • d := by
  rcases exists_quotient_eq_smul_of_mem_fullSpan M i hu with ⟨t, ht⟩
  rcases exists_quotient_eq_smul_of_mem_fullSpan M i hv with ⟨s, hs⟩
  refine ⟨t, s, ?_⟩
  dsimp only
  constructor
  · rw [show u - M.left i = (u - u₀) - (M.left i - u₀) by abel]
    rw [Submodule.Quotient.mk_sub, ht]
    abel
  constructor
  · rw [show v - M.right i =
        (v - u₀) - ((M.left i - u₀) + M.difference i) by
      simp [difference]]
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add, hs]
    module
  constructor
  · rw [show v - M.left i = (v - u₀) - (M.left i - u₀) by abel]
    rw [Submodule.Quotient.mk_sub, hs]
    abel
  · rw [show u - M.right i =
        (u - u₀) - ((M.left i - u₀) + M.difference i) by
      simp [difference]]
    rw [Submodule.Quotient.mk_sub, Submodule.Quotient.mk_add, ht]
    module

/-- The crossed-replacement contradiction in the exact affine-coset setup of
the source proof.  If two distinct unused points exist and `2 ≠ 0`, every
matched left endpoint lies in their common affine coset of the old-difference
span. -/
theorem left_sub_mem_fullSpan_of_maximum [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (hmax : M.IsMaximum)
    (i : ι) {u₀ u v : V}
    (hu₀A : u₀ ∈ A) (huA : u ∈ A) (hvA : v ∈ A)
    (hu₀ : ∀ z, u₀ ≠ M.endpoint z)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v) (htwo : (2 : F) ≠ 0) :
    M.left i - u₀ ∈ Submodule.span F (Set.range M.difference) := by
  by_contra hout
  have huW := all_unused_sub_mem_span M hmax hu₀A hu₀ huA hu
  have hvW := all_unused_sub_mem_span M hmax hu₀A hu₀ hvA hv
  have hcd := quotient_pair_independent_of_left_outside M i hout
  rcases exists_crossed_quotient_coordinates M i huW hvW with ⟨t, s, hcoords⟩
  dsimp only at hcoords
  rcases hcoords with ⟨hfirst0, hfirst1, hsecond0, hsecond1⟩
  exact not_crossedCoordinateConfiguration_of_maximum M hmax i huA hvA hu hv
    huv htwo hcd t s hfirst0 hfirst1 hsecond0 hsecond1

/-- Right endpoints satisfy the same affine-coset containment, because their
difference from the corresponding left endpoint is an old matching
difference. -/
theorem right_sub_mem_fullSpan_of_maximum [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (hmax : M.IsMaximum)
    (i : ι) {u₀ u v : V}
    (hu₀A : u₀ ∈ A) (huA : u ∈ A) (hvA : v ∈ A)
    (hu₀ : ∀ z, u₀ ≠ M.endpoint z)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v) (htwo : (2 : F) ≠ 0) :
    M.right i - u₀ ∈ Submodule.span F (Set.range M.difference) := by
  rw [show M.right i - u₀ = (M.left i - u₀) + M.difference i by
    simp [difference]]
  exact Submodule.add_mem _
    (left_sub_mem_fullSpan_of_maximum M hmax i hu₀A huA hvA hu₀ hu hv huv htwo)
    (Submodule.subset_span ⟨i, rfl⟩)

/-- The finite set of vertices occupied by the occurrence-labelled matching. -/
noncomputable def usedVertices [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) : Finset V :=
  by
    classical
    exact Finset.univ.image M.endpoint

theorem usedVertices_subset [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) :
    usedVertices M ⊆ A := by
  classical
  intro x hx
  change x ∈ Finset.univ.image M.endpoint at hx
  rcases Finset.mem_image.mp hx with ⟨z, _, rfl⟩
  cases z with
  | inl i => exact M.left_mem i
  | inr i => exact M.right_mem i

theorem card_usedVertices [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) :
    (usedVertices M).card = 2 * Fintype.card ι := by
  classical
  change (Finset.univ.image M.endpoint).card = 2 * Fintype.card ι
  have hinj : Function.Injective M.endpoint := M.endpoint_injective
  have himage : (Finset.univ.image M.endpoint).card =
      (Finset.univ : Finset (ι ⊕ ι)).card :=
    Finset.card_image_iff.mpr hinj.injOn
  rw [himage]
  simp [Fintype.card_sum, Nat.two_mul]

/-- The exact counting step behind the source phrase “there are at least two
unmatched vertices”. -/
theorem exists_two_unused_of_card_lt_half [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι)
    (hcard : Fintype.card ι < A.card / 2) :
    ∃ u ∈ A, (∀ z, u ≠ M.endpoint z) ∧
      ∃ v ∈ A, (∀ z, v ≠ M.endpoint z) ∧ u ≠ v := by
  classical
  let U : Finset V := A \ usedVertices M
  have hUcard : U.card = A.card - 2 * Fintype.card ι := by
    change (A \ usedVertices M).card = A.card - 2 * Fintype.card ι
    rw [Finset.card_sdiff]
    have hinter : usedVertices M ∩ A = usedVertices M :=
      Finset.inter_eq_left.mpr (usedVertices_subset M)
    rw [hinter, card_usedVertices]
  have hUtwo : 1 < U.card := by
    rw [hUcard]
    omega
  rcases Finset.one_lt_card.mp hUtwo with ⟨u, huU, v, hvU, huv⟩
  have huA : u ∈ A := (Finset.mem_sdiff.mp huU).1
  have hvA : v ∈ A := (Finset.mem_sdiff.mp hvU).1
  have huUnused : ∀ z, u ≠ M.endpoint z := by
    intro z huz
    apply (Finset.mem_sdiff.mp huU).2
    change u ∈ Finset.univ.image M.endpoint
    apply Finset.mem_image.mpr
    exact ⟨z, Finset.mem_univ z, huz.symm⟩
  have hvUnused : ∀ z, v ≠ M.endpoint z := by
    intro z hvz
    apply (Finset.mem_sdiff.mp hvU).2
    change v ∈ Finset.univ.image M.endpoint
    apply Finset.mem_image.mpr
    exact ⟨z, Finset.mem_univ z, hvz.symm⟩
  exact ⟨u, huA, huUnused, v, hvA, hvUnused, huv⟩

/-- Under the strict half-cardinality hypothesis, all points of `A` lie in
one affine coset of the old-difference span.  The two unused points are
produced by `exists_two_unused_of_card_lt_half`, not assumed. -/
theorem exists_base_all_sub_mem_fullSpan [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (hmax : M.IsMaximum)
    (hcard : Fintype.card ι < A.card / 2) (htwo : (2 : F) ≠ 0) :
    ∃ u₀ ∈ A, ∀ x ∈ A,
      x - u₀ ∈ Submodule.span F (Set.range M.difference) := by
  classical
  rcases exists_two_unused_of_card_lt_half M hcard with
    ⟨u, huA, hu, v, hvA, hv, huv⟩
  refine ⟨u, huA, ?_⟩
  intro x hxA
  by_cases hxUsed : x ∈ usedVertices M
  · change x ∈ Finset.univ.image M.endpoint at hxUsed
    rcases Finset.mem_image.mp hxUsed with ⟨z, _, rfl⟩
    cases z with
    | inl i =>
        exact left_sub_mem_fullSpan_of_maximum M hmax i huA huA hvA
          hu hu hv huv htwo
    | inr i =>
        exact right_sub_mem_fullSpan_of_maximum M hmax i huA huA hvA
          hu hu hv huv htwo
  · have hxUnused : ∀ z, x ≠ M.endpoint z := by
      intro z hxz
      apply hxUsed
      change x ∈ Finset.univ.image M.endpoint
      exact Finset.mem_image.mpr ⟨z, Finset.mem_univ z, hxz.symm⟩
    exact all_unused_sub_mem_span M hmax huA hu hxA hxUnused

/-- Full independent-difference matching theorem for a maximum matching.
Here `finrank (vectorSpan F A)` is Mathlib's affine dimension of the finite
point set `A`.  This closes the crossed-replacement, maximality, finite-count,
and affine-dimension branches of Theorem 1.1. -/
theorem card_eq_min_finrank_vectorSpan_half_of_maximum [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (hmax : M.IsMaximum)
    (htwo : (2 : F) ≠ 0) :
    Fintype.card ι =
      min (Module.finrank F (vectorSpan F (A : Set V))) (A.card / 2) := by
  classical
  have hhalf : Fintype.card ι ≤ A.card / 2 := by
    have hused := Finset.card_le_card (usedVertices_subset M)
    rw [card_usedVertices] at hused
    omega
  have hdim : Fintype.card ι ≤
      Module.finrank F (vectorSpan F (A : Set V)) := by
    letI : Module.Finite F (vectorSpan F (A : Set V)) :=
      finiteDimensional_vectorSpan_of_finite F A.finite_toSet
    have hspan : Submodule.span F (Set.range M.difference) ≤
        vectorSpan F (A : Set V) := by
      rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa [difference] using
        (vsub_mem_vectorSpan F (show M.right i ∈ (A : Set V) from M.right_mem i)
          (show M.left i ∈ (A : Set V) from M.left_mem i))
    have hrank := Submodule.finrank_mono hspan
    have hind : LinearIndependent F M.difference := by
      change LinearIndependent F (fun i => M.right i - M.left i)
      exact M.independent
    rw [finrank_span_eq_card hind] at hrank
    exact hrank
  apply le_antisymm (le_min hdim hhalf)
  by_contra hmin
  have hlt : Fintype.card ι <
      min (Module.finrank F (vectorSpan F (A : Set V))) (A.card / 2) :=
    Nat.lt_of_not_ge hmin
  have hcard : Fintype.card ι < A.card / 2 :=
    lt_of_lt_of_le hlt (min_le_right _ _)
  have hfinrank : Fintype.card ι <
      Module.finrank F (vectorSpan F (A : Set V)) :=
    lt_of_lt_of_le hlt (min_le_left _ _)
  rcases exists_base_all_sub_mem_fullSpan M hmax hcard htwo with
    ⟨u₀, hu₀A, hall⟩
  letI : Module.Finite F (Submodule.span F (Set.range M.difference)) :=
    Module.Finite.span_of_finite F (Set.finite_range M.difference)
  have hvspan : vectorSpan F (A : Set V) ≤
      Submodule.span F (Set.range M.difference) := by
    rw [vectorSpan_eq_span_vsub_set_right F
      (show u₀ ∈ (A : Set V) from hu₀A), Submodule.span_le]
    rintro _ ⟨x, hxA, rfl⟩
    simpa using hall x hxA
  have hrank := Submodule.finrank_mono hvspan
  have hind : LinearIndependent F M.difference := by
    change LinearIndependent F (fun i => M.right i - M.left i)
    exact M.independent
  rw [finrank_span_eq_card hind] at hrank
  omega

/-- Reindex a matching along an equivalence of occurrence labels. -/
def reindex {κ : Type*}
    (M : IndependentDifferenceMatching (F := F) A ι) (e : κ ≃ ι) :
    IndependentDifferenceMatching (F := F) A κ where
  left := M.left ∘ e
  right := M.right ∘ e
  left_mem := fun i => M.left_mem (e i)
  right_mem := fun i => M.right_mem (e i)
  endpoint_injective := by
    have he : Function.Injective (Sum.map e e) := (e.injective.sumMap e.injective)
    have hfun : Sum.elim (M.left ∘ e) (M.right ∘ e) =
        M.endpoint ∘ Sum.map e e := by
      funext z
      cases z <;> rfl
    rw [hfun]
    exact M.endpoint_injective.comp he
  independent := by
    change LinearIndependent F (fun i => M.right (e i) - M.left (e i))
    exact M.independent.comp e e.injective

/-- The empty occurrence-labelled matching, used to seed the finite maximum
construction. -/
def emptyMatching : IndependentDifferenceMatching (F := F) A (Fin 0) where
  left := Fin.elim0
  right := Fin.elim0
  left_mem := fun i => i.elim0
  right_mem := fun i => i.elim0
  endpoint_injective := Function.injective_of_subsingleton _
  independent := linearIndependent_empty_type

theorem card_le_half [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) :
    Fintype.card ι ≤ A.card / 2 := by
  have hused := Finset.card_le_card (usedVertices_subset M)
  rw [card_usedVertices] at hused
  omega

/-- A maximum matching exists because all achievable sizes lie in the finite
interval `0 .. |A|/2`.  Arbitrary finite occurrence types are transported to
canonical `Fin n` labels before comparison. -/
theorem exists_maximum_matching :
    ∃ n : ℕ, ∃ M : IndependentDifferenceMatching (F := F) A (Fin n),
      M.IsMaximum := by
  classical
  let S : Finset ℕ := (Finset.range (A.card / 2 + 1)).filter fun n =>
    Nonempty (IndependentDifferenceMatching (F := F) A (Fin n))
  have hS : S.Nonempty := by
    refine ⟨0, ?_⟩
    change 0 ∈ (Finset.range (A.card / 2 + 1)).filter fun n =>
      Nonempty (IndependentDifferenceMatching (F := F) A (Fin n))
    rw [Finset.mem_filter]
    exact ⟨by simp, ⟨emptyMatching⟩⟩
  let n := S.max' hS
  have hnS : n ∈ S := Finset.max'_mem S hS
  have hnmatch : Nonempty (IndependentDifferenceMatching (F := F) A (Fin n)) :=
    (Finset.mem_filter.mp hnS).2
  rcases hnmatch with ⟨M⟩
  refine ⟨n, M, ?_⟩
  intro κ _ N
  have hkhalf := card_le_half N
  have hkS : Fintype.card κ ∈ S := by
    change Fintype.card κ ∈
      (Finset.range (A.card / 2 + 1)).filter fun n =>
        Nonempty (IndependentDifferenceMatching (F := F) A (Fin n))
    rw [Finset.mem_filter]
    constructor
    · simp only [Finset.mem_range]
      omega
    · exact ⟨reindex N (Fintype.equivFin κ).symm⟩
  simpa [n] using Finset.le_max' S (Fintype.card κ) hkS

/-- Standalone existence form of the independent-difference matching main
theorem: a maximum matching with exactly the stated minimum size exists. -/
theorem exists_maximum_matching_at_formula (htwo : (2 : F) ≠ 0) :
    ∃ M : IndependentDifferenceMatching (F := F) A
        (Fin (min (Module.finrank F (vectorSpan F (A : Set V))) (A.card / 2))),
      M.IsMaximum := by
  rcases exists_maximum_matching (F := F) (A := A) with ⟨n, M, hmax⟩
  have hn := card_eq_min_finrank_vectorSpan_half_of_maximum M hmax htwo
  simp only [Fintype.card_fin] at hn
  subst n
  exact ⟨M, hmax⟩

end GaoFormal.IndependentDifferenceMatching
