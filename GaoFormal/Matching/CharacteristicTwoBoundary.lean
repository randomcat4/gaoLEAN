import GaoFormal.Matching.Basic

/-!
# The sharp characteristic-two boundary

The affine independent-difference formula needs the hypothesis `2 ≠ 0`.
On the four-point affine plane over `ZMod 2`, every perfect matching has two
equal difference directions, while a one-edge independent matching exists.
-/

namespace GaoFormal

open scoped BigOperators

/-- The four-point vector space used by the characteristic-two counterexample. -/
abbrev F2Plane := Fin 2 → ZMod 2

private theorem sum_univ_f2Plane : ∑ v : F2Plane, v = 0 := by
  decide

/-- Four distinct endpoints in `F₂²` exhaust the plane, so the sum of the two
edge differences is zero. -/
theorem f2Plane_sum_differences_eq_zero
    (M : IndependentDifferenceMatching (F := ZMod 2)
      (Finset.univ : Finset F2Plane) (Fin 2)) :
    ∑ i : Fin 2, M.difference i = 0 := by
  have hcard : Fintype.card ((Fin 2) ⊕ (Fin 2)) = Fintype.card F2Plane := by
    decide
  have hbij : Function.Bijective M.endpoint :=
    (Fintype.bijective_iff_injective_and_card M.endpoint).2
      ⟨M.endpoint_injective, hcard⟩
  have hsum : ∑ z : (Fin 2) ⊕ (Fin 2), M.endpoint z = 0 := by
    rw [hbij.sum_comp (fun v : F2Plane => v)]
    exact sum_univ_f2Plane
  have hsum' :
      (M.left 0 + M.left 1) + (M.right 0 + M.right 1) = 0 := by
    simpa [IndependentDifferenceMatching.endpoint, Fin.sum_univ_two] using hsum
  simpa [IndependentDifferenceMatching.difference, Fin.sum_univ_two,
    ZModModule.sub_eq_add, add_left_comm, add_comm] using hsum'

/-- No independent-difference matching can use two edges on all four points of
`F₂²`.  This is the negative half of the sharp boundary witness. -/
theorem no_two_edge_independentDifferenceMatching_f2Plane :
    ¬ Nonempty (IndependentDifferenceMatching (F := ZMod 2)
      (Finset.univ : Finset F2Plane) (Fin 2)) := by
  rintro ⟨M⟩
  have hsum : M.difference 0 + M.difference 1 = 0 := by
    simpa [Fin.sum_univ_two] using f2Plane_sum_differences_eq_zero M
  have heq : M.difference 0 = M.difference 1 := by
    have hneg : M.difference 0 = -M.difference 1 :=
      eq_neg_of_add_eq_zero_left hsum
    simpa [ZModModule.neg_eq_self] using hneg
  exact Fin.zero_ne_one (M.independent.injective heq)

/-- A one-edge matching does exist, so the exact maximum in `F₂²` is one. -/
def oneEdgeIndependentDifferenceMatchingF2Plane :
    IndependentDifferenceMatching (F := ZMod 2)
      (Finset.univ : Finset F2Plane) (Fin 1) where
  left := fun _ => 0
  right := fun _ => fun i => if i = 0 then 1 else 0
  left_mem := by simp
  right_mem := by simp
  endpoint_injective := by
    intro a b hab
    fin_cases a <;> fin_cases b
    · rfl
    · exfalso
      have h := congrFun hab 0
      norm_num at h
    · exfalso
      have h := congrFun hab 0
      norm_num at h
    · rfl
  independent := by
    rw [linearIndependent_unique_iff]
    intro h
    have h0 := congrFun h 0
    norm_num at h0

/-- The characteristic-two example has exact matching number one: one edge
exists, and a two-edge (perfect) matching does not. -/
theorem f2Plane_exact_boundary :
    Nonempty (IndependentDifferenceMatching (F := ZMod 2)
      (Finset.univ : Finset F2Plane) (Fin 1)) ∧
    ¬ Nonempty (IndependentDifferenceMatching (F := ZMod 2)
      (Finset.univ : Finset F2Plane) (Fin 2)) :=
  ⟨⟨oneEdgeIndependentDifferenceMatchingF2Plane⟩,
    no_two_edge_independentDifferenceMatching_f2Plane⟩

end GaoFormal
