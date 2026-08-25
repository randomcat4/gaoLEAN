import GaoFormal.Matching.AffineBridge

/-!
# Occurrence-labelled lift of the matching theorem

This file formalizes Corollary 2.1.  A sequence is represented by a finite
type of occurrence labels `Ω` and a value map `C : Ω → V`; equal values never
identify occurrence labels.
-/

namespace GaoFormal

open Set Submodule

variable {F V Ω : Type*} [Field F] [AddCommGroup V] [Module F V]

noncomputable local instance : DecidableEq V := Classical.decEq V

/-- Values occurring at least `t` times in the occurrence-labelled sequence. -/
noncomputable def thresholdSupport [Fintype Ω] (C : Ω → V) (t : ℕ) : Finset V := by
  classical
  exact (Finset.univ.image C).filter fun x =>
    t ≤ Fintype.card {ω : Ω // C ω = x}

theorem thresholdSupport_card_fiber [Fintype Ω] (C : Ω → V) (t : ℕ) {x : V}
    (hx : x ∈ thresholdSupport C t) :
    t ≤ Fintype.card {ω : Ω // C ω = x} := by
  classical
  exact (Finset.mem_filter.mp hx).2

/-- Choose `t` distinct occurrence labels from a fiber of size at least `t`. -/
noncomputable def chooseCopies [Fintype Ω] (C : Ω → V) (t : ℕ) (x : V)
    (hx : t ≤ Fintype.card {ω : Ω // C ω = x}) : Fin t → Ω :=
  fun j => ((Fintype.equivFin {ω : Ω // C ω = x}).symm (Fin.castLE hx j)).1

theorem chooseCopies_value [Fintype Ω] (C : Ω → V) (t : ℕ) (x : V)
    (hx : t ≤ Fintype.card {ω : Ω // C ω = x}) (j : Fin t) :
    C (chooseCopies C t x hx j) = x :=
  ((Fintype.equivFin {ω : Ω // C ω = x}).symm (Fin.castLE hx j)).2

theorem chooseCopies_injective [Fintype Ω] (C : Ω → V) (t : ℕ) (x : V)
    (hx : t ≤ Fintype.card {ω : Ω // C ω = x}) :
    Function.Injective (chooseCopies C t x hx) := by
  intro a b hab
  have hsub :
      (Fintype.equivFin {ω : Ω // C ω = x}).symm (Fin.castLE hx a) =
        (Fintype.equivFin {ω : Ω // C ω = x}).symm (Fin.castLE hx b) := by
    apply Subtype.ext
    exact hab
  have hfin := (Fintype.equivFin {ω : Ω // C ω = x}).symm.injective hsub
  exact Fin.castLE_injective hx hfin

/-- `k` independent directions, each supplied by `t` ordered pairs, with all
`2tk` occurrence endpoints globally distinct. -/
structure OccurrenceReservoir [Fintype Ω] (C : Ω → V) (k t : ℕ) where
  left : Fin k × Fin t → Ω
  right : Fin k × Fin t → Ω
  endpoint_injective : Function.Injective (Sum.elim left right)
  direction : Fin k → V
  difference_eq : ∀ i j, C (right (i, j)) - C (left (i, j)) = direction i
  independent : LinearIndependent F direction

namespace IndependentDifferenceMatching

/-- Lift support-value pairs to pairwise disjoint occurrence pairs by choosing
copies independently inside disjoint value fibers. -/
noncomputable def toOccurrenceReservoir [Fintype Ω] (C : Ω → V) (t : ℕ)
    {k : ℕ}
    (M : IndependentDifferenceMatching (F := F) (thresholdSupport C t) (Fin k)) :
    OccurrenceReservoir (F := F) C k t := by
  classical
  let hl : ∀ i : Fin k, t ≤ Fintype.card {ω : Ω // C ω = M.left i} :=
    fun i => thresholdSupport_card_fiber C t (M.left_mem i)
  let hr : ∀ i : Fin k, t ≤ Fintype.card {ω : Ω // C ω = M.right i} :=
    fun i => thresholdSupport_card_fiber C t (M.right_mem i)
  let L : Fin k × Fin t → Ω := fun p => chooseCopies C t (M.left p.1) (hl p.1) p.2
  let R : Fin k × Fin t → Ω := fun p => chooseCopies C t (M.right p.1) (hr p.1) p.2
  refine
    { left := L
      right := R
      endpoint_injective := ?_
      direction := M.difference
      difference_eq := ?_
      independent := ?_ }
  · have hL : Function.Injective L := by
      rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have hvalue : M.left i = M.left j := by
        calc
          M.left i = C (L (i, a)) := (chooseCopies_value C t _ _ _).symm
          _ = C (L (j, b)) := congrArg C hab
          _ = M.left j := chooseCopies_value C t _ _ _
      have hij : i = j := Sum.inl.inj (M.endpoint_injective hvalue)
      subst j
      have hab' : a = b := chooseCopies_injective C t (M.left i) (hl i) hab
      subst b
      rfl
    have hR : Function.Injective R := by
      rintro ⟨i, a⟩ ⟨j, b⟩ hab
      have hvalue : M.right i = M.right j := by
        calc
          M.right i = C (R (i, a)) := (chooseCopies_value C t _ _ _).symm
          _ = C (R (j, b)) := congrArg C hab
          _ = M.right j := chooseCopies_value C t _ _ _
      have hij : i = j := Sum.inr.inj (M.endpoint_injective hvalue)
      subst j
      have hab' : a = b := chooseCopies_injective C t (M.right i) (hr i) hab
      subst b
      rfl
    apply hL.sumElim hR
    rintro ⟨i, a⟩ ⟨j, b⟩ hab
    have hvalue : M.left i = M.right j := by
      calc
        M.left i = C (L (i, a)) := (chooseCopies_value C t _ _ _).symm
        _ = C (R (j, b)) := congrArg C hab
        _ = M.right j := chooseCopies_value C t _ _ _
    exact Sum.inl_ne_inr (M.endpoint_injective hvalue)
  · intro i j
    change C (R (i, j)) - C (L (i, j)) = M.difference i
    rw [chooseCopies_value C t (M.right i) (hr i) j,
      chooseCopies_value C t (M.left i) (hl i) j]
    rfl
  · change LinearIndependent F M.difference
    change LinearIndependent F (fun i => M.right i - M.left i)
    exact M.independent

theorem toOccurrenceReservoir_left_value [Fintype Ω] (C : Ω → V) (t : ℕ)
    {k : ℕ}
    (M : IndependentDifferenceMatching (F := F) (thresholdSupport C t) (Fin k))
    (i : Fin k) (j : Fin t) :
    C ((M.toOccurrenceReservoir C t).left (i, j)) = M.left i := by
  classical
  exact chooseCopies_value C t (M.left i)
    (thresholdSupport_card_fiber C t (M.left_mem i)) j

theorem toOccurrenceReservoir_right_value [Fintype Ω] (C : Ω → V) (t : ℕ)
    {k : ℕ}
    (M : IndependentDifferenceMatching (F := F) (thresholdSupport C t) (Fin k))
    (i : Fin k) (j : Fin t) :
    C ((M.toOccurrenceReservoir C t).right (i, j)) = M.right i := by
  classical
  exact chooseCopies_value C t (M.right i)
    (thresholdSupport_card_fiber C t (M.right_mem i)) j

end IndependentDifferenceMatching

/-- Corollary 2.1 in occurrence-labelled form. -/
theorem exists_occurrenceReservoir_at_threshold [Fintype Ω]
    (C : Ω → V) (t : ℕ) (htwo : (2 : F) ≠ 0) :
    Nonempty (OccurrenceReservoir (F := F) C
        (min (Module.finrank F
          (vectorSpan F ((thresholdSupport C t : Finset V) : Set V)))
          ((thresholdSupport C t).card / 2)) t) := by
  rcases IndependentDifferenceMatching.exists_maximum_matching_at_formula
      (F := F) (A := thresholdSupport C t) htwo with ⟨M, _⟩
  exact ⟨M.toOccurrenceReservoir C t⟩

end GaoFormal
