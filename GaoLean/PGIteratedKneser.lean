import GaoLean.PGGMOFoundations

/-!
# Iterated Kneser inequality for finite setpartitions

This file derives the finite-list form of Kneser's theorem needed by the
setpartition layer.  The proof quotients by the stabilizer of the complete
sumset, proves the aperiodic inequality there by induction, and then lifts the
cardinality inequality back to the original group.
-/

namespace GaoLean

open scoped Pointwise

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

/-- Sum of a finite list of finite subsets; the empty sum is `{0}`. -/
def iteratedFinsetSum : List (Finset A) → Finset A
  | [] => {0}
  | B :: P => B + iteratedFinsetSum P

@[simp]
theorem iteratedFinsetSum_nil :
    iteratedFinsetSum ([] : List (Finset A)) = {0} := rfl

@[simp]
theorem iteratedFinsetSum_cons (B : Finset A) (P : List (Finset A)) :
    iteratedFinsetSum (B :: P) = B + iteratedFinsetSum P := rfl

/-- A sumset of a list of nonempty finite sets is nonempty. -/
theorem iteratedFinsetSum_nonempty
    (P : List (Finset A)) (hP : ∀ B ∈ P, B.Nonempty) :
    (iteratedFinsetSum P).Nonempty := by
  induction P with
  | nil => simp
  | cons B P ih =>
      exact (hP B (by simp)).add
        (ih fun C hC => hP C (by simp [hC]))

/-- A homomorphism commutes with the finite-list sumset construction. -/
theorem image_iteratedFinsetSum
    {B : Type*} [AddCommGroup B] [DecidableEq B]
    (f : A →+ B) (P : List (Finset A)) :
    (iteratedFinsetSum P).image f =
      iteratedFinsetSum (P.map fun C => C.image f) := by
  induction P with
  | nil => simp [iteratedFinsetSum]
  | cons C P ih =>
      simp only [iteratedFinsetSum_cons, List.map_cons]
      rw [Finset.image_add, ih]

/-- Aperiodic iterated Kneser inequality.  Every partial tail is aperiodic
because its stabilizer embeds into the stabilizer of the complete sumset. -/
theorem sum_card_add_one_le_card_iteratedFinsetSum_add_length_of_aperiodic
    (P : List (Finset A)) (hP : ∀ B ∈ P, B.Nonempty)
    (hstab : (iteratedFinsetSum P).addStab = {0}) :
    (P.map Finset.card).sum + 1 ≤
      (iteratedFinsetSum P).card + P.length := by
  induction P with
  | nil => simp [iteratedFinsetSum]
  | cons C P ih =>
      change (C + iteratedFinsetSum P).addStab = {0} at hstab
      have hC : C.Nonempty := hP C (by simp)
      have htail : ∀ B ∈ P, B.Nonempty := by
        intro B hB
        exact hP B (by simp [hB])
      have htailNonempty := iteratedFinsetSum_nonempty P htail
      have htailStab : (iteratedFinsetSum P).addStab = {0} := by
        apply Finset.eq_singleton_iff_unique_mem.mpr
        refine ⟨htailNonempty.zero_mem_addStab, ?_⟩
        intro a ha
        have ha' : a ∈ (C + iteratedFinsetSum P).addStab :=
          Finset.subset_addStab_add_right hC ha
        rw [hstab] at ha'
        simpa using ha'
      have hind := ih htail htailStab
      have hk := Finset.add_kneser C (iteratedFinsetSum P)
      have hk' : C.card + (iteratedFinsetSum P).card ≤
          (C + iteratedFinsetSum P).card + 1 := by
        simpa [hstab] using hk
      simp only [List.map_cons, List.sum_cons, List.length_cons,
        iteratedFinsetSum_cons]
      omega

/-- Iterated Kneser inequality in the original group.  Each summand is first
saturated by the stabilizer of the complete sumset; occurrence multiplicity
is intentionally not involved at this finite-set layer. -/
theorem sum_card_addStab_add_card_addStab_le
    (P : List (Finset A)) (hP : ∀ B ∈ P, B.Nonempty) :
    (P.map fun B =>
        (B + (iteratedFinsetSum P).addStab).card).sum +
        (iteratedFinsetSum P).addStab.card ≤
      (iteratedFinsetSum P).card +
        P.length * (iteratedFinsetSum P).addStab.card := by
  classical
  let T := iteratedFinsetSum P
  have hT : T.Nonempty := iteratedFinsetSum_nonempty P hP
  let H : AddSubgroup A := AddAction.stabilizer A (T : Set A)
  let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
  let Pq : List (Finset (A ⧸ H)) := P.map fun B => B.image q
  have hPq : ∀ C ∈ Pq, C.Nonempty := by
    intro C hC
    obtain ⟨B, hBP, rfl⟩ := List.mem_map.mp hC
    exact (hP B hBP).image q
  have hsumq : iteratedFinsetSum Pq = T.image q := by
    simpa [Pq, T] using (image_iteratedFinsetSum q P).symm
  have hstabq : (iteratedFinsetSum Pq).addStab = {0} := by
    rw [hsumq]
    change (T.image ((↑) : A → A ⧸ AddAction.stabilizer A (T : Set A))).addStab = {0}
    rw [Finset.addStab_image_coe_quotient hT]
    ext x
    simp
  have hap :=
    sum_card_add_one_le_card_iteratedFinsetSum_add_length_of_aperiodic
      Pq hPq hstabq
  have hterm (B : Finset A) :
      T.addStab.card * (B.image q).card = (B + T.addStab).card := by
    simpa [H, q] using Finset.card_addStab_add_card_image_coe' B T
  have hsumcard :
      T.addStab.card * (Pq.map Finset.card).sum =
        (P.map fun B => (B + T.addStab).card).sum := by
    rw [← List.sum_map_mul_left]
    simp only [Pq, List.map_map]
    congr 1
    exact List.map_congr_left fun B _ => hterm B
  have hTcard :
      T.addStab.card * (iteratedFinsetSum Pq).card = T.card := by
    rw [hsumq]
    simpa [H, q] using Finset.card_addStab_add_card_image_coe' T T
  have hmul := Nat.mul_le_mul_left T.addStab.card hap
  have hlength : Pq.length = P.length := by simp [Pq]
  rw [hlength] at hmul
  simp only [Nat.mul_add, Nat.mul_one] at hmul
  rw [Nat.mul_comm T.addStab.card P.length] at hmul
  dsimp only [T] at hsumcard hTcard hmul ⊢
  omega

end GaoLean

#print axioms GaoLean.iteratedFinsetSum_nonempty
#print axioms GaoLean.image_iteratedFinsetSum
#print axioms GaoLean.sum_card_add_one_le_card_iteratedFinsetSum_add_length_of_aperiodic
#print axioms GaoLean.sum_card_addStab_add_card_addStab_le
