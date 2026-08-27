import MiscYD.AddCombi.Kneser.Kneser

/-!
# Scherk's one-representation sumset bound

This file records the `r = 1` case of the deletion form of Scherk's
theorem (Proposition 1.3 in the source used by the GMO formalization).
The proof uses Kneser's theorem together with the two fibres, modulo the
actual stabilizer of the sumset, containing the unique representation.
-/

namespace GaoLean

open scoped Pointwise

variable {G : Type*} [AddCommGroup G]

private theorem neg_mem_addStab [DecidableEq G]
    {S : Finset G} (hS : S.Nonempty) {x : G} (hx : x ∈ S.addStab) :
    -x ∈ S.addStab := by
  rw [← Finset.mem_coe, Finset.coe_addStab hS, SetLike.mem_coe] at hx ⊢
  exact (AddAction.stabilizer G (S : Set G)).neg_mem hx

/-- Scherk's sumset bound in deletion form (`r = 1`).  If deleting one
specified element of `B` genuinely shrinks `A + B`, then that lost sum has
a unique representation, and consequently `|A| + |B| - 1 ≤ |A + B|`.

No finiteness assumption is made on the ambient group: only the two input
finsets are finite. -/
theorem card_add_sub_one_le_of_add_ne_add_erase [DecidableEq G]
    (A B : Finset G) {z : G} (hA : A.Nonempty) (hz : z ∈ B)
    (hne : A + B ≠ A + B.erase z) :
    A.card + B.card - 1 ≤ (A + B).card := by
  let S : Finset G := A + B
  let H : Finset G := S.addStab
  have hS : S.Nonempty := hA.add ⟨z, hz⟩
  have hsmallSubset : A + B.erase z ⊆ S := by
    exact Finset.add_subset_add (fun _ ha ↦ ha) (Finset.erase_subset z B)
  have hsmallNe : A + B.erase z ≠ S := by
    simpa [S] using hne.symm
  obtain ⟨w, hwS, hwsmall⟩ :=
    Finset.exists_of_ssubset (hsmallSubset.ssubset_of_ne hsmallNe)
  obtain ⟨a, ha, b, hb, hab⟩ := (Finset.mem_add.mp (by simpa [S] using hwS))
  have hbz : b = z := by
    by_contra hbz
    apply hwsmall
    exact Finset.mem_add.mpr
      ⟨a, ha, b, Finset.mem_erase.mpr ⟨hbz, hb⟩, hab⟩
  subst b
  have hw : a + z = w := hab
  have hunique :
      ∀ a' b' : G, a' ∈ A → b' ∈ B → a' + b' = w → a' = a ∧ b' = z := by
    intro a' b' ha' hb' hab'
    have hb'z : b' = z := by
      by_contra hb'z
      apply hwsmall
      exact Finset.mem_add.mpr
        ⟨a', ha', b', Finset.mem_erase.mpr ⟨hb'z, hb'⟩, hab'⟩
    subst b'
    exact ⟨add_right_cancel (hab'.trans hw.symm), rfl⟩
  have hzeroH : 0 ∈ H := by
    exact hS.zero_mem_addStab
  let CA : Finset G := ({a} : Finset G) + H
  let CZ : Finset G := ({z} : Finset G) + H
  let Af : Finset G := A ∩ CA
  let Bf : Finset G := B ∩ CZ
  let Rf : Finset G := Bf.image fun y ↦ w - y
  have haCA : a ∈ CA := by
    simpa using Finset.add_mem_add (Finset.mem_singleton_self a) hzeroH
  have hzCZ : z ∈ CZ := by
    simpa using Finset.add_mem_add (Finset.mem_singleton_self z) hzeroH
  have haAf : a ∈ Af := Finset.mem_inter.mpr ⟨ha, haCA⟩
  have hzBf : z ∈ Bf := Finset.mem_inter.mpr ⟨hz, hzCZ⟩
  have hRfSubset : Rf ⊆ CA := by
    intro x hx
    obtain ⟨y, hyBf, rfl⟩ := Finset.mem_image.mp hx
    have hyCZ : y ∈ CZ := (Finset.mem_inter.mp hyBf).2
    obtain ⟨u, hu, h, hh, huh⟩ := Finset.mem_add.mp hyCZ
    have hu : u = z := Finset.mem_singleton.mp hu
    subst u
    have hneg : -h ∈ H := neg_mem_addStab hS hh
    change w - y ∈ ({a} : Finset G) + H
    have hmem : a + -h ∈ ({a} : Finset G) + H :=
      Finset.add_mem_add (Finset.mem_singleton_self a) hneg
    have heq : a + -h = w - y := by
      rw [← hw, ← huh]
      abel
    rwa [heq] at hmem
  have hAfInterRf : Af ∩ Rf = {a} := by
    apply Finset.Subset.antisymm
    · intro x hx
      have hxAf : x ∈ Af := (Finset.mem_inter.mp hx).1
      have hxA : x ∈ A := (Finset.mem_inter.mp hxAf).1
      have hxRf : x ∈ Rf := (Finset.mem_inter.mp hx).2
      obtain ⟨y, hyBf, hy⟩ := Finset.mem_image.mp hxRf
      have hyB : y ∈ B := (Finset.mem_inter.mp hyBf).1
      have hxy : x + y = w := by
        rw [← hy]
        abel
      exact Finset.mem_singleton.mpr (hunique x y hxA hyB hxy).1
    · intro x hx
      have hxa : x = a := Finset.mem_singleton.mp hx
      subst x
      apply Finset.mem_inter.mpr
      refine ⟨haAf, ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨z, hzBf, ?_⟩
      rw [← hw]
      abel
  have hRfCard : Rf.card = Bf.card := by
    unfold Rf
    rw [Finset.card_image_iff.mpr]
    intro x _ y _ hxy
    exact sub_right_injective hxy
  have hAfRfCard : Af.card + Bf.card ≤ H.card + 1 := by
    have hunionSubset : Af ∪ Rf ⊆ CA :=
      Finset.union_subset
        (Finset.Subset.trans Finset.inter_subset_right (fun _ hx ↦ hx)) hRfSubset
    have hunionCard := Finset.card_le_card hunionSubset
    have hCAcard : CA.card = H.card := by
      simpa [CA] using Finset.card_singleton_add a H
    have hinterCard : (Af ∩ Rf).card = 1 := by simp [hAfInterRf]
    have hpartition := Finset.card_union_add_card_inter Af Rf
    rw [hCAcard] at hunionCard
    rw [hinterCard, hRfCard] at hpartition
    omega
  have hCAminusSubset : CA \ Af ⊆ (A + H) \ A := by
    intro x hx
    have hxCA : x ∈ CA := (Finset.mem_sdiff.mp hx).1
    have hxnotAf : x ∉ Af := (Finset.mem_sdiff.mp hx).2
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.add_subset_add (Finset.singleton_subset_iff.mpr ha)
          (fun _ hh ↦ hh)
        hxCA
    · intro hxA
      exact hxnotAf (Finset.mem_inter.mpr ⟨hxA, hxCA⟩)
  have hCZminusSubset : CZ \ Bf ⊆ (B + H) \ B := by
    intro x hx
    have hxCZ : x ∈ CZ := (Finset.mem_sdiff.mp hx).1
    have hxnotBf : x ∉ Bf := (Finset.mem_sdiff.mp hx).2
    apply Finset.mem_sdiff.mpr
    constructor
    · apply Finset.add_subset_add (Finset.singleton_subset_iff.mpr hz)
          (fun _ hh ↦ hh)
        hxCZ
    · intro hxB
      exact hxnotBf (Finset.mem_inter.mpr ⟨hxB, hxCZ⟩)
  have hAsubSat : A ⊆ A + H := by
    intro x hx
    simpa using Finset.add_mem_add hx hzeroH
  have hBsubSat : B ⊆ B + H := by
    intro x hx
    simpa using Finset.add_mem_add hx hzeroH
  have hAgrowth : H.card - Af.card ≤ (A + H).card - A.card := by
    have hcard := Finset.card_le_card hCAminusSubset
    have hAinter : A ∩ (A + H) = A := Finset.inter_eq_left.mpr hAsubSat
    simpa [Finset.card_sdiff, CA, Af, Finset.card_singleton_add, hAinter] using hcard
  have hBgrowth : H.card - Bf.card ≤ (B + H).card - B.card := by
    have hcard := Finset.card_le_card hCZminusSubset
    have hBinter : B ∩ (B + H) = B := Finset.inter_eq_left.mpr hBsubSat
    simpa [Finset.card_sdiff, CZ, Bf, Finset.card_singleton_add, hBinter] using hcard
  have hAcard : A.card + ((A + H).card - A.card) = (A + H).card := by
    exact Nat.add_sub_of_le (Finset.card_le_card hAsubSat)
  have hBcard : B.card + ((B + H).card - B.card) = (B + H).card := by
    exact Nat.add_sub_of_le (Finset.card_le_card hBsubSat)
  have hHpos : 1 ≤ H.card := Finset.card_pos.mpr ⟨0, hzeroH⟩
  have hgrowth :
      H.card - 1 ≤
        ((A + H).card - A.card) + ((B + H).card - B.card) := by
    have hparts : H.card - 1 ≤ (H.card - Af.card) + (H.card - Bf.card) := by
      omega
    exact hparts.trans (Nat.add_le_add hAgrowth hBgrowth)
  have hk := Finset.add_kneser A B
  change (A + H).card + (B + H).card ≤ S.card + H.card at hk
  change A.card + B.card - 1 ≤ S.card
  omega

end GaoLean

#print axioms GaoLean.card_add_sub_one_le_of_add_ne_add_erase
