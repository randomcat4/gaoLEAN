import GaoLean.GAOARFinal

/-!
# Homocyclic numerical specialization

This file packages Corollary 6.1 of the frozen 13-page manuscript.  Its
ordinary Davenport value and kernel cardinality are unconditional; the Gao
equality uses exactly the final visible GMO input package.
-/

namespace GaoLean

/-- The additive kernel `C_(p^k)^r`. -/
abbrev HomocyclicKernel (p k r : ℕ) := Fin r → ZMod (p ^ k)

/-- The displayed Olson value for `C_(p^k)^r`. -/
def homocyclicDavenportValue (p k r : ℕ) : ℕ :=
  1 + r * (p ^ k - 1)

theorem natCard_homocyclicKernel (p k r : ℕ) (hp : p.Prime) :
    Nat.card (HomocyclicKernel p k r) = p ^ (k * r) := by
  classical
  letI : NeZero p := ⟨hp.ne_zero⟩
  rw [Nat.card_pi]
  simp [← pow_mul]

/-- Olson's formula in the literal homocyclic display form used in
Corollary 6.1. -/
theorem isOrdinaryDavenportConstant_homocyclicKernel
    (p k r : ℕ) (hp : p.Prime) :
    IsOrdinaryDavenportConstant (HomocyclicKernel p k r)
      (homocyclicDavenportValue p k r) := by
  let μ : Fin r → ℕ := fun _ ↦ k
  let e : HomocyclicKernel p k r ≃+
      ((i : Fin r) → ZMod (p ^ μ i)) := AddEquiv.refl _
  have h := isOrdinaryDavenportConstant_invariantProduct p hp μ e
  simpa [homocyclicDavenportValue, μ, e,
    pGroupGeneratorDegree_invariantProductGeneratorData] using h

theorem isPGroup_homocyclicKernel
    (p k r : ℕ) (hp : p.Prime) :
    IsPGroup p (Multiplicative (HomocyclicKernel p k r)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  apply IsPGroup.of_card
  rw [Nat.card_congr Multiplicative.toAdd]
  exact natCard_homocyclicKernel p k r hp

namespace ConcreteGDihedral

/-- Corollary 6.1 in the project's exact-threshold semantics.  The sole
premise is the same visible GMO package as the general 13-page theorem. -/
theorem pgGao_homocyclic_of_structuralRemainingInputs
    (hremaining : PGGaoStructuralRemainingInputs.{0})
    (p k r : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    [Nontrivial (HomocyclicKernel p k r)] :
    letI : NeZero p := ⟨hp.ne_zero⟩
    PGGaoV1 (HomocyclicKernel p k r)
      (homocyclicDavenportValue p k r) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  let A := HomocyclicKernel p k r
  let D := homocyclicDavenportValue p k r
  have hD : IsOrdinaryDavenportConstant A D :=
    isOrdinaryDavenportConstant_homocyclicKernel p k r hp
  have hsource : PGGaoStructuralUpperInputs A D :=
    hremaining p A hp hpTwo (isPGroup_homocyclicKernel p k r hp) D hD
  exact pgGaoV1_of_structuralUpperInputs_and_ordinaryDavenport
    p D hp hpTwo (isPGroup_homocyclicKernel p k r hp)
      (odd_natCard_of_odd_prime_pgroup p A hp hpTwo
        (isPGroup_homocyclicKernel p k r hp)) hsource hD

/-- The exact numerical threshold displayed in Corollary 6.1. -/
theorem pgGao_homocyclic_display_of_structuralRemainingInputs
    (hremaining : PGGaoStructuralRemainingInputs.{0})
    (p k r : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    [Nontrivial (HomocyclicKernel p k r)] :
    letI : NeZero p := ⟨hp.ne_zero⟩
    IsExactProductOneThreshold
      (Group (HomocyclicKernel p k r))
      (2 * p ^ (k * r) + r * (p ^ k - 1) + 1)
      (2 * p ^ (k * r)) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  have h := pgGao_homocyclic_of_structuralRemainingInputs
    hremaining p k r hp hpTwo
  simpa [PGGaoV1, homocyclicDavenportValue,
    Nat.card_eq_fintype_card, natCard_homocyclicKernel p k r hp,
    ← pow_mul, Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using h

/-- Elementary-abelian specialization `k=1`. -/
theorem pgGao_elementaryAbelian_display_of_structuralRemainingInputs
    (hremaining : PGGaoStructuralRemainingInputs.{0})
    (p r : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    [Nontrivial (HomocyclicKernel p 1 r)] :
    letI : NeZero p := ⟨hp.ne_zero⟩
    IsExactProductOneThreshold
      (Group (HomocyclicKernel p 1 r))
      (2 * p ^ r + r * (p - 1) + 1)
      (2 * p ^ r) := by
  letI : NeZero p := ⟨hp.ne_zero⟩
  simpa using pgGao_homocyclic_display_of_structuralRemainingInputs
    hremaining p 1 r hp hpTwo

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.isOrdinaryDavenportConstant_homocyclicKernel
#print axioms GaoLean.ConcreteGDihedral.pgGao_homocyclic_display_of_structuralRemainingInputs
#print axioms GaoLean.ConcreteGDihedral.pgGao_elementaryAbelian_display_of_structuralRemainingInputs
