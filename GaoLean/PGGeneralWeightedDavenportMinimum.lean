import GaoLean.PGGeneralWeightedDavenport

/-!
# Existence of the exact general weighted Davenport constant

For every nonempty integer weight set and finite additive group, the least
weighted Davenport upper threshold exists.  Minimality supplies a labelled
zero-sum-free witness at every smaller length, exactly matching
`IsWeightedDavenportConstant`.
-/

namespace GaoLean

universe u

variable (W : Set ℤ) (A : Type u) [AddCommGroup A] [Finite A]

theorem exists_isWeightedDavenportConstant
    (hW : W.Nonempty) :
    ∃ D : ℕ, IsWeightedDavenportConstant W A D := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨Dordinary, hDordinary⟩ := exists_isOrdinaryDavenportConstant A
  have hexUpper : ∃ D : ℕ, WeightedDavenportAtMost W A D :=
    ⟨Dordinary,
      weightedDavenportAtMost_of_ordinary hW Dordinary hDordinary.1⟩
  let D := Nat.find hexUpper
  have hupper : WeightedDavenportAtMost W A D := Nat.find_spec hexUpper
  refine ⟨D, hupper, ?_⟩
  intro n hn
  have hnot : ¬WeightedDavenportAtMost W A n :=
    Nat.find_min hexUpper hn
  unfold WeightedDavenportAtMost at hnot
  simp only [not_forall] at hnot
  rcases hnot with ⟨xs, hlen, hfree⟩
  exact ⟨xs, hlen, hfree⟩

/-- The canonical least weighted Davenport threshold. -/
noncomputable def weightedDavenportValue (hW : W.Nonempty) : ℕ := by
  classical
  exact Nat.find (exists_isWeightedDavenportConstant W A hW)

theorem weightedDavenportValue_spec (hW : W.Nonempty) :
    IsWeightedDavenportConstant W A (weightedDavenportValue W A hW) := by
  classical
  exact Nat.find_spec (exists_isWeightedDavenportConstant W A hW)

/-- An exact weighted Davenport value is bounded by every certified upper
threshold. -/
theorem weightedDavenportConstant_le_of_atMost
    {Dexact D : ℕ}
    (hexact : IsWeightedDavenportConstant W A Dexact)
    (hupper : WeightedDavenportAtMost W A D) :
    Dexact ≤ D := by
  by_contra hnot
  have hlt : D < Dexact := Nat.lt_of_not_ge hnot
  rcases hexact.2 D hlt with ⟨xs, hlen, hfree⟩
  exact hfree (hupper xs hlen)

/-- Exact weighted Davenport values are unique. -/
theorem isWeightedDavenportConstant_unique
    {D₁ D₂ : ℕ}
    (h₁ : IsWeightedDavenportConstant W A D₁)
    (h₂ : IsWeightedDavenportConstant W A D₂) :
    D₁ = D₂ := by
  exact Nat.le_antisymm
    (weightedDavenportConstant_le_of_atMost W A h₁ h₂.1)
    (weightedDavenportConstant_le_of_atMost W A h₂ h₁.1)

/-- Canonical weighted Davenport values satisfy the subgroup--quotient
convolution inequality.  This packages the exact constants used by the
general weighted induction, so later cardinal arithmetic does not need to
carry three independent exactness witnesses. -/
theorem weightedDavenportValue_subgroup_quotient
    (hW : W.Nonempty) (K : AddSubgroup A) :
    weightedDavenportValue W K hW +
        weightedDavenportValue W (A ⧸ K) hW ≤
      weightedDavenportValue W A hW + 1 := by
  exact weightedDavenport_subgroup_quotient W K
    (weightedDavenportValue W A hW)
    (weightedDavenportValue W K hW)
    (weightedDavenportValue W (A ⧸ K) hW)
    (weightedDavenportValue_spec W A hW)
    (weightedDavenportValue_spec W K hW)
    (weightedDavenportValue_spec W (A ⧸ K) hW)

end GaoLean

#print axioms GaoLean.exists_isWeightedDavenportConstant
#print axioms GaoLean.weightedDavenportValue_spec
#print axioms GaoLean.weightedDavenportConstant_le_of_atMost
#print axioms GaoLean.isWeightedDavenportConstant_unique
#print axioms GaoLean.weightedDavenportValue_subgroup_quotient
