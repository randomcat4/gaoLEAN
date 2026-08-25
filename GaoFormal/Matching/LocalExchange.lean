import GaoFormal.Matching.CrossedReplacement

/-!
# Characteristic-not-two crossed exchange

This module composes the R1 determinant leaf with the version-controlled
delete-one/add-two constructor.  The four displayed quotient equalities are
the exact coordinate identities from the natural-language proof; deriving
them from the affine-coset setup is a separate statement-fidelity edge.
-/

namespace GaoFormal

open Set Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

theorem firstReplacement_independent
    {c d : V} (hcd : LinearIndependent F ![c, d]) {t s : F}
    (hdet : t - s + 1 ≠ 0) :
    LinearIndependent F ![-c + t • d, -c + (s - 1) • d] := by
  rw [LinearIndependent.pair_iff]
  intro a b hab
  have hcoeff : (-a - b) • c + (a * t + b * (s - 1)) • d = 0 := by
    calc
      (-a - b) • c + (a * t + b * (s - 1)) • d =
          a • (-c + t • d) + b • (-c + (s - 1) • d) := by module
      _ = 0 := hab
  have hz := (LinearIndependent.pair_iff.mp hcd) (-a - b)
    (a * t + b * (s - 1)) hcoeff
  have hb : b = -a := by
    linear_combination -hz.1
  have ha_mul : a * (t - s + 1) = 0 := by
    rw [hb] at hz
    linear_combination hz.2
  have ha : a = 0 := (mul_eq_zero.mp ha_mul).resolve_right hdet
  exact ⟨ha, by simpa [ha] using hb⟩

theorem oneReplacement_independent_of_two_ne_zero
    {c d : V} (hcd : LinearIndependent F ![c, d])
    (htwo : (2 : F) ≠ 0) (t s : F) :
    LinearIndependent F ![-c + t • d, -c + (s - 1) • d] ∨
      LinearIndependent F ![-c + s • d, -c + (t - 1) • d] := by
  by_cases hdet : t - s + 1 = 0
  · right
    apply firstReplacement_independent hcd
    intro hdet'
    apply htwo
    linear_combination hdet + hdet'
  · left
    exact firstReplacement_independent hcd hdet

namespace IndependentDifferenceMatching

variable {A : Finset V} {ι : Type*}

noncomputable instance remainingFintype [Fintype ι] (i : ι) :
    Fintype (Remaining i) := Fintype.ofFinite _

theorem card_crossedIndex [Fintype ι] (i : ι) :
    Fintype.card (CrossedIndex i) = Fintype.card ι + 1 := by
  classical
  have hone : Fintype.card {j : ι // j = i} = 1 := by
    rw [Fintype.card_eq_one_iff]
    exact ⟨⟨i, rfl⟩, fun y => Subtype.ext y.2⟩
  have hremaining : Fintype.card (Remaining i) = Fintype.card ι - 1 := by
    simpa [Remaining, hone] using
      (Fintype.card_subtype_compl (fun j : ι => j = i))
  change Fintype.card (Remaining i ⊕ Fin 2) = Fintype.card ι + 1
  rw [Fintype.card_sum, hremaining, Fintype.card_fin]
  have hpos : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i⟩
  omega

/-- Under the four quotient-coordinate identities in the source proof, one
of the two crossed replacements is a genuine independent-difference matching.
The result has all endpoint bookkeeping and quotient gluing discharged. -/
theorem oneOfTwoCrossedReplacements
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) {u v : V}
    (huA : u ∈ A) (hvA : v ∈ A)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v) (htwo : (2 : F) ≠ 0)
    {c d : V ⧸ deletedSpan M i} (hcd : LinearIndependent F ![c, d])
    (t s : F)
    (hfirst0 : Submodule.Quotient.mk (p := deletedSpan M i) (u - M.left i) =
      -c + t • d)
    (hfirst1 : Submodule.Quotient.mk (p := deletedSpan M i) (v - M.right i) =
      -c + (s - 1) • d)
    (hsecond0 : Submodule.Quotient.mk (p := deletedSpan M i) (v - M.left i) =
      -c + s • d)
    (hsecond1 : Submodule.Quotient.mk (p := deletedSpan M i) (u - M.right i) =
      -c + (t - 1) • d) :
    Nonempty (IndependentDifferenceMatching (F := F) A (CrossedIndex i)) := by
  rcases oneReplacement_independent_of_two_ne_zero hcd htwo t s with hfirst | hsecond
  · have hquot : LinearIndependent F
        (Submodule.Quotient.mk (p := deletedSpan M i) ∘
          (![u - M.left i, v - M.right i] : Fin 2 → V)) := by
      have heq :
          (Submodule.Quotient.mk (p := deletedSpan M i) ∘
            (![u - M.left i, v - M.right i] : Fin 2 → V)) =
            (![-c + t • d, -c + (s - 1) • d] : Fin 2 → (V ⧸ deletedSpan M i)) := by
        funext k
        fin_cases k
        · exact hfirst0
        · exact hfirst1
      rw [heq]
      exact hfirst
    exact ⟨crossedReplacementOfQuotient M i huA hvA hu hv huv hquot⟩
  · have hquot : LinearIndependent F
        (Submodule.Quotient.mk (p := deletedSpan M i) ∘
          (![v - M.left i, u - M.right i] : Fin 2 → V)) := by
      have heq :
          (Submodule.Quotient.mk (p := deletedSpan M i) ∘
            (![v - M.left i, u - M.right i] : Fin 2 → V)) =
            (![-c + s • d, -c + (t - 1) • d] : Fin 2 → (V ⧸ deletedSpan M i)) := by
        funext k
        fin_cases k
        · exact hsecond0
        · exact hsecond1
      rw [heq]
      exact hsecond
    exact ⟨crossedReplacementOfQuotient M i hvA huA hv hu huv.symm hquot⟩

/-- A maximum matching cannot satisfy the crossed-replacement coordinate
configuration at an edge outside the unmatched affine coset: either crossing
would create a matching with one additional edge. -/
theorem not_crossedCoordinateConfiguration_of_maximum
    {ι : Type u} [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (hmax : M.IsMaximum)
    (i : ι) {u v : V}
    (huA : u ∈ A) (hvA : v ∈ A)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v) (htwo : (2 : F) ≠ 0)
    {c d : V ⧸ deletedSpan M i} (hcd : LinearIndependent F ![c, d])
    (t s : F)
    (hfirst0 : Submodule.Quotient.mk (p := deletedSpan M i) (u - M.left i) =
      -c + t • d)
    (hfirst1 : Submodule.Quotient.mk (p := deletedSpan M i) (v - M.right i) =
      -c + (s - 1) • d)
    (hsecond0 : Submodule.Quotient.mk (p := deletedSpan M i) (v - M.left i) =
      -c + s • d)
    (hsecond1 : Submodule.Quotient.mk (p := deletedSpan M i) (u - M.right i) =
      -c + (t - 1) • d) : False := by
  rcases oneOfTwoCrossedReplacements M i huA hvA hu hv huv htwo hcd t s
    hfirst0 hfirst1 hsecond0 hsecond1 with ⟨N⟩
  have hcard := hmax (CrossedIndex i) N
  rw [card_crossedIndex i] at hcard
  omega

end IndependentDifferenceMatching

end GaoFormal
