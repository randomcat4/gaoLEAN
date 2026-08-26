import GaoLean.GAOARRankThreeLine

/-!
# Rank-three subgroup classification and ordinary inside-subgroup leaf
-/

namespace GaoLean

/-- A nonzero proper additive subgroup of `F_q^3` has dimension one or two,
hence cardinality `q` or `q²`. -/
theorem natCard_eq_prime_or_square_of_ne_bot_of_lt_top_rankThree
    (q : ℕ) [NeZero q] (hq : Nat.Prime q)
    (K : AddSubgroup (PrimeVectorSpace q 3))
    (hKbot : K ≠ ⊥) (hKtop : K < ⊤) :
    Nat.card K = q ∨ Nat.card K = q ^ 2 := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let L : Submodule (ZMod q) (PrimeVectorSpace q 3) :=
    AddSubgroup.toZModSubmodule q K
  have hLbot : L ≠ ⊥ := by
    intro h
    apply hKbot
    exact (AddSubgroup.toZModSubmodule q).injective (by simpa [L] using h)
  have hLtop : L ≠ ⊤ := by
    intro h
    apply hKtop.ne
    exact (AddSubgroup.toZModSubmodule q).injective (by simpa [L] using h)
  have hpos : 0 < Module.finrank (ZMod q) L := by
    have h := Submodule.finrank_lt_finrank_of_lt
      (bot_lt_iff_ne_bot.mpr hLbot)
    simpa using h
  have hlt : Module.finrank (ZMod q) L < 3 := by
    have h := Submodule.finrank_lt hLtop
    simpa [L, PrimeVectorSpace] using h
  have hdim : Module.finrank (ZMod q) L = 1 ∨
      Module.finrank (ZMod q) L = 2 := by omega
  have hcard : Nat.card K = q ^ Module.finrank (ZMod q) L := by
    calc
      Nat.card K = Nat.card L := by
        exact Nat.card_congr
          { toFun := fun x => ⟨x.1, x.2⟩
            invFun := fun x => ⟨x.1, x.2⟩
            left_inv := fun _ => rfl
            right_inv := fun _ => rfl }
      _ = Nat.card (ZMod q) ^ Module.finrank (ZMod q) L :=
        Module.natCard_eq_pow_finrank
      _ = q ^ Module.finrank (ZMod q) L := by simp
  rcases hdim with hdim | hdim
  · left
    simpa [hdim] using hcard
  · right
    simpa [hdim] using hcard

/-- Mapping a subgroup of the subtype `K` back into the ambient group does
not change its cardinality. -/
theorem natCard_map_subtype
    {A : Type*} [AddCommGroup A]
    (K : AddSubgroup A) (H : AddSubgroup K) :
    Nat.card (H.map K.subtype) = Nat.card H := by
  exact (Nat.card_congr
    (H.equivMapOfInjective K.subtype K.subtype_injective)).symm

/-- A proper subgroup of `K`, viewed in the ambient group, is still strictly
below `K`. -/
theorem map_subtype_lt_of_lt_top
    {A : Type*} [AddCommGroup A] [Fintype A]
    (K : AddSubgroup A) [Fintype K]
    (H : AddSubgroup K) (hH : H < ⊤) :
    H.map K.subtype < K := by
  have hle : H.map K.subtype ≤ K := AddSubgroup.map_subtype_le H
  have hcardlt : Nat.card (H.map K.subtype) < Nat.card K := by
    rw [natCard_map_subtype K H]
    simpa using natCard_lt_of_addSubgroup_lt hH
  exact lt_of_le_of_ne hle (by
    intro heq
    rw [heq] at hcardlt
    omega)

/-- A nonzero proper subgroup of a cardinality-`q²` plane inside `F_q³`
has cardinality `q`.  No basis of the plane is chosen. -/
theorem natCard_eq_prime_of_ne_bot_of_lt_top_of_square_subgroup_rankThree
    (q : ℕ) [NeZero q] (hq : Nat.Prime q)
    (K : AddSubgroup (PrimeVectorSpace q 3)) [Fintype K]
    (hKcard : Nat.card K = q ^ 2)
    (H : AddSubgroup K) (hHbot : H ≠ ⊥) (hHtop : H < ⊤) :
    Nat.card H = q := by
  let H' : AddSubgroup (PrimeVectorSpace q 3) := H.map K.subtype
  have hH'ne : H' ≠ ⊥ := by
    intro h
    apply hHbot
    apply (AddSubgroup.map_injective K.subtype_injective)
    simpa [H'] using h
  have hH'ltK : H' < K := by
    simpa [H'] using map_subtype_lt_of_lt_top K H hHtop
  have hH'top : H' < ⊤ := hH'ltK.trans_le le_top
  rcases natCard_eq_prime_or_square_of_ne_bot_of_lt_top_rankThree
      q hq H' hH'ne hH'top with hqcard | hq2card
  · dsimp only [H'] at hqcard
    rw [natCard_map_subtype K H] at hqcard
    exact hqcard
  · have hlt := natCard_lt_of_addSubgroup_lt hH'ltK
    rw [hKcard, hq2card] at hlt
    omega

namespace ConcreteGDihedral

/-- A direct ordinary prescribed-length GMO call on the rotations lying in a
subgroup, transported back to the original occurrence labels. -/
theorem hasProductOneSubsequence_of_insideOrdinaryGMO
    {A : Type*} [AddCommGroup A] [Fintype A]
    (K : AddSubgroup A) [Fintype K]
    (Q DK : ℕ) (hQ : Q = Nat.card A)
    (hKtarget : Nat.card K ≤ 2 * Q)
    (hordinary : OrdinaryGMOPrescribedLengthProvider K DK)
    (s : List (Group A))
    (hthreshold : 2 * Q + DK - 1 ≤
      (rotationOccurrencesIn s K).card) :
    HasProductOneSubsequenceOfCard s (2 * Q) := by
  have hlength : (rotationInCoordinateSequence s K).length =
      (rotationOccurrencesIn s K).card := by
    simp [rotationInCoordinateSequence]
  obtain ⟨hout⟩ := hordinary (rotationInCoordinateSequence s K) (2 * Q)
    hKtarget (by simpa [hlength] using hthreshold)
  have htarget :=
    LowReflectionTargetOutput.ofLineOrdinaryGMOTargetOutput (Q := Q) hout
  exact hasProductOneSubsequenceOfTwice_of_lowReflectionTargetOutput
    s Q hQ htarget

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.natCard_eq_prime_or_square_of_ne_bot_of_lt_top_rankThree
#print axioms GaoLean.natCard_map_subtype
#print axioms GaoLean.map_subtype_lt_of_lt_top
#print axioms GaoLean.natCard_eq_prime_of_ne_bot_of_lt_top_of_square_subgroup_rankThree
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequence_of_insideOrdinaryGMO
