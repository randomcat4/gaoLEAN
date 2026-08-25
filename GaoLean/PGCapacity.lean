import GaoLean.PGTranslation

/-!
# Residual-controller capacity arithmetic

This file isolates the finite-cardinality composition in A-R6 equations
(5.10)--(5.11).  It does not assert the GMO concentration alternative; it
only consumes the two occurrence lower bounds which that branch must supply.
-/

namespace GaoLean

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- For `H ≤ K ≤ A`, the ambient quotient factors into the quotient by `K`
and the internal quotient `K/H`. -/
theorem natCard_quotient_eq_mul_quotient_subgroupOf
    (H K : AddSubgroup A) (hHK : H ≤ K) :
    Nat.card (A ⧸ H) =
      Nat.card (A ⧸ K) * Nat.card (K ⧸ H.addSubgroupOf K) := by
  rw [← Nat.card_prod]
  exact Nat.card_congr (AddSubgroup.quotientEquivProdOfLE hHK)

/-- A proper subgroup gives a quotient with at least two elements. -/
theorem two_le_natCard_quotient_of_lt_top
    (K : AddSubgroup A) (hK : K < ⊤) :
    2 ≤ Nat.card (A ⧸ K) := by
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
  have hlt : Nat.card K < Nat.card A :=
    by simpa using natCard_lt_of_addSubgroup_lt hK
  have hpos : 0 < Nat.card (A ⧸ K) := Nat.card_pos
  by_contra hnot
  have hone : Nat.card (A ⧸ K) = 1 := by omega
  rw [hone, one_mul] at hcard
  omega

/-- A strict inclusion `H<K` gives an internal quotient `K/H` with at least
two elements. -/
theorem two_le_natCard_internal_quotient_of_lt
    (H K : AddSubgroup A) (hHK : H < K) :
    2 ≤ Nat.card (K ⧸ H.addSubgroupOf K) := by
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup
    (H.addSubgroupOf K)
  have hinsCard : Nat.card (H.addSubgroupOf K) = Nat.card H :=
    Nat.card_congr (AddSubgroup.addSubgroupOfEquivOfLe hHK.le)
  rw [hinsCard] at hcard
  have hlt : Nat.card H < Nat.card K :=
    natCard_lt_of_addSubgroup_lt hHK
  have hpos : 0 < Nat.card (K ⧸ H.addSubgroupOf K) := Nat.card_pos
  by_contra hnot
  have hone : Nat.card (K ⧸ H.addSubgroupOf K) = 1 := by omega
  rw [hone, one_mul] at hcard
  omega

/-- The elementary strict-quotient inequality used in (5.11). -/
theorem quotient_factor_sum_le_product_add_two
    (I J : ℕ) (hI : 2 ≤ I) (hJ : 2 ≤ J) :
    I + J ≤ I * J + 2 := by
  obtain ⟨i, rfl⟩ := Nat.le.dest hI
  obtain ⟨j, rfl⟩ := Nat.le.dest hJ
  nlinarith [Nat.zero_le (i * j)]

/-- Exact natural-number form of the capacity composition in (5.10).  The
subtractions are truncated, so this statement also checks all small-`b`
boundary cases rather than silently coercing to integers. -/
theorem residual_capacity_composition
    (b I J M MH : ℕ)
    (hI : 2 ≤ I) (hJ : 2 ≤ J)
    (hM : b - I + 2 ≤ M)
    (hMH : M - J + 2 ≤ MH) :
    b - I * J + 2 ≤ MH := by
  have hIJ := quotient_factor_sum_le_product_add_two I J hI hJ
  omega

/-- Version with the ambient quotient cardinal written explicitly. -/
theorem residual_capacity_composition_of_quotient_card
    (H K : AddSubgroup A) (hHK : H ≤ K)
    (b M MH : ℕ)
    (hI : 2 ≤ Nat.card (A ⧸ K))
    (hJ : 2 ≤ Nat.card (K ⧸ H.addSubgroupOf K))
    (hM : b - Nat.card (A ⧸ K) + 2 ≤ M)
    (hMH : M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ MH) :
    b - Nat.card (A ⧸ H) + 2 ≤ MH := by
  rw [natCard_quotient_eq_mul_quotient_subgroupOf H K hHK]
  exact residual_capacity_composition b _ _ M MH hI hJ hM hMH

/-- Source-facing form of (5.10)--(5.11): strictness supplies both quotient
factors' lower bounds automatically. -/
theorem residual_capacity_composition_of_strict
    (H K : AddSubgroup A) (hHK : H < K) (hKtop : K < ⊤)
    (b M MH : ℕ)
    (hM : b - Nat.card (A ⧸ K) + 2 ≤ M)
    (hMH : M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ MH) :
    b - Nat.card (A ⧸ H) + 2 ≤ MH := by
  exact residual_capacity_composition_of_quotient_card H K hHK.le b M MH
    (two_le_natCard_quotient_of_lt_top K hKtop)
    (two_le_natCard_internal_quotient_of_lt H K hHK) hM hMH

namespace ConcreteGDihedral

/-- Combine the labelled affine-coset inclusion with (5.10)--(5.11) to
produce exactly the translated capacity premise required by `ZR_A(-,H)`. -/
theorem translatedCapacity_of_strict_concentration
    (α : A) (s : List (Group A))
    (H K : AddSubgroup A) (hHK : H < K) (hKtop : K < ⊤)
    (b M : ℕ) (C : Selection s)
    (hC : ∀ i ∈ C,
      IsRotation (occurrenceValue s i) ∧
        coordinate (occurrenceValue s i) - α ∈ H)
    (hM : b - Nat.card (A ⧸ K) + 2 ≤ M)
    (hCcard : M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ C.card) :
    b - Nat.card (A ⧸ H) + 2 ≤
      (rotationOccurrencesIn (translatedSequence α s) H).card := by
  exact (residual_capacity_composition_of_strict H K hHK hKtop b M C.card
    hM hCcard).trans
      (card_le_rotationOccurrencesIn_translatedSequence α s H C hC)

/-- Source-facing non-full rotation-channel closure.  Once GMO supplies a
strict `H`, translation center `α`, and a sufficiently large labelled set in
`α+H`, the smaller `ZR` theorem yields the required exact block in the
original sequence. -/
theorem hasAllRotationProductOneSubsequence_of_concentration_and_smallerZR
    (α : A) (s : List (Group A)) (Q D a b M : ℕ)
    (H K : AddSubgroup A) (hHK : H < K) (hKtop : K < ⊤)
    (C : Selection s)
    (hC : ∀ i ∈ C,
      IsRotation (occurrenceValue s i) ∧
        coordinate (occurrenceValue s i) - α ∈ H)
    (hM : b - Nat.card (A ⧸ K) + 2 ≤ M)
    (hCcard : M - Nat.card (K ⧸ H.addSubgroupOf K) + 2 ≤ C.card)
    (hZR : ConcreteZRStatement (translatedSequence α s) Q D a b H)
    (hlen : s.length = 2 * Q + D)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hα : α ∈ K) (hguard : QuotientNoReflection s K)
    (hQ : Q = Nat.card A) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  apply hasAllRotationProductOneSubsequence_of_concreteZR_translatedSequence
    α s Q D a b H K hZR hlen href hrot
  · exact translatedCapacity_of_strict_concentration α s H K hHK hKtop
      b M C hC hM hCcard
  · exact hHK.le
  · exact hα
  · exact hguard
  · exact hQ

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.natCard_quotient_eq_mul_quotient_subgroupOf
#print axioms GaoLean.two_le_natCard_quotient_of_lt_top
#print axioms GaoLean.two_le_natCard_internal_quotient_of_lt
#print axioms GaoLean.quotient_factor_sum_le_product_add_two
#print axioms GaoLean.residual_capacity_composition
#print axioms GaoLean.residual_capacity_composition_of_quotient_card
#print axioms GaoLean.residual_capacity_composition_of_strict
#print axioms GaoLean.ConcreteGDihedral.translatedCapacity_of_strict_concentration
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_concentration_and_smallerZR
