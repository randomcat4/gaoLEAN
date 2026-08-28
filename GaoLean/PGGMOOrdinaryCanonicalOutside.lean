import GaoLean.PGGMOOrdinaryCanonicalStep1

/-!
# The literal outside ledger of a canonical Step 1 core

For a canonical Step 1 core, the container is the complete labelled source
fiber over one affine subgroup coset.  Its complement therefore consists
exactly of the genuine source occurrences outside that coset.  This module
records their centered quotient values, proves that all of them are nonzero,
and isolates the exact cardinal and finite `p`-group facts needed by a later
pair construction.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance ordinaryCanonicalOutsideQuotientFintype
    (H : AddSubgroup A) : Fintype (A ⧸ H) :=
  Fintype.ofFinite (A ⧸ H)

namespace CanonicalOrdinaryGMOStep1Core

/-- Literal occurrence complement of the complete canonical container. -/
noncomputable def outsideOccurrences
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs) : Selection xs :=
  Finset.univ \ C.container

/-- The centered quotient value of a genuine outside occurrence. -/
noncomputable def outsideQuotientValue
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (i : ↑C.outsideOccurrences) : A ⧸ C.H :=
  quotientDisplacement C.H C.beta (occurrenceValue xs i.1)

/-- The outside ledger has the exact complementary labelled cardinality. -/
theorem card_outsideOccurrences
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs) :
    C.outsideOccurrences.card = xs.length - C.container.card := by
  classical
  unfold outsideOccurrences
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ C.container)]
  simp

/-- No outside occurrence has zero centered quotient value.  Canonicality is
essential here: a zero value puts the occurrence in the complete affine
container, contradicting membership in its literal complement. -/
theorem outsideQuotientValue_ne_zero
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (i : ↑C.outsideOccurrences) :
    C.outsideQuotientValue i ≠ 0 := by
  intro hiZero
  have hiCoset : occurrenceValue xs i.1 ∈
      addCosetFinset C.H C.beta := by
    apply (quotientDisplacement_eq_zero_iff C.H C.beta
      (occurrenceValue xs i.1)).1
    exact hiZero
  have hiComplete : i.1 ∈ occurrencesInAddCoset xs C.H C.beta :=
    (mem_occurrencesInAddCoset_iff xs C.H C.beta i.1).2
      ((mem_addCosetFinset_iff C.H C.beta _).1 hiCoset)
  have hiContainer : i.1 ∈ C.container := by
    rw [C.container_eq]
    exact hiComplete
  exact (Finset.mem_sdiff.mp i.2).2 hiContainer

/-- Properness of the canonical subgroup makes its quotient nontrivial. -/
theorem nontrivial_outsideQuotient
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (hproper : C.H < ⊤) :
    Nontrivial (A ⧸ C.H) :=
  QuotientAddGroup.nontrivial_iff.mpr hproper.ne

/-- Below the source-coset threshold, the literal outside ledger contains at
least `|A/H| - 1` labels.  The proof explicitly rules out truncated
subtraction by deriving two labels in the canonical container from
properness and its ambient `d*` lower bound. -/
theorem quotientCard_sub_one_le_card_outsideOccurrences
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (hproper : C.H < ⊤)
    (hsmall : C.container.card <
      xs.length - Nat.card (A ⧸ C.H) + 2) :
    Nat.card (A ⧸ C.H) - 1 ≤ C.outsideOccurrences.card := by
  letI : Nontrivial (A ⧸ C.H) := C.nontrivial_outsideQuotient hproper
  letI : Nontrivial A :=
    (QuotientAddGroup.mk'_surjective C.H).nontrivial
  have hdApos : 1 ≤ pGroupDStar A := by
    have hgt := one_lt_ordinaryDavenportValue (B := A)
    have hrecover := pGroupDStar_add_one A
    omega
  have hHpos : 1 ≤ Nat.card C.H := Nat.card_pos
  have hcontainerTwo : 2 ≤ C.container.card := by
    have hlower := C.container_card_lower
    omega
  have hcard := C.card_outsideOccurrences
  omega

/-- Quotienting an ambient finite additive `p`-group by the canonical
subgroup preserves the `p`-group structure. -/
theorem isPGroup_outsideQuotient
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (p : ℕ) (hA : IsPGroup p (Multiplicative A)) :
    IsPGroup p (Multiplicative (A ⧸ C.H)) :=
  isPGroup_multiplicative_quotient p hA C.H

/-- Honest algebraic and labelled input extracted from a proper canonical
core below the source-coset threshold.  It contains only the outside ledger
facts and quotient-group structure. -/
structure OutsideInput
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs) (p : ℕ) : Prop where
  card_eq :
    C.outsideOccurrences.card = xs.length - C.container.card
  value_ne_zero :
    ∀ i : ↑C.outsideOccurrences, C.outsideQuotientValue i ≠ 0
  card_lower :
    Nat.card (A ⧸ C.H) - 1 ≤ C.outsideOccurrences.card
  quotientPGroup :
    IsPGroup p (Multiplicative (A ⧸ C.H))
  quotientNontrivial :
    Nontrivial (A ⧸ C.H)

/-- Assemble the literal outside input without storing any later extension
or structural result. -/
theorem outsideInput
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (p : ℕ) (hA : IsPGroup p (Multiplicative A))
    (hproper : C.H < ⊤)
    (hsmall : C.container.card <
      xs.length - Nat.card (A ⧸ C.H) + 2) :
    C.OutsideInput p where
  card_eq := C.card_outsideOccurrences
  value_ne_zero := C.outsideQuotientValue_ne_zero
  card_lower := C.quotientCard_sub_one_le_card_outsideOccurrences
    hproper hsmall
  quotientPGroup := C.isPGroup_outsideQuotient p hA
  quotientNontrivial := C.nontrivial_outsideQuotient hproper

end CanonicalOrdinaryGMOStep1Core

end GaoLean

#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.card_outsideOccurrences
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.outsideQuotientValue_ne_zero
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.nontrivial_outsideQuotient
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.quotientCard_sub_one_le_card_outsideOccurrences
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.isPGroup_outsideQuotient
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.outsideInput
