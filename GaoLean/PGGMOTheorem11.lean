import GaoLean.PGGMOPlusMinusSource
import GaoLean.PGGMOTheorem21
import GaoLean.PGDGMStructuralGap
import GaoLean.PGDavenportBridge
import GaoLean.PGInduction
import GaoLean.GAOARDihedralBlocks

/-!
# Theorem 1.1 induction boundary for the `{+1,-1}` GMO specialization

This file separates three logically different layers of the published proof.

1. `GMOTheorem21Output` from `PGGMOTheorem21` records the literal
   occurrence/setpartition output of Theorem 2.1.  This file deliberately
   reuses that unique frozen ordinary interface rather than redeclaring it.
2. `PlusMinusTheorem11InductionEngine` is the remaining *local* signed
   Theorem 1.1 proof.  At a subgroup it may use only source packages already
   proved for strict subgroups together with DGM at that subgroup.  Ordinary
   Theorem 2.1 is intentionally absent from this main path.
3. The theorems below prove the finite strict-subgroup induction, the trivial
   base case, the conversion of whole signed blocks into both weight-coset
   fields, and the final ambient/all-subgroup provider assembly.

The imported `ZMod 5` regression certificate remains a guard against an invalid
shortcut: membership of one quotient value in `{x,-x}` does not imply that the
whole block lies in one coset.  Accordingly, the concentration certificate here
requires a subset statement for every element of the signed block.
-/

namespace GaoLean

open scoped BigOperators Pointwise

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Canonical finite instances for subgroup carrier types used throughout the
strict-subgroup scheduler. -/
noncomputable local instance subgroupFintype (K : AddSubgroup A) : Fintype K :=
  Fintype.ofFinite K

noncomputable local instance quotientFintype (K : AddSubgroup A) :
    Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)

/-! ## Exact Theorem 2.1 large branch -/

/-- The canonical Theorem 2.1 setpartition sumset embeds into the ambient
exact `{+1,-1}` spectrum by assigning the positive sign to the labelled
occurrences supplied by its ordinary-spectrum embedding. -/
theorem theorem21SetPartition_sumset_subset_plusMinusExactSpectrum
    (xs : List A) (n m : ℕ) (P : Theorem21SetPartition xs n m) :
    P.sumset ⊆ plusMinusExactSpectrum xs n := by
  classical
  intro y hy
  have hyOrd : y ∈ ordinaryExactSpectrum xs n :=
    P.sumset_subset_ordinaryExactSpectrum hy
  obtain ⟨I, hIcard, hIsum⟩ :=
    (mem_ordinaryExactSpectrum_iff xs n y).1 hyOrd
  apply (mem_plusMinusExactSpectrum_iff xs n y).2
  exact ⟨{
    positive := I
    negative := ∅
    disjoint := by simp
    card_selected := by simpa using hIcard
    weighted_sum := by simpa using hIsum
  }⟩

/-- A concrete automatically-closing branch of the local Theorem 1.1 proof.
Theorem 2.1 supplies a large cell sumset, and the available room makes its
lower bound reach `|A|`. -/
structure PlusMinusTheorem21FullCertificate
    (xs : List A) (n : ℕ) where
  seed : Selection xs
  output : GMOTheorem21Output xs seed n
  room : Nat.card A ≤ seed.card - n + 1
  largeBranch :
    GMOTheorem21LargeAlternative xs seed n output.partition

/-- The large Theorem 2.1 branch is genuinely sufficient to make the ambient
exact signed spectrum full; this part is no longer delegated to the induction
engine. -/
theorem PlusMinusTheorem21FullCertificate.fullSpectrum
    {xs : List A} {n : ℕ} (h : PlusMinusTheorem21FullCertificate xs n) :
    plusMinusExactSpectrum xs n = Finset.univ := by
  classical
  have hsumcard : Nat.card A ≤
      h.output.partition.sumset.card := by
    have hmin : min (Nat.card A) (h.seed.card - n + 1) = Nat.card A :=
      min_eq_left h.room
    have hlarge := h.largeBranch.card_lower
    rw [hmin] at hlarge
    exact hlarge
  have hsubset : h.output.partition.sumset ⊆
      plusMinusExactSpectrum xs n :=
    theorem21SetPartition_sumset_subset_plusMinusExactSpectrum
      xs n h.seed.card h.output.partition
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  have hspectrumCard : Nat.card A ≤ (plusMinusExactSpectrum xs n).card :=
    hsumcard.trans (Finset.card_le_card hsubset)
  simpa [Nat.card_eq_fintype_card] using hspectrumCard

/-- Corollary 1.2's target follows immediately on the automatically-closing
large branch. -/
theorem PlusMinusTheorem21FullCertificate.corollary12At
    {xs : List A} {n : ℕ} (h : PlusMinusTheorem21FullCertificate xs n) :
    PlusMinusGMOCorollary12At xs n := by
  refine ⟨0, ?_⟩
  apply (mem_plusMinusExactSpectrum_iff xs n (n • (0 : A))).1
  rw [h.fullSpectrum]
  simp

/-- A deliberately conditional numerical helper for the full branch.  The
GMO source-length hypothesis `n + d - 1 ≤ |S|` yields the required width for
the full source seed only when the additional comparison `|A| ≤ d` is
available.  No later theorem assumes that this comparison follows from the
plus-minus Davenport bound. -/
theorem theorem21FullRoom_of_sourceLength
    (xs : List A) (n d : ℕ)
    (hcard : Nat.card A ≤ d)
    (hlen : n + d - 1 ≤ xs.length) :
    Nat.card A ≤ (Finset.univ : Selection xs).card - n + 1 := by
  classical
  simp only [Finset.card_univ, Fintype.card_fin]
  have hpos : 0 < Nat.card A := Nat.card_pos
  omega

/-! The preceding Theorem 2.1 material is an optional conditional route.  It
is not an input of the signed induction below: the paper uses Theorem 2.1 only
in Step 2, where the weight support has cardinality one. -/

/-- DGM with the finite type's canonical classical equality decision hidden
inside a proposition wrapper. -/
noncomputable def FiniteDGMSetpartitionInput
    (A : Type*) [AddCommGroup A] [Fintype A] : Prop := by
  classical
  exact GeneralDGMSetpartitionTheorem A

/-! ## The whole-block coset boundary -/

/-- Structural evidence strong enough for Corollary 1.3: the *entire* signed
block of every selected occurrence is contained in one weight coset.  Since
`+1` is one of the weights, this same condition also supplies the source coset
with `alpha = beta`; no separate source-coset premise is needed in the
`{+1,-1}` specialization.  Whole-block containment remains intentionally
stronger than membership of one element of the block. -/
structure PlusMinusPairedCosetCertificate (xs : List A) where
  K : AddSubgroup A
  strict : K < ⊤
  beta : A
  selected : Selection xs
  signedBlockCoset : ∀ i ∈ selected,
    ∀ y ∈ plusMinusOccurrenceBlock xs i, y - beta ∈ K
  card_lower :
    xs.length - Nat.card (A ⧸ K) + 2 ≤ selected.card

/-- Whole-block containment gives the positive weight-coset field. -/
theorem PlusMinusPairedCosetCertificate.positiveWeightCoset
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs)
    (i : Occurrence xs) (hi : i ∈ h.selected) :
    occurrenceValue xs i - h.beta ∈ h.K := by
  apply h.signedBlockCoset i hi
  simp [plusMinusOccurrenceBlock, plusMinusValueBlock]

/-- Whole-block containment gives the negative weight-coset field separately;
it is not inferred from the positive membership. -/
theorem PlusMinusPairedCosetCertificate.negativeWeightCoset
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs)
    (i : Occurrence xs) (hi : i ∈ h.selected) :
    -occurrenceValue xs i - h.beta ∈ h.K := by
  apply h.signedBlockCoset i hi
  simp [plusMinusOccurrenceBlock, plusMinusValueBlock]

/-- Convert paired-layer structural evidence to the exact occurrence-labelled
concentration record used by the manuscript. -/
theorem PlusMinusPairedCosetCertificate.toGMOConcentration
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs) :
    Nonempty (PlusMinusGMOConcentration xs) := by
  exact ⟨{
    K := h.K
    strict := h.strict
    alpha := h.beta
    beta := h.beta
    selected := h.selected
    sourceCoset := h.positiveWeightCoset
    positiveWeightCoset := h.positiveWeightCoset
    negativeWeightCoset := h.negativeWeightCoset
    card_lower := h.card_lower
  }⟩

/-- Regression certificate for the forbidden one-sign shortcut. -/
theorem theorem11_singleLayer_membership_is_not_paired_containment :
    ∃ x q : ZMod 5,
      q ∈ plusMinusValueBlock x ∧
        ¬plusMinusValueBlock x ⊆ ({q} : Finset (ZMod 5)) :=
  zmod5_signedLayer_member_not_subset_singleton

/-! ## Local endpoints and the trivial base -/

/-- The two local endpoints which the substantive signed Theorem 1.1 step must
produce after using DGM, Davenport, and strict-subgroup induction.
The non-full endpoint returns whole-block coset evidence rather than directly
returning the manuscript concentration record. -/
structure PlusMinusTheorem11StepEndpoints
    (A : Type*) [AddCommGroup A] [Fintype A] where
  target :
    ∀ (xs : List A) (n d : ℕ),
      Nat.card A ≤ n →
      PlusMinusDavenportAtMost A d →
      n + d - 1 ≤ xs.length →
      PlusMinusGMOCorollary12At xs n
  nonfull :
    ∀ (xs : List A) (n d : ℕ),
      Nat.card A ≤ n →
      PlusMinusDavenportAtMost A d →
      n + d - 1 ≤ xs.length →
      plusMinusExactSpectrum xs n ≠ Finset.univ →
      Nonempty (PlusMinusPairedCosetCertificate xs)

/-! ## Step 4: split on the stabilizer of the signed exact spectrum -/

/-- Step 4's `L = G` branch.  A nonempty exact signed spectrum whose additive
stabilizer is the whole ambient group is the whole group.  Nonemptiness uses
an exact `n`-occurrence selection and therefore keeps the paper's labelled
semantics. -/
theorem plusMinusExactSpectrum_eq_univ_of_stabilizer_eq_top
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length)
    (htop : plusMinusSpectrumStabilizer xs n = ⊤) :
    plusMinusExactSpectrum xs n = Finset.univ := by
  classical
  by_contra hne
  have hstrict : plusMinusSpectrumStabilizer xs n < ⊤ := by
    apply stabilizer_lt_top_of_finset_nonempty_ne_univ
      (plusMinusExactSpectrum xs n)
      (plusMinusExactSpectrum_nonempty xs n hn)
      hne
  exact (ne_of_lt hstrict) htop

/-- Exact labelled transport of signed spectra through an additive
homomorphism.  Both directions move the positive and negative occurrence sets
through the canonical equivalence of list positions; hence repetitions,
disjointness and exact cardinality are all preserved. -/
theorem image_plusMinusExactSpectrum_addMonoidHom
    {B : Type*} [AddCommGroup B] [Fintype B] [DecidableEq B]
    (f : A →+ B) (xs : List A) (n : ℕ) :
    (plusMinusExactSpectrum xs n).image f =
      plusMinusExactSpectrum (xs.map f) n := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨h⟩ := (mem_plusMinusExactSpectrum_iff xs n z).1 hz
    let e := ConcreteGDihedral.mapOccurrenceEquiv f xs
    let positive : Selection (xs.map f) := h.positive.map e.toEmbedding
    let negative : Selection (xs.map f) := h.negative.map e.toEmbedding
    have hpositive :
        (∑ i ∈ positive, occurrenceValue (xs.map f) i) =
          ∑ i ∈ h.positive, f (occurrenceValue xs i) := by
      simp only [positive, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i hi
      exact ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f xs i
    have hnegative :
        (∑ i ∈ negative, occurrenceValue (xs.map f) i) =
          ∑ i ∈ h.negative, f (occurrenceValue xs i) := by
      simp only [negative, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i hi
      exact ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f xs i
    apply (mem_plusMinusExactSpectrum_iff (xs.map f) n (f z)).2
    exact ⟨{
      positive := positive
      negative := negative
      disjoint := by
        simpa [positive, negative] using h.disjoint
      card_selected := by
        simpa [positive, negative] using h.card_selected
      weighted_sum := by
        rw [hpositive, hnegative, ← map_sum, ← map_sum,
          ← map_sub, h.weighted_sum]
    }⟩
  · intro hy
    obtain ⟨h⟩ :=
      (mem_plusMinusExactSpectrum_iff (xs.map f) n y).1 hy
    let e := ConcreteGDihedral.mapOccurrenceEquiv f xs
    let positive : Selection xs := h.positive.map e.symm.toEmbedding
    let negative : Selection xs := h.negative.map e.symm.toEmbedding
    let z : A :=
      (∑ i ∈ positive, occurrenceValue xs i) -
        ∑ i ∈ negative, occurrenceValue xs i
    have hpositive :
        (∑ i ∈ positive, f (occurrenceValue xs i)) =
          ∑ i ∈ h.positive, occurrenceValue (xs.map f) i := by
      simp only [positive, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i hi
      exact ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm f xs i
    have hnegative :
        (∑ i ∈ negative, f (occurrenceValue xs i)) =
          ∑ i ∈ h.negative, occurrenceValue (xs.map f) i := by
      simp only [negative, Finset.sum_map]
      apply Finset.sum_congr rfl
      intro i hi
      exact ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm f xs i
    have hz : z ∈ plusMinusExactSpectrum xs n := by
      apply (mem_plusMinusExactSpectrum_iff xs n z).2
      exact ⟨{
        positive := positive
        negative := negative
        disjoint := by
          simpa [positive, negative] using h.disjoint
        card_selected := by
          simpa [positive, negative] using h.card_selected
        weighted_sum := rfl
      }⟩
    apply Finset.mem_image.mpr
    refine ⟨z, hz, ?_⟩
    calc
      f z =
          (∑ i ∈ positive, f (occurrenceValue xs i)) -
            ∑ i ∈ negative, f (occurrenceValue xs i) := by simp [z]
      _ = (∑ i ∈ h.positive, occurrenceValue (xs.map f) i) -
            ∑ i ∈ h.negative, occurrenceValue (xs.map f) i := by
          rw [hpositive, hnegative]
      _ = y := h.weighted_sum

/-- Step 5's quotient specialization of the exact transport lemma. -/
theorem image_plusMinusExactSpectrum_quotient
    (xs : List A) (n : ℕ) (K : AddSubgroup A)
    [DecidableEq (A ⧸ K)] :
    (plusMinusExactSpectrum xs n).image (QuotientAddGroup.mk' K) =
      plusMinusExactSpectrum (xs.map (QuotientAddGroup.mk' K)) n :=
  image_plusMinusExactSpectrum_addMonoidHom
    (QuotientAddGroup.mk' K) xs n

/-- The obligations remaining strictly after Step 4's full-stabilizer branch.
Unlike the earlier residual wrapper, this interface mentions no ordinary
Theorem 2.1 output: it is precisely the `L < G` signed DGM branch, to be split
further into Step 5 (`L ≠ 0`) and Step 6 (`L = 0`). -/
structure PlusMinusTheorem11ProperStabilizerEndpoints
    (A : Type*) [AddCommGroup A] [Fintype A] where
  target :
    ∀ (xs : List A) (n d : ℕ),
      Nat.card A ≤ n →
      PlusMinusDavenportAtMost A d →
      n + d - 1 ≤ xs.length →
      plusMinusSpectrumStabilizer xs n < ⊤ →
      PlusMinusGMOCorollary12At xs n
  nonfull :
    ∀ (xs : List A) (n d : ℕ),
      Nat.card A ≤ n →
      PlusMinusDavenportAtMost A d →
      n + d - 1 ≤ xs.length →
      plusMinusExactSpectrum xs n ≠ Finset.univ →
      plusMinusSpectrumStabilizer xs n < ⊤ →
      Nonempty (PlusMinusPairedCosetCertificate xs)

/-- The genuinely unresolved local cases after removing the automatically
closing Theorem 2.1 large branch.  This is strictly narrower than the source
endpoints: every field is required only when no full-branch certificate exists.
The remaining proof corresponds to the periodic/small-large cases in Steps
1--6 of Theorem 1.1 and their uses of Lemmas 3.1--3.5. -/
structure PlusMinusTheorem11ResidualEndpoints
    (A : Type*) [AddCommGroup A] [Fintype A] where
  target :
    ∀ (xs : List A) (n d : ℕ),
      Nat.card A ≤ n →
      PlusMinusDavenportAtMost A d →
      n + d - 1 ≤ xs.length →
      ¬Nonempty (PlusMinusTheorem21FullCertificate xs n) →
      PlusMinusGMOCorollary12At xs n
  nonfull :
    ∀ (xs : List A) (n d : ℕ),
      Nat.card A ≤ n →
      PlusMinusDavenportAtMost A d →
      n + d - 1 ≤ xs.length →
      plusMinusExactSpectrum xs n ≠ Finset.univ →
      ¬Nonempty (PlusMinusTheorem21FullCertificate xs n) →
      Nonempty (PlusMinusPairedCosetCertificate xs)

/-- Reinsert the now-proved large/full branch around the residual Theorem 1.1
obligation.  In the non-full endpoint, a full certificate contradicts the
non-full hypothesis, so only the residual branch can remain. -/
theorem plusMinusTheorem11StepEndpoints_of_residual
    (h : PlusMinusTheorem11ResidualEndpoints A) :
    PlusMinusTheorem11StepEndpoints A := by
  classical
  refine {
    target := ?_
    nonfull := ?_
  }
  · intro xs n d hn hD hlen
    by_cases hfull : Nonempty (PlusMinusTheorem21FullCertificate xs n)
    · obtain ⟨hfull⟩ := hfull
      exact hfull.corollary12At
    · exact h.target xs n d hn hD hlen hfull
  · intro xs n d hn hD hlen hnotfull
    by_cases hfull : Nonempty (PlusMinusTheorem21FullCertificate xs n)
    · obtain ⟨hfull⟩ := hfull
      exact (hnotfull hfull.fullSpectrum).elim
    · exact h.nonfull xs n d hn hD hlen hnotfull hfull

/-- A Davenport upper threshold cannot be zero: the empty sequence has no
nonempty occurrence selection. -/
theorem one_le_of_plusMinusDavenportAtMost
    {d : ℕ} (hD : PlusMinusDavenportAtMost A d) : 1 ≤ d := by
  by_contra hnot
  have hd : d = 0 := by omega
  subst d
  rcases hD [] rfl with ⟨I, ⟨i, _hi⟩, _sign, _hsum⟩
  exact Fin.elim0 i

/-- Close Step 4 around the proper-stabilizer obligations.  The `L = G`
branch is proved above; in the non-full conclusion, `L < G` follows
automatically from exact-spectrum nonemptiness and properness. -/
theorem plusMinusTheorem11StepEndpoints_of_properStabilizer
    (h : PlusMinusTheorem11ProperStabilizerEndpoints A) :
    PlusMinusTheorem11StepEndpoints A := by
  classical
  refine {
    target := ?_
    nonfull := ?_
  }
  · intro xs n d hn hD hlen
    have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hD
    have hnlen : n ≤ xs.length := by omega
    by_cases htop : plusMinusSpectrumStabilizer xs n = ⊤
    · have hfull :=
        plusMinusExactSpectrum_eq_univ_of_stabilizer_eq_top xs n hnlen htop
      refine ⟨0, ?_⟩
      apply (mem_plusMinusExactSpectrum_iff xs n (n • (0 : A))).1
      rw [hfull]
      simp
    · exact h.target xs n d hn hD hlen (lt_top_iff_ne_top.mpr htop)
  · intro xs n d hn hD hlen hnotfull
    have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hD
    have hnlen : n ≤ xs.length := by omega
    have hstrict : plusMinusSpectrumStabilizer xs n < ⊤ := by
      apply stabilizer_lt_top_of_finset_nonempty_ne_univ
        (plusMinusExactSpectrum xs n)
        (plusMinusExactSpectrum_nonempty xs n hnlen)
        hnotfull
    exact h.nonfull xs n d hn hD hlen hnotfull hstrict

/-- In a subsingleton group, any prescribed target has an exact signed
selection as soon as enough labelled source occurrences are available. -/
theorem hasPlusMinusSumOfCard_of_subsingleton
    [Subsingleton A] (xs : List A) (n : ℕ) (hn : n ≤ xs.length) (y : A) :
    Nonempty (HasPlusMinusSumOfCard xs n y) := by
  classical
  obtain ⟨I, _hI, hIcard⟩ :=
    Finset.exists_subset_card_eq
      (s := (Finset.univ : Selection xs)) (by simpa using hn)
  exact ⟨{
    positive := I
    negative := ∅
    disjoint := by simp
    card_selected := by simpa using hIcard
    weighted_sum := Subsingleton.elim _ _
  }⟩

/-- The trivial-group base of Theorem 1.1 is proved internally.  Both source
corollaries are full there; no DGM or partition-theorem input is needed. -/
theorem plusMinusTheorem11StepEndpoints_of_subsingleton
    [Subsingleton A] : PlusMinusTheorem11StepEndpoints A := by
  refine {
    target := ?_
    nonfull := ?_
  }
  · intro xs n d _hn hD hlen
    have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hD
    have hnlen : n ≤ xs.length := by omega
    exact ⟨0, hasPlusMinusSumOfCard_of_subsingleton xs n hnlen (n • (0 : A))⟩
  · intro xs n d _hn hD hlen hnotfull
    have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hD
    have hnlen : n ≤ xs.length := by omega
    exfalso
    apply hnotfull
    rw [Finset.eq_univ_iff_forall]
    intro y
    exact (mem_plusMinusExactSpectrum_iff xs n y).2
      (hasPlusMinusSumOfCard_of_subsingleton xs n hnlen y)

/-- Local endpoints assemble the exact Corollary 1.2/1.3 source package.  The
only nontrivial structural conversion is the checked whole-block-to-two-coset
map above. -/
theorem plusMinusGMOSourcePackage_of_theorem11StepEndpoints
    (h : PlusMinusTheorem11StepEndpoints A) :
    PlusMinusGMOSourcePackage A := by
  constructor
  · exact h.target
  · intro xs n d hn hD hlen
    by_cases hfull : plusMinusExactSpectrum xs n = Finset.univ
    · exact Or.inl hfull
    · obtain ⟨hpaired⟩ := h.nonfull xs n d hn hD hlen hfull
      exact Or.inr ⟨{
        K := hpaired.K
        strict := hpaired.strict
        alpha := hpaired.beta
        beta := hpaired.beta
        card_lower := hpaired.card_lower.trans (Finset.card_le_card (by
          intro i hi
          exact (mem_occurrencesInPlusMinusGMOCosets_iff
            xs hpaired.K hpaired.beta hpaired.beta i).2
              ⟨hpaired.positiveWeightCoset i hi,
                hpaired.positiveWeightCoset i hi,
                hpaired.negativeWeightCoset i hi⟩))
      }⟩

/-- The full signed GMO package for any subsingleton finite additive group. -/
theorem plusMinusGMOSourcePackage_of_subsingleton
    [Subsingleton A] : PlusMinusGMOSourcePackage A :=
  plusMinusGMOSourcePackage_of_theorem11StepEndpoints
    plusMinusTheorem11StepEndpoints_of_subsingleton

/-! ## Strict-subgroup induction and provider elimination -/

/-- The remaining signed local Theorem 1.1 proof engine.  Its subgroup step
receives DGM at that subgroup and may call the source theorem only for strict
subgroups.  It starts after the proved Step 4 `L = G` branch, so its endpoint
is required only for `L < G`.  In particular, ordinary Theorem 2.1 is not a
premise: the source paper uses it only in the singleton-weight Step 2. -/
structure PlusMinusTheorem11InductionEngine
    (A : Type*) [AddCommGroup A] [Fintype A] where
  subgroupStep :
    ∀ K : AddSubgroup A, ⊥ < K →
      FiniteDGMSetpartitionInput K →
      (∀ H : AddSubgroup A, H < K → PlusMinusGMOSourcePackage H) →
      PlusMinusTheorem11ProperStabilizerEndpoints K
  ambientStep :
    FiniteDGMSetpartitionInput A →
    (∀ K : AddSubgroup A, K < ⊤ → PlusMinusGMOSourcePackage K) →
    PlusMinusTheorem11ProperStabilizerEndpoints A

/-- The substantive scheduler: strict-subgroup induction plus the internally
proved trivial base converts local Theorem 1.1 steps into the ambient source
package and source packages for every subgroup. -/
theorem plusMinusGMOSources_of_theorem11Induction
    (hDGMSubgroup :
      ∀ K : AddSubgroup A, FiniteDGMSetpartitionInput K)
    (hDGMAmbient : FiniteDGMSetpartitionInput A)
    (engine : PlusMinusTheorem11InductionEngine A) :
    PlusMinusGMOSourcePackage A ∧
      ∀ K : AddSubgroup A, PlusMinusGMOSourcePackage K := by
  have hall : ∀ K : AddSubgroup A, PlusMinusGMOSourcePackage K :=
    addSubgroup_strongInduction
      (fun K : AddSubgroup A ↦ PlusMinusGMOSourcePackage K) (fun K ih ↦ by
      by_cases hK : K = ⊥
      · subst K
        exact @plusMinusGMOSourcePackage_of_subsingleton
          (⊥ : AddSubgroup A) inferInstance (subgroupFintype ⊥) inferInstance
      · exact plusMinusGMOSourcePackage_of_theorem11StepEndpoints
          (plusMinusTheorem11StepEndpoints_of_properStabilizer
            (engine.subgroupStep K (bot_lt_iff_ne_bot.mpr hK)
              (hDGMSubgroup K) ih)))
  have hambient : PlusMinusGMOSourcePackage A :=
    plusMinusGMOSourcePackage_of_theorem11StepEndpoints
      (plusMinusTheorem11StepEndpoints_of_properStabilizer
        (engine.ambientStep hDGMAmbient
          (fun K _hK ↦ hall K)))
  exact ⟨hambient, fun K ↦ hall K⟩

/-- The exact three signed GMO providers required by the 13-page assembly are
derived from the local Theorem 1.1 induction engine: ambient prescribed length,
ambient structural, and structural GMO for every subgroup. -/
theorem plusMinusGMOProviders_of_theorem11Induction
    (hDGMSubgroup :
      ∀ K : AddSubgroup A, FiniteDGMSetpartitionInput K)
    (hDGMAmbient : FiniteDGMSetpartitionInput A)
    (engine : PlusMinusTheorem11InductionEngine A) :
    WeightedGMOPrescribedLengthProvider A ∧
      PlusMinusGMOStructuralProvider A ∧
      (∀ K : AddSubgroup A, PlusMinusGMOStructuralProvider K) := by
  obtain ⟨hambient, hall⟩ :=
    plusMinusGMOSources_of_theorem11Induction
      hDGMSubgroup hDGMAmbient engine
  exact ⟨
    weightedGMOPrescribedLengthProvider_of_corollary12Source hambient.1,
    plusMinusGMOStructuralProvider_of_corollary13Source hambient.2,
    fun K ↦ plusMinusGMOStructuralProvider_of_corollary13Source (hall K).2⟩

end GaoLean

#print axioms GaoLean.theorem11_singleLayer_membership_is_not_paired_containment
#print axioms GaoLean.theorem21SetPartition_sumset_subset_plusMinusExactSpectrum
#print axioms GaoLean.PlusMinusTheorem21FullCertificate.fullSpectrum
#print axioms GaoLean.plusMinusTheorem11StepEndpoints_of_residual
#print axioms GaoLean.plusMinusTheorem11StepEndpoints_of_subsingleton
#print axioms GaoLean.plusMinusGMOSourcePackage_of_theorem11StepEndpoints
#print axioms GaoLean.plusMinusGMOSources_of_theorem11Induction
#print axioms GaoLean.plusMinusGMOProviders_of_theorem11Induction
