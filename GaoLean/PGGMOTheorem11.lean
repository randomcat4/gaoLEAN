import GaoLean.PGGMOPlusMinusSource
import GaoLean.PGGMOTheorem21
import GaoLean.PGDGMStructuralGap
import GaoLean.PGDavenportBridge
import GaoLean.PGDavenportConvolution
import GaoLean.PGInduction
import GaoLean.GAOARDihedralBlocks
import GaoLean.PGFrontend
import GaoLean.PGMiddleNonfull

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

universe u

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-! ## Signed Davenport threshold mechanics -/

/-- Exact occurrence-sensitive definition of the plus-minus Davenport
constant, mirroring the ordinary exact-constant interface. -/
def IsPlusMinusDavenportConstant
    (A : Type*) [AddCommGroup A] (D : ℕ) : Prop :=
  PlusMinusDavenportAtMost A D ∧
    ∀ n : ℕ, n < D →
      ∃ s : List A, s.length = n ∧ ¬HasNonemptyPlusMinusZeroSum s

/-- A signed zero sum in a prefix remains a signed zero sum in the original
labelled source. -/
theorem hasNonemptyPlusMinusZeroSum_of_take
    (s : List A) (N : ℕ) (hN : N ≤ s.length)
    (hzero : HasNonemptyPlusMinusZeroSum (s.take N)) :
    HasNonemptyPlusMinusZeroSum s := by
  classical
  rcases hzero with ⟨I, hIne, sign, hsum⟩
  let emb : Occurrence (s.take N) ↪ Occurrence s :=
    { toFun := fun i =>
        ⟨i.1, lt_of_lt_of_le i.2
          ((List.length_take_le N s).trans hN)⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun x : Occurrence s => x.val) hij }
  let J : Selection s := I.map emb
  let sign' : Occurrence s → PlusMinusSign := fun j =>
    if hj : j.1 < (s.take N).length then sign ⟨j.1, hj⟩
    else .positive
  have hsign (i : Occurrence (s.take N)) : sign' (emb i) = sign i := by
    have hlt : (emb i).1 < (s.take N).length := by
      simpa [emb] using i.2
    rw [show sign' (emb i) =
        if hj : (emb i).1 < (s.take N).length then
          sign ⟨(emb i).1, hj⟩ else .positive by rfl,
      dif_pos hlt]
    congr 1
  have hvalue (i : Occurrence (s.take N)) :
      occurrenceValue s (emb i) = occurrenceValue (s.take N) i := by
    simp [occurrenceValue, emb, List.get_eq_getElem]
  refine ⟨J, ?_, sign', ?_⟩
  · simpa [J] using hIne
  · simpa [J, Finset.sum_map, hsign, hvalue] using hsum

/-- A plus-minus Davenport upper bound at length `D` applies to every longer
source by taking its first `D` labelled occurrences. -/
theorem plusMinusDavenportAtLeast_of_atMost
    {D : ℕ} (hD : PlusMinusDavenportAtMost A D) :
    ∀ s : List A, D ≤ s.length → HasNonemptyPlusMinusZeroSum s := by
  intro s hs
  apply hasNonemptyPlusMinusZeroSum_of_take s D hs
  apply hD (s.take D)
  simp [List.length_take, Nat.min_eq_left hs]

/-- Every exact plus-minus Davenport value is positive. -/
theorem plusMinusDavenportConstant_pos
    (D : ℕ) (hD : IsPlusMinusDavenportConstant A D) : 0 < D := by
  by_contra hnot
  have hDzero : D = 0 := Nat.eq_zero_of_not_pos hnot
  have hempty := hD.1 ([] : List A) (by simp [hDzero])
  rcases hempty with ⟨I, ⟨i, _hi⟩, _sign, _hsum⟩
  exact Fin.elim0 i

/-- A labelled signed zero sum is preserved by every additive homomorphism. -/
theorem hasNonemptyPlusMinusZeroSum_map_addMonoidHom
    {B : Type*} [AddCommGroup B]
    (f : A →+ B) (s : List A)
    (hzero : HasNonemptyPlusMinusZeroSum s) :
    HasNonemptyPlusMinusZeroSum (s.map f) := by
  classical
  rcases hzero with ⟨I, hIne, sign, hsum⟩
  let e := ConcreteGDihedral.mapOccurrenceEquiv f s
  let J : Selection (s.map f) := I.map e.toEmbedding
  let sign' : Occurrence (s.map f) → PlusMinusSign := fun j ↦ sign (e.symm j)
  have hterm (i : Occurrence s) :
      (sign' (e i)).act (occurrenceValue (s.map f) (e i)) =
        f ((sign i).act (occurrenceValue s i)) := by
    have hvalue : occurrenceValue (s.map f) (e i) =
        f (occurrenceValue s i) := by
      simpa [e] using
        ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f s i
    cases hsign : sign i <;>
      simp [sign', hsign, PlusMinusSign.act, hvalue]
  refine ⟨J, ?_, sign', ?_⟩
  · simpa [J] using hIne
  · calc
      (∑ j ∈ J, (sign' j).act (occurrenceValue (s.map f) j)) =
          ∑ i ∈ I, f ((sign i).act (occurrenceValue s i)) := by
            simp [J, Finset.sum_map, hterm]
      _ = f (∑ i ∈ I, (sign i).act (occurrenceValue s i)) := by
            rw [map_sum]
      _ = 0 := by rw [hsum, map_zero]

/-- A plus-minus Davenport threshold descends along an additive quotient.
The proof lifts each labelled quotient occurrence through a fixed section,
uses the ambient threshold, and maps the resulting signed zero sum back. -/
theorem plusMinusDavenportAtMost_quotient
    (K : AddSubgroup A) {d : ℕ}
    (hD : PlusMinusDavenportAtMost A d) :
    PlusMinusDavenportAtMost (A ⧸ K) d := by
  intro s hs
  let lifts : List A := s.map (quotientAddSection K)
  have hlifts : lifts.length = d := by simpa [lifts] using hs
  have hzero : HasNonemptyPlusMinusZeroSum lifts := hD lifts hlifts
  have hmapped := hasNonemptyPlusMinusZeroSum_map_addMonoidHom
    (QuotientAddGroup.mk' K) lifts hzero
  have hliftmap : lifts.map (QuotientAddGroup.mk' K) = s := by
    change (s.map (quotientAddSection K)).map
      (QuotientAddGroup.mk' K) = s
    rw [List.map_map]
    have hcomp : (QuotientAddGroup.mk' K : A → A ⧸ K) ∘
        quotientAddSection K = id := by
      funext x
      exact quotientAddSection_mk K x
    rw [hcomp, List.map_id]
  rw [hliftmap] at hmapped
  exact hmapped

/-- Split a signed sum on an appended source into its labelled prefix and
suffix selections.  The signs are pulled back along the two canonical
occurrence embeddings. -/
theorem sum_signed_prefixSelection_add_sum_signed_suffixSelection
    (left right : List A) (I : Selection (left ++ right))
    (sign : Occurrence (left ++ right) → PlusMinusSign) :
    let IL := prefixSelection left right I
    let IR := suffixSelection left right I
    let signL : Occurrence left → PlusMinusSign := fun i ↦
      sign (appendLeftOccurrenceEmbedding left right i)
    let signR : Occurrence right → PlusMinusSign := fun i ↦
      sign (appendRightOccurrenceEmbedding left right i)
    (∑ i ∈ IL, (signL i).act (occurrenceValue left i)) +
        (∑ i ∈ IR, (signR i).act (occurrenceValue right i)) =
      ∑ i ∈ I, (sign i).act (occurrenceValue (left ++ right) i) := by
  classical
  dsimp only
  have hleft :
      (∑ i ∈ prefixSelection left right I,
          (sign (appendLeftOccurrenceEmbedding left right i)).act
            (occurrenceValue left i)) =
        ∑ i ∈ I ∩ prefixOccurrences left right,
          (sign i).act (occurrenceValue (left ++ right) i) := by
    rw [← map_prefixSelection_eq_inter left right I]
    simp [Finset.sum_map, occurrenceValue_appendLeftOccurrenceEmbedding]
  have hright :
      (∑ i ∈ suffixSelection left right I,
          (sign (appendRightOccurrenceEmbedding left right i)).act
            (occurrenceValue right i)) =
        ∑ i ∈ I \ prefixOccurrences left right,
          (sign i).act (occurrenceValue (left ++ right) i) := by
    rw [← map_suffixSelection_eq_sdiff left right I]
    simp [Finset.sum_map, occurrenceValue_appendRightOccurrenceEmbedding]
  let P := prefixOccurrences left right
  have hdis : Disjoint (I ∩ P) (I \ P) := by
    exact Finset.disjoint_left.mpr (by
      intro x hxinter hxsdiff
      exact (Finset.mem_sdiff.mp hxsdiff).2
        (Finset.mem_inter.mp hxinter).2)
  have hunion : (I ∩ P) ∪ (I \ P) = I := by
    ext x
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  rw [hleft, hright]
  rw [← Finset.sum_union hdis, hunion]

/-! ## Finite extraction for the signed Step 1 branch -/

/-- Labelled zero occurrences.  This finset counts repetitions by source
position and is the singleton-cell count in odd order. -/
noncomputable def plusMinusZeroOccurrences (xs : List A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i ↦ occurrenceValue xs i = 0

@[simp]
theorem mem_plusMinusZeroOccurrences_iff (xs : List A) (i : Occurrence xs) :
    i ∈ plusMinusZeroOccurrences xs ↔ occurrenceValue xs i = 0 := by
  classical
  simp [plusMinusZeroOccurrences]

/-- A possibly empty occurrence selection equipped with a signed sum zero.
Unlike `HasNonemptyPlusMinusZeroSum`, this predicate is closed under disjoint
union and therefore supports a maximal-cardinality argument. -/
def IsPlusMinusZeroSelection (xs : List A) (I : Selection xs) : Prop :=
  ∃ sign : Occurrence xs → PlusMinusSign,
    ∑ i ∈ I, (sign i).act (occurrenceValue xs i) = 0

theorem isPlusMinusZeroSelection_empty (xs : List A) :
    IsPlusMinusZeroSelection xs ∅ := by
  exact ⟨fun _ ↦ .positive, by simp⟩

/-- Disjoint occurrence-level signed zero selections may be joined without
identifying repeated source values. -/
theorem IsPlusMinusZeroSelection.union
    {xs : List A} {I J : Selection xs}
    (hI : IsPlusMinusZeroSelection xs I)
    (hJ : IsPlusMinusZeroSelection xs J) (hdis : Disjoint I J) :
    IsPlusMinusZeroSelection xs (I ∪ J) := by
  classical
  obtain ⟨signI, hsumI⟩ := hI
  obtain ⟨signJ, hsumJ⟩ := hJ
  let sign : Occurrence xs → PlusMinusSign := fun i ↦
    if i ∈ I then signI i else signJ i
  refine ⟨sign, ?_⟩
  rw [Finset.sum_union hdis]
  have hleft : (∑ i ∈ I, (sign i).act (occurrenceValue xs i)) = 0 := by
    calc
      (∑ i ∈ I, (sign i).act (occurrenceValue xs i)) =
          ∑ i ∈ I, (signI i).act (occurrenceValue xs i) := by
            apply Finset.sum_congr rfl
            intro i hi
            simp [sign, hi]
      _ = 0 := hsumI
  have hright : (∑ i ∈ J, (sign i).act (occurrenceValue xs i)) = 0 := by
    calc
      (∑ i ∈ J, (sign i).act (occurrenceValue xs i)) =
          ∑ i ∈ J, (signJ i).act (occurrenceValue xs i) := by
            apply Finset.sum_congr rfl
            intro i hi
            have hiI : i ∉ I := by
              intro hi'
              exact Finset.disjoint_left.mp hdis hi' hi
            simp [sign, hiI]
      _ = 0 := hsumJ
  rw [hleft, hright, add_zero]

/-- Lift a signed zero sum from the value list of a labelled subselection
back to its exact source positions. -/
theorem exists_isPlusMinusZeroSelection_subset_of_occurrenceSubsequence
    (xs : List A) (R : Selection xs)
    (hzero : HasNonemptyPlusMinusZeroSum (occurrenceSubsequence xs R)) :
    ∃ J : Selection xs,
      J.Nonempty ∧ J ⊆ R ∧ J.card ≤ R.card ∧
        IsPlusMinusZeroSelection xs J := by
  classical
  rcases hzero with ⟨I, hIne, sign, hsum⟩
  let e : Occurrence (occurrenceSubsequence xs R) ↪ Occurrence xs :=
    ⟨occurrenceSubsequenceSource xs R,
      occurrenceSubsequenceSource_injective xs R⟩
  let J : Selection xs := I.map e
  letI : Nonempty (Occurrence (occurrenceSubsequence xs R)) :=
    ⟨hIne.choose⟩
  let sign' : Occurrence xs → PlusMinusSign := fun i ↦
    sign (Function.invFun e i)
  have hsign (i : Occurrence (occurrenceSubsequence xs R)) :
      sign' (e i) = sign i := by
    exact congrArg sign (Function.leftInverse_invFun e.injective i)
  have hvalue (i : Occurrence (occurrenceSubsequence xs R)) :
      occurrenceValue xs (e i) =
        occurrenceValue (occurrenceSubsequence xs R) i := by
    exact (occurrenceValue_occurrenceSubsequence xs R i).symm
  refine ⟨J, ?_, ?_, ?_, ?_⟩
  · simpa [J] using hIne
  · intro j hj
    rcases Finset.mem_map.mp hj with ⟨i, _hi, rfl⟩
    exact occurrenceSubsequenceSource_mem xs R i
  · rw [Finset.card_map]
    calc
      I.card ≤ (Finset.univ : Selection (occurrenceSubsequence xs R)).card :=
        Finset.card_le_card (Finset.subset_univ I)
      _ = (occurrenceSubsequence xs R).length := by simp
      _ = R.card := by simp [occurrenceSubsequence]
  · refine ⟨sign', ?_⟩
    simpa [J, Finset.sum_map, hsign, hvalue] using hsum

/-- A zero occurrence selection has signed sum zero with every sign positive. -/
theorem isPlusMinusZeroSelection_of_subset_zeroOccurrences
    {xs : List A} {I : Selection xs}
    (hI : I ⊆ plusMinusZeroOccurrences xs) :
    IsPlusMinusZeroSelection xs I := by
  refine ⟨fun _ ↦ .positive, ?_⟩
  apply Finset.sum_eq_zero
  intro i hi
  have hizero : occurrenceValue xs i = 0 :=
    (mem_plusMinusZeroOccurrences_iff xs i).1 (hI hi)
  simp [PlusMinusSign.act, hizero]

/-- Convert a zero-sum selection of exact cardinality into the manuscript's
positive/negative occurrence split via the already proved signed-block
spectrum equivalence. -/
theorem hasPlusMinusSumOfCard_zero_of_isPlusMinusZeroSelection
    {xs : List A} {I : Selection xs} {n : ℕ}
    (hI : IsPlusMinusZeroSelection xs I) (hcard : I.card = n) :
    Nonempty (HasPlusMinusSumOfCard xs n 0) := by
  classical
  obtain ⟨sign, hsum⟩ := hI
  let choice : PlusMinusSetpartitionChoice xs n 0 := {
    selected := I
    card_selected := hcard
    chosenValue := fun i ↦ (sign i).act (occurrenceValue xs i)
    chosenValue_mem := by
      intro i _hi
      cases sign i <;>
        simp [plusMinusOccurrenceBlock, plusMinusValueBlock,
          PlusMinusSign.act]
    sum_chosen := hsum
  }
  have hmem : 0 ∈ plusMinusSetpartitionSpectrum xs n :=
    (mem_plusMinusSetpartitionSpectrum_iff xs n 0).2 ⟨choice⟩
  rw [plusMinusSetpartitionSpectrum_eq_plusMinusExactSpectrum] at hmem
  exact (mem_plusMinusExactSpectrum_iff xs n 0).1 hmem

/-- Signed Step 1 in the high-zero-multiplicity branch.  A maximum-cardinality
signed zero selection among the nonzero occurrences must reach `n-z`: if it
did not, `d` remaining occurrences would supply another nonempty Davenport
block, and `z ≥ d` keeps the enlarged union below `n`.  Zero occurrences then
pad the result to exactly `n`. -/
theorem hasPlusMinusSumOfCard_zero_of_many_zeroOccurrences
    (xs : List A) (n d : ℕ)
    (hD : PlusMinusDavenportAtMost A d)
    (hlen : n + d - 1 ≤ xs.length)
    (hz : d ≤ (plusMinusZeroOccurrences xs).card) :
    Nonempty (HasPlusMinusSumOfCard xs n 0) := by
  classical
  let Z : Selection xs := plusMinusZeroOccurrences xs
  let N : Selection xs := Finset.univ \ Z
  have hZcard : Z.card ≤ xs.length := by
    simpa using Finset.card_le_card (Finset.subset_univ Z)
  have hz' : d ≤ Z.card := by simpa [Z] using hz
  have hNcard : N.card = xs.length - Z.card := by
    dsimp only [N]
    rw [Finset.card_sdiff]
    simp
  have hd : 1 ≤ d := by
    by_contra hd0
    have hdEq : d = 0 := Nat.eq_zero_of_not_pos hd0
    have hempty := hD ([] : List A) (by simp [hdEq])
    rcases hempty with ⟨I, ⟨i, _hi⟩, _sign, _hsum⟩
    exact Fin.elim0 i
  let good : Finset (Selection xs) := Finset.univ.filter fun I ↦
    I ⊆ N ∧ I.card ≤ n ∧ IsPlusMinusZeroSelection xs I
  have hemptyGood : (∅ : Selection xs) ∈ good := by
    simp [good, isPlusMinusZeroSelection_empty]
  obtain ⟨I, hIgood, hImax⟩ := Finset.exists_max_image good
    (fun J ↦ J.card) ⟨∅, hemptyGood⟩
  have hIsub : I ⊆ N := (Finset.mem_filter.mp hIgood).2.1
  have hIcardN : I.card ≤ n := (Finset.mem_filter.mp hIgood).2.2.1
  have hIzero : IsPlusMinusZeroSelection xs I :=
    (Finset.mem_filter.mp hIgood).2.2.2
  have hIlarge : n - Z.card ≤ I.card := by
    by_contra hnot
    have hIsmall : I.card < n - Z.card := Nat.lt_of_not_ge hnot
    let R : Selection xs := N \ I
    have hRcard : d ≤ R.card := by
      have hcard : R.card = N.card - I.card := by
        dsimp only [R]
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIsub]
      rw [hcard, hNcard]
      omega
    obtain ⟨Rd, hRdsub, hRdcard⟩ :=
      Finset.exists_subset_card_eq (s := R) hRcard
    have htlen : (occurrenceSubsequence xs Rd).length = d := by
      simpa [occurrenceSubsequence] using hRdcard
    have hzeroSub :
        HasNonemptyPlusMinusZeroSum (occurrenceSubsequence xs Rd) :=
      hD (occurrenceSubsequence xs Rd) htlen
    obtain ⟨J, hJne, hJsubRd, hJcard, hJzero⟩ :=
      exists_isPlusMinusZeroSelection_subset_of_occurrenceSubsequence
        xs Rd hzeroSub
    have hJsubR : J ⊆ R := hJsubRd.trans hRdsub
    have hJsubN : J ⊆ N := by
      intro j hj
      exact (Finset.mem_sdiff.mp (hJsubR hj)).1
    have hdis : Disjoint I J := by
      rw [Finset.disjoint_left]
      intro j hjI hjJ
      exact (Finset.mem_sdiff.mp (hJsubR hjJ)).2 hjI
    have hUnionSub : I ∪ J ⊆ N := Finset.union_subset hIsub hJsubN
    have hJcardD : J.card ≤ d := hJcard.trans_eq hRdcard
    have hUnionCard : (I ∪ J).card ≤ n := by
      rw [Finset.card_union_of_disjoint hdis]
      omega
    have hUnionZero : IsPlusMinusZeroSelection xs (I ∪ J) :=
      hIzero.union hJzero hdis
    have hUnionGood : I ∪ J ∈ good := by
      simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hUnionSub, hUnionCard, hUnionZero⟩
    have hmaxUnion : (I ∪ J).card ≤ I.card := hImax _ hUnionGood
    rw [Finset.card_union_of_disjoint hdis] at hmaxUnion
    have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
    omega
  let k := n - I.card
  have hkZ : k ≤ Z.card := by
    dsimp only [k]
    omega
  obtain ⟨F, hFsub, hFcard⟩ :=
    Finset.exists_subset_card_eq (s := Z) hkZ
  have hdisIF : Disjoint I F := by
    rw [Finset.disjoint_left]
    intro i hiI hiF
    have hiN := hIsub hiI
    exact (Finset.mem_sdiff.mp hiN).2 (hFsub hiF)
  have hFzero : IsPlusMinusZeroSelection xs F :=
    isPlusMinusZeroSelection_of_subset_zeroOccurrences hFsub
  have hUnionZero : IsPlusMinusZeroSelection xs (I ∪ F) :=
    hIzero.union hFzero hdisIF
  have hUnionCard : (I ∪ F).card = n := by
    rw [Finset.card_union_of_disjoint hdisIF, hFcard]
    dsimp only [k]
    omega
  exact hasPlusMinusSumOfCard_zero_of_isPlusMinusZeroSelection
    hUnionZero hUnionCard

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

/-- In the odd-order specialization used by the 13-page manuscript, putting
both `x` and `-x` in the same `K`-coset forces the labelled source value `x`
itself into `K`.  This is the exact place where the odd-order hypothesis
removes the two-torsion obstruction present for general even groups. -/
theorem PlusMinusPairedCosetCertificate.selectedValue_mem_of_odd
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs)
    (hodd : Odd (Nat.card A))
    (i : Occurrence xs) (hi : i ∈ h.selected) :
    occurrenceValue xs i ∈ h.K := by
  have hquotNat : Odd (Nat.card (A ⧸ h.K)) :=
    odd_natCard_quotient_of_odd_natCard h.K hodd
  have hquot : Odd (Fintype.card (A ⧸ h.K)) := by
    simpa [Nat.card_eq_fintype_card] using hquotNat
  exact mem_of_pos_neg_mem_same_coset_of_quotient_card_odd h.K hquot
    (h.positiveWeightCoset i hi) (h.negativeWeightCoset i hi)

/-- The same odd-order argument also shows that the common coset center is
in `K`: the certificate's cardinality bound makes the selected occurrence
set nonempty, and `x ∈ K` together with `x - beta ∈ K` gives `beta ∈ K`.
Consequently the apparent affine/over-group seam collapses to a genuinely
`K`-valued selected list in the odd specialization, without silently
discarding either sign condition. -/
theorem PlusMinusPairedCosetCertificate.center_mem_and_selectedValues_mem_of_odd
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs)
    (hodd : Odd (Nat.card A)) :
    h.beta ∈ h.K ∧
      ∀ i ∈ h.selected, occurrenceValue xs i ∈ h.K := by
  have hselpos : 0 < h.selected.card := by
    have hlowerPos : 0 < xs.length - Nat.card (A ⧸ h.K) + 2 := by omega
    exact hlowerPos.trans_le h.card_lower
  obtain ⟨i, hi⟩ := h.selected.card_pos.mp hselpos
  have hxi : occurrenceValue xs i ∈ h.K :=
    h.selectedValue_mem_of_odd hodd i hi
  have hxsub : occurrenceValue xs i - h.beta ∈ h.K :=
    h.positiveWeightCoset i hi
  constructor
  · have hdiff := h.K.sub_mem hxi hxsub
    have heq : occurrenceValue xs i -
        (occurrenceValue xs i - h.beta) = h.beta := by abel
    rwa [heq] at hdiff
  · intro j hj
    exact h.selectedValue_mem_of_odd hodd j hj

/-- Reindex the selected labelled occurrences as a genuine list in the
subgroup.  No source value is coerced into `K` without the preceding odd-order
proof; repetitions remain distinct because the list is built from attached
occurrences, not from a finset of values. -/
noncomputable def PlusMinusPairedCosetCertificate.selectedSubtypeListOfOdd
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs)
    (hodd : Odd (Nat.card A)) : List h.K := by
  classical
  exact h.selected.attach.toList.map fun j ↦
    ⟨occurrenceValue xs j.1,
      h.selectedValue_mem_of_odd hodd j.1 j.2⟩

@[simp]
theorem PlusMinusPairedCosetCertificate.length_selectedSubtypeListOfOdd
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs)
    (hodd : Odd (Nat.card A)) :
    (h.selectedSubtypeListOfOdd hodd).length = h.selected.card := by
  classical
  simp [PlusMinusPairedCosetCertificate.selectedSubtypeListOfOdd]

/-- Forgetting the subgroup proof recovers, in the same attached-occurrence
order, the original labelled source values. -/
theorem PlusMinusPairedCosetCertificate.map_coe_selectedSubtypeListOfOdd
    {xs : List A} (h : PlusMinusPairedCosetCertificate xs)
    (hodd : Odd (Nat.card A)) :
    (h.selectedSubtypeListOfOdd hodd).map (fun x : h.K ↦ (x : A)) =
      h.selected.attach.toList.map fun j ↦ occurrenceValue xs j.1 := by
  classical
  simp [PlusMinusPairedCosetCertificate.selectedSubtypeListOfOdd]

/-! ## Odd-order collapse of singleton signed cells -/

/-- An odd-order finite additive group has no nonzero self-negative element,
expressed using the manuscript's `Nat.card` convention. -/
theorem eq_zero_of_neg_eq_self_of_natCard_odd
    (hodd : Odd (Nat.card A)) {x : A} (hx : -x = x) : x = 0 := by
  have hcard : Odd (Fintype.card A) := by
    simpa [Nat.card_eq_fintype_card] using hodd
  apply eq_zero_of_two_nsmul_eq_zero_of_card_odd hcard
  rw [two_nsmul]
  calc
    x + x = x + (-x) := by rw [hx]
    _ = 0 := add_neg_cancel x

/-- For the `{+1,-1}` weight set in odd order, a signed cell is a singleton
exactly at the zero source value.  This is the formal `d = gcd(2, exp G)=1`
collapse used to shorten Step 6 in the 13-page specialization. -/
theorem plusMinusValueBlock_eq_singleton_self_iff_of_natCard_odd
    (hodd : Odd (Nat.card A)) (x : A) :
    plusMinusValueBlock x = {x} ↔ x = 0 := by
  constructor
  · intro hsingle
    have hnegmem : -x ∈ plusMinusValueBlock x := by
      simp [plusMinusValueBlock]
    rw [hsingle] at hnegmem
    have hneg : -x = x := by simpa using hnegmem
    exact eq_zero_of_neg_eq_self_of_natCard_odd hodd hneg
  · rintro rfl
    simp [plusMinusValueBlock]

/-- The same singleton criterion for a labelled occurrence block. -/
theorem plusMinusOccurrenceBlock_eq_singleton_iff_of_natCard_odd
    (hodd : Odd (Nat.card A)) (xs : List A) (i : Occurrence xs) :
    plusMinusOccurrenceBlock xs i = {occurrenceValue xs i} ↔
      occurrenceValue xs i = 0 := by
  simpa [plusMinusOccurrenceBlock] using
    plusMinusValueBlock_eq_singleton_self_iff_of_natCard_odd
      hodd (occurrenceValue xs i)

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

/-- Any manuscript concentration record contains enough two-sign data to
form a whole-block certificate.  The source-coset field is not used in this
direction; both positive and negative weight-coset fields are used
separately. -/
theorem plusMinusPairedCosetCertificate_of_GMOConcentration
    {xs : List A} (h : PlusMinusGMOConcentration xs) :
    Nonempty (PlusMinusPairedCosetCertificate xs) := by
  refine ⟨{
    K := h.K
    strict := h.strict
    beta := h.beta
    selected := h.selected
    signedBlockCoset := ?_
    card_lower := h.card_lower
  }⟩
  intro i hi y hy
  rw [mem_plusMinusOccurrenceBlock_iff] at hy
  rcases hy with rfl | rfl
  · exact h.positiveWeightCoset i hi
  · exact h.negativeWeightCoset i hi

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

/-- A nonempty finite set which is invariant under `L` and meets every
`L`-coset is the whole ambient group. -/
theorem finset_eq_univ_of_quotient_image_eq_univ
    (S : Finset A) (hS : S.Nonempty) (L : AddSubgroup A)
    [DecidableEq (A ⧸ L)]
    (hL : L ≤ AddAction.stabilizer A (S : Set A))
    (himage : S.image (QuotientAddGroup.mk' L) = Finset.univ) :
    S = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  intro y
  have hqy : QuotientAddGroup.mk' L y ∈
      S.image (QuotientAddGroup.mk' L) := by
    rw [himage]
    simp
  obtain ⟨x, hxS, hqxy⟩ := Finset.mem_image.mp hqy
  have hyxL : y - x ∈ L := by
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    exact hqxy.symm
  have hyxStab : y - x ∈ AddAction.stabilizer A (S : Set A) := hL hyxL
  have hyxFin : y - x ∈ S.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hS]
    exact hyxStab
  have htranslate := (Finset.mem_addStab hS).mp hyxFin
  have hy : (y - x) +ᵥ x ∈ (y - x) +ᵥ S :=
    Finset.vadd_mem_vadd_finset hxS
  rw [htranslate] at hy
  simpa [vadd_eq_add] using hy

/-- Step 5's quotient-full branch closes the ambient spectrum: the original
exact signed spectrum is invariant under its full stabilizer, and exact
homomorphic transport says that quotient fullness meets every stabilizer
coset. -/
theorem plusMinusExactSpectrum_eq_univ_of_stabilizerQuotient_full
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length)
    (L : AddSubgroup A)
    (hL : L = plusMinusSpectrumStabilizer xs n)
    (hquot : plusMinusExactSpectrum
      (xs.map (QuotientAddGroup.mk' L)) n = Finset.univ) :
    plusMinusExactSpectrum xs n = Finset.univ := by
  classical
  apply finset_eq_univ_of_quotient_image_eq_univ
    (plusMinusExactSpectrum xs n)
    (plusMinusExactSpectrum_nonempty xs n hn) L
  · simpa [hL, plusMinusSpectrumStabilizer]
  · rw [image_plusMinusExactSpectrum_quotient, hquot]

/-- Lift a paired concentration certificate from `A/L` to `A`.  The lifted
subgroup is the comap of the quotient subgroup, the center is an arbitrary
section lift, and the selected occurrence set is transported through the
canonical position equivalence.  Crucially, whole signed-block containment
is pulled back; no one-sign membership shortcut is used. -/
theorem plusMinusPairedCosetCertificate_of_quotient
    (xs : List A) (L : AddSubgroup A)
    (hQ : PlusMinusPairedCosetCertificate
      (xs.map (QuotientAddGroup.mk' L))) :
    Nonempty (PlusMinusPairedCosetCertificate xs) := by
  classical
  let q : A →+ A ⧸ L := QuotientAddGroup.mk' L
  let e : Occurrence xs ≃
      Occurrence (xs.map (QuotientAddGroup.mk' L)) :=
    ConcreteGDihedral.mapOccurrenceEquiv (QuotientAddGroup.mk' L) xs
  let K : AddSubgroup A := hQ.K.comap q
  let beta : A := quotientAddSection L hQ.beta
  let selected : Selection xs := hQ.selected.map e.symm.toEmbedding
  have hmapK : K.map q = hQ.K := by
    simpa [K, q] using
      AddSubgroup.map_comap_eq_self_of_surjective
        (QuotientAddGroup.mk'_surjective L) hQ.K
  have hLK : L ≤ K := by
    intro x hx
    change q x ∈ hQ.K
    have hqx : q x = 0 := (QuotientAddGroup.eq_zero_iff x).2 hx
    rw [hqx]
    exact hQ.K.zero_mem
  have hcardQuot : Nat.card ((A ⧸ L) ⧸ hQ.K) = Nat.card (A ⧸ K) := by
    have hcard := Nat.card_congr
      (QuotientAddGroup.quotientQuotientEquivQuotient L K hLK).toEquiv
    rw [hmapK] at hcard
    simpa [Nat.card_eq_fintype_card] using hcard
  have hstrictK : K < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply (ne_of_lt hQ.strict)
    apply top_unique
    intro z _hz
    obtain ⟨x, rfl⟩ := QuotientAddGroup.mk'_surjective L z
    have hxK : x ∈ K := by
      rw [htop]
      trivial
    exact hxK
  refine ⟨{
    K := K
    strict := hstrictK
    beta := beta
    selected := selected
    signedBlockCoset := ?_
    card_lower := ?_
  }⟩
  · intro i hi y hy
    have hei : e i ∈ hQ.selected := by
      obtain ⟨j, hj, hji⟩ := Finset.mem_map.mp hi
      have hje : j = e i := by
        exact e.symm_apply_eq.mp hji
      simpa [hje] using hj
    have hqy : q y ∈ plusMinusOccurrenceBlock
        (xs.map (QuotientAddGroup.mk' L)) (e i) := by
      rw [mem_plusMinusOccurrenceBlock_iff] at hy ⊢
      rcases hy with hy | hy
      · left
        rw [hy]
        simpa [e, q] using
          (ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv
            (QuotientAddGroup.mk' L) xs i).symm
      · right
        rw [hy, map_neg]
        congr 1
        simpa [e, q] using
          (ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv
            (QuotientAddGroup.mk' L) xs i).symm
    have hmem := hQ.signedBlockCoset (e i) hei (q y) hqy
    change q (y - beta) ∈ hQ.K
    have hqbeta : q beta = hQ.beta := by
      simpa [q, beta] using quotientAddSection_mk L hQ.beta
    rw [map_sub, hqbeta]
    exact hmem
  · change xs.length - Nat.card (A ⧸ K) + 2 ≤ selected.card
    have hlenmap : (xs.map (QuotientAddGroup.mk' L)).length = xs.length :=
      by simp
    have hselcard : selected.card = hQ.selected.card := by
      simpa [selected]
    calc
      xs.length - Nat.card (A ⧸ K) + 2 =
          (xs.map (QuotientAddGroup.mk' L)).length -
            Nat.card ((A ⧸ L) ⧸ hQ.K) + 2 := by
              rw [hlenmap, hcardQuot]
      _ ≤ hQ.selected.card := hQ.card_lower
      _ = selected.card := hselcard.symm

/-- Complete Step 5 structural lifting from the source theorem on the
stabilizer quotient.  Quotient fullness closes the ambient spectrum by
stabilizer invariance; quotient concentration is converted to a whole-block
certificate and lifted by the preceding theorem.  The Davenport threshold
is transported to the quotient without changing `d`. -/
theorem plusMinusCorollary13At_of_stabilizerQuotientSource
    (xs : List A) (n d : ℕ)
    (hn : Nat.card A ≤ n)
    (hD : PlusMinusDavenportAtMost A d)
    (hlen : n + d - 1 ≤ xs.length)
    (L : AddSubgroup A)
    (hL : L = plusMinusSpectrumStabilizer xs n)
    (hsourceQ : PlusMinusGMOCorollary13Source (A ⧸ L)) :
    PlusMinusGMOCorollary13At xs n := by
  classical
  have hQcard : Nat.card (A ⧸ L) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos L.card_quotient_dvd_card
  have hQn : Nat.card (A ⧸ L) ≤ n := hQcard.trans hn
  have hQD : PlusMinusDavenportAtMost (A ⧸ L) d :=
    plusMinusDavenportAtMost_quotient L hD
  have hQlen : n + d - 1 ≤
      (xs.map (QuotientAddGroup.mk' L)).length := by simpa using hlen
  rcases hsourceQ (xs.map (QuotientAddGroup.mk' L)) n d
      hQn hQD hQlen with hfull | hcon
  · exact Or.inl
      (plusMinusExactSpectrum_eq_univ_of_stabilizerQuotient_full
        xs n (by
          have hd : 1 ≤ d := by
            by_contra hnot
            have hd0 : d = 0 := by omega
            subst d
            rcases hD [] rfl with ⟨I, ⟨i, _hi⟩, _sign, _hsum⟩
            exact Fin.elim0 i
          omega) L hL hfull)
  · obtain ⟨hcon⟩ := hcon
    obtain ⟨hgmoQ⟩ :=
      plusMinusGMOConcentration_of_corollary13Concentration hcon
    obtain ⟨hpairedQ⟩ :=
      plusMinusPairedCosetCertificate_of_GMOConcentration hgmoQ
    obtain ⟨hpairedA⟩ :=
      plusMinusPairedCosetCertificate_of_quotient xs L hpairedQ
    obtain ⟨hgmoA⟩ := hpairedA.toGMOConcentration
    exact Or.inr
      (corollary13Concentration_of_plusMinusGMOConcentration hgmoA)

/-- Step 5 for the prescribed target.  A quotient exact-`n` signed sum lifts
to some ambient representative `y`.  Its difference from `n • z`, for a
section lift `z` of the quotient target, lies in the spectrum stabilizer;
translation invariance therefore replaces `y` by the literal target
`n • z`. -/
theorem plusMinusCorollary12At_of_stabilizerQuotientSource
    (xs : List A) (n d : ℕ)
    (hn : Nat.card A ≤ n)
    (hD : PlusMinusDavenportAtMost A d)
    (hlen : n + d - 1 ≤ xs.length)
    (L : AddSubgroup A)
    (hL : L = plusMinusSpectrumStabilizer xs n)
    (hsourceQ : PlusMinusGMOCorollary12Source (A ⧸ L)) :
    PlusMinusGMOCorollary12At xs n := by
  classical
  have hd : 1 ≤ d := by
    by_contra hnot
    have hd0 : d = 0 := by omega
    subst d
    rcases hD [] rfl with ⟨I, ⟨i, _hi⟩, _sign, _hsum⟩
    exact Fin.elim0 i
  have hnlen : n ≤ xs.length := by omega
  have hQcard : Nat.card (A ⧸ L) ≤ Nat.card A :=
    Nat.le_of_dvd Nat.card_pos L.card_quotient_dvd_card
  have hQn : Nat.card (A ⧸ L) ≤ n := hQcard.trans hn
  have hQD : PlusMinusDavenportAtMost (A ⧸ L) d :=
    plusMinusDavenportAtMost_quotient L hD
  have hQlen : n + d - 1 ≤
      (xs.map (QuotientAddGroup.mk' L)).length := by simpa using hlen
  obtain ⟨q0, hq0⟩ := hsourceQ
    (xs.map (QuotientAddGroup.mk' L)) n d hQn hQD hQlen
  have hqmem : n • q0 ∈ plusMinusExactSpectrum
      (xs.map (QuotientAddGroup.mk' L)) n :=
    (mem_plusMinusExactSpectrum_iff _ _ _).2 hq0
  rw [← image_plusMinusExactSpectrum_quotient xs n L] at hqmem
  obtain ⟨y, hy, hyq⟩ := Finset.mem_image.mp hqmem
  let z : A := quotientAddSection L q0
  have hqz : QuotientAddGroup.mk' L z = q0 := by
    simpa [z] using quotientAddSection_mk L q0
  have hdiffL : n • z - y ∈ L := by
    apply QuotientAddGroup.eq_iff_sub_mem.mp
    calc
      QuotientAddGroup.mk' L (n • z) = n • QuotientAddGroup.mk' L z := by
        rw [map_nsmul]
      _ = n • q0 := by rw [hqz]
      _ = QuotientAddGroup.mk' L y := hyq.symm
  let S := plusMinusExactSpectrum xs n
  have hSnonempty : S.Nonempty := by
    simpa [S] using plusMinusExactSpectrum_nonempty xs n hnlen
  have hdiffStab : n • z - y ∈ AddAction.stabilizer A (S : Set A) := by
    simpa [S, hL, plusMinusSpectrumStabilizer] using hdiffL
  have hdiffFin : n • z - y ∈ S.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hSnonempty]
    exact hdiffStab
  have htranslate := (Finset.mem_addStab hSnonempty).mp hdiffFin
  have htarget : n • z ∈ S := by
    have hv : (n • z - y) +ᵥ y ∈ (n • z - y) +ᵥ S :=
      Finset.vadd_mem_vadd_finset (by simpa [S] using hy)
    rw [htranslate] at hv
    simpa [vadd_eq_add, S] using hv
  exact ⟨z, (mem_plusMinusExactSpectrum_iff xs n (n • z)).1
    (by simpa [S] using htarget)⟩

/-- The DGM inequality for the literal signed occurrence setpartition, with
the canonical classical equality decision hidden in a proposition wrapper. -/
noncomputable def PlusMinusOccurrenceDGMSetpartitionBound
    (xs : List A) (n : ℕ) : Prop := by
  classical
  exact DGMSetpartitionBound (plusMinusOccurrenceSetpartition xs) n

/-- Applying the frozen General DGM statement to the literal signed
occurrence setpartition.  This is only a connector: it does not assert that
General DGM has already been proved. -/
theorem dgmSetpartitionBound_plusMinusOccurrenceSetpartition
    (hDGM : FiniteDGMSetpartitionInput A)
    (xs : List A) (n : ℕ) (hnpos : 1 ≤ n) (hn : n ≤ xs.length) :
    PlusMinusOccurrenceDGMSetpartitionBound xs n := by
  classical
  exact hDGM (plusMinusOccurrenceSetpartition xs) n
    (plusMinusOccurrenceSetpartition_nonempty xs) hnpos (by simpa using hn)

/-- The numerical part of Step 6 after the signed exact spectrum is
aperiodic.  This deliberately stops at DGM's capped-multiplicity expression;
the remaining manuscript work is the signed Davenport/counting estimate that
makes the left side reach the ambient group cardinality. -/
noncomputable def PlusMinusTrivialStabilizerDGMCount
    (xs : List A) (n : ℕ) : Prop := by
  classical
  let P := plusMinusOccurrenceSetpartition xs
  let T := layerSubsumSpectrum P n
  exact T.addStab = {0} →
    stabilizerDgmCappedMultiplicitySum T P n - n + 1 ≤ T.card

/-- General DGM gives the Step 6 capped count as soon as the exact signed
spectrum has trivial stabilizer.  General DGM remains an explicit input. -/
theorem plusMinusTrivialStabilizerDGMCount_of_generalDGM
    (hDGM : FiniteDGMSetpartitionInput A)
    (xs : List A) (n : ℕ) (hnpos : 1 ≤ n) (hn : n ≤ xs.length) :
    PlusMinusTrivialStabilizerDGMCount xs n := by
  classical
  have hbound := dgmSetpartitionBound_plusMinusOccurrenceSetpartition
    hDGM xs n hnpos hn
  unfold PlusMinusOccurrenceDGMSetpartitionBound at hbound
  unfold PlusMinusTrivialStabilizerDGMCount
  dsimp only
  intro hstab
  unfold DGMSetpartitionBound at hbound
  dsimp only at hbound
  rw [hstab] at hbound
  simpa using hbound

/-- Step 5's exact quotient fact in DGM's finite-setpartition vocabulary.
The partition is the literal list of labelled `{x,-x}` occurrence blocks;
thus this statement retains exact `n` and repeated source occurrences without
an expensive definitional conversion of the projected list spectrum.  The
conversion before quotienting is
`plusMinusExactSpectrum_eq_layerSubsumSpectrum`, and homomorphic transport is
`image_plusMinusExactSpectrum_quotient`. -/
theorem addStab_quotient_plusMinusOccurrenceSpectrum_eq_singleton
    [DecidableEq A]
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length) :
    let P := plusMinusOccurrenceSetpartition xs
    let T := layerSubsumSpectrum P n
    let H := AddAction.stabilizer A (T : Set A)
    let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
    (layerSubsumSpectrum (P.map fun B ↦ B.image q) n).addStab = {0} := by
  classical
  exact addStab_layerSubsumSpectrum_stabilizerQuotient_eq_singleton
    (plusMinusOccurrenceSetpartition xs)
    (plusMinusOccurrenceSetpartition_nonempty xs) n (by simpa using hn)

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

/-! ## Odd-order cross-type induction for the structural corollary -/

/-- When the target spectrum is aperiodic, its stabilizer quotient is
literally a relabelling of the ambient group.  Hence the DGM capped sum in
the quotient is the raw capped incidence sum of the signed layers. -/
theorem stabilizerDgmCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
    {B : Type u} [AddCommGroup B] [Fintype B] [DecidableEq B]
    (T : Finset B) (hT : T.Nonempty) (hstab : T.addStab = {0})
    (P : List (Finset B)) (n : ℕ) :
    stabilizerDgmCappedMultiplicitySum T P n =
      rawDgmCappedMultiplicitySum P n := by
  classical
  rw [← rawDgmCappedMultiplicitySum_projected T P n]
  exact rawDgmCappedMultiplicitySum_portionQuotient_eq_of_addStab_eq_singleton
    T hT hstab P n

/-- Capping each summand loses no more than capping their total. -/
theorem min_sum_le_sum_min
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ) (n : ℕ) :
    min n (∑ x ∈ s, f x) ≤ ∑ x ∈ s, min n (f x) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      simp only [Finset.sum_insert hx]
      have hpair : min n (f x + ∑ y ∈ s, f y) ≤
          min n (f x) + min n (∑ y ∈ s, f y) := by
        by_cases hfx : n ≤ f x
        · rw [min_eq_left hfx,
            min_eq_left (hfx.trans (Nat.le_add_right _ _))]
          exact Nat.le_add_right _ _
        · have hfx' : f x ≤ n := Nat.le_of_lt (Nat.lt_of_not_ge hfx)
          rw [min_eq_right hfx']
          by_cases hs : n ≤ ∑ y ∈ s, f y
          · rw [min_eq_left hs]
            exact (min_le_left _ _).trans (Nat.le_add_left n (f x))
          · have hs' : (∑ y ∈ s, f y) ≤ n :=
              Nat.le_of_lt (Nat.lt_of_not_ge hs)
            rw [min_eq_right hs']
            exact min_le_right _ _
      exact hpair.trans (Nat.add_le_add_left ih _)

/-- If a finite family has total mass `2*r` and no coordinate exceeds `r`,
then truncating every coordinate at `n` retains at least `2*min n r`.
This is the elementary two-bin estimate behind the nonzero signed pairs. -/
theorem two_mul_min_le_sum_min_of_sum_eq_two_mul
    {ι : Type*} [DecidableEq ι] (s : Finset ι) (f : ι → ℕ)
    (n r : ℕ) (htotal : ∑ x ∈ s, f x = 2 * r)
    (hmax : ∀ x ∈ s, f x ≤ r) :
    2 * min n r ≤ ∑ x ∈ s, min n (f x) := by
  by_cases hrn : r ≤ n
  · rw [min_eq_right hrn]
    have hcap : ∀ x ∈ s, min n (f x) = f x := by
      intro x hx
      rw [min_eq_right ((hmax x hx).trans hrn)]
    have hsumcap : (∑ x ∈ s, min n (f x)) = ∑ x ∈ s, f x := by
      apply Finset.sum_congr rfl
      intro x hx
      exact hcap x hx
    rw [hsumcap, htotal]
  · have hnr : n ≤ r := Nat.le_of_lt (Nat.lt_of_not_ge hrn)
    rw [min_eq_left hnr]
    by_cases hheavy : ∃ x ∈ s, n ≤ f x
    · obtain ⟨x, hxs, hnx⟩ := hheavy
      have hrest : n ≤ ∑ y ∈ s.erase x, f y := by
        have hsplit : f x + ∑ y ∈ s.erase x, f y = 2 * r := by
          have herase := s.sum_erase_add f hxs
          omega
        have hxr := hmax x hxs
        omega
      have hrestCap : n ≤ ∑ y ∈ s.erase x, min n (f y) := by
        exact (by simpa [min_eq_left hrest] using
          (min_sum_le_sum_min (s.erase x) f n))
      rw [← Finset.sum_erase_add _ (fun y ↦ min n (f y)) hxs,
        min_eq_left hnx]
      omega
    · push_neg at hheavy
      have hcap : ∀ x ∈ s, min n (f x) = f x := by
        intro x hx
        rw [min_eq_right (Nat.le_of_lt (hheavy x hx))]
      calc
        2 * n ≤ 2 * r := Nat.mul_le_mul_left 2 hnr
        _ = ∑ x ∈ s, f x := htotal.symm
        _ = ∑ x ∈ s, min n (f x) := by
          apply Finset.sum_congr rfl
          intro x hx
          exact (hcap x hx).symm

/-- Adding a source head changes the labelled zero-occurrence count by one
exactly when that head is zero.  The proof explicitly reindexes tail
occurrences, so it does not identify repeated values. -/
theorem card_plusMinusZeroOccurrences_cons [DecidableEq A]
    (x : A) (xs : List A) :
    (plusMinusZeroOccurrences (x :: xs)).card =
      (if x = 0 then 1 else 0) + (plusMinusZeroOccurrences xs).card := by
  classical
  let p : Fin (xs.length + 1) → Prop := fun i ↦
    occurrenceValue (x :: xs) i = 0
  have hwhole : plusMinusZeroOccurrences (x :: xs) =
      Finset.univ.filter p := by
    ext i
    simp [plusMinusZeroOccurrences, p]
  have htail : (Finset.univ.filter fun i : Fin xs.length ↦ p i.succ) =
      plusMinusZeroOccurrences xs := by
    ext i
    simp [plusMinusZeroOccurrences, p, occurrenceValue]
  rw [hwhole, Fin.card_filter_univ_succ', htail]
  by_cases hx : x = 0 <;> simp [p, occurrenceValue, hx]

/-- The labelled zero-occurrence finset has the corresponding Boolean list
count.  This is used only as a counting bridge; the selected object remains
the occurrence finset above. -/
theorem card_plusMinusZeroOccurrences_eq_countP [DecidableEq A]
    (xs : List A) :
    (plusMinusZeroOccurrences xs).card =
      xs.countP fun x ↦ decide (x = 0) := by
  induction xs with
  | nil =>
      have hempty : plusMinusZeroOccurrences ([] : List A) = ∅ := by
        ext i
        exact Fin.elim0 i
      rw [hempty]
      simp
  | cons x xs ih =>
      rw [card_plusMinusZeroOccurrences_cons]
      by_cases hx : x = 0 <;>
        simp [List.countP_cons, ih, hx, Nat.add_comm]

/-- Raw multiplicity in the signed occurrence layers is the number of source
positions whose `{x,-x}` block contains the requested value. -/
theorem rawLayerMultiplicity_plusMinusOccurrenceSetpartition
    [DecidableEq A] (xs : List A) (y : A) :
    rawLayerMultiplicity (plusMinusOccurrenceSetpartition xs) y =
      xs.countP fun x ↦ decide (y = x ∨ y = -x) := by
  induction xs with
  | nil => simp [rawLayerMultiplicity]
  | cons x xs ih =>
      rw [plusMinusOccurrenceSetpartition_cons]
      by_cases hy : y = x ∨ y = -x
      · have hmem : y ∈ plusMinusValueBlock x := by
          simpa [plusMinusValueBlock] using hy
        rw [rawLayerMultiplicity_cons_of_mem _ _ _ hmem, ih]
        simp [hy, Nat.add_comm]
      · have hmem : y ∉ plusMinusValueBlock x := by
          simpa [plusMinusValueBlock] using hy
        rw [rawLayerMultiplicity_cons_of_not_mem _ _ _ hmem, ih]
        simp [hy]

/-- At zero, raw signed-layer multiplicity is exactly the number of labelled
zero source occurrences. -/
theorem rawLayerMultiplicity_zero_plusMinusOccurrenceSetpartition
    [DecidableEq A] (xs : List A) :
    rawLayerMultiplicity (plusMinusOccurrenceSetpartition xs) 0 =
      (plusMinusZeroOccurrences xs).card := by
  rw [rawLayerMultiplicity_plusMinusOccurrenceSetpartition,
    card_plusMinusZeroOccurrences_eq_countP]
  apply List.countP_congr
  intro x _hx
  simp [eq_comm]

/-- A nonzero signed value can occur only in a nonzero source block, so its
raw layer multiplicity is bounded by the number of nonzero occurrences. -/
theorem rawLayerMultiplicity_le_nonzeroCount
    [DecidableEq A] (xs : List A) {y : A} (hy : y ≠ 0) :
    rawLayerMultiplicity (plusMinusOccurrenceSetpartition xs) y ≤
      xs.countP fun x ↦ !(decide (x = 0)) := by
  rw [rawLayerMultiplicity_plusMinusOccurrenceSetpartition]
  apply List.countP_mono_left
  intro x _hx hmem
  simp only [decide_eq_true_eq] at hmem ⊢
  rcases hmem with hxy | hxy
  · have hx0 : x ≠ 0 := by
      intro hx
      exact hy (hxy.trans hx)
    simp [hx0]
  · have hx0 : x ≠ 0 := by
      intro hx
      apply hy
      rw [hxy, hx, neg_zero]
    simp [hx0]

/-- Zero and nonzero Boolean counts partition the labelled source list. -/
theorem countP_zero_add_countP_nonzero [DecidableEq A] (xs : List A) :
    xs.countP (fun x ↦ decide (x = 0)) +
      xs.countP (fun x ↦ !(decide (x = 0))) = xs.length := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      rw [List.countP_cons, List.countP_cons, List.length_cons]
      by_cases hx : x = 0 <;> simp [hx] <;> omega

/-- The total cardinality of the signed blocks, before eliminating the two
Boolean source counts. -/
theorem sum_card_plusMinusOccurrenceSetpartition_eq_counts
    [DecidableEq A] (hodd : Odd (Nat.card A)) (xs : List A) :
    ((plusMinusOccurrenceSetpartition xs).map Finset.card).sum =
      xs.countP (fun x ↦ decide (x = 0)) +
        2 * xs.countP (fun x ↦ !(decide (x = 0))) := by
  induction xs with
  | nil => simp [plusMinusOccurrenceSetpartition]
  | cons x xs ih =>
      rw [plusMinusOccurrenceSetpartition_cons, List.map_cons, List.sum_cons]
      by_cases hx : x = 0
      · subst x
        simp [plusMinusValueBlock, ih, List.countP_cons]
        omega
      · have hne : x ≠ -x := by
          intro h
          exact hx (eq_zero_of_neg_eq_self_of_natCard_odd hodd h.symm)
        have hcard : (plusMinusValueBlock x).card = 2 := by
          simp [plusMinusValueBlock, hne]
        rw [hcard]
        simp [hx, ih, List.countP_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm]
        omega

/-- In odd order, total incidence of the signed occurrence blocks is one for
each zero occurrence and two for every nonzero occurrence. -/
theorem sum_card_plusMinusOccurrenceSetpartition
    [DecidableEq A] (hodd : Odd (Nat.card A)) (xs : List A) :
    ((plusMinusOccurrenceSetpartition xs).map Finset.card).sum =
      (plusMinusZeroOccurrences xs).card +
        2 * (xs.length - (plusMinusZeroOccurrences xs).card) := by
  have hcounts := countP_zero_add_countP_nonzero xs
  have hsum := sum_card_plusMinusOccurrenceSetpartition_eq_counts hodd xs
  rw [← card_plusMinusZeroOccurrences_eq_countP xs] at hcounts hsum
  omega

/-- Removing zero from the ambient finite sum leaves total nonzero raw
signed-layer multiplicity equal to twice the nonzero occurrence count. -/
theorem sum_rawLayerMultiplicity_erase_zero_plusMinus
    [DecidableEq A] (hodd : Odd (Nat.card A)) (xs : List A) :
    (∑ y ∈ (Finset.univ.erase (0 : A)),
        rawLayerMultiplicity (plusMinusOccurrenceSetpartition xs) y) =
      2 * (xs.length - (plusMinusZeroOccurrences xs).card) := by
  have htotal := sum_rawLayerMultiplicity
    (plusMinusOccurrenceSetpartition xs)
  rw [sum_card_plusMinusOccurrenceSetpartition hodd xs] at htotal
  have hzero := rawLayerMultiplicity_zero_plusMinusOccurrenceSetpartition xs
  have hsplit := (Finset.univ : Finset A).sum_erase_add
    (fun y ↦ rawLayerMultiplicity (plusMinusOccurrenceSetpartition xs) y)
    (Finset.mem_univ (0 : A))
  omega

/-- The one remaining local branch after the proved Step 4 and Step 5
reductions: odd ambient group and trivial stabilizer.  General DGM is explicit
and the statement retains the full signed Davenport and source-length
quantifiers.  This is a narrow Step 6 boundary, not a restatement of the
whole source theorem. -/
def OddPlusMinusTrivialStabilizerStep
    (B : Type u) [AddCommGroup B] [Fintype B] : Prop :=
  FiniteDGMSetpartitionInput B →
    ∀ (xs : List B) (n d : ℕ),
      Odd (Nat.card B) →
      Nat.card B ≤ n →
      PlusMinusDavenportAtMost B d →
      n + d - 1 ≤ xs.length →
      plusMinusSpectrumStabilizer xs n = ⊥ →
      PlusMinusGMOCorollary13At xs n

/-- The elementary capped-incidence estimate left by the odd-order Step 6
specialization.  Nonzero signed cells occur in disjoint negation pairs and
contribute twice; zero cells contribute once.  The hypothesis that the exact
spectrum is aperiodic prevents quotient layers from identifying these values.
This statement contains no GMO conclusion. -/
noncomputable def OddSignedCappedMultiplicityEstimate
    (B : Type u) [AddCommGroup B] [Fintype B] : Prop := by
  classical
  exact ∀ (xs : List B) (n : ℕ),
      Odd (Nat.card B) →
      let P := plusMinusOccurrenceSetpartition xs
      let T := layerSubsumSpectrum P n
      T.addStab = {0} →
      n ≤ xs.length →
        min n (plusMinusZeroOccurrences xs).card +
            2 * min n (xs.length - (plusMinusZeroOccurrences xs).card) ≤
          stabilizerDgmCappedMultiplicitySum T P n

/-- The odd signed capped-incidence estimate is unconditional in the valid
exact-layer range.  It is a finite counting theorem: zero contributes one
incidence, nonzero values occur in negation-paired bins of total mass twice
the nonzero occurrence count, and no one bin exceeds that count. -/
theorem oddSignedCappedMultiplicityEstimate
    {B : Type u} [AddCommGroup B] [Fintype B] :
    OddSignedCappedMultiplicityEstimate B := by
  classical
  intro xs n hodd
  dsimp only
  intro hstab hnlen
  let P := plusMinusOccurrenceSetpartition xs
  let T := layerSubsumSpectrum P n
  let z := (plusMinusZeroOccurrences xs).card
  let r := xs.length - z
  have hTnonempty : T.Nonempty := by
    simpa [T, P, ← plusMinusExactSpectrum_eq_layerSubsumSpectrum] using
      plusMinusExactSpectrum_nonempty xs n hnlen
  have hraw : stabilizerDgmCappedMultiplicitySum T P n =
      rawDgmCappedMultiplicitySum P n :=
    stabilizerDgmCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
      T hTnonempty hstab P n
  have hzero : rawLayerMultiplicity P 0 = z := by
    simpa [P, z] using
      rawLayerMultiplicity_zero_plusMinusOccurrenceSetpartition xs
  have hcounts := countP_zero_add_countP_nonzero xs
  rw [← card_plusMinusZeroOccurrences_eq_countP xs] at hcounts
  have hnonzeroCount :
      xs.countP (fun x ↦ !(decide (x = 0))) = r := by
    dsimp only [z, r]
    omega
  let s : Finset B := Finset.univ.erase 0
  let f : B → ℕ := fun y ↦ rawLayerMultiplicity P y
  have htotal : ∑ y ∈ s, f y = 2 * r := by
    simpa [s, f, P, r, z] using
      sum_rawLayerMultiplicity_erase_zero_plusMinus hodd xs
  have hmax : ∀ y ∈ s, f y ≤ r := by
    intro y hy
    have hy0 : y ≠ 0 := by simpa [s] using hy
    have hle := rawLayerMultiplicity_le_nonzeroCount xs hy0
    simpa [f, P, hnonzeroCount] using hle
  have hpair : 2 * min n r ≤ ∑ y ∈ s, min n (f y) :=
    two_mul_min_le_sum_min_of_sum_eq_two_mul s f n r htotal hmax
  rw [hraw]
  unfold rawDgmCappedMultiplicitySum
  have hsplit := (Finset.univ : Finset B).sum_erase_add
    (fun y ↦ min n (rawLayerMultiplicity P y)) (Finset.mem_univ (0 : B))
  dsimp only [s, f] at hpair
  rw [hzero] at hsplit
  simp only [z, r] at hpair
  omega

/-- The small-zero half of odd Step 6 is literally the full-spectrum branch.
This formulation is separated out because Corollary 1.2 consumes fullness,
whereas Corollary 1.3 packages it in a disjunction. -/
theorem plusMinusExactSpectrum_eq_univ_of_odd_trivialStab_smallZero
    {B : Type u} [AddCommGroup B] [Fintype B]
    (hDGM : FiniteDGMSetpartitionInput B)
    (xs : List B) (n d : ℕ)
    (hodd : Odd (Nat.card B))
    (hn : Nat.card B ≤ n)
    (hD : PlusMinusDavenportAtMost B d)
    (hlen : n + d - 1 ≤ xs.length)
    (hstab : plusMinusSpectrumStabilizer xs n = ⊥)
    (hsmall : ¬ xs.length - Nat.card B + 2 ≤
      (plusMinusZeroOccurrences xs).card) :
    plusMinusExactSpectrum xs n = Finset.univ := by
  classical
  let P := plusMinusOccurrenceSetpartition xs
  let T := layerSubsumSpectrum P n
  have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hD
  have hnlen : n ≤ xs.length := by omega
  have hTstab : T.addStab = {0} := by
    have hTeq : T = plusMinusExactSpectrum xs n := by
      simpa [T, P] using
        (plusMinusExactSpectrum_eq_layerSubsumSpectrum xs n).symm
    rw [hTeq]
    ext x
    rw [← Finset.mem_coe,
      Finset.coe_addStab (plusMinusExactSpectrum_nonempty xs n hnlen)]
    change x ∈ AddAction.stabilizer B
        (plusMinusExactSpectrum xs n : Set B) ↔ x ∈ ({0} : Finset B)
    rw [← plusMinusSpectrumStabilizer, hstab]
    simp
  have hzsmall : (plusMinusZeroOccurrences xs).card ≤
      xs.length - Nat.card B + 1 := by omega
  have hcap := oddSignedCappedMultiplicityEstimate xs n hodd hTstab hnlen
  have hE : n + Nat.card B - 1 ≤
      min n (plusMinusZeroOccurrences xs).card +
        2 * min n (xs.length - (plusMinusZeroOccurrences xs).card) := by
    by_cases hzN : (plusMinusZeroOccurrences xs).card ≤ n
    · rw [min_eq_right hzN]
      by_cases hrN : xs.length - (plusMinusZeroOccurrences xs).card ≤ n
      · rw [min_eq_right hrN]
        omega
      · rw [min_eq_left (Nat.le_of_not_ge hrN)]
        omega
    · rw [min_eq_left (Nat.le_of_not_ge hzN)]
      by_cases hrN : xs.length - (plusMinusZeroOccurrences xs).card ≤ n
      · rw [min_eq_right hrN]
        omega
      · rw [min_eq_left (Nat.le_of_not_ge hrN)]
        omega
  have hbound := dgmSetpartitionBound_plusMinusOccurrenceSetpartition
    hDGM xs n (Nat.card_pos.trans_le hn) hnlen
  unfold PlusMinusOccurrenceDGMSetpartitionBound at hbound
  unfold DGMSetpartitionBound at hbound
  dsimp only at hbound
  have hstabCard :
      (layerSubsumSpectrum (plusMinusOccurrenceSetpartition xs) n).addStab.card = 1 := by
    rw [hTstab]
    simp
  rw [hstabCard, Nat.mul_one] at hbound
  have hTcard : Nat.card B ≤ T.card := by
    have hcapped : n + Nat.card B - 1 ≤
        stabilizerDgmCappedMultiplicitySum T P n := hE.trans hcap
    dsimp only [T, P]
    dsimp only [T, P] at hcapped
    omega
  rw [plusMinusExactSpectrum_eq_layerSubsumSpectrum]
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [T, P, Nat.card_eq_fintype_card] using hTcard

/-- General DGM plus the elementary odd signed-cell capped estimate closes
the entire trivial-stabilizer Step 6.  If enough zero cells exist, `K = 0`
is the required paired concentration.  Otherwise the DGM lower bound reaches
the ambient cardinality, forcing the exact spectrum to be full. -/
theorem oddPlusMinusTrivialStabilizerStep_of_cappedEstimate
    {B : Type u} [AddCommGroup B] [Fintype B]
    (hestimate : OddSignedCappedMultiplicityEstimate B) :
    OddPlusMinusTrivialStabilizerStep B := by
  intro hDGM xs n d hodd hn hD hlen hstab
  classical
  unfold OddSignedCappedMultiplicityEstimate at hestimate
  by_cases hsub : Subsingleton B
  · exact (@plusMinusGMOSourcePackage_of_subsingleton
      B inferInstance inferInstance hsub).2 xs n d hn hD hlen
  · let P := plusMinusOccurrenceSetpartition xs
    let T := layerSubsumSpectrum P n
    let z := (plusMinusZeroOccurrences xs).card
    have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hD
    have hnlen : n ≤ xs.length := by omega
    have hTnonempty : T.Nonempty := by
      simpa [T, P, ← plusMinusExactSpectrum_eq_layerSubsumSpectrum] using
        plusMinusExactSpectrum_nonempty xs n hnlen
    have hTstab : T.addStab = {0} := by
      have hTeq : T = plusMinusExactSpectrum xs n := by
        simpa [T, P] using
          (plusMinusExactSpectrum_eq_layerSubsumSpectrum xs n).symm
      rw [hTeq]
      ext x
      rw [← Finset.mem_coe,
        Finset.coe_addStab (plusMinusExactSpectrum_nonempty xs n hnlen)]
      change x ∈ AddAction.stabilizer B
          (plusMinusExactSpectrum xs n : Set B) ↔ x ∈ ({0} : Finset B)
      rw [← plusMinusSpectrumStabilizer, hstab]
      simp
    by_cases hlarge : xs.length - Nat.card B + 2 ≤ z
    · letI : Nontrivial B := not_subsingleton_iff_nontrivial.mp hsub
      let selected : Selection xs := plusMinusZeroOccurrences xs
      have hpaired : PlusMinusPairedCosetCertificate xs := {
        K := ⊥
        strict := bot_lt_top
        beta := 0
        selected := selected
        signedBlockCoset := by
          intro i hi y hy
          have hzero : occurrenceValue xs i = 0 := by
            exact (mem_plusMinusZeroOccurrences_iff xs i).1
              (by simpa [selected] using hi)
          have hyzero : y = 0 := by
            simpa [plusMinusOccurrenceBlock, plusMinusValueBlock, hzero] using hy
          simp [hyzero]
        card_lower := by
          have hqbot : Nat.card (B ⧸ (⊥ : AddSubgroup B)) = Nat.card B :=
            ConcreteGDihedral.natCard_quotient_bot
          rw [hqbot]
          simpa [selected, z] using hlarge
      }
      obtain ⟨hgmo⟩ := hpaired.toGMOConcentration
      exact Or.inr
        (corollary13Concentration_of_plusMinusGMOConcentration hgmo)
    · have hzsmall : z ≤ xs.length - Nat.card B + 1 := by omega
      have hcap := hestimate xs n hodd hTstab hnlen
      dsimp only [P, T, z] at hzsmall hcap ⊢
      have hE : n + Nat.card B - 1 ≤
          min n (plusMinusZeroOccurrences xs).card +
            2 * min n (xs.length - (plusMinusZeroOccurrences xs).card) := by
        by_cases hzN : (plusMinusZeroOccurrences xs).card ≤ n
        · rw [min_eq_right hzN]
          by_cases hrN : xs.length - (plusMinusZeroOccurrences xs).card ≤ n
          · rw [min_eq_right hrN]
            omega
          · rw [min_eq_left (Nat.le_of_not_ge hrN)]
            omega
        · rw [min_eq_left (Nat.le_of_not_ge hzN)]
          by_cases hrN : xs.length - (plusMinusZeroOccurrences xs).card ≤ n
          · rw [min_eq_right hrN]
            omega
          · rw [min_eq_left (Nat.le_of_not_ge hrN)]
            omega
      have hbound := dgmSetpartitionBound_plusMinusOccurrenceSetpartition
        hDGM xs n (Nat.card_pos.trans_le hn) hnlen
      unfold PlusMinusOccurrenceDGMSetpartitionBound at hbound
      unfold DGMSetpartitionBound at hbound
      dsimp only at hbound
      have hstabCard :
          (layerSubsumSpectrum (plusMinusOccurrenceSetpartition xs) n).addStab.card = 1 := by
        rw [hTstab]
        simp
      rw [hstabCard, Nat.mul_one] at hbound
      have hTcard : Nat.card B ≤ T.card := by
        have hcapped : n + Nat.card B - 1 ≤
            stabilizerDgmCappedMultiplicitySum T P n := hE.trans hcap
        dsimp only [T, P]
        dsimp only [T, P] at hcapped
        omega
      apply Or.inl
      rw [plusMinusExactSpectrum_eq_layerSubsumSpectrum]
      apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
      simpa [Nat.card_eq_fintype_card] using hTcard

/-- Odd-order Step 6 with its last capped-incidence boundary discharged. -/
theorem oddPlusMinusTrivialStabilizerStep
    {B : Type u} [AddCommGroup B] [Fintype B] :
    OddPlusMinusTrivialStabilizerStep B :=
  oddPlusMinusTrivialStabilizerStep_of_cappedEstimate
    oddSignedCappedMultiplicityEstimate

/-- Quotienting by a nontrivial finite subgroup strictly lowers cardinality.
This is the well-founded measure needed for the Step 5 quotient call. -/
theorem natCard_quotient_lt_of_bot_lt
    {B : Type u} [AddCommGroup B] [Fintype B]
    (L : AddSubgroup B) (hL : ⊥ < L) :
    Nat.card (B ⧸ L) < Nat.card B := by
  have hLcard : 2 ≤ Nat.card L := by
    have hcardlt : Nat.card (⊥ : AddSubgroup B) < Nat.card L :=
      natCard_lt_of_addSubgroup_lt hL
    have hbotcard : Nat.card (⊥ : AddSubgroup B) = 1 := by simp
    rw [hbotcard] at hcardlt
    omega
  have hqpos : 0 < Nat.card (B ⧸ L) := Nat.card_pos
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup L
  nlinarith

/-- All Steps 4 and 5 are discharged here by strong induction on the
cardinality of *arbitrary types in the same universe*.  Thus both a strict
subgroup and a proper quotient are legitimate recursive calls.  Only the
precise odd/trivial-stabilizer Step 6 boundary remains an input. -/
theorem plusMinusCorollary13Source_of_oddStep6
    (hDGM : ∀ (B : Type u) [AddCommGroup B] [Fintype B],
      FiniteDGMSetpartitionInput B)
    (hstep6 : ∀ (B : Type u) [AddCommGroup B] [Fintype B],
      OddPlusMinusTrivialStabilizerStep B)
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    PlusMinusGMOCorollary13Source B := by
  have outer : ∀ m : ℕ,
      ∀ (C : Type u) [AddCommGroup C] [Fintype C],
        Nat.card C = m → Odd m → PlusMinusGMOCorollary13Source C := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro C _instC _finC hcardC hoddm
        have hoddC : Odd (Nat.card C) := by
          rw [hcardC]
          exact hoddm
        intro xs n d hn hDC hlen
        by_cases hsub : Subsingleton C
        · exact (@plusMinusGMOSourcePackage_of_subsingleton
            C _instC _finC hsub).2 xs n d hn hDC hlen
        · let L : AddSubgroup C := plusMinusSpectrumStabilizer xs n
          by_cases htop : L = ⊤
          · have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hDC
            have hnlen : n ≤ xs.length := by omega
            exact Or.inl
              (plusMinusExactSpectrum_eq_univ_of_stabilizer_eq_top
                xs n hnlen (by simpa [L] using htop))
          · have hLtop : L < ⊤ := lt_top_iff_ne_top.mpr htop
            by_cases hbot : L = ⊥
            · exact hstep6 C (hDGM C) xs n d hoddC hn hDC hlen
                (by simpa [L] using hbot)
            · have hLpos : ⊥ < L := bot_lt_iff_ne_bot.mpr hbot
              have hqcardlt : Nat.card (C ⧸ L) < m := by
                rw [← hcardC]
                exact natCard_quotient_lt_of_bot_lt L hLpos
              have hqodd : Odd (Nat.card (C ⧸ L)) :=
                odd_natCard_quotient_of_odd_natCard L hoddC
              have hsourceQ : PlusMinusGMOCorollary13Source (C ⧸ L) :=
                ih (Nat.card (C ⧸ L)) hqcardlt (C ⧸ L) rfl hqodd
              exact plusMinusCorollary13At_of_stabilizerQuotientSource
                xs n d hn hDC hlen L rfl hsourceQ
  exact outer (Nat.card B) B rfl hodd

/-- Odd-order prescribed-target source theorem.  The same cardinal
strong-induction handles proper stabilizers through quotient target lifting.
At trivial stabilizer, small zero multiplicity forces fullness by DGM, while
large zero multiplicity is the proved maximal signed-zero extraction plus
zero padding. -/
theorem plusMinusCorollary12Source_of_oddDGM
    (hDGM : ∀ (C : Type u) [AddCommGroup C] [Fintype C],
      FiniteDGMSetpartitionInput C)
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    PlusMinusGMOCorollary12Source B := by
  have outer : ∀ m : ℕ,
      ∀ (C : Type u) [AddCommGroup C] [Fintype C],
        Nat.card C = m → Odd m → PlusMinusGMOCorollary12Source C := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro C _instC _finC hcardC hoddm
        have hoddC : Odd (Nat.card C) := by
          rw [hcardC]
          exact hoddm
        intro xs n d hn hDC hlen
        by_cases hsub : Subsingleton C
        · exact (@plusMinusGMOSourcePackage_of_subsingleton
            C _instC _finC hsub).1 xs n d hn hDC hlen
        · let L : AddSubgroup C := plusMinusSpectrumStabilizer xs n
          have hd : 1 ≤ d := one_le_of_plusMinusDavenportAtMost hDC
          have hnlen : n ≤ xs.length := by omega
          by_cases htop : L = ⊤
          · have hfull := plusMinusExactSpectrum_eq_univ_of_stabilizer_eq_top
                xs n hnlen (by simpa [L] using htop)
            refine ⟨0, (mem_plusMinusExactSpectrum_iff xs n (n • (0 : C))).1 ?_⟩
            rw [hfull]
            simp
          · by_cases hbot : L = ⊥
            · by_cases hlarge : xs.length - Nat.card C + 2 ≤
                  (plusMinusZeroOccurrences xs).card
              · have hzD : d ≤ (plusMinusZeroOccurrences xs).card := by
                  omega
                have hzero := hasPlusMinusSumOfCard_zero_of_many_zeroOccurrences
                  xs n d hDC hlen hzD
                refine ⟨0, ?_⟩
                simpa using hzero
              · have hfull :=
                  plusMinusExactSpectrum_eq_univ_of_odd_trivialStab_smallZero
                    (hDGM C) xs n d hoddC hn hDC hlen
                    (by simpa [L] using hbot) hlarge
                refine ⟨0,
                  (mem_plusMinusExactSpectrum_iff xs n (n • (0 : C))).1 ?_⟩
                rw [hfull]
                simp
            · have hLpos : ⊥ < L := bot_lt_iff_ne_bot.mpr hbot
              have hqcardlt : Nat.card (C ⧸ L) < m := by
                rw [← hcardC]
                exact natCard_quotient_lt_of_bot_lt L hLpos
              have hqodd : Odd (Nat.card (C ⧸ L)) :=
                odd_natCard_quotient_of_odd_natCard L hoddC
              have hsourceQ : PlusMinusGMOCorollary12Source (C ⧸ L) :=
                ih (Nat.card (C ⧸ L)) hqcardlt (C ⧸ L) rfl hqodd
              exact plusMinusCorollary12At_of_stabilizerQuotientSource
                xs n d hn hDC hlen L rfl hsourceQ
  exact outer (Nat.card B) B rfl hodd

/-- The exact odd-order `{±1}` source package needed by the 13-page draft,
conditional only on the separately formalized General DGM input. -/
theorem plusMinusGMOSourcePackage_of_oddDGM
    (hDGM : ∀ (C : Type u) [AddCommGroup C] [Fintype C],
      FiniteDGMSetpartitionInput C)
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    PlusMinusGMOSourcePackage B := by
  exact ⟨plusMinusCorollary12Source_of_oddDGM hDGM B hodd,
    plusMinusCorollary13Source_of_oddStep6 hDGM
      (fun _C _group _finite ↦ oddPlusMinusTrivialStabilizerStep) B hodd⟩

/-- The odd-order structural provider, with all subgroup instances obtained
from the same cross-type induction rather than from the insufficient fixed
ambient subgroup scheduler. -/
theorem oddPlusMinusStructuralProviders_of_step6
    (hDGM : ∀ (B : Type u) [AddCommGroup B] [Fintype B],
      FiniteDGMSetpartitionInput B)
    (hstep6 : ∀ (B : Type u) [AddCommGroup B] [Fintype B],
      OddPlusMinusTrivialStabilizerStep B)
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    PlusMinusGMOStructuralProvider B ∧
      ∀ K : AddSubgroup B, PlusMinusGMOStructuralProvider K := by
  have hsourceB := plusMinusCorollary13Source_of_oddStep6
    hDGM hstep6 B hodd
  refine ⟨plusMinusGMOStructuralProvider_of_corollary13Source hsourceB, ?_⟩
  intro K
  have hoddK : Odd (Nat.card K) :=
    Odd.of_dvd_nat hodd (AddSubgroup.card_addSubgroup_dvd_card K)
  exact plusMinusGMOStructuralProvider_of_corollary13Source
    (plusMinusCorollary13Source_of_oddStep6 hDGM hstep6 K hoddK)

/-- For odd finite groups, General DGM now supplies the ambient and every
subgroup structural GMO provider with no signed-Theorem-1.1 local interface
left over.  Oddness passes to subgroups and quotients inside the proved
cross-type scheduler. -/
theorem oddPlusMinusStructuralProviders
    (hDGM : ∀ (C : Type u) [AddCommGroup C] [Fintype C],
      FiniteDGMSetpartitionInput C)
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    PlusMinusGMOStructuralProvider B ∧
      ∀ K : AddSubgroup B, PlusMinusGMOStructuralProvider K :=
  oddPlusMinusStructuralProviders_of_step6 hDGM
    (fun _C _group _finite ↦ oddPlusMinusTrivialStabilizerStep)
    B hodd

/-- Final provider elimination for the odd-order specialization: prescribed
signed target, ambient structural GMO, and structural GMO in every subgroup.
No ordinary Davenport shortcut is used. -/
theorem oddPlusMinusGMOProviders
    (hDGM : ∀ (C : Type u) [AddCommGroup C] [Fintype C],
      FiniteDGMSetpartitionInput C)
    (B : Type u) [AddCommGroup B] [Fintype B]
    (hodd : Odd (Nat.card B)) :
    WeightedGMOPrescribedLengthProvider B ∧
      PlusMinusGMOStructuralProvider B ∧
      (∀ K : AddSubgroup B, PlusMinusGMOStructuralProvider K) := by
  have hpackage := plusMinusGMOSourcePackage_of_oddDGM hDGM B hodd
  have hstruct := oddPlusMinusStructuralProviders hDGM B hodd
  exact ⟨weightedGMOPrescribedLengthProvider_of_corollary12Source hpackage.1,
    hstruct.1, hstruct.2⟩

end GaoLean

#print axioms GaoLean.theorem11_singleLayer_membership_is_not_paired_containment
#print axioms GaoLean.hasNonemptyPlusMinusZeroSum_of_take
#print axioms GaoLean.plusMinusDavenportAtLeast_of_atMost
#print axioms GaoLean.PlusMinusPairedCosetCertificate.center_mem_and_selectedValues_mem_of_odd
#print axioms GaoLean.dgmSetpartitionBound_plusMinusOccurrenceSetpartition
#print axioms GaoLean.plusMinusTrivialStabilizerDGMCount_of_generalDGM
#print axioms GaoLean.addStab_quotient_plusMinusOccurrenceSpectrum_eq_singleton
#print axioms GaoLean.theorem21SetPartition_sumset_subset_plusMinusExactSpectrum
#print axioms GaoLean.PlusMinusTheorem21FullCertificate.fullSpectrum
#print axioms GaoLean.plusMinusTheorem11StepEndpoints_of_residual
#print axioms GaoLean.plusMinusTheorem11StepEndpoints_of_subsingleton
#print axioms GaoLean.plusMinusGMOSourcePackage_of_theorem11StepEndpoints
#print axioms GaoLean.plusMinusGMOSources_of_theorem11Induction
#print axioms GaoLean.plusMinusGMOProviders_of_theorem11Induction
#print axioms GaoLean.hasPlusMinusSumOfCard_zero_of_many_zeroOccurrences
#print axioms GaoLean.plusMinusCorollary12At_of_stabilizerQuotientSource
#print axioms GaoLean.oddSignedCappedMultiplicityEstimate
#print axioms GaoLean.plusMinusExactSpectrum_eq_univ_of_odd_trivialStab_smallZero
#print axioms GaoLean.oddPlusMinusTrivialStabilizerStep
#print axioms GaoLean.plusMinusCorollary12Source_of_oddDGM
#print axioms GaoLean.plusMinusGMOSourcePackage_of_oddDGM
#print axioms GaoLean.oddPlusMinusStructuralProviders
#print axioms GaoLean.oddPlusMinusGMOProviders
