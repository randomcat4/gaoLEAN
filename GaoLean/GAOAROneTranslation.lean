import GaoLean.PGRotationExtraction

/-!
# GAO-AR one-translation completion

This file packages the exact occurrence calculation used at both quotient
reductions in the arbitrary-rank manuscript.  It then combines the second
completion in the translated sequence with the already checked
occurrence-preserving translation pullback.
-/

namespace GaoLean

/-- The exponential estimate used in the heavy-support population argument. -/
theorem three_pow_strict_quadratic (r : ℕ) (hr : 4 ≤ r) :
    2 * (r - 1) ^ 2 < 3 * 3 ^ (r - 2) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have hquad : 2 * r ^ 2 ≤ 3 * (2 * (r - 1) ^ 2) := by
        have hrEq : r = (r - 1) + 1 := by omega
        conv_lhs => rw [hrEq]
        nlinarith [show 3 ≤ r - 1 by omega]
      have hmul :
          3 * (2 * (r - 1) ^ 2) < 3 * (3 * 3 ^ (r - 2)) :=
        Nat.mul_lt_mul_of_pos_left ih (by omega)
      have hexp : (r + 1) - 2 = (r - 2) + 1 := by omega
      calc
        2 * ((r + 1) - 1) ^ 2 = 2 * r ^ 2 := by congr 2 <;> omega
        _ ≤ 3 * (2 * (r - 1) ^ 2) := hquad
        _ < 3 * (3 * 3 ^ (r - 2)) := hmul
        _ = 3 * 3 ^ ((r + 1) - 2) := by rw [hexp, pow_succ]; ring

/-- Uniform exponential inequality from the manuscript's heavy-population
count.  It is valid for every `q ≥ 3`, with no relation bounding `r` by `q`. -/
theorem uniformHeavySupportExponentialInequality
    (q r : ℕ) (hq : 3 ≤ q) (hr : 4 ≤ r) :
    2 * (r - 1) ^ 2 * (q - 1) < 3 * q ^ (r - 1) := by
  have hbase := three_pow_strict_quadratic r hr
  have hqpos : 0 < q - 1 := by omega
  have hmul := Nat.mul_lt_mul_of_pos_right hbase hqpos
  have hpow : 3 ^ (r - 2) ≤ q ^ (r - 2) :=
    Nat.pow_le_pow_left hq (r - 2)
  have hmiddle :
      (3 * 3 ^ (r - 2)) * (q - 1) ≤
        (3 * q ^ (r - 2)) * (q - 1) :=
    Nat.mul_le_mul_right (q - 1) (Nat.mul_le_mul_left 3 hpow)
  have hexp : r - 1 = (r - 2) + 1 := by omega
  have hlast :
      (3 * q ^ (r - 2)) * (q - 1) ≤ 3 * q ^ (r - 1) := by
    rw [hexp, pow_succ]
    simpa [mul_assoc] using
      Nat.mul_le_mul_left (3 * q ^ (r - 2)) (Nat.sub_le q 1)
  exact hmul.trans_le (hmiddle.trans hlast)

/-- The numerical core of the manuscript's heavy-support lemma.  The input
`hpopulation` is exactly the elementary multiplicity count

`M ≤ (q-2)q^h + s((r-1)(q-1)-1)`.

Together with the residual mass lower bound it forces `s > 2h`. -/
theorem heavySupportCard_gt_twice_dimension
    (q r h M s : ℕ)
    (hq : 3 ≤ q) (hr : 4 ≤ r) (hh : h ≤ r - 1)
    (hM : q ^ r + q ^ (r - 1) + q ≤ M)
    (hpopulation :
      M ≤ (q - 2) * q ^ h +
        s * ((r - 1) * (q - 1) - 1)) :
    2 * h < s := by
  by_contra hnot
  have hs : s ≤ 2 * h := Nat.le_of_not_gt hnot
  have hsRank : s ≤ 2 * (r - 1) := by omega
  have hpow : q ^ h ≤ q ^ (r - 1) :=
    Nat.pow_le_pow_right (by omega) hh
  have hfirst : (q - 2) * q ^ h ≤ (q - 2) * q ^ (r - 1) :=
    Nat.mul_le_mul_left (q - 2) hpow
  have hdenom :
      s * ((r - 1) * (q - 1) - 1) ≤
        2 * (r - 1) ^ 2 * (q - 1) := by
    calc
      s * ((r - 1) * (q - 1) - 1) ≤
          (2 * (r - 1)) * ((r - 1) * (q - 1) - 1) :=
        Nat.mul_le_mul_right _ hsRank
      _ ≤ (2 * (r - 1)) * ((r - 1) * (q - 1)) :=
        Nat.mul_le_mul_left _ (Nat.sub_le _ _)
      _ = 2 * (r - 1) ^ 2 * (q - 1) := by ring
  have hexp := uniformHeavySupportExponentialInequality q r hq hr
  have hupper :
      (q - 2) * q ^ h + s * ((r - 1) * (q - 1) - 1) <
        q ^ r + q ^ (r - 1) + q := by
    have hstep : q * q ^ (r - 1) = q ^ r := by
      calc
        q * q ^ (r - 1) = q ^ (r - 1) * q := by ring
        _ = q ^ ((r - 1) + 1) := (pow_succ q (r - 1)).symm
        _ = q ^ r := by congr 1 <;> omega
    have hcoeff :
        (q - 2) * q ^ (r - 1) + 3 * q ^ (r - 1) =
          q * q ^ (r - 1) + q ^ (r - 1) := by
      calc
        (q - 2) * q ^ (r - 1) + 3 * q ^ (r - 1) =
            ((q - 2) + 3) * q ^ (r - 1) := by ring
        _ = (q + 1) * q ^ (r - 1) := by congr 1 <;> omega
        _ = q * q ^ (r - 1) + q ^ (r - 1) := by ring
    calc
      (q - 2) * q ^ h + s * ((r - 1) * (q - 1) - 1) ≤
          (q - 2) * q ^ (r - 1) +
            2 * (r - 1) ^ 2 * (q - 1) := Nat.add_le_add hfirst hdenom
      _ < (q - 2) * q ^ (r - 1) + 3 * q ^ (r - 1) :=
        Nat.add_lt_add_left hexp _
      _ = q ^ r + q ^ (r - 1) := by rw [hcoeff, hstep]
      _ < q ^ r + q ^ (r - 1) + q := by omega
  exact (Nat.not_lt_of_ge (hM.trans hpopulation)) hupper

/-- Elementary exponential estimate used in the dimension-free mass bound. -/
theorem two_mul_le_three_pow_sub_one (r : ℕ) (hr : 4 ≤ r) :
    2 * r ≤ 3 ^ (r - 1) := by
  induction r, hr using Nat.le_induction with
  | base => norm_num
  | succ r hr ih =>
      have hr1 : 1 ≤ r := by omega
      calc
        2 * (r + 1) ≤ 3 * (2 * r) := by omega
        _ ≤ 3 * (3 ^ (r - 1)) := Nat.mul_le_mul_left 3 ih
        _ = 3 ^ ((r - 1) + 1) := by rw [pow_succ]; ring
        _ = 3 ^ ((r + 1) - 1) := by congr 1 <;> omega

/-- Uniform version for every base `q ≥ 3`. -/
theorem two_mul_le_pow_sub_one (q r : ℕ) (hq : 3 ≤ q) (hr : 4 ≤ r) :
    2 * r ≤ q ^ (r - 1) := by
  exact (two_mul_le_three_pow_sub_one r hr).trans
    (Nat.pow_le_pow_left hq (r - 1))

/-- Manuscript inequality (6.8): no upper bound on `r` in terms of `q` is
used.  It is stated without truncated subtraction so that every budget term
is visible to later arithmetic consumers. -/
theorem dimensionFreeMassInequality (q r : ℕ) (hq : 3 ≤ q) (hr : 4 ≤ r) :
    r * (q - 1) + 1 + (r - 1) * (q - 1) <
      q ^ r + q ^ (r - 1) + q := by
  have hpow := two_mul_le_pow_sub_one q r hq hr
  have hmul := Nat.mul_le_mul_left q hpow
  have hr1 : 1 ≤ r := by omega
  have hpowstep : q * q ^ (r - 1) = q ^ r := by
    calc
      q * q ^ (r - 1) = q ^ (r - 1) * q := by ring
      _ = q ^ ((r - 1) + 1) := (pow_succ q (r - 1)).symm
      _ = q ^ r := by congr 1 <;> omega
  have hmain : 2 * r * q ≤ q ^ r := by
    nlinarith [hmul, hpowstep]
  have hqsub : q - 1 + 1 = q := by omega
  have hrsub : r - 1 + 1 = r := by omega
  have htworsub : 2 * r - 1 + 1 = 2 * r := by omega
  have hstrict : (2 * r - 1) * (q - 1) + 1 < 2 * r * q := by
    nlinarith
  have hcore : (2 * r - 1) * (q - 1) + 1 < q ^ r :=
    hstrict.trans_le hmain
  nlinarith

/-- Exact availability inequality after the single affine translation.  Here
`d ≤ r(q-1)+1-2` is the manuscript's second `d'` range and `e ≤ q-2` is the
exceptional-label bound. -/
theorem oneTranslationSecondAvailability
    (q r h M d e : ℕ)
    (hq : 3 ≤ q) (hr : 4 ≤ r) (hh : h ≤ r - 1)
    (hM : q ^ r + q ^ (r - 1) + q ≤ M)
    (hd : d ≤ r * (q - 1) + 1 - 2)
    (he : e ≤ q - 2) :
    d + (h - 1) * (q - 1) + e < M := by
  have hmass := dimensionFreeMassInequality q r hq hr
  have hh' : h - 1 ≤ r - 2 := by omega
  have hhmul : (h - 1) * (q - 1) ≤ (r - 2) * (q - 1) :=
    Nat.mul_le_mul_right (q - 1) hh'
  have hsumle :
      d + (h - 1) * (q - 1) + e ≤
        (r * (q - 1) + 1 - 2) + (r - 2) * (q - 1) + (q - 2) :=
    Nat.add_le_add (Nat.add_le_add hd hhmul) he
  have hbudget :
      (r * (q - 1) + 1 - 2) + (r - 2) * (q - 1) + (q - 2) <
        r * (q - 1) + 1 + (r - 1) * (q - 1) := by
    have hrsub1 : r - 1 = (r - 2) + 1 := by omega
    have hqm : 2 ≤ q - 1 := by omega
    have hprod : 8 ≤ r * (q - 1) := Nat.mul_le_mul hr hqm
    have hhead : r * (q - 1) + 1 - 2 < r * (q - 1) + 1 := by
      omega
    have htail :
        (r - 2) * (q - 1) + (q - 2) ≤ (r - 1) * (q - 1) := by
      rw [hrsub1, add_mul]
      omega
    calc
      (r * (q - 1) + 1 - 2) + (r - 2) * (q - 1) + (q - 2) =
          (r * (q - 1) + 1 - 2) +
            ((r - 2) * (q - 1) + (q - 2)) := by omega
      _ < (r * (q - 1) + 1) +
            ((r - 2) * (q - 1) + (q - 2)) :=
        Nat.add_lt_add_right hhead _
      _ ≤ (r * (q - 1) + 1) + (r - 1) * (q - 1) :=
        Nat.add_le_add_left htail _
  exact hsumle.trans_lt (hbudget.trans (hmass.trans_le hM))

/-- Availability before the affine obstruction is encountered. -/
theorem oneTranslationFirstAvailability
    (q r h M d : ℕ)
    (hq : 3 ≤ q) (hr : 4 ≤ r) (hh : h ≤ r - 1)
    (hM : q ^ r + q ^ (r - 1) + q ≤ M)
    (hd : d ≤ r * (q - 1) + 1 - 2) :
    d + h * (q - 1) < M := by
  have hmass := dimensionFreeMassInequality q r hq hr
  have hhmul : h * (q - 1) ≤ (r - 1) * (q - 1) :=
    Nat.mul_le_mul_right (q - 1) hh
  have hsumle :
      d + h * (q - 1) ≤
        (r * (q - 1) + 1 - 2) + (r - 1) * (q - 1) :=
    Nat.add_le_add hd hhmul
  have hstrict :
      (r * (q - 1) + 1 - 2) + (r - 1) * (q - 1) <
        r * (q - 1) + 1 + (r - 1) * (q - 1) := by
    have hqm : 2 ≤ q - 1 := by omega
    have hprod : 8 ≤ r * (q - 1) := Nat.mul_le_mul hr hqm
    omega
  exact hsumle.trans_lt (hstrict.trans (hmass.trans_le hM))

/-- Manuscript display (6.16) in truncated-subtraction form. -/
theorem oneTranslationSecondAvailability_sub
    (q r h M d e : ℕ)
    (hq : 3 ≤ q) (hr : 4 ≤ r) (hh : h ≤ r - 1)
    (hM : q ^ r + q ^ (r - 1) + q ≤ M)
    (hd : d ≤ r * (q - 1) + 1 - 2)
    (he : e ≤ q - 2) :
    d < M - e - (h - 1) * (q - 1) := by
  have havail := oneTranslationSecondAvailability q r h M d e
    hq hr hh hM hd he
  omega

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Exact occurrence-level identification of the new residual rotations.
After translating rotation coordinates by `-α`, a source label lies over `W`
exactly when it was a rotation with coordinate in the affine coset `α + W`.
This also rules out an outside-`P` rotation entering `W` whenever
`W ≤ P` and `α ∈ P`. -/
theorem mem_rotationOccurrencesIn_translatedSequence_iff_affineCoset
    (α : A) (s : List (Group A)) (W : AddSubgroup A)
    (i : Occurrence s) :
    translatedOccurrenceEquiv α s i ∈
        rotationOccurrencesIn (translatedSequence α s) W ↔
      IsRotation (occurrenceValue s i) ∧
        coordinate (occurrenceValue s i) - α ∈ W := by
  classical
  simp only [rotationOccurrencesIn, Finset.mem_filter, Finset.mem_univ,
    true_and, occurrenceValue_translatedSequence,
    isRotation_translateRotations_iff]
  constructor
  · rintro ⟨hrot, hmem⟩
    exact ⟨hrot, by simpa [coordinate_translateRotations α _ hrot] using hmem⟩
  · rintro ⟨hrot, hmem⟩
    exact ⟨hrot, by simpa [coordinate_translateRotations α _ hrot] using hmem⟩

/-- No source rotation outside `P` can enter the translated residual space
`W ≤ P` when the translation vector belongs to `P`. -/
theorem source_coordinate_mem_of_translated_mem
    (α : A) (s : List (Group A)) (W P : AddSubgroup A)
    (hWP : W ≤ P) (hα : α ∈ P) (i : Occurrence s)
    (hi : translatedOccurrenceEquiv α s i ∈
      rotationOccurrencesIn (translatedSequence α s) W) :
    coordinate (occurrenceValue s i) ∈ P := by
  have hcoset :=
    (mem_rotationOccurrencesIn_translatedSequence_iff_affineCoset
      α s W i).1 hi
  have hdiff : coordinate (occurrenceValue s i) - α ∈ P := hWP hcoset.2
  have := P.add_mem hdiff hα
  simpa [sub_add_cancel] using this

/-- Full exact exchange on the actual labelled inside-`K` occurrences.  This
is the source-faithful consumer interface produced by the affine engine: it
returns a subset of `C`, not merely a support-level multiset. -/
def FullExactExchange
    (s : List (Group A)) (C : Selection s) (K : AddSubgroup A)
    (d : ℕ) : Prop :=
  ∀ y : A, y ∈ K →
    ∃ D : Selection s,
      D ⊆ C ∧ D.card = d ∧ coordinateSum s D = y

/-- Bridge from an affine-exchange theorem stated on the subtype of labels in
`C` and with values in the residual subgroup `K`, to the list-facing
`FullExactExchange` consumer.  Mapping subtype labels back to source
positions preserves both cardinality and every repeated occurrence. -/
theorem fullExactExchange_of_subtype
    (s : List (Group A)) (C : Selection s) (K : AddSubgroup A) (d : ℕ)
    (hinside : ∀ i ∈ C, coordinate (occurrenceValue s i) ∈ K)
    (hexchange : ∀ y : K,
      ∃ I : Finset {i // i ∈ C},
        I.card = d ∧
          (∑ i ∈ I,
            (⟨coordinate (occurrenceValue s i.1),
              hinside i.1 i.2⟩ : K)) = y) :
    FullExactExchange s C K d := by
  classical
  intro y hy
  rcases hexchange ⟨y, hy⟩ with ⟨I, hIcard, hIsum⟩
  let emb : {i // i ∈ C} ↪ Occurrence s := Function.Embedding.subtype _
  let D : Selection s := I.map emb
  refine ⟨D, ?_, ?_, ?_⟩
  · intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, _hj, rfl⟩
    exact j.2
  · simpa [D] using hIcard
  · have hval := congrArg Subtype.val hIsum
    simpa [coordinateSum, D, emb] using hval

/-- The quotient extraction plus a full exact exchange provider closes the
rotation channel without any GMO alternative.  In particular, `Bprime` and
the defect `d` are the data actually produced by the maximum labelled
quotient-zero-sum extraction. -/
theorem hasAllRotationProductOneSubsequence_of_preGMOFullExactExchange
    (s : List (Group A)) (Q Dtotal a b : ℕ) (K : AddSubgroup A)
    (h : RotationChannelPreGMOData s Q Dtotal a b K)
    (hexchange : FullExactExchange s h.C K h.d) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  have hCmem : coordinateSum s h.C ∈ K := by
    rw [coordinateSum]
    apply AddSubgroup.sum_mem
    intro i hi
    have hi' : IsRotation (occurrenceValue s i) ∧
        coordinate (occurrenceValue s i) ∈ K := by
      simpa [h.C_eq, rotationOccurrencesIn] using hi
    exact hi'.2
  have htarget :
      coordinateSum s h.C + coordinateSum s h.Bprime ∈ K :=
    K.add_mem hCmem h.coordinateSum_Bprime_mem
  obtain ⟨Dsel, hDsub, hDcard, hDsum⟩ :=
    hexchange (coordinateSum s h.C + coordinateSum s h.Bprime) htarget
  have hdis : Disjoint (h.C \ Dsel) h.Bprime :=
    h.CBprime_disjoint.mono_left Finset.sdiff_subset
  apply hasAllRotationProductOneSubsequence_of_coordinateSum_eq_zero
    s ((h.C \ Dsel) ∪ h.Bprime) (2 * Q)
  · rw [Finset.card_union_of_disjoint hdis,
      Finset.card_sdiff_of_subset hDsub, h.Ccard, hDcard, h.exactSize]
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact h.allC i (Finset.mem_sdiff.mp hi).1
    · exact h.allBprime i hi
  · rw [coordinateSum_union s (h.C \ Dsel) h.Bprime hdis,
      coordinateSum_sdiff s h.C Dsel hDsub, hDsum]
    abel

/-- Run the labelled quotient extraction automatically, then discharge its
unique remaining internal obligation with a full exact exchange provider. -/
theorem hasAllRotationProductOneSubsequence_of_extractedFullExactExchange
    (s : List (Group A)) (Q Dtotal a b Dq : ℕ) (K : AddSubgroup A)
    (htotal : a + b = 2 * Q + Dtotal)
    (href : (reflectionOccurrences s).card = a)
    (hrot : (rotationOccurrences s).card = b)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq)
    (hDqD : Dq ≤ Dtotal)
    (hQ : Q = Nat.card A)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn s K).card)
    (hguard : QuotientNoReflection s K)
    (hexchange : ∀ h : RotationChannelPreGMOData s Q Dtotal a b K,
      FullExactExchange s h.C K h.d) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  rcases exists_rotationChannelPreGMOData s Q Dtotal a b Dq K
      htotal href hrot hsmall hDqD hQ hcapacity hguard with ⟨h⟩
  exact hasAllRotationProductOneSubsequence_of_preGMOFullExactExchange
    s Q Dtotal a b K h (hexchange h)

/-- The extracted second quotient reduction in the translated list, followed
by the exact occurrence-preserving pullback to the original list. -/
theorem hasAllRotationProductOneSubsequence_of_oneTranslationExtraction
    (α : A) (s : List (Group A))
    (Q Dtotal a b Dq : ℕ) (K : AddSubgroup A)
    (htotal : a + b = 2 * Q + Dtotal)
    (href : (reflectionOccurrences (translatedSequence α s)).card = a)
    (hrot : (rotationOccurrences (translatedSequence α s)).card = b)
    (hsmall : QuotientSmallDavenportProductOneFreeAtMost K Dq)
    (hDqD : Dq ≤ Dtotal)
    (hQ : Q = Nat.card A)
    (hcapacity : b - Nat.card (A ⧸ K) + 2 ≤
      (rotationOccurrencesIn (translatedSequence α s) K).card)
    (hguard : QuotientNoReflection (translatedSequence α s) K)
    (hexchange :
      ∀ h : RotationChannelPreGMOData (translatedSequence α s)
          Q Dtotal a b K,
        FullExactExchange (translatedSequence α s) h.C K h.d)
    (hQα : Q • α = 0) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  apply hasAllRotationProductOneSubsequence_pullback_translatedSequence α s Q
  · exact hasAllRotationProductOneSubsequence_of_extractedFullExactExchange
      (translatedSequence α s) Q Dtotal a b Dq K htotal href hrot
      hsmall hDqD hQ hcapacity hguard hexchange
  · exact hQα

/-- Fixed-cardinality quotient-completion interface.  Removing `D` from the
inside-residual rotation set `C` and adjoining the disjoint extracted block
`Bprime` gives an exact all-rotation product-one selection.  The source
identity `sum D = sum C + z` is represented by `hsum`, with
`z = coordinateSum s Bprime`.
-/
theorem hasAllRotationProductOneSubsequence_of_reductionCompletion
    (s : List (Group A)) (C D Bprime : Selection s)
    (Q M d n : ℕ)
    (hDC : D ⊆ C) (hCB : Disjoint C Bprime)
    (hCcard : C.card = M) (hDcard : D.card = d)
    (hBcard : Bprime.card = n) (hsize : M - d + n = 2 * Q)
    (hallC : ∀ i ∈ C, IsRotation (occurrenceValue s i))
    (hallB : ∀ i ∈ Bprime, IsRotation (occurrenceValue s i))
    (hsum : coordinateSum s D =
      coordinateSum s C + coordinateSum s Bprime) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  have hdis : Disjoint (C \ D) Bprime :=
    hCB.mono_left Finset.sdiff_subset
  apply hasAllRotationProductOneSubsequence_of_coordinateSum_eq_zero
    s ((C \ D) ∪ Bprime) (2 * Q)
  · rw [Finset.card_union_of_disjoint hdis,
      Finset.card_sdiff_of_subset hDC, hCcard, hDcard, hBcard, hsize]
  · intro i hi
    rcases Finset.mem_union.mp hi with hi | hi
    · exact hallC i (Finset.mem_sdiff.mp hi).1
    · exact hallB i hi
  · rw [coordinateSum_union s (C \ D) Bprime hdis,
      coordinateSum_sdiff s C D hDC, hsum]
    abel

/-- The exact second completion followed by the one translation pullback.
The translated selections are indexed by their actual translated list; the
result transports their labels through the canonical `Fin` equivalence and
uses `Q • α = 0` to remove the total translation error. -/
theorem hasAllRotationProductOneSubsequence_of_oneTranslationCompletion
    (α : A) (s : List (Group A))
    (C D Bprime : Selection (translatedSequence α s))
    (Q M d n : ℕ)
    (hDC : D ⊆ C) (hCB : Disjoint C Bprime)
    (hCcard : C.card = M) (hDcard : D.card = d)
    (hBcard : Bprime.card = n) (hsize : M - d + n = 2 * Q)
    (hallC : ∀ i ∈ C,
      IsRotation (occurrenceValue (translatedSequence α s) i))
    (hallB : ∀ i ∈ Bprime,
      IsRotation (occurrenceValue (translatedSequence α s) i))
    (hsum : coordinateSum (translatedSequence α s) D =
      coordinateSum (translatedSequence α s) C +
        coordinateSum (translatedSequence α s) Bprime)
    (hQα : Q • α = 0) :
    HasAllRotationProductOneSubsequenceOfCard s (2 * Q) := by
  apply hasAllRotationProductOneSubsequence_pullback_translatedSequence α s Q
  · exact hasAllRotationProductOneSubsequence_of_reductionCompletion
      (translatedSequence α s) C D Bprime Q M d n hDC hCB
      hCcard hDcard hBcard hsize hallC hallB hsum
  · exact hQα

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.two_mul_le_three_pow_sub_one
#print axioms GaoLean.three_pow_strict_quadratic
#print axioms GaoLean.uniformHeavySupportExponentialInequality
#print axioms GaoLean.heavySupportCard_gt_twice_dimension
#print axioms GaoLean.two_mul_le_pow_sub_one
#print axioms GaoLean.dimensionFreeMassInequality
#print axioms GaoLean.oneTranslationSecondAvailability
#print axioms GaoLean.oneTranslationFirstAvailability
#print axioms GaoLean.oneTranslationSecondAvailability_sub

#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_reductionCompletion
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_oneTranslationCompletion
#print axioms GaoLean.ConcreteGDihedral.mem_rotationOccurrencesIn_translatedSequence_iff_affineCoset
#print axioms GaoLean.ConcreteGDihedral.source_coordinate_mem_of_translated_mem
#print axioms GaoLean.ConcreteGDihedral.fullExactExchange_of_subtype
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_preGMOFullExactExchange
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_extractedFullExactExchange
#print axioms GaoLean.ConcreteGDihedral.hasAllRotationProductOneSubsequence_of_oneTranslationExtraction
