import GaoLean.GAOARRankThree
import GaoFormal.Matching.VariableDirectionCoverage

/-!
# Rank-three line-completion auxiliary facts

This file begins the direct formalization of the three auxiliary facts inside
the manuscript's line-completion lemma.  The signed-lifting fact is derived
from the same structural GMO theorem already cited by the paper: on a
prime-order line, its non-full branch would leave at most `q-2` nonzero
occurrences and therefore contradicts the stated reservoir hypothesis.
-/

namespace GaoLean

open scoped BigOperators

/-- Occurrence labels carrying a nonzero value. -/
noncomputable def nonzeroOccurrences
    {A : Type*} [Zero A] (xs : List A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i => occurrenceValue xs i ≠ 0

noncomputable def zeroOccurrences
    {A : Type*} [Zero A] (xs : List A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i => occurrenceValue xs i = 0

noncomputable def valueOccurrences
    {A : Type*} (xs : List A) (a : A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i => occurrenceValue xs i = a

noncomputable def otherValueOccurrences
    {A : Type*} (xs : List A) (a : A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i => occurrenceValue xs i ≠ a

theorem card_nonzeroOccurrences_add_card_zeroOccurrences
    {A : Type*} [Zero A] (xs : List A) :
    (nonzeroOccurrences xs).card +
      (zeroOccurrences xs).card =
        xs.length := by
  classical
  have hpartition :
      nonzeroOccurrences xs ∪
          zeroOccurrences xs =
        Finset.univ := by
    ext i
    by_cases h : occurrenceValue xs i = 0 <;>
      simp [nonzeroOccurrences, zeroOccurrences, h]
  have hdis : Disjoint (nonzeroOccurrences xs)
      (zeroOccurrences xs) := by
    rw [Finset.disjoint_left]
    intro i hi hn
    have hi' : occurrenceValue xs i ≠ 0 := by
      simpa [nonzeroOccurrences] using hi
    have hn' : occurrenceValue xs i = 0 := by
      simpa [zeroOccurrences] using hn
    exact hi' hn'
  rw [← Finset.card_union_of_disjoint hdis, hpartition]
  simp

/-- Signed lifting in a prime-order line for the range actually used in the
line-completion proof (`q-1 ≤ t`). -/
theorem primeLine_signedLifting_of_structuralGMO
    {J : Type*} [AddCommGroup J] [Fintype J]
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hJcard : Nat.card J = q)
    (hGMO : PlusMinusGMOStructuralProvider J)
    (xs : List J) (t : ℕ)
    (htlower : q - 1 ≤ t) (htupper : t ≤ xs.length)
    (htarget : Nat.card J ≤ xs.length - t)
    (hnonzero : q - 1 ≤ (nonzeroOccurrences xs).card)
    (y : J) :
    Nonempty (HasPlusMinusSumOfCard xs (xs.length - t) y) := by
  classical
  have hpm : PlusMinusDavenportAtMost J q := by
    rw [← hJcard]
    exact plusMinusDavenportAtMost_natCard
  have hthreshold : (xs.length - t) + q - 1 ≤ xs.length := by
    omega
  rcases hGMO xs (xs.length - t) q htarget hpm hthreshold with
      hfull | hnonfull
  · exact hfull y
  · obtain ⟨hc⟩ := hnonfull
    have hHbot : hc.K = ⊥ :=
      ConcreteGDihedral.addSubgroup_eq_bot_of_lt_top_of_prime_natCard
        q hqPrime hJcard hc.K hc.strict
    have hoddJ : Odd (Nat.card J) := by rw [hJcard]; exact hqodd
    have hselectedZero : ∀ i ∈ hc.selected, occurrenceValue xs i = 0 := by
      intro i hi
      have himem : occurrenceValue xs i ∈ hc.K :=
        hc.value_mem_subgroup
          (odd_natCard_quotient_of_odd_natCard hc.K hoddJ) i hi
      rw [hHbot] at himem
      simpa using himem
    have hdis : Disjoint (nonzeroOccurrences xs) hc.selected := by
      rw [Finset.disjoint_left]
      intro i hinz hisel
      have hinz' : occurrenceValue xs i ≠ 0 := by
        simpa [nonzeroOccurrences] using hinz
      exact hinz' (hselectedZero i hisel)
    have hsumcard :
        (nonzeroOccurrences xs).card + hc.selected.card ≤ xs.length := by
      calc
        (nonzeroOccurrences xs).card + hc.selected.card =
            (nonzeroOccurrences xs ∪ hc.selected).card :=
          (Finset.card_union_of_disjoint hdis).symm
        _ ≤ (Finset.univ : Selection xs).card :=
          Finset.card_le_card (Finset.subset_univ _)
        _ = xs.length := by simp
    have hquotcard : Nat.card (J ⧸ hc.K) = q := by
      rw [hHbot]
      calc
        Nat.card (J ⧸ (⊥ : AddSubgroup J)) = Nat.card J :=
          Nat.card_congr
            (QuotientAddGroup.quotientBot (G := J)).toEquiv
        _ = q := hJcard
    have hselLower : xs.length - q + 2 ≤ hc.selected.card := by
      simpa only [hquotcard] using hc.card_lower
    omega

/-- Fixed-cardinality sums on a prime-order line from `q-1` labelled
exceptions to a heavy value and a disjoint reservoir of that heavy value.
This is the occurrence-level form of the manuscript's replacement argument. -/
theorem primeLine_fixedCardinality_of_heavyValue
    {J Ω : Type*} [AddCommGroup J] [Fintype J]
    [Fintype Ω] [DecidableEq Ω]
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q)
    (hJcard : Nat.card J = q)
    (C : Ω → J) (g : J) (E G : Finset Ω) (d : ℕ)
    (hEcard : E.card = q - 1)
    (hEexception : ∀ i ∈ E, C i ≠ g)
    (hGvalue : ∀ i ∈ G, C i = g)
    (hEG : Disjoint E G)
    (hd : q - 1 ≤ d) (hGcard : d ≤ G.card)
    (y : J) :
    ∃ I : Finset Ω, I.card = d ∧ ∑ i ∈ I, C i = y := by
  classical
  letI : Fact (Nat.Prime q) := ⟨hqPrime⟩
  let e : J ≃+ ZMod q :=
    addEquivZModOfPrimeCard hJcard
  have hfinCard : Fintype.card (Fin (q - 1)) = Fintype.card E := by
    simp [hEcard]
  let idx : Fin (q - 1) ≃ E := Fintype.equivOfCardEq hfinCard
  let inc : Fin (q - 1) → ZMod q := fun k => e (C (idx k).1 - g)
  have hinc : ∀ k, inc k ≠ 0 := by
    intro k hk
    have hzero : C (idx k).1 - g = 0 := by
      apply e.injective
      simpa [inc] using hk
    exact hEexception (idx k).1 (idx k).2 (sub_eq_zero.mp hzero)
  obtain ⟨T, hTsum⟩ :=
    GaoFormal.exists_labelled_subset_sum_eq_of_nonzero inc hinc
      (e (y - d • g))
  let ET : Finset Ω := T.image fun k => (idx k).1
  have hidxinj : Function.Injective (fun k : Fin (q - 1) => (idx k).1) := by
    intro i j hij
    apply idx.injective
    exact Subtype.ext hij
  have hETcard : ET.card = T.card := by
    dsimp [ET]
    rw [Finset.card_image_of_injective _ hidxinj]
  have hETsub : ET ⊆ E := by
    intro i hi
    rcases Finset.mem_image.mp hi with ⟨k, _hk, rfl⟩
    exact (idx k).2
  have hTcard : T.card ≤ d := by
    calc
      T.card ≤ Fintype.card (Fin (q - 1)) := Finset.card_le_univ T
      _ = q - 1 := by simp
      _ ≤ d := hd
  have hfillAvail : d - T.card ≤ G.card := by omega
  obtain ⟨F, hFsub, hFcard⟩ := Finset.exists_subset_card_eq hfillAvail
  have hETF : Disjoint ET F :=
    (hEG.mono hETsub hFsub)
  have hcorr :
      (∑ k ∈ T, (C (idx k).1 - g)) = y - d • g := by
    apply e.injective
    simpa [inc, map_sum] using hTsum
  have hETsum :
      (∑ i ∈ ET, C i) = (y - d • g) + T.card • g := by
    dsimp [ET]
    rw [Finset.sum_image]
    · calc
        (∑ k ∈ T, C (idx k).1) =
            ∑ k ∈ T, ((C (idx k).1 - g) + g) := by
          apply Finset.sum_congr rfl
          intro k hk
          abel
        _ = (∑ k ∈ T, (C (idx k).1 - g)) +
              ∑ _k ∈ T, g := by
          rw [Finset.sum_add_distrib]
        _ = (y - d • g) + T.card • g := by
          rw [hcorr, Finset.sum_const]
    · intro i hi j hj hij
      exact hidxinj hij
  have hFsum : (∑ i ∈ F, C i) = (d - T.card) • g := by
    calc
      (∑ i ∈ F, C i) = ∑ _i ∈ F, g := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hGvalue i (hFsub hi)
      _ = (d - T.card) • g := by rw [Finset.sum_const, hFcard]
  refine ⟨ET ∪ F, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hETF, hETcard, hFcard]
    omega
  · rw [Finset.sum_union hETF, hETsum, hFsum]
    have hdecomp : T.card + (d - T.card) = d :=
      Nat.add_sub_of_le hTcard
    calc
      y - d • g + T.card • g + (d - T.card) • g =
          y - d • g + (T.card • g + (d - T.card) • g) := by abel
      _ = y - d • g + d • g := by
        rw [← add_nsmul, hdecomp]
      _ = y := by abel

/-- The manuscript's heavy-value dichotomy for a long sequence on a line:
either at most `q-2` occurrences differ from the heavy value, or every target
is realized at every cardinality in the required interval. -/
theorem primeLine_heavyValue_or_fixedCardinalitySums
    {J : Type*} [AddCommGroup J] [Fintype J]
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q) (hqodd : Odd q)
    (hJcard : Nat.card J = q)
    (xs : List J)
    (hlength : 2 * q ^ 3 - q ^ 2 + 2 ≤ xs.length) :
    ∃ g : J,
      3 * q - 3 ≤ (valueOccurrences xs g).card ∧
      ((otherValueOccurrences xs g).card ≤ q - 2 ∨
        ∀ d, q - 1 ≤ d → d ≤ 3 * q - 4 → ∀ y : J,
          ∃ I : Selection xs, I.card = d ∧
            ∑ i ∈ I, occurrenceValue xs i = y) := by
  classical
  have hq3 : 3 ≤ q := by
    by_contra h
    have hq2 : 2 ≤ q := hqPrime.two_le
    have hqeq : q = 2 := by omega
    rw [hqeq] at hqodd
    norm_num at hqodd
  have hJfcard : Fintype.card J = q := by
    simpa [Nat.card_eq_fintype_card] using hJcard
  have hpigeon : q * (3 * q - 3) ≤ xs.length := by
    apply le_trans ?_ hlength
    have hq2 : q - 2 + 2 = q := Nat.sub_add_cancel (by omega)
    have hthree : 3 * q - 3 + 3 = 3 * q :=
      Nat.sub_add_cancel (by omega)
    have hsqle : q ^ 2 ≤ 2 * q ^ 3 := by
      nlinarith [Nat.zero_le (q ^ 2 * (2 * q - 1))]
    have hsub : 2 * q ^ 3 - q ^ 2 + q ^ 2 = 2 * q ^ 3 :=
      Nat.sub_add_cancel hsqle
    nlinarith [Nat.zero_le ((q - 2) * (2 * q ^ 2 + 3))]
  have hpigeon' : (Finset.univ : Finset J).card * (3 * q - 3) ≤
      (Finset.univ : Selection xs).card := by
    simpa [hJfcard] using hpigeon
  obtain ⟨g, _hg, hGlarge⟩ :=
    Finset.exists_le_card_fiber_of_mul_le_card_of_maps_to
      (s := (Finset.univ : Selection xs))
      (t := (Finset.univ : Finset J)) (f := occurrenceValue xs)
      (n := 3 * q - 3) (fun _ _ => Finset.mem_univ _) Finset.univ_nonempty
      hpigeon'
  have hGlarge' : 3 * q - 3 ≤ (valueOccurrences xs g).card := by
    simpa [valueOccurrences] using hGlarge
  refine ⟨g, hGlarge', ?_⟩
  by_cases hother : (otherValueOccurrences xs g).card ≤ q - 2
  · exact Or.inl hother
  · right
    intro d hd hdupper y
    have hEavail : q - 1 ≤ (otherValueOccurrences xs g).card := by omega
    obtain ⟨E, hEsub, hEcard⟩ :=
      Finset.exists_subset_card_eq hEavail
    let G := valueOccurrences xs g
    have hEexception : ∀ i ∈ E, occurrenceValue xs i ≠ g := by
      intro i hi
      have hi' := hEsub hi
      simpa [otherValueOccurrences] using hi'
    have hGvalue : ∀ i ∈ G, occurrenceValue xs i = g := by
      intro i hi
      simpa [G, valueOccurrences] using hi
    have hEG : Disjoint E G := by
      rw [Finset.disjoint_left]
      intro i hiE hiG
      exact hEexception i hiE (hGvalue i hiG)
    have hGcard : d ≤ G.card := by
      dsimp only [G]
      omega
    exact primeLine_fixedCardinality_of_heavyValue q hqPrime hJcard
      (occurrenceValue xs) g E G d hEcard hEexception hGvalue hEG hd
        hGcard y

end GaoLean

#print axioms GaoLean.primeLine_signedLifting_of_structuralGMO
#print axioms GaoLean.primeLine_fixedCardinality_of_heavyValue
#print axioms GaoLean.primeLine_heavyValue_or_fixedCardinalitySums
