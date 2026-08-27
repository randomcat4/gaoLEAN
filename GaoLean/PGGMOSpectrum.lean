import GaoLean.GAOARGMOInterfaces
import GaoLean.PGGMOFoundations

/-!
# Finite exact-sum spectra for GMO

This file turns the occurrence-quantified ordinary and `{+1,-1}` spectra in
the manuscript interfaces into literal finite subsets of the ambient group.
The equivalence lemmas ensure that the later stabilizer/sumset argument uses
exactly the existing provider statements.
-/

namespace GaoLean

open scoped BigOperators Pointwise

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- All sums of exactly `n` labelled occurrences of `xs`. -/
noncomputable def ordinaryExactSpectrum (xs : List A) (n : ℕ) : Finset A := by
  classical
  exact Finset.univ.filter fun y ↦ ∃ I : Selection xs,
    I.card = n ∧ ∑ i ∈ I, occurrenceValue xs i = y

@[simp]
theorem mem_ordinaryExactSpectrum_iff (xs : List A) (n : ℕ) (y : A) :
    y ∈ ordinaryExactSpectrum xs n ↔
      ∃ I : Selection xs,
        I.card = n ∧ ∑ i ∈ I, occurrenceValue xs i = y := by
  classical
  simp [ordinaryExactSpectrum]

theorem ordinarySpectrumFull_iff_exactSpectrum_eq_univ
    (xs : List A) (n : ℕ) :
    OrdinarySpectrumFull xs n ↔ ordinaryExactSpectrum xs n = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  exact forall_congr' fun y ↦ (mem_ordinaryExactSpectrum_iff xs n y).symm

theorem ordinaryExactSpectrum_nonempty
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length) :
    (ordinaryExactSpectrum xs n).Nonempty := by
  classical
  obtain ⟨I, -, hIcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Selection xs)) (by
      simpa using hn)
  refine ⟨∑ i ∈ I, occurrenceValue xs i, ?_⟩
  exact mem_ordinaryExactSpectrum_iff xs n _ |>.2 ⟨I, hIcard, rfl⟩

/-- All signed sums of exactly `n` labelled occurrences of `xs`. -/
noncomputable def plusMinusExactSpectrum (xs : List A) (n : ℕ) : Finset A := by
  classical
  exact Finset.univ.filter fun y ↦ Nonempty (HasPlusMinusSumOfCard xs n y)

@[simp]
theorem mem_plusMinusExactSpectrum_iff (xs : List A) (n : ℕ) (y : A) :
    y ∈ plusMinusExactSpectrum xs n ↔
      Nonempty (HasPlusMinusSumOfCard xs n y) := by
  classical
  simp [plusMinusExactSpectrum]

theorem plusMinusSpectrumFull_iff_exactSpectrum_eq_univ
    (xs : List A) (n : ℕ) :
    PlusMinusSpectrumFull xs n ↔ plusMinusExactSpectrum xs n = Finset.univ := by
  classical
  rw [Finset.eq_univ_iff_forall]
  exact forall_congr' fun y ↦ (mem_plusMinusExactSpectrum_iff xs n y).symm

theorem plusMinusExactSpectrum_nonempty
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length) :
    (plusMinusExactSpectrum xs n).Nonempty := by
  classical
  obtain ⟨I, -, hIcard⟩ :=
    Finset.exists_subset_card_eq (s := (Finset.univ : Selection xs)) (by
      simpa using hn)
  let h : HasPlusMinusSumOfCard xs n
      (∑ i ∈ I, occurrenceValue xs i) := {
    positive := I
    negative := ∅
    disjoint := by simp
    card_selected := by simpa using hIcard
    weighted_sum := by simp
  }
  exact ⟨_, mem_plusMinusExactSpectrum_iff xs n _ |>.2 ⟨h⟩⟩

/-- The additive stabilizer of a nonempty proper finite subset of a finite
group is a proper subgroup. -/
theorem stabilizer_lt_top_of_finset_nonempty_ne_univ
    (s : Finset A) (hs : s.Nonempty) (hne : s ≠ Finset.univ) :
    AddAction.stabilizer A (s : Set A) < ⊤ := by
  classical
  rw [lt_top_iff_ne_top]
  intro htop
  apply hne
  rw [Finset.eq_univ_iff_forall]
  intro y
  have hs0 : s.Nonempty := hs
  obtain ⟨x, hx⟩ := hs
  have hmemStab : y - x ∈ AddAction.stabilizer A (s : Set A) := by
    rw [htop]
    trivial
  have hmemFin : y - x ∈ s.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hs0]
    exact hmemStab
  have htranslate := (Finset.mem_addStab hs0).mp hmemFin
  have hy : (y - x) +ᵥ x ∈ (y - x) +ᵥ s :=
    Finset.vadd_mem_vadd_finset hx
  rw [htranslate] at hy
  simpa [vadd_eq_add] using hy

noncomputable def ordinarySpectrumStabilizer
    (xs : List A) (n : ℕ) : AddSubgroup A :=
  AddAction.stabilizer A (ordinaryExactSpectrum xs n : Set A)

theorem ordinarySpectrumStabilizer_strict_of_not_full
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length)
    (hnot : ¬ OrdinarySpectrumFull xs n) :
    ordinarySpectrumStabilizer xs n < ⊤ := by
  apply stabilizer_lt_top_of_finset_nonempty_ne_univ
    (ordinaryExactSpectrum xs n) (ordinaryExactSpectrum_nonempty xs n hn)
  intro heq
  exact hnot ((ordinarySpectrumFull_iff_exactSpectrum_eq_univ xs n).2 heq)

noncomputable def plusMinusSpectrumStabilizer
    (xs : List A) (n : ℕ) : AddSubgroup A :=
  AddAction.stabilizer A (plusMinusExactSpectrum xs n : Set A)

theorem plusMinusSpectrumStabilizer_strict_of_not_full
    (xs : List A) (n : ℕ) (hn : n ≤ xs.length)
    (hnot : ¬ PlusMinusSpectrumFull xs n) :
    plusMinusSpectrumStabilizer xs n < ⊤ := by
  apply stabilizer_lt_top_of_finset_nonempty_ne_univ
    (plusMinusExactSpectrum xs n) (plusMinusExactSpectrum_nonempty xs n hn)
  intro heq
  exact hnot ((plusMinusSpectrumFull_iff_exactSpectrum_eq_univ xs n).2 heq)

/-- Occurrences of `xs` lying in the additive coset `alpha + K`. -/
noncomputable def occurrencesInAddCoset
    (xs : List A) (K : AddSubgroup A) (alpha : A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i ↦ occurrenceValue xs i - alpha ∈ K

@[simp]
theorem mem_occurrencesInAddCoset_iff
    (xs : List A) (K : AddSubgroup A) (alpha : A) (i : Occurrence xs) :
    i ∈ occurrencesInAddCoset xs K alpha ↔
      occurrenceValue xs i - alpha ∈ K := by
  classical
  simp [occurrencesInAddCoset]

/-- Once the source theorem supplies the large-coset inequality, conversion
to the project's occurrence-labelled ordinary concentration structure is
pure bookkeeping. -/
theorem ordinaryGMOConcentration_of_coset_card
    (xs : List A) (K : AddSubgroup A) (hK : K < ⊤) (alpha : A)
    (hcard : xs.length - Nat.card (A ⧸ K) + 2 ≤
      (occurrencesInAddCoset xs K alpha).card) :
    Nonempty (OrdinaryGMOConcentration xs) := by
  refine ⟨{
    K := K
    strict := hK
    alpha := alpha
    selected := occurrencesInAddCoset xs K alpha
    sourceCoset := ?_
    card_lower := hcard
  }⟩
  intro i hi
  exact (mem_occurrencesInAddCoset_iff xs K alpha i).1 hi

/-- Occurrences simultaneously satisfying the source-coset and both signed
weight-coset conditions of GMO Corollary 1.3. -/
noncomputable def occurrencesInPlusMinusGMOCosets
    (xs : List A) (K : AddSubgroup A) (alpha beta : A) : Selection xs := by
  classical
  exact Finset.univ.filter fun i ↦
    occurrenceValue xs i - alpha ∈ K ∧
    occurrenceValue xs i - beta ∈ K ∧
    -occurrenceValue xs i - beta ∈ K

@[simp]
theorem mem_occurrencesInPlusMinusGMOCosets_iff
    (xs : List A) (K : AddSubgroup A) (alpha beta : A)
    (i : Occurrence xs) :
    i ∈ occurrencesInPlusMinusGMOCosets xs K alpha beta ↔
      occurrenceValue xs i - alpha ∈ K ∧
      occurrenceValue xs i - beta ∈ K ∧
      -occurrenceValue xs i - beta ∈ K := by
  classical
  simp [occurrencesInPlusMinusGMOCosets]

theorem plusMinusGMOConcentration_of_coset_card
    (xs : List A) (K : AddSubgroup A) (hK : K < ⊤) (alpha beta : A)
    (hcard : xs.length - Nat.card (A ⧸ K) + 2 ≤
      (occurrencesInPlusMinusGMOCosets xs K alpha beta).card) :
    Nonempty (PlusMinusGMOConcentration xs) := by
  refine ⟨{
    K := K
    strict := hK
    alpha := alpha
    beta := beta
    selected := occurrencesInPlusMinusGMOCosets xs K alpha beta
    sourceCoset := ?_
    positiveWeightCoset := ?_
    negativeWeightCoset := ?_
    card_lower := hcard
  }⟩
  · intro i hi
    exact (mem_occurrencesInPlusMinusGMOCosets_iff xs K alpha beta i).1 hi |>.1
  · intro i hi
    exact (mem_occurrencesInPlusMinusGMOCosets_iff xs K alpha beta i).1 hi |>.2.1
  · intro i hi
    exact (mem_occurrencesInPlusMinusGMOCosets_iff xs K alpha beta i).1 hi |>.2.2

end GaoLean

#print axioms GaoLean.ordinarySpectrumFull_iff_exactSpectrum_eq_univ
#print axioms GaoLean.ordinaryExactSpectrum_nonempty
#print axioms GaoLean.plusMinusSpectrumFull_iff_exactSpectrum_eq_univ
#print axioms GaoLean.plusMinusExactSpectrum_nonempty
#print axioms GaoLean.ordinarySpectrumStabilizer_strict_of_not_full
#print axioms GaoLean.plusMinusSpectrumStabilizer_strict_of_not_full
#print axioms GaoLean.ordinaryGMOConcentration_of_coset_card
#print axioms GaoLean.plusMinusGMOConcentration_of_coset_card
