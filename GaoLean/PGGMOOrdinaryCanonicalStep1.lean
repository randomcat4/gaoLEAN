import GaoLean.PGGMOOrdinaryTargetBase

/-!
# Canonical ordinary GMO Step 1 cores

The original Step 1 core records a labelled affine container, but does not
require it to contain every source occurrence in that coset.  This module
adds precisely that equality.  It closes the trivial-subgroup excess-fiber
base, the top-subgroup full-spectrum branch, and the direct proper-subgroup
concentration threshold.  No strict-enlargement or provider conclusion is
asserted here.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A Step 1 core whose affine container is the complete labelled source
fiber over its coset.  The equality counts repeated values by occurrence. -/
structure CanonicalOrdinaryGMOStep1Core (xs : List A)
    extends OrdinaryGMOStep1Core xs where
  container_eq :
    container = occurrencesInAddCoset xs H beta

/-- A fiber strictly larger than `d*(A)` gives the canonical `H = bot`
Step 1 core.  Unlike the weaker base constructor, the container equality is
retained in the result. -/
theorem canonicalOrdinaryGMOStep1Core_bot_of_excess_occurrenceFiber
    (xs : List A) (a : A)
    (hexcess : pGroupDStar A < (occurrenceFiber xs a).card) :
    Nonempty (CanonicalOrdinaryGMOStep1Core xs) := by
  classical
  let F : Selection xs := occurrenceFiber xs a
  have hbotCard : Nat.card (⊥ : AddSubgroup A) = 1 :=
    AddSubgroup.card_bot
  have hbotD : pGroupDStar (⊥ : AddSubgroup A) = 0 :=
    pGroupDStar_addSubgroup_bot
  have honeF : 1 ≤ F.card := by
    dsimp only [F]
    omega
  obtain ⟨core, hcoreSub, hcoreCard⟩ :=
    Finset.exists_subset_card_eq (s := F) honeF
  refine ⟨{
    H := ⊥
    beta := a
    container := F
    core := core
    core_subset_container := hcoreSub
    container_in_coset := ?_
    container_card_lower := ?_
    core_card := ?_
    core_full := ?_
    container_eq := ?_
  }⟩
  · intro i hi
    apply (mem_addCosetFinset_iff (⊥ : AddSubgroup A) a _).2
    have hvalue : occurrenceValue xs i = a := by
      simpa [F, occurrenceFiber] using hi
    simp [hvalue]
  · rw [hbotCard]
    dsimp only [F]
    omega
  · rw [hcoreCard, hbotCard, hbotD]
  · intro h hh
    have hhzero : h = 0 := by simpa using hh
    refine ⟨core, Finset.Subset.rfl, ?_, ?_⟩
    · simpa [hbotCard] using hcoreCard
    · have hcoreValue : ∀ i ∈ core, occurrenceValue xs i = a := by
        intro i hi
        have hiF := hcoreSub hi
        simpa [F, occurrenceFiber] using hiF
      calc
        (∑ i ∈ core, occurrenceValue xs i) = ∑ _i ∈ core, a := by
          apply Finset.sum_congr rfl
          intro i hi
          exact hcoreValue i hi
        _ = core.card • a := by simp
        _ = a := by rw [hcoreCard]; simp
        _ = Nat.card (⊥ : AddSubgroup A) • a + h := by
          rw [hbotCard, hhzero]
          simp
  · ext i
    simp [F, occurrenceFiber, mem_occurrencesInAddCoset_iff,
      sub_eq_zero]

namespace CanonicalOrdinaryGMOStep1Core

/-- At `H = top`, the core supplies an arbitrary `|A|`-term sum.  Choose
a fixed genuine tail outside the core and ask `core_full` to cancel its
sum.  This yields the full exact `n`-spectrum, not merely the weaker GMO
target output. -/
theorem ordinarySpectrumFull_of_H_eq_top
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (n : ℕ) (hH : C.H = ⊤)
    (hnA : Nat.card A ≤ n)
    (hlen : n + pGroupDStar A ≤ xs.length) :
    OrdinarySpectrumFull xs n := by
  classical
  intro y
  let available : Selection xs := Finset.univ \ C.core
  have hcoreSubUniv :
      C.core ⊆ (Finset.univ : Selection xs) :=
    Finset.subset_univ C.core
  have havailableCard :
      available.card = xs.length - C.core.card := by
    dsimp only [available]
    rw [Finset.card_sdiff_of_subset hcoreSubUniv]
    simp
  have htopCard : Nat.card C.H = Nat.card A := by
    rw [hH]
    simp [Nat.card_eq_fintype_card]
  have htopD : pGroupDStar C.H = pGroupDStar A := by
    rw [hH]
    exact pGroupDStar_addEquiv AddSubgroup.topEquiv
  have htailLe : n - Nat.card A ≤ available.card := by
    rw [havailableCard, C.core_card, htopCard, htopD]
    omega
  obtain ⟨tail, htailSub, htailCard⟩ :=
    Finset.exists_subset_card_eq (s := available) htailLe
  let tailSum : A := ∑ i ∈ tail, occurrenceValue xs i
  let h : A := y - tailSum - Nat.card A • C.beta
  have hh : h ∈ C.H := by
    rw [hH]
    trivial
  obtain ⟨coreSel, hcoreSelSub, hcoreSelCard, hcoreSelSum⟩ :=
    C.core_full h hh
  have hcoreTail : Disjoint coreSel tail := by
    rw [Finset.disjoint_left]
    intro i hiCore hiTail
    have hiAvailable := htailSub hiTail
    exact (Finset.mem_sdiff.mp hiAvailable).2
      (hcoreSelSub hiCore)
  refine ⟨coreSel ∪ tail, ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hcoreTail, hcoreSelCard,
      htailCard, htopCard]
    exact Nat.add_sub_of_le hnA
  · rw [Finset.sum_union hcoreTail, hcoreSelSum, htopCard]
    dsimp only [h, tailSum]
    abel

/-- Once the complete canonical container crosses the source-coset
threshold, a proper Step 1 subgroup is already an honest ordinary GMO
concentration witness. -/
theorem nonempty_concentration_of_card_lower
    {xs : List A} (C : CanonicalOrdinaryGMOStep1Core xs)
    (hproper : C.H < ⊤)
    (hcard :
      xs.length - Nat.card (A ⧸ C.H) + 2 ≤ C.container.card) :
    Nonempty (OrdinaryGMOConcentration xs) := by
  apply ordinaryGMOConcentration_of_coset_card
    xs C.H hproper C.beta
  rw [← C.container_eq]
  exact hcard

end CanonicalOrdinaryGMOStep1Core

end GaoLean

#print axioms GaoLean.canonicalOrdinaryGMOStep1Core_bot_of_excess_occurrenceFiber
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.ordinarySpectrumFull_of_H_eq_top
#print axioms GaoLean.CanonicalOrdinaryGMOStep1Core.nonempty_concentration_of_card_lower
