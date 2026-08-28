import GaoLean.PGGMOOrdinaryComplement
import GaoLean.PGGMOOrdinarySeed
import GaoLean.PGGMOOrdinaryStep1

/-!
# Honest base cases for the ordinary prescribed-target theorem

This module closes the two source-faithful base branches needed by the final
ordinary GMO driver.

* Full `r`-spectrum at a source of exact length `target + r` is dual to full
  `target`-spectrum by taking the literal complement in all occurrences.
* A value occurring more than `d*(A)` times supplies the `H = bot` Step 1
  core.  The final target is then obtained from `PGGMOOrdinaryStep1`; it is
  not stored as an input field.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Complement duality in the literal full occurrence universe.  Repeated
values remain distinguished by their source positions. -/
theorem ordinarySpectrumFull_complement_univ
    {xs : List A} {target r : ℕ}
    (hlen : xs.length = target + r)
    (hfull : OrdinarySpectrumFull xs r) :
    OrdinarySpectrumFull xs target := by
  classical
  intro y
  let total : A := ∑ i : Occurrence xs, occurrenceValue xs i
  obtain ⟨D, hDcard, hDsum⟩ := hfull (total - y)
  let I : Selection xs := Finset.univ \ D
  have hDsub : D ⊆ (Finset.univ : Selection xs) := Finset.subset_univ D
  refine ⟨I, ?_, ?_⟩
  · dsimp only [I]
    rw [Finset.card_sdiff_of_subset hDsub, hDcard]
    have hunivCard : (Finset.univ : Selection xs).card = xs.length := by
      simp
    rw [hunivCard]
    omega
  · have hsplit :=
      (Finset.univ : Selection xs).sum_inter_add_sum_sdiff D
        (occurrenceValue xs)
    rw [Finset.inter_eq_right.mpr hDsub, hDsum] at hsplit
    dsimp only [I]
    have hcancel := congrArg (fun z : A => z - (total - y)) hsplit
    dsimp only [total] at hcancel
    calc
      (∑ i ∈ (Finset.univ \ D : Selection xs), occurrenceValue xs i) =
          (∑ i : Occurrence xs, occurrenceValue xs i) -
            ((∑ i : Occurrence xs, occurrenceValue xs i) - y) := by
        simpa only [add_sub_cancel_left] using hcancel
      _ = y := by abel

/-- A full exact spectrum immediately gives the weaker prescribed-multiple
target by choosing target value `0 = n • 0`. -/
theorem ordinaryGMOTargetOutput_nonempty_of_spectrumFull
    {xs : List A} {n : ℕ} (hfull : OrdinarySpectrumFull xs n) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  obtain ⟨I, hIcard, hIsum⟩ := hfull 0
  exact ⟨{
    selected := I
    card_selected := hIcard
    sum_mem_target := ⟨0, by simpa using hIsum⟩
  }⟩

/-- Full `r`-spectrum at complementary source length closes the prescribed
target branch. -/
theorem ordinaryGMOTargetOutput_nonempty_of_complement_spectrumFull
    {xs : List A} {target r : ℕ}
    (hlen : xs.length = target + r)
    (hfull : OrdinarySpectrumFull xs r) :
    Nonempty (OrdinaryGMOTargetOutput xs target) :=
  ordinaryGMOTargetOutput_nonempty_of_spectrumFull
    (ordinarySpectrumFull_complement_univ hlen hfull)

/-- The canonical `d*` of the trivial additive subgroup is zero.  This is
derived from subgroup--quotient convolution and invariance under the genuine
equivalence `A / bot ≃+ A`, rather than postulated as a simplification rule. -/
theorem pGroupDStar_addSubgroup_bot :
    pGroupDStar (⊥ : AddSubgroup A) = 0 := by
  have hconv := pGroupDStar_subgroup_quotient_le (⊥ : AddSubgroup A)
  have hquot : pGroupDStar (A ⧸ (⊥ : AddSubgroup A)) = pGroupDStar A :=
    pGroupDStar_addEquiv (QuotientAddGroup.quotientBot (G := A))
  rw [hquot] at hconv
  omega

/-- A fiber strictly larger than `d*(A)` is exactly the trivial-subgroup
Step 1 base core: choose one genuine occurrence as the full singleton core,
while retaining the entire large fiber as its affine container. -/
theorem ordinaryGMOStep1Core_bot_of_excess_occurrenceFiber
    (xs : List A) (a : A)
    (hexcess : pGroupDStar A < (occurrenceFiber xs a).card) :
    Nonempty (OrdinaryGMOStep1Core xs) := by
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

/-- High multiplicity closes every admissible prescribed length through the
honest `H = bot` Step 1 core. -/
theorem ordinaryGMOTargetOutput_nonempty_of_excess_occurrenceFiber
    (xs : List A) (a : A) (n : ℕ)
    (hexcess : pGroupDStar A < (occurrenceFiber xs a).card)
    (hnA : Nat.card A ≤ n)
    (hlen : n + pGroupDStar A ≤ xs.length) :
    Nonempty (OrdinaryGMOTargetOutput xs n) := by
  obtain ⟨C⟩ := ordinaryGMOStep1Core_bot_of_excess_occurrenceFiber
    xs a hexcess
  exact C.nonempty_target n hnA hlen

end GaoLean

#print axioms GaoLean.ordinarySpectrumFull_complement_univ
#print axioms GaoLean.ordinaryGMOTargetOutput_nonempty_of_spectrumFull
#print axioms GaoLean.ordinaryGMOTargetOutput_nonempty_of_complement_spectrumFull
#print axioms GaoLean.pGroupDStar_addSubgroup_bot
#print axioms GaoLean.ordinaryGMOStep1Core_bot_of_excess_occurrenceFiber
#print axioms GaoLean.ordinaryGMOTargetOutput_nonempty_of_excess_occurrenceFiber
