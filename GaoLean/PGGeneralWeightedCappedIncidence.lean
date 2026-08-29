import GaoLean.PGGeneralWeightedQuotient
import GaoLean.PGGeneralWeightedDavenportMinimum

/-!
# Capped incidence for arbitrary weighted occurrence layers

The aperiodic DGM branch needs more than the baseline contribution of one
incidence per layer.  Every layer with at least two values contributes one
additional unit, even after all value multiplicities are capped at the target
length.  This file proves that statement for an arbitrary finite
setpartition, then specializes it to general weighted occurrence blocks.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- Number of literal list layers containing at least two values.  Equal
layers at different positions are counted separately. -/
def nonsingletonLayerCount : List (Finset A) → ℕ
  | [] => 0
  | B :: P => (if 2 ≤ B.card then 1 else 0) + nonsingletonLayerCount P

/-- Number of literal list layers that are singletons. -/
def singletonLayerCount : List (Finset A) → ℕ
  | [] => 0
  | B :: P => (if B.card = 1 then 1 else 0) + singletonLayerCount P

@[simp]
theorem nonsingletonLayerCount_nil :
    nonsingletonLayerCount ([] : List (Finset A)) = 0 := rfl

@[simp]
theorem nonsingletonLayerCount_cons (B : Finset A) (P : List (Finset A)) :
    nonsingletonLayerCount (B :: P) =
      (if 2 ≤ B.card then 1 else 0) + nonsingletonLayerCount P := rfl

@[simp]
theorem singletonLayerCount_nil :
    singletonLayerCount ([] : List (Finset A)) = 0 := rfl

@[simp]
theorem singletonLayerCount_cons (B : Finset A) (P : List (Finset A)) :
    singletonLayerCount (B :: P) =
      (if B.card = 1 then 1 else 0) + singletonLayerCount P := rfl

/-- For a nonempty setpartition, every literal layer is either a singleton
or a nonsingleton, and the occurrence-sensitive counts partition the list. -/
theorem singletonLayerCount_add_nonsingletonLayerCount
    (P : List (Finset A)) (hP : IsNonemptySetPartition P) :
    singletonLayerCount P + nonsingletonLayerCount P = P.length := by
  induction P with
  | nil => simp
  | cons B P ih =>
      have hBpos : 1 ≤ B.card :=
        Finset.card_pos.mpr (hP B (by simp))
      have hP' : IsNonemptySetPartition P := by
        intro C hC
        exact hP C (by simp [hC])
      have htail := ih hP'
      simp only [singletonLayerCount_cons, nonsingletonLayerCount_cons,
        List.length_cons]
      by_cases hBone : B.card = 1
      · simp [hBone]
        omega
      · have hBtwo : 2 ≤ B.card := by omega
        simp [hBone, hBtwo]
        omega

/-- A nonempty layer contributes one incidence, and a nonsingleton layer
contributes one further incidence. -/
theorem length_add_nonsingletonLayerCount_le_sum_card
    (P : List (Finset A)) (hP : IsNonemptySetPartition P) :
    P.length + nonsingletonLayerCount P ≤ (P.map Finset.card).sum := by
  induction P with
  | nil => simp
  | cons B P ih =>
      have hBpos : 1 ≤ B.card :=
        Finset.card_pos.mpr (hP B (by simp))
      have hP' : IsNonemptySetPartition P := by
        intro C hC
        exact hP C (by simp [hC])
      have htail := ih hP'
      simp only [List.length_cons, nonsingletonLayerCount_cons,
        List.map_cons, List.sum_cons]
      split_ifs with hBtwo
      · omega
      · omega

/-- No raw value multiplicity can exceed the number of literal layers. -/
theorem rawLayerMultiplicity_le_length
    (P : List (Finset A)) (x : A) :
    rawLayerMultiplicity P x ≤ P.length := by
  classical
  induction P with
  | nil => simp [rawLayerMultiplicity]
  | cons B P ih =>
      by_cases hx : x ∈ B
      · rw [rawLayerMultiplicity_cons_of_mem B P x hx]
        simp only [List.length_cons]
        omega
      · rw [rawLayerMultiplicity_cons_of_not_mem B P x hx]
        simp only [List.length_cons]
        omega

/-- Numerical two-bin principle behind the capped-incidence estimate.  If
all coordinates have mass at most `m` and total mass at least `m+k`, then
capping at `n ≤ m` preserves at least `n + min n k` mass. -/
theorem add_min_le_sum_min_of_sum_ge_add_of_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (f : ι → ℕ) (m k n : ℕ)
    (hnm : n ≤ m)
    (hmax : ∀ x : ι, f x ≤ m)
    (htotal : m + k ≤ ∑ x : ι, f x) :
    n + min n k ≤ ∑ x : ι, min n (f x) := by
  classical
  by_cases hheavy : ∃ x : ι, n ≤ f x
  · obtain ⟨x, hx⟩ := hheavy
    let s : Finset ι := Finset.univ.erase x
    have hsplit : f x + ∑ y ∈ s, f y = ∑ y : ι, f y := by
      dsimp only [s]
      have h := Finset.sum_erase_add (Finset.univ : Finset ι) f
        (Finset.mem_univ x)
      omega
    have hkrest : k ≤ ∑ y ∈ s, f y := by
      have hxmax := hmax x
      omega
    have hrestCap : min n k ≤ ∑ y ∈ s, min n (f y) := by
      calc
        min n k ≤ min n (∑ y ∈ s, f y) :=
          min_le_min_left n hkrest
        _ ≤ ∑ y ∈ s, min n (f y) :=
          min_sum_le_sum_min s f n
    rw [← Finset.sum_erase_add _ (fun y ↦ min n (f y))
      (Finset.mem_univ x), min_eq_left hx]
    dsimp only [s] at hrestCap
    omega
  · push Not at hheavy
    have hcap : ∀ x : ι, min n (f x) = f x := by
      intro x
      exact min_eq_right (Nat.le_of_lt (hheavy x))
    simp_rw [hcap]
    exact (Nat.add_le_add hnm (min_le_right n k)).trans htotal

/-- General capped-incidence lower bound: one capped contribution for every
requested layer, plus one for every nonsingleton layer up to the same cap. -/
theorem add_min_nonsingletonLayerCount_le_rawDgmCappedMultiplicitySum
    (P : List (Finset A)) (hP : IsNonemptySetPartition P)
    (n : ℕ) (hn : n ≤ P.length) :
    n + min n (nonsingletonLayerCount P) ≤
      rawDgmCappedMultiplicitySum P n := by
  classical
  unfold rawDgmCappedMultiplicitySum
  apply add_min_le_sum_min_of_sum_ge_add_of_le
      (fun x : A ↦ rawLayerMultiplicity P x)
      P.length (nonsingletonLayerCount P) n hn
  · exact rawLayerMultiplicity_le_length P
  · rw [sum_rawLayerMultiplicity]
    exact length_add_nonsingletonLayerCount_le_sum_card P hP

/-- Literal number of weighted source occurrences whose weighted value block
has at least two elements. -/
noncomputable def weightedNonsingletonOccurrenceCount
    (W : Set ℤ) (xs : List A) : ℕ :=
  nonsingletonLayerCount (weightedOccurrenceSetpartition W xs)

/-- Literal number of weighted source occurrences whose weighted value block
is a singleton. -/
noncomputable def weightedSingletonOccurrenceCount
    (W : Set ℤ) (xs : List A) : ℕ :=
  singletonLayerCount (weightedOccurrenceSetpartition W xs)

/-- Singleton and nonsingleton weighted occurrence layers partition all
source positions whenever the weight set is nonempty. -/
theorem weightedSingleton_add_weightedNonsingleton
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) :
    weightedSingletonOccurrenceCount W xs +
      weightedNonsingletonOccurrenceCount W xs = xs.length := by
  simpa [weightedSingletonOccurrenceCount,
    weightedNonsingletonOccurrenceCount] using
      singletonLayerCount_add_nonsingletonLayerCount
        (weightedOccurrenceSetpartition W xs)
        (weightedOccurrenceSetpartition_isNonempty hW xs)

/-- Weighted specialization of the general capped-incidence estimate. -/
theorem weighted_add_min_nonsingleton_le_rawDgmCappedMultiplicitySum
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A)
    (n : ℕ) (hn : n ≤ xs.length) :
    n + min n (weightedNonsingletonOccurrenceCount W xs) ≤
      rawDgmCappedMultiplicitySum
        (weightedOccurrenceSetpartition W xs) n := by
  classical
  apply add_min_nonsingletonLayerCount_le_rawDgmCappedMultiplicitySum
  · exact weightedOccurrenceSetpartition_isNonempty hW xs
  · simpa using hn

/-- In the aperiodic branch, `|A| - 1` nonsingleton weighted occurrence
layers already force the exact weighted spectrum to fill the ambient group.

This is the arbitrary-weight analogue of the elementary full-spectrum half
of Step 6: capped incidence contributes at least `n + |A| - 1`, while DGM
with trivial stabilizer converts that contribution into `|A|` distinct
exact weighted sums. -/
theorem weightedExactSpectrum_eq_univ_of_aperiodic_of_manyNonsingleton
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (n : ℕ)
    (hn : Nat.card A ≤ n) (hnlen : n ≤ xs.length)
    (hstab : (weightedExactSpectrum W xs n).addStab = {0})
    (hmany : Nat.card A - 1 ≤
      weightedNonsingletonOccurrenceCount W xs) :
    weightedExactSpectrum W xs n = Finset.univ := by
  classical
  let P := weightedOccurrenceSetpartition W xs
  let T := layerSubsumSpectrum P n
  have hnpos : 1 ≤ n := (Nat.card_pos.trans_le hn)
  have hTeq : T = weightedExactSpectrum W xs n := by
    simpa [T, P] using
      (weightedExactSpectrum_eq_layerSubsumSpectrum W xs n).symm
  have hTnonempty : T.Nonempty := by
    rw [hTeq]
    exact weightedExactSpectrum_nonempty hW xs n hnlen
  have hTstab : T.addStab = {0} := by
    simpa [hTeq] using hstab
  have hraw : stabilizerDgmCappedMultiplicitySum T P n =
      rawDgmCappedMultiplicitySum P n :=
    stabilizerDgmCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
      T hTnonempty hTstab P n
  have hcapped :=
    weighted_add_min_nonsingleton_le_rawDgmCappedMultiplicitySum
      hW xs n hnlen
  have hminimum : n + Nat.card A - 1 ≤
      rawDgmCappedMultiplicitySum P n := by
    have hcardPred : Nat.card A - 1 ≤ n := by omega
    have hmin : Nat.card A - 1 ≤
        min n (weightedNonsingletonOccurrenceCount W xs) := by
      exact le_min hcardPred hmany
    change n + Nat.card A - 1 ≤
      rawDgmCappedMultiplicitySum
        (weightedOccurrenceSetpartition W xs) n
    omega
  have hbound := weightedOccurrenceSetpartition_dgmBound_of_doubleInduction
    W hW xs n hnpos hnlen
  unfold DGMSetpartitionBound at hbound
  dsimp only at hbound
  have hstabCard : T.addStab.card = 1 := by
    rw [hTstab]
    simp
  have hboundT :
      (stabilizerDgmCappedMultiplicitySum T P n - n + 1) ≤ T.card := by
    simpa [T, P, hstabCard] using hbound
  have hTcard : Nat.card A ≤ T.card := by
    rw [hraw] at hboundT
    omega
  rw [weightedExactSpectrum_eq_layerSubsumSpectrum]
  apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
  simpa [T, P, Nat.card_eq_fintype_card] using hTcard

/-- Step 6 in the source's literal cardinality form.  At the critical source
length `|A| + D - 1`, having at most `D` singleton weighted layers leaves at
least `|A| - 1` nonsingleton layers; the preceding DGM argument then forces
the `|A|`-term weighted spectrum to be all of `A`. -/
theorem weightedExactSpectrum_card_eq_univ_of_aperiodic_of_singletonsAtMost
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (D : ℕ)
    (hDpos : 1 ≤ D)
    (hlen : Nat.card A + D - 1 ≤ xs.length)
    (hstab :
      (weightedExactSpectrum W xs (Nat.card A)).addStab = {0})
    (hsingle : weightedSingletonOccurrenceCount W xs ≤ D) :
    weightedExactSpectrum W xs (Nat.card A) = Finset.univ := by
  have hsplit := weightedSingleton_add_weightedNonsingleton hW xs
  have hmany : Nat.card A - 1 ≤
      weightedNonsingletonOccurrenceCount W xs := by
    omega
  apply weightedExactSpectrum_eq_univ_of_aperiodic_of_manyNonsingleton
      hW xs (Nat.card A) (by rfl) _ hstab hmany
  have hcardPos : 1 ≤ Nat.card A := Nat.card_pos
  omega

/-- The same full-spectrum branch stated with the canonical spectrum
stabilizer used by the general GMO induction driver. -/
theorem weightedExactSpectrum_card_eq_univ_of_bottomStabilizer_of_singletonsAtMost
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (D : ℕ)
    (hD : IsWeightedDavenportConstant W A D)
    (hlen : Nat.card A + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs (Nat.card A) = ⊥)
    (hsingle : weightedSingletonOccurrenceCount W xs ≤ D) :
    weightedExactSpectrum W xs (Nat.card A) = Finset.univ := by
  classical
  have hDpos : 1 ≤ D := weightedDavenportConstant_pos W D hD
  have hnlen : Nat.card A ≤ xs.length := by omega
  have hfinStab :
      (weightedExactSpectrum W xs (Nat.card A)).addStab = {0} := by
    ext x
    rw [← Finset.mem_coe,
      Finset.coe_addStab
        (weightedExactSpectrum_nonempty hW xs (Nat.card A) hnlen)]
    change x ∈ AddAction.stabilizer A
        (weightedExactSpectrum W xs (Nat.card A) : Set A) ↔
      x ∈ ({0} : Finset A)
    rw [← weightedSpectrumStabilizer, hstab]
    simp
  exact weightedExactSpectrum_card_eq_univ_of_aperiodic_of_singletonsAtMost
    hW xs D hDpos hlen hfinStab hsingle

/-- The full-spectrum Step 6 branch already contains the prescribed target
`|A| • 0 = 0`, hence gives the cardinal-case existence conclusion. -/
theorem weightedGMOExistenceConclusion_card_of_bottomStabilizer_of_singletonsAtMost
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (D : ℕ)
    (hD : IsWeightedDavenportConstant W A D)
    (hlen : Nat.card A + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs (Nat.card A) = ⊥)
    (hsingle : weightedSingletonOccurrenceCount W xs ≤ D) :
    WeightedGMOExistenceConclusion W xs (Nat.card A) := by
  have hfull :=
    weightedExactSpectrum_card_eq_univ_of_bottomStabilizer_of_singletonsAtMost
      hW xs D hD hlen hstab hsingle
  refine ⟨0, ?_⟩
  rw [← mem_weightedExactSpectrum_iff, hfull]
  simp

/-- Exact source Step 6 split at the critical cardinal target.  The DGM
branch closes unless at least `D + 1` weighted occurrence layers are
singletons; no structural conclusion is assumed in the remaining branch. -/
theorem weightedExactSpectrum_card_eq_univ_or_manySingleton_of_bottomStabilizer
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) (D : ℕ)
    (hD : IsWeightedDavenportConstant W A D)
    (hlen : Nat.card A + D - 1 ≤ xs.length)
    (hstab : weightedSpectrumStabilizer W xs (Nat.card A) = ⊥) :
    weightedExactSpectrum W xs (Nat.card A) = Finset.univ ∨
      D + 1 ≤ weightedSingletonOccurrenceCount W xs := by
  by_cases hsingle : weightedSingletonOccurrenceCount W xs ≤ D
  · exact Or.inl
      (weightedExactSpectrum_card_eq_univ_of_bottomStabilizer_of_singletonsAtMost
        hW xs D hD hlen hstab hsingle)
  · exact Or.inr (by omega)

end GaoLean

#print axioms GaoLean.length_add_nonsingletonLayerCount_le_sum_card
#print axioms GaoLean.singletonLayerCount_add_nonsingletonLayerCount
#print axioms GaoLean.rawLayerMultiplicity_le_length
#print axioms GaoLean.add_min_le_sum_min_of_sum_ge_add_of_le
#print axioms GaoLean.add_min_nonsingletonLayerCount_le_rawDgmCappedMultiplicitySum
#print axioms GaoLean.weighted_add_min_nonsingleton_le_rawDgmCappedMultiplicitySum
#print axioms GaoLean.weightedSingleton_add_weightedNonsingleton
#print axioms GaoLean.weightedExactSpectrum_eq_univ_of_aperiodic_of_manyNonsingleton
#print axioms GaoLean.weightedExactSpectrum_card_eq_univ_of_aperiodic_of_singletonsAtMost
#print axioms GaoLean.weightedExactSpectrum_card_eq_univ_of_bottomStabilizer_of_singletonsAtMost
#print axioms GaoLean.weightedGMOExistenceConclusion_card_of_bottomStabilizer_of_singletonsAtMost
#print axioms GaoLean.weightedExactSpectrum_card_eq_univ_or_manySingleton_of_bottomStabilizer
