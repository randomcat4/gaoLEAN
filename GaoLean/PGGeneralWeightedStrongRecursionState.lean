import GaoLean.PGGeneralWeightedStep1Affine
import GaoLean.PGGeneralWeightedSubsequence
import GaoLean.PGInduction

/-!
# Overgroup-aware state for the strong general-weight recursion

The corollary-level existence and concentration providers forget data that is
needed by the strict-subgroup recursion in GMO Theorem 1.1.  This file records
that data without asserting that the state exists.  In particular, the state
retains the affine overgroup input, an occurrence-labelled full core, one
common weighted centre, periodicity, and the small carrier from equations
(3)--(9).

Equation (8), including its exact translated-spectrum equality and centre
membership, is intentionally part of the frozen output state.  Recording it
does not construct it: the later local recursion step must supply the state.
-/

namespace GaoLean

open scoped Pointwise

universe u

variable {G₀ : Type u} [AddCommGroup G₀] [Fintype G₀]

noncomputable local instance strongRecursionStateDecidableEq
    {X : Type*} : DecidableEq X :=
  Classical.decEq X

/-- Exact weighted spectrum supported on a literal selection of source
occurrences.  Passing through `occurrenceSubsequence` retains repetitions and
the increasing source-index order. -/
noncomputable def weightedExactSpectrumOn
    (W : Set ℤ) (xs : List G₀) (I : Selection xs) (n : ℕ) : Finset G₀ :=
  weightedExactSpectrum W (occurrenceSubsequence xs I) n

/-- Exact weighted spectrum whose witnesses use only the labelled source
occurrences in `I`.  This is deliberately not a spectrum of source values:
equal values at different positions remain different usable occurrences. -/
noncomputable def weightedExactSpectrumWithin
    (W : Set ℤ) (xs : List G₀) (I : Selection xs) (n : ℕ) : Finset G₀ := by
  classical
  exact Finset.univ.filter fun y ↦
    ∃ z : HasWeightedSumOfCard W xs n y, z.selected ⊆ I

@[simp]
theorem mem_weightedExactSpectrumWithin_iff
    (W : Set ℤ) (xs : List G₀) (I : Selection xs) (n : ℕ) (y : G₀) :
    y ∈ weightedExactSpectrumWithin W xs I n ↔
      ∃ z : HasWeightedSumOfCard W xs n y, z.selected ⊆ I := by
  classical
  simp [weightedExactSpectrumWithin]

/-- Translate a finite spectrum by one fixed group element. -/
noncomputable def translateWeightedSpectrum
    (c : G₀) (T : Finset G₀) : Finset G₀ :=
  T.image fun y ↦ c + y

omit [Fintype G₀] in
@[simp]
theorem mem_translateWeightedSpectrum_iff
    (c z : G₀) (T : Finset G₀) :
    z ∈ translateWeightedSpectrum c T ↔
      ∃ y ∈ T, c + y = z := by
  classical
  constructor
  · intro hz
    obtain ⟨y, hy, hyz⟩ := Finset.mem_image.mp hz
    exact ⟨y, hy, hyz⟩
  · rintro ⟨y, hy, hyz⟩
    exact Finset.mem_image.mpr ⟨y, hy, hyz⟩

/-- The strong occurrence-faithful state corresponding to equations (3)--(9)
of GMO Theorem 1.1.

`G` is the recursive subgroup inside an ambient overgroup `G₀`; `gamma` and
`delta` are the incoming source and weighted affine centres.  The subgroup
`H` and the output centres remain in that same overgroup.  The field
`core_full` is the operational form of the full `|H| beta + H` spectrum: it
produces an actual labelled selection for every element of `H`.

The two small-spectrum fields faithfully freeze equation (8), which is part
of the strong theorem's conclusion and in particular entails the final
`n beta` witness.  They are state obligations, not a proof that such a state
has been constructed. -/
structure GeneralWeightedStrongRecursionState
    (W : Set ℤ) (G : AddSubgroup G₀) (gamma delta : G₀)
    (xs : List G₀) (n D : ℕ) where
  H : AddSubgroup G₀
  H_le_G : H ≤ G
  alpha : G₀
  beta : G₀
  alpha_sub_gamma_mem : alpha - gamma ∈ G
  beta_sub_delta_mem : beta - delta ∈ G
  retained : Selection xs
  core : Selection xs
  small : Selection xs
  core_subset_retained : core ⊆ retained
  retained_sourceCoset :
    ∀ i ∈ retained, occurrenceValue xs i - alpha ∈ H
  retained_weightCoset :
    ∀ i ∈ retained, ∀ w ∈ W,
      w • occurrenceValue xs i - beta ∈ H
  retained_card_lower :
    min xs.length
      (xs.length - Nat.card (G ⧸ H.addSubgroupOf G) + 2) ≤
        retained.card
  DH : ℕ
  DQ : ℕ
  DH_exact : IsWeightedDavenportConstant W H DH
  DQ_exact : IsWeightedDavenportConstant W
    (G ⧸ H.addSubgroupOf G) DQ
  core_card : core.card = Nat.card H + DH - 1
  core_full :
    ∀ h : H,
      ∃ z : HasWeightedSumOfCard W xs (Nat.card H)
          (Nat.card H • beta + (h : G₀)),
        z.selected ⊆ core
  r : ℕ
  r_eq_complement_card : r =
    ((Finset.univ : Selection xs) \ retained).card
  r_le_quotient_sub_two :
    r ≤ Nat.card (G ⧸ H.addSubgroupOf G) - 2
  outside_union_core_subset_small :
    ((Finset.univ : Selection xs) \ retained) ∪ core ⊆ small
  H_card_add_r_le_n : Nat.card H + r ≤ n
  small_card :
    small.card = Nat.card H + r + DH + DQ - 2
  small_card_upper :
    small.card ≤ Nat.card H + r + D - 1
  spectrum_periodic : H ≤ weightedSpectrumStabilizer W xs n
  spectrum_reduction :
    weightedExactSpectrum W xs n =
      translateWeightedSpectrum
        ((n - Nat.card H - r) • beta)
        (weightedExactSpectrumOn W xs small (Nat.card H + r))
  small_center_mem :
    (Nat.card H + r) • beta ∈
      weightedExactSpectrumOn W xs small (Nat.card H + r)

namespace GeneralWeightedStrongRecursionState

variable {W : Set ℤ} {G : AddSubgroup G₀} {gamma delta : G₀}
  {xs : List G₀} {n D : ℕ}

/-- The complement count is genuinely occurrence-labelled and completes the
retained count to the source length. -/
theorem retained_card_add_r
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    S.retained.card + S.r = xs.length := by
  classical
  rw [S.r_eq_complement_card]
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ S.retained)]
  have hle : S.retained.card ≤ xs.length := by
    simpa [Occurrence] using
      Finset.card_le_card (Finset.subset_univ S.retained)
  simp only [Finset.card_univ, Fintype.card_fin]
  omega

/-- The stored small carrier contains every omitted occurrence and every
full-core occurrence, exactly the occurrence form of `S S'⁻¹ S'' | S₀`. -/
theorem complement_subset_small
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    (Finset.univ : Selection xs) \ S.retained ⊆ S.small :=
  Finset.subset_union_left.trans S.outside_union_core_subset_small

theorem core_subset_small
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    S.core ⊆ S.small :=
  Finset.subset_union_right.trans S.outside_union_core_subset_small

theorem core_card_le_retained_card
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    S.core.card ≤ S.retained.card :=
  Finset.card_le_card S.core_subset_retained

/-- Lift the operational full core of a recursive state on an occurrence
subsequence back to the original source labels.

This transports only the fields that are genuinely invariant under the
occurrence embedding: the stored core cardinality and every exact full-core
witness.  It does not claim that the recursive retained bound, complement
count, quotient Davenport constant, or spectrum-reduction fields lift to the
larger source sequence. -/
theorem exists_liftedFullCore
    {xs : List G₀} {R : Selection xs}
    (S : GeneralWeightedStrongRecursionState W G gamma delta
      (occurrenceSubsequence xs R) n D) :
    ∃ core : Selection xs,
      core ⊆ R ∧
      core.card = Nat.card S.H + S.DH - 1 ∧
      ∀ h : S.H,
        ∃ z : HasWeightedSumOfCard W xs (Nat.card S.H)
            (Nat.card S.H • S.beta + (h : G₀)),
          z.selected ⊆ core := by
  classical
  let core : Selection xs :=
    liftOccurrenceSubsequenceSelection xs R S.core
  refine ⟨core, liftOccurrenceSubsequenceSelection_subset xs R S.core,
    ?_, ?_⟩
  · rw [show core.card = S.core.card by
      exact card_liftOccurrenceSubsequenceSelection xs R S.core]
    exact S.core_card
  · intro h
    obtain ⟨z, hz⟩ := S.core_full h
    let zLift := z.liftOccurrenceSubsequence
    refine ⟨zLift, ?_⟩
    intro i hi
    change i ∈ liftOccurrenceSubsequenceSelection xs R z.selected at hi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp hi
    apply Finset.mem_map.mpr
    exact ⟨j, hz hj, rfl⟩

/-- The operational `core_full` field and the common weighted coset condition
recover equation (7) as an exact equality of the spectrum supported on the
labelled core with the affine coset `|H| beta + H`. -/
theorem core_exactSpectrumWithin_eq
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    weightedExactSpectrumWithin W xs S.core (Nat.card S.H) =
      translateWeightedSpectrum (Nat.card S.H • S.beta)
        (weightedStep1SubgroupFinset S.H) := by
  classical
  ext y
  rw [mem_weightedExactSpectrumWithin_iff,
    mem_translateWeightedSpectrum_iff]
  constructor
  · rintro ⟨z, hzcore⟩
    have hsum :
        (∑ i ∈ z.selected,
          (z.weights i • occurrenceValue xs i - S.beta)) ∈ S.H := by
      apply S.H.sum_mem
      intro i hi
      exact S.retained_weightCoset i
        (S.core_subset_retained (hzcore hi)) (z.weights i)
        (z.weights_mem i hi)
    have hdiff : y - Nat.card S.H • S.beta ∈ S.H := by
      have hsum' :
          (∑ i ∈ z.selected, z.weights i • occurrenceValue xs i) -
              z.selected.card • S.beta ∈ S.H := by
        simpa [Finset.sum_sub_distrib] using hsum
      simpa only [z.weighted_sum, z.card_selected] using hsum'
    refine ⟨y - Nat.card S.H • S.beta, ?_, by abel⟩
    exact (mem_weightedStep1SubgroupFinset S.H _).2 hdiff
  · rintro ⟨h, hh, hhy⟩
    have hhH : h ∈ S.H :=
      (mem_weightedStep1SubgroupFinset S.H h).1 hh
    obtain ⟨z, hzcore⟩ := S.core_full ⟨h, hhH⟩
    refine ⟨{
      selected := z.selected
      weights := z.weights
      weights_mem := z.weights_mem
      card_selected := z.card_selected
      weighted_sum := z.weighted_sum.trans hhy
    }, hzcore⟩

/-- Equation (8)'s smaller-spectrum centre and its exact translation imply
the ambient exact `n beta` membership. -/
theorem nsmul_beta_mem_weightedExactSpectrum
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    n • S.beta ∈ weightedExactSpectrum W xs n := by
  classical
  rw [S.spectrum_reduction]
  rw [mem_translateWeightedSpectrum_iff]
  refine ⟨(Nat.card S.H + S.r) • S.beta, S.small_center_mem, ?_⟩
  rw [← add_nsmul]
  congr 1
  rw [Nat.sub_sub, Nat.sub_add_cancel S.H_card_add_r_le_n]

/-- The strong state supplies the exact prescribed `n beta` witness, hence
the corollary-level existence conclusion, without storing that conclusion as
a state field. -/
theorem nonempty_hasWeightedSumOfCard_nsmul_beta
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    Nonempty (HasWeightedSumOfCard W xs n (n • S.beta)) :=
  (mem_weightedExactSpectrum_iff W xs n (n • S.beta)).1
    S.nsmul_beta_mem_weightedExactSpectrum

theorem weightedGMOExistenceConclusion
    (S : GeneralWeightedStrongRecursionState W G gamma delta xs n D) :
    WeightedGMOExistenceConclusion W xs n :=
  ⟨S.beta, S.nonempty_hasWeightedSumOfCard_nsmul_beta⟩

end GeneralWeightedStrongRecursionState

/-- Equation (3), kept as an occurrence-faithful overgroup input predicate.
Both the source and every allowed weighted value have fixed affine centres. -/
structure GeneralWeightedOvergroupInput
    (W : Set ℤ) (G : AddSubgroup G₀) (gamma delta : G₀)
    (xs : List G₀) : Prop where
  source_mem :
    ∀ i : Occurrence xs, occurrenceValue xs i - gamma ∈ G
  weighted_mem :
    ∀ i : Occurrence xs, ∀ w ∈ W,
      w • occurrenceValue xs i - delta ∈ G

/-- Honest strong-recursion goal at one subgroup of the fixed overgroup.  It
returns the equation-(3)--(9) state, not merely either corollary. -/
def GeneralWeightedStrongRecursionAt
    (G : AddSubgroup G₀) : Prop :=
  ∀ (W : Set ℤ), W.Nonempty → IsPrimitiveWeightSet W →
    ∀ (D : ℕ), IsWeightedDavenportConstant W G D →
      ∀ (gamma delta : G₀) (xs : List G₀) (n : ℕ),
        Nat.card G ≤ n →
        GeneralWeightedOvergroupInput W G gamma delta xs →
        n + D - 1 ≤ xs.length →
        Nonempty
          (GeneralWeightedStrongRecursionState W G gamma delta xs n D)

/-- The only recursion hypothesis permitted at `G`: the strong theorem is
available for strict subgroups of `G`, never for `G` itself. -/
def GeneralWeightedStrictSubgroupRecursionHypothesis
    (G : AddSubgroup G₀) : Prop :=
  ∀ K : AddSubgroup G₀, K < G → GeneralWeightedStrongRecursionAt K

/-- Interface for the substantive local proof step.  This is conditional data
to be implemented by later mathematics; neither this interface nor an engine
value is supplied in this file, so the declaration is not a completed proof
of the strong theorem. -/
structure GeneralWeightedStrongRecursionStepInterface
    (G : AddSubgroup G₀) : Prop where
  run : GeneralWeightedStrictSubgroupRecursionHypothesis G →
    GeneralWeightedStrongRecursionAt G

/-- A uniform collection of honest strict-subgroup steps. -/
structure GeneralWeightedStrongRecursionEngine (G₀ : Type u)
    [AddCommGroup G₀] [Fintype G₀] : Prop where
  step : ∀ G : AddSubgroup G₀,
    GeneralWeightedStrongRecursionStepInterface G

/-- Once the local step interface is genuinely implemented, ordinary strong
induction on additive subgroups eliminates every recursive hypothesis. -/
theorem generalWeightedStrongRecursionAt_of_engine
    (engine : GeneralWeightedStrongRecursionEngine G₀) :
    ∀ G : AddSubgroup G₀, GeneralWeightedStrongRecursionAt G := by
  apply addSubgroup_strongInduction
  intro G ih
  exact (engine.step G).run ih

end GaoLean

#print axioms GaoLean.GeneralWeightedStrongRecursionState.retained_card_add_r
#print axioms GaoLean.GeneralWeightedStrongRecursionState.exists_liftedFullCore
#print axioms GaoLean.GeneralWeightedStrongRecursionState.core_exactSpectrumWithin_eq
#print axioms GaoLean.GeneralWeightedStrongRecursionState.nsmul_beta_mem_weightedExactSpectrum
#print axioms GaoLean.GeneralWeightedStrongRecursionState.nonempty_hasWeightedSumOfCard_nsmul_beta
#print axioms GaoLean.GeneralWeightedStrongRecursionState.weightedGMOExistenceConclusion
#print axioms GaoLean.generalWeightedStrongRecursionAt_of_engine
