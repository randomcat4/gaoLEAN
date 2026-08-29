import GaoLean.PGGeneralWeightedSelectionConvolution
import GaoLean.PGGeneralWeightedSingletonOccurrences

/-!
# Occurrence-faithful reserve extraction and assembly

All pools in this file are finsets of source positions.  Equal source values
at different positions are never identified.  The generic construction
extracts exactly `k` labels from `retained \ core`, records the literal
`Nat.sub` capacity, and feeds a weighted witness supported on that reserve
into the selection convolution interface.
-/

namespace GaoLean

universe u v

/-! ## Generic labelled reserve extraction -/

/-- Explicit data for `k` reserve labels drawn from the retained pool after
deleting the core labels. -/
structure OccurrenceReserveExtraction
    {α : Type u} (xs : List α)
    (retained core : Selection xs) (k : ℕ) where
  reserve : Selection xs
  reserve_subset_available : reserve ⊆ retained \ core
  reserve_card : reserve.card = k

namespace OccurrenceReserveExtraction

variable {α : Type u} {xs : List α}
  {retained core : Selection xs} {k : ℕ}

theorem reserve_subset_retained
    (R : OccurrenceReserveExtraction xs retained core k) :
    R.reserve ⊆ retained := by
  intro i hi
  exact (Finset.mem_sdiff.mp (R.reserve_subset_available hi)).1

theorem disjoint_core_reserve
    (R : OccurrenceReserveExtraction xs retained core k) :
    Disjoint core R.reserve := by
  rw [Finset.disjoint_left]
  intro i hiCore hiReserve
  exact (Finset.mem_sdiff.mp (R.reserve_subset_available hiReserve)).2 hiCore

theorem card_core_union_reserve
    (R : OccurrenceReserveExtraction xs retained core k) :
    (core ∪ R.reserve).card = core.card + k := by
  rw [Finset.card_union_of_disjoint R.disjoint_core_reserve, R.reserve_card]

theorem core_union_reserve_subset
    (R : OccurrenceReserveExtraction xs retained core k)
    (hcore : core ⊆ retained) :
    core ∪ R.reserve ⊆ retained := by
  intro i hi
  rcases Finset.mem_union.mp hi with hiCore | hiReserve
  · exact hcore hiCore
  · exact R.reserve_subset_retained hiReserve

end OccurrenceReserveExtraction

/-- Exact cardinality of the available retained pool.  The intersection is
necessary when no containment relation between `core` and `retained` is
assumed. -/
theorem card_retained_sdiff_core
    {α : Type u} {xs : List α}
    (retained core : Selection xs) :
    (retained \ core).card = retained.card - (core ∩ retained).card := by
  rw [Finset.card_sdiff]

/-- Familiar subtraction form when the core is already inside the retained
pool. -/
theorem card_retained_sdiff_core_of_subset
    {α : Type u} {xs : List α}
    {retained core : Selection xs} (hcore : core ⊆ retained) :
    (retained \ core).card = retained.card - core.card := by
  rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hcore]

/-- Boundary regression: without `core ⊆ retained`, replacing the
intersection by the full core cardinality is false even for two labelled
positions. -/
theorem card_sdiff_ne_card_sub_without_subset_regression :
    let retained : Finset (Fin 2) := {0}
    let core : Finset (Fin 2) := {1}
    (retained \ core).card ≠ retained.card - core.card := by
  decide

/-- Choose exactly `k` occurrence labels from the literal complement of the
core in the retained pool. -/
noncomputable def extractOccurrenceReserve
    {α : Type u} {xs : List α}
    (retained core : Selection xs) (k : ℕ)
    (hcap : k ≤ (retained \ core).card) :
    OccurrenceReserveExtraction xs retained core k := by
  classical
  let hex : ∃ reserve ⊆ retained \ core, reserve.card = k :=
    Finset.exists_subset_card_eq (s := retained \ core) hcap
  let reserve := Classical.choose hex
  have hreserve : reserve ⊆ retained \ core :=
    (Classical.choose_spec hex).1
  have hcard : reserve.card = k :=
    (Classical.choose_spec hex).2
  exact {
    reserve := reserve
    reserve_subset_available := hreserve
    reserve_card := hcard
  }

/-- A non-truncated additive budget implies the exact `Nat.sub` capacity.
No containment hypothesis is needed: core labels outside `retained` do not
consume retained capacity, while counting them in `core.card` only makes the
premise stronger. -/
theorem reserve_capacity_of_core_card_add_le
    {α : Type u} {xs : List α}
    {retained core : Selection xs} {k : ℕ}
    (hbudget : core.card + k ≤ retained.card) :
    k ≤ (retained \ core).card := by
  rw [card_retained_sdiff_core]
  have hinter : (core ∩ retained).card ≤ core.card :=
    Finset.card_le_card Finset.inter_subset_left
  omega

/-- Step-facing constructor using the common additive capacity premise. -/
noncomputable def extractOccurrenceReserveOfCoreCardAddLe
    {α : Type u} {xs : List α}
    (retained core : Selection xs) (k : ℕ)
    (hbudget : core.card + k ≤ retained.card) :
    OccurrenceReserveExtraction xs retained core k :=
  extractOccurrenceReserve retained core k
    (reserve_capacity_of_core_card_add_le hbudget)

/-! ## Literal singleton and nonsingleton occurrence pools -/

variable {A : Type v} [AddCommGroup A] [Fintype A]

/-- Literal complement of the singleton-layer occurrence pool. -/
noncomputable def weightedNonsingletonOccurrences
    (W : Set ℤ) (xs : List A) : Selection xs := by
  classical
  exact Finset.univ \ weightedSingletonOccurrences W xs

@[simp]
theorem mem_weightedNonsingletonOccurrences_iff
    (W : Set ℤ) (xs : List A) (i : Occurrence xs) :
    i ∈ weightedNonsingletonOccurrences W xs ↔
      (weightedValueBlock W (occurrenceValue xs i)).card ≠ 1 := by
  classical
  simp [weightedNonsingletonOccurrences,
    mem_weightedSingletonOccurrences_iff]

theorem disjoint_weightedSingletonOccurrences_weightedNonsingletonOccurrences
    (W : Set ℤ) (xs : List A) :
    Disjoint (weightedSingletonOccurrences W xs)
      (weightedNonsingletonOccurrences W xs) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiSingleton hiNonsingleton
  exact (Finset.mem_sdiff.mp hiNonsingleton).2 hiSingleton

theorem weightedSingletonOccurrences_union_weightedNonsingletonOccurrences
    (W : Set ℤ) (xs : List A) :
    weightedSingletonOccurrences W xs ∪
        weightedNonsingletonOccurrences W xs = Finset.univ := by
  classical
  rw [weightedNonsingletonOccurrences]
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

/-- The explicit nonsingleton selection has exactly the existing literal
nonsingleton-layer count. -/
theorem card_weightedNonsingletonOccurrences_eq_count
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A) :
    (weightedNonsingletonOccurrences W xs).card =
      weightedNonsingletonOccurrenceCount W xs := by
  classical
  have hdis :=
    disjoint_weightedSingletonOccurrences_weightedNonsingletonOccurrences W xs
  have hunion :=
    weightedSingletonOccurrences_union_weightedNonsingletonOccurrences W xs
  have hcardPartition :
      (weightedSingletonOccurrences W xs).card +
          (weightedNonsingletonOccurrences W xs).card = xs.length := by
    rw [← Finset.card_union_of_disjoint hdis, hunion]
    simp
  have hcountPartition := weightedSingleton_add_weightedNonsingleton hW xs
  have hsingleton := card_weightedSingletonOccurrences_eq_count W xs
  omega

/-- Choose an exact reserve from singleton-layer occurrences after deleting
an arbitrary labelled core. -/
noncomputable def extractWeightedSingletonReserve
    {W : Set ℤ} (xs : List A) (core : Selection xs) (k : ℕ)
    (hcap : k ≤
      (weightedSingletonOccurrences W xs \ core).card) :
    OccurrenceReserveExtraction xs
      (weightedSingletonOccurrences W xs) core k :=
  extractOccurrenceReserve (weightedSingletonOccurrences W xs) core k hcap

/-- Count-facing singleton reserve constructor. -/
noncomputable def extractWeightedSingletonReserveOfBudget
    {W : Set ℤ} (xs : List A) (core : Selection xs) (k : ℕ)
    (hbudget : core.card + k ≤
      (weightedSingletonOccurrences W xs).card) :
    OccurrenceReserveExtraction xs
      (weightedSingletonOccurrences W xs) core k :=
  extractOccurrenceReserveOfCoreCardAddLe
    (weightedSingletonOccurrences W xs) core k hbudget

/-- Singleton-count-facing reserve constructor. -/
noncomputable def extractWeightedSingletonReserveOfCountBudget
    {W : Set ℤ} (_hW : W.Nonempty) (xs : List A)
    (core : Selection xs) (k : ℕ)
    (hbudget : core.card + k ≤
      weightedSingletonOccurrenceCount W xs) :
    OccurrenceReserveExtraction xs
      (weightedSingletonOccurrences W xs) core k := by
  apply extractWeightedSingletonReserveOfBudget xs core k
  rw [card_weightedSingletonOccurrences_eq_count W xs]
  exact hbudget

/-- Choose an exact reserve from nonsingleton-layer occurrences after
deleting an arbitrary labelled core. -/
noncomputable def extractWeightedNonsingletonReserve
    {W : Set ℤ} (xs : List A) (core : Selection xs) (k : ℕ)
    (hcap : k ≤
      (weightedNonsingletonOccurrences W xs \ core).card) :
    OccurrenceReserveExtraction xs
      (weightedNonsingletonOccurrences W xs) core k :=
  extractOccurrenceReserve (weightedNonsingletonOccurrences W xs) core k hcap

/-- Numeric-count-facing nonsingleton reserve constructor. -/
noncomputable def extractWeightedNonsingletonReserveOfCountBudget
    {W : Set ℤ} (hW : W.Nonempty) (xs : List A)
    (core : Selection xs) (k : ℕ)
    (hbudget : core.card + k ≤
      weightedNonsingletonOccurrenceCount W xs) :
    OccurrenceReserveExtraction xs
      (weightedNonsingletonOccurrences W xs) core k := by
  apply extractOccurrenceReserveOfCoreCardAddLe
  rw [card_weightedNonsingletonOccurrences_eq_count hW xs]
  exact hbudget

/-! ## Assembly with exact weighted selections -/

/-- Feed an already constructed weighted reserve witness into the explicit
pool-preserving convolution output.  The extraction certificate supplies
both disjointness and the reserve-to-retained subset. -/
def OccurrenceReserveExtraction.assembleWeighted
    {W : Set ℤ} {xs : List A} {nCore nAdded : ℕ} {yCore yAdded : A}
    (hCore : HasWeightedSumOfCard W xs nCore yCore)
    (hAdded : HasWeightedSumOfCard W xs nAdded yAdded)
    (retained : Selection xs) (k : ℕ)
    (R : OccurrenceReserveExtraction xs retained hCore.selected k)
    (hAddedReserve : hAdded.selected ⊆ R.reserve) :
    WeightedSelectionPoolConvolutionOutput
      hCore hAdded R.reserve retained := by
  exact hCore.disjointUnionOfReserve hAdded R.reserve retained
    hAddedReserve R.reserve_subset_retained R.disjoint_core_reserve

/-- When the added witness uses the entire extracted reserve, its selected
cardinality is forced to be the reserve cardinality. -/
theorem OccurrenceReserveExtraction.added_card_eq_of_selected_eq_reserve
    {W : Set ℤ} {xs : List A} {nCore nAdded : ℕ} {yCore yAdded : A}
    (hCore : HasWeightedSumOfCard W xs nCore yCore)
    (hAdded : HasWeightedSumOfCard W xs nAdded yAdded)
    {retained : Selection xs} {k : ℕ}
    (R : OccurrenceReserveExtraction xs retained hCore.selected k)
    (hselected : hAdded.selected = R.reserve) :
    nAdded = k := by
  rw [← hAdded.card_selected, hselected, R.reserve_card]

/-- Data returned when the added witness uses the entire extracted reserve.
-/
structure WeightedFullReserveAssemblyOutput
    {W : Set ℤ} {xs : List A} {nCore nAdded : ℕ} {yCore yAdded : A}
    (hCore : HasWeightedSumOfCard W xs nCore yCore)
    (hAdded : HasWeightedSumOfCard W xs nAdded yAdded)
    (retained : Selection xs) (k : ℕ)
    (R : OccurrenceReserveExtraction xs retained hCore.selected k) where
  convolution : WeightedSelectionPoolConvolutionOutput
    hCore hAdded R.reserve retained
  added_card_eq : nAdded = k

/-- Full-reserve assembly.  Besides the convolution output, this records
that the added exact-cardinality parameter is literally the extracted
reserve size. -/
def OccurrenceReserveExtraction.assembleWeightedFullReserve
    {W : Set ℤ} {xs : List A} {nCore nAdded : ℕ} {yCore yAdded : A}
    (hCore : HasWeightedSumOfCard W xs nCore yCore)
    (hAdded : HasWeightedSumOfCard W xs nAdded yAdded)
    (retained : Selection xs) (k : ℕ)
    (R : OccurrenceReserveExtraction xs retained hCore.selected k)
    (hselected : hAdded.selected = R.reserve) :
    WeightedFullReserveAssemblyOutput hCore hAdded retained k R := {
  convolution := R.assembleWeighted hCore hAdded retained k
    (by rw [hselected])
  added_card_eq :=
    R.added_card_eq_of_selected_eq_reserve hCore hAdded hselected
}

end GaoLean

#print axioms GaoLean.card_retained_sdiff_core
#print axioms GaoLean.card_retained_sdiff_core_of_subset
#print axioms GaoLean.card_sdiff_ne_card_sub_without_subset_regression
#print axioms GaoLean.reserve_capacity_of_core_card_add_le
#print axioms GaoLean.extractOccurrenceReserve
#print axioms GaoLean.mem_weightedNonsingletonOccurrences_iff
#print axioms GaoLean.card_weightedNonsingletonOccurrences_eq_count
#print axioms GaoLean.extractWeightedSingletonReserveOfBudget
#print axioms GaoLean.extractWeightedSingletonReserveOfCountBudget
#print axioms GaoLean.extractWeightedNonsingletonReserveOfCountBudget
#print axioms GaoLean.OccurrenceReserveExtraction.assembleWeighted
#print axioms GaoLean.OccurrenceReserveExtraction.assembleWeightedFullReserve
