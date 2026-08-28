import GaoLean.PGGMOOrdinaryCappedLedger
import GaoLean.PGGMOTheorem21
import GaoLean.PGGMOPGroupInvariant

/-!
# Labelled pair-subgroup certificates for the ordinary GMO Step 1

This module isolates the occurrence/index-free core of Lemma 3.5 from
Grynkiewicz--Marchan--Ordaz in the ordinary singleton-weight case.  A labelled
index `i` contributes the honest pair `{0, v i}`; indices are never collapsed
to the value set of `v`.

The eventual existence theorem must assume a nontrivial ambient group.  This
is not cosmetic: for the trivial group, empty index type, and the empty map
`v`, both

* `∀ i, v i ≠ 0`, and
* `Nat.card Q - 1 ≤ Nat.card ι`

hold vacuously, while no nontrivial subgroup certificate can exist.  The
source Lemma 3.5 likewise explicitly assumes a nontrivial ambient subgroup.

The present file freezes the honest certificate and proves its labelled
subset-sum, retained/omitted, quotient-incidence, and p-group inheritance
ledgers.  It deliberately does not package certificate existence as a
provider or hypothesis.  The remaining construction is the strong-induction
greedy/stabilizer argument described at the end of the file.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

variable {Q : Type u} [AddCommGroup Q] [Fintype Q]
variable {ι : Type v} [Fintype ι]

noncomputable local instance pairSubgroupDecidableEq {α : Type*} :
    DecidableEq α := Classical.decEq α
noncomputable local instance pairSubgroupPropDecidable (p : Prop) :
    Decidable p := Classical.propDecidable p

section NontrivialAmbient

variable [Nontrivial Q]

/-- The corrected nontrivial ambient hypothesis turns the source length
bound into a genuinely inhabited labelled index type. -/
theorem one_le_index_card_of_pair_length
    (hlen : Nat.card Q - 1 ≤ Nat.card ι) :
    1 ≤ Nat.card ι := by
  have hQ : 1 < Nat.card Q := Finite.one_lt_card
  omega

end NontrivialAmbient

/-! ## Honest labelled subset sums -/

/-- All subset sums supported on the literal labelled index finset `s`.
Repeated values at different indices remain different choices in
`s.powerset`. -/
noncomputable def pairIndexSubsetSums
    (v : ι → Q) (s : Finset ι) : Finset Q := by
  classical
  exact s.powerset.image fun t ↦ ∑ i ∈ t, v i

@[simp]
theorem mem_pairIndexSubsetSums_iff
    (v : ι → Q) (s : Finset ι) (x : Q) :
    x ∈ pairIndexSubsetSums v s ↔
      ∃ t : Finset ι, t ⊆ s ∧ (∑ i ∈ t, v i) = x := by
  classical
  constructor
  · intro hx
    obtain ⟨t, ht, hsum⟩ := Finset.mem_image.mp hx
    exact ⟨t, Finset.mem_powerset.mp ht, hsum⟩
  · rintro ⟨t, ht, rfl⟩
    exact Finset.mem_image.mpr
      ⟨t, Finset.mem_powerset.mpr ht, rfl⟩

@[simp]
theorem zero_mem_pairIndexSubsetSums
    (v : ι → Q) (s : Finset ι) :
    0 ∈ pairIndexSubsetSums v s := by
  exact (mem_pairIndexSubsetSums_iff v s 0).2
    ⟨∅, Finset.empty_subset _, by simp⟩

/-- Enlarging the literal carrier can only enlarge its labelled subset-sum
spectrum. -/
theorem pairIndexSubsetSums_mono
    (v : ι → Q) {s t : Finset ι} (hst : s ⊆ t) :
    pairIndexSubsetSums v s ⊆ pairIndexSubsetSums v t := by
  intro x hx
  obtain ⟨a, ha, hsum⟩ :=
    (mem_pairIndexSubsetSums_iff v s x).1 hx
  exact (mem_pairIndexSubsetSums_iff v t x).2
    ⟨a, ha.trans hst, hsum⟩

/-- If every labelled value in `s` lies in `J`, then every subset sum
lies in `J`. -/
theorem pairIndexSubsetSums_subset_subgroupFinset
    (v : ι → Q) (J : AddSubgroup Q) (s : Finset ι)
    (hs : ∀ i ∈ s, v i ∈ J) :
    pairIndexSubsetSums v s ⊆ subgroupFinset J := by
  intro x hx
  obtain ⟨t, ht, hsum⟩ :=
    (mem_pairIndexSubsetSums_iff v s x).1 hx
  apply (mem_subgroupFinset J x).2
  rw [← hsum]
  exact AddSubgroup.sum_mem J fun i hi ↦ hs i (ht hi)

/-- Coverage plus subgroup containment upgrades to the exact subgroup
sumset equality used in the source lemma. -/
theorem pairIndexSubsetSums_eq_subgroupFinset
    (v : ι → Q) (J : AddSubgroup Q) (s : Finset ι)
    (hs : ∀ i ∈ s, v i ∈ J)
    (hcover : ∀ x : Q, x ∈ J → x ∈ pairIndexSubsetSums v s) :
    pairIndexSubsetSums v s = subgroupFinset J := by
  apply Finset.Subset.antisymm
  · exact pairIndexSubsetSums_subset_subgroupFinset v J s hs
  · intro x hx
    exact hcover x ((mem_subgroupFinset J x).1 hx)

/-! ## Canonical retained and omitted labelled indices -/

/-- All, rather than merely some, labelled indices whose value belongs to
`J`. -/
noncomputable def pairIndicesInSubgroup
    (v : ι → Q) (J : AddSubgroup Q) : Finset ι := by
  classical
  exact Finset.univ.filter fun i ↦ v i ∈ J

/-- The literal complement of `pairIndicesInSubgroup` in the source index
type. -/
noncomputable def pairIndicesOutsideSubgroup
    (v : ι → Q) (J : AddSubgroup Q) : Finset ι := by
  classical
  exact (Finset.univ : Finset ι) \ pairIndicesInSubgroup v J

@[simp]
theorem mem_pairIndicesInSubgroup_iff
    (v : ι → Q) (J : AddSubgroup Q) (i : ι) :
    i ∈ pairIndicesInSubgroup v J ↔ v i ∈ J := by
  classical
  simp [pairIndicesInSubgroup]

@[simp]
theorem mem_pairIndicesOutsideSubgroup_iff
    (v : ι → Q) (J : AddSubgroup Q) (i : ι) :
    i ∈ pairIndicesOutsideSubgroup v J ↔ v i ∉ J := by
  classical
  simp [pairIndicesOutsideSubgroup]

theorem pairIndicesInSubgroup_disjoint_outside
    (v : ι → Q) (J : AddSubgroup Q) :
    Disjoint (pairIndicesInSubgroup v J)
      (pairIndicesOutsideSubgroup v J) := by
  classical
  exact Finset.disjoint_sdiff

theorem pairIndicesInSubgroup_union_outside
    (v : ι → Q) (J : AddSubgroup Q) :
    pairIndicesInSubgroup v J ∪ pairIndicesOutsideSubgroup v J =
      (Finset.univ : Finset ι) := by
  classical
  exact Finset.union_sdiff_of_subset (Finset.subset_univ _)

theorem card_pairIndicesInSubgroup_add_outside
    (v : ι → Q) (J : AddSubgroup Q) :
    (pairIndicesInSubgroup v J).card +
        (pairIndicesOutsideSubgroup v J).card =
      Nat.card ι := by
  classical
  have hcard := Finset.card_union_of_disjoint
    (pairIndicesInSubgroup_disjoint_outside v J)
  rw [pairIndicesInSubgroup_union_outside v J] at hcard
  simpa [Nat.card_eq_fintype_card] using hcard.symm

/-- The literal subtype of retained labels used as the recursive index type
inside `J`. -/
def PairRetainedIndex (v : ι → Q) (J : AddSubgroup Q) :=
  {i : ι // v i ∈ J}

noncomputable instance (v : ι → Q) (J : AddSubgroup Q) :
    Fintype (PairRetainedIndex v J) := by
  unfold PairRetainedIndex
  infer_instance

/-- The retained labelled value, now typed in the recursive ambient
subgroup. -/
def pairRetainedValue
    (v : ι → Q) (J : AddSubgroup Q) : PairRetainedIndex v J → J :=
  fun i ↦ ⟨v i.1, i.2⟩

theorem pairRetainedValue_ne_zero
    (v : ι → Q) (J : AddSubgroup Q)
    (hv : ∀ i, v i ≠ 0) (i : PairRetainedIndex v J) :
    pairRetainedValue v J i ≠ 0 := by
  intro hi
  exact hv i.1 (congrArg Subtype.val hi)

/-- Passing to the recursive subtype preserves the exact number of labelled
retained indices. -/
theorem natCard_pairRetainedIndex
    (v : ι → Q) (J : AddSubgroup Q) :
    Nat.card (PairRetainedIndex v J) =
      (pairIndicesInSubgroup v J).card := by
  classical
  simpa [PairRetainedIndex, pairIndicesInSubgroup,
    Nat.card_eq_fintype_card] using
      (Fintype.card_subtype fun i : ι ↦ v i ∈ J)

/-! ## Pair layers and their exact quotient incidence -/

/-- The honest two-choice layer contributed by one labelled nonzero value. -/
noncomputable def pairIndexLayer (v : ι → Q) (i : ι) : Finset Q := by
  classical
  exact {0, v i}

@[simp]
theorem card_pairIndexLayer_of_ne_zero
    (v : ι → Q) (i : ι) (hi : v i ≠ 0) :
    (pairIndexLayer v i).card = 2 := by
  classical
  simp [pairIndexLayer, hi, Ne.symm hi]

/-- The pair setpartition on a literal labelled carrier.  The arbitrary
`Finset.toList` order affects no additive sumset, while retaining every
source index exactly once. -/
noncomputable def pairIndexSetpartitionOn
    (v : ι → Q) (s : Finset ι) : List (Finset Q) := by
  classical
  exact s.toList.map fun i ↦ pairIndexLayer v i

/-- The full pair setpartition on every labelled source index. -/
noncomputable def pairIndexSetpartition
    (v : ι → Q) : List (Finset Q) :=
  pairIndexSetpartitionOn v Finset.univ

@[simp]
theorem length_pairIndexSetpartitionOn
    (v : ι → Q) (s : Finset ι) :
    (pairIndexSetpartitionOn v s).length = s.card := by
  classical
  simp [pairIndexSetpartitionOn]

@[simp]
theorem length_pairIndexSetpartition (v : ι → Q) :
    (pairIndexSetpartition v).length = Nat.card ι := by
  classical
  simp [pairIndexSetpartition, Nat.card_eq_fintype_card]

theorem pairIndexSetpartitionOn_nonempty
    (v : ι → Q) (s : Finset ι) :
    IsNonemptySetPartition (pairIndexSetpartitionOn v s) := by
  classical
  intro B hB
  obtain ⟨i, -, rfl⟩ := List.mem_map.mp hB
  simp [pairIndexLayer]

theorem pairIndexSetpartition_nonempty (v : ι → Q) :
    IsNonemptySetPartition (pairIndexSetpartition v) := by
  exact pairIndexSetpartitionOn_nonempty v Finset.univ

theorem pairIndexSetpartitionOn_card_two
    (v : ι → Q) (s : Finset ι)
    (hv : ∀ i ∈ s, v i ≠ 0) :
    ∀ B ∈ pairIndexSetpartitionOn v s, B.card = 2 := by
  classical
  intro B hB
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hB
  exact card_pairIndexLayer_of_ne_zero v i
    (hv i (Finset.mem_toList.mp hi))

/-- The proved full-layer DGM theorem applies directly to every labelled
pair carrier; no general-DGM provider is accepted as input. -/
theorem pairIndexSetpartitionOn_dgmBound
    (v : ι → Q) (s : Finset ι) :
    DGMSetpartitionBound (pairIndexSetpartitionOn v s) s.card := by
  classical
  have h := dgmSetpartitionBound_full
    (pairIndexSetpartitionOn v s)
    (pairIndexSetpartitionOn_nonempty v s)
  simpa using h

theorem pairIndexSetpartition_dgmBound (v : ι → Q) :
    DGMSetpartitionBound (pairIndexSetpartition v) (Nat.card ι) := by
  have h := pairIndexSetpartitionOn_dgmBound
    v (Finset.univ : Finset ι)
  simpa [pairIndexSetpartition, Nat.card_eq_fintype_card] using h

/-- Full sumset of all honest pair layers. -/
noncomputable def pairIndexFullSumset (v : ι → Q) : Finset Q :=
  fullLayerSumSpectrum (pairIndexSetpartition v)

/-- The canonical stabilizer used in the proper branch of the strong
induction. -/
noncomputable def pairIndexStabilizer (v : ι → Q) : AddSubgroup Q :=
  AddAction.stabilizer Q (pairIndexFullSumset v : Set Q)

theorem pairIndexFullSumset_nonempty (v : ι → Q) :
    (pairIndexFullSumset v).Nonempty := by
  unfold pairIndexFullSumset
  exact layerSubsumSpectrum_nonempty
    (pairIndexSetpartition v)
    (pairIndexSetpartition_nonempty v)
    (pairIndexSetpartition v).length le_rfl

/-- The quotient image of one labelled pair layer. -/
noncomputable def pairIndexQuotientLayer
    (v : ι → Q) (J : AddSubgroup Q) (i : ι) :
    Finset (Q ⧸ J) :=
  quotientLayer J (pairIndexLayer v i)

theorem pairIndexQuotientLayer_eq
    (v : ι → Q) (J : AddSubgroup Q) (i : ι) :
    pairIndexQuotientLayer v J i =
      ({0, (v i : Q ⧸ J)} : Finset (Q ⧸ J)) := by
  classical
  ext q
  simp [pairIndexQuotientLayer, pairIndexLayer, quotientLayer]

/-- A pair contributes one quotient class precisely when its nonzero entry
lies in `J`, and otherwise contributes two. -/
theorem card_pairIndexQuotientLayer
    (v : ι → Q) (J : AddSubgroup Q) (i : ι) :
    (pairIndexQuotientLayer v J i).card =
      if v i ∈ J then 1 else 2 := by
  classical
  rw [pairIndexQuotientLayer_eq]
  by_cases hi : v i ∈ J
  · have hq : (v i : Q ⧸ J) = 0 :=
      (QuotientAddGroup.eq_zero_iff (v i)).2 hi
    simp [hi, hq]
  · have hq : (v i : Q ⧸ J) ≠ 0 := by
      intro hz
      exact hi ((QuotientAddGroup.eq_zero_iff (v i)).1 hz)
    simp [hi, hq, Ne.symm hq]

/-- Exact incidence ledger: the excess over one quotient class per layer is
the number of literal indices outside `J`. -/
theorem sum_card_pairIndexQuotientLayer
    (v : ι → Q) (J : AddSubgroup Q) :
    (∑ i : ι, (pairIndexQuotientLayer v J i).card) =
      Nat.card ι + (pairIndicesOutsideSubgroup v J).card := by
  classical
  simp only [card_pairIndexQuotientLayer]
  change (∑ i ∈ (Finset.univ : Finset ι),
      if v i ∈ J then 1 else 2) =
    Nat.card ι + (pairIndicesOutsideSubgroup v J).card
  calc
    (∑ i ∈ (Finset.univ : Finset ι), if v i ∈ J then 1 else 2) =
        ∑ i ∈ (Finset.univ : Finset ι),
          (1 + if v i ∈ J then 0 else 1) := by
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hi : v i ∈ J <;> simp [hi]
    _ = (∑ _i ∈ (Finset.univ : Finset ι), 1) +
          ∑ i ∈ (Finset.univ : Finset ι),
            (if v i ∈ J then 0 else 1) := by
      rw [Finset.sum_add_distrib]
    _ = Nat.card ι + (pairIndicesOutsideSubgroup v J).card := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        mul_one, Nat.card_eq_fintype_card]
      congr 1
      rw [Finset.card_eq_sum_ite
        (s := pairIndicesOutsideSubgroup v J)
        (t := (Finset.univ : Finset ι)) (Finset.subset_univ _)]
      apply Finset.sum_congr rfl
      intro i _hi
      simp [pairIndicesOutsideSubgroup]

omit [AddCommGroup Q] [Fintype Q] in
theorem sum_map_finset_toList_nat
    (s : Finset ι) (f : ι → ℕ) :
    (s.toList.map f).sum = ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [hi, ih]

/-- The list incidence seen by DGM is exactly the labelled-index incidence;
the arbitrary `toList` order introduces no multiplicity loss. -/
theorem sum_card_quotientLayer_pairIndexSetpartitionOn
    (v : ι → Q) (J : AddSubgroup Q) (s : Finset ι) :
    ((pairIndexSetpartitionOn v s).map fun B ↦
        (quotientLayer J B).card).sum =
      ∑ i ∈ s, (pairIndexQuotientLayer v J i).card := by
  classical
  unfold pairIndexSetpartitionOn
  simp only [List.map_map]
  exact sum_map_finset_toList_nat s fun i ↦
    (pairIndexQuotientLayer v J i).card

theorem sum_card_quotientLayer_pairIndexSetpartition
    (v : ι → Q) (J : AddSubgroup Q) :
    ((pairIndexSetpartition v).map fun B ↦
        (quotientLayer J B).card).sum =
      Nat.card ι + (pairIndicesOutsideSubgroup v J).card := by
  rw [pairIndexSetpartition,
    sum_card_quotientLayer_pairIndexSetpartitionOn]
  simpa using sum_card_pairIndexQuotientLayer v J

/-! ## Frozen honest certificate -/

/-- The exact occurrence/index-free output needed from the ordinary pair
specialization of Lemma 3.5.

The retained carrier is definitionally audited against *all* indices with
value in `J`; the omitted count therefore cannot hide repeated source
values.  The core consists of exactly `|J|-1` literal indices, and its
labelled subset sums equal the full subgroup finset. -/
structure OrdinaryPairSubgroupCertificate
    (v : ι → Q) where
  J : AddSubgroup Q
  J_ne_bot : J ≠ ⊥
  retained : Finset ι
  retained_eq : retained = pairIndicesInSubgroup v J
  omitted_bound :
    ((Finset.univ : Finset ι) \ retained).card ≤
      Nat.card (Q ⧸ J) - 2
  core : Finset ι
  core_subset_retained : core ⊆ retained
  core_card : core.card = Nat.card J - 1
  core_sumset :
    pairIndexSubsetSums v core = subgroupFinset J

namespace OrdinaryPairSubgroupCertificate

variable {v : ι → Q} (C : OrdinaryPairSubgroupCertificate v)

@[simp]
theorem mem_retained_iff (i : ι) :
    i ∈ C.retained ↔ v i ∈ C.J := by
  rw [C.retained_eq, mem_pairIndicesInSubgroup_iff]

@[simp]
theorem mem_omitted_iff (i : ι) :
    i ∈ (Finset.univ : Finset ι) \ C.retained ↔ v i ∉ C.J := by
  classical
  simp [C.mem_retained_iff]

theorem core_value_mem (i : ι) (hi : i ∈ C.core) :
    v i ∈ C.J :=
  (C.mem_retained_iff i).1 (C.core_subset_retained hi)

theorem core_subset_sum_mem (x : Q) :
    x ∈ pairIndexSubsetSums v C.core ↔ x ∈ C.J := by
  rw [C.core_sumset, mem_subgroupFinset]

theorem exists_core_subset_sum (x : Q) (hx : x ∈ C.J) :
    ∃ t : Finset ι, t ⊆ C.core ∧ (∑ i ∈ t, v i) = x :=
  (mem_pairIndexSubsetSums_iff v C.core x).1
    ((C.core_subset_sum_mem x).2 hx)

theorem card_retained_add_omitted :
    C.retained.card +
        ((Finset.univ : Finset ι) \ C.retained).card =
      Nat.card ι := by
  classical
  rw [C.retained_eq]
  exact card_pairIndicesInSubgroup_add_outside v C.J

theorem source_card_le_retained_add_quotient_sub_two :
    Nat.card ι ≤ C.retained.card + (Nat.card (Q ⧸ C.J) - 2) := by
  have hsplit := C.card_retained_add_omitted
  have homit := C.omitted_bound
  omega

theorem subgroup_isPGroup
    (p : ℕ) (hQ : IsPGroup p (Multiplicative Q)) :
    IsPGroup p (Multiplicative C.J) :=
  isPGroup_multiplicative_addSubgroup p hQ C.J

theorem quotient_isPGroup
    (p : ℕ) (hQ : IsPGroup p (Multiplicative Q)) :
    IsPGroup p (Multiplicative (Q ⧸ C.J)) :=
  isPGroup_multiplicative_quotient p hQ C.J

end OrdinaryPairSubgroupCertificate

/-!
## Remaining existence proof

For a nontrivial finite p-group `Q`, nonzero `v : ι → Q`, and
`Nat.card Q - 1 ≤ Nat.card ι`, the still-to-be-proved constructor proceeds
-/

#print axioms one_le_index_card_of_pair_length
#print axioms pairIndexSubsetSums_eq_subgroupFinset
#print axioms pairIndexSetpartitionOn_dgmBound
#print axioms sum_card_pairIndexQuotientLayer
#print axioms OrdinaryPairSubgroupCertificate.exists_core_subset_sum
#print axioms OrdinaryPairSubgroupCertificate.source_card_le_retained_add_quotient_sub_two
