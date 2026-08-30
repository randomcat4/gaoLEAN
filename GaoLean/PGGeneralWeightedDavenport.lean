import GaoLean.PGGeneralWeightedDefinitions
import GaoLean.PGDavenportConvolution

/-!
# General weighted Davenport mechanics

This file develops the occurrence-sensitive elementary facts about the
integer-weighted Davenport constant which do not require the full weighted
GMO argument.  The weight set is always an arbitrary `Set ℤ`.
-/

namespace GaoLean

open scoped BigOperators

section Take

variable {A : Type*} [AddCommGroup A]

/-- An exact weighted selection from a prefix embeds into the original
source, with the same weights and weighted sum. -/
def hasWeightedSumOfCard_of_take
    (W : Set ℤ) (s : List A) (N n : ℕ) (y : A)
    (hN : N ≤ s.length)
    (h : HasWeightedSumOfCard W (s.take N) n y) :
    HasWeightedSumOfCard W s n y := by
  classical
  let emb : Occurrence (s.take N) ↪ Occurrence s :=
    { toFun := fun i =>
        ⟨i.1, lt_of_lt_of_le i.2
          ((List.length_take_le N s).trans hN)⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun x : Occurrence s => x.val) hij }
  let J : Selection s := h.selected.map emb
  let weights : Occurrence s → ℤ := fun j =>
    if hj : j.1 < (s.take N).length then h.weights ⟨j.1, hj⟩ else 0
  have hvalue (i : Occurrence (s.take N)) :
      occurrenceValue s (emb i) = occurrenceValue (s.take N) i := by
    simp [occurrenceValue, emb, List.get_eq_getElem]
  have hweights (i : Occurrence (s.take N)) :
      weights (emb i) = h.weights i := by
    have hiN : i.1 < N := lt_of_lt_of_le i.2 (List.length_take_le N s)
    simp [weights, emb, hiN]
  refine {
    selected := J
    weights := weights
    weights_mem := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · intro j hj
    rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
    simpa [hweights] using h.weights_mem i hi
  · simpa [J] using h.card_selected
  · simpa [J, hweights, hvalue] using h.weighted_sum

/-- A weighted zero-sum selection from a prefix remains a weighted zero-sum
selection of the full source. -/
theorem hasNonemptyWeightedZeroSum_of_take
    (W : Set ℤ) (s : List A) (N : ℕ) (hN : N ≤ s.length)
    (hzero : HasNonemptyWeightedZeroSum W (s.take N)) :
    HasNonemptyWeightedZeroSum W s := by
  rcases hzero with ⟨n, hn, ⟨h⟩⟩
  exact ⟨n, hn, ⟨hasWeightedSumOfCard_of_take W s N n 0 hN h⟩⟩

/-- A weighted Davenport upper bound at length `D` applies to every longer
source by taking its first `D` labelled occurrences. -/
theorem weightedDavenportAtLeast_of_atMost
    (W : Set ℤ) {D : ℕ} (hD : WeightedDavenportAtMost W A D) :
    ∀ s : List A, D ≤ s.length → HasNonemptyWeightedZeroSum W s := by
  intro s hs
  apply hasNonemptyWeightedZeroSum_of_take W s D hs
  apply hD (s.take D)
  simp [List.length_take, Nat.min_eq_left hs]

/-- Every exact weighted Davenport value is positive. -/
theorem weightedDavenportConstant_pos
    (W : Set ℤ) (D : ℕ) (hD : IsWeightedDavenportConstant W A D) :
    0 < D := by
  by_contra hnot
  have hDzero : D = 0 := Nat.eq_zero_of_not_pos hnot
  rcases hD.1 ([] : List A) (by simp [hDzero]) with
    ⟨n, hn, ⟨h⟩⟩
  have hle : n ≤ 0 := by simpa using h.card_le_length
  omega

end Take

section LabelledPool

variable {X B : Type*} [Fintype X] [DecidableEq X]
variable [AddCommGroup B]

/-- Apply a weighted Davenport bound to a finite labelled pool.  The
returned zero-sum block is a literal subset of the input labels, with an
explicit allowed weight on every selected label.  Equal values of `f` do
not identify their source labels. -/
theorem exists_nonempty_weightedZeroSum_finset_subset
    (W : Set ℤ) (R : Finset X) (f : X → B) (D : ℕ)
    (hD : WeightedDavenportAtMost W B D) (hcard : D ≤ R.card) :
    ∃ J : Finset X, J.Nonempty ∧ J ⊆ R ∧
      ∃ weights : X → ℤ,
        (∀ x ∈ J, weights x ∈ W) ∧
        (∑ x ∈ J, weights x • f x) = 0 := by
  classical
  let word : List B := R.toList.map f
  have hwordLength : D ≤ word.length := by
    simpa [word] using hcard
  obtain ⟨n, hn, ⟨z⟩⟩ :=
    weightedDavenportAtLeast_of_atMost W hD word hwordLength
  let source : Occurrence word ↪ X :=
    { toFun := fun i => R.toList.get
        ⟨i.1, by simpa [word] using i.2⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun q : Fin R.toList.length => q.val)
          (R.nodup_toList.injective_get hij) }
  let J : Finset X := z.selected.map source
  let weights : X → ℤ := fun x =>
    if hx : ∃ i, source i = x then z.weights (Classical.choose hx) else 0
  have hsourceMem (i : Occurrence word) : source i ∈ R := by
    exact Finset.mem_toList.mp (List.get_mem R.toList _)
  have hvalue (i : Occurrence word) :
      f (source i) = occurrenceValue word i := by
    simp [source, word, occurrenceValue, List.get_eq_getElem]
  have hweights (i : Occurrence word) :
      weights (source i) = z.weights i := by
    have hi : ∃ j, source j = source i := ⟨i, rfl⟩
    simp only [weights, dif_pos hi]
    congr 1
    exact source.injective (Classical.choose_spec hi)
  have hzNonempty : z.selected.Nonempty := by
    rw [← Finset.card_pos, z.card_selected]
    exact hn
  refine ⟨J, ?_, ?_, weights, ?_, ?_⟩
  · obtain ⟨i, hi⟩ := hzNonempty
    exact ⟨source i, Finset.mem_map.mpr ⟨i, hi, rfl⟩⟩
  · intro x hx
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_map.mp hx
    exact hsourceMem i
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hx
    rw [hweights]
    exact z.weights_mem i hi
  · simpa [J, Finset.sum_map, hweights, hvalue] using z.weighted_sum

/-- A maximum-cardinality weighted zero-sum block leaves fewer than `D`
labels.  The weights are attached to the literal source labels, so this
statement can be used before any quotient values with equal images are
identified. -/
theorem exists_weightedZeroSum_subset_remainder_lt_davenport
    (W : Set ℤ) (R : Finset X) (f : X → B) (D : ℕ)
    (hD : WeightedDavenportAtMost W B D) :
    ∃ I : Finset X,
      I ⊆ R ∧
      (∃ weights : X → ℤ,
        (∀ x ∈ I, weights x ∈ W) ∧
        (∑ x ∈ I, weights x • f x) = 0) ∧
      R.card - I.card < D := by
  classical
  let good : Finset (Finset X) := Finset.univ.filter fun I =>
    I ⊆ R ∧
      ∃ weights : X → ℤ,
        (∀ x ∈ I, weights x ∈ W) ∧
        (∑ x ∈ I, weights x • f x) = 0
  have hempty : (∅ : Finset X) ∈ good := by
    simp [good]
  obtain ⟨I, hIgood, hImax⟩ := Finset.exists_max_image good
    (fun J => J.card) ⟨∅, hempty⟩
  obtain ⟨hIsub, weightsI, hIweights, hIsum⟩ :=
    (Finset.mem_filter.mp hIgood).2
  refine ⟨I, hIsub, ⟨weightsI, hIweights, hIsum⟩, ?_⟩
  by_contra hnot
  have hrem : D ≤ (R \ I).card := by
    rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hIsub]
    omega
  obtain ⟨J, hJne, hJsub, weightsJ, hJweights, hJsum⟩ :=
    exists_nonempty_weightedZeroSum_finset_subset W (R \ I) f D hD hrem
  have hJsubR : J ⊆ R := fun x hx => (Finset.mem_sdiff.mp (hJsub hx)).1
  have hdis : Disjoint I J := by
    rw [Finset.disjoint_left]
    intro x hxI hxJ
    exact (Finset.mem_sdiff.mp (hJsub hxJ)).2 hxI
  let weightsUnion : X → ℤ := fun x =>
    if x ∈ I then weightsI x else weightsJ x
  have hUnionWeights : ∀ x ∈ I ∪ J, weightsUnion x ∈ W := by
    intro x hx
    by_cases hxI : x ∈ I
    · simpa [weightsUnion, hxI] using hIweights x hxI
    · have hxJ : x ∈ J := (Finset.mem_union.mp hx).resolve_left hxI
      simpa [weightsUnion, hxI] using hJweights x hxJ
  have hUnionSum : (∑ x ∈ I ∪ J, weightsUnion x • f x) = 0 := by
    rw [Finset.sum_union hdis]
    have hleft : (∑ x ∈ I, weightsUnion x • f x) = 0 := by
      calc
        (∑ x ∈ I, weightsUnion x • f x) =
            ∑ x ∈ I, weightsI x • f x := by
              apply Finset.sum_congr rfl
              intro x hx
              simp [weightsUnion, hx]
        _ = 0 := hIsum
    have hright : (∑ x ∈ J, weightsUnion x • f x) = 0 := by
      calc
        (∑ x ∈ J, weightsUnion x • f x) =
            ∑ x ∈ J, weightsJ x • f x := by
              apply Finset.sum_congr rfl
              intro x hx
              have hxI : x ∉ I := by
                intro hxI
                exact (Finset.disjoint_left.mp hdis) hxI hx
              simp [weightsUnion, hxI]
        _ = 0 := hJsum
    rw [hleft, hright, zero_add]
  have hUnionGood : I ∪ J ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨Finset.union_subset hIsub hJsubR,
      ⟨weightsUnion, hUnionWeights, hUnionSum⟩⟩
  have hmax := hImax _ hUnionGood
  rw [Finset.card_union_of_disjoint hdis] at hmax
  have hJpos : 0 < J.card := Finset.card_pos.mpr hJne
  omega

/-- Pad the omitted part of a maximal weighted zero-sum block by the same
number of genuine zero-valued reserve labels.  The returned selection has
exactly the cardinality of `pool`, lies in `pool ∪ reserve`, and carries an
explicit allowed weight on every selected label. -/
theorem exists_weightedZeroSum_padded_selection
    (W : Set ℤ) (pool reserve : Finset X) (f : X → B) (D : ℕ)
    (hD : IsWeightedDavenportConstant W B D)
    (hdis : Disjoint pool reserve)
    (hreserveZero : ∀ x ∈ reserve, f x = 0)
    (hreserveCard : D - 1 ≤ reserve.card) :
    ∃ tail : Finset X,
      tail ⊆ pool ∪ reserve ∧ tail.card = pool.card ∧
      ∃ weights : X → ℤ,
        (∀ x ∈ tail, weights x ∈ W) ∧
        (∑ x ∈ tail, weights x • f x) = 0 := by
  classical
  have hDpos : 0 < D := weightedDavenportConstant_pos W D hD
  have hWnonempty : W.Nonempty := by
    obtain ⟨n, hn, ⟨z⟩⟩ :=
      hD.1 (List.replicate D (0 : B)) (by simp)
    have hzNonempty : z.selected.Nonempty := by
      rw [← Finset.card_pos, z.card_selected]
      exact hn
    obtain ⟨i, hi⟩ := hzNonempty
    exact ⟨z.weights i, z.weights_mem i hi⟩
  obtain ⟨I, hIsub, ⟨weightsI, hIweights, hIsum⟩, hrem⟩ :=
    exists_weightedZeroSum_subset_remainder_lt_davenport W pool f D hD.1
  let k := pool.card - I.card
  have hk : k ≤ reserve.card := by
    dsimp only [k]
    omega
  obtain ⟨F, hFsub, hFcard⟩ :=
    Finset.exists_subset_card_eq (s := reserve) hk
  have hIF : Disjoint I F := hdis.mono hIsub hFsub
  obtain ⟨w₀, hw₀⟩ := hWnonempty
  let weights : X → ℤ := fun x =>
    if x ∈ I then weightsI x else w₀
  refine ⟨I ∪ F, ?_, ?_, weights, ?_, ?_⟩
  · exact Finset.union_subset
      (hIsub.trans Finset.subset_union_left)
      (hFsub.trans Finset.subset_union_right)
  · rw [Finset.card_union_of_disjoint hIF, hFcard]
    dsimp only [k]
    exact Nat.add_sub_of_le (Finset.card_le_card hIsub)
  · intro x hx
    by_cases hxI : x ∈ I
    · simpa [weights, hxI] using hIweights x hxI
    · simpa [weights, hxI] using hw₀
  · rw [Finset.sum_union hIF]
    have hleft : (∑ x ∈ I, weights x • f x) = 0 := by
      calc
        (∑ x ∈ I, weights x • f x) =
            ∑ x ∈ I, weightsI x • f x := by
              apply Finset.sum_congr rfl
              intro x hx
              simp [weights, hx]
        _ = 0 := hIsum
    have hright : (∑ x ∈ F, weights x • f x) = 0 := by
      apply Finset.sum_eq_zero
      intro x hx
      have hxI : x ∉ I := by
        intro hxI
        exact (Finset.disjoint_left.mp hIF) hxI hx
      simp [weights, hxI, hreserveZero x (hFsub hx)]
    rw [hleft, hright, zero_add]

end LabelledPool

section Map

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Push an exact integer-weighted sum through an additive homomorphism. -/
def hasWeightedSumOfCard_map_addMonoidHom
    (W : Set ℤ) (f : A →+ B) (s : List A) (n : ℕ) (y : A)
    (h : HasWeightedSumOfCard W s n y) :
    HasWeightedSumOfCard W (s.map f) n (f y) := by
  classical
  let e := ConcreteGDihedral.mapOccurrenceEquiv f s
  let J : Selection (s.map f) := h.selected.map e.toEmbedding
  let weights : Occurrence (s.map f) → ℤ :=
    fun j => h.weights (e.symm j)
  have hvalue (i : Occurrence s) :
      occurrenceValue (s.map f) (e i) = f (occurrenceValue s i) :=
    ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f s i
  refine {
    selected := J
    weights := weights
    weights_mem := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · intro j hj
    rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
    simpa [weights, e] using h.weights_mem i hi
  · simpa [J] using h.card_selected
  · rw [← h.weighted_sum]
    simp [J, weights, e, hvalue]

/-- Weighted zero sums push forward through every additive homomorphism. -/
theorem hasNonemptyWeightedZeroSum_map_addMonoidHom
    (W : Set ℤ) (f : A →+ B) (s : List A)
    (hzero : HasNonemptyWeightedZeroSum W s) :
    HasNonemptyWeightedZeroSum W (s.map f) := by
  rcases hzero with ⟨n, hn, ⟨h⟩⟩
  refine ⟨n, hn, ⟨?_⟩⟩
  simpa using hasWeightedSumOfCard_map_addMonoidHom W f s n 0 h

/-- Pull an exact weighted sum back through an injective additive
homomorphism.  Injectivity is needed only to recover the source sum from its
image. -/
noncomputable def hasWeightedSumOfCard_of_map_addMonoidHom
    (W : Set ℤ) (f : A →+ B) (hf : Function.Injective f)
    (s : List A) (n : ℕ) (y : A)
    (h : HasWeightedSumOfCard W (s.map f) n (f y)) :
    HasWeightedSumOfCard W s n y := by
  classical
  let e := ConcreteGDihedral.mapOccurrenceEquiv f s
  let J : Selection s := h.selected.map e.symm.toEmbedding
  let weights : Occurrence s → ℤ := fun i => h.weights (e i)
  have hvalue (i : Occurrence s) :
      occurrenceValue (s.map f) (e i) = f (occurrenceValue s i) :=
    ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f s i
  have hvalueSymm (j : Occurrence (s.map f)) :
      f (occurrenceValue s (e.symm j)) = occurrenceValue (s.map f) j :=
    ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm f s j
  refine {
    selected := J
    weights := weights
    weights_mem := ?_
    card_selected := ?_
    weighted_sum := ?_
  }
  · intro i hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    simpa [weights, e] using h.weights_mem j hj
  · simpa [J] using h.card_selected
  · apply hf
    simpa [J, weights, e, hvalue, hvalueSymm] using h.weighted_sum

/-- Consequently, weighted zero sums pull back through injective additive
homomorphisms. -/
theorem hasNonemptyWeightedZeroSum_of_map_addMonoidHom
    (W : Set ℤ) (f : A →+ B) (hf : Function.Injective f) (s : List A)
    (hzero : HasNonemptyWeightedZeroSum W (s.map f)) :
    HasNonemptyWeightedZeroSum W s := by
  rcases hzero with ⟨n, hn, ⟨h⟩⟩
  refine ⟨n, hn, ⟨?_⟩⟩
  have h' : HasWeightedSumOfCard W (s.map f) n (f 0) := by
    simpa using h
  exact hasWeightedSumOfCard_of_map_addMonoidHom W f hf s n 0 h'

/-- A Davenport upper bound descends along any surjective additive
homomorphism. -/
theorem weightedDavenportAtMost_of_surjective
    (W : Set ℤ) (f : A →+ B) (hf : Function.Surjective f) (D : ℕ)
    (hA : WeightedDavenportAtMost W A D) :
    WeightedDavenportAtMost W B D := by
  classical
  intro ys hlen
  let sec : B → A := Function.surjInv hf
  let xs : List A := ys.map sec
  have hxs : xs.length = D := by simpa [xs] using hlen
  have hzero := hA xs hxs
  have hmapped := hasNonemptyWeightedZeroSum_map_addMonoidHom W f xs hzero
  have hsection : f ∘ sec = id := by
    funext y
    exact Function.surjInv_eq hf y
  simpa [xs, List.map_map, hsection] using hmapped

/-- Exact weighted Davenport constants are invariant under additive
equivalence.  The upper threshold is transported by surjectivity, while each
shorter zero-sum-free witness is mapped forward and pulled back by
injectivity if a weighted zero sum were to appear. -/
theorem isWeightedDavenportConstant_addEquiv
    (W : Set ℤ) (e : A ≃+ B) {D : ℕ}
    (hA : IsWeightedDavenportConstant W A D) :
    IsWeightedDavenportConstant W B D := by
  refine ⟨weightedDavenportAtMost_of_surjective W e.toAddMonoidHom
    e.surjective D hA.1, ?_⟩
  intro n hn
  rcases hA.2 n hn with ⟨xs, hxsCard, hxsFree⟩
  refine ⟨xs.map e, by simpa using hxsCard, ?_⟩
  intro hzero
  exact hxsFree
    (hasNonemptyWeightedZeroSum_of_map_addMonoidHom W e.toAddMonoidHom
      e.injective xs hzero)

/-- In particular, a weighted Davenport upper bound descends to every
additive quotient. -/
theorem weightedDavenportAtMost_quotient
    {A : Type*} [AddCommGroup A] (W : Set ℤ) (K : AddSubgroup A) (D : ℕ)
    (hA : WeightedDavenportAtMost W A D) :
    WeightedDavenportAtMost W (A ⧸ K) D :=
  weightedDavenportAtMost_of_surjective W (QuotientAddGroup.mk' K)
    (QuotientAddGroup.mk'_surjective K) D hA

/-- A weighted Davenport upper bound restricts to every additive subgroup.
The source list is mapped through the injective subtype homomorphism; any
ambient zero sum then pulls back to the original labelled subgroup list. -/
theorem weightedDavenportAtMost_subgroup
    {A : Type*} [AddCommGroup A] (W : Set ℤ) (K : AddSubgroup A) (D : ℕ)
    (hA : WeightedDavenportAtMost W A D) :
    WeightedDavenportAtMost W K D := by
  intro xs hlen
  apply hasNonemptyWeightedZeroSum_of_map_addMonoidHom
    W K.subtype K.subtype_injective xs
  exact hA (xs.map K.subtype) (by simpa using hlen)

end Map

section AppendSplit

variable {A : Type*} [AddCommGroup A]

/-- Split an integer-weighted sum on an appended source into the canonical
prefix and suffix selections. -/
theorem sum_weighted_prefixSelection_add_sum_weighted_suffixSelection
    (left right : List A) (I : Selection (left ++ right))
    (weights : Occurrence (left ++ right) → ℤ) :
    let IL := prefixSelection left right I
    let IR := suffixSelection left right I
    let weightsL : Occurrence left → ℤ := fun i ↦
      weights (appendLeftOccurrenceEmbedding left right i)
    let weightsR : Occurrence right → ℤ := fun i ↦
      weights (appendRightOccurrenceEmbedding left right i)
    (∑ i ∈ IL, weightsL i • occurrenceValue left i) +
        (∑ i ∈ IR, weightsR i • occurrenceValue right i) =
      ∑ i ∈ I, weights i • occurrenceValue (left ++ right) i := by
  classical
  dsimp only
  have hleft :
      (∑ i ∈ prefixSelection left right I,
          weights (appendLeftOccurrenceEmbedding left right i) •
            occurrenceValue left i) =
        ∑ i ∈ I ∩ prefixOccurrences left right,
          weights i • occurrenceValue (left ++ right) i := by
    rw [← map_prefixSelection_eq_inter left right I]
    simp [Finset.sum_map, occurrenceValue_appendLeftOccurrenceEmbedding]
  have hright :
      (∑ i ∈ suffixSelection left right I,
          weights (appendRightOccurrenceEmbedding left right i) •
            occurrenceValue right i) =
        ∑ i ∈ I \ prefixOccurrences left right,
          weights i • occurrenceValue (left ++ right) i := by
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

end AppendSplit

section OrdinaryComparison

variable {A : Type*} [AddCommGroup A]

/-- An ordinary zero sum becomes a `W`-weighted zero sum by assigning one
fixed member of the nonempty weight set to every selected occurrence. -/
theorem hasNonemptyWeightedZeroSum_of_hasNonemptyZeroSum
    {W : Set ℤ} (hW : W.Nonempty) (s : List A)
    (hzero : HasNonemptyZeroSum s) :
    HasNonemptyWeightedZeroSum W s := by
  classical
  obtain ⟨w, hw⟩ := hW
  rcases hzero with ⟨I, hIne, hIsum⟩
  refine ⟨I.card, Finset.card_pos.mpr hIne, ⟨{
    selected := I
    weights := fun _ => w
    weights_mem := by intro i hi; exact hw
    card_selected := rfl
    weighted_sum := ?_
  }⟩⟩
  rw [← Finset.smul_sum]
  simp [hIsum]

/-- Every ordinary Davenport upper bound is also a weighted upper bound for
a nonempty set of weights. -/
theorem weightedDavenportAtMost_of_ordinary
    {W : Set ℤ} (hW : W.Nonempty) (D : ℕ)
    (hD : OrdinaryDavenportAtMost A D) :
    WeightedDavenportAtMost W A D := by
  intro s hs
  exact hasNonemptyWeightedZeroSum_of_hasNonemptyZeroSum hW s (hD s hs)

/-- For a nonempty weight set, the exact weighted Davenport constant is at
most the exact ordinary Davenport constant. -/
theorem weightedDavenportConstant_le_ordinary
    {W : Set ℤ} (hW : W.Nonempty) (DW D : ℕ)
    (hDW : IsWeightedDavenportConstant W A DW)
    (hD : IsOrdinaryDavenportConstant A D) :
    DW ≤ D := by
  by_contra hnot
  have hlt : D < DW := Nat.lt_of_not_ge hnot
  rcases hDW.2 D hlt with ⟨s, hslen, hsfree⟩
  exact hsfree
    (hasNonemptyWeightedZeroSum_of_hasNonemptyZeroSum hW s (hD.1 s hslen))

end OrdinaryComparison

section WeightedConvolution

variable {A : Type*} [AddCommGroup A]

/-- The ordinary subgroup--quotient concatenation word remains
`W`-weighted-zero-sum-free when both component words are.  This argument
uses no closure property of `W`: after projecting to the quotient, a
nonempty selected suffix would itself be a forbidden `W`-weighted zero sum.
-/
theorem davenportConvolutionWord_weightedZeroSumFree
    (W : Set ℤ) (K : AddSubgroup A)
    (u : List K) (v : List (A ⧸ K))
    (hu : ¬HasNonemptyWeightedZeroSum W u)
    (hv : ¬HasNonemptyWeightedZeroSum W v) :
    ¬HasNonemptyWeightedZeroSum W
      (davenportConvolutionWord K u v) := by
  classical
  intro hzero
  let left : List A := u.map K.subtype
  let right : List A := v.map (quotientAddSection K)
  change HasNonemptyWeightedZeroSum W (left ++ right) at hzero
  rcases hzero with ⟨n, hn, ⟨h⟩⟩
  let IL := prefixSelection left right h.selected
  let IR := suffixSelection left right h.selected
  let weightsL : Occurrence left → ℤ := fun i ↦
    h.weights (appendLeftOccurrenceEmbedding left right i)
  let weightsR : Occurrence right → ℤ := fun i ↦
    h.weights (appendRightOccurrenceEmbedding left right i)
  have hsplit :=
    sum_weighted_prefixSelection_add_sum_weighted_suffixSelection
      left right h.selected h.weights
  have hsumSplit :
      (∑ i ∈ IL, weightsL i • occurrenceValue left i) +
          (∑ i ∈ IR, weightsR i • occurrenceValue right i) = 0 := by
    simpa [IL, IR, weightsL, weightsR, h.weighted_sum] using hsplit
  let qmap : A →+ A ⧸ K := QuotientAddGroup.mk' K
  have hqleft :
      qmap (∑ i ∈ IL, weightsL i • occurrenceValue left i) = 0 := by
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    rw [map_zsmul]
    have hmap :=
      ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm
        K.subtype u i
    rw [← hmap]
    have hzeroK :
        qmap (K.subtype
          (occurrenceValue u
            ((ConcreteGDihedral.mapOccurrenceEquiv K.subtype u).symm i))) = 0 := by
      exact (QuotientAddGroup.eq_zero_iff
        (K.subtype (occurrenceValue u
          ((ConcreteGDihedral.mapOccurrenceEquiv K.subtype u).symm i)))).2
            (occurrenceValue u
              ((ConcreteGDihedral.mapOccurrenceEquiv K.subtype u).symm i)).property
    rw [hzeroK]
    simp
  have hqright :
      qmap (∑ i ∈ IR, weightsR i • occurrenceValue right i) = 0 := by
    have hproj := congrArg qmap hsumSplit
    simpa [map_add, hqleft] using hproj
  by_cases hIRne : IR.Nonempty
  · let e := ConcreteGDihedral.mapOccurrenceEquiv (quotientAddSection K) v
    let Jv : Selection v := IR.map e.symm.toEmbedding
    let weightsV : Occurrence v → ℤ := fun j ↦ weightsR (e j)
    have hJvne : Jv.Nonempty := by
      rcases hIRne with ⟨i, hi⟩
      refine ⟨e.symm i, ?_⟩
      exact Finset.mem_map.mpr ⟨i, hi, by simp⟩
    have hweightsVmem : ∀ j ∈ Jv, weightsV j ∈ W := by
      intro j hj
      rcases Finset.mem_map.mp hj with ⟨i, hi, rfl⟩
      have hiI : appendRightOccurrenceEmbedding left right i ∈ h.selected :=
        (Finset.mem_filter.mp hi).2
      simpa [weightsV, weightsR, e] using h.weights_mem _ hiI
    have hsumV :
        (∑ j ∈ Jv, weightsV j • occurrenceValue v j) = 0 := by
      calc
        (∑ j ∈ Jv, weightsV j • occurrenceValue v j) =
            ∑ i ∈ IR, weightsR i •
              occurrenceValue v (e.symm i) := by
                simp [Jv, weightsV]
                rfl
        _ = ∑ i ∈ IR, weightsR i •
              qmap (occurrenceValue right i) := by
                apply Finset.sum_congr rfl
                intro i hi
                have hpull :=
                  ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm
                    (quotientAddSection K) v i
                have hpullq := congrArg qmap hpull
                have heq : occurrenceValue v (e.symm i) =
                    qmap (occurrenceValue right i) := by
                  have hsec :
                      qmap (quotientAddSection K
                        (occurrenceValue v (e.symm i))) =
                        occurrenceValue v (e.symm i) := by
                    exact quotientAddSection_mk K _
                  exact hsec.symm.trans (by simpa [e, right] using hpullq)
                rw [heq]
        _ = qmap (∑ i ∈ IR,
              weightsR i • occurrenceValue right i) := by
                simp
        _ = 0 := hqright
    apply hv
    exact ⟨Jv.card, Finset.card_pos.mpr hJvne, ⟨{
      selected := Jv
      weights := weightsV
      weights_mem := hweightsVmem
      card_selected := rfl
      weighted_sum := hsumV
    }⟩⟩
  · have hIRempty : IR = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIRne
    have hselectedNe : h.selected.Nonempty := by
      apply Finset.card_pos.mp
      rw [h.card_selected]
      exact hn
    have hILne : IL.Nonempty := by
      by_contra hILnot
      have hILempty : IL = ∅ := Finset.not_nonempty_iff_eq_empty.mp hILnot
      have hleftEmpty : h.selected ∩ prefixOccurrences left right = ∅ := by
        rw [← map_prefixSelection_eq_inter left right h.selected,
          show prefixSelection left right h.selected = ∅ by simpa [IL] using hILempty]
        simp
      have hrightEmpty : h.selected \ prefixOccurrences left right = ∅ := by
        rw [← map_suffixSelection_eq_sdiff left right h.selected,
          show suffixSelection left right h.selected = ∅ by simpa [IR] using hIRempty]
        simp
      apply hselectedNe.ne_empty
      ext i
      have hcover :
          i ∈ h.selected ↔
            i ∈ h.selected ∩ prefixOccurrences left right ∨
            i ∈ h.selected \ prefixOccurrences left right := by
        simp
        tauto
      simp [hcover, hleftEmpty, hrightEmpty]
    have hsumLeft :
        (∑ i ∈ IL, weightsL i • occurrenceValue left i) = 0 := by
      rw [hIRempty] at hsumSplit
      simpa using hsumSplit
    have hweightsLmem : ∀ i ∈ IL, weightsL i ∈ W := by
      intro i hi
      have hiI : appendLeftOccurrenceEmbedding left right i ∈ h.selected :=
        (Finset.mem_filter.mp hi).2
      exact h.weights_mem _ hiI
    have hzeroLeft : HasNonemptyWeightedZeroSum W left :=
      ⟨IL.card, Finset.card_pos.mpr hILne, ⟨{
        selected := IL
        weights := weightsL
        weights_mem := hweightsLmem
        card_selected := rfl
        weighted_sum := hsumLeft
      }⟩⟩
    apply hu
    exact hasNonemptyWeightedZeroSum_of_map_addMonoidHom
      W K.subtype K.subtype_injective u (by simpa [left] using hzeroLeft)

/-- Exact weighted Davenport constants satisfy the same zero-free
subgroup--quotient concatenation inequality as in the ordinary case. -/
theorem weightedDavenport_subgroup_quotient
    (W : Set ℤ) (K : AddSubgroup A) (DA DK DQ : ℕ)
    (hA : IsWeightedDavenportConstant W A DA)
    (hK : IsWeightedDavenportConstant W K DK)
    (hQ : IsWeightedDavenportConstant W (A ⧸ K) DQ) :
    DK + DQ ≤ DA + 1 := by
  have hDKpos := weightedDavenportConstant_pos W DK hK
  have hDQpos := weightedDavenportConstant_pos W DQ hQ
  have hDKpred : DK - 1 < DK := by omega
  have hDQpred : DQ - 1 < DQ := by omega
  rcases hK.2 (DK - 1) hDKpred with ⟨u, hulen, hufree⟩
  rcases hQ.2 (DQ - 1) hDQpred with ⟨v, hvlen, hvfree⟩
  have hwordfree :=
    davenportConvolutionWord_weightedZeroSumFree W K u v hufree hvfree
  by_contra hnot
  apply hwordfree
  apply weightedDavenportAtLeast_of_atMost W hA.1
  simp [davenportConvolutionWord, hulen, hvlen]
  omega

end WeightedConvolution

end GaoLean

#print axioms GaoLean.hasWeightedSumOfCard_of_take
#print axioms GaoLean.hasNonemptyWeightedZeroSum_of_take
#print axioms GaoLean.weightedDavenportAtLeast_of_atMost
#print axioms GaoLean.weightedDavenportConstant_pos
#print axioms GaoLean.exists_nonempty_weightedZeroSum_finset_subset
#print axioms GaoLean.exists_weightedZeroSum_subset_remainder_lt_davenport
#print axioms GaoLean.exists_weightedZeroSum_padded_selection
#print axioms GaoLean.hasWeightedSumOfCard_map_addMonoidHom
#print axioms GaoLean.hasNonemptyWeightedZeroSum_map_addMonoidHom
#print axioms GaoLean.hasWeightedSumOfCard_of_map_addMonoidHom
#print axioms GaoLean.hasNonemptyWeightedZeroSum_of_map_addMonoidHom
#print axioms GaoLean.weightedDavenportAtMost_subgroup
#print axioms GaoLean.weightedDavenportAtMost_of_surjective
#print axioms GaoLean.isWeightedDavenportConstant_addEquiv
#print axioms GaoLean.weightedDavenportAtMost_quotient
#print axioms GaoLean.sum_weighted_prefixSelection_add_sum_weighted_suffixSelection
#print axioms GaoLean.hasNonemptyWeightedZeroSum_of_hasNonemptyZeroSum
#print axioms GaoLean.weightedDavenportAtMost_of_ordinary
#print axioms GaoLean.weightedDavenportConstant_le_ordinary
#print axioms GaoLean.davenportConvolutionWord_weightedZeroSumFree
#print axioms GaoLean.weightedDavenport_subgroup_quotient
