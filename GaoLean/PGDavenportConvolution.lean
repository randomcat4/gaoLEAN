import GaoLean.PGDavenportBridge
import GaoLean.PGDavenportBound

/-!
# Ordinary Davenport subgroup--quotient convolution

This file reconstructs Lemma 5.2 of the 13-page `gao0824` PR #7 source.
It first supplies the missing occurrence-labelled prefix/suffix mechanics and
the monotonicity of the ordinary Davenport threshold.  The final theorem will
derive the subgroup--quotient inequality from exact Davenport constants,
rather than accepting that inequality as a proposition parameter.
-/

namespace GaoLean

section OrdinaryMonotonicity

variable {A : Type*} [AddCommGroup A]

/-- A zero-sum selection from a prefix remains the same labelled selection in
the full source list. -/
theorem hasNonemptyZeroSum_of_take
    (s : List A) (N : ℕ) (hN : N ≤ s.length)
    (hzero : HasNonemptyZeroSum (s.take N)) :
    HasNonemptyZeroSum s := by
  classical
  rcases hzero with ⟨I, hIne, hIsum⟩
  let emb : Occurrence (s.take N) ↪ Occurrence s :=
    { toFun := fun i =>
        ⟨i.1, lt_of_lt_of_le i.2
          ((List.length_take_le N s).trans hN)⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun x : Occurrence s => x.val) hij }
  let J : Selection s := I.map emb
  have hvalue (i : Occurrence (s.take N)) :
      occurrenceValue s (emb i) = occurrenceValue (s.take N) i := by
    simp [occurrenceValue, emb, List.get_eq_getElem]
  refine ⟨J, ?_, ?_⟩
  · simpa [J] using hIne
  · simpa [J, hvalue] using hIsum

/-- An ordinary Davenport upper bound at length `D` applies to every longer
source sequence by taking its first `D` occurrences. -/
theorem ordinaryDavenportAtLeast_of_atMost
    {D : ℕ} (hD : OrdinaryDavenportAtMost A D) :
    ∀ s : List A, D ≤ s.length → HasNonemptyZeroSum s := by
  intro s hs
  apply hasNonemptyZeroSum_of_take s D hs
  apply hD (s.take D)
  simp [List.length_take, Nat.min_eq_left hs]

/-- Every exact ordinary Davenport value is positive. -/
theorem ordinaryDavenportConstant_pos
    (D : ℕ) (hD : IsOrdinaryDavenportConstant A D) :
    0 < D := by
  by_contra hnot
  have hDzero : D = 0 := Nat.eq_zero_of_not_pos hnot
  have hempty := hD.1 ([] : List A) (by simp [hDzero])
  rcases hempty with ⟨I, hIne, _⟩
  rcases hIne with ⟨i, _⟩
  exact Fin.elim0 i

end OrdinaryMonotonicity

section CanonicalOrdinaryDavenport

variable (A : Type*) [AddCommGroup A] [Finite A]

/-- Every finite additive group has an exact value for the project's
occurrence-labelled ordinary Davenport definition. -/
theorem exists_isOrdinaryDavenportConstant :
    ∃ D : ℕ, IsOrdinaryDavenportConstant A D := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hexUpper : ∃ D : ℕ, OrdinaryDavenportAtMost A D := by
    refine ⟨Nat.card A, ?_⟩
    intro s hlen
    exact hasNonemptyZeroSum_of_length_natCard s hlen
  let D := Nat.find hexUpper
  have hupper : OrdinaryDavenportAtMost A D := Nat.find_spec hexUpper
  refine ⟨D, hupper, ?_⟩
  intro n hn
  have hnot : ¬OrdinaryDavenportAtMost A n :=
    Nat.find_min hexUpper hn
  unfold OrdinaryDavenportAtMost at hnot
  simp only [not_forall] at hnot
  rcases hnot with ⟨s, hslen, hsfree⟩
  exact ⟨s, hslen, hsfree⟩

/-- Canonical exact ordinary Davenport value, chosen as the least threshold
at which every occurrence-labelled source has a nonempty zero sum. -/
noncomputable def ordinaryDavenportValue : ℕ :=
  by
    classical
    exact Nat.find (exists_isOrdinaryDavenportConstant A)

theorem ordinaryDavenportValue_spec :
    IsOrdinaryDavenportConstant A (ordinaryDavenportValue A) := by
  classical
  exact Nat.find_spec (exists_isOrdinaryDavenportConstant A)

end CanonicalOrdinaryDavenport

section SuffixOccurrences

variable {X : Type*}

/-- Embed an occurrence of the right list into an appended source. -/
def appendRightOccurrenceEmbedding (left right : List X) :
    Occurrence right ↪ Occurrence (left ++ right) where
  toFun i := ⟨left.length + i.1, by simp⟩
  inj' := by
    intro i j hij
    apply Fin.ext
    have hval := congrArg (fun x : Occurrence (left ++ right) => x.val) hij
    exact Nat.add_left_cancel hval

@[simp]
theorem occurrenceValue_appendRightOccurrenceEmbedding
    (left right : List X) (i : Occurrence right) :
    occurrenceValue (left ++ right)
        (appendRightOccurrenceEmbedding left right i) =
      occurrenceValue right i := by
  simp [occurrenceValue, appendRightOccurrenceEmbedding,
    List.get_eq_getElem, List.getElem_append_right]

/-- Pull the selected suffix occurrences back to the right source list. -/
noncomputable def suffixSelection (left right : List X)
    (I : Selection (left ++ right)) : Selection right := by
  classical
  exact Finset.univ.filter fun i =>
    appendRightOccurrenceEmbedding left right i ∈ I

theorem map_suffixSelection_eq_sdiff
    (left right : List X) (I : Selection (left ++ right)) :
    (suffixSelection left right I).map
        (appendRightOccurrenceEmbedding left right) =
      I \ prefixOccurrences left right := by
  classical
  ext i
  constructor
  · intro hi
    rcases Finset.mem_map.mp hi with ⟨j, hj, rfl⟩
    have hjI : appendRightOccurrenceEmbedding left right j ∈ I :=
      (Finset.mem_filter.mp hj).2
    refine Finset.mem_sdiff.mpr ⟨hjI, ?_⟩
    simp [prefixOccurrences, appendRightOccurrenceEmbedding]
  · intro hi
    have hiI : i ∈ I := (Finset.mem_sdiff.mp hi).1
    have hge : left.length ≤ i.1 := by
      have hnot := (Finset.mem_sdiff.mp hi).2
      simpa [prefixOccurrences, not_lt] using hnot
    have hlt : i.1 - left.length < right.length := by
      have hibound := i.2
      simp only [List.length_append] at hibound
      omega
    let j : Occurrence right := ⟨i.1 - left.length, hlt⟩
    have hji : appendRightOccurrenceEmbedding left right j = i := by
      apply Fin.ext
      simp [appendRightOccurrenceEmbedding, j]
      omega
    apply Finset.mem_map.mpr
    refine ⟨j, ?_, hji⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, by simpa [hji] using hiI⟩

theorem selectedMultiset_suffixSelection
    (left right : List X) (I : Selection (left ++ right)) :
    selectedMultiset right (suffixSelection left right I) =
      selectedMultiset (left ++ right)
        (I \ prefixOccurrences left right) := by
  classical
  rw [← map_suffixSelection_eq_sdiff left right I]
  simp [selectedMultiset, occurrenceValue_appendRightOccurrenceEmbedding]

theorem selectedMultiset_union_of_disjoint_any
    (s : List X) (I J : Selection s) (hdis : Disjoint I J) :
    selectedMultiset s (I ∪ J) =
      selectedMultiset s I + selectedMultiset s J := by
  have hval : (I ∪ J).1 = I.1 + J.1 := by
    rw [Finset.union_val]
    exact (Multiset.add_eq_union_iff_disjoint.mpr
      ((Finset.disjoint_val).2 hdis)).symm
  simp only [selectedMultiset, hval, Multiset.map_add]

/-- Prefix and suffix selections partition the selected multiset of an
appended source. -/
theorem selectedMultiset_prefix_add_suffix
    (left right : List X) (I : Selection (left ++ right)) :
    selectedMultiset left (prefixSelection left right I) +
        selectedMultiset right (suffixSelection left right I) =
      selectedMultiset (left ++ right) I := by
  classical
  rw [selectedMultiset_prefixSelection,
    selectedMultiset_suffixSelection]
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
  rw [← selectedMultiset_union_of_disjoint_any
    (left ++ right) (I ∩ P) (I \ P) hdis, hunion]

theorem sum_prefixSelection_add_sum_suffixSelection
    [AddCommMonoid X] (left right : List X)
    (I : Selection (left ++ right)) :
    (selectedMultiset left (prefixSelection left right I)).sum +
        (selectedMultiset right (suffixSelection left right I)).sum =
      (selectedMultiset (left ++ right) I).sum := by
  simpa using congrArg Multiset.sum
    (selectedMultiset_prefix_add_suffix left right I)

end SuffixOccurrences

section MapZeroSum

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- Pull a zero-sum occurrence selection through an injective additive map. -/
theorem hasNonemptyZeroSum_of_map_addMonoidHom
    (f : A →+ B) (hf : Function.Injective f) (s : List A)
    (hzero : HasNonemptyZeroSum (s.map f)) :
    HasNonemptyZeroSum s := by
  classical
  rcases hzero with ⟨I, hIne, hIsum⟩
  let J := ConcreteGDihedral.pullbackMapSelection f s I
  have hJne : J.Nonempty := by
    rcases hIne with ⟨i, hi⟩
    refine ⟨(ConcreteGDihedral.mapOccurrenceEquiv f s).symm i, ?_⟩
    exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
  have hpull :=
    ConcreteGDihedral.selectedMultiset_pullbackMapSelection f s I
  have hmapSum : f ((selectedMultiset s J).sum) =
      (selectedMultiset (s.map f) I).sum := by
    calc
      f ((selectedMultiset s J).sum) =
          ((selectedMultiset s J).map f).sum :=
        f.map_multiset_sum _
      _ = (selectedMultiset (s.map f) I).sum :=
        congrArg Multiset.sum hpull
  have hzeroSelected : (selectedMultiset s J).sum = 0 := by
    apply hf
    rw [map_zero, hmapSum]
    simpa [selectedMultiset] using hIsum
  refine ⟨J, hJne, ?_⟩
  simpa [selectedMultiset] using hzeroSelected

end MapZeroSum

section DavenportConvolution

variable {A : Type*} [AddCommGroup A]

/-- A fixed set-theoretic choice of representatives for an additive
quotient.  No homomorphism property is asserted or used. -/
noncomputable def quotientAddSection (K : AddSubgroup A) : A ⧸ K → A :=
  Function.surjInv (QuotientAddGroup.mk'_surjective K)

@[simp]
theorem quotientAddSection_mk (K : AddSubgroup A) (x : A ⧸ K) :
    QuotientAddGroup.mk' K (quotientAddSection K x) = x := by
  exact Function.surjInv_eq (QuotientAddGroup.mk'_surjective K) x

/-- The zero-sum-free word used in the subgroup--quotient lower-bound
construction: a subgroup word followed by arbitrary lifts of a quotient
word. -/
noncomputable def davenportConvolutionWord
    (K : AddSubgroup A) (u : List K) (v : List (A ⧸ K)) : List A :=
  u.map K.subtype ++ v.map (quotientAddSection K)

/-- A zero-sum in the concatenated word would give either a nonempty
zero-sum in the quotient word or, if no lifted quotient term is selected, a
nonempty zero-sum in the subgroup word. -/
theorem davenportConvolutionWord_zeroSumFree
    (K : AddSubgroup A) (u : List K) (v : List (A ⧸ K))
    (hu : ¬HasNonemptyZeroSum u) (hv : ¬HasNonemptyZeroSum v) :
    ¬HasNonemptyZeroSum (davenportConvolutionWord K u v) := by
  classical
  intro hzero
  let left : List A := u.map K.subtype
  let right : List A := v.map (quotientAddSection K)
  change HasNonemptyZeroSum (left ++ right) at hzero
  rcases hzero with ⟨I, hIne, hIsum⟩
  let IL := prefixSelection left right I
  let IR := suffixSelection left right I
  have hwholeSum : (selectedMultiset (left ++ right) I).sum = 0 := by
    simpa [selectedMultiset] using hIsum
  have hsplit :=
    sum_prefixSelection_add_sum_suffixSelection left right I
  have hsumSplit :
      (selectedMultiset left IL).sum +
          (selectedMultiset right IR).sum = 0 := by
    rw [hsplit]
    exact hwholeSum
  let qmap : A →+ A ⧸ K := QuotientAddGroup.mk' K
  have hqleft : qmap ((selectedMultiset left IL).sum) = 0 := by
    have hqvalue (i : Occurrence left) :
        qmap (occurrenceValue left i) = 0 := by
      have hmap :=
        ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm
          K.subtype u i
      rw [← hmap]
      simp [qmap]
    change qmap (∑ i ∈ IL, occurrenceValue left i) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i hi => hqvalue i)
  have hqright : qmap ((selectedMultiset right IR).sum) = 0 := by
    have h := congrArg qmap hsumSplit
    simpa [map_add, hqleft] using h
  by_cases hIRne : IR.Nonempty
  · let Jv :=
      ConcreteGDihedral.pullbackMapSelection (quotientAddSection K) v IR
    have hJvne : Jv.Nonempty := by
      rcases hIRne with ⟨i, hi⟩
      refine ⟨(ConcreteGDihedral.mapOccurrenceEquiv
        (quotientAddSection K) v).symm i, ?_⟩
      exact Finset.mem_map.mpr ⟨i, hi, rfl⟩
    have hpull :=
      ConcreteGDihedral.selectedMultiset_pullbackMapSelection
        (quotientAddSection K) v IR
    have hmaps :
        selectedMultiset v Jv =
          (selectedMultiset right IR).map qmap := by
      have h := congrArg (Multiset.map qmap) hpull
      rw [Multiset.map_map] at h
      have hcomp : qmap ∘ quotientAddSection K = id := by
        funext x
        exact quotientAddSection_mk K x
      rw [hcomp, Multiset.map_id] at h
      simpa [right] using h
    have hsumv : (selectedMultiset v Jv).sum = 0 := by
      calc
        (selectedMultiset v Jv).sum =
            ((selectedMultiset right IR).map qmap).sum :=
          congrArg Multiset.sum hmaps
        _ = qmap ((selectedMultiset right IR).sum) :=
          (qmap.map_multiset_sum _).symm
        _ = 0 := hqright
    apply hv
    refine ⟨Jv, hJvne, ?_⟩
    simpa [selectedMultiset] using hsumv
  · have hIRempty : IR = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIRne
    have hILne : IL.Nonempty := by
      by_contra hILnot
      have hILempty : IL = ∅ :=
        Finset.not_nonempty_iff_eq_empty.mp hILnot
      have hILempty' : prefixSelection left right I = ∅ := by
        simpa [IL] using hILempty
      have hIRempty' : suffixSelection left right I = ∅ := by
        simpa [IR] using hIRempty
      have hselectedEmpty : selectedMultiset (left ++ right) I = 0 := by
        rw [← selectedMultiset_prefix_add_suffix left right I,
          hILempty', hIRempty']
        simp [selectedMultiset]
      have hIcard : I.card = 0 := by
        rw [← card_selectedMultiset (left ++ right) I, hselectedEmpty]
        simp
      exact hIne.ne_empty (Finset.card_eq_zero.mp hIcard)
    have hsumLeft : (selectedMultiset left IL).sum = 0 := by
      rw [hIRempty] at hsumSplit
      simpa [selectedMultiset] using hsumSplit
    have hzeroLeft : HasNonemptyZeroSum left := by
      refine ⟨IL, hILne, ?_⟩
      simpa [selectedMultiset] using hsumLeft
    apply hu
    exact hasNonemptyZeroSum_of_map_addMonoidHom
      K.subtype K.subtype_injective u hzeroLeft

/-- Lemma 5.2 of the 13-page manuscript: exact ordinary Davenport constants
satisfy the subgroup--quotient concatenation inequality. -/
theorem ordinaryDavenport_subgroup_quotient
    (K : AddSubgroup A) (DA DK DQ : ℕ)
    (hA : IsOrdinaryDavenportConstant A DA)
    (hK : IsOrdinaryDavenportConstant K DK)
    (hQ : IsOrdinaryDavenportConstant (A ⧸ K) DQ) :
    DK + DQ ≤ DA + 1 := by
  have hDKpos := ordinaryDavenportConstant_pos DK hK
  have hDQpos := ordinaryDavenportConstant_pos DQ hQ
  have hDKpred : DK - 1 < DK := by omega
  have hDQpred : DQ - 1 < DQ := by omega
  rcases hK.2 (DK - 1) hDKpred with ⟨u, hulen, hufree⟩
  rcases hQ.2 (DQ - 1) hDQpred with ⟨v, hvlen, hvfree⟩
  have hwordfree :=
    davenportConvolutionWord_zeroSumFree K u v hufree hvfree
  by_contra hnot
  apply hwordfree
  apply ordinaryDavenportAtLeast_of_atMost hA.1
  simp [davenportConvolutionWord, hulen, hvlen]
  omega

end DavenportConvolution

end GaoLean

#print axioms GaoLean.hasNonemptyZeroSum_of_take
#print axioms GaoLean.ordinaryDavenportAtLeast_of_atMost
#print axioms GaoLean.ordinaryDavenportConstant_pos
#print axioms GaoLean.exists_isOrdinaryDavenportConstant
#print axioms GaoLean.ordinaryDavenportValue_spec
#print axioms GaoLean.map_suffixSelection_eq_sdiff
#print axioms GaoLean.selectedMultiset_suffixSelection
#print axioms GaoLean.selectedMultiset_prefix_add_suffix
#print axioms GaoLean.sum_prefixSelection_add_sum_suffixSelection
#print axioms GaoLean.hasNonemptyZeroSum_of_map_addMonoidHom
#print axioms GaoLean.quotientAddSection_mk
#print axioms GaoLean.davenportConvolutionWord_zeroSumFree
#print axioms GaoLean.ordinaryDavenport_subgroup_quotient
