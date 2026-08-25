import GaoLean.PGDavenportBridge

/-!
# Sequence-level capacity-entry counterexample

This module formalizes the labelled cyclic family from
`gao0824/research/sequence-entry-2026-08-24`.  It first supplies reusable
occurrence lemmas: a selected multiset is a submultiset of its source, and a
product-one selection from rotations followed by one reflection pulls back to
an additive zero-sum selection of the same cardinality.
-/

namespace GaoLean

open scoped BigOperators

theorem selectedMultiset_le_source {α : Type*} (s : List α) (I : Selection s) :
    selectedMultiset s I ≤ (Multiset.ofList s) := by
  classical
  unfold selectedMultiset
  calc
    I.1.map (occurrenceValue s) ≤
        (Finset.univ : Finset (Occurrence s)).1.map (occurrenceValue s) := by
      apply Multiset.map_le_map
      rw [Finset.val_le_iff_val_subset]
      intro i hi
      simp
    _ = Multiset.ofList s := by
      rw [Fin.univ_val_map]
      have hof : List.ofFn (occurrenceValue s) = s := by
        change List.ofFn s.get = s
        exact List.ofFn_get s
      rw [hof]

theorem selectedMultiset_filter_univ {α : Type*} (s : List α) (p : α → Prop)
    [DecidablePred p] :
    selectedMultiset s (Finset.univ.filter fun i => p (occurrenceValue s i)) =
      (Multiset.ofList s).filter p := by
  classical
  unfold selectedMultiset
  have hof : List.ofFn (occurrenceValue s) = s := by
    change List.ofFn s.get = s
    exact List.ofFn_get s
  rw [Finset.filter_val]
  calc
    Multiset.map (occurrenceValue s)
        (Multiset.filter (fun i => p (occurrenceValue s i)) Finset.univ.1) =
        Multiset.filter p
          (Multiset.map (occurrenceValue s) Finset.univ.1) := by
      rw [Multiset.filter_map]
      rfl
    _ = Multiset.filter p (Multiset.ofList s) := by
      rw [Fin.univ_val_map, hof]

theorem card_occurrences_satisfying {α : Type*} (s : List α) (p : α → Prop)
    [DecidablePred p] :
    (Finset.univ.filter fun i => p (occurrenceValue s i)).card =
      (Multiset.ofList s).countP p := by
  rw [Multiset.countP_eq_card_filter]
  rw [← selectedMultiset_filter_univ s p]
  exact (card_selectedMultiset s _).symm

private theorem list_countP_replicate {α : Type*} (p : α → Prop)
    [DecidablePred p] (a : α) (k : ℕ) :
    List.countP p (List.replicate k a) = if p a then k else 0 := by
  rw [List.countP_eq_length_filter]
  by_cases h : p a
  · simp [h]
  · simp [h]

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Pull a product-one selection through a rotation prefix and a single final
reflection.  Cardinality and the additive coordinate sum are both preserved. -/
theorem exists_zeroSumSelection_of_productOneSelection_singleReflection
    (w : List A) (I : Selection (davenportLiftWord w))
    (hprod : IsProductOneSelection (davenportLiftWord w) I) :
    ∃ J : Selection w,
      J.card = I.card ∧ (selectedMultiset w J).sum = 0 := by
  classical
  change Selection
    (w.map (data A).rot ++ [(data A).refl 0]) at I
  change IsProductOneSelection
    (w.map (data A).rot ++ [(data A).refl 0]) I at hprod
  let rotations := w.map (data A).rot
  let reflection : Group A := (data A).refl 0
  have hall :=
    allRotation_of_productOneSelection_of_reflection_card_le_one
      (rotations ++ [reflection]) I
      (by simpa [rotations, reflection, davenportLiftWord] using
        card_reflectionOccurrences_davenportLiftWord_le_one w) hprod
  have hprefix : I ⊆ prefixOccurrences rotations [reflection] := by
    intro i hi
    have hrot := hall i hi
    have hibound' : i.1 < rotations.length + 1 := by
      simpa [rotations] using i.2
    have hlt : i.1 < rotations.length := by
      by_contra hnot
      have hieq : i.1 = rotations.length := by omega
      have hvalue : occurrenceValue (rotations ++ [reflection]) i = reflection := by
        simp [occurrenceValue, List.get_eq_getElem, hieq,
          List.getElem_append_right]
      rw [hvalue] at hrot
      simp [reflection, IsRotation] at hrot
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩
  have hinter : I ∩ prefixOccurrences rotations [reflection] = I :=
    Finset.inter_eq_left.mpr hprefix
  let Jrot := prefixSelection rotations [reflection] I
  have hmapJrot : Jrot.map
        (appendLeftOccurrenceEmbedding rotations [reflection]) = I := by
    have h := map_prefixSelection_eq_inter rotations [reflection] I
    rw [hinter] at h
    simpa [Jrot] using h
  have hJrotCard : Jrot.card = I.card := by
    rw [← hmapJrot, Finset.card_map]
  have hselectedJrot : selectedMultiset rotations Jrot =
      selectedMultiset (rotations ++ [reflection]) I := by
    have h := selectedMultiset_prefixSelection rotations [reflection] I
    rw [hinter] at h
    simpa [Jrot] using h
  rcases hprod with ⟨word, hword, hprodWord⟩
  have hword' : Multiset.ofList word =
      selectedMultiset (rotations ++ [reflection]) I := by
    simpa [rotations, reflection] using hword
  have hallWord : ∀ g ∈ word, IsRotation g := by
    intro g hg
    have hgSelected : g ∈ selectedMultiset (rotations ++ [reflection]) I := by
      rw [← hword']
      simpa using hg
    rw [selectedMultiset] at hgSelected
    rcases Multiset.mem_map.mp hgSelected with ⟨i, hi, rfl⟩
    exact hall i hi
  have hwordSum :=
    sum_coordinate_eq_zero_of_prod_one word hallWord hprodWord
  have hselectedSum :
      ((selectedMultiset (rotations ++ [reflection]) I).map coordinate).sum = 0 := by
    rw [← hword']
    simpa using hwordSum
  have hJrotSum :
      ((selectedMultiset rotations Jrot).map coordinate).sum = 0 := by
    rw [hselectedJrot]
    exact hselectedSum
  let J := pullbackMapSelection (data A).rot w Jrot
  have hpull :
      (selectedMultiset w J).map (data A).rot =
        selectedMultiset rotations Jrot := by
    simpa [J, rotations] using
      selectedMultiset_pullbackMapSelection (data A).rot w Jrot
  have hJCard : J.card = I.card := by
    calc
      J.card = Jrot.card := by simp [J, pullbackMapSelection]
      _ = I.card := hJrotCard
  have hJSum : (selectedMultiset w J).sum = 0 := by
    rw [← hpull] at hJrotSum
    simpa [coordinate, GaoLean.GDihedralData.rot, data, rotation] using
      hJrotSum
  exact ⟨J, hJCard, hJSum⟩

/-- Additive rotation prefix of the cyclic entry counterexample. -/
def cyclicEntryRotationWord (n t : ℕ) : List (ZMod n) :=
  List.replicate (2 * n - 1 - t) 0 ++ List.replicate (n - 1) 1

/-- Full generalized-dihedral counterexample word, with one final reflection. -/
def cyclicEntryWord (n t : ℕ) : List (Group (ZMod n)) :=
  davenportLiftWord (cyclicEntryRotationWord n t)

/-- Canonical regrouping of the word after adjoining `t+1` new identities. -/
def cyclicEntryPaddedRotationWord (n : ℕ) : List (ZMod n) :=
  List.replicate (2 * n) 0 ++ List.replicate (n - 1) 1

def cyclicEntryPaddedWord (n : ℕ) : List (Group (ZMod n)) :=
  davenportLiftWord (cyclicEntryPaddedRotationWord n)

private theorem multiset_sum_eq_count_one_of_zero_or_one {n : ℕ}
    [Nontrivial (ZMod n)]
    (S : Multiset (ZMod n)) (hS : ∀ x ∈ S, x = 0 ∨ x = 1) :
    S.sum = ((S.count 1 : ℕ) : ZMod n) := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons x S ih =>
      have hx := hS x (by simp)
      have htail : ∀ y ∈ S, y = 0 ∨ y = 1 := by
        intro y hy
        exact hS y (by simp [hy])
      rcases hx with rfl | rfl
      · simpa using ih htail
      · simp [ih htail, add_comm]

private theorem multiset_card_eq_counts_of_zero_or_one {n : ℕ}
    [Nontrivial (ZMod n)]
    (S : Multiset (ZMod n)) (hS : ∀ x ∈ S, x = 0 ∨ x = 1) :
    S.card = S.count 0 + S.count 1 := by
  induction S using Multiset.induction_on with
  | empty => simp
  | @cons x S ih =>
      have hx := hS x (by simp)
      have htail : ∀ y ∈ S, y = 0 ∨ y = 1 := by
        intro y hy
        exact hS y (by simp [hy])
      rcases hx with rfl | rfl
      · rw [Multiset.card_cons, ih htail]
        simp
        omega
      · rw [Multiset.card_cons, ih htail]
        simp
        omega

/-- The rotation prefix has no zero-sum occurrence selection of size `2n`.
The proof is fully labelled: it bounds the selected counts by the source
multiset counts and does not collapse repeated zero or generator values. -/
theorem no_zeroSumSelection_cyclicEntryRotationWord
    (n t : ℕ) (hn : 3 ≤ n) (_ht : t ≤ n - 1) :
    ¬ ∃ J : Selection (cyclicEntryRotationWord n t),
      J.card = 2 * n ∧ (selectedMultiset (cyclicEntryRotationWord n t) J).sum = 0 := by
  classical
  haveI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  rintro ⟨J, hJcard, hJsum⟩
  let w := cyclicEntryRotationWord n t
  let S := selectedMultiset w J
  have hsub : S ≤ Multiset.ofList w := selectedMultiset_le_source w J
  have hvalues : ∀ x ∈ S, x = 0 ∨ x = 1 := by
    intro x hx
    have hxsrc : x ∈ Multiset.ofList w := Multiset.mem_of_le hsub hx
    simp [w, cyclicEntryRotationWord] at hxsrc
    exact hxsrc.imp And.right And.right
  have hScard : S.card = 2 * n := by
    simpa [S, w, card_selectedMultiset] using hJcard
  have hcountOne : S.count 1 ≤ n - 1 := by
    have hle := Multiset.count_le_of_le (1 : ZMod n) hsub
    simpa [w, cyclicEntryRotationWord, List.count_replicate,
      zero_ne_one, one_ne_zero] using hle
  have hcountZero : S.count 0 ≤ 2 * n - 1 - t := by
    have hle := Multiset.count_le_of_le (0 : ZMod n) hsub
    simpa [w, cyclicEntryRotationWord, List.count_replicate,
      zero_ne_one, one_ne_zero] using hle
  have hcounts : S.card = S.count 0 + S.count 1 :=
    multiset_card_eq_counts_of_zero_or_one S hvalues
  have hcountOnePos : 0 < S.count 1 := by
    by_contra hnot
    have hz : S.count 1 = 0 := by omega
    omega
  have hcast : ((S.count 1 : ℕ) : ZMod n) = 0 := by
    rw [← multiset_sum_eq_count_one_of_zero_or_one S hvalues]
    exact hJsum
  have hdiv : n ∣ S.count 1 := (ZMod.natCast_eq_zero_iff _ _).1 hcast
  have hnle : n ≤ S.count 1 := Nat.le_of_dvd hcountOnePos hdiv
  omega

/-- The labelled cyclic family avoids every exact `2n` product-one target. -/
theorem cyclicEntryWord_avoids_exactTarget
    (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n - 1) :
    ¬ HasProductOneSubsequenceOfCard (cyclicEntryWord n t) (2 * n) := by
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  rintro ⟨I, hIcard, hprod⟩
  rcases exists_zeroSumSelection_of_productOneSelection_singleReflection
      (cyclicEntryRotationWord n t) I hprod with ⟨J, hJcard, hJsum⟩
  exact no_zeroSumSelection_cyclicEntryRotationWord n t hn ht
    ⟨J, hJcard.trans hIcard, hJsum⟩

theorem cyclicEntryWord_length
    (n t : ℕ) (hn : 1 ≤ n) (ht : t ≤ n - 1) :
    (cyclicEntryWord n t).length = 3 * n - 1 - t := by
  unfold cyclicEntryWord davenportLiftWord cyclicEntryRotationWord
  rw [List.length_append, List.length_map, List.length_singleton,
    List.length_append, List.length_replicate, List.length_replicate]
  omega

theorem one_not_mem_proper_addSubgroup_zmod
    (n : ℕ) [NeZero n] [Fact (1 < n)]
    (K : AddSubgroup (ZMod n)) (hK : K < ⊤) :
    (1 : ZMod n) ∉ K := by
  intro h1
  apply hK.ne
  apply top_unique
  intro x hx
  rw [← x.natCast_zmod_val]
  simpa using K.nsmul_mem h1 x.val

private theorem card_rotationOccurrencesIn_zero_one_singleReflection
    (n z k : ℕ) [NeZero n] [Fact (1 < n)]
    (K : AddSubgroup (ZMod n)) (hK : K < ⊤) :
    (rotationOccurrencesIn
      (davenportLiftWord
        (List.replicate z (0 : ZMod n) ++ List.replicate k 1)) K).card = z := by
  classical
  have h1 : (1 : ZMod n) ∉ K :=
    one_not_mem_proper_addSubgroup_zmod n K hK
  rw [rotationOccurrencesIn]
  have hcard := card_occurrences_satisfying
    (davenportLiftWord
      (List.replicate z (0 : ZMod n) ++ List.replicate k 1))
    (fun g => IsRotation g ∧ coordinate g ∈ K)
  rw [hcard]
  let p : Group (ZMod n) → Prop := fun g => IsRotation g ∧ coordinate g ∈ K
  have hpIdentity : p (1 : Group (ZMod n)) := by
    simp [p, IsRotation, coordinate]
  have hpRot1 :
      ¬p (SemidirectProduct.inl (Multiplicative.ofAdd (1 : ZMod n))) := by
    simpa [p, IsRotation, coordinate] using h1
  have hpReflection :
      ¬p (SemidirectProduct.inr (Multiplicative.ofAdd (1 : ZMod 2))) := by
    simp [p, IsRotation]
  change Multiset.countP p
    (Multiset.ofList (davenportLiftWord
      (List.replicate z (0 : ZMod n) ++ List.replicate k 1))) = z
  simp [davenportLiftWord, hpReflection]
  rw [list_countP_replicate, list_countP_replicate]
  simp [hpIdentity, hpRot1]

/-- Every proper subgroup sees exactly the identity-rotation block of the
cyclic counterexample. -/
theorem card_rotationOccurrencesIn_cyclicEntryWord
    (n t : ℕ) (hn : 3 ≤ n) (_ht : t ≤ n - 1)
    (K : AddSubgroup (ZMod n)) (hK : K < ⊤) :
    (rotationOccurrencesIn (cyclicEntryWord n t) K).card =
      2 * n - 1 - t := by
  classical
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  simpa [cyclicEntryWord, cyclicEntryRotationWord] using
    card_rotationOccurrencesIn_zero_one_singleReflection
      n (2 * n - 1 - t) (n - 1) K hK

theorem card_rotationOccurrencesIn_cyclicEntryPaddedWord
    (n : ℕ) (hn : 3 ≤ n)
    (K : AddSubgroup (ZMod n)) (hK : K < ⊤) :
    (rotationOccurrencesIn (cyclicEntryPaddedWord n) K).card = 2 * n := by
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  simpa [cyclicEntryPaddedWord, cyclicEntryPaddedRotationWord] using
    card_rotationOccurrencesIn_zero_one_singleReflection
      n (2 * n) (n - 1) K hK

/-- The raw `+2` origin-centred subgroup-capacity entry fails for every proper
subgroup of every member of the cyclic family. -/
theorem cyclicEntryWord_no_rawCapacityEntry
    (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n - 1) :
    ∀ K : AddSubgroup (ZMod n), K < ⊤ →
      (rotationOccurrencesIn (cyclicEntryWord n t) K).card <
        (3 * n - 2 - t) - Nat.card (ZMod n ⧸ K) + 2 := by
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  intro K hK
  have hcount := card_rotationOccurrencesIn_cyclicEntryWord n t hn ht K hK
  have hquotientLe : Nat.card (ZMod n ⧸ K) ≤ n := by
    have hle : Nat.card (ZMod n ⧸ K) ≤ Nat.card (ZMod n) :=
      Nat.le_of_dvd Nat.card_pos K.card_quotient_dvd_card
    simpa using hle
  omega

/-- The padded word still misses every proper-subgroup `+2` capacity gate. -/
theorem cyclicEntryPaddedWord_no_capacityEntry
    (n : ℕ) (hn : 3 ≤ n) :
    ∀ K : AddSubgroup (ZMod n), K < ⊤ →
      (rotationOccurrencesIn (cyclicEntryPaddedWord n) K).card <
        (3 * n - 1) - Nat.card (ZMod n ⧸ K) + 2 := by
  letI : NeZero n := ⟨by omega⟩
  letI : Fact (1 < n) := ⟨by omega⟩
  intro K hK
  have hcount := card_rotationOccurrencesIn_cyclicEntryPaddedWord n hn K hK
  have hquotientLe : Nat.card (ZMod n ⧸ K) ≤ n := by
    have hle : Nat.card (ZMod n ⧸ K) ≤ Nat.card (ZMod n) :=
      Nat.le_of_dvd Nat.card_pos K.card_quotient_dvd_card
    simpa using hle
  omega

/-- Complete theorem-level falsification package for the frozen raw entry:
the source has the exact advertised length, avoids the exact target, and
misses every proper-subgroup capacity gate. -/
theorem cyclicEntryWord_disproves_unconditional_rawEntry
    (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n - 1) :
    (cyclicEntryWord n t).length = 3 * n - 1 - t ∧
    ¬ HasProductOneSubsequenceOfCard (cyclicEntryWord n t) (2 * n) ∧
    (∀ K : AddSubgroup (ZMod n), K < ⊤ →
      (rotationOccurrencesIn (cyclicEntryWord n t) K).card <
        (3 * n - 2 - t) - Nat.card (ZMod n ⧸ K) + 2) :=
  ⟨cyclicEntryWord_length n t (by omega) ht,
    cyclicEntryWord_avoids_exactTarget n t hn ht,
    cyclicEntryWord_no_rawCapacityEntry n t hn ht⟩

/-- Both frozen universal entry assertions are false on the same infinite
family: the raw word avoids the target and has no entry, while its canonical
identity padding still has no entry. -/
theorem cyclicEntryWord_disproves_raw_and_padded_entry
    (n t : ℕ) (hn : 3 ≤ n) (ht : t ≤ n - 1) :
    (¬ HasProductOneSubsequenceOfCard (cyclicEntryWord n t) (2 * n)) ∧
    (∀ K : AddSubgroup (ZMod n), K < ⊤ →
      (rotationOccurrencesIn (cyclicEntryWord n t) K).card <
        (3 * n - 2 - t) - Nat.card (ZMod n ⧸ K) + 2) ∧
    (∀ K : AddSubgroup (ZMod n), K < ⊤ →
      (rotationOccurrencesIn (cyclicEntryPaddedWord n) K).card <
        (3 * n - 1) - Nat.card (ZMod n ⧸ K) + 2) :=
  ⟨cyclicEntryWord_avoids_exactTarget n t hn ht,
    cyclicEntryWord_no_rawCapacityEntry n t hn ht,
    cyclicEntryPaddedWord_no_capacityEntry n hn⟩

end ConcreteGDihedral
end GaoLean
