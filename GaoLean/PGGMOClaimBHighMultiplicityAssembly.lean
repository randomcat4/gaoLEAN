import GaoLean.PGGMOClaimBHighMultiplicity
import Mathlib.Data.Fintype.EquivFin

/-!
# Honest labelled assembly ledger for the high-multiplicity extension

This module begins the proper-subgroup enlargement step after the verified
high-multiplicity core.  It performs the exact `d*` arithmetic and selects
the additional zero-class occurrences without replacing labelled source
positions by values.

The payload proved here is deliberately prior to the final partition and
saturation construction.  In particular, it does not assert that the
enlarged Claim-B witness already exists.  The selected singleton range is
literal source data, is disjoint from the old support and from both parts of
the previously selected high/reserve pairs, and has exactly the residual
length forced by subgroup--quotient convolution.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

section LengthLedger

/-- Number of old `K`-cells retained by the enlargement. -/
noncomputable def OrdinaryGMOClaimBOutput.highMultiplicityOldLength
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) : ℕ :=
  pGroupDStar W.K

/-- Number of two-point cells used to span the internal quotient `L/K`. -/
noncomputable def OrdinaryGMOClaimBOutput.highMultiplicityPairLength
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) : ℕ :=
  W.highMultiplicityLength z

/-- Number of cells of the extension subgroup `L`. -/
noncomputable def OrdinaryGMOClaimBOutput.highMultiplicityExtensionLength
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) : ℕ :=
  pGroupDStar (W.highMultiplicityExtensionSubgroup z)

/-- Residual number of genuine zero-class singleton cells. -/
noncomputable def OrdinaryGMOClaimBOutput.highMultiplicitySingletonLength
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) : ℕ :=
  W.highMultiplicityExtensionLength z -
    W.highMultiplicityOldLength - W.highMultiplicityPairLength z

theorem OrdinaryGMOClaimBOutput.old_add_pair_le_extensionLength
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    W.highMultiplicityOldLength + W.highMultiplicityPairLength z ≤
      W.highMultiplicityExtensionLength z := by
  simpa only [OrdinaryGMOClaimBOutput.highMultiplicityOldLength,
    OrdinaryGMOClaimBOutput.highMultiplicityPairLength,
    OrdinaryGMOClaimBOutput.highMultiplicityExtensionLength,
    OrdinaryGMOClaimBOutput.highMultiplicityLength] using
      W.pGroupDStar_K_add_internalQuotient_le_extension z

/-- The three blocks have exactly the extension length.  This is the precise
Nat-subtraction form of subgroup--quotient convolution. -/
theorem OrdinaryGMOClaimBOutput.old_add_pair_add_singleton_eq_extensionLength
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    W.highMultiplicityOldLength + W.highMultiplicityPairLength z +
        W.highMultiplicitySingletonLength z =
      W.highMultiplicityExtensionLength z := by
  have h := W.old_add_pair_le_extensionLength z
  simp only [OrdinaryGMOClaimBOutput.highMultiplicitySingletonLength]
  omega

theorem OrdinaryGMOClaimBOutput.pair_add_singleton_eq_extension_sub_old
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    W.highMultiplicityPairLength z +
        W.highMultiplicitySingletonLength z =
      W.highMultiplicityExtensionLength z -
        W.highMultiplicityOldLength := by
  have h := W.old_add_pair_le_extensionLength z
  have hsum := W.old_add_pair_add_singleton_eq_extensionLength z
  omega

end LengthLedger

section ExtraSingletonSelection

/-- Honest labelled source data needed before assembling the enlarged
partition.  The extra singleton positions are selected from the old
`g+K` reserve after deleting the already reserved zero positions. -/
structure OrdinaryGMOClaimBHighMultiplicityAssemblyData
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) where
  singletonSource :
    Fin (E.W.highMultiplicitySingletonLength z) ↪ Occurrence xs
  singleton_mem : ∀ t,
    singletonSource t ∈ E.W.partition.unusedInAddCoset E.W.K E.W.g
  singleton_not_reserve : ∀ s t,
    singletonSource s ≠ D.reserveSource t

/-- The actual selected range of residual singleton positions. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonSourceRange
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) : Selection xs := by
  classical
  exact Finset.univ.map M.singletonSource

@[simp]
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.card_singletonSourceRange
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.singletonSourceRange.card =
      E.W.highMultiplicitySingletonLength z := by
  classical
  simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonSourceRange]

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonSource_not_mem_support
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) :
    M.singletonSource t ∉ E.W.partition.support :=
  (E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g
    (M.singletonSource t)).1 (M.singleton_mem t) |>.1

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonSource_value_mem_KCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) :
    occurrenceValue xs (M.singletonSource t) ∈
      addCosetFinset E.W.K E.W.g :=
  (E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g
    (M.singletonSource t)).1 (M.singleton_mem t) |>.2

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonSource_value_mem_extensionCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) :
    occurrenceValue xs (M.singletonSource t) ∈
      addCosetFinset (E.W.highMultiplicityExtensionSubgroup z) E.W.g := by
  apply (mem_addCosetFinset_iff
    (E.W.highMultiplicityExtensionSubgroup z) E.W.g _).2
  exact E.W.K_le_highMultiplicityExtensionSubgroup z
    ((mem_addCosetFinset_iff E.W.K E.W.g _).1
      (M.singletonSource_value_mem_KCoset t))

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonRange_disjoint_support
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    Disjoint M.singletonSourceRange E.W.partition.support := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hsupp
  obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hi
  exact M.singletonSource_not_mem_support t hsupp

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonRange_disjoint_reserveRange
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    Disjoint M.singletonSourceRange D.reserveSourceRange := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hs
  obtain ⟨s, -, hsEq⟩ := Finset.mem_map.mp hi
  obtain ⟨t, -, htEq⟩ := Finset.mem_map.mp hs
  exact M.singleton_not_reserve s t (hsEq.trans htEq.symm)

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonRange_disjoint_highRange
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    Disjoint M.singletonSourceRange D.highSourceRange := by
  classical
  rw [Finset.disjoint_left]
  intro i hi hs
  obtain ⟨s, -, rfl⟩ := Finset.mem_map.mp hi
  obtain ⟨t, -, htEq⟩ := Finset.mem_map.mp hs
  have hzero : E.W.centeredQuotientValue (M.singletonSource s) = 0 := by
    exact (QuotientAddGroup.eq_zero_iff _).2
      ((mem_addCosetFinset_iff E.W.K E.W.g _).1
        (M.singletonSource_value_mem_KCoset s))
  have hhigh :
      E.W.centeredQuotientValue (D.highSource t) = z :=
    (E.W.mem_sourceQuotientFiber_iff z (D.highSource t)).1
      (D.high_mem_fiber t)
  rw [htEq] at hhigh
  exact D.nonzero (hhigh.symm.trans hzero)

/-- The remaining ledger contains enough positions to choose the exact
residual singleton block after deleting the already selected reserve range. -/
theorem exists_ordinaryGMOClaimBHighMultiplicityAssemblyData
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (hnL : E.W.highMultiplicityExtensionLength z ≤ n) :
    Nonempty (OrdinaryGMOClaimBHighMultiplicityAssemblyData D) := by
  classical
  let reserve := E.W.partition.unusedInAddCoset E.W.K E.W.g
  let used := D.reserveSourceRange
  let available := reserve \ used
  let rQ := E.W.highMultiplicityPairLength z
  let s := E.W.highMultiplicitySingletonLength z
  have husedSub : used ⊆ reserve := by
    intro i hi
    obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hi
    exact D.reserve_mem t
  have husedCard : used.card = rQ := by
    simp [used, rQ,
      OrdinaryGMOClaimBOutput.highMultiplicityPairLength]
  have hreserve :
      n - E.W.highMultiplicityOldLength + (xs.length - seed.card) ≤
        reserve.card := by
    simpa [reserve,
      OrdinaryGMOClaimBOutput.highMultiplicityOldLength] using
      E.W.remaining_in_coset
  have hrs : rQ + s =
      E.W.highMultiplicityExtensionLength z -
        E.W.highMultiplicityOldLength :=
    E.W.pair_add_singleton_eq_extension_sub_old z
  have hrsLe : rQ + s ≤ n - E.W.highMultiplicityOldLength := by
    omega
  have hinter : used ∩ reserve = used := Finset.inter_eq_left.mpr husedSub
  have hsAvailable : s ≤ available.card := by
    rw [show available.card = reserve.card - used.card by
      simp only [available, Finset.card_sdiff, hinter], husedCard]
    omega
  obtain ⟨singleSet, hsingleSub, hsingleCard⟩ :=
    Finset.exists_subset_card_eq hsAvailable
  let singletonSource : Fin s ↪ Occurrence xs :=
    (singleSet.equivFinOfCardEq hsingleCard).symm.toEmbedding.trans
      (Function.Embedding.subtype _)
  have hsingleMem (t : Fin s) : singletonSource t ∈ reserve := by
    have ht : singletonSource t ∈ available :=
      hsingleSub ((singleSet.equivFinOfCardEq hsingleCard).symm t).property
    exact (Finset.mem_sdiff.mp ht).1
  have hsingleNotReserve (q : Fin s)
      (t : Fin (E.W.highMultiplicityLength z)) :
      singletonSource q ≠ D.reserveSource t := by
    intro heq
    have hqAvail : singletonSource q ∈ available :=
      hsingleSub ((singleSet.equivFinOfCardEq hsingleCard).symm q).property
    have hnotUsed := (Finset.mem_sdiff.mp hqAvail).2
    apply hnotUsed
    apply Finset.mem_map.mpr
    exact ⟨t, Finset.mem_univ _, heq.symm⟩
  refine ⟨{
    singletonSource := singletonSource
    singleton_mem := ?_
    singleton_not_reserve := ?_
  }⟩
  · intro t
    simpa [reserve] using hsingleMem t
  · intro q t
    exact hsingleNotReserve q t

end ExtraSingletonSelection

section HonestPartition

/-- The explicit three-block index type: retained `K`-cells, quotient-spanning
pairs, and residual singleton cells. -/
abbrev OrdinaryGMOClaimBHighMultiplicityAssemblyData.BlockIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (_M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :=
  Fin E.W.highMultiplicityOldLength ⊕
    (Fin (E.W.highMultiplicityPairLength z) ⊕
      Fin (E.W.highMultiplicitySingletonLength z))

/-- Order-preserving identification of the `d*(L)` final cell positions with
the three literal blocks. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.blockIndexEquiv
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    Fin (E.W.highMultiplicityExtensionLength z) ≃ M.BlockIndex := by
  let hlen : E.W.highMultiplicityOldLength +
        (E.W.highMultiplicityPairLength z +
          E.W.highMultiplicitySingletonLength z) =
      E.W.highMultiplicityExtensionLength z := by
    simpa only [Nat.add_assoc] using
      E.W.old_add_pair_add_singleton_eq_extensionLength z
  exact (finCongr hlen.symm).trans
    (finSumFinEquiv.symm.trans
      (Equiv.sumCongr (Equiv.refl _ ) finSumFinEquiv.symm))

/-- A genuine two-occurrence cell, retaining both source labels. -/
noncomputable def OrdinaryGMOClaimBHighMultiplicityCore.pairCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) : Selection xs := by
  classical
  exact {D.highSource t, D.reserveSource t}

/-- A genuine residual singleton cell. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) : Selection xs := by
  classical
  exact {M.singletonSource t}

/-- The ordered raw cell family before transporting the cell count along the
proved equality `dK + (rQ+s) = dL`. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    Fin (E.W.highMultiplicityOldLength +
      (E.W.highMultiplicityPairLength z +
        E.W.highMultiplicitySingletonLength z)) → Selection xs :=
  Fin.append E.W.partition.cells
    (Fin.append D.pairCell M.singletonCell)

theorem OrdinaryGMOClaimBHighMultiplicityCore.highSource_value_ne_reserveSource_value
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    occurrenceValue xs (D.highSource t) ≠
      occurrenceValue xs (D.reserveSource t) := by
  intro hval
  have hhigh : E.W.centeredQuotientValue (D.highSource t) = z :=
    (E.W.mem_sourceQuotientFiber_iff z (D.highSource t)).1
      (D.high_mem_fiber t)
  have hzero := D.reserveSource_centered_eq_zero t
  simp only [OrdinaryGMOClaimBOutput.centeredQuotientValue] at hhigh hzero
  rw [hval] at hhigh
  exact D.nonzero (hhigh.symm.trans hzero)

theorem OrdinaryGMOClaimBHighMultiplicityCore.pairCell_nonempty
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    (D.pairCell t).Nonempty := by
  classical
  exact ⟨D.highSource t, by simp [OrdinaryGMOClaimBHighMultiplicityCore.pairCell]⟩

theorem OrdinaryGMOClaimBHighMultiplicityCore.pairCell_value_injective
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    Set.InjOn (occurrenceValue xs) (D.pairCell t : Set (Occurrence xs)) := by
  classical
  intro i hi j hj hij
  simp only [OrdinaryGMOClaimBHighMultiplicityCore.pairCell,
    Finset.coe_insert, Finset.coe_singleton, Set.mem_insert_iff,
    Set.mem_singleton_iff] at hi hj
  rcases hi with rfl | rfl <;> rcases hj with rfl | rfl
  · rfl
  · exact (D.highSource_value_ne_reserveSource_value t hij).elim
  · exact (D.highSource_value_ne_reserveSource_value t hij.symm).elim
  · rfl

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.oldCell_disjoint_pairCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (j : Fin E.W.highMultiplicityOldLength)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    Disjoint (E.W.partition.cells j) (D.pairCell t) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiOld hiPair
  have hiSupport : i ∈ E.W.partition.support := by
    exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hiOld⟩
  simp only [OrdinaryGMOClaimBHighMultiplicityCore.pairCell,
    Finset.mem_insert, Finset.mem_singleton] at hiPair
  rcases hiPair with rfl | rfl
  · exact D.highSource_not_mem_support D.nonzero t hiSupport
  · exact D.reserveSource_not_mem_support t hiSupport

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.oldCell_disjoint_singletonCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (j : Fin E.W.highMultiplicityOldLength)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) :
    Disjoint (E.W.partition.cells j) (M.singletonCell t) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiOld hiSingle
  have hiSupport : i ∈ E.W.partition.support :=
    Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, hiOld⟩
  have hiEq : i = M.singletonSource t := by
    simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell] using
      hiSingle
  subst i
  exact M.singletonSource_not_mem_support t hiSupport

theorem OrdinaryGMOClaimBHighMultiplicityCore.pairCell_disjoint_of_ne
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    {s t : Fin (E.W.highMultiplicityPairLength z)} (hst : s ≠ t) :
    Disjoint (D.pairCell s) (D.pairCell t) := by
  classical
  rw [Finset.disjoint_left]
  intro i his hit
  simp only [OrdinaryGMOClaimBHighMultiplicityCore.pairCell,
    Finset.mem_insert, Finset.mem_singleton] at his hit
  rcases his with his | his <;> rcases hit with hit | hit
  · exact hst (D.highSource.injective (his.symm.trans hit))
  · exact D.highSource_ne_reserveSource D.nonzero s t (his.symm.trans hit)
  · exact D.highSource_ne_reserveSource D.nonzero t s (hit.symm.trans his)
  · exact hst (D.reserveSource.injective (his.symm.trans hit))

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.pairCell_disjoint_singletonCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicityPairLength z))
    (q : Fin (E.W.highMultiplicitySingletonLength z)) :
    Disjoint (D.pairCell t) (M.singletonCell q) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiPair hiSingle
  have hiSingleEq : i = M.singletonSource q := by
    simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell] using
      hiSingle
  simp only [OrdinaryGMOClaimBHighMultiplicityCore.pairCell,
    Finset.mem_insert, Finset.mem_singleton] at hiPair
  rcases hiPair with hiHigh | hiReserve
  · have hmemHigh : D.highSource t ∈ D.highSourceRange := by
      simp [OrdinaryGMOClaimBHighMultiplicityCore.highSourceRange]
    have hmemSingle : M.singletonSource q ∈ M.singletonSourceRange := by
      simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonSourceRange]
    have heq : M.singletonSource q = D.highSource t :=
      hiSingleEq.symm.trans hiHigh
    have hmemHigh' : M.singletonSource q ∈ D.highSourceRange := by
      rw [heq]
      exact hmemHigh
    exact Finset.disjoint_left.mp M.singletonRange_disjoint_highRange
      hmemSingle hmemHigh'
  · exact M.singleton_not_reserve q t
      (hiSingleEq.symm.trans hiReserve)

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell_disjoint_of_ne
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    {s t : Fin (E.W.highMultiplicitySingletonLength z)} (hst : s ≠ t) :
    Disjoint (M.singletonCell s) (M.singletonCell t) := by
  classical
  rw [Finset.disjoint_left]
  intro i his hit
  have hisEq : i = M.singletonSource s := by
    simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell] using his
  have hitEq : i = M.singletonSource t := by
    simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell] using hit
  exact hst (M.singletonSource.injective (hisEq.symm.trans hitEq))

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells_nonempty
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    ∀ c, (M.rawCells c).Nonempty := by
  intro c
  induction c using Fin.addCases with
  | left j =>
      simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
        E.W.partition.cells_nonempty j
  | right q =>
      induction q using Fin.addCases with
      | left t =>
          simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
            D.pairCell_nonempty t
      | right s =>
          exact ⟨M.singletonSource s, by
            simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells,
              OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell]⟩

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells_pairwise_disjoint
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    {c d} (hcd : c ≠ d) : Disjoint (M.rawCells c) (M.rawCells d) := by
  induction c using Fin.addCases with
  | left j =>
      induction d using Fin.addCases with
      | left k =>
          have hjk : j ≠ k := by intro h; subst k; exact hcd rfl
          simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
            E.W.partition.cells_pairwise_disjoint hjk
      | right q =>
          induction q using Fin.addCases with
          | left t =>
              simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                M.oldCell_disjoint_pairCell j t
          | right s =>
              simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                M.oldCell_disjoint_singletonCell j s
  | right q =>
      induction q using Fin.addCases with
      | left t =>
          induction d using Fin.addCases with
          | left j =>
              simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                (M.oldCell_disjoint_pairCell j t).symm
          | right q' =>
              induction q' using Fin.addCases with
              | left u =>
                  have htu : t ≠ u := by intro h; subst u; exact hcd rfl
                  simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                    D.pairCell_disjoint_of_ne htu
              | right s =>
                  simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                    M.pairCell_disjoint_singletonCell t s
      | right s =>
          induction d using Fin.addCases with
          | left j =>
              simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                (M.oldCell_disjoint_singletonCell j s).symm
          | right q' =>
              induction q' using Fin.addCases with
              | left t =>
                  simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                    (M.pairCell_disjoint_singletonCell t s).symm
              | right u =>
                  have hsu : s ≠ u := by intro h; subst u; exact hcd rfl
                  simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
                    M.singletonCell_disjoint_of_ne hsu

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells_value_injective
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    ∀ c, Set.InjOn (occurrenceValue xs) (M.rawCells c : Set (Occurrence xs)) := by
  intro c
  induction c using Fin.addCases with
  | left j =>
      simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
        E.W.partition.value_injective j
  | right q =>
      induction q using Fin.addCases with
      | left t =>
          simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using
            D.pairCell_value_injective t
      | right s =>
          intro i hi j hj _
          simp only [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells,
            Fin.append_right, OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell,
            Finset.coe_singleton, Set.mem_singleton_iff] at hi hj
          exact hi.trans hj.symm

/-- Literal support of the three raw blocks. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.biUnion_rawCells
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    Finset.univ.biUnion M.rawCells =
      E.W.partition.support ∪
        (D.highSourceRange ∪
          (D.reserveSourceRange ∪ M.singletonSourceRange)) := by
  classical
  ext i
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    Finset.mem_union]
  constructor
  · rintro ⟨c, hic⟩
    induction c using Fin.addCases with
    | left j =>
        exact Or.inl (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, by
          simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using hic⟩)
    | right q =>
        induction q using Fin.addCases with
        | left t =>
            simp only [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells,
              Fin.append_right, Fin.append_left,
              OrdinaryGMOClaimBHighMultiplicityCore.pairCell,
              Finset.mem_insert, Finset.mem_singleton] at hic
            rcases hic with rfl | rfl
            · exact Or.inr (Or.inl (by
                simp [OrdinaryGMOClaimBHighMultiplicityCore.highSourceRange]))
            · exact Or.inr (Or.inr (Or.inl (by
                simp [OrdinaryGMOClaimBHighMultiplicityCore.reserveSourceRange])))
        | right s =>
            have hi : i = M.singletonSource s := by
              simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells,
                OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell] using hic
            subst i
            exact Or.inr (Or.inr (Or.inr (by
              simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonSourceRange])))
  · rintro (hiOld | hiHigh | hiReserve | hiSingle)
    · obtain ⟨j, -, hij⟩ := Finset.mem_biUnion.mp hiOld
      exact ⟨Fin.castAdd _ j, by
        simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells] using hij⟩
    · obtain ⟨t, -, hit⟩ := Finset.mem_map.mp hiHigh
      exact ⟨Fin.natAdd E.W.highMultiplicityOldLength (Fin.castAdd _ t), by
        simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells,
          OrdinaryGMOClaimBHighMultiplicityCore.pairCell, hit.symm]⟩
    · obtain ⟨t, -, hit⟩ := Finset.mem_map.mp hiReserve
      exact ⟨Fin.natAdd E.W.highMultiplicityOldLength (Fin.castAdd _ t), by
        simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells,
          OrdinaryGMOClaimBHighMultiplicityCore.pairCell, hit.symm]⟩
    · obtain ⟨s, -, his⟩ := Finset.mem_map.mp hiSingle
      exact ⟨Fin.natAdd E.W.highMultiplicityOldLength
          (Fin.natAdd (E.W.highMultiplicityPairLength z) s), by
        simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells,
          OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell, his.symm]⟩

/-- Exact support cardinality of the assembled partition. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.assembledSupportCard
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (_M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) : ℕ :=
  E.W.supportCard + 2 * E.W.highMultiplicityPairLength z +
    E.W.highMultiplicitySingletonLength z

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.card_biUnion_rawCells
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    (Finset.univ.biUnion M.rawCells).card = M.assembledSupportCard := by
  classical
  have hRS : Disjoint D.reserveSourceRange M.singletonSourceRange :=
    M.singletonRange_disjoint_reserveRange.symm
  have hHRS : Disjoint D.highSourceRange
      (D.reserveSourceRange ∪ M.singletonSourceRange) :=
    Finset.disjoint_union_right.mpr
      ⟨D.disjoint_sourceRanges D.nonzero,
        M.singletonRange_disjoint_highRange.symm⟩
  have hOldRest : Disjoint E.W.partition.support
      (D.highSourceRange ∪
        (D.reserveSourceRange ∪ M.singletonSourceRange)) :=
    Finset.disjoint_union_right.mpr
      ⟨D.highSourceRange_disjoint_support D.nonzero |>.symm,
        Finset.disjoint_union_right.mpr
          ⟨D.reserveSourceRange_disjoint_support.symm,
            M.singletonRange_disjoint_support.symm⟩⟩
  rw [M.biUnion_rawCells,
    Finset.card_union_of_disjoint hOldRest,
    Finset.card_union_of_disjoint hHRS,
    Finset.card_union_of_disjoint hRS,
    E.W.partition.card_support_eq,
    D.card_highSourceRange, D.card_reserveSourceRange,
    M.card_singletonSourceRange]
  simp only [OrdinaryGMOClaimBOutput.highMultiplicityPairLength,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.assembledSupportCard]
  omega

/-- The honest `d*(L)`-cell partition built from the three labelled blocks. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    Theorem21SetPartition xs (E.W.highMultiplicityExtensionLength z)
      M.assembledSupportCard := by
  classical
  let hlen : E.W.highMultiplicityOldLength +
        (E.W.highMultiplicityPairLength z +
          E.W.highMultiplicitySingletonLength z) =
      E.W.highMultiplicityExtensionLength z := by
    simpa only [Nat.add_assoc] using
      E.W.old_add_pair_add_singleton_eq_extensionLength z
  refine {
    cells := fun c ↦ M.rawCells (Fin.cast hlen.symm c)
    cells_nonempty := fun c ↦ M.rawCells_nonempty (Fin.cast hlen.symm c)
    cells_pairwise_disjoint := ?_
    value_injective := fun c ↦ M.rawCells_value_injective (Fin.cast hlen.symm c)
    card_support := ?_
  }
  · intro c d hcd
    apply M.rawCells_pairwise_disjoint
    intro heq
    apply hcd
    exact Fin.cast_injective hlen.symm heq
  · have hunion :
        Finset.univ.biUnion (fun c ↦ M.rawCells (Fin.cast hlen.symm c)) =
          Finset.univ.biUnion M.rawCells := by
      ext i
      simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨c, hc⟩
        exact ⟨Fin.cast hlen.symm c, hc⟩
      · rintro ⟨c, hc⟩
        exact ⟨Fin.cast hlen c, by simpa using hc⟩
    rw [hunion]
    exact M.card_biUnion_rawCells

/-- Canonical positions of the three blocks in the final `Fin dL` index. -/
noncomputable def OrdinaryGMOClaimBHighMultiplicityAssemblyData.oldIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (j : Fin E.W.highMultiplicityOldLength) :
    Fin (E.W.highMultiplicityExtensionLength z) :=
  M.blockIndexEquiv.symm (Sum.inl j)

noncomputable def OrdinaryGMOClaimBHighMultiplicityAssemblyData.pairIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    Fin (E.W.highMultiplicityExtensionLength z) :=
  M.blockIndexEquiv.symm (Sum.inr (Sum.inl t))

noncomputable def OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) :
    Fin (E.W.highMultiplicityExtensionLength z) :=
  M.blockIndexEquiv.symm (Sum.inr (Sum.inr t))

@[simp]
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.cells_oldIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (j : Fin E.W.highMultiplicityOldLength) :
    M.partition.cells (M.oldIndex j) = E.W.partition.cells j := by
  simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.oldIndex,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.blockIndexEquiv,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells]

@[simp]
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.cells_pairIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    M.partition.cells (M.pairIndex t) = D.pairCell t := by
  simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.pairIndex,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.blockIndexEquiv,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells]

@[simp]
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.cells_singletonIndex
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) :
    M.partition.cells (M.singletonIndex t) = M.singletonCell t := by
  simp [OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonIndex,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.blockIndexEquiv,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells]

/-- Every occurrence retained by the assembled partition has value in the
single affine extension coset `g+L`. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.support_value_mem_extensionCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (i : Occurrence xs) (hi : i ∈ M.partition.support) :
    occurrenceValue xs i ∈
      addCosetFinset (E.W.highMultiplicityExtensionSubgroup z) E.W.g := by
  have hraw : i ∈ Finset.univ.biUnion M.rawCells := by
    have hlen : E.W.highMultiplicityOldLength +
          (E.W.highMultiplicityPairLength z +
            E.W.highMultiplicitySingletonLength z) =
        E.W.highMultiplicityExtensionLength z := by
      simpa only [Nat.add_assoc] using
        E.W.old_add_pair_add_singleton_eq_extensionLength z
    obtain ⟨c, -, hic⟩ := Finset.mem_biUnion.mp hi
    exact Finset.mem_biUnion.mpr
      ⟨Fin.cast hlen.symm c, Finset.mem_univ _, hic⟩
  rw [M.biUnion_rawCells] at hraw
  rcases Finset.mem_union.mp hraw with hOld | hNew
  · apply (mem_addCosetFinset_iff
      (E.W.highMultiplicityExtensionSubgroup z) E.W.g _).2
    exact E.W.K_le_highMultiplicityExtensionSubgroup z
      ((mem_addCosetFinset_iff E.W.K E.W.g _).1
        (E.W.support_in_coset i hOld))
  · rcases Finset.mem_union.mp hNew with hHigh | hRest
    · obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hHigh
      exact D.highSource_value_mem_extensionCoset t
    · rcases Finset.mem_union.mp hRest with hReserve | hSingle
      · obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hReserve
        apply (mem_addCosetFinset_iff
          (E.W.highMultiplicityExtensionSubgroup z) E.W.g _).2
        exact E.W.K_le_highMultiplicityExtensionSubgroup z
          ((mem_addCosetFinset_iff E.W.K E.W.g _).1
            ((E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g _).1
              (D.reserve_mem t) |>.2))
      · obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hSingle
        exact M.singletonSource_value_mem_extensionCoset t

/-- Pointwise finite-set image commutes with the ordered `Fin.append` ledger
after conversion to a list.  The explicit function extensionality avoids
relying on a fragile definitional equality for `Fin.append`. -/
theorem listOfFn_image_finAppend
    {X Y : Type*} [DecidableEq Y] {r s : ℕ}
    (a : Fin r → Finset X) (b : Fin s → Finset X) (f : X → Y) :
    List.ofFn (fun c ↦ (Fin.append a b c).image f) =
      List.ofFn (fun i ↦ (a i).image f) ++
        List.ofFn (fun j ↦ (b j).image f) := by
  have hfun : (fun c ↦ (Fin.append a b c).image f) =
      Fin.append (fun i ↦ (a i).image f) (fun j ↦ (b j).image f) := by
    funext c
    induction c using Fin.addCases <;> simp
  rw [hfun, List.ofFn_fin_append]

/-- Value cell of one genuine high/reserve pair, with its classical finite-set
instance hidden behind a stable noncomputable interface. -/
noncomputable def OrdinaryGMOClaimBHighMultiplicityCore.pairValueCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) : Finset A := by
  classical
  exact (D.pairCell t).image (occurrenceValue xs)

/-- Value cell of one genuine residual singleton. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonValueCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (t : Fin (E.W.highMultiplicitySingletonLength z)) : Finset A := by
  classical
  exact (M.singletonCell t).image (occurrenceValue xs)

/-- Exact ordered value-cell decomposition used by the next saturation
increment. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.valueCells_eq_append_blocks
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.partition.valueCells =
      E.W.partition.valueCells ++
        (List.ofFn fun t : Fin (E.W.highMultiplicityPairLength z) ↦
          D.pairValueCell t) ++
        (List.ofFn fun t : Fin (E.W.highMultiplicitySingletonLength z) ↦
          M.singletonValueCell t) := by
  classical
  let hlen : E.W.highMultiplicityOldLength +
        (E.W.highMultiplicityPairLength z +
          E.W.highMultiplicitySingletonLength z) =
      E.W.highMultiplicityExtensionLength z := by
    simpa only [Nat.add_assoc] using
      E.W.old_add_pair_add_singleton_eq_extensionLength z
  let F := fun c : Fin (E.W.highMultiplicityOldLength +
      (E.W.highMultiplicityPairLength z +
        E.W.highMultiplicitySingletonLength z)) ↦
    (M.rawCells c).image (occurrenceValue xs)
  have hcast := (List.ofFn_congr hlen F).symm
  change List.ofFn (fun c : Fin (E.W.highMultiplicityExtensionLength z) ↦
      (M.rawCells (Fin.cast hlen.symm c)).image (occurrenceValue xs)) = _
  rw [hcast]
  simp only [F, OrdinaryGMOClaimBHighMultiplicityAssemblyData.rawCells]
  rw [listOfFn_image_finAppend, listOfFn_image_finAppend]
  simp only [Theorem21SetPartition.valueCells,
    OrdinaryGMOClaimBHighMultiplicityCore.pairValueCell,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonValueCell,
    List.append_assoc]
  have hold (i : Fin E.W.highMultiplicityOldLength) :
      (E.W.partition.cells i).image (occurrenceValue xs) =
        E.W.partition.valueCell i := by
    unfold Theorem21SetPartition.valueCell
    exact congrArg
      (fun d : DecidableEq A =>
        @Finset.image (Occurrence xs) A d
          (occurrenceValue xs) (E.W.partition.cells i))
      (Subsingleton.elim (inferInstance : DecidableEq A)
        (Classical.decEq A))
  simp_rw [hold]
  rfl

/-- The exact iterated-sum expression of the three ordered blocks, with the
classical finite-set operations hidden in the definition. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.assembledBlockIteratedSum
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) : Finset A := by
  classical
  exact iteratedFinsetSum E.W.partition.valueCells +
    (iteratedFinsetSum
      (List.ofFn fun t : Fin (E.W.highMultiplicityPairLength z) ↦
        D.pairValueCell t) +
      iteratedFinsetSum
      (List.ofFn fun t : Fin (E.W.highMultiplicitySingletonLength z) ↦
        M.singletonValueCell t))

theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.sumset_eq_assembledBlockIteratedSum
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.partition.sumset = M.assembledBlockIteratedSum := by
  classical
  unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.assembledBlockIteratedSum
  rw [Theorem21SetPartition.sumset,
    fullLayerSumSpectrum_eq_iteratedFinsetSum,
    M.valueCells_eq_append_blocks, iteratedFinsetSum_append,
    iteratedFinsetSum_append, add_assoc]

end HonestPartition

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.old_add_pair_add_singleton_eq_extensionLength
#print axioms GaoLean.exists_ordinaryGMOClaimBHighMultiplicityAssemblyData
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonRange_disjoint_highRange
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.support_value_mem_extensionCoset
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.sumset_eq_assembledBlockIteratedSum
