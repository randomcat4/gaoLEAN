import GaoLean.PGGMOClaimBHighMultiplicitySaturation

/-!
# Honest lift of high-multiplicity quotient saturation

This module lifts the verified saturation of the paired block in `L / K`
back to actual values of actual source occurrences.  It then combines the
lifted pair sum with the old `K`-saturated block and the genuine residual
singletons.  The result is the exact saturation equality for the assembled
`d*(L)`-cell partition.

No remaining-occurrence estimate and no enlarged Claim-B witness is asserted
here.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Every occurrence of a genuine pair has value in the extension coset. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.pairCell_value_mem_extensionCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z))
    {i : Occurrence xs} (hi : i ∈ D.pairCell t) :
    occurrenceValue xs i ∈
      addCosetFinset (E.W.highMultiplicityExtensionSubgroup z) E.W.g := by
  classical
  simp only [OrdinaryGMOClaimBHighMultiplicityCore.pairCell,
    Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · exact D.highSource_value_mem_extensionCoset t
  · apply (mem_addCosetFinset_iff
      (E.W.highMultiplicityExtensionSubgroup z) E.W.g _).2
    exact E.W.K_le_highMultiplicityExtensionSubgroup z
      ((mem_addCosetFinset_iff E.W.K E.W.g _).1
        ((E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g _).1
          (D.reserve_mem t) |>.2))

/-- An honest lift of one arbitrary target class of `L / K` through the
whole paired block.  Both the quotient choices and their labelled source
occurrences are retained. -/
structure OrdinaryGMOClaimBHighMultiplicityPairLift
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (q : E.W.HighMultiplicityInternalQuotient z) where
  quotientChoice : Fin (E.W.highMultiplicityPairLength z) →
    E.W.HighMultiplicityInternalQuotient z
  quotientChoice_mem : ∀ t,
    quotientChoice t ∈ D.pairInternalQuotientValueCell t
  source : Fin (E.W.highMultiplicityPairLength z) → Occurrence xs
  source_mem : ∀ t, source t ∈ D.pairCell t
  source_projected : ∀ t,
    E.W.centeredExtensionQuotientValue z
        (occurrenceValue xs (source t)) = quotientChoice t
  source_injective : Function.Injective source
  quotientChoice_sum : (∑ t, quotientChoice t) = q
  centeredSum_mem_extension :
    (∑ t, occurrenceValue xs (source t)) -
        E.W.highMultiplicityPairLength z • E.W.g ∈
      E.W.highMultiplicityExtensionSubgroup z
  projected_centeredSum :
    QuotientAddGroup.mk'
        (internalAddSubgroup E.W.K
          (E.W.highMultiplicityExtensionSubgroup z))
        (⟨(∑ t, occurrenceValue xs (source t)) -
              E.W.highMultiplicityPairLength z • E.W.g,
            centeredSum_mem_extension⟩ :
          E.W.highMultiplicityExtensionSubgroup z) = q

/-- Quotient saturation supplies an honest labelled lift for every target
class.  Membership in each projected cell is unpacked back through the
literal `Finset.image` of that cell. -/
theorem exists_ordinaryGMOClaimBHighMultiplicityPairLift
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (q : E.W.HighMultiplicityInternalQuotient z) :
    Nonempty (OrdinaryGMOClaimBHighMultiplicityPairLift D q) := by
  classical
  letI : Fintype (E.W.HighMultiplicityInternalQuotient z) :=
    Fintype.ofFinite (E.W.HighMultiplicityInternalQuotient z)
  have hqFull : q ∈ E.W.fullHighMultiplicityInternalQuotient z := by
    unfold OrdinaryGMOClaimBOutput.fullHighMultiplicityInternalQuotient
    simp
  have hqIter : q ∈ D.pairInternalQuotientIteratedSum := by
    rw [D.iterated_pairInternalQuotientValueCells_eq_univ]
    exact hqFull
  have hqLayer : q ∈ fullLayerSumSpectrum
      (List.ofFn fun t : Fin (E.W.highMultiplicityPairLength z) ↦
        D.pairInternalQuotientValueCell t) := by
    unfold OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientIteratedSum at hqIter
    unfold OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCells at hqIter
    simpa only [fullLayerSumSpectrum_eq_iteratedFinsetSum] using hqIter
  have hchoice : ∃ a : Fin (E.W.highMultiplicityPairLength z) →
        E.W.HighMultiplicityInternalQuotient z,
      (∀ t, a t ∈ D.pairInternalQuotientValueCell t) ∧
        (∑ t, a t) = q := by
    rw [mem_fullLayerSumSpectrum_iff_exists_choice] at hqLayer
    let f : Fin (E.W.highMultiplicityPairLength z) ≃
        Fin (List.ofFn fun t : Fin (E.W.highMultiplicityPairLength z) ↦
          D.pairInternalQuotientValueCell t).length :=
      finCongr (by simp)
    obtain ⟨a, ha, hsum⟩ := hqLayer
    refine ⟨fun t ↦ a (f t), ?_, ?_⟩
    · intro t
      have ht := ha (f t)
      simp only [List.get_ofFn] at ht
      convert ht using 1
      · congr 1
    · exact (f.sum_comp a).trans hsum
  obtain ⟨a, ha, hsum⟩ := hchoice
  have hpick (t : Fin (E.W.highMultiplicityPairLength z)) :
      ∃ i ∈ D.pairCell t,
        E.W.centeredExtensionQuotientValue z
          (occurrenceValue xs i) = a t := by
    exact Finset.mem_image.mp (ha t)
  let pick : Fin (E.W.highMultiplicityPairLength z) → Occurrence xs :=
    fun t ↦ Classical.choose (hpick t)
  have pick_mem (t : Fin (E.W.highMultiplicityPairLength z)) :
      pick t ∈ D.pairCell t :=
    (Classical.choose_spec (hpick t)).1
  have pick_projected (t : Fin (E.W.highMultiplicityPairLength z)) :
      E.W.centeredExtensionQuotientValue z
          (occurrenceValue xs (pick t)) = a t :=
    (Classical.choose_spec (hpick t)).2
  have pick_injective : Function.Injective pick := by
    intro s t hst
    by_contra hne
    have hd := D.pairCell_disjoint_of_ne hne
    exact (Finset.disjoint_left.mp hd)
      (pick_mem s) (by simpa [hst] using pick_mem t)
  have hcenter (t : Fin (E.W.highMultiplicityPairLength z)) :
      occurrenceValue xs (pick t) - E.W.g ∈
        E.W.highMultiplicityExtensionSubgroup z :=
    (mem_addCosetFinset_iff
      (E.W.highMultiplicityExtensionSubgroup z) E.W.g _).1
      (D.pairCell_value_mem_extensionCoset t (pick_mem t))
  have hcenterSum :
      (∑ t, occurrenceValue xs (pick t)) -
          E.W.highMultiplicityPairLength z • E.W.g ∈
        E.W.highMultiplicityExtensionSubgroup z := by
    have hmem : (∑ t,
        (occurrenceValue xs (pick t) - E.W.g)) ∈
        E.W.highMultiplicityExtensionSubgroup z := by
      exact AddSubgroup.sum_mem _ fun t _ ↦ hcenter t
    simpa [Finset.sum_sub_distrib] using hmem
  have hprojected :
      QuotientAddGroup.mk'
          (internalAddSubgroup E.W.K
            (E.W.highMultiplicityExtensionSubgroup z))
          (⟨(∑ t, occurrenceValue xs (pick t)) -
                E.W.highMultiplicityPairLength z • E.W.g,
              hcenterSum⟩ :
            E.W.highMultiplicityExtensionSubgroup z) = q := by
    let f := QuotientAddGroup.mk'
      (internalAddSubgroup E.W.K
        (E.W.highMultiplicityExtensionSubgroup z))
    have hsubtype :
        (⟨(∑ t, occurrenceValue xs (pick t)) -
              E.W.highMultiplicityPairLength z • E.W.g,
            hcenterSum⟩ :
          E.W.highMultiplicityExtensionSubgroup z) =
        ∑ t, (⟨occurrenceValue xs (pick t) - E.W.g, hcenter t⟩ :
          E.W.highMultiplicityExtensionSubgroup z) := by
      apply Subtype.ext
      simp [Finset.sum_sub_distrib]
    calc
      f (⟨(∑ t, occurrenceValue xs (pick t)) -
            E.W.highMultiplicityPairLength z • E.W.g,
          hcenterSum⟩ : E.W.highMultiplicityExtensionSubgroup z) =
          f (∑ t, (⟨occurrenceValue xs (pick t) - E.W.g,
            hcenter t⟩ : E.W.highMultiplicityExtensionSubgroup z)) :=
        congrArg f hsubtype
      _ = ∑ t, f (⟨occurrenceValue xs (pick t) - E.W.g,
          hcenter t⟩ : E.W.highMultiplicityExtensionSubgroup z) := by
        rw [map_sum]
      _ = ∑ t, E.W.centeredExtensionQuotientValue z
          (occurrenceValue xs (pick t)) := by
        apply Finset.sum_congr rfl
        intro t _
        dsimp only [f]
        simp only [OrdinaryGMOClaimBOutput.centeredExtensionQuotientValue,
          dif_pos (hcenter t)]
      _ = ∑ t, a t := by
        apply Finset.sum_congr rfl
        intro t _
        exact pick_projected t
      _ = q := hsum
  exact ⟨{
    quotientChoice := a
    quotientChoice_mem := ha
    source := pick
    source_mem := pick_mem
    source_projected := pick_projected
    source_injective := pick_injective
    quotientChoice_sum := hsum
    centeredSum_mem_extension := hcenterSum
    projected_centeredSum := hprojected
  }⟩

/-- Sum of the actual A-values selected by a paired lift. -/
noncomputable def OrdinaryGMOClaimBHighMultiplicityPairLift.pairSum
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    {q : E.W.HighMultiplicityInternalQuotient z}
    (R : OrdinaryGMOClaimBHighMultiplicityPairLift D q) : A :=
  ∑ t, occurrenceValue xs (R.source t)

/-- The genuine paired A-valued block sumset, behind a stable noncomputable
interface so public statements do not require a chosen `DecidableEq A`. -/
noncomputable def OrdinaryGMOClaimBHighMultiplicityCore.pairBlockIteratedSum
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) : Finset A := by
  classical
  exact iteratedFinsetSum
    (List.ofFn fun t : Fin (E.W.highMultiplicityPairLength z) ↦
      D.pairValueCell t)

/-- The lifted paired A-sum is a genuine member of the paired value-block
sumset. -/
theorem OrdinaryGMOClaimBHighMultiplicityPairLift.pairSum_mem
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    {q : E.W.HighMultiplicityInternalQuotient z}
    (R : OrdinaryGMOClaimBHighMultiplicityPairLift D q) :
    R.pairSum ∈ D.pairBlockIteratedSum := by
  classical
  unfold OrdinaryGMOClaimBHighMultiplicityCore.pairBlockIteratedSum
  rw [← fullLayerSumSpectrum_eq_iteratedFinsetSum]
  apply (mem_fullLayerSumSpectrum_iff_exists_choice _ R.pairSum).2
  let f : Fin (E.W.highMultiplicityPairLength z) ≃
      Fin (List.ofFn fun t : Fin (E.W.highMultiplicityPairLength z) ↦
        D.pairValueCell t).length :=
    finCongr (by simp)
  refine ⟨fun i ↦ occurrenceValue xs (R.source (f.symm i)), ?_, ?_⟩
  · intro i
    simp only [List.get_ofFn]
    convert Finset.mem_image.mpr
      ⟨R.source (f.symm i), R.source_mem (f.symm i), rfl⟩ using 1
    congr 1
  · simpa only [OrdinaryGMOClaimBHighMultiplicityPairLift.pairSum] using
      (f.symm.sum_comp fun t ↦ occurrenceValue xs (R.source t))

/-- Literal sum of the genuine residual singleton values. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlockSum
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) : A :=
  ∑ t, occurrenceValue xs (M.singletonSource t)

/-- The genuine singleton A-valued block sumset, behind a stable
noncomputable interface so public statements do not require a chosen
`DecidableEq A`. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlockIteratedSum
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) : Finset A := by
  classical
  exact iteratedFinsetSum
    (List.ofFn fun t : Fin (E.W.highMultiplicitySingletonLength z) ↦
      M.singletonValueCell t)

/-- The singleton block contributes the fixed center `g` modulo `K`. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlock_centered_mem_K
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.singletonBlockSum -
        E.W.highMultiplicitySingletonLength z • E.W.g ∈ E.W.K := by
  have hmem : (∑ t,
      (occurrenceValue xs (M.singletonSource t) - E.W.g)) ∈ E.W.K := by
    exact AddSubgroup.sum_mem _ fun t _ ↦
      (mem_addCosetFinset_iff E.W.K E.W.g _).1
        (M.singletonSource_value_mem_KCoset t)
  simpa [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlockSum,
    Finset.sum_sub_distrib] using hmem

/-- The fixed singleton sum is genuinely realized by the singleton block. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlockSum_mem
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.singletonBlockSum ∈ M.singletonBlockIteratedSum := by
  classical
  unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlockIteratedSum
  rw [← fullLayerSumSpectrum_eq_iteratedFinsetSum]
  apply (mem_fullLayerSumSpectrum_iff_exists_choice _ M.singletonBlockSum).2
  let f : Fin (E.W.highMultiplicitySingletonLength z) ≃
      Fin (List.ofFn fun t : Fin (E.W.highMultiplicitySingletonLength z) ↦
        M.singletonValueCell t).length :=
    finCongr (by simp)
  refine ⟨fun i ↦ occurrenceValue xs (M.singletonSource (f.symm i)), ?_, ?_⟩
  · intro i
    simp only [List.get_ofFn]
    have hi : occurrenceValue xs (M.singletonSource (f.symm i)) ∈
        M.singletonValueCell (f.symm i) := by
      unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonValueCell
      unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonCell
      simp
    convert hi using 1
    congr 1
  · simpa only [OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlockSum] using
      (f.symm.sum_comp fun t ↦ occurrenceValue xs (M.singletonSource t))

/-- The assembled sumset has no values outside the predicted affine
`d*(L) • g + L` coset. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.sumset_subset_extensionCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.partition.sumset ⊆
      addCosetFinset (E.W.highMultiplicityExtensionSubgroup z)
        (E.W.highMultiplicityExtensionLength z • E.W.g) := by
  classical
  rw [Theorem21SetPartition.sumset,
    fullLayerSumSpectrum_eq_iteratedFinsetSum]
  have hcell (c : Fin (E.W.highMultiplicityExtensionLength z)) :
      M.partition.valueCell c ⊆
        addCosetFinset (E.W.highMultiplicityExtensionSubgroup z) E.W.g := by
    intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    apply M.support_value_mem_extensionCoset i
    exact Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hi⟩
  have hsub := iteratedFinsetSum_subset_addCosetFinset_of_each_subset
    (E.W.highMultiplicityExtensionSubgroup z) E.W.g
    M.partition.valueCells (by
      intro C hC
      simp only [Theorem21SetPartition.valueCells, List.mem_ofFn] at hC
      obtain ⟨c, rfl⟩ := hC
      exact hcell c)
  simpa only [M.partition.length_valueCells] using hsub

/-- Reverse saturation inclusion.  A target extension-coset element is first
represented in `L / K` by actual paired occurrences; the old saturated block
then absorbs the resulting `K` discrepancy together with the genuine
singleton offsets. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.extensionCoset_subset_sumset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    addCosetFinset (E.W.highMultiplicityExtensionSubgroup z)
        (E.W.highMultiplicityExtensionLength z • E.W.g) ⊆
      M.partition.sumset := by
  classical
  intro y hy
  let L := E.W.highMultiplicityExtensionSubgroup z
  let dK := E.W.highMultiplicityOldLength
  let rQ := E.W.highMultiplicityPairLength z
  let s := E.W.highMultiplicitySingletonLength z
  let dL := E.W.highMultiplicityExtensionLength z
  have hyL : y - dL • E.W.g ∈ L := by
    exact (mem_addCosetFinset_iff L (dL • E.W.g) y).1 hy
  let ell : L := ⟨y - dL • E.W.g, hyL⟩
  let q : E.W.HighMultiplicityInternalQuotient z :=
    QuotientAddGroup.mk' (internalAddSubgroup E.W.K L) ell
  let R : OrdinaryGMOClaimBHighMultiplicityPairLift D q :=
    Classical.choice (exists_ordinaryGMOClaimBHighMultiplicityPairLift D q)
  have hpairDiff : ell.1 -
      (R.pairSum - rQ • E.W.g) ∈ E.W.K := by
    let pairCentered : L :=
      ⟨R.pairSum - rQ • E.W.g, by
        simpa only [L, rQ,
          OrdinaryGMOClaimBHighMultiplicityPairLift.pairSum] using
            R.centeredSum_mem_extension⟩
    have hmk :
        QuotientAddGroup.mk' (internalAddSubgroup E.W.K L) ell =
          QuotientAddGroup.mk' (internalAddSubgroup E.W.K L) pairCentered := by
      simpa only [q, pairCentered, L, rQ,
        OrdinaryGMOClaimBHighMultiplicityPairLift.pairSum] using
          R.projected_centeredSum.symm
    have hint := QuotientAddGroup.eq_iff_sub_mem.mp hmk
    change ell.1 - (R.pairSum - rQ • E.W.g) ∈ E.W.K at hint
    exact hint
  have hsingleK : M.singletonBlockSum - s • E.W.g ∈ E.W.K := by
    simpa only [s] using M.singletonBlock_centered_mem_K
  let correction : A := ell.1 - (R.pairSum - rQ • E.W.g) -
    (M.singletonBlockSum - s • E.W.g)
  have hcorrection : correction ∈ E.W.K := by
    exact E.W.K.sub_mem hpairDiff hsingleK
  let oldTarget : A := dK • E.W.g + correction
  have holdCoset : oldTarget ∈ addCosetFinset E.W.K (dK • E.W.g) := by
    apply (mem_addCosetFinset_iff E.W.K (dK • E.W.g) oldTarget).2
    simpa only [oldTarget, add_sub_cancel_left] using hcorrection
  have hold : oldTarget ∈ iteratedFinsetSum E.W.partition.valueCells := by
    have hsumset : oldTarget ∈ E.W.partition.sumset := by
      rw [E.W.saturation]
      simpa only [dK,
        OrdinaryGMOClaimBOutput.highMultiplicityOldLength] using holdCoset
    simpa only [Theorem21SetPartition.sumset,
      fullLayerSumSpectrum_eq_iteratedFinsetSum] using hsumset
  have hpair := R.pairSum_mem
  have hsingle := M.singletonBlockSum_mem
  have htail : R.pairSum + M.singletonBlockSum ∈
      D.pairBlockIteratedSum + M.singletonBlockIteratedSum :=
    Finset.mem_add.mpr ⟨R.pairSum, hpair, M.singletonBlockSum,
      hsingle, rfl⟩
  have hlen : dK + rQ + s = dL := by
    simpa only [dK, rQ, s, dL] using
      E.W.old_add_pair_add_singleton_eq_extensionLength z
  have hyEq : oldTarget + (R.pairSum + M.singletonBlockSum) = y := by
    have hell : dL • E.W.g + ell.1 = y := by
      dsimp only [ell]
      abel
    rw [← hell]
    dsimp only [oldTarget, correction]
    rw [← hlen, add_nsmul, add_nsmul]
    abel
  rw [M.sumset_eq_assembledBlockIteratedSum]
  unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.assembledBlockIteratedSum
  simpa only [OrdinaryGMOClaimBHighMultiplicityCore.pairBlockIteratedSum,
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlockIteratedSum] using
      (Finset.mem_add.mpr
        ⟨oldTarget, hold, R.pairSum + M.singletonBlockSum, htail, hyEq⟩)

/-- Exact honest saturation of the assembled `d*(L)`-cell partition. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.saturation
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.partition.sumset =
      addCosetFinset (E.W.highMultiplicityExtensionSubgroup z)
        (E.W.highMultiplicityExtensionLength z • E.W.g) :=
  Finset.Subset.antisymm M.sumset_subset_extensionCoset
    M.extensionCoset_subset_sumset

end GaoLean

#print axioms GaoLean.exists_ordinaryGMOClaimBHighMultiplicityPairLift
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityPairLift.pairSum_mem
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.singletonBlock_centered_mem_K
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.sumset_subset_extensionCoset
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.extensionCoset_subset_sumset
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.saturation
