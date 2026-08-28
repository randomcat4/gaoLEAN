import GaoLean.PGGMOClaimBHighMultiplicityLift

/-!
# Honest remaining ledger for high-multiplicity enlargement

This module completes the occurrence ledger after the verified three-block
assembly.  The enlarged witness is still a plain `OrdinaryGMOClaimBOutput`:
its support is the literal union of the old support and the three genuinely
selected source ranges, and its subgroup is the strict extension `L`.

The old `g + K` reserve loses exactly the reserve and singleton ranges.  The
high range has nonzero centered quotient value, so it is disjoint from the
entire old zero-class reserve and does not enter that subtraction.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The two genuinely consumed parts of the old zero-class reserve. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.consumedKReserve
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) : Selection xs := by
  classical
  exact D.reserveSourceRange ∪ M.singletonSourceRange

/-- The assembled partition support is exactly the old support together with
the three labelled source ranges; no full-envelope support is substituted. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition_support_eq
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.partition.support =
      E.W.partition.support ∪
        (D.highSourceRange ∪
          (D.reserveSourceRange ∪ M.singletonSourceRange)) := by
  classical
  let hlen : E.W.highMultiplicityOldLength +
        (E.W.highMultiplicityPairLength z +
          E.W.highMultiplicitySingletonLength z) =
      E.W.highMultiplicityExtensionLength z := by
    simpa only [Nat.add_assoc] using
      E.W.old_add_pair_add_singleton_eq_extensionLength z
  have hunion :
      Finset.univ.biUnion
          (fun c ↦ M.rawCells (Fin.cast hlen.symm c)) =
        Finset.univ.biUnion M.rawCells := by
    ext i
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨c, hc⟩
      exact ⟨Fin.cast hlen.symm c, hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨Fin.cast hlen c, by simpa using hc⟩
  unfold Theorem21SetPartition.support
  unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition
  change Finset.univ.biUnion
      (fun c ↦ M.rawCells (Fin.cast hlen.symm c)) = _
  rw [hunion, M.biUnion_rawCells]
  rfl

/-- Every consumed zero-class position really belongs to the old `g + K`
reserve. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.consumedKReserve_subset_old
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.consumedKReserve ⊆
      E.W.partition.unusedInAddCoset E.W.K E.W.g := by
  classical
  intro i hi
  unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.consumedKReserve at hi
  rcases Finset.mem_union.mp hi with hiReserve | hiSingle
  · obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hiReserve
    exact D.reserve_mem t
  · obtain ⟨t, -, rfl⟩ := Finset.mem_map.mp hiSingle
    exact M.singleton_mem t

/-- Exactly `d*(L) - d*(K)` positions are consumed from the old `K` reserve. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.card_consumedKReserve
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    M.consumedKReserve.card =
      E.W.highMultiplicityExtensionLength z -
        E.W.highMultiplicityOldLength := by
  classical
  unfold OrdinaryGMOClaimBHighMultiplicityAssemblyData.consumedKReserve
  rw [Finset.card_union_of_disjoint
      M.singletonRange_disjoint_reserveRange.symm,
    D.card_reserveSourceRange, M.card_singletonSourceRange]
  simpa only [OrdinaryGMOClaimBOutput.highMultiplicityPairLength] using
    E.W.pair_add_singleton_eq_extension_sub_old z

/-- The nonzero high range is disjoint from the whole old zero-class reserve,
not merely from the selected reserve subrange.  This is why high occurrences
do not count as consumed old reserve. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.highSourceRange_disjoint_oldReserve
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    Disjoint D.highSourceRange
      (E.W.partition.unusedInAddCoset E.W.K E.W.g) := by
  classical
  rw [Finset.disjoint_left]
  intro i hiHigh hiOld
  obtain ⟨t, -, hi⟩ := Finset.mem_map.mp hiHigh
  have hhigh : E.W.centeredQuotientValue (D.highSource t) = z :=
    (E.W.mem_sourceQuotientFiber_iff z (D.highSource t)).1
      (D.high_mem_fiber t)
  have hzero : E.W.centeredQuotientValue i = 0 := by
    exact (QuotientAddGroup.eq_zero_iff _).2
      ((mem_addCosetFinset_iff E.W.K E.W.g _).1
        ((E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g i).1 hiOld |>.2))
  rw [hi] at hhigh
  exact D.nonzero (hhigh.symm.trans hzero)

/-- Deleting exactly the consumed zero-class ranges from the old reserve
leaves genuine unused occurrences for the assembled partition in `g + L`. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.oldReserve_sdiff_consumed_subset_newReserve
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D) :
    E.W.partition.unusedInAddCoset E.W.K E.W.g \ M.consumedKReserve ⊆
      M.partition.unusedInAddCoset
        (E.W.highMultiplicityExtensionSubgroup z) E.W.g := by
  classical
  intro i hi
  have hiOld := (Finset.mem_sdiff.mp hi).1
  have hiNotConsumed := (Finset.mem_sdiff.mp hi).2
  apply (M.partition.mem_unusedInAddCoset_iff
    (E.W.highMultiplicityExtensionSubgroup z) E.W.g i).2
  constructor
  · intro hiSupport
    rw [M.partition_support_eq] at hiSupport
    rcases Finset.mem_union.mp hiSupport with hiOldSupport | hiNew
    · exact ((E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g i).1
        hiOld |>.1) hiOldSupport
    · rcases Finset.mem_union.mp hiNew with hiHigh | hiConsumed
      · exact (Finset.disjoint_left.mp
          D.highSourceRange_disjoint_oldReserve) hiHigh hiOld
      · exact hiNotConsumed hiConsumed
  · apply (mem_addCosetFinset_iff
      (E.W.highMultiplicityExtensionSubgroup z) E.W.g _).2
    exact E.W.K_le_highMultiplicityExtensionSubgroup z
      ((mem_addCosetFinset_iff E.W.K E.W.g _).1
        ((E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g i).1 hiOld |>.2))

/-- Exact remaining-occurrence lower bound for the enlarged plain witness.
The standard driver hypothesis `Nat.card A ≤ n` supplies `d*(L) ≤ n`; no
separate length premise is added. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.remaining_in_extensionCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (hnA : Nat.card A ≤ n) :
    n - E.W.highMultiplicityExtensionLength z +
        (xs.length - seed.card) ≤
      (M.partition.unusedInAddCoset
        (E.W.highMultiplicityExtensionSubgroup z) E.W.g).card := by
  classical
  let oldReserve := E.W.partition.unusedInAddCoset E.W.K E.W.g
  let consumed := M.consumedKReserve
  let newReserve := M.partition.unusedInAddCoset
    (E.W.highMultiplicityExtensionSubgroup z) E.W.g
  have hsub : oldReserve \ consumed ⊆ newReserve := by
    simpa only [oldReserve, consumed, newReserve] using
      M.oldReserve_sdiff_consumed_subset_newReserve
  have hcard := Finset.card_le_card hsub
  have hconsumedSub : consumed ⊆ oldReserve := by
    simpa only [consumed, oldReserve] using M.consumedKReserve_subset_old
  have hinter : consumed ∩ oldReserve = consumed :=
    Finset.inter_eq_left.mpr hconsumedSub
  have hsdiff : (oldReserve \ consumed).card =
      oldReserve.card - consumed.card := by
    simp only [Finset.card_sdiff, hinter]
  rw [hsdiff] at hcard
  have hold :
      n - E.W.highMultiplicityOldLength + (xs.length - seed.card) ≤
        oldReserve.card := by
    simpa only [oldReserve,
      OrdinaryGMOClaimBOutput.highMultiplicityOldLength] using
        E.W.remaining_in_coset
  have hconsumed : consumed.card =
      E.W.highMultiplicityExtensionLength z -
        E.W.highMultiplicityOldLength := by
    simpa only [consumed] using M.card_consumedKReserve
  have hnL : E.W.highMultiplicityExtensionLength z ≤ n := by
    simpa only [OrdinaryGMOClaimBOutput.highMultiplicityExtensionLength] using
      pGroupDStar_addSubgroup_le_of_natCard_le
        (E.W.highMultiplicityExtensionSubgroup z) hnA
  have hdKLe : E.W.highMultiplicityOldLength ≤
      E.W.highMultiplicityExtensionLength z := by
    have h := E.W.old_add_pair_le_extensionLength z
    omega
  have hbeforeSubtract :
      (n - E.W.highMultiplicityExtensionLength z +
          (xs.length - seed.card)) + consumed.card ≤ oldReserve.card := by
    rw [hconsumed]
    calc
      (n - E.W.highMultiplicityExtensionLength z +
            (xs.length - seed.card)) +
          (E.W.highMultiplicityExtensionLength z -
            E.W.highMultiplicityOldLength) =
        n - E.W.highMultiplicityOldLength +
          (xs.length - seed.card) := by omega
      _ ≤ oldReserve.card := hold
  have hafterSubtract :
      n - E.W.highMultiplicityExtensionLength z +
          (xs.length - seed.card) ≤
        oldReserve.card - consumed.card :=
    Nat.le_sub_of_add_le hbeforeSubtract
  exact hafterSubtract.trans hcard

/-- The extension subgroup is nontrivial because it strictly contains the
already nontrivial Claim-B subgroup. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.extensionSubgroup_ne_bot
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    E.W.highMultiplicityExtensionSubgroup z ≠ ⊥ := by
  intro hbot
  apply E.W.nontrivial
  apply le_antisymm
  · rw [← hbot]
    exact E.W.K_le_highMultiplicityExtensionSubgroup z
  · exact bot_le

/-- The genuine enlarged plain Claim-B witness.  Its partition is the
assembled occurrence partition and its saturation is the proved equality,
not a field copied from an envelope. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityAssemblyData.enlargedOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (hnA : Nat.card A ≤ n) : OrdinaryGMOClaimBOutput xs seed n := {
  K := E.W.highMultiplicityExtensionSubgroup z
  nontrivial := D.extensionSubgroup_ne_bot
  g := E.W.g
  supportCard := M.assembledSupportCard
  partition := M.partition
  support_in_coset := M.support_value_mem_extensionCoset
  saturation := M.saturation
  remaining_in_coset := M.remaining_in_extensionCoset hnA
}

@[simp]
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.enlargedOutput_K
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (hnA : Nat.card A ≤ n) :
    (M.enlargedOutput hnA).K =
      E.W.highMultiplicityExtensionSubgroup z := rfl

/-- The assembled witness is a strict plain Claim-B enlargement. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.old_K_lt_enlarged_K
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (hnA : Nat.card A ≤ n) :
    E.W.K < (M.enlargedOutput hnA).K := by
  change E.W.K < E.W.highMultiplicityExtensionSubgroup z
  exact E.W.K_lt_highMultiplicityExtensionSubgroup D.nonzero

/-- Existential interface for downstream plain-witness maximality. -/
theorem exists_strictly_enlarged_ordinaryGMOClaimBOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (hnA : Nat.card A ≤ n) :
    ∃ W' : OrdinaryGMOClaimBOutput xs seed n, E.W.K < W'.K :=
  ⟨M.enlargedOutput hnA, M.old_K_lt_enlarged_K hnA⟩

/-- The honest high-multiplicity assembly contradicts cardinal maximality of
the old plain Claim-B witness. -/
theorem OrdinaryGMOClaimBHighMultiplicityAssemblyData.not_card_maximal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    {D : OrdinaryGMOClaimBHighMultiplicityCore E z}
    (M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D)
    (hnA : Nat.card A ≤ n)
    (hmax : ∀ W : OrdinaryGMOClaimBOutput xs seed n,
      Nat.card W.K ≤ Nat.card E.W.K) : False :=
  E.W.not_subgroup_lt_of_card_maximal hmax (M.enlargedOutput hnA)
    (M.old_K_lt_enlarged_K hnA)

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.partition_support_eq
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityCore.highSourceRange_disjoint_oldReserve
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.remaining_in_extensionCoset
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.enlargedOutput
#print axioms GaoLean.exists_strictly_enlarged_ordinaryGMOClaimBOutput
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityAssemblyData.not_card_maximal
