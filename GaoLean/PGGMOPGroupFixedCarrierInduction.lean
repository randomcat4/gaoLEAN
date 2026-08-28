import GaoLean.PGGMOPGroupStructuralInduction
import GaoLean.PGGMOClaimBQuotientFixedCarrier

/-!
# Fixed-carrier structural induction for odd-primary groups

This module strengthens the structural recursion without turning a bare full
spectrum into a setpartition.  Its full branch retains one labelled carrier
of cardinality `seed.card`; every exact-`n` witness lies inside that same
carrier.  The other branches retain a genuine large partition or the
occurrence-faithful concentration conclusion.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The support-faithful recursive trichotomy. -/
def OrdinaryGMOFixedCarrierStructuralTrichotomy
    (xs : List A) (seed : Selection xs) (n : ℕ) : Prop :=
  Nonempty (OrdinaryFixedCarrierSpectrumFull xs seed.card n) ∨
    (∃ P : Theorem21SetPartition xs n seed.card,
      GMOTheorem21LargeAlternative xs seed n P) ∨
    Nonempty (OrdinaryGMOConcentration xs)

/-- A full replacement-partition sumset gives a fixed-carrier full spectrum
on its literal support. -/
noncomputable def Theorem21SetPartition.fixedCarrierSpectrumFull_of_sumset_eq_univ
    {xs : List A} {n m : ℕ}
    (P : Theorem21SetPartition xs n m)
    (hsumset : P.sumset = Finset.univ) :
    OrdinaryFixedCarrierSpectrumFull xs m n := by
  classical
  refine {
    carrier := P.support
    card_carrier := P.card_support_eq
    spectrumFull := ?_
  }
  intro y
  have hy : y ∈ P.sumset := by
    rw [hsumset]
    exact Finset.mem_univ y
  obtain ⟨I, hIsub, hIcard, hIsum⟩ :=
    P.exists_selection_subset_support_of_mem_sumset hy
  exact ⟨I, hIsub, hIcard, hIsum⟩

/-- A genuine large alternative is retained with its actual partition. -/
theorem ordinaryGMOFixedCarrierStructuralTrichotomy_of_large
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (P : Theorem21SetPartition xs n seed.card)
    (hlarge : GMOTheorem21LargeAlternative xs seed n P) :
    OrdinaryGMOFixedCarrierStructuralTrichotomy xs seed n :=
  Or.inr (Or.inl ⟨P, hlarge⟩)

/-- The terminal source output preserves a fixed carrier in the top-period
case and a genuine partition in every large case. -/
theorem GMOTheoremESourceOutput.fixedCarrierStructuralTrichotomy_of_terminal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {I : GMOTheoremEInput xs seed n}
    (out : GMOTheoremESourceOutput I)
    (hsourceWide : Nat.card A ≤ xs.length)
    (hterminal : out.partition.commonCosetCount out.H ≤ 1) :
    OrdinaryGMOFixedCarrierStructuralTrichotomy xs seed n := by
  classical
  have hlen : n ≤ seed.card := by
    have hmass := length_le_sum_layer_card out.partition.valueCells
      out.partition.valueCells_nonempty
    rw [out.partition.length_valueCells] at hmass
    simpa [Theorem21SetPartition.valueCells, List.map_ofFn,
      List.sum_ofFn, out.partition.sum_card_valueCell] using hmass
  by_cases htop : out.H = ⊤
  · have hsumset :=
      out.toProjected.sumset_eq_univ_of_H_eq_top htop
    exact Or.inl ⟨out.partition.fixedCarrierSpectrumFull_of_sumset_eq_univ
      hsumset⟩
  by_cases hbot : out.H = ⊥
  · exact Or.inr (Or.inl
      ⟨out.partition,
        out.toProjected.largeAlternative_of_H_eq_bot hbot hlen⟩)
  have hproper : out.H < ⊤ := lt_top_iff_ne_top.mpr htop
  have hcount :
      out.partition.commonCosetCount out.H = 0 ∨
        out.partition.commonCosetCount out.H = 1 := by
    omega
  rcases hcount with hzero | hone
  · exact Or.inr (Or.inl
      ⟨out.partition,
        out.largeAlternative_of_commonCosetCount_eq_zero hlen hzero⟩)
  · obtain ⟨h21⟩ :=
      out.toProjected.nonempty_theorem21Output_of_count_eq_one
        hbot hproper hone
    rcases h21.alternative with hlarge | hperiodic
    · exact Or.inr (Or.inl ⟨h21.partition, hlarge⟩)
    · obtain ⟨hperiodic⟩ := hperiodic
      have hquotientLe : Nat.card (A ⧸ hperiodic.H) ≤ Nat.card A :=
        Nat.le_of_dvd Nat.card_pos hperiodic.H.card_quotient_dvd_card
      exact Or.inr (Or.inr
        ⟨hperiodic.toOrdinaryGMOConcentration
          (hquotientLe.trans hsourceWide)⟩)

/-- A top Claim-B subgroup admits one parent carrier of cardinality
`seed.card`.  The old saturated support is retained literally; a fixed tail
is chosen once from the unused top-coset occurrences. -/
theorem OrdinaryGMOClaimBOutput.nonempty_fixedCarrierSpectrumFull_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hrn : pGroupDStar W.K ≤ n)
    (hKtop : W.K = ⊤) :
    Nonempty (OrdinaryFixedCarrierSpectrumFull xs seed.card n) := by
  classical
  let dK : ℕ := pGroupDStar W.K
  let U : Selection xs := W.partition.unusedInAddCoset W.K W.g
  have hseedLe : seed.card ≤ xs.length := by
    simpa using Finset.card_le_univ seed
  have hsupportLe : W.supportCard ≤ xs.length := by
    rw [← W.partition.card_support_eq]
    simpa using Finset.card_le_univ W.partition.support
  have hallUnused :
      ∀ i : Occurrence xs, i ∉ W.partition.support →
        occurrenceValue xs i ∈ addCosetFinset W.K W.g := by
    intro i _hi
    simp [hKtop]
  have hUCardRaw :
      (W.partition.unusedInAddCoset W.K W.g).card =
        xs.length - W.supportCard := by
    rw [W.partition.unusedInAddCoset_eq_unused W.K W.g hallUnused,
      W.partition.card_unused]
  have hsupportSeed : W.supportCard ≤ seed.card := by
    have hremaining := W.remaining_in_coset
    rw [hUCardRaw] at hremaining
    omega

  have hcarrierTailLe :
      seed.card - W.supportCard ≤ U.card := by
    dsimp only [U]
    rw [hUCardRaw]
    omega
  obtain ⟨carrierTail, hcarrierTailSub, hcarrierTailCard⟩ :=
    Finset.exists_subset_card_eq (s := U) hcarrierTailLe
  have htailBudget : n - dK ≤ seed.card - W.supportCard := by
    have hremaining := W.remaining_in_coset
    rw [hUCardRaw] at hremaining
    dsimp only [dK]
    omega
  have htailLe : n - dK ≤ carrierTail.card := by
    rw [hcarrierTailCard]
    exact htailBudget
  obtain ⟨tail, htailSub, htailCard⟩ :=
    Finset.exists_subset_card_eq (s := carrierTail) htailLe
  have hcarrierTailUnused :
      carrierTail ⊆ W.partition.unusedInAddCoset W.K W.g :=
    hcarrierTailSub
  have hsupportDisjointCarrierTail :
      Disjoint W.partition.support carrierTail := by
    rw [Finset.disjoint_left]
    intro i hiSupport hiTail
    have hiUnused :=
      (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1
        (hcarrierTailUnused hiTail)
    exact hiUnused.1 hiSupport
  let carrier : Selection xs := W.partition.support ∪ carrierTail
  have hcarrierCard : carrier.card = seed.card := by
    dsimp only [carrier]
    rw [Finset.card_union_of_disjoint hsupportDisjointCarrierTail,
      W.partition.card_support_eq, hcarrierTailCard]
    omega
  have htailUnused :
      tail ⊆ W.partition.unusedInAddCoset W.K W.g :=
    htailSub.trans hcarrierTailUnused
  let tailSum : A := ∑ i ∈ tail, occurrenceValue xs i
  refine ⟨{
    carrier := carrier
    card_carrier := hcarrierCard
    spectrumFull := ?_
  }⟩
  intro y
  let firstTarget : A := y - tailSum
  have hfirstTargetSumset : firstTarget ∈ W.partition.sumset := by
    rw [W.saturation]
    simp [hKtop]
  obtain ⟨first, hfirstSub, hfirstCard, hfirstSum⟩ :=
    W.partition.exists_selection_subset_support_of_mem_sumset
      hfirstTargetSumset
  have hdisj : Disjoint first tail := by
    rw [Finset.disjoint_left]
    intro i hiFirst hiTail
    have hiUnused :=
      (W.partition.mem_unusedInAddCoset_iff W.K W.g i).1
        (htailUnused hiTail)
    exact hiUnused.1 (hfirstSub hiFirst)
  let witness : Selection xs := first ∪ tail
  refine ⟨witness, ?_, ?_, ?_⟩
  · intro i hi
    change i ∈ first ∪ tail at hi
    change i ∈ W.partition.support ∪ carrierTail
    rcases Finset.mem_union.mp hi with hiFirst | hiTail
    · exact Finset.mem_union.mpr (Or.inl (hfirstSub hiFirst))
    · exact Finset.mem_union.mpr (Or.inr (htailSub hiTail))
  · dsimp only [witness]
    rw [Finset.card_union_of_disjoint hdisj, hfirstCard, htailCard]
    dsimp only [dK]
    exact Nat.add_sub_of_le hrn
  · dsimp only [witness]
    rw [Finset.sum_union hdisj, hfirstSum]
    dsimp [firstTarget, tailSum]
    abel

/-- The strengthened quotient trichotomy lifts either to a parent fixed
carrier or to source concentration. -/
theorem OrdinaryGMOClaimBOutput.fixedCarrier_or_concentration_of_quotientTrichotomy
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hproper : W.K < ⊤)
    (hzero : pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card)
    (hlen : pGroupDStar W.K + pGroupDStar (A ⧸ W.K) ≤ n)
    (htri : OrdinaryGMOFixedCarrierStructuralTrichotomy
      (W.paddedQuotientRValues hzero)
      (W.paddedQuotientRSeed hzero) (pGroupDStar (A ⧸ W.K))) :
    Nonempty (OrdinaryFixedCarrierSpectrumFull xs seed.card n) ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
  letI : Fintype (A ⧸ W.K) := Fintype.ofFinite (A ⧸ W.K)
  letI : Nontrivial (A ⧸ W.K) :=
    W.nontrivial_quotient_of_ne_top (ne_of_lt hproper)
  have hdQpos : 1 ≤ pGroupDStar (A ⧸ W.K) := by
    have hgt := one_lt_ordinaryDavenportValue (B := A ⧸ W.K)
    have hrecover := pGroupDStar_add_one (A ⧸ W.K)
    omega
  rcases htri with hfixed | hlarge | hconcentration
  · obtain ⟨FQ⟩ := hfixed
    exact Or.inl
      (W.exists_fixedCarrier_spectrumFull_of_paddedQuotientR
        hzero hdQpos FQ.toOrdinarySpectrumFull hlen)
  · obtain ⟨Qpartition, Qlarge⟩ := hlarge
    by_cases hsumset : Qpartition.sumset = Finset.univ
    · have hquotientFull :=
        Qpartition.ordinarySpectrumFull_of_sumset_eq_univ hsumset
      exact Or.inl
        (W.exists_fixedCarrier_spectrumFull_of_paddedQuotientR
          hzero hdQpos hquotientFull hlen)
    · exact Or.inr
        (W.nonempty_concentration_of_quotientLarge_nonfull
          hzero hdQpos Qpartition Qlarge hsumset)
  · obtain ⟨CQ⟩ := hconcentration
    exact Or.inr
      (W.nonempty_quotientConcentrationPullback hzero hdQpos CQ)

/-- The proposition-valued goal of the fixed-carrier recursion. -/
def OrdinaryGMOPGroupFixedCarrierInductionGoal
    (A : Type u) [AddCommGroup A] [Fintype A] : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ (xs : List A) (seed : Selection xs) (n : ℕ)
      (I : GMOTheoremEInput xs seed n),
      0 < n →
      pGroupDStar A ≤ n →
      Nat.card A ≤ xs.length →
      OrdinaryGMOFixedCarrierStructuralTrichotomy xs seed n

/-- Genuine well-founded recursion with the ambient cardinality as measure.
No recursive conclusion or external boundary is accepted as an input. -/
theorem ordinaryGMOPGroupFixedCarrierStructuralTrichotomy
    (A : Type u) [AddCommGroup A] [Fintype A]
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (xs : List A) (seed : Selection xs) (n : ℕ)
    (I : GMOTheoremEInput xs seed n)
    (hn : 0 < n)
    (hambient : pGroupDStar A ≤ n)
    (hsourceWide : Nat.card A ≤ xs.length) :
    OrdinaryGMOFixedCarrierStructuralTrichotomy xs seed n := by
  obtain ⟨out⟩ :=
    nonempty_gmoTheoremESourceOutput_for_structuralInduction I hn
  by_cases hterminal : out.partition.commonCosetCount out.H ≤ 1
  · exact out.fixedCarrierStructuralTrichotomy_of_terminal
      hsourceWide hterminal
  have hN : 2 ≤ out.partition.commonCosetCount out.H := by omega
  by_cases hlarge :
      GMOTheorem21LargeAlternative xs seed n out.partition
  · exact ordinaryGMOFixedCarrierStructuralTrichotomy_of_large
      out.partition hlarge
  obtain ⟨Wmax, hmax⟩ :=
    exists_card_maximal_ordinaryGMOClaimBOutput
      (out.nonempty_ordinaryGMOClaimBOutput_case1
        p hp hpTwo hA hambient hN hlarge)
  by_cases hKtop : Wmax.K = ⊤
  · have hrn : pGroupDStar Wmax.K ≤ n := by
      exact (Nat.le_add_right (pGroupDStar Wmax.K)
        (pGroupDStar (A ⧸ Wmax.K))).trans
          (Wmax.canonicalQuotient_budget hambient)
    exact Or.inl
      (Wmax.nonempty_fixedCarrierSpectrumFull_of_K_eq_top hrn hKtop)
  have hproper : Wmax.K < ⊤ := lt_top_iff_ne_top.mpr hKtop
  obtain ⟨R⟩ :=
    Wmax.nonempty_quotientRecursiveInput_of_card_maximal
      p hp hpTwo hA hmax hproper hambient
  obtain ⟨IQ⟩ := R.theoremEInput
  letI : Fintype (A ⧸ Wmax.K) := Fintype.ofFinite (A ⧸ Wmax.K)
  have hquotientTrichotomy : OrdinaryGMOFixedCarrierStructuralTrichotomy
      (Wmax.paddedQuotientRValues R.zeroCapacity)
      (Wmax.paddedQuotientRSeed R.zeroCapacity)
      (pGroupDStar (A ⧸ Wmax.K)) :=
    ordinaryGMOPGroupFixedCarrierStructuralTrichotomy
      (A ⧸ Wmax.K) p hp hpTwo R.quotientPGroup
      (Wmax.paddedQuotientRValues R.zeroCapacity)
      (Wmax.paddedQuotientRSeed R.zeroCapacity)
      (pGroupDStar (A ⧸ Wmax.K)) IQ R.dQPos le_rfl R.sourceWide
  have hparent :=
    Wmax.fixedCarrier_or_concentration_of_quotientTrichotomy
      hproper R.zeroCapacity R.liftBudget hquotientTrichotomy
  rcases hparent with hfixed | hconcentration
  · exact Or.inl hfixed
  · exact Or.inr (Or.inr hconcentration)
termination_by Nat.card A
decreasing_by
  exact R.quotientCardLt

/-- The fixed-carrier recursive theorem closes its goal internally. -/
theorem ordinaryGMOPGroupFixedCarrierInductionGoal
    (A : Type u) [AddCommGroup A] [Fintype A] :
    OrdinaryGMOPGroupFixedCarrierInductionGoal A := by
  intro p hp hpTwo hA xs seed n I hn hambient hsourceWide
  exact ordinaryGMOPGroupFixedCarrierStructuralTrichotomy
    A p hp hpTwo hA xs seed n I hn hambient hsourceWide

#print axioms GaoLean.Theorem21SetPartition.fixedCarrierSpectrumFull_of_sumset_eq_univ
#print axioms GaoLean.GMOTheoremESourceOutput.fixedCarrierStructuralTrichotomy_of_terminal
#print axioms GaoLean.OrdinaryGMOClaimBOutput.nonempty_fixedCarrierSpectrumFull_of_K_eq_top
#print axioms GaoLean.OrdinaryGMOClaimBOutput.fixedCarrier_or_concentration_of_quotientTrichotomy
#print axioms GaoLean.ordinaryGMOPGroupFixedCarrierStructuralTrichotomy
#print axioms GaoLean.ordinaryGMOPGroupFixedCarrierInductionGoal

end GaoLean
