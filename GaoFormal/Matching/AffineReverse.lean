import GaoFormal.Matching.FiniteFieldCoverage

/-!
# Labelled reverse construction for the affine-failure certificate

This file closes the constructive direction of (3.4) in the frozen
affine-exchange theorem.  A preselected set of exceptional source labels is
kept fixed.  Fillers are chosen only from the affine fibre and outside every
reservoir endpoint; toggling the `q - 1` copies of each independent direction
then corrects the remaining error in the kernel of the quotient map.
-/

namespace GaoFormal

open scoped BigOperators

namespace OccurrenceReservoir

variable {q : ℕ} [NeZero q] [Fact q.Prime]
variable {Ω V Q : Type*} [Fintype Ω] [DecidableEq Ω]
variable [AddCommGroup V] [Module (ZMod q) V]
variable [AddCommGroup Q] [Module (ZMod q) Q]
variable {C : Ω → V} {k : ℕ}

/-- Source-shaped full affine exchange.  The heavy support spans the ambient
space affinely, and its cardinality is large enough that the matching formula
chooses the full finrank.  Consequently every target has an exact-`d`
occurrence-labelled representation; no reservoir is supplied by the caller. -/
theorem exists_fixedCardinality_sum_of_fullHeavySupport
    [FiniteDimensional (ZMod q) V]
    (C : Ω → V)
    (hvectorSpan :
      vectorSpan (ZMod q)
        ((thresholdSupport C (q - 1) : Finset V) : Set V) = ⊤)
    (hhalf : Module.finrank (ZMod q) V ≤
      (thresholdSupport C (q - 1)).card / 2)
    (htwo : (2 : ZMod q) ≠ 0)
    (d : ℕ)
    (hbase : Module.finrank (ZMod q) V * (q - 1) ≤ d)
    (hcapacity : d + Module.finrank (ZMod q) V * (q - 1) ≤
      Fintype.card Ω)
    (y : V) :
    ∃ I : Finset Ω, I.card = d ∧ (∑ ω ∈ I, C ω) = y := by
  have hR := exists_occurrenceReservoir_at_threshold
    (F := ZMod q) C (q - 1) htwo
  rw [hvectorSpan, finrank_top, min_eq_left hhalf] at hR
  rcases hR with ⟨R⟩
  exact R.exists_fixedCardinality_sum_of_card_eq_finrank rfl d
    hbase hcapacity y

/-- The geometric dichotomy's non-full branch, derived from the raw support
hypotheses.  If a finite set spans `V` linearly but not affinely, its affine
direction is a hyperplane.  Any support point `α` is outside that direction,
and every other support point lies in the affine fibre `α + W`.

This is the precise linear-algebra bridge needed before the labelled
exceptional-count split; no hyperplane or base point is supplied by the
caller. -/
theorem exists_affineHyperplaneGeometry_of_linearSpan_eq_top
    [FiniteDimensional (ZMod q) V]
    (S : Finset V) (hS : S.Nonempty)
    (hlinear : Submodule.span (ZMod q) (S : Set V) = ⊤)
    (hproper : vectorSpan (ZMod q) (S : Set V) ≠ ⊤) :
    ∃ α ∈ S,
      α ∉ vectorSpan (ZMod q) (S : Set V) ∧
      Module.finrank (ZMod q) (vectorSpan (ZMod q) (S : Set V)) + 1 =
        Module.finrank (ZMod q) V ∧
      ∀ x ∈ S, x - α ∈ vectorSpan (ZMod q) (S : Set V) := by
  classical
  rcases hS with ⟨α, hαS⟩
  let W := vectorSpan (ZMod q) (S : Set V)
  have hdiff : ∀ x ∈ S, x - α ∈ W := by
    intro x hx
    exact vsub_mem_vectorSpan (ZMod q)
      (show x ∈ (S : Set V) from hx)
      (show α ∈ (S : Set V) from hαS)
  have hαnot : α ∉ W := by
    intro hαW
    have hSsub : (S : Set V) ⊆ W := by
      intro x hx
      have hxDiff := hdiff x hx
      have hxMem := W.add_mem hxDiff hαW
      simpa using hxMem
    have htopLe : (⊤ : Submodule (ZMod q) V) ≤ W := by
      rw [← hlinear]
      exact Submodule.span_le.mpr hSsub
    exact hproper (eq_top_iff.mpr htopLe)
  have hαzero : α ≠ 0 := by
    intro hα
    apply hαnot
    simpa [hα] using W.zero_mem
  have hSsup : (S : Set V) ⊆
      ((W ⊔ (ZMod q) ∙ α : Submodule (ZMod q) V) : Set V) := by
    intro x hx
    change x ∈ W ⊔ (ZMod q) ∙ α
    have hxDiffSup : x - α ∈ W ⊔ (ZMod q) ∙ α :=
      (show W ≤ W ⊔ (ZMod q) ∙ α from le_sup_left) (hdiff x hx)
    have hαSup : α ∈ W ⊔ (ZMod q) ∙ α :=
      (show (ZMod q) ∙ α ≤ W ⊔ (ZMod q) ∙ α from le_sup_right)
        (Submodule.mem_span_singleton_self α)
    simpa only [sub_add_cancel] using
      (W ⊔ (ZMod q) ∙ α).add_mem hxDiffSup hαSup
  have hsup : W ⊔ (ZMod q) ∙ α = ⊤ := by
    apply top_unique
    rw [← hlinear]
    exact Submodule.span_le.mpr hSsup
  have hdimLower :
      Module.finrank (ZMod q) V ≤ Module.finrank (ZMod q) W + 1 := by
    have hdim := Submodule.finrank_add_le_finrank_add_finrank
      W ((ZMod q) ∙ α)
    rw [hsup, finrank_top, finrank_span_singleton hαzero] at hdim
    exact hdim
  have hdimUpper :
      Module.finrank (ZMod q) W < Module.finrank (ZMod q) V :=
    Submodule.finrank_lt hproper
  refine ⟨α, hαS, hαnot, ?_, hdiff⟩
  exact Nat.le_antisymm hdimUpper hdimLower

/-- Lift the independent-difference matching on the heavy support to an
occurrence reservoir whose directions span exactly the kernel of the affine
quotient.  This is the geometric-to-labelled bridge used in the hyperplane
branch: the affine direction space of the heavy support is supplied as the
kernel equality, while the half-cardinality hypothesis ensures that the
matching formula chooses its full affine dimension rather than the support
cardinality boundary. -/
theorem exists_kernel_reservoir_of_heavySupport
    [FiniteDimensional (ZMod q) V]
    (C : Ω → V) (φ : V →ₗ[ZMod q] Q) (β : Q)
    (hvectorSpan :
      vectorSpan (ZMod q)
        ((thresholdSupport C (q - 1) : Finset V) : Set V) = LinearMap.ker φ)
    (hhalf : Module.finrank (ZMod q) (LinearMap.ker φ) ≤
      (thresholdSupport C (q - 1)).card / 2)
    (hfibre : ∀ x ∈ thresholdSupport C (q - 1), φ x = β)
    (htwo : (2 : ZMod q) ≠ 0) :
    ∃ R : OccurrenceReservoir (F := ZMod q) C
        (Module.finrank (ZMod q) (LinearMap.ker φ)) (q - 1),
      Submodule.span (ZMod q) (Set.range R.direction) = LinearMap.ker φ ∧
      ∀ ω ∈ endpoints R, φ (C ω) = β := by
  classical
  have hmatch := IndependentDifferenceMatching.exists_maximum_matching_at_formula
    (F := ZMod q) (A := thresholdSupport C (q - 1)) htwo
  rw [hvectorSpan, min_eq_left hhalf] at hmatch
  rcases hmatch with ⟨M, _hmax⟩
  let R := M.toOccurrenceReservoir C (q - 1)
  have hleftValue : ∀ p,
      C (R.left p) = M.left p.1 := by
    intro p
    exact M.toOccurrenceReservoir_left_value C (q - 1) p.1 p.2
  have hrightValue : ∀ p,
      C (R.right p) = M.right p.1 := by
    intro p
    exact M.toOccurrenceReservoir_right_value C (q - 1) p.1 p.2
  have hleftFibre : ∀ p, φ (C (R.left p)) = β := by
    intro p
    rw [hleftValue p]
    exact hfibre (M.left p.1) (M.left_mem p.1)
  have hrightFibre : ∀ p, φ (C (R.right p)) = β := by
    intro p
    rw [hrightValue p]
    exact hfibre (M.right p.1) (M.right_mem p.1)
  have hqpos : 0 < q - 1 := by
    have hq2 : 2 ≤ q := (Fact.out : q.Prime).two_le
    omega
  let j : Fin (q - 1) := ⟨0, hqpos⟩
  have hspanle :
      Submodule.span (ZMod q) (Set.range R.direction) ≤ LinearMap.ker φ := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    change φ (R.direction i) = 0
    rw [← R.difference_eq i j, map_sub, hrightFibre (i, j),
      hleftFibre (i, j), sub_self]
  have hfinrank :
      Module.finrank (ZMod q)
          (Submodule.span (ZMod q) (Set.range R.direction)) =
        Module.finrank (ZMod q) (LinearMap.ker φ) := by
    rw [finrank_span_eq_card R.independent]
    simp
  have hspanExact :
      Submodule.span (ZMod q) (Set.range R.direction) = LinearMap.ker φ :=
    Submodule.eq_of_le_of_finrank_eq hspanle hfinrank
  refine ⟨R, hspanExact, ?_⟩
  intro ω hω
  rcases Finset.mem_union.mp hω with hω | hω
  · rcases Finset.mem_image.mp hω with ⟨p, _hp, rfl⟩
    exact hleftFibre p
  · rcases Finset.mem_image.mp hω with ⟨p, _hp, rfl⟩
    exact hrightFibre p

/-- The exact reverse implication in the labelled affine certificate.

`E` is the complete set of exceptional labels.  The hypotheses deliberately
record both sides of that classification: labels in `E` are precisely those
whose quotient value is not `β`.  The reservoir endpoints therefore lie in
the affine fibre, while `J` is the exceptional subset prescribed by the
right-hand side of (3.4).
-/
theorem exists_fixedCardinality_sum_of_exceptionalOffsets
    (R : OccurrenceReservoir (F := ZMod q) C k (q - 1))
    (φ : V →ₗ[ZMod q] Q) (β : Q) (E J : Finset Ω)
    (hExceptional : ∀ ω, ω ∈ E ↔ φ (C ω) ≠ β)
    (hJ : J ⊆ E)
    (hEndpoint : ∀ ω ∈ endpoints R, φ (C ω) = β)
    (hspan : Submodule.span (ZMod q) (Set.range R.direction) = LinearMap.ker φ)
    (d : ℕ)
    (hbase : k * (q - 1) + E.card ≤ d)
    (hcapacity : d + k * (q - 1) + E.card ≤ Fintype.card Ω)
    (y : V)
    (hquotient :
      φ y - d • β = ∑ ω ∈ J, (φ (C ω) - β)) :
    ∃ I : Finset Ω, I.card = d ∧ (∑ ω ∈ I, C ω) = y := by
  classical
  let m := k * (q - 1)
  have hEndpointE : Disjoint (endpoints R) E := by
    rw [Finset.disjoint_left]
    intro ω hωR hωE
    exact (hExceptional ω).mp hωE (hEndpoint ω hωR)
  have hforbiddenCard : (endpoints R ∪ E).card = 2 * m + E.card := by
    rw [Finset.card_union_of_disjoint hEndpointE, card_endpoints R]
  have hforbiddenSubset : endpoints R ∪ E ⊆ (Finset.univ : Finset Ω) :=
    Finset.subset_univ _
  have havailableCard :
      ((Finset.univ : Finset Ω) \ (endpoints R ∪ E)).card =
        Fintype.card Ω - (2 * m + E.card) := by
    rw [Finset.card_sdiff_of_subset hforbiddenSubset, hforbiddenCard]
    simp
  have hneed : d - J.card - m ≤
      ((Finset.univ : Finset Ω) \ (endpoints R ∪ E)).card := by
    rw [havailableCard]
    have hJE := Finset.card_le_card hJ
    omega
  obtain ⟨fillers, hfillers, hfillersCard⟩ :=
    Finset.exists_subset_card_eq hneed
  have hJcard : J.card + m ≤ d := by
    have hJE := Finset.card_le_card hJ
    omega
  have hcardDecomp : d = J.card + fillers.card + m := by
    rw [hfillersCard]
    omega
  have hfillersEndpoint : Disjoint fillers (endpoints R) := by
    rw [Finset.disjoint_left]
    intro ω hωF hωR
    have hcomp := Finset.mem_sdiff.mp (hfillers hωF)
    exact hcomp.2 (Finset.mem_union_left E hωR)
  have hfillersE : Disjoint fillers E := by
    rw [Finset.disjoint_left]
    intro ω hωF hωE
    have hcomp := Finset.mem_sdiff.mp (hfillers hωF)
    exact hcomp.2 (Finset.mem_union_right (endpoints R) hωE)
  have hJEdis : Disjoint J fillers := by
    exact Finset.disjoint_of_subset_left hJ hfillersE.symm

  let baseline : V := ∑ p : Fin k × Fin (q - 1), C (R.left p)
  let exceptionalSum : V := ∑ ω ∈ J, C ω
  let fillerSum : V := ∑ ω ∈ fillers, C ω

  have hmapExceptional : φ exceptionalSum = ∑ ω ∈ J, φ (C ω) := by
    simp [exceptionalSum, map_sum]
  have hmapFillers : φ fillerSum = fillers.card • β := by
    dsimp only [fillerSum]
    rw [map_sum]
    calc
      (∑ ω ∈ fillers, φ (C ω)) = ∑ _ω ∈ fillers, β := by
        apply Finset.sum_congr rfl
        intro ω hω
        have hωnotE : ω ∉ E := by
          intro hωE
          exact Finset.disjoint_left.mp hfillersE hω hωE
        exact not_ne_iff.mp (not_congr (hExceptional ω) |>.mp hωnotE)
      _ = fillers.card • β := by simp
  have hmapBaseline : φ baseline = m • β := by
    dsimp only [baseline]
    rw [map_sum]
    have hleft : ∀ p : Fin k × Fin (q - 1),
        R.left p ∈ endpoints R := by
      intro p
      exact Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨p, Finset.mem_univ p, rfl⟩)
    simp_rw [hEndpoint _ (hleft _)]
    rw [Finset.sum_const]
    simp [m]
  have hoffsets :
      (∑ ω ∈ J, (φ (C ω) - β)) = φ exceptionalSum - J.card • β := by
    rw [Finset.sum_sub_distrib, hmapExceptional]
    simp
  have hyMap :
      φ y = φ exceptionalSum + fillers.card • β + m • β := by
    have hy := (sub_eq_iff_eq_add).mp hquotient
    rw [hoffsets] at hy
    rw [hy, hcardDecomp]
    simp only [add_nsmul]
    abel
  let z : V := y - exceptionalSum - fillerSum - baseline
  have hzKer : z ∈ LinearMap.ker φ := by
    rw [LinearMap.mem_ker]
    dsimp only [z]
    rw [map_sub, map_sub, map_sub, hmapFillers, hmapBaseline, hyMap]
    abel
  have hzSpan : z ∈ Submodule.span (ZMod q) (Set.range R.direction) := by
    rw [hspan]
    exact hzKer
  rcases (Submodule.mem_span_range_iff_exists_fun (ZMod q)).1 hzSpan with
    ⟨a, ha⟩
  obtain ⟨T, hT⟩ := exists_directionToggleSet_sum_eq R.direction a
  have hTz : (∑ p ∈ T, R.direction p.1) = z := hT.trans ha
  have htoggleSum :
      (∑ ω ∈ toggledSelection R T, C ω) = baseline + z := by
    rw [sum_toggledSelection_eq_directions R T, hTz]
  have htoggleFillers : Disjoint (toggledSelection R T) fillers := by
    exact (Finset.disjoint_of_subset_left
      (toggledSelection_subset_endpoints R T) hfillersEndpoint.symm)
  have hJtoggle : Disjoint J (toggledSelection R T) := by
    rw [Finset.disjoint_left]
    intro ω hωJ hωT
    have hωE := hJ hωJ
    have hωR := toggledSelection_subset_endpoints R T hωT
    exact Finset.disjoint_left.mp hEndpointE hωR hωE
  have hJrest : Disjoint J (toggledSelection R T ∪ fillers) :=
    Finset.disjoint_union_right.mpr ⟨hJtoggle, hJEdis⟩
  refine ⟨J ∪ (toggledSelection R T ∪ fillers), ?_, ?_⟩
  · rw [Finset.card_union_of_disjoint hJrest,
      Finset.card_union_of_disjoint htoggleFillers,
      card_toggledSelection R T]
    omega
  · rw [Finset.sum_union hJrest, Finset.sum_union htoggleFillers,
      htoggleSum]
    change exceptionalSum + (baseline + z + fillerSum) = y
    dsimp only [z]
    abel

/-- Complete labelled affine equivalence: an exact-`d` source selection with
sum `y` exists exactly when some labelled exceptional subset realizes the
quotient defect.  This combines the forward residue identity from M39 with
the reserved-label reverse construction above. -/
theorem fixedCardinality_sum_iff_exceptionalOffsetSubset
    (R : OccurrenceReservoir (F := ZMod q) C k (q - 1))
    (φ : V →ₗ[ZMod q] Q) (β : Q) (E : Finset Ω)
    (hExceptional : ∀ ω, ω ∈ E ↔ φ (C ω) ≠ β)
    (hEndpoint : ∀ ω ∈ endpoints R, φ (C ω) = β)
    (hspan : Submodule.span (ZMod q) (Set.range R.direction) = LinearMap.ker φ)
    (d : ℕ)
    (hbase : k * (q - 1) + E.card ≤ d)
    (hcapacity : d + k * (q - 1) + E.card ≤ Fintype.card Ω)
    (y : V) :
    (∃ I : Finset Ω, I.card = d ∧ (∑ ω ∈ I, C ω) = y) ↔
      ∃ J : Finset Ω, J ⊆ E ∧
        φ y - d • β = ∑ ω ∈ J, (φ (C ω) - β) := by
  classical
  constructor
  · rintro ⟨I, hIcard, hIsum⟩
    let J := I.filter fun ω => φ (C ω) ≠ β
    have hJ : J ⊆ E := by
      intro ω hω
      dsimp only [J] at hω
      have hfilter := Finset.mem_filter.mp hω
      exact (hExceptional ω).mpr hfilter.2
    refine ⟨J, hJ, ?_⟩
    have hfull :
        (∑ ω ∈ I, (φ (C ω) - β)) =
          ∑ ω ∈ J, (φ (C ω) - β) := by
      dsimp only [J]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro ω hω
      by_cases h : φ (C ω) ≠ β
      · simp [h]
      · simp [not_ne_iff.mp h]
    calc
      φ y - d • β = (∑ ω ∈ I, φ (C ω)) - I.card • β := by
        rw [hIcard, ← hIsum, map_sum]
      _ = ∑ ω ∈ J, (φ (C ω) - β) := by
        rw [← hfull, Finset.sum_sub_distrib]
        simp
  · rintro ⟨J, hJ, hquotient⟩
    exact exists_fixedCardinality_sum_of_exceptionalOffsets R φ β E J
      hExceptional hJ hEndpoint hspan d hbase hcapacity y hquotient

/-- Source-shaped affine-hyperplane certificate with no reservoir supplied by
the caller.  The independent-difference matching theorem constructs the
kernel reservoir from the heavy support, after which the exact labelled
equivalence follows from the preceding theorem. -/
theorem fixedCardinality_sum_iff_exceptionalOffsetSubset_of_heavySupport
    [FiniteDimensional (ZMod q) V]
    (C : Ω → V) (φ : V →ₗ[ZMod q] Q) (β : Q) (E : Finset Ω)
    (hvectorSpan :
      vectorSpan (ZMod q)
        ((thresholdSupport C (q - 1) : Finset V) : Set V) = LinearMap.ker φ)
    (hhalf : Module.finrank (ZMod q) (LinearMap.ker φ) ≤
      (thresholdSupport C (q - 1)).card / 2)
    (hfibre : ∀ x ∈ thresholdSupport C (q - 1), φ x = β)
    (htwo : (2 : ZMod q) ≠ 0)
    (hExceptional : ∀ ω, ω ∈ E ↔ φ (C ω) ≠ β)
    (d : ℕ)
    (hbase : Module.finrank (ZMod q) (LinearMap.ker φ) * (q - 1) + E.card ≤ d)
    (hcapacity : d + Module.finrank (ZMod q) (LinearMap.ker φ) * (q - 1) +
      E.card ≤ Fintype.card Ω)
    (y : V) :
    (∃ I : Finset Ω, I.card = d ∧ (∑ ω ∈ I, C ω) = y) ↔
      ∃ J : Finset Ω, J ⊆ E ∧
        φ y - d • β = ∑ ω ∈ J, (φ (C ω) - β) := by
  rcases exists_kernel_reservoir_of_heavySupport C φ β hvectorSpan hhalf
      hfibre htwo with ⟨R, hspan, hEndpoint⟩
  exact fixedCardinality_sum_iff_exceptionalOffsetSubset R φ β E
    hExceptional hEndpoint hspan d hbase hcapacity y

/-- Automatic affine-hyperplane certificate from the raw heavy-support
hypotheses.  In the proper affine-span branch this theorem chooses a base
point `α`, takes the canonical quotient by the affine direction, and defines
the exceptional occurrence labels exactly as those outside the resulting
affine fibre.  The caller supplies neither quotient data nor the exceptional
set. -/
theorem exists_affineHyperplaneCertificate_of_linearSpan_eq_top
    [FiniteDimensional (ZMod q) V]
    (C : Ω → V)
    (hS : (thresholdSupport C (q - 1)).Nonempty)
    (hlinear : Submodule.span (ZMod q)
      ((thresholdSupport C (q - 1) : Finset V) : Set V) = ⊤)
    (hproper : vectorSpan (ZMod q)
      ((thresholdSupport C (q - 1) : Finset V) : Set V) ≠ ⊤)
    (hhalf : Module.finrank (ZMod q)
      (vectorSpan (ZMod q)
        ((thresholdSupport C (q - 1) : Finset V) : Set V)) ≤
      (thresholdSupport C (q - 1)).card / 2)
    (htwo : (2 : ZMod q) ≠ 0) :
    ∃ α ∈ thresholdSupport C (q - 1),
      α ∉ vectorSpan (ZMod q)
        ((thresholdSupport C (q - 1) : Finset V) : Set V) ∧
      Module.finrank (ZMod q)
          (vectorSpan (ZMod q)
            ((thresholdSupport C (q - 1) : Finset V) : Set V)) + 1 =
        Module.finrank (ZMod q) V ∧
      (let W := vectorSpan (ZMod q)
          ((thresholdSupport C (q - 1) : Finset V) : Set V)
       let φ := W.mkQ
       let β := φ α
       ∃ E : Finset Ω,
         (∀ ω, ω ∈ E ↔ φ (C ω) ≠ β) ∧
         ∀ d,
           Module.finrank (ZMod q) W * (q - 1) + E.card ≤ d →
           d + Module.finrank (ZMod q) W * (q - 1) + E.card ≤
             Fintype.card Ω →
           ∀ y : V,
             (∃ I : Finset Ω, I.card = d ∧ (∑ ω ∈ I, C ω) = y) ↔
               ∃ J : Finset Ω, J ⊆ E ∧
                 φ y - d • β = ∑ ω ∈ J, (φ (C ω) - β)) := by
  classical
  let S := thresholdSupport C (q - 1)
  let W := vectorSpan (ZMod q) (S : Set V)
  rcases exists_affineHyperplaneGeometry_of_linearSpan_eq_top S hS hlinear hproper with
    ⟨α, hαS, hαnot, hdim, hdiff⟩
  refine ⟨α, hαS, hαnot, hdim, ?_⟩
  dsimp only
  let φ := W.mkQ
  let β := φ α
  let E := Finset.univ.filter fun ω => φ (C ω) ≠ β
  have hker : W = LinearMap.ker φ := by
    simpa [φ] using (Submodule.ker_mkQ W).symm
  have hfibre : ∀ x ∈ S, φ x = β := by
    intro x hx
    rw [← sub_eq_zero, ← map_sub]
    exact (LinearMap.mem_ker.mp (hker ▸ hdiff x hx))
  have hhalfKer : Module.finrank (ZMod q) (LinearMap.ker φ) ≤ S.card / 2 := by
    rw [← hker]
    exact hhalf
  have hExceptional : ∀ ω, ω ∈ E ↔ φ (C ω) ≠ β := by
    intro ω
    simp [E]
  refine ⟨E, hExceptional, ?_⟩
  intro d hbase hcapacity y
  have hbaseKer :
      Module.finrank (ZMod q) (LinearMap.ker φ) * (q - 1) + E.card ≤ d := by
    rw [← hker]
    exact hbase
  have hcapacityKer :
      d + Module.finrank (ZMod q) (LinearMap.ker φ) * (q - 1) + E.card ≤
        Fintype.card Ω := by
    rw [← hker]
    exact hcapacity
  exact fixedCardinality_sum_iff_exceptionalOffsetSubset_of_heavySupport
    C φ β E hker hhalfKer hfibre htwo hExceptional d hbaseKer hcapacityKer y

end OccurrenceReservoir

end GaoFormal

#print axioms GaoFormal.OccurrenceReservoir.exists_fixedCardinality_sum_of_exceptionalOffsets
#print axioms GaoFormal.OccurrenceReservoir.exists_fixedCardinality_sum_of_fullHeavySupport
#print axioms GaoFormal.OccurrenceReservoir.exists_affineHyperplaneGeometry_of_linearSpan_eq_top
#print axioms GaoFormal.OccurrenceReservoir.fixedCardinality_sum_iff_exceptionalOffsetSubset
#print axioms GaoFormal.OccurrenceReservoir.exists_kernel_reservoir_of_heavySupport
#print axioms GaoFormal.OccurrenceReservoir.fixedCardinality_sum_iff_exceptionalOffsetSubset_of_heavySupport
#print axioms GaoFormal.OccurrenceReservoir.exists_affineHyperplaneCertificate_of_linearSpan_eq_top
