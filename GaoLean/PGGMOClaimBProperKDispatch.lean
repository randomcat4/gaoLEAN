import GaoLean.PGGMOClaimBHighMultiplicityEnlarge
import GaoLean.PGGMOClaimBQuotientRecursiveInput

/-!
# Proper-K dispatch for a cardinal-maximal plain Claim-B witness

For a cardinal-maximal genuine Claim-B witness with proper subgroup `K`, a
nonzero quotient fiber cannot reach the high-multiplicity threshold
`d*(A/K)`: the verified high-multiplicity construction would produce a
strictly larger plain witness.  Negating that branch gives the exact strict
low-multiplicity condition on every nonzero source fiber.

The quotient-position fibers are then identified with the source-occurrence
fibers away from zero.  Together with a direct zero-capacity estimate, this
feeds the existing generic padded-quotient API at the same honest threshold
`d*(A/K)`.  No envelope, provider, or historical induction hypothesis is
used here.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A high nonzero source fiber would construct a strict enlargement and
contradict cardinal maximality of the original plain witness. -/
theorem OrdinaryGMOClaimBOutput.not_exists_highMultiplicityFiber_of_card_maximal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hmax : ∀ W' : OrdinaryGMOClaimBOutput xs seed n,
      Nat.card W'.K ≤ Nat.card W.K)
    (hproper : W.K < ⊤) (hambient : pGroupDStar A ≤ n) :
    ¬ ∃ z : A ⧸ W.K, z ≠ 0 ∧
      pGroupDStar (A ⧸ W.K) ≤ (W.sourceQuotientFiber z).card := by
  rintro ⟨z, hz, hhigh⟩
  let D : OrdinaryGMOClaimBHighMultiplicityCore W z :=
    Classical.choice
      (exists_ordinaryGMOClaimBHighMultiplicityCore W hproper.ne hambient z hz hhigh)
  have hnL : W.highMultiplicityExtensionLength z ≤ n := by
    simpa only [OrdinaryGMOClaimBOutput.highMultiplicityExtensionLength] using
      pGroupDStar_addSubgroup_le_of_ambient_le
        (W.highMultiplicityExtensionSubgroup z) hambient
  let M : OrdinaryGMOClaimBHighMultiplicityAssemblyData D :=
    Classical.choice
      (exists_ordinaryGMOClaimBHighMultiplicityAssemblyData D hnL)
  exact M.not_card_maximal hambient hmax

/-- The logical complement of the impossible high branch is strict low
multiplicity on every nonzero labelled source fiber. -/
theorem OrdinaryGMOClaimBOutput.sourceQuotientFiber_lt_quotientDStar_of_card_maximal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hmax : ∀ W' : OrdinaryGMOClaimBOutput xs seed n,
      Nat.card W'.K ≤ Nat.card W.K)
    (hproper : W.K < ⊤) (hambient : pGroupDStar A ≤ n) :
    ∀ z : A ⧸ W.K, z ≠ 0 →
      (W.sourceQuotientFiber z).card < pGroupDStar (A ⧸ W.K) := by
  intro z hz
  apply Nat.lt_of_not_ge
  intro hhigh
  exact W.not_exists_highMultiplicityFiber_of_card_maximal
    hmax hproper hambient ⟨z, hz, hhigh⟩

/-- Away from zero, quotient-sequence positions enumerate exactly the same
labelled source occurrences as the centered source fiber.  The nonzero
hypothesis is what excludes every support occurrence. -/
theorem OrdinaryGMOClaimBOutput.map_quotientFiber_eq_sourceQuotientFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (z : A ⧸ W.K) (hz : z ≠ 0) :
    (W.quotientFiber z).map W.quotientSourceEmbedding =
      W.sourceQuotientFiber z := by
  classical
  ext i
  constructor
  · intro hi
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hi
    apply (W.mem_sourceQuotientFiber_iff z _).2
    change W.quotientDisplacement (W.quotientSourceOccurrence q) = z
    rw [← W.occurrenceValue_quotientDisplacementSequence q]
    exact (W.mem_quotientFiber_iff z q).1 hq
  · intro hi
    have hiEq : W.centeredQuotientValue i = z :=
      (W.mem_sourceQuotientFiber_iff z i).1 hi
    have hiNotSupport : i ∉ W.partition.support := by
      intro hiSupport
      have hiCoset := W.support_in_coset i hiSupport
      have hiZero : W.centeredQuotientValue i = 0 := by
        exact (QuotientAddGroup.eq_zero_iff _).2
          ((mem_addCosetFinset_iff W.K W.g _).1 hiCoset)
      exact hz (hiEq.symm.trans hiZero)
    have hiRemaining : i ∈ W.remainingOccurrences :=
      (W.mem_remainingOccurrences_iff i).2 hiNotSupport
    have hiRange : i ∈
        (Finset.univ : Selection W.quotientDisplacementSequence).map
          W.quotientSourceEmbedding := by
      rw [W.map_univ_quotientSourceEmbedding]
      exact hiRemaining
    obtain ⟨q, -, hqi⟩ := Finset.mem_map.mp hiRange
    apply Finset.mem_map.mpr
    refine ⟨q, ?_, hqi⟩
    apply (W.mem_quotientFiber_iff z q).2
    rw [W.occurrenceValue_quotientDisplacementSequence q]
    change W.centeredQuotientValue (W.quotientSourceEmbedding q) = z
    rw [hqi]
    exact hiEq

/-- Hence nonzero quotient-position fibers and source-occurrence fibers have
the same cardinality, without collapsing repeated values. -/
theorem OrdinaryGMOClaimBOutput.card_quotientFiber_eq_card_sourceQuotientFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (z : A ⧸ W.K) (hz : z ≠ 0) :
    (W.quotientFiber z).card = (W.sourceQuotientFiber z).card := by
  have hcard := congrArg Finset.card
    (W.map_quotientFiber_eq_sourceQuotientFiber z hz)
  simpa using hcard

/-- The strict source-fiber bound transfers verbatim to genuine quotient
positions. -/
theorem OrdinaryGMOClaimBOutput.quotientFiber_lt_quotientDStar_of_card_maximal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hmax : ∀ W' : OrdinaryGMOClaimBOutput xs seed n,
      Nat.card W'.K ≤ Nat.card W.K)
    (hproper : W.K < ⊤) (hambient : pGroupDStar A ≤ n) :
    ∀ z : A ⧸ W.K, z ≠ 0 →
      (W.quotientFiber z).card < pGroupDStar (A ⧸ W.K) := by
  intro z hz
  rw [W.card_quotientFiber_eq_card_sourceQuotientFiber z hz]
  exact W.sourceQuotientFiber_lt_quotientDStar_of_card_maximal
    hmax hproper hambient z hz

/-- The weak form consumed by the generic padded-quotient multiplicity API. -/
theorem OrdinaryGMOClaimBOutput.quotientFiber_le_quotientDStar_of_card_maximal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hmax : ∀ W' : OrdinaryGMOClaimBOutput xs seed n,
      Nat.card W'.K ≤ Nat.card W.K)
    (hproper : W.K < ⊤) (hambient : pGroupDStar A ≤ n) :
    ∀ z : A ⧸ W.K, z ≠ 0 →
      (W.quotientFiber z).card ≤ pGroupDStar (A ⧸ W.K) := by
  intro z hz
  exact Nat.le_of_lt
    (W.quotientFiber_lt_quotientDStar_of_card_maximal
      hmax hproper hambient z hz)

/-- Canonical subgroup--quotient subadditivity and the ambient `d*` budget
place the two Claim-B budgets inside `n`.  The ordinary remaining ledger then
supplies enough genuine zero quotient positions for quotient-star padding. -/
theorem OrdinaryGMOClaimBOutput.quotientDStar_le_zeroQuotientFiber
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hambient : pGroupDStar A ≤ n) :
    pGroupDStar (A ⧸ W.K) ≤ (W.quotientFiber 0).card := by
  have hbudgets : pGroupDStar (A ⧸ W.K) + pGroupDStar W.K ≤ n :=
    by
      have hconv := pGroupDStar_subgroup_quotient_le W.K
      omega
  have hdQSub : pGroupDStar (A ⧸ W.K) ≤ n - pGroupDStar W.K :=
    Nat.le_sub_of_add_le hbudgets
  calc
    pGroupDStar (A ⧸ W.K) ≤ n - pGroupDStar W.K := hdQSub
    _ ≤ n - pGroupDStar W.K + (xs.length - seed.card) :=
      Nat.le_add_right _ _
    _ ≤ (W.quotientFiber 0).card := W.zeroQuotientFiber_lower

/-- The proper, cardinal-maximal plain witness therefore supplies the complete
honest recursive quotient input at the canonical quotient threshold
`dQ = d*(A/K)`. -/
theorem OrdinaryGMOClaimBOutput.nonempty_quotientRecursiveInput_of_card_maximal
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n)
    (hmax : ∀ W' : OrdinaryGMOClaimBOutput xs seed n,
      Nat.card W'.K ≤ Nat.card W.K)
    (hproper : W.K < ⊤) (hambient : pGroupDStar A ≤ n) :
    Nonempty (OrdinaryGMOClaimBQuotientRecursiveInput p W) := by
  let hzero := W.quotientDStar_le_zeroQuotientFiber hambient
  have hlow : ∀ z : A ⧸ W.K, z ≠ 0 →
      (W.quotientFiber z).card ≤ pGroupDStar (A ⧸ W.K) :=
    W.quotientFiber_le_quotientDStar_of_card_maximal
      hmax hproper hambient
  exact W.nonempty_quotientRecursiveInput
    p hp hpTwo hA hproper hambient hzero hlow

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBOutput.not_exists_highMultiplicityFiber_of_card_maximal
#print axioms GaoLean.OrdinaryGMOClaimBOutput.sourceQuotientFiber_lt_quotientDStar_of_card_maximal
#print axioms GaoLean.OrdinaryGMOClaimBOutput.map_quotientFiber_eq_sourceQuotientFiber
#print axioms GaoLean.OrdinaryGMOClaimBOutput.quotientFiber_lt_quotientDStar_of_card_maximal
#print axioms GaoLean.OrdinaryGMOClaimBOutput.quotientDStar_le_zeroQuotientFiber
#print axioms GaoLean.OrdinaryGMOClaimBOutput.nonempty_quotientRecursiveInput_of_card_maximal
