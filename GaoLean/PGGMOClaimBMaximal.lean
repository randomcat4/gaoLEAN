import GaoLean.PGGMOClaimBCase1

/-!
# Maximal ordinary GMO Claim-B witnesses

This module performs the finite maximal-subgroup choice used after ordinary
Claim B.  The maximized objects are the genuine occurrence-faithful witnesses
`OrdinaryGMOClaimBOutput`; no replacement data and no saturation property is
reconstructed.  We maximize only the finite cardinality of the witness
subgroup, so the chosen witness retains its original center, partition,
saturation equality, and remaining-occurrence ledger definitionally.

At the top-subgroup endpoint the existing saturation equality immediately
makes the selected partition sumset the whole ambient group.  Turning that
partition into a `GMOTheorem21LargeAlternative` would additionally require
the interface equalities `pGroupDStar K = n` and `supportCard = seed.card`,
which are intentionally not fields of `OrdinaryGMOClaimBOutput`.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A subgroup of a finite ambient group has at most the ambient cardinality.
This explicit bound lets us maximize witness subgroup sizes in a finite
natural-number range without asking for a computable finite enumeration of
the proof-carrying witness type. -/
theorem natCard_addSubgroup_le_ambient (K : AddSubgroup A) :
    Nat.card K ≤ Nat.card A :=
  Nat.card_le_card_of_injective (fun x : K ↦ (x.1 : A))
    (fun x y hxy ↦ Subtype.ext hxy)

/-- From any genuine Claim-B witness, choose a genuine witness whose subgroup
has maximum cardinality among all Claim-B witnesses for the same source data.
The returned object is an original witness, rather than a record rebuilt from
its fields. -/
theorem exists_card_maximal_ordinaryGMOClaimBOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (hne : Nonempty (OrdinaryGMOClaimBOutput xs seed n)) :
    ∃ Wmax : OrdinaryGMOClaimBOutput xs seed n,
      ∀ W : OrdinaryGMOClaimBOutput xs seed n,
        Nat.card W.K ≤ Nat.card Wmax.K := by
  classical
  let cards : Finset ℕ :=
    (Finset.range (Nat.card A + 1)).filter fun c ↦
      ∃ W : OrdinaryGMOClaimBOutput xs seed n, Nat.card W.K = c
  have hmem (W : OrdinaryGMOClaimBOutput xs seed n) :
      Nat.card W.K ∈ cards := by
    apply Finset.mem_filter.mpr
    refine ⟨?_, ⟨W, rfl⟩⟩
    rw [Finset.mem_range]
    exact Nat.lt_succ_of_le (natCard_addSubgroup_le_ambient W.K)
  obtain ⟨W₀⟩ := hne
  have hcards : cards.Nonempty := ⟨Nat.card W₀.K, hmem W₀⟩
  obtain ⟨c, hc, hcmax⟩ :=
    Finset.exists_max_image cards (fun q ↦ q) hcards
  obtain ⟨Wmax, hWmax⟩ :
      ∃ W : OrdinaryGMOClaimBOutput xs seed n, Nat.card W.K = c :=
    (Finset.mem_filter.mp hc).2
  refine ⟨Wmax, ?_⟩
  intro W
  have hle : Nat.card W.K ≤ c := by
    simpa using hcmax (Nat.card W.K) (hmem W)
  exact hle.trans_eq hWmax.symm

/-- Cardinal maximality rules out strict enlargement by the subgroup of any
other genuine Claim-B witness. -/
theorem OrdinaryGMOClaimBOutput.not_subgroup_lt_of_card_maximal
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (Wmax : OrdinaryGMOClaimBOutput xs seed n)
    (hmax : ∀ W : OrdinaryGMOClaimBOutput xs seed n,
      Nat.card W.K ≤ Nat.card Wmax.K)
    (W : OrdinaryGMOClaimBOutput xs seed n) :
    ¬ Wmax.K < W.K := by
  intro hlt
  have hcardlt : Nat.card Wmax.K < Nat.card W.K :=
    natCard_lt_of_addSubgroup_lt hlt
  exact (Nat.not_lt_of_ge (hmax W)) hcardlt

/-- Combined selection form: a nonempty Claim-B witness type contains a
witness whose subgroup cannot be strictly enlarged by any other witness. -/
theorem exists_subgroup_maximal_ordinaryGMOClaimBOutput
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (hne : Nonempty (OrdinaryGMOClaimBOutput xs seed n)) :
    ∃ Wmax : OrdinaryGMOClaimBOutput xs seed n,
      (∀ W : OrdinaryGMOClaimBOutput xs seed n,
        Nat.card W.K ≤ Nat.card Wmax.K) ∧
      (∀ W : OrdinaryGMOClaimBOutput xs seed n, ¬ Wmax.K < W.K) := by
  obtain ⟨Wmax, hmax⟩ :=
    exists_card_maximal_ordinaryGMOClaimBOutput hne
  exact ⟨Wmax, hmax, fun W ↦ Wmax.not_subgroup_lt_of_card_maximal hmax W⟩

/-- If a genuine Claim-B witness uses the top subgroup, its retained
saturation equality is literally the full ambient sumset. -/
theorem OrdinaryGMOClaimBOutput.sumset_eq_univ_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (hK : W.K = ⊤) :
    W.partition.sumset = Finset.univ := by
  classical
  rw [W.saturation, hK]
  ext x
  simp [mem_addCosetFinset_iff]

/-- Cardinal form of the top-subgroup endpoint. -/
theorem OrdinaryGMOClaimBOutput.card_sumset_eq_natCard_of_K_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (hK : W.K = ⊤) :
    W.partition.sumset.card = Nat.card A := by
  rw [W.sumset_eq_univ_of_K_eq_top hK, Finset.card_univ]
  exact Nat.card_eq_fintype_card.symm

end GaoLean

#print axioms GaoLean.exists_card_maximal_ordinaryGMOClaimBOutput
#print axioms GaoLean.OrdinaryGMOClaimBOutput.not_subgroup_lt_of_card_maximal
#print axioms GaoLean.exists_subgroup_maximal_ordinaryGMOClaimBOutput
#print axioms GaoLean.OrdinaryGMOClaimBOutput.sumset_eq_univ_of_K_eq_top
