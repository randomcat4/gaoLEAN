import GaoLean.GAOARStatements

/-!
# Additive subgroups of the rank-two prime vector space

Every additive subgroup of `(ZMod q)^2` is automatically a `ZMod q`-linear
subspace.  This file packages that elementary fact and derives the only
classification data used by the rank-two line branch: a nonzero proper
subgroup has cardinality `q`.
-/

namespace GaoLean

/-- An additive subgroup of a prime-vector space is closed under field
scalars because every scalar is represented by a natural multiple. -/
def addSubgroupAsZModSubmodule
    (q : ℕ) [NeZero q]
    (K : AddSubgroup (Fin 2 → ZMod q)) :
    Submodule (ZMod q) (Fin 2 → ZMod q) where
  carrier := K
  zero_mem' := K.zero_mem
  add_mem' := K.add_mem
  smul_mem' := by
    intro c x hx
    rw [← ZMod.natCast_zmod_val c, Nat.cast_smul_eq_nsmul]
    exact K.nsmul_mem hx c.val

theorem natCard_addSubgroupAsZModSubmodule
    (q : ℕ) [NeZero q]
    (K : AddSubgroup (Fin 2 → ZMod q)) :
    Nat.card K = Nat.card (addSubgroupAsZModSubmodule q K) := by
  apply Nat.card_congr
  exact {
    toFun := fun x => ⟨x.1, x.2⟩
    invFun := fun x => ⟨x.1, x.2⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl
  }

/-- A nonzero proper additive subgroup of `F_q²` is a line.  The conclusion
is stated only as the cardinality fact needed downstream, avoiding any choice
of basis or coordinate normalization. -/
theorem natCard_eq_prime_of_ne_bot_of_lt_top_rankTwo
    (q : ℕ) [NeZero q] (hq : Nat.Prime q)
    (K : AddSubgroup (Fin 2 → ZMod q))
    (hKbot : K ≠ ⊥) (hKtop : K < ⊤) :
    Nat.card K = q := by
  letI : Fact (Nat.Prime q) := ⟨hq⟩
  let L := addSubgroupAsZModSubmodule q K
  have hLbot : L ≠ ⊥ := by
    intro h
    apply hKbot
    ext x
    have hx := SetLike.ext_iff.mp h x
    simpa [L, addSubgroupAsZModSubmodule] using hx
  have hLtop : L ≠ ⊤ := by
    intro h
    apply hKtop.ne
    ext x
    have hx := SetLike.ext_iff.mp h x
    simpa [L, addSubgroupAsZModSubmodule] using hx
  have hpos : 0 < Module.finrank (ZMod q) L := by
    have h := Submodule.finrank_lt_finrank_of_lt
      (bot_lt_iff_ne_bot.mpr hLbot)
    simpa using h
  have hlt : Module.finrank (ZMod q) L < 2 := by
    have h := Submodule.finrank_lt hLtop
    simpa [L] using h
  have hfin : Module.finrank (ZMod q) L = 1 := by omega
  rw [natCard_addSubgroupAsZModSubmodule q K]
  rw [Module.natCard_eq_pow_finrank (K := ZMod q), hfin]
  simp

/-- Consequently the quotient by a nonzero proper rank-two subgroup also has
prime cardinality `q`. -/
theorem natCard_quotient_eq_prime_of_ne_bot_of_lt_top_rankTwo
    (q : ℕ) [NeZero q] (hq : Nat.Prime q)
    (K : AddSubgroup (Fin 2 → ZMod q))
    (hKbot : K ≠ ⊥) (hKtop : K < ⊤) :
    Nat.card ((Fin 2 → ZMod q) ⧸ K) = q := by
  have hcard := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
  rw [natCard_eq_prime_of_ne_bot_of_lt_top_rankTwo q hq K hKbot hKtop] at hcard
  have hambient : Nat.card (Fin 2 → ZMod q) = q ^ 2 := by simp
  rw [hambient] at hcard
  exact Nat.mul_right_cancel hq.pos (by simpa [pow_two] using hcard.symm)

end GaoLean

#print axioms GaoLean.natCard_eq_prime_of_ne_bot_of_lt_top_rankTwo
#print axioms GaoLean.natCard_quotient_eq_prime_of_ne_bot_of_lt_top_rankTwo
