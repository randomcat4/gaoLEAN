import GaoLean.PGStatements

/-!
# Numerical consequences of the odd-prime p-group hypothesis

This module isolates the elementary cardinality parity edge used by the
frozen PG-GAO statement.
-/

namespace GaoLean

/-- A finite `p`-group for an odd prime has odd cardinality. -/
theorem odd_natCard_of_odd_prime_pgroup
    (p : ℕ) (A : Type*) [AddCommGroup A] [Fintype A]
    (hp : p.Prime) (hpne : p ≠ 2)
    (hgroup : IsPGroup p (Multiplicative A)) :
    Odd (Nat.card A) := by
  letI : Fact p.Prime := ⟨hp⟩
  rcases IsPGroup.iff_card.mp hgroup with ⟨n, hcard⟩
  have hpodd : Odd p := hp.odd_of_ne_two hpne
  have hpow : Odd (p ^ n) := hpodd.pow
  rw [show Nat.card A = p ^ n by simpa using hcard]
  exact hpow

end GaoLean

#print axioms GaoLean.odd_natCard_of_odd_prime_pgroup
