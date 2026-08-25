import GaoLean.PGStatements

/-!
# Frozen arbitrary-rank Gao statement

This file freezes the exact theorem stated in the GAO23-A-R3 manuscript.
It introduces no mathematical premise and proves no upper bound.  In
particular, compiling the definition `GAOARV1Statement` is not evidence that
the proposition has been proved.
-/

namespace GaoLean

universe u

/-- The additive group `C_q^r`, represented with labelled coordinates. -/
abbrev PrimeVectorSpace (q r : ℕ) := Fin r → ZMod q

/-- The generalized-dihedral group `(C_q^r) ⋊_{-1} C₂`. -/
abbrev PrimeVectorDihedral (q r : ℕ) :=
  ConcreteGDihedral.Group (PrimeVectorSpace q r)

/-- The proposed exact threshold from the frozen manuscript.  The selected
block has the literal cardinality `2 * q^r`; occurrence labels are inherited
from `IsExactProductOneThreshold`. -/
def GAOARV1 (q r : ℕ) : Prop :=
  IsExactProductOneThreshold (PrimeVectorDihedral q r)
    (2 * q ^ r + r * (q - 1) + 1) (2 * q ^ r)

/-- Fully quantified frozen statement `GAO-AR-v1`.  Oddness is expressed as
`q.Prime` together with `q ≠ 2`, and the manuscript range is exactly `r ≥ 2`.
No proof term of this proposition is supplied in the statement layer. -/
def GAOARV1Statement : Prop :=
  ∀ q r : ℕ, q.Prime → q ≠ 2 → 2 ≤ r → GAOARV1 q r

/-- Cardinality check connecting the explicit target length in `GAOARV1`
to the order of the represented generalized-dihedral group. -/
theorem card_primeVectorDihedral
    (q r : ℕ) [NeZero q] :
    Fintype.card (PrimeVectorDihedral q r) = 2 * q ^ r := by
  simp [PrimeVectorDihedral, PrimeVectorSpace,
    ConcreteGDihedral.Group, Nat.mul_comm]

end GaoLean

#print axioms GaoLean.card_primeVectorDihedral
