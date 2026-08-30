import GaoLean.PGGaoOrdinaryComplete

/-!
# Gao's theorem for odd-primary generalized dihedral groups

This module provides the stable, mathematically named public entry point for
the fully assembled theorem. The historical assembly names remain available
for provenance, but downstream users should import this module and use
`gaoGeneralizedDihedralOddPGroup`.
-/

namespace GaoLean.ConcreteGDihedral

/-- The exact Gao theorem for generalized dihedral groups whose rotation
subgroup is a finite abelian odd-prime `p`-group.

This is the stable public alias of the fully unconditional theorem assembled
from the ordinary Gao--Mori--Ohno input and the manuscript bridge. -/
theorem gaoGeneralizedDihedralOddPGroup :
    PR7ThirteenPageMainStatement.{u} :=
  pr7ThirteenPageMain

end GaoLean.ConcreteGDihedral
