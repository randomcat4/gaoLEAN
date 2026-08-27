import GaoLean.GAOARFinal

/-!
# Frozen 13-page gao0824 PR #7 theorem

This file identifies the exact paper being audited:

* repository: `randomcat4/gao0824`;
* pull request: `#7`, `paper/arxiv-rewrite-2026-08-24`;
* audited head: `6d4ab81b14f49aaa61d7aeb8c02182f1259a736b`;
* manuscript: the 13-page arXiv source under `paper/arxiv`.

The paper's core statement is precisely the p-group statement already frozen
as `PGGaoV1Statement`: for every nontrivial finite abelian p-group of odd
prime characteristic and every exact ordinary Davenport value `D`, the exact
Gao threshold is `2 * |A| + D`, with an occurrence-labelled block of literal
cardinality `2 * |A|`.

The displayed invariant-factor formula is now proved internally through
Olson's theorem.  The equality with the small Davenport constant is also
proved internally, by an occurrence-labelled path-boundary proof of the
Godara--Joshi--Mazumdar theorem.  The remaining source boundary is GMO.
-/

namespace GaoLean

universe u

/-- Exact core theorem stated by the 13-page `gao0824` PR #7 manuscript. -/
def PR7ThirteenPageMainStatement : Prop :=
  PGGaoV1Statement.{u}

namespace ConcreteGDihedral

/-- Checked conditional assembly of the exact 13-page paper statement.

The premise is deliberately visible.  It includes all source-facing
statements that have not yet been proved locally, so the result has status
`LEAN_CONDITIONAL`, not `LEAN_FULLY_CHECKED`. -/
theorem pr7ThirteenPageMain_of_remainingInputs
    (hremaining : PGGaoStructuralRemainingInputs.{u}) :
    PR7ThirteenPageMainStatement.{u} := by
  exact pgGaoV1Statement_of_structuralRemainingInputs hremaining

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.ConcreteGDihedral.pr7ThirteenPageMain_of_remainingInputs
