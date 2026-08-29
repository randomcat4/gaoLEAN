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

The displayed invariant-factor formula is proved internally through Olson's
theorem.  The equality with the small Davenport constant is also proved
internally, by an occurrence-labelled path-boundary proof of the
Godara--Joshi--Mazumdar theorem.  The ordinary `W={1}` and signed `W={+1,-1}`
GMO specializations used by the main proof are discharged unconditionally in
later modules, culminating in `ConcreteGDihedral.pr7ThirteenPageMain`.

This frozen core is deliberately narrower than a line-by-line formalization
of every auxiliary manuscript theorem.  In particular, the source form of
Theorem 2.2 quantifies over an arbitrary nonempty integer weight set `W`, and
its structural clause assumes `gcd(W)=1`.  That full general-weight statement
is not represented by this definition or by the two special-purpose
providers.  Thus the main Gao theorem is unconditional, while the manuscript
as a whole remains only partially verified until that source range is added.
-/

namespace GaoLean

universe u

/-- Exact core theorem stated by the 13-page `gao0824` PR #7 manuscript. -/
def PR7ThirteenPageMainStatement : Prop :=
  PGGaoV1Statement.{u}

namespace ConcreteGDihedral

/-- Historical conditional assembly of the exact 13-page main statement.

The premise is deliberately visible.  This theorem remains useful as a
layered API and records the former proof boundary.  It must not be read as the
current final status: `PGGaoOrdinaryComplete` later supplies the remaining
specialized providers and proves `ConcreteGDihedral.pr7ThirteenPageMain`
without this premise.  Conversely, that unconditional main endpoint does not
by itself formalize Theorem 2.2 for arbitrary integer weight sets. -/
theorem pr7ThirteenPageMain_of_remainingInputs
    (hremaining : PGGaoStructuralRemainingInputs.{u}) :
    PR7ThirteenPageMainStatement.{u} := by
  exact pgGaoV1Statement_of_structuralRemainingInputs hremaining

end ConcreteGDihedral
end GaoLean

#print axioms GaoLean.ConcreteGDihedral.pr7ThirteenPageMain_of_remainingInputs
