import GaoLean.ConcreteGDihedral
import GaoLean.PlusMinus
import Mathlib.GroupTheory.PGroup

/-!
# Frozen p-group Gao statements

These definitions freeze statement shapes only.  They do not assert Olson,
GJM, GMO, Troi--Zannier, or the final generalized-dihedral Gao equality.
-/

namespace GaoLean

universe u

/-- A nonempty occurrence-labelled ordinary zero-sum subsequence. -/
def HasNonemptyZeroSum {A : Type*} [AddCommGroup A] (s : List A) : Prop :=
  ∃ I : Selection s, I.Nonempty ∧
    ∑ i ∈ I, occurrenceValue s i = 0

/-- Threshold formulation of `D(A) ≤ D`. -/
def OrdinaryDavenportAtMost (A : Type*) [AddCommGroup A] (D : ℕ) : Prop :=
  ∀ s : List A, s.length = D → HasNonemptyZeroSum s

/-- Exact occurrence-sensitive definition of a proposed ordinary Davenport
value: the upper property holds at `D`, and fails for some sequence at
`D - 1`. -/
def IsOrdinaryDavenportConstant (A : Type*) [AddCommGroup A] (D : ℕ) : Prop :=
  OrdinaryDavenportAtMost A D ∧
    ∀ n : ℕ, n < D →
      ∃ s : List A, s.length = n ∧ ¬HasNonemptyZeroSum s

/-- Every source sequence of length `N` has an exact `k`-occurrence
product-one subsequence. -/
def HasExactProductOneBlockAtLength (G : Type*) [Group G] (N k : ℕ) : Prop :=
  ∀ s : List G, s.length = N → HasProductOneSubsequenceOfCard s k

/-- Paper-facing monotone form: every source sequence of length at least
`N` has an exact `k`-occurrence product-one subsequence. -/
def HasExactProductOneBlockAtLeast (G : Type*) [Group G] (N k : ℕ) : Prop :=
  ∀ s : List G, N ≤ s.length → HasProductOneSubsequenceOfCard s k

/-- An exact product-one block selected from a prefix remains the same
occurrence-labelled block in the full source sequence. -/
theorem hasProductOneSubsequenceOfCard_of_take
    {G : Type*} [Group G] (s : List G) (N k : ℕ)
    (hN : N ≤ s.length)
    (hblock : HasProductOneSubsequenceOfCard (s.take N) k) :
    HasProductOneSubsequenceOfCard s k := by
  classical
  rcases hblock with ⟨I, hIcard, hIprod⟩
  let emb : Occurrence (s.take N) ↪ Occurrence s :=
    { toFun := fun i =>
        ⟨i.1, lt_of_lt_of_le i.2
          ((List.length_take_le N s).trans hN)⟩
      inj' := by
        intro i j hij
        apply Fin.ext
        exact congrArg (fun x : Occurrence s => x.val) hij }
  let J : Selection s := I.map emb
  have hvalue (i : Occurrence (s.take N)) :
      occurrenceValue s (emb i) = occurrenceValue (s.take N) i := by
    simp [occurrenceValue, emb, List.get_eq_getElem]
  have hselected :
      selectedMultiset s J = selectedMultiset (s.take N) I := by
    simp [selectedMultiset, J, hvalue]
  refine ⟨J, ?_, ?_⟩
  · simpa [J] using hIcard
  · rw [IsProductOneSelection, hselected]
    exact hIprod

/-- The upper property at the exact threshold automatically extends to all
longer source sequences by selecting from their first `N` occurrences. -/
theorem hasExactProductOneBlockAtLeast_of_atLength
    {G : Type*} [Group G] {N k : ℕ}
    (h : HasExactProductOneBlockAtLength G N k) :
    HasExactProductOneBlockAtLeast G N k := by
  intro s hN
  apply hasProductOneSubsequenceOfCard_of_take s N k hN
  apply h (s.take N)
  simp [List.length_take, Nat.min_eq_left hN]

/-- The exact threshold certificate used to express a Gao constant without
silently importing a pre-existing constant definition: the upper property
holds at `N`, and a counterexample exists at `N - 1`. -/
def IsExactProductOneThreshold (G : Type*) [Group G] (N k : ℕ) : Prop :=
  HasExactProductOneBlockAtLength G N k ∧
    ∀ n : ℕ, n < N →
      ∃ s : List G, s.length = n ∧
        ¬HasProductOneSubsequenceOfCard s k

/-- The threshold in the manuscript's literal “all lengths at least `N`”
form, with counterexamples at every smaller length. -/
def IsAtLeastProductOneThreshold (G : Type*) [Group G] (N k : ℕ) : Prop :=
  HasExactProductOneBlockAtLeast G N k ∧
    ∀ n : ℕ, n < N →
      ∃ s : List G, s.length = n ∧
        ¬HasProductOneSubsequenceOfCard s k

/-- The exact-length threshold certificate used internally is equivalent to
the paper's monotone definition. -/
theorem isExactProductOneThreshold_iff_isAtLeast
    {G : Type*} [Group G] {N k : ℕ} :
    IsExactProductOneThreshold G N k ↔
      IsAtLeastProductOneThreshold G N k := by
  constructor
  · intro h
    exact ⟨hasExactProductOneBlockAtLeast_of_atLength h.1, h.2⟩
  · intro h
    refine ⟨?_, h.2⟩
    intro s hs
    exact h.1 s (by omega)

/-- Frozen Lean statement `PG-GAO-v1` for a proposed Davenport value `D`.
The external mathematical package must later identify `D` with `D(A)` and
prove the two conjuncts. -/
def PGGaoV1 (A : Type*) [AddCommGroup A] [Fintype A] (D : ℕ) : Prop :=
  IsExactProductOneThreshold (ConcreteGDihedral.Group A)
    (2 * Fintype.card A + D) (2 * Fintype.card A)

/-- Frozen Lean statement `PG-PM-v1` at a proposed Davenport value `D`.
Oddness of `D(A)` is deliberately kept separate from this threshold statement. -/
def PGPMV1 (A : Type*) [AddCommGroup A] (D : ℕ) : Prop :=
  PlusMinusDavenportAtMost A ((D + 1) / 2)

/-- Fully quantified frozen statement `(A) PG-GAO-v1`.  This is
`STATEMENT_ONLY`: no proof term of this proposition is provided. -/
def PGGaoV1Statement : Prop :=
  ∀ (p : ℕ) (A : Type u),
    [AddCommGroup A] → [Fintype A] → [Nontrivial A] →
    p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ D : ℕ, IsOrdinaryDavenportConstant A D → PGGaoV1 A D

/-- Fully quantified frozen statement `(B) PG-PM-v1`.  Its compiled
conditional realization is `pg_pm_v1_of_restrictedCoefficientOutput`; the
external restricted-coefficient existence theorem is not asserted here. -/
def PGPMV1Statement : Prop :=
  ∀ (p : ℕ) (A : Type u),
    [AddCommGroup A] → [Fintype A] → [Nontrivial A] →
    p.Prime → p ≠ 2 → IsPGroup p (Multiplicative A) →
    ∀ D : ℕ, IsOrdinaryDavenportConstant A D → PGPMV1 A D

end GaoLean

#print axioms GaoLean.hasProductOneSubsequenceOfCard_of_take
#print axioms GaoLean.hasExactProductOneBlockAtLeast_of_atLength
#print axioms GaoLean.isExactProductOneThreshold_iff_isAtLeast
