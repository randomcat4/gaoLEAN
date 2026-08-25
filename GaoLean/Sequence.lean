import Mathlib

/-!
# Occurrence-faithful sequence semantics

Zero-sum and product-one arguments work with *occurrences*, not merely with
the set of values appearing in a sequence.  In this file an occurrence of a
list `s` is a position `Fin s.length`.  Thus two equal entries at different
positions remain distinct throughout selection.

For a noncommutative monoid, a selected multiset is product-one when there is
some ordering of exactly that multiset whose list product is one.  No order is
silently inherited from the ambient list.
-/

namespace GaoLean

section Occurrences

variable {α : Type*}

/-- An occurrence of `s` is one of its positions, rather than an element of
the value-set of `s`. -/
abbrev Occurrence (s : List α) := Fin s.length

/-- The value carried by a particular occurrence. -/
def occurrenceValue (s : List α) (i : Occurrence s) : α := s.get i

/-- A subsequence selection is a finite set of positions of the source list.
Using positions retains multiplicity when equal values occur more than once. -/
abbrev Selection (s : List α) := Finset (Occurrence s)

/-- The multiset of values selected by a set of occurrences. -/
def selectedMultiset (s : List α) (I : Selection s) : Multiset α :=
  I.1.map (occurrenceValue s)

@[simp]
theorem card_selectedMultiset (s : List α) (I : Selection s) :
    (selectedMultiset s I).card = I.card := by
  simp [selectedMultiset]

/-- Disjoint selections really are disjoint at the occurrence level.  They
may still contain equal values, which is intentional. -/
def DisjointSelections (s : List α) (I J : Selection s) : Prop :=
  Disjoint I J

end Occurrences

section ProductOne

variable {G : Type*} [Monoid G]

/-- A noncommutative multiset is product-one if its occurrences have some
ordering whose literal list product is one. -/
def HasProductOneOrdering (S : Multiset G) : Prop :=
  ∃ word : List G, Multiset.ofList word = S ∧ word.prod = 1

/-- List-facing version: the witness may reorder the input list, but must use
exactly the same multiplicities. -/
def IsProductOneSequence (s : List G) : Prop :=
  ∃ word : List G, word.Perm s ∧ word.prod = 1

theorem hasProductOneOrdering_ofList_iff (s : List G) :
    HasProductOneOrdering (Multiset.ofList s) ↔ IsProductOneSequence s := by
  constructor
  · rintro ⟨word, hword, hprod⟩
    exact ⟨word, Multiset.coe_eq_coe.mp hword, hprod⟩
  · rintro ⟨word, hperm, hprod⟩
    exact ⟨word, Multiset.coe_eq_coe.mpr hperm, hprod⟩

/-- Product-one selection from a source sequence.  Selection uses source
positions; product-one uses an arbitrary ordering of the selected values. -/
def IsProductOneSelection (s : List G) (I : Selection s) : Prop :=
  HasProductOneOrdering (selectedMultiset s I)

/-- The exact subsequence predicate used by Gao-type constants. -/
def HasProductOneSubsequenceOfCard (s : List G) (k : ℕ) : Prop :=
  ∃ I : Selection s, I.card = k ∧ IsProductOneSelection s I

theorem isProductOneSequence_perm {s t : List G} (hst : s.Perm t) :
    IsProductOneSequence s ↔ IsProductOneSequence t := by
  constructor
  · rintro ⟨word, hword, hprod⟩
    exact ⟨word, hword.trans hst, hprod⟩
  · rintro ⟨word, hword, hprod⟩
    exact ⟨word, hword.trans hst.symm, hprod⟩

@[simp]
theorem isProductOneSequence_nil :
    IsProductOneSequence ([] : List G) := by
  exact ⟨[], List.Perm.refl [], by simp⟩

theorem isProductOneSequence_singleton_iff (g : G) :
    IsProductOneSequence [g] ↔ g = 1 := by
  constructor
  · rintro ⟨word, hperm, hprod⟩
    have hword : word = [g] := List.perm_singleton.mp hperm
    simpa [hword] using hprod
  · intro hg
    exact ⟨[g], List.Perm.refl _, by simp [hg]⟩

end ProductOne

end GaoLean

#print axioms GaoLean.card_selectedMultiset
#print axioms GaoLean.hasProductOneOrdering_ofList_iff
#print axioms GaoLean.isProductOneSequence_perm
#print axioms GaoLean.isProductOneSequence_singleton_iff
