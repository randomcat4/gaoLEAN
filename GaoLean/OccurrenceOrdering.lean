import GaoLean.Sequence
import GaoLean.Ordering

/-!
# Bridge from occurrence selections to literal product orderings

`Sequence.lean` selects positions of a source list and records their values as
a multiset.  `Ordering.lean` describes a literal word by `List.Perm`.  The
results here show that these representations agree without collapsing equal
values at distinct positions.
-/

namespace GaoLean.OccurrenceOrdering

open GaoLean.Ordering

variable {G : Type*}

/-- The list-facing predicate in `Sequence.lean` and the generic ordering
predicate are definitionally the same occurrence-sensitive assertion. -/
theorem hasProductOneOrdering_iff_isProductOneSequence [Monoid G]
    (source : List G) :
    Ordering.HasProductOneOrdering source ↔ IsProductOneSequence source := by
  rfl

/-- A product-one ordering of a list is equivalent to a product-one ordering
of its occurrence multiset. -/
theorem hasProductOneOrdering_iff_multiset [Monoid G] (source : List G) :
    Ordering.HasProductOneOrdering source ↔
      GaoLean.HasProductOneOrdering (Multiset.ofList source) := by
  rw [GaoLean.hasProductOneOrdering_ofList_iff]
  exact hasProductOneOrdering_iff_isProductOneSequence source

/-- Choosing an arbitrary list representative of the selected multiset loses
no product-one information. -/
theorem isProductOneSelection_iff_toList
    [Monoid G]
    (source : List G) (I : Selection source) :
    IsProductOneSelection source I ↔
      Ordering.HasProductOneOrdering (selectedMultiset source I).toList := by
  unfold IsProductOneSelection
  rw [hasProductOneOrdering_iff_multiset]
  simp

/-- A product-one selection has a literal product-one word using precisely
the selected occurrences. -/
theorem IsProductOneSelection.exists_literal_ordering
    [Monoid G]
    {source : List G} {I : Selection source}
    (h : IsProductOneSelection source I) :
    ∃ word : List G,
      word.Perm (selectedMultiset source I).toList ∧
      word.prod = 1 := by
  exact (isProductOneSelection_iff_toList source I).1 h

/-- Every literal witness for a selection has exactly the selected number of
occurrences. -/
theorem literal_ordering_length_eq_card
    {source : List G} {I : Selection source} {word : List G}
    (hperm : word.Perm (selectedMultiset source I).toList) :
    word.length = I.card := by
  calc
    word.length = (selectedMultiset source I).toList.length := hperm.length_eq
    _ = (selectedMultiset source I).card := by simp
    _ = I.card := card_selectedMultiset source I

/-- A product-one selection therefore has a literal witness whose length is
the cardinality of the selected position set. -/
theorem IsProductOneSelection.exists_literal_ordering_of_length
    [Monoid G]
    {source : List G} {I : Selection source}
    (h : IsProductOneSelection source I) :
    ∃ word : List G,
      word.Perm (selectedMultiset source I).toList ∧
      word.length = I.card ∧
      word.prod = 1 := by
  rcases IsProductOneSelection.exists_literal_ordering h with
    ⟨word, hperm, hprod⟩
  exact ⟨word, hperm, literal_ordering_length_eq_card hperm, hprod⟩

/-- Literal reordering preserves the multiplicity of every selected value. -/
theorem literal_ordering_count_eq [DecidableEq G]
    {source : List G} {I : Selection source} {word : List G}
    (hperm : word.Perm (selectedMultiset source I).toList) (x : G) :
    word.count x = (selectedMultiset source I).count x := by
  have hmulti : Multiset.ofList word = selectedMultiset source I :=
    (Quot.sound hperm).trans (Multiset.coe_toList _)
  calc
    word.count x = (Multiset.ofList word).count x :=
      (Multiset.coe_count x word).symm
    _ = (selectedMultiset source I).count x :=
      congrArg (Multiset.count x) hmulti

/-- A bundled `Ordering.IsProductOrdering` witness gives both cardinality and
value-by-value multiplicity preservation for a selected sequence. -/
theorem IsProductOrdering.selection_card_and_count [DecidableEq G]
    [Monoid G]
    {source : List G} {I : Selection source} {word : List G} {target : G}
    (h : Ordering.IsProductOrdering
      (selectedMultiset source I).toList word target) :
    word.length = I.card ∧
      ∀ x : G, word.count x = (selectedMultiset source I).count x := by
  constructor
  · exact literal_ordering_length_eq_card h.1
  · exact fun x => literal_ordering_count_eq h.1 x

end GaoLean.OccurrenceOrdering

#print axioms GaoLean.OccurrenceOrdering.isProductOneSelection_iff_toList
#print axioms GaoLean.OccurrenceOrdering.IsProductOneSelection.exists_literal_ordering_of_length
#print axioms GaoLean.OccurrenceOrdering.IsProductOrdering.selection_card_and_count
