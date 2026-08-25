import Mathlib

/-!
# Occurrence-sensitive product orderings

This file separates the combinatorics of occurrences from the algebra used by
the generalized-dihedral project.  Lists represent indexed occurrences: equal
values may occur at several positions, and `List.Perm` records that a proposed
word uses exactly the supplied occurrences, with multiplicity.

No commutativity assumption is made.  The product is taken in the literal
order of the realizing word.
-/

namespace GaoLean.Ordering

variable {α G H : Type*}

/-- `word` is an ordering of exactly the occurrences in `source` and its
literal product is `target`. -/
def IsProductOrdering [Monoid G]
    (source word : List G) (target : G) : Prop :=
  word.Perm source ∧ word.prod = target

/-- The supplied occurrences have some ordering with literal product
`target`. -/
def HasProductOrdering [Monoid G] (source : List G) (target : G) : Prop :=
  ∃ word, IsProductOrdering source word target

/-- The usual product-one condition, phrased without forgetting repeated
occurrences. -/
abbrev HasProductOneOrdering [Monoid G] (source : List G) : Prop :=
  HasProductOrdering source 1

theorem isProductOrdering_iff [Monoid G]
    {source word : List G} {target : G} :
    IsProductOrdering source word target ↔
      Multiset.ofList word = Multiset.ofList source ∧ word.prod = target := by
  constructor
  · rintro ⟨hperm, hprod⟩
    exact ⟨Quot.sound hperm, hprod⟩
  · rintro ⟨hmulti, hprod⟩
    exact ⟨Quotient.exact hmulti, hprod⟩

theorem IsProductOrdering.toMultiset_eq [Monoid G]
    {source word : List G} {target : G}
    (h : IsProductOrdering source word target) :
    Multiset.ofList word = Multiset.ofList source :=
  Quot.sound h.1

theorem IsProductOrdering.length_eq [Monoid G]
    {source word : List G} {target : G}
    (h : IsProductOrdering source word target) :
    word.length = source.length :=
  h.1.length_eq

theorem IsProductOrdering.count_eq [Monoid G] [DecidableEq G]
    {source word : List G} {target x : G}
    (h : IsProductOrdering source word target) :
    word.count x = source.count x :=
  h.1.count_eq x

@[simp]
theorem isProductOrdering_self [Monoid G] (word : List G) :
    IsProductOrdering word word word.prod :=
  ⟨List.Perm.refl word, rfl⟩

theorem hasProductOrdering_prod [Monoid G] (word : List G) :
    HasProductOrdering word word.prod :=
  ⟨word, isProductOrdering_self word⟩

theorem IsProductOrdering.source_perm [Monoid G]
    {source source' word : List G} {target : G}
    (h : IsProductOrdering source word target)
    (hsource : source.Perm source') :
    IsProductOrdering source' word target :=
  ⟨h.1.trans hsource, h.2⟩

theorem HasProductOrdering.congr [Monoid G]
    {source source' : List G} {target : G}
    (hsource : source.Perm source') :
    HasProductOrdering source target ↔ HasProductOrdering source' target := by
  constructor
  · rintro ⟨word, hword⟩
    exact ⟨word, hword.source_perm hsource⟩
  · rintro ⟨word, hword⟩
    exact ⟨word, hword.source_perm hsource.symm⟩

theorem IsProductOrdering.append [Monoid G]
    {source₁ source₂ word₁ word₂ : List G} {target₁ target₂ : G}
    (h₁ : IsProductOrdering source₁ word₁ target₁)
    (h₂ : IsProductOrdering source₂ word₂ target₂) :
    IsProductOrdering (source₁ ++ source₂) (word₁ ++ word₂)
      (target₁ * target₂) := by
  exact ⟨h₁.1.append h₂.1, by simp [h₁.2, h₂.2]⟩

theorem HasProductOrdering.append [Monoid G]
    {source₁ source₂ : List G} {target₁ target₂ : G}
    (h₁ : HasProductOrdering source₁ target₁)
    (h₂ : HasProductOrdering source₂ target₂) :
    HasProductOrdering (source₁ ++ source₂) (target₁ * target₂) := by
  rcases h₁ with ⟨word₁, hword₁⟩
  rcases h₂ with ⟨word₂, hword₂⟩
  exact ⟨word₁ ++ word₂, hword₁.append hword₂⟩

theorem IsProductOrdering.map
    [Monoid G] [Monoid H] (f : G →* H)
    {source word : List G} {target : G}
    (h : IsProductOrdering source word target) :
    IsProductOrdering (source.map f) (word.map f) (f target) := by
  constructor
  · exact h.1.map f
  · rw [← map_list_prod f word]
    exact congrArg f h.2

/-- Moving one occurrence across an arbitrary middle block preserves the
occurrence multiset.  This is the generic permutation step used by the old
dihedral list realization. -/
theorem move_singleton_across_middle
    (pre mid post : List α) (a : α) :
    (pre ++ [a] ++ mid ++ post).Perm
      (pre ++ mid ++ [a] ++ post) := by
  have hmove : ([a] ++ mid).Perm (mid ++ [a]) :=
    List.perm_append_comm
  simpa [List.append_assoc] using hmove.append_right post |>.append_left pre

/-- The two distinguished occurrences can be written on opposite sides of a
middle block while retaining exactly the source multiplicities. -/
theorem split_pair_perm
    (pre mid post : List α) (a b : α) :
    (pre ++ [a] ++ mid ++ [b] ++ post).Perm
      (pre ++ mid ++ [a, b] ++ post) := by
  simpa [List.append_assoc] using
    move_singleton_across_middle pre mid ([b] ++ post) a

/-- Package a literal product computation together with the generic
occurrence-preservation step. -/
theorem productOrdering_of_split_pair
    [Monoid G]
    (pre mid post : List G) (a b target : G)
    (hprod : (pre ++ [a] ++ mid ++ [b] ++ post).prod = target) :
    IsProductOrdering
      (pre ++ mid ++ [a, b] ++ post)
      (pre ++ [a] ++ mid ++ [b] ++ post)
      target :=
  ⟨split_pair_perm pre mid post a b, hprod⟩

/-- A zero-cost bridge for constructions that already supplied a multiset
identity rather than a `List.Perm` proof. -/
theorem productOrdering_of_multiset_eq [Monoid G]
    {source word : List G} {target : G}
    (hmulti : Multiset.ofList word = Multiset.ofList source)
    (hprod : word.prod = target) :
    IsProductOrdering source word target :=
  (isProductOrdering_iff).2 ⟨hmulti, hprod⟩

end GaoLean.Ordering

#print axioms GaoLean.Ordering.IsProductOrdering.append
#print axioms GaoLean.Ordering.IsProductOrdering.map
#print axioms GaoLean.Ordering.productOrdering_of_split_pair
