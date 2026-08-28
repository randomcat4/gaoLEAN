import GaoLean.PGGMOOrdinaryCanonicalStep1

/-!
# Finite maximality bookkeeping for canonical ordinary Step 1 cores

Canonical Step 1 cores form a finite search problem at the subgroup level.
This module chooses a core whose subgroup has maximal cardinality and records
the two terminal consequences already proved: top gives a full spectrum, and
a proper core with a sufficiently large complete coset container gives
concentration.

The scheduler at the end is deliberately conditional.  Its strict local
enlargement function is an explicit proof obligation; this file does not prove
the missing Step 1.2 extension and does not store such an extension inside a
core or maximality structure.
-/

namespace GaoLean

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- A canonical Step 1 core maximal only by the cardinality of its subgroup
among all canonical cores for the same labelled source. -/
structure SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core
    (xs : List A) where
  core : CanonicalOrdinaryGMOStep1Core xs
  subgroupCard_maximal :
    ∀ C : CanonicalOrdinaryGMOStep1Core xs,
      Nat.card C.H ≤ Nat.card core.H

/-- Any inhabited family of canonical cores contains one whose subgroup
cardinality is maximal.  The finite maximization is over actual additive
subgroups; a witnessing canonical core is then recovered from the filtered
family. -/
theorem exists_subgroupCardMaximalCanonicalOrdinaryGMOStep1Core
    {xs : List A}
    (hcore : Nonempty (CanonicalOrdinaryGMOStep1Core xs)) :
    Nonempty (SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core xs) := by
  classical
  letI : Fintype (AddSubgroup A) := Fintype.ofFinite _
  let good : Finset (AddSubgroup A) :=
    Finset.univ.filter fun H ↦
      ∃ C : CanonicalOrdinaryGMOStep1Core xs, C.H = H
  obtain ⟨C₀⟩ := hcore
  have hC₀good : C₀.H ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C₀, rfl⟩
  obtain ⟨H, hHgood, hHmax⟩ :=
    Finset.exists_max_image good
      (fun H : AddSubgroup A ↦ Nat.card H) ⟨C₀.H, hC₀good⟩
  obtain ⟨C, hCH⟩ :=
    (Finset.mem_filter.mp hHgood).2
  refine ⟨{
    core := C
    subgroupCard_maximal := ?_
  }⟩
  intro C''
  have hC''good : C''.H ∈ good := by
    simp only [good, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨C'', rfl⟩
  have hmax := hHmax C''.H hC''good
  rw [hCH]
  exact hmax

namespace SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core

/-- The top-subgroup terminal branch delegates to the direct
occurrence-level full-spectrum construction for canonical cores. -/
theorem ordinarySpectrumFull_of_H_eq_top
    {xs : List A}
    (M : SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core xs)
    (n : ℕ) (hH : M.core.H = ⊤)
    (hnA : Nat.card A ≤ n)
    (hlen : n + pGroupDStar A ≤ xs.length) :
    OrdinarySpectrumFull xs n :=
  M.core.ordinarySpectrumFull_of_H_eq_top n hH hnA hlen

/-- A proper maximal core whose complete canonical container reaches the
source-coset threshold gives the existing concentration endpoint. -/
theorem nonempty_concentration_of_card_lower
    {xs : List A}
    (M : SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core xs)
    (hproper : M.core.H < ⊤)
    (hcard :
      xs.length - Nat.card (A ⧸ M.core.H) + 2 ≤ M.core.container.card) :
    Nonempty (OrdinaryGMOConcentration xs) :=
  M.core.nonempty_concentration_of_card_lower hproper hcard

end SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core

/-- Conditional finite scheduler for canonical Step 1 cores.

This theorem is bookkeeping only.  The argument `henlarge` is exactly the
unproved local Step 1.2 obligation: every proper, sub-threshold canonical core
must strictly enlarge its subgroup.  Given that obligation, subgroup-card
maximality rules out the remaining branch.  No extension result is asserted
or hidden in the data structures of this module. -/
theorem ordinaryStructuralAlternative_of_canonicalLocalStrictEnlargement
    {xs : List A} (n : ℕ)
    (hcore : Nonempty (CanonicalOrdinaryGMOStep1Core xs))
    (hnA : Nat.card A ≤ n)
    (hlen : n + pGroupDStar A ≤ xs.length)
    (henlarge :
      ∀ C : CanonicalOrdinaryGMOStep1Core xs,
        C.H < ⊤ →
        C.container.card <
          xs.length - Nat.card (A ⧸ C.H) + 2 →
        ∃ C'' : CanonicalOrdinaryGMOStep1Core xs, C.H < C''.H) :
    OrdinarySpectrumFull xs n ∨
      Nonempty (OrdinaryGMOConcentration xs) := by
  obtain ⟨M⟩ :=
    exists_subgroupCardMaximalCanonicalOrdinaryGMOStep1Core hcore
  by_cases htop : M.core.H = ⊤
  · exact Or.inl
      (M.ordinarySpectrumFull_of_H_eq_top n htop hnA hlen)
  · have hproper : M.core.H < ⊤ :=
      lt_top_iff_ne_top.mpr htop
    by_cases hcard :
        xs.length - Nat.card (A ⧸ M.core.H) + 2 ≤
          M.core.container.card
    · exact Or.inr
        (M.nonempty_concentration_of_card_lower hproper hcard)
    · have hsmall :
          M.core.container.card <
            xs.length - Nat.card (A ⧸ M.core.H) + 2 :=
        Nat.lt_of_not_ge hcard
      obtain ⟨C'', hstrict⟩ :=
        henlarge M.core hproper hsmall
      have hltCard : Nat.card M.core.H < Nat.card C''.H :=
        natCard_lt_of_addSubgroup_lt hstrict
      have hmax := M.subgroupCard_maximal C''
      omega

end GaoLean

#print axioms GaoLean.exists_subgroupCardMaximalCanonicalOrdinaryGMOStep1Core
#print axioms GaoLean.SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core.ordinarySpectrumFull_of_H_eq_top
#print axioms GaoLean.SubgroupCardMaximalCanonicalOrdinaryGMOStep1Core.nonempty_concentration_of_card_lower
#print axioms GaoLean.ordinaryStructuralAlternative_of_canonicalLocalStrictEnlargement
