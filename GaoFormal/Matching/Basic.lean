import Mathlib

/-!
# Occurrence-faithful independent-difference matchings

This is the version-controlled successor of the isolated R1/R2 dossier files.
It keeps oriented edges for their differences, while injectivity of the tagged
endpoint map expresses an unordered matching with globally distinct vertices.
-/

namespace GaoFormal

open Set Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

structure IndependentDifferenceMatching (A : Finset V) (ι : Type*) where
  left : ι → V
  right : ι → V
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ A
  endpoint_injective : Function.Injective (Sum.elim left right)
  independent : LinearIndependent F (fun i => right i - left i)

namespace IndependentDifferenceMatching

universe u

variable {A : Finset V} {ι : Type*}

def endpoint (M : IndependentDifferenceMatching (F := F) A ι) : ι ⊕ ι → V :=
  Sum.elim M.left M.right

def difference (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) : V :=
  M.right i - M.left i

@[simp] theorem endpoint_inl
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    M.endpoint (Sum.inl i) = M.left i := rfl

@[simp] theorem endpoint_inr
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    M.endpoint (Sum.inr i) = M.right i := rfl

def IsMaximum {ι : Type u} [Fintype ι]
    (_M : IndependentDifferenceMatching (F := F) A ι) : Prop :=
  ∀ (κ : Type u) [Fintype κ],
    IndependentDifferenceMatching (F := F) A κ → Fintype.card κ ≤ Fintype.card ι

/-- Adjoin an edge through two unused points when its difference is outside
the span of the old differences. -/
def extend (M : IndependentDifferenceMatching (F := F) A ι) {u v : V}
    (huA : u ∈ A) (hvA : v ∈ A)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v)
    (hind : v - u ∉ Submodule.span F (Set.range M.difference)) :
    IndependentDifferenceMatching (F := F) A (Option ι) where
  left := fun o => Option.casesOn' o u M.left
  right := fun o => Option.casesOn' o v M.right
  left_mem := by
    intro o
    cases o with
    | none => exact huA
    | some i => exact M.left_mem i
  right_mem := by
    intro o
    cases o with
    | none => exact hvA
    | some i => exact M.right_mem i
  endpoint_injective := by
    have hleft : Function.Injective (fun o => Option.casesOn' o u M.left) := by
      intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some j => exact (hu (Sum.inl j) hab).elim
      | some i =>
          cases b with
          | none => exact (hu (Sum.inl i) hab.symm).elim
          | some j =>
              have hz : M.endpoint (Sum.inl i) = M.endpoint (Sum.inl j) := hab
              exact congrArg some (Sum.inl.inj (M.endpoint_injective hz))
    have hright : Function.Injective (fun o => Option.casesOn' o v M.right) := by
      intro a b hab
      cases a with
      | none =>
          cases b with
          | none => rfl
          | some j => exact (hv (Sum.inr j) hab).elim
      | some i =>
          cases b with
          | none => exact (hv (Sum.inr i) hab.symm).elim
          | some j =>
              have hz : M.endpoint (Sum.inr i) = M.endpoint (Sum.inr j) := hab
              exact congrArg some (Sum.inr.inj (M.endpoint_injective hz))
    apply hleft.sumElim hright
    intro a b hab
    cases a with
    | none =>
        cases b with
        | none => exact huv hab
        | some j => exact hu (Sum.inr j) hab
    | some i =>
        cases b with
        | none => exact hv (Sum.inl i) hab.symm
        | some j =>
            have hz : M.endpoint (Sum.inl i) = M.endpoint (Sum.inr j) := hab
            exact Sum.inl_ne_inr (M.endpoint_injective hz)
  independent := by
    have hfun :
        (fun o : Option ι => Option.casesOn' o v M.right - Option.casesOn' o u M.left) =
          (fun o => Option.casesOn' o (v - u) (fun i => M.right i - M.left i)) := by
      funext o
      cases o <;> rfl
    rw [hfun]
    exact M.independent.option hind

theorem sub_mem_span_of_maximum {ι : Type u} [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (hmax : M.IsMaximum)
    {u v : V} (huA : u ∈ A) (hvA : v ∈ A)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z) :
    v - u ∈ Submodule.span F (Set.range M.difference) := by
  by_contra hind
  have huv : u ≠ v := by
    intro huv
    subst v
    apply hind
    simp
  let N := M.extend huA hvA hu hv huv hind
  have hcard := hmax (Option ι) N
  simp only [Fintype.card_option] at hcard
  omega

theorem all_unused_sub_mem_span [Fintype ι]
    (M : IndependentDifferenceMatching (F := F) A ι) (hmax : M.IsMaximum)
    {u0 : V} (hu0A : u0 ∈ A) (hu0 : ∀ z, u0 ≠ M.endpoint z) :
    ∀ {u : V}, u ∈ A → (∀ z, u ≠ M.endpoint z) →
      u - u0 ∈ Submodule.span F (Set.range M.difference) := by
  intro u huA hu
  exact M.sub_mem_span_of_maximum hmax hu0A huA hu0 hu

end IndependentDifferenceMatching

end GaoFormal
