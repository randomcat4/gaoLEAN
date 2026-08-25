import GaoFormal.Matching.Basic

/-!
# Delete-one/add-two crossed replacement

The source matching loses one edge `i`; two edges through two unused points
are inserted.  The resulting index type has `(card ι - 1) + 2` edges.  This
file first closes the globally-distinct endpoint bookkeeping, then exposes the
linear-independence obligation used by the quotient-space exchange argument.
-/

namespace GaoFormal.IndependentDifferenceMatching

open Set Submodule

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
variable {A : Finset V} {ι : Type*}

abbrev Remaining (i : ι) := {j : ι // j ≠ i}
abbrev CrossedIndex (i : ι) := Remaining i ⊕ Fin 2

def crossedLeft (M : IndependentDifferenceMatching (F := F) A ι)
    (i : ι) : CrossedIndex i → V :=
  Sum.elim (fun j => M.left j.1) ![M.left i, M.right i]

def crossedRight (M : IndependentDifferenceMatching (F := F) A ι)
    (i : ι) (u v : V) : CrossedIndex i → V :=
  Sum.elim (fun j => M.right j.1) ![u, v]

def crossedDifference (M : IndependentDifferenceMatching (F := F) A ι)
    (i : ι) (u v : V) : CrossedIndex i → V :=
  fun j => crossedRight M i u v j - crossedLeft M i j

/-- Span of the differences of all old edges except `i`. -/
def deletedSpan (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    Submodule F V :=
  Submodule.span F (Set.range fun j : Remaining i => M.difference j.1)

/-- The surviving old differences, regarded as vectors in their own span. -/
def remainingDifferenceInSpan
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    Remaining i → deletedSpan M i :=
  fun j => ⟨M.difference j.1, Submodule.subset_span (Set.mem_range_self j)⟩

theorem remainingDifferenceInSpan_independent
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    LinearIndependent F (remainingDifferenceInSpan M i) := by
  apply LinearIndependent.of_comp (deletedSpan M i).subtype
  simpa [remainingDifferenceInSpan, difference, Function.comp_def] using
    M.independent.comp (fun j : Remaining i => j.1) Subtype.val_injective

/-- Quotient independence of the two inserted differences glues to the
independence of all surviving old differences.  This is the exact bridge from
the R1 two-vector calculation to the R2 matching structure. -/
theorem crossedDifference_independent_of_quotient
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) (u v : V)
    (hquot : LinearIndependent F
      (Submodule.Quotient.mk (p := deletedSpan M i) ∘
        (![u - M.left i, v - M.right i] : Fin 2 → V))) :
    LinearIndependent F (crossedDifference M i u v) := by
  have h := (remainingDifferenceInSpan_independent M i).sumElim_of_quotient
    (![u - M.left i, v - M.right i] : Fin 2 → V) hquot
  have heq : crossedDifference M i u v =
      Sum.elim (fun j : Remaining i => M.difference j.1)
        (![u - M.left i, v - M.right i] : Fin 2 → V) := by
    funext j
    cases j with
    | inl j => rfl
    | inr j => fin_cases j <;> rfl
  rw [heq]
  simpa [remainingDifferenceInSpan] using h

private theorem crossedLeft_injective
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) :
    Function.Injective (crossedLeft M i) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact Sum.inl.inj (M.endpoint_injective hxy)
      | inr y =>
          fin_cases y
          · exfalso
            exact x.2 (Sum.inl.inj (M.endpoint_injective hxy))
          · exfalso
            exact Sum.inl_ne_inr (M.endpoint_injective hxy)
  | inr x =>
      cases y with
      | inl y =>
          fin_cases x
          · exfalso
            exact y.2 (Sum.inl.inj (M.endpoint_injective hxy.symm))
          · exfalso
            exact Sum.inl_ne_inr (M.endpoint_injective hxy.symm)
      | inr y =>
          fin_cases x <;> fin_cases y
          · rfl
          · exfalso
            exact Sum.inl_ne_inr (M.endpoint_injective hxy)
          · exfalso
            exact Sum.inl_ne_inr (M.endpoint_injective hxy.symm)
          · rfl

private theorem crossedRight_injective
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) (u v : V)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v) :
    Function.Injective (crossedRight M i u v) := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          apply congrArg Sum.inl
          apply Subtype.ext
          exact Sum.inr.inj (M.endpoint_injective hxy)
      | inr y =>
          fin_cases y
          · exact (hu (Sum.inr x.1) hxy.symm).elim
          · exact (hv (Sum.inr x.1) hxy.symm).elim
  | inr x =>
      cases y with
      | inl y =>
          fin_cases x
          · exact (hu (Sum.inr y.1) hxy).elim
          · exact (hv (Sum.inr y.1) hxy).elim
      | inr y =>
          fin_cases x <;> fin_cases y
          · rfl
          · exact (huv hxy).elim
          · exact (huv hxy.symm).elim
          · rfl

private theorem crossedLeft_ne_crossedRight
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) (u v : V)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z) :
    ∀ x y, crossedLeft M i x ≠ crossedRight M i u v y := by
  intro x y hxy
  cases x with
  | inl x =>
      cases y with
      | inl y => exact Sum.inl_ne_inr (M.endpoint_injective hxy)
      | inr y =>
          fin_cases y
          · exact hu (Sum.inl x.1) hxy.symm
          · exact hv (Sum.inl x.1) hxy.symm
  | inr x =>
      cases y with
      | inl y =>
          fin_cases x
          · have hz : M.endpoint (Sum.inl i) = M.endpoint (Sum.inr y.1) := hxy
            exact Sum.inl_ne_inr (M.endpoint_injective hz)
          · have hz : M.endpoint (Sum.inr i) = M.endpoint (Sum.inr y.1) := hxy
            exact y.2 (Sum.inr.inj (M.endpoint_injective hz)).symm
      | inr y =>
          fin_cases x <;> fin_cases y
          · exact hu (Sum.inl i) hxy.symm
          · exact hv (Sum.inl i) hxy.symm
          · exact hu (Sum.inr i) hxy.symm
          · exact hv (Sum.inr i) hxy.symm

theorem crossedEndpoint_injective
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) (u v : V)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v) :
    Function.Injective (Sum.elim (crossedLeft M i) (crossedRight M i u v)) := by
  apply (crossedLeft_injective M i).sumElim
    (crossedRight_injective M i u v hu hv huv)
  exact crossedLeft_ne_crossedRight M i u v hu hv

def crossedReplacement
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) {u v : V}
    (huA : u ∈ A) (hvA : v ∈ A)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v)
    (hind : LinearIndependent F (crossedDifference M i u v)) :
    IndependentDifferenceMatching (F := F) A (CrossedIndex i) where
  left := crossedLeft M i
  right := crossedRight M i u v
  left_mem := by
    intro j
    cases j with
    | inl j => exact M.left_mem j.1
    | inr j =>
        fin_cases j
        · exact M.left_mem i
        · exact M.right_mem i
  right_mem := by
    intro j
    cases j with
    | inl j => exact M.right_mem j.1
    | inr j =>
        fin_cases j
        · exact huA
        · exact hvA
  endpoint_injective := crossedEndpoint_injective M i u v hu hv huv
  independent := hind

/-- The complete delete-one/add-two matching constructor with its linear
independence discharged in the quotient by the surviving old differences. -/
def crossedReplacementOfQuotient
    (M : IndependentDifferenceMatching (F := F) A ι) (i : ι) {u v : V}
    (huA : u ∈ A) (hvA : v ∈ A)
    (hu : ∀ z, u ≠ M.endpoint z) (hv : ∀ z, v ≠ M.endpoint z)
    (huv : u ≠ v)
    (hquot : LinearIndependent F
      (Submodule.Quotient.mk (p := deletedSpan M i) ∘
        (![u - M.left i, v - M.right i] : Fin 2 → V))) :
    IndependentDifferenceMatching (F := F) A (CrossedIndex i) :=
  crossedReplacement M i huA hvA hu hv huv
    (crossedDifference_independent_of_quotient M i u v hquot)

end GaoFormal.IndependentDifferenceMatching
