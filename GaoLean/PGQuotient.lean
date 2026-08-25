import GaoLean.PGController

/-!
# Concrete quotient projection for the PG-O3 controller

This promotes the previously isolated semidirect-product naturality probe to
a formal module.  It constructs the actual group homomorphism induced by
`A → A/K` and proves its action on rotations, the distinguished flip, and
reflections.
-/

namespace GaoLean.ConcreteGDihedral

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

def normalMap (f : A →+ B) : Multiplicative A →* Multiplicative B :=
  AddMonoidHom.toMultiplicative f

@[simp] theorem inversionAction_zero (a : A) :
    inversionAction A (Multiplicative.ofAdd (0 : ZMod 2))
      (Multiplicative.ofAdd a) = Multiplicative.ofAdd a := by
  have h : Multiplicative.ofAdd (0 : ZMod 2) = 1 := rfl
  rw [h]
  simp

theorem naturality (f : A →+ B) (g : Multiplicative (ZMod 2)) :
    (normalMap f).comp (inversionAction A g).toMonoidHom =
      (inversionAction B g).toMonoidHom.comp (normalMap f) := by
  change ZMod 2 at g
  fin_cases g
  · ext a
    change f (Multiplicative.toAdd
        (inversionAction A (Multiplicative.ofAdd (0 : ZMod 2))
          (Multiplicative.ofAdd (Multiplicative.toAdd a)))) =
      Multiplicative.toAdd
        (inversionAction B (Multiplicative.ofAdd (0 : ZMod 2))
          (Multiplicative.ofAdd (f (Multiplicative.toAdd a))))
    rw [inversionAction_zero, inversionAction_zero]
    rfl
  · ext a
    change Multiplicative.ofAdd (f (-Multiplicative.toAdd a)) =
      Multiplicative.ofAdd (-f (Multiplicative.toAdd a))
    rw [map_neg]

/-- The generalized-dihedral quotient homomorphism induced by `A → A/K`. -/
def quotientMap (K : AddSubgroup A) : Group A →* Group (A ⧸ K) :=
  SemidirectProduct.map
    (normalMap (QuotientAddGroup.mk' K))
    (MonoidHom.id (Multiplicative (ZMod 2)))
    (naturality (QuotientAddGroup.mk' K))

@[simp] theorem quotientMap_rotation (K : AddSubgroup A) (a : A) :
    quotientMap K (rotation A (Multiplicative.ofAdd a)) =
      rotation (A ⧸ K) (Multiplicative.ofAdd (QuotientAddGroup.mk' K a)) := by
  unfold quotientMap
  apply SemidirectProduct.ext <;> rfl

@[simp] theorem quotientMap_flip (K : AddSubgroup A) :
    quotientMap K (flip A) = flip (A ⧸ K) := by
  simp [quotientMap, flip]

@[simp] theorem quotientMap_refl (K : AddSubgroup A) (a : A) :
    quotientMap K ((data A).refl a) =
      (data (A ⧸ K)).refl (QuotientAddGroup.mk' K a) := by
  change quotientMap K (rotation A (Multiplicative.ofAdd a) * flip A) =
    rotation (A ⧸ K)
      (Multiplicative.ofAdd (QuotientAddGroup.mk' K a)) * flip (A ⧸ K)
  rw [map_mul, quotientMap_rotation, quotientMap_flip]

/-- Quotient projection preserves the rotation/reflection coset exactly. -/
theorem quotientMap_isRotation_iff (K : AddSubgroup A) (g : Group A) :
    IsRotation (quotientMap K g) ↔ IsRotation g := by
  rfl

/-- The additive rotation coordinate is mapped by the ordinary quotient map. -/
theorem coordinate_quotientMap (K : AddSubgroup A) (g : Group A) :
    coordinate (quotientMap K g) = QuotientAddGroup.mk' K (coordinate g) := by
  rfl

/-- A concrete element vanishes in the generalized-dihedral quotient exactly
when it is a rotation whose additive coordinate lies in the kernel subgroup. -/
theorem quotientMap_eq_one_iff (K : AddSubgroup A) (g : Group A) :
    quotientMap K g = 1 ↔ IsRotation g ∧ coordinate g ∈ K := by
  constructor
  · intro hg
    have hright := congrArg SemidirectProduct.right hg
    have hleft := congrArg SemidirectProduct.left hg
    constructor
    · exact hright
    · apply (QuotientAddGroup.eq_zero_iff (coordinate g)).1
      change Multiplicative.toAdd
          (normalMap (QuotientAddGroup.mk' K) g.left) = 0
      change Multiplicative.toAdd
          (normalMap (QuotientAddGroup.mk' K) g.left) =
        Multiplicative.toAdd 1
      exact congrArg Multiplicative.toAdd hleft
  · rintro ⟨hrot, hcoord⟩
    apply SemidirectProduct.ext
    · change Multiplicative.ofAdd
          (QuotientAddGroup.mk' K (coordinate g)) = 1
      have hz : QuotientAddGroup.mk' K (coordinate g) = 0 :=
        (QuotientAddGroup.eq_zero_iff (coordinate g)).2 hcoord
      rw [hz]
      rfl
    · exact hrot

/-- The additive map `A/H → A/K` induced by an inclusion `H ≤ K`. -/
def quotientBetweenAddMap (H K : AddSubgroup A) (hHK : H ≤ K) :
    A ⧸ H →+ A ⧸ K :=
  QuotientAddGroup.map H K (AddMonoidHom.id A) (by simpa using hHK)

@[simp] theorem quotientBetweenAddMap_mk (H K : AddSubgroup A) (hHK : H ≤ K)
    (a : A) :
    quotientBetweenAddMap H K hHK (QuotientAddGroup.mk' H a) =
      QuotientAddGroup.mk' K a := by
  rfl

/-- The generalized-dihedral map `G(A/H) → G(A/K)` induced by `H ≤ K`. -/
def quotientBetweenMap (H K : AddSubgroup A) (hHK : H ≤ K) :
    Group (A ⧸ H) →* Group (A ⧸ K) :=
  SemidirectProduct.map
    (normalMap (quotientBetweenAddMap H K hHK))
    (MonoidHom.id (Multiplicative (ZMod 2)))
    (naturality (quotientBetweenAddMap H K hHK))

/-- Direct projection to `A/K` factors through projection to `A/H`. -/
theorem quotientBetweenMap_quotientMap (H K : AddSubgroup A) (hHK : H ≤ K)
    (g : Group A) :
    quotientBetweenMap H K hHK (quotientMap H g) = quotientMap K g := by
  apply SemidirectProduct.ext <;> rfl

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ConcreteGDihedral.naturality
#print axioms GaoLean.ConcreteGDihedral.quotientMap_rotation
#print axioms GaoLean.ConcreteGDihedral.quotientMap_refl
#print axioms GaoLean.ConcreteGDihedral.quotientMap_isRotation_iff
#print axioms GaoLean.ConcreteGDihedral.coordinate_quotientMap
#print axioms GaoLean.ConcreteGDihedral.quotientMap_eq_one_iff
#print axioms GaoLean.ConcreteGDihedral.quotientBetweenMap_quotientMap
