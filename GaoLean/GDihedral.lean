import Mathlib

/-!
# Abstract generalized-dihedral interface

This file records the algebraic relations used by the Gao project without
claiming any zero-sum or Gao-constant theorem.  The normal subgroup is an
additive commutative group `A`; `rotation` embeds its additive law into an
ambient multiplicative group, while `flip` acts by inversion.

The interface is intentionally usable before a concrete semidirect-product
implementation is chosen.  Injectivity or surjectivity of `rotation` is not
assumed here because the elementary word identities do not need them.
-/

namespace GaoLean

/-- Data and relations for a generalized-dihedral realization inside an
ambient group `G`. -/
structure GDihedralData (A G : Type*) [AddCommGroup A] [Group G] where
  /-- The rotation subgroup, written multiplicatively in `G`. -/
  rotation : Multiplicative A →* G
  /-- A distinguished reflection. -/
  flip : G
  /-- The distinguished reflection is an involution. -/
  flip_sq : flip * flip = 1
  /-- Conjugation across the reflection negates a rotation coordinate. -/
  flip_mul_rotation : ∀ a : A,
    flip * rotation (Multiplicative.ofAdd a) =
      rotation (Multiplicative.ofAdd (-a)) * flip

namespace GDihedralData

variable {A G : Type*} [AddCommGroup A] [Group G]
variable (D : GDihedralData A G)

/-- Rotation in additive coordinates. -/
def rot (a : A) : G := D.rotation (Multiplicative.ofAdd a)

/-- Paper convention for a reflection: `refl a = rot a * flip`. -/
def refl (a : A) : G := D.rot a * D.flip

@[simp]
theorem rot_zero : D.rot 0 = 1 := by
  simp [rot]

@[simp]
theorem rot_add (a b : A) : D.rot (a + b) = D.rot a * D.rot b := by
  exact D.rotation.map_mul _ _

@[simp]
theorem flip_mul_rot (a : A) : D.flip * D.rot a = D.rot (-a) * D.flip := by
  exact D.flip_mul_rotation a

@[simp]
theorem rot_mul_refl (a b : A) : D.rot a * D.refl b = D.refl (a + b) := by
  unfold refl
  rw [← mul_assoc, ← rot_add]

@[simp]
theorem refl_mul_rot (a b : A) : D.refl a * D.rot b = D.refl (a - b) := by
  simp only [refl, sub_eq_add_neg]
  rw [mul_assoc, flip_mul_rot, ← mul_assoc, ← rot_add]

@[simp]
theorem refl_mul_refl (a b : A) : D.refl a * D.refl b = D.rot (a - b) := by
  simp only [refl, sub_eq_add_neg]
  calc
    (D.rot a * D.flip) * (D.rot b * D.flip) =
        D.rot a * (D.flip * D.rot b) * D.flip := by simp only [mul_assoc]
    _ = D.rot a * (D.rot (-b) * D.flip) * D.flip := by rw [flip_mul_rot]
    _ = (D.rot a * D.rot (-b)) * (D.flip * D.flip) := by
      simp only [mul_assoc]
    _ = D.rot (a + -b) := by rw [← rot_add, D.flip_sq, mul_one]

@[simp]
theorem refl_sq (a : A) : D.refl a * D.refl a = 1 := by
  rw [refl_mul_refl, sub_self, rot_zero]

/-- A pair of reflections contributes the signed coordinate `a - b`. -/
def pairWord : List (A × A) → G
  | [] => 1
  | (a, b) :: pairs => (D.refl a * D.refl b) * pairWord pairs

/-- Additive coordinate carried by a list of ordered reflection pairs. -/
def pairCoordinate : List (A × A) → A
  | [] => 0
  | (a, b) :: pairs => (a - b) + pairCoordinate pairs

@[simp]
theorem pairWord_eq_rot_pairCoordinate (pairs : List (A × A)) :
    pairWord D pairs = D.rot (pairCoordinate pairs) := by
  induction pairs with
  | nil => simp [pairWord, pairCoordinate]
  | cons p pairs ih =>
      rcases p with ⟨a, b⟩
      simp [pairWord, pairCoordinate, ih]

theorem pairWord_eq_one_of_pairCoordinate_eq_zero
    (pairs : List (A × A)) (hzero : pairCoordinate pairs = 0) :
    pairWord D pairs = 1 := by
  rw [pairWord_eq_rot_pairCoordinate, hzero, rot_zero]

end GDihedralData

end GaoLean

#print axioms GaoLean.GDihedralData.rot_add
#print axioms GaoLean.GDihedralData.refl_mul_refl
#print axioms GaoLean.GDihedralData.pairWord_eq_rot_pairCoordinate
#print axioms GaoLean.GDihedralData.pairWord_eq_one_of_pairCoordinate_eq_zero
