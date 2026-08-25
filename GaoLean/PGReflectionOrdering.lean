import GaoLean.PGGMO

/-!
# Balanced reflection/rotation ordering

A-R6 Section 1 states that a positive even set of reflections with balanced
signs, together with arbitrarily signed rotations, admits one literal
ordering whose product coordinate is the assigned signed sum.  This file gives
an explicit construction and lifts it to occurrence-labelled selections.
-/

namespace GaoLean

namespace GDihedralData

variable {A G : Type*} [AddCommGroup A] [Group G]
variable (D : GDihedralData A G)

/-- Interleave equal-length positive and negative reflection-coordinate lists
as `(positive, negative)` pairs. -/
def pairedReflectionWord : List A → List A → List G
  | p :: ps, n :: ns => D.refl p :: D.refl n :: pairedReflectionWord ps ns
  | _, _ => []

/-- The explicit word realizing arbitrary rotation signs and balanced
reflection signs.  Negative rotations are placed between the first positive
and first negative reflection. -/
def balancedSignedWord
    (rotationPlus rotationMinus reflectionPlus reflectionMinus : List A) :
    List G :=
  match reflectionPlus, reflectionMinus with
  | p :: ps, n :: ns =>
      rotationPlus.map D.rot ++ [D.refl p] ++
        rotationMinus.map D.rot ++ [D.refl n] ++
          pairedReflectionWord D ps ns
  | _, _ => []

@[simp]
theorem prod_map_rot (xs : List A) :
    (xs.map D.rot).prod = D.rot xs.sum := by
  induction xs with
  | nil => simp
  | cons x xs ih => simp [ih]

theorem prod_pairedReflectionWord
    (positive negative : List A) (hlen : positive.length = negative.length) :
    (pairedReflectionWord D positive negative).prod =
      D.rot (positive.sum - negative.sum) := by
  induction positive generalizing negative with
  | nil =>
      have hneg : negative = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst negative
      simp [pairedReflectionWord]
  | cons p ps ih =>
      cases negative with
      | nil => simp at hlen
      | cons n ns =>
          have htail : ps.length = ns.length := by simpa using hlen
          rw [show pairedReflectionWord D (p :: ps) (n :: ns) =
              D.refl p :: D.refl n :: pairedReflectionWord D ps ns by rfl]
          simp only [List.prod_cons]
          rw [← mul_assoc, D.refl_mul_refl, ih ns htail, ← D.rot_add]
          congr 2
          simp only [List.sum_cons]
          abel

theorem multiset_pairedReflectionWord
    (positive negative : List A) (hlen : positive.length = negative.length) :
    Multiset.ofList (pairedReflectionWord D positive negative) =
      (Multiset.ofList (positive.map D.refl)) +
        Multiset.ofList (negative.map D.refl) := by
  induction positive generalizing negative with
  | nil =>
      have hneg : negative = [] := List.length_eq_zero_iff.mp (by simpa using hlen.symm)
      subst negative
      simp [pairedReflectionWord]
  | cons p ps ih =>
      cases negative with
      | nil => simp at hlen
      | cons n ns =>
          have htail : ps.length = ns.length := by simpa using hlen
          change (D.refl p ::ₘ D.refl n ::ₘ
              Multiset.ofList (pairedReflectionWord D ps ns)) =
            (D.refl p ::ₘ Multiset.ofList (ps.map D.refl)) +
              (D.refl n ::ₘ Multiset.ofList (ns.map D.refl))
          rw [ih ns htail]
          simp only [← Multiset.singleton_add]
          ac_rfl

theorem prod_balancedSignedWord
    (rotationPlus rotationMinus reflectionPlus reflectionMinus : List A)
    (hlen : reflectionPlus.length = reflectionMinus.length)
    (hnonempty : reflectionPlus ≠ []) :
    (balancedSignedWord D rotationPlus rotationMinus
      reflectionPlus reflectionMinus).prod =
      D.rot (rotationPlus.sum - rotationMinus.sum +
        reflectionPlus.sum - reflectionMinus.sum) := by
  cases reflectionPlus with
  | nil => exact False.elim (hnonempty rfl)
  | cons p ps =>
      cases reflectionMinus with
      | nil => simp at hlen
      | cons n ns =>
          have htail : ps.length = ns.length := by simpa using hlen
          simp only [balancedSignedWord, List.prod_append, prod_map_rot,
            List.prod_cons, List.prod_nil, mul_one]
          rw [D.rot_mul_refl, D.refl_mul_rot, D.refl_mul_refl,
            prod_pairedReflectionWord D ps ns htail]
          simp only [List.sum_cons]
          rw [← D.rot_add]
          congr 1
          abel

theorem multiset_balancedSignedWord
    (rotationPlus rotationMinus reflectionPlus reflectionMinus : List A)
    (hlen : reflectionPlus.length = reflectionMinus.length)
    (hnonempty : reflectionPlus ≠ []) :
    Multiset.ofList (balancedSignedWord D rotationPlus rotationMinus
      reflectionPlus reflectionMinus) =
      Multiset.ofList (rotationPlus.map D.rot) +
      Multiset.ofList (rotationMinus.map D.rot) +
      Multiset.ofList (reflectionPlus.map D.refl) +
      Multiset.ofList (reflectionMinus.map D.refl) := by
  cases reflectionPlus with
  | nil => exact False.elim (hnonempty rfl)
  | cons p ps =>
      cases reflectionMinus with
      | nil => simp at hlen
      | cons n ns =>
          have htail : ps.length = ns.length := by simpa using hlen
          simp only [balancedSignedWord, ← Multiset.coe_add, List.map_cons,
            ← Multiset.cons_coe]
          rw [multiset_pairedReflectionWord D ps ns htail]
          simp only [← Multiset.singleton_add]
          ac_rfl

theorem prod_balancedSignedWord_eq_one
    (rotationPlus rotationMinus reflectionPlus reflectionMinus : List A)
    (hlen : reflectionPlus.length = reflectionMinus.length)
    (hnonempty : reflectionPlus ≠ [])
    (hzero : rotationPlus.sum - rotationMinus.sum +
      reflectionPlus.sum - reflectionMinus.sum = 0) :
    (balancedSignedWord D rotationPlus rotationMinus
      reflectionPlus reflectionMinus).prod = 1 := by
  rw [prod_balancedSignedWord D rotationPlus rotationMinus
    reflectionPlus reflectionMinus hlen hnonempty, hzero, D.rot_zero]

end GDihedralData

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A]

/-- Exact multiplicity-sensitive encoding of the signed assignment in A-R6
Section 1.  The carrier equality says that the four coordinate lists partition
the selected multiset, not merely its value set. -/
structure BalancedSignedAssignment
    (S : Multiset (Group A)) where
  rotationPlus : List A
  rotationMinus : List A
  reflectionPlus : List A
  reflectionMinus : List A
  reflectionLengthEq : reflectionPlus.length = reflectionMinus.length
  reflectionPlusNonempty : reflectionPlus ≠ []
  carrier_eq :
    S = Multiset.ofList (rotationPlus.map (data A).rot) +
      Multiset.ofList (rotationMinus.map (data A).rot) +
      Multiset.ofList (reflectionPlus.map (data A).refl) +
      Multiset.ofList (reflectionMinus.map (data A).refl)
  signedSum_eq_zero :
    rotationPlus.sum - rotationMinus.sum +
      reflectionPlus.sum - reflectionMinus.sum = 0

/-- The natural-language ordering interface, now as an exact multiset theorem. -/
theorem hasProductOneOrdering_of_balancedSignedAssignment
    (S : Multiset (Group A)) (h : BalancedSignedAssignment S) :
    HasProductOneOrdering S := by
  let word := (data A).balancedSignedWord h.rotationPlus h.rotationMinus
    h.reflectionPlus h.reflectionMinus
  refine ⟨word, ?_, ?_⟩
  · rw [show Multiset.ofList word =
        Multiset.ofList (h.rotationPlus.map (data A).rot) +
        Multiset.ofList (h.rotationMinus.map (data A).rot) +
        Multiset.ofList (h.reflectionPlus.map (data A).refl) +
        Multiset.ofList (h.reflectionMinus.map (data A).refl) by
      exact (data A).multiset_balancedSignedWord _ _ _ _
        h.reflectionLengthEq h.reflectionPlusNonempty]
    exact h.carrier_eq.symm
  · exact (data A).prod_balancedSignedWord_eq_one _ _ _ _
      h.reflectionLengthEq h.reflectionPlusNonempty h.signedSum_eq_zero

/-- Occurrence-labelled lift: a balanced assignment of the exact selected
multiset yields a product-one selection. -/
theorem isProductOneSelection_of_balancedSignedAssignment
    (s : List (Group A)) (I : Selection s)
    (h : BalancedSignedAssignment (selectedMultiset s I)) :
    IsProductOneSelection s I :=
  hasProductOneOrdering_of_balancedSignedAssignment _ h

theorem hasProductOneSubsequenceOfCard_of_balancedSignedAssignment
    (s : List (Group A)) (I : Selection s) (k : ℕ)
    (hcard : I.card = k)
    (h : BalancedSignedAssignment (selectedMultiset s I)) :
    HasProductOneSubsequenceOfCard s k := by
  exact ⟨I, hcard, isProductOneSelection_of_balancedSignedAssignment s I h⟩

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.GDihedralData.prod_balancedSignedWord
#print axioms GaoLean.GDihedralData.multiset_balancedSignedWord
#print axioms GaoLean.GDihedralData.prod_balancedSignedWord_eq_one
#print axioms GaoLean.ConcreteGDihedral.hasProductOneOrdering_of_balancedSignedAssignment
#print axioms GaoLean.ConcreteGDihedral.isProductOneSelection_of_balancedSignedAssignment
#print axioms GaoLean.ConcreteGDihedral.hasProductOneSubsequenceOfCard_of_balancedSignedAssignment
