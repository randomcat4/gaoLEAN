import GaoLean.PGQuotient

/-!
# Concrete quotient guard for PG-O3

The natural-language guard keeps all reflections and all rotations outside
`K`, projects them to the generalized-dihedral quotient by `K`, and forbids a
product-one subsequence containing a reflection.  Definitions here quantify
over original occurrence labels, so repeated values never collapse.
-/

namespace GaoLean

section ProductOneTransport

variable {G H : Type*} [Monoid G] [Monoid H]

/-- A product-one multiset stays product one after applying a monoid
homomorphism. -/
theorem hasProductOneOrdering_map (f : G →* H) {S : Multiset G}
    (hS : HasProductOneOrdering S) :
    HasProductOneOrdering (S.map f) := by
  rcases hS with ⟨word, hword, hprod⟩
  refine ⟨word.map f, ?_, ?_⟩
  · simpa using congrArg (Multiset.map f) hword
  · calc
      (word.map f).prod = f word.prod := (f.map_list_prod word).symm
      _ = 1 := by rw [hprod, map_one]

private theorem prod_filter_ne_one [DecidableEq G] (word : List G) :
    (word.filter fun g => decide (g ≠ 1)).prod = word.prod := by
  have hfilter :
      word.filter (fun g => decide (g ≠ 1)) =
        word.filter (fun g => g != 1) := by
    congr 1
    funext g
    by_cases hg : g = 1 <;> simp [hg]
  rw [hfilter]
  exact List.prod_filter_bne_one word

/-- Deleting identity entries from a product-one multiset preserves a
product-one ordering. -/
theorem hasProductOneOrdering_filter_ne_one [DecidableEq G]
    {S : Multiset G} (hS : HasProductOneOrdering S) :
    HasProductOneOrdering (S.filter fun g => g ≠ 1) := by
  rcases hS with ⟨word, hword, hprod⟩
  refine ⟨word.filter (fun g => decide (g ≠ 1)), ?_, ?_⟩
  · simpa using congrArg (Multiset.filter fun g => g ≠ 1) hword
  · rw [prod_filter_ne_one, hprod]

end ProductOneTransport

namespace ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

/-- Occurrence-type formulation of a reflection-containing quotient block.
It is convenient for transformations which preserve labels but change their
values. -/
def HasReflectionContainingQuotientProductOneOn
    {Ω : Type*} [Fintype Ω] (X : Ω → Group A) (K : AddSubgroup A) : Prop :=
  ∃ I : Finset Ω,
    (∀ i ∈ I, quotientMap K (X i) ≠ 1) ∧
    (∃ i ∈ I, ¬IsRotation (X i)) ∧
    HasProductOneOrdering ((I.1.map X).map (quotientMap K))

def QuotientNoReflectionOn
    {Ω : Type*} [Fintype Ω] (X : Ω → Group A) (K : AddSubgroup A) : Prop :=
  ¬HasReflectionContainingQuotientProductOneOn X K

/-- Original occurrence labels which survive in the quotient carrier: all
reflections and precisely the rotations whose coordinate is outside `K`. -/
noncomputable def quotientCarrierOccurrences
    (s : List (Group A)) (K : AddSubgroup A) : Selection s := by
  classical
  exact Finset.univ.filter fun i =>
    quotientMap K (occurrenceValue s i) ≠ 1

theorem mem_quotientCarrierOccurrences_iff
    (s : List (Group A)) (K : AddSubgroup A) (i : Occurrence s) :
    i ∈ quotientCarrierOccurrences s K ↔
      quotientMap K (occurrenceValue s i) ≠ 1 := by
  classical
  simp [quotientCarrierOccurrences]

/-- A reflection-containing product-one block in the quotient carrier,
quantified over the original labelled occurrences. -/
def HasReflectionContainingQuotientProductOne
    (s : List (Group A)) (K : AddSubgroup A) : Prop :=
  ∃ I : Selection s,
    I ⊆ quotientCarrierOccurrences s K ∧
    (∃ i ∈ I, ¬IsRotation (occurrenceValue s i)) ∧
    HasProductOneOrdering
      ((selectedMultiset s I).map (quotientMap K))

/-- Concrete realization of the previously abstract `quotientNoReflection`
guard. -/
def QuotientNoReflection
    (s : List (Group A)) (K : AddSubgroup A) : Prop :=
  ¬HasReflectionContainingQuotientProductOne s K

/-- The list-facing guard is definitionally faithful to the generic
occurrence-label formulation.  This bridge is what permits value transforms
without replacing occurrence labels by a value set. -/
theorem hasReflectionContainingQuotientProductOne_iff_on
    (s : List (Group A)) (K : AddSubgroup A) :
    HasReflectionContainingQuotientProductOne s K ↔
      HasReflectionContainingQuotientProductOneOn (occurrenceValue s) K := by
  constructor
  · rintro ⟨I, hcarrier, href, hprod⟩
    refine ⟨I, ?_, href, ?_⟩
    · intro i hi
      exact (mem_quotientCarrierOccurrences_iff s K i).1 (hcarrier hi)
    · simpa [selectedMultiset] using hprod
  · rintro ⟨I, hcarrier, href, hprod⟩
    refine ⟨I, ?_, href, ?_⟩
    · intro i hi
      exact (mem_quotientCarrierOccurrences_iff s K i).2 (hcarrier i hi)
    · simpa [selectedMultiset] using hprod

theorem quotientNoReflection_iff_on
    (s : List (Group A)) (K : AddSubgroup A) :
    QuotientNoReflection s K ↔
      QuotientNoReflectionOn (occurrenceValue s) K := by
  exact not_congr (hasReflectionContainingQuotientProductOne_iff_on s K)

/-- The carrier predicate is exactly “reflection or rotation outside `K`”. -/
theorem mem_quotientCarrierOccurrences_iff_reflection_or_rotation_outside
    (s : List (Group A)) (K : AddSubgroup A) (i : Occurrence s) :
    i ∈ quotientCarrierOccurrences s K ↔
      (¬IsRotation (occurrenceValue s i) ∨
        coordinate (occurrenceValue s i) ∉ K) := by
  rw [mem_quotientCarrierOccurrences_iff]
  rw [Ne, quotientMap_eq_one_iff]
  tauto

/-- A reflection-containing block modulo a finer subgroup `H` projects to
one modulo `K`; rotations from `K/H` become identities and are deleted.  The
new selection is a filter of the old finite label set, hence no occurrence is
reused. -/
theorem hasReflectionContainingQuotientProductOne_mono
    (s : List (Group A)) (H K : AddSubgroup A) (hHK : H ≤ K)
    (hblock : HasReflectionContainingQuotientProductOne s H) :
    HasReflectionContainingQuotientProductOne s K := by
  classical
  rcases hblock with ⟨I, hIcarrier, ⟨r, hrI, hrRefl⟩, hprodH⟩
  let J : Selection s := I.filter fun i =>
    quotientMap K (occurrenceValue s i) ≠ 1
  have hrK : quotientMap K (occurrenceValue s r) ≠ 1 := by
    intro hrOne
    exact hrRefl (quotientMap_eq_one_iff K _ |>.1 hrOne).1
  have hrJ : r ∈ J := by simp [J, hrI, hrK]
  have hprodMapped : HasProductOneOrdering
      (((selectedMultiset s I).map (quotientMap H)).map
        (quotientBetweenMap H K hHK)) :=
    hasProductOneOrdering_map (quotientBetweenMap H K hHK) hprodH
  have hmapEq :
      (((selectedMultiset s I).map (quotientMap H)).map
          (quotientBetweenMap H K hHK)) =
        (selectedMultiset s I).map (quotientMap K) := by
    simp only [Multiset.map_map]
    have hfun :
        (quotientBetweenMap H K hHK : Group (A ⧸ H) → Group (A ⧸ K)) ∘
            (quotientMap H : Group A → Group (A ⧸ H)) =
          (quotientMap K : Group A → Group (A ⧸ K)) := by
      funext g
      exact quotientBetweenMap_quotientMap H K hHK g
    rw [hfun]
  rw [hmapEq] at hprodMapped
  have hfiltered := hasProductOneOrdering_filter_ne_one hprodMapped
  have hselectedEq :
      ((selectedMultiset s I).map (quotientMap K)).filter (fun g => g ≠ 1) =
        (selectedMultiset s J).map (quotientMap K) := by
    change ((selectedMultiset s I).map (quotientMap K)).filter
        (fun g => g ≠ 1) =
      (selectedMultiset s (I.filter fun i =>
        quotientMap K (occurrenceValue s i) ≠ 1)).map (quotientMap K)
    rw [Multiset.filter_map, selectedMultiset, Multiset.filter_map,
      selectedMultiset, Finset.filter_val]
    rfl
  rw [hselectedEq] at hfiltered
  refine ⟨J, ?_, ⟨r, hrJ, hrRefl⟩, hfiltered⟩
  intro i hiJ
  have hiK : quotientMap K (occurrenceValue s i) ≠ 1 := by
    exact (by simpa [J] using hiJ : i ∈ I ∧
      quotientMap K (occurrenceValue s i) ≠ 1).2
  exact (mem_quotientCarrierOccurrences_iff s K i).2 hiK

/-- Absence of a reflection-containing quotient block descends from `K` to
every subgroup `H ≤ K`. -/
theorem quotientNoReflection_anti
    (s : List (Group A)) (H K : AddSubgroup A) (hHK : H ≤ K)
    (hguard : QuotientNoReflection s K) :
    QuotientNoReflection s H := by
  intro hH
  exact hguard (hasReflectionContainingQuotientProductOne_mono s H K hHK hH)

/-- Label-generic form of quotient descent and identity deletion. -/
theorem hasReflectionContainingQuotientProductOneOn_mono
    {Ω : Type*} [Fintype Ω] (X : Ω → Group A)
    (H K : AddSubgroup A) (hHK : H ≤ K)
    (hblock : HasReflectionContainingQuotientProductOneOn X H) :
    HasReflectionContainingQuotientProductOneOn X K := by
  classical
  rcases hblock with ⟨I, hIcarrier, ⟨r, hrI, hrRefl⟩, hprodH⟩
  let J : Finset Ω := I.filter fun i => quotientMap K (X i) ≠ 1
  have hrK : quotientMap K (X r) ≠ 1 := by
    intro hrOne
    exact hrRefl (quotientMap_eq_one_iff K _ |>.1 hrOne).1
  have hrJ : r ∈ J := by simp [J, hrI, hrK]
  have hprodMapped : HasProductOneOrdering
      ((((I.1.map X).map (quotientMap H)).map
        (quotientBetweenMap H K hHK))) :=
    hasProductOneOrdering_map (quotientBetweenMap H K hHK) hprodH
  have hmapEq :
      ((((I.1.map X).map (quotientMap H)).map
          (quotientBetweenMap H K hHK))) =
        (I.1.map X).map (quotientMap K) := by
    simp only [Multiset.map_map]
    have hfun :
        (quotientBetweenMap H K hHK : Group (A ⧸ H) → Group (A ⧸ K)) ∘
            (quotientMap H : Group A → Group (A ⧸ H)) ∘ X =
          (quotientMap K : Group A → Group (A ⧸ K)) ∘ X := by
      funext i
      exact quotientBetweenMap_quotientMap H K hHK (X i)
    rw [hfun]
  rw [hmapEq] at hprodMapped
  have hfiltered := hasProductOneOrdering_filter_ne_one hprodMapped
  have hselectedEq :
      (((I.1.map X).map (quotientMap K)).filter (fun g => g ≠ 1)) =
        (J.1.map X).map (quotientMap K) := by
    change (((I.1.map X).map (quotientMap K)).filter (fun g => g ≠ 1)) =
      (((I.filter fun i => quotientMap K (X i) ≠ 1).1.map X).map
        (quotientMap K))
    rw [Multiset.filter_map, Multiset.filter_map, Finset.filter_val]
    rfl
  rw [hselectedEq] at hfiltered
  exact ⟨J, (fun i hi => (by simpa [J] using hi : i ∈ I ∧
    quotientMap K (X i) ≠ 1).2), ⟨r, hrJ, hrRefl⟩, hfiltered⟩

theorem quotientNoReflectionOn_anti
    {Ω : Type*} [Fintype Ω] (X : Ω → Group A)
    (H K : AddSubgroup A) (hHK : H ≤ K)
    (hguard : QuotientNoReflectionOn X K) :
    QuotientNoReflectionOn X H := by
  intro hH
  exact hguard
    (hasReflectionContainingQuotientProductOneOn_mono X H K hHK hH)

/-- Translate rotation coordinates by `-α`, leaving reflections unchanged. -/
noncomputable def translateRotations (α : A) (g : Group A) : Group A := by
  classical
  exact if IsRotation g then rotation A (Multiplicative.ofAdd (-α)) * g else g

theorem isRotation_translateRotations_iff (α : A) (g : Group A) :
    IsRotation (translateRotations α g) ↔ IsRotation g := by
  classical
  by_cases hg : IsRotation g
  · have hright : g.right = 1 := hg
    rw [translateRotations, if_pos hg]
    change (rotation A (Multiplicative.ofAdd (-α)) * g).right = 1 ↔
      g.right = 1
    have hrotRight : (rotation A (Multiplicative.ofAdd (-α))).right = 1 := rfl
    rw [SemidirectProduct.mul_right, hrotRight, one_mul]
  · rw [translateRotations, if_neg hg]

/-- Translation by a kernel element is invisible after quotienting by `K`. -/
theorem quotientMap_translateRotations (K : AddSubgroup A) {α : A}
    (hα : α ∈ K) (g : Group A) :
    quotientMap K (translateRotations α g) = quotientMap K g := by
  classical
  by_cases hg : IsRotation g
  · rw [translateRotations, if_pos hg, map_mul, quotientMap_rotation]
    have hneg : -α ∈ K := K.neg_mem hα
    have hz : QuotientAddGroup.mk' K (-α) = 0 :=
      (QuotientAddGroup.eq_zero_iff (-α)).2 hneg
    rw [hz]
    change rotation (A ⧸ K) 1 * quotientMap K g = quotientMap K g
    rw [map_one, one_mul]
  · rw [translateRotations, if_neg hg]

/-- At a fixed quotient, translating all rotation values by a kernel element
preserves the quotient guard on the same occurrence-label type. -/
theorem quotientNoReflectionOn_translateRotations_iff
    {Ω : Type*} [Fintype Ω] (X : Ω → Group A)
    (K : AddSubgroup A) {α : A} (hα : α ∈ K) :
    QuotientNoReflectionOn (fun i => translateRotations α (X i)) K ↔
      QuotientNoReflectionOn X K := by
  have hblock :
      HasReflectionContainingQuotientProductOneOn
          (fun i => translateRotations α (X i)) K ↔
        HasReflectionContainingQuotientProductOneOn X K := by
    constructor
    · rintro ⟨I, hcarrier, ⟨r, hrI, hrRefl⟩, hprod⟩
      have hmulti :
          ((I.1.map (fun i => translateRotations α (X i))).map
              (quotientMap K)) =
            (I.1.map X).map (quotientMap K) := by
        simp only [Multiset.map_map]
        have hfun :
            (quotientMap K : Group A → Group (A ⧸ K)) ∘
                (fun i => translateRotations α (X i)) =
              (quotientMap K : Group A → Group (A ⧸ K)) ∘ X := by
          funext i
          exact quotientMap_translateRotations K hα (X i)
        rw [hfun]
      rw [hmulti] at hprod
      have hcarrierX : ∀ i ∈ I, quotientMap K (X i) ≠ 1 := by
        intro i hi
        rw [← quotientMap_translateRotations K hα (X i)]
        exact hcarrier i hi
      have hrReflX : ¬IsRotation (X r) := by
        intro hr
        exact hrRefl ((isRotation_translateRotations_iff α (X r)).2 hr)
      exact ⟨I, hcarrierX, ⟨r, hrI, hrReflX⟩, hprod⟩
    · rintro ⟨I, hcarrier, ⟨r, hrI, hrRefl⟩, hprod⟩
      have hmulti :
          ((I.1.map (fun i => translateRotations α (X i))).map
              (quotientMap K)) =
            (I.1.map X).map (quotientMap K) := by
        simp only [Multiset.map_map]
        have hfun :
            (quotientMap K : Group A → Group (A ⧸ K)) ∘
                (fun i => translateRotations α (X i)) =
              (quotientMap K : Group A → Group (A ⧸ K)) ∘ X := by
          funext i
          exact quotientMap_translateRotations K hα (X i)
        rw [hfun]
      have hcarrierT : ∀ i ∈ I,
          quotientMap K (translateRotations α (X i)) ≠ 1 := by
        intro i hi
        rw [quotientMap_translateRotations K hα (X i)]
        exact hcarrier i hi
      have hrReflT : ¬IsRotation (translateRotations α (X r)) := by
        intro hr
        exact hrRefl ((isRotation_translateRotations_iff α (X r)).1 hr)
      have hprodT : HasProductOneOrdering
          ((I.1.map (fun i => translateRotations α (X i))).map
            (quotientMap K)) := by
        rw [hmulti]
        exact hprod
      exact ⟨I, hcarrierT, ⟨r, hrI, hrReflT⟩, hprodT⟩
  exact not_congr hblock

/-- Exact recursive guard transfer used in the rotation non-full branch:
translate by `α ∈ K`, then descend to any `H ≤ K`. -/
theorem quotientNoReflectionOn_translate_anti
    {Ω : Type*} [Fintype Ω] (X : Ω → Group A)
    (H K : AddSubgroup A) (hHK : H ≤ K) {α : A} (hα : α ∈ K)
    (hguard : QuotientNoReflectionOn X K) :
    QuotientNoReflectionOn (fun i => translateRotations α (X i)) H := by
  have hguardK :
      QuotientNoReflectionOn (fun i => translateRotations α (X i)) K :=
    (quotientNoReflectionOn_translateRotations_iff X K hα).2 hguard
  exact quotientNoReflectionOn_anti _ H K hHK hguardK

/-- List-facing entry to the recursive guard transfer.  The output remains
indexed by the source list's exact occurrences, with only their values
translated. -/
theorem quotientNoReflection_translate_occurrences_anti
    (s : List (Group A)) (H K : AddSubgroup A) (hHK : H ≤ K)
    {α : A} (hα : α ∈ K) (hguard : QuotientNoReflection s K) :
    QuotientNoReflectionOn
      (fun i : Occurrence s => translateRotations α (occurrenceValue s i)) H := by
  apply quotientNoReflectionOn_translate_anti (occurrenceValue s) H K hHK hα
  exact (quotientNoReflection_iff_on s K).1 hguard

end ConcreteGDihedral

/-- The controller statement with its natural-language quotient guard, rather
than an arbitrary predicate parameter. -/
def ConcreteZRStatement {A : Type*} [AddCommGroup A] [Fintype A]
    (X : List (ConcreteGDihedral.Group A))
    (Q D a b : ℕ) (K : AddSubgroup A) : Prop :=
  ZRStatement ConcreteGDihedral.QuotientNoReflection X Q D a b K

end GaoLean

#print axioms GaoLean.hasProductOneOrdering_map
#print axioms GaoLean.hasProductOneOrdering_filter_ne_one
#print axioms GaoLean.ConcreteGDihedral.mem_quotientCarrierOccurrences_iff_reflection_or_rotation_outside
#print axioms GaoLean.ConcreteGDihedral.hasReflectionContainingQuotientProductOne_mono
#print axioms GaoLean.ConcreteGDihedral.quotientNoReflection_anti
#print axioms GaoLean.ConcreteGDihedral.hasReflectionContainingQuotientProductOne_iff_on
#print axioms GaoLean.ConcreteGDihedral.quotientNoReflection_iff_on
#print axioms GaoLean.ConcreteGDihedral.hasReflectionContainingQuotientProductOneOn_mono
#print axioms GaoLean.ConcreteGDihedral.quotientMap_translateRotations
#print axioms GaoLean.ConcreteGDihedral.quotientNoReflectionOn_translateRotations_iff
#print axioms GaoLean.ConcreteGDihedral.quotientNoReflectionOn_translate_anti
#print axioms GaoLean.ConcreteGDihedral.quotientNoReflection_translate_occurrences_anti
