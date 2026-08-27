import GaoLean.PGGMOSpectrum
import GaoLean.PGIteratedKneser

/-!
# Setpartition and multiplicity core for DeVos--Goddyn--Mohar

This file supplies the literal finite objects which occur in the
DeVos--Goddyn--Mohar theorem used by GMO.  A setpartition is represented by a
list of finite layers.  `layerSubsumSpectrum P n` chooses `n` *different
layers* and one value from each chosen layer.  Thus repeated values in
different layers retain their multiplicity, while repetitions inside a layer
are collapsed, exactly as in the source definition of a setpartition.

No form of the DGM inequality is assumed here.  The proved results isolate
the recursive exact-`n` spectrum, its full-layer endpoint, quotient-layer
multiplicities, and the two-layer Kneser base case.
-/

namespace GaoLean

open scoped BigOperators Pointwise

variable {A : Type*} [AddCommGroup A] [DecidableEq A]

/-- Every layer of a source setpartition is nonempty. -/
def IsNonemptySetPartition (P : List (Finset A)) : Prop :=
  ∀ B ∈ P, B.Nonempty

/-- The union of all sums obtained by choosing `n` distinct layers and one
element from every chosen layer.  The recursion records whether the first
layer is skipped or used. -/
def layerSubsumSpectrum : List (Finset A) → ℕ → Finset A
  | _, 0 => {0}
  | [], _ + 1 => ∅
  | B :: P, n + 1 =>
      layerSubsumSpectrum P (n + 1) ∪
        (B + layerSubsumSpectrum P n)

@[simp]
theorem layerSubsumSpectrum_zero (P : List (Finset A)) :
    layerSubsumSpectrum P 0 = {0} := by
  cases P <;> rfl

@[simp]
theorem layerSubsumSpectrum_nil_succ (n : ℕ) :
    layerSubsumSpectrum ([] : List (Finset A)) (n + 1) = ∅ := rfl

@[simp]
theorem layerSubsumSpectrum_cons_succ (B : Finset A)
    (P : List (Finset A)) (n : ℕ) :
    layerSubsumSpectrum (B :: P) (n + 1) =
      layerSubsumSpectrum P (n + 1) ∪
        (B + layerSubsumSpectrum P n) := rfl

/-- One cannot select more layers than are present. -/
theorem layerSubsumSpectrum_eq_empty_of_length_lt
    (P : List (Finset A)) (n : ℕ) (h : P.length < n) :
    layerSubsumSpectrum P n = ∅ := by
  induction P generalizing n with
  | nil =>
      obtain rfl | n := n
      · omega
      · rfl
  | cons B P ih =>
      obtain rfl | n := n
      · omega
      · simp only [layerSubsumSpectrum_cons_succ]
        have htail : P.length < n := by simpa using h
        rw [ih (n + 1) (by omega), ih n htail]
        simp

/-- At the full-layer endpoint, the first layer must be used. -/
theorem layerSubsumSpectrum_full_cons (B : Finset A)
    (P : List (Finset A)) :
    layerSubsumSpectrum (B :: P) (B :: P).length =
      B + layerSubsumSpectrum P P.length := by
  simp only [List.length_cons, layerSubsumSpectrum_cons_succ]
  rw [layerSubsumSpectrum_eq_empty_of_length_lt P (P.length + 1) (by omega)]
  simp

/-- The sumset obtained by choosing one element from every layer. -/
def fullLayerSumSpectrum (P : List (Finset A)) : Finset A :=
  layerSubsumSpectrum P P.length

/-- Union of the value sets in all layers. -/
def layerUnion : List (Finset A) → Finset A
  | [] => ∅
  | B :: P => B ∪ layerUnion P

/-- Choosing exactly one layer and one value gives the union of the layers. -/
theorem layerSubsumSpectrum_one (P : List (Finset A)) :
    layerSubsumSpectrum P 1 = layerUnion P := by
  induction P with
  | nil => rfl
  | cons B P ih =>
      simp only [layerSubsumSpectrum_cons_succ, layerSubsumSpectrum_zero,
        layerUnion, ih]
      have hB0 : B + ({0} : Finset A) = B := by
        change B + (0 : Finset A) = B
        exact add_zero B
      rw [hB0]
      exact Finset.union_comm _ _

@[simp]
theorem fullLayerSumSpectrum_nil :
    fullLayerSumSpectrum ([] : List (Finset A)) = {0} := rfl

@[simp]
theorem fullLayerSumSpectrum_cons (B : Finset A)
    (P : List (Finset A)) :
    fullLayerSumSpectrum (B :: P) = B + fullLayerSumSpectrum P := by
  exact layerSubsumSpectrum_full_cons B P

/-- The exact full-layer spectrum agrees with the recursive iterated sumset
used by the Kneser layer. -/
theorem fullLayerSumSpectrum_eq_iteratedFinsetSum
    (P : List (Finset A)) :
    fullLayerSumSpectrum P = iteratedFinsetSum P := by
  induction P with
  | nil => rfl
  | cons B P ih =>
      rw [fullLayerSumSpectrum_cons, iteratedFinsetSum_cons, ih]

/-- Exact-`n` layer spectra commute with additive homomorphisms.  This is the
quotient transport used by the stabilizer-reduction step in DGM. -/
theorem image_layerSubsumSpectrum
    {B : Type*} [AddCommGroup B] [DecidableEq B]
    (f : A →+ B) (P : List (Finset A)) (n : ℕ) :
    (layerSubsumSpectrum P n).image f =
      layerSubsumSpectrum (P.map fun C ↦ C.image f) n := by
  induction P generalizing n with
  | nil =>
      obtain rfl | n := n
      · simp [layerSubsumSpectrum]
      · simp [layerSubsumSpectrum]
  | cons C P ih =>
      obtain rfl | n := n
      · simp [layerSubsumSpectrum]
      · simp only [layerSubsumSpectrum_cons_succ, List.map_cons,
          Finset.image_union, Finset.image_add]
        rw [ih (n + 1), ih n]

/-- A nonempty setpartition has at least one exact `n`-layer sum whenever
`n` does not exceed the number of layers. -/
theorem layerSubsumSpectrum_nonempty
    (P : List (Finset A)) (hP : IsNonemptySetPartition P)
    (n : ℕ) (hn : n ≤ P.length) :
    (layerSubsumSpectrum P n).Nonempty := by
  induction P generalizing n with
  | nil =>
      have : n = 0 := by simpa using hn
      subst n
      simp
  | cons B P ih =>
      obtain rfl | n := n
      · simp
      · have hB : B.Nonempty := hP B (by simp)
        have hP' : IsNonemptySetPartition P := by
          intro C hC
          exact hP C (by simp [hC])
        have hn' : n ≤ P.length := by simpa using hn
        exact (hB.add (ih hP' n hn')).mono (by
          intro x hx
          exact Finset.mem_union_right _ hx)

/-- The projected finite set contributed by a single layer modulo `K`. -/
noncomputable def quotientLayer (K : AddSubgroup A) (B : Finset A) :
    Finset (A ⧸ K) := by
  classical
  exact B.image ((↑) : A → A ⧸ K)

@[simp]
theorem mem_quotientLayer_iff (K : AddSubgroup A) (B : Finset A)
    (q : A ⧸ K) :
    q ∈ quotientLayer K B ↔ ∃ x ∈ B, (x : A ⧸ K) = q := by
  classical
  simp [quotientLayer]

theorem quotientLayer_nonempty (K : AddSubgroup A) (B : Finset A)
    (hB : B.Nonempty) : (quotientLayer K B).Nonempty := by
  classical
  obtain ⟨x, hx⟩ := hB
  exact ⟨(x : A ⧸ K), (mem_quotientLayer_iff K B _).2 ⟨x, hx, rfl⟩⟩

/-- The DGM multiplicity of a quotient value: the number of projected layers
which contain that value.  A layer contributes at most once even if several
of its original elements collapse modulo `K`. -/
noncomputable def quotientLayerMultiplicity
    (K : AddSubgroup A) (P : List (Finset A)) (q : A ⧸ K) : ℕ := by
  classical
  exact P.foldr
    (fun B multiplicity ↦
      if q ∈ quotientLayer K B then multiplicity + 1 else multiplicity) 0

theorem quotientLayerMultiplicity_cons_of_mem
    (K : AddSubgroup A) (B : Finset A) (P : List (Finset A))
    (q : A ⧸ K) (hq : q ∈ quotientLayer K B) :
    quotientLayerMultiplicity K (B :: P) q =
      1 + quotientLayerMultiplicity K P q := by
  classical
  have hq' : ∃ x ∈ B, (x : A ⧸ K) = q :=
    (mem_quotientLayer_iff K B q).1 hq
  simp [quotientLayerMultiplicity, hq', add_comm]

theorem quotientLayerMultiplicity_cons_of_not_mem
    (K : AddSubgroup A) (B : Finset A) (P : List (Finset A))
    (q : A ⧸ K) (hq : q ∉ quotientLayer K B) :
    quotientLayerMultiplicity K (B :: P) q =
      quotientLayerMultiplicity K P q := by
  classical
  have hq' : ¬∃ x ∈ B, (x : A ⧸ K) = q := by
    simpa only [mem_quotientLayer_iff] using hq
  simp [quotientLayerMultiplicity, hq']

/-- Every quotient value occurs in at most one copy per layer. -/
theorem quotientLayerMultiplicity_le_length
    (K : AddSubgroup A) (P : List (Finset A)) (q : A ⧸ K) :
    quotientLayerMultiplicity K P q ≤ P.length := by
  classical
  induction P with
  | nil => simp [quotientLayerMultiplicity]
  | cons B P ih =>
      by_cases hq : q ∈ quotientLayer K B
      · rw [quotientLayerMultiplicity_cons_of_mem K B P q hq]
        simp only [List.length_cons]
        omega
      · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hq]
        exact ih.trans (Nat.le_succ _)

/-- Double counting the incidences `(layer, quotient value in that layer)`.
This is the exact multiplicity accounting term in the DGM lower bound. -/
theorem sum_quotientLayerMultiplicity
    (K : AddSubgroup A) [Fintype (A ⧸ K)] (P : List (Finset A)) :
    (∑ q : A ⧸ K, quotientLayerMultiplicity K P q) =
      (P.map fun B ↦ (quotientLayer K B).card).sum := by
  classical
  induction P with
  | nil => simp [quotientLayerMultiplicity]
  | cons B P ih =>
      calc
        (∑ q : A ⧸ K, quotientLayerMultiplicity K (B :: P) q) =
            ∑ q : A ⧸ K,
              ((if q ∈ quotientLayer K B then 1 else 0) +
                quotientLayerMultiplicity K P q) := by
                  apply Finset.sum_congr rfl
                  intro q _
                  by_cases hq : q ∈ quotientLayer K B
                  · simp [hq, quotientLayerMultiplicity_cons_of_mem]
                  · simp [hq, quotientLayerMultiplicity_cons_of_not_mem]
        _ = (∑ q : A ⧸ K, if q ∈ quotientLayer K B then 1 else 0) +
              ∑ q : A ⧸ K, quotientLayerMultiplicity K P q := by
                rw [Finset.sum_add_distrib]
        _ = (quotientLayer K B).card +
              (P.map fun C ↦ (quotientLayer K C).card).sum := by
                rw [ih]
                rw [← Finset.card_eq_sum_ite
                  (s := quotientLayer K B)
                  (t := (Finset.univ : Finset (A ⧸ K)))
                  (Finset.subset_univ _)]
        _ = ((B :: P).map fun C ↦ (quotientLayer K C).card).sum := by
                simp

/-- A nonempty setpartition has at least one quotient incidence per layer. -/
theorem length_le_sum_quotientLayer_card
    (K : AddSubgroup A) (P : List (Finset A))
    (hP : IsNonemptySetPartition P) :
    P.length ≤ (P.map fun B ↦ (quotientLayer K B).card).sum := by
  classical
  induction P with
  | nil => simp
  | cons B P ih =>
      have hB : B.Nonempty := hP B (by simp)
      have hP' : IsNonemptySetPartition P := by
        intro C hC
        exact hP C (by simp [hC])
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      have hcard : 1 ≤ (quotientLayer K B).card :=
        Finset.card_pos.mpr (quotientLayer_nonempty K B hB)
      have htail := ih hP'
      omega

/-- The capped incidence count which appears in the DGM theorem. -/
noncomputable def dgmCappedMultiplicitySum
    (K : AddSubgroup A) [Finite (A ⧸ K)]
    (P : List (Finset A)) (n : ℕ) : ℕ := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  exact ∑ q : A ⧸ K, min n (quotientLayerMultiplicity K P q)

/-- At the full-layer endpoint the cap is inactive. -/
theorem dgmCappedMultiplicitySum_length
    (K : AddSubgroup A) [Finite (A ⧸ K)] (P : List (Finset A)) :
    dgmCappedMultiplicitySum K P P.length =
      (P.map fun B ↦ (quotientLayer K B).card).sum := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  rw [dgmCappedMultiplicitySum]
  simp_rw [min_eq_right (quotientLayerMultiplicity_le_length K P _)]
  exact sum_quotientLayerMultiplicity K P

/-- The capped DGM incidence term is at least the requested number of layers
for every nonempty setpartition with enough layers. -/
theorem le_dgmCappedMultiplicitySum
    (K : AddSubgroup A) [Finite (A ⧸ K)]
    (P : List (Finset A)) (hP : IsNonemptySetPartition P)
    (n : ℕ) (hn : n ≤ P.length) :
    n ≤ dgmCappedMultiplicitySum K P n := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  have htotal : n ≤ ∑ q : A ⧸ K, quotientLayerMultiplicity K P q := by
    rw [sum_quotientLayerMultiplicity K P]
    exact hn.trans (length_le_sum_quotientLayer_card K P hP)
  by_cases hbig : ∃ q : A ⧸ K, n ≤ quotientLayerMultiplicity K P q
  · obtain ⟨q, hq⟩ := hbig
    rw [dgmCappedMultiplicitySum]
    calc
      n = min n (quotientLayerMultiplicity K P q) := (min_eq_left hq).symm
      _ ≤ ∑ z : A ⧸ K, min n (quotientLayerMultiplicity K P z) := by
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset (A ⧸ K)))
          (f := fun z ↦ min n (quotientLayerMultiplicity K P z))
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ q)
  · push Not at hbig
    rw [dgmCappedMultiplicitySum]
    simp_rw [min_eq_right (Nat.le_of_lt (hbig _))]
    exact htotal

/-- Source occurrences counted in one quotient coset. -/
noncomputable def occurrenceQuotientMultiplicity
    [Fintype A] (xs : List A) (K : AddSubgroup A)
    [Fintype (A ⧸ K)] (q : A ⧸ K) : ℕ := by
  classical
  exact ((Finset.univ : Selection xs).filter fun i ↦
    QuotientAddGroup.mk' K (occurrenceValue xs i) = q).card

/-- Quotient cosets partition the occurrence labels, hence their
multiplicities sum to the source length (not merely the support size). -/
theorem sum_occurrenceQuotientMultiplicity
    [Fintype A] (xs : List A) (K : AddSubgroup A)
    [Fintype (A ⧸ K)] :
    (∑ q : A ⧸ K, occurrenceQuotientMultiplicity xs K q) = xs.length := by
  classical
  have h := Finset.card_eq_sum_card_fiberwise
    (s := (Finset.univ : Selection xs))
    (t := (Finset.univ : Finset (A ⧸ K)))
    (f := fun i ↦ QuotientAddGroup.mk' K (occurrenceValue xs i)) (by simp)
  simpa [occurrenceQuotientMultiplicity] using h.symm

/-- Occurrence multiplicity in the quotient coset represented by `alpha` is
literally the cardinality of the canonical occurrence selection used by the
ordinary GMO concentration interface. -/
theorem occurrenceQuotientMultiplicity_mk_eq_card_occurrencesInAddCoset
    [Fintype A] (xs : List A) (K : AddSubgroup A)
    [Fintype (A ⧸ K)] (alpha : A) :
    occurrenceQuotientMultiplicity xs K (QuotientAddGroup.mk' K alpha) =
      (occurrencesInAddCoset xs K alpha).card := by
  classical
  apply congrArg Finset.card
  ext i
  simp [occurrencesInAddCoset,
    QuotientAddGroup.eq_iff_sub_mem]

/-- Stabilizer subgroup of the full-layer sum spectrum. -/
noncomputable def fullLayerSpectrumStabilizer [Fintype A]
    (P : List (Finset A)) : AddSubgroup A :=
  AddAction.stabilizer A (fullLayerSumSpectrum P : Set A)

/-- A layer projected modulo the stabilizer of a specified finite sumset.
Unlike `quotientLayer`, this specialized definition uses the decidable
stabilizer membership supplied by the finite set itself. -/
def stabilizerQuotientLayer (T B : Finset A) :
    Finset (A ⧸ AddAction.stabilizer A (T : Set A)) :=
  B.image ((↑) : A → A ⧸ AddAction.stabilizer A (T : Set A))

/-- Multiplicity of a quotient value among the projected layers, with the
quotient taken by the stabilizer of `T`. -/
noncomputable def stabilizerLayerMultiplicity
    (T : Finset A) (P : List (Finset A))
    (q : A ⧸ AddAction.stabilizer A (T : Set A)) : ℕ := by
  classical
  exact P.foldr
    (fun B multiplicity ↦
      if q ∈ stabilizerQuotientLayer T B then multiplicity + 1
      else multiplicity) 0

theorem stabilizerLayerMultiplicity_cons_of_mem
    (T B : Finset A) (P : List (Finset A))
    (q : A ⧸ AddAction.stabilizer A (T : Set A))
    (hq : q ∈ stabilizerQuotientLayer T B) :
    stabilizerLayerMultiplicity T (B :: P) q =
      1 + stabilizerLayerMultiplicity T P q := by
  classical
  simp [stabilizerLayerMultiplicity, hq, add_comm]

theorem stabilizerLayerMultiplicity_cons_of_not_mem
    (T B : Finset A) (P : List (Finset A))
    (q : A ⧸ AddAction.stabilizer A (T : Set A))
    (hq : q ∉ stabilizerQuotientLayer T B) :
    stabilizerLayerMultiplicity T (B :: P) q =
      stabilizerLayerMultiplicity T P q := by
  classical
  simp [stabilizerLayerMultiplicity, hq]

theorem stabilizerLayerMultiplicity_le_length
    (T : Finset A) (P : List (Finset A))
    (q : A ⧸ AddAction.stabilizer A (T : Set A)) :
    stabilizerLayerMultiplicity T P q ≤ P.length := by
  classical
  induction P with
  | nil => simp [stabilizerLayerMultiplicity]
  | cons B P ih =>
      by_cases hq : q ∈ stabilizerQuotientLayer T B
      · rw [stabilizerLayerMultiplicity_cons_of_mem T B P q hq]
        simp only [List.length_cons]
        omega
      · rw [stabilizerLayerMultiplicity_cons_of_not_mem T B P q hq]
        exact ih.trans (Nat.le_succ _)

theorem stabilizerLayerMultiplicity_pos_iff_mem_layerUnion
    (T : Finset A) (P : List (Finset A))
    (q : A ⧸ AddAction.stabilizer A (T : Set A)) :
    0 < stabilizerLayerMultiplicity T P q ↔
      q ∈ stabilizerQuotientLayer T (layerUnion P) := by
  classical
  induction P with
  | nil => simp [stabilizerLayerMultiplicity, layerUnion,
      stabilizerQuotientLayer]
  | cons B P ih =>
      by_cases hq : q ∈ stabilizerQuotientLayer T B
      · rw [stabilizerLayerMultiplicity_cons_of_mem T B P q hq]
        obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hq
        constructor
        · intro _
          exact Finset.mem_image.mpr ⟨x, Finset.mem_union_left _ hx, hxq⟩
        · intro _
          omega
      · rw [stabilizerLayerMultiplicity_cons_of_not_mem T B P q hq]
        rw [ih]
        constructor
        · intro htail
          obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp htail
          exact Finset.mem_image.mpr ⟨x, Finset.mem_union_right _ hx, hxq⟩
        · intro hunion
          obtain ⟨x, hx, hxq⟩ := Finset.mem_image.mp hunion
          rcases Finset.mem_union.mp hx with hxB | hxP
          · exact False.elim (hq (Finset.mem_image.mpr ⟨x, hxB, hxq⟩))
          · exact Finset.mem_image.mpr ⟨x, hxP, hxq⟩

theorem sum_stabilizerLayerMultiplicity
    [Fintype A] (T : Finset A) (P : List (Finset A)) :
    (∑ q : A ⧸ AddAction.stabilizer A (T : Set A),
        stabilizerLayerMultiplicity T P q) =
      (P.map fun B ↦ (stabilizerQuotientLayer T B).card).sum := by
  classical
  induction P with
  | nil => simp [stabilizerLayerMultiplicity]
  | cons B P ih =>
      calc
        (∑ q, stabilizerLayerMultiplicity T (B :: P) q) =
            ∑ q,
              ((if q ∈ stabilizerQuotientLayer T B then 1 else 0) +
                stabilizerLayerMultiplicity T P q) := by
                  apply Finset.sum_congr rfl
                  intro q _
                  by_cases hq : q ∈ stabilizerQuotientLayer T B
                  · simp [hq, stabilizerLayerMultiplicity_cons_of_mem]
                  · simp [hq, stabilizerLayerMultiplicity_cons_of_not_mem]
        _ = (∑ q, if q ∈ stabilizerQuotientLayer T B then 1 else 0) +
              ∑ q, stabilizerLayerMultiplicity T P q := by
                rw [Finset.sum_add_distrib]
        _ = (stabilizerQuotientLayer T B).card +
              (P.map fun C ↦ (stabilizerQuotientLayer T C).card).sum := by
                rw [ih, ← Finset.card_eq_sum_ite
                  (s := stabilizerQuotientLayer T B)
                  (t := Finset.univ) (Finset.subset_univ _)]
        _ = ((B :: P).map fun C ↦
              (stabilizerQuotientLayer T C).card).sum := by simp

/-- The exact capped multiplicity term in DGM, with its stabilizer tied to
the target spectrum `T`. -/
noncomputable def stabilizerDgmCappedMultiplicitySum
    [Fintype A] (T : Finset A) (P : List (Finset A)) (n : ℕ) : ℕ :=
  ∑ q : A ⧸ AddAction.stabilizer A (T : Set A),
    min n (stabilizerLayerMultiplicity T P q)

theorem stabilizerDgmCappedMultiplicitySum_length
    [Fintype A] (T : Finset A) (P : List (Finset A)) :
    stabilizerDgmCappedMultiplicitySum T P P.length =
      (P.map fun B ↦ (stabilizerQuotientLayer T B).card).sum := by
  classical
  rw [stabilizerDgmCappedMultiplicitySum]
  simp_rw [min_eq_right (stabilizerLayerMultiplicity_le_length T P _)]
  exact sum_stabilizerLayerMultiplicity T P

theorem stabilizerDgmCappedMultiplicitySum_one
    [Fintype A] (T : Finset A) (P : List (Finset A)) :
    stabilizerDgmCappedMultiplicitySum T P 1 =
      (stabilizerQuotientLayer T (layerUnion P)).card := by
  classical
  rw [stabilizerDgmCappedMultiplicitySum]
  calc
    (∑ q, min 1 (stabilizerLayerMultiplicity T P q)) =
        ∑ q,
          if q ∈ stabilizerQuotientLayer T (layerUnion P) then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro q _
            by_cases hq : q ∈ stabilizerQuotientLayer T (layerUnion P)
            · have hm : 1 ≤ stabilizerLayerMultiplicity T P q := by
                exact (stabilizerLayerMultiplicity_pos_iff_mem_layerUnion
                  T P q).2 hq
              simp [hq, min_eq_left hm]
            · have hm : stabilizerLayerMultiplicity T P q = 0 := by
                have := not_lt.mp (mt
                  (stabilizerLayerMultiplicity_pos_iff_mem_layerUnion
                    T P q).1 hq)
                omega
              simp [hq, hm]
    _ = (stabilizerQuotientLayer T (layerUnion P)).card := by
      rw [← Finset.card_eq_sum_ite
        (s := stabilizerQuotientLayer T (layerUnion P))
        (t := Finset.univ) (Finset.subset_univ _)]

/-- Frozen general DGM finite-setpartition statement.  This is the exact
remaining target for arbitrary positive `n ≤ P.length`; defining the target
does not assume it. -/
def DGMSetpartitionBound [Fintype A]
    (P : List (Finset A)) (n : ℕ) : Prop :=
  let T := layerSubsumSpectrum P n
  (stabilizerDgmCappedMultiplicitySum T P n - n + 1) *
      T.addStab.card ≤ T.card

/-- Fully quantified finite DGM theorem, frozen without being assumed. -/
def GeneralDGMSetpartitionTheorem
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] : Prop :=
  ∀ (P : List (Finset A)) (n : ℕ),
    IsNonemptySetPartition P →
    1 ≤ n → n ≤ P.length →
    DGMSetpartitionBound P n

/-- Raw layer multiplicity before any further quotient. -/
def rawLayerMultiplicity (P : List (Finset A)) (x : A) : ℕ :=
  P.foldr (fun B multiplicity ↦
    if x ∈ B then multiplicity + 1 else multiplicity) 0

theorem rawLayerMultiplicity_cons_of_mem
    (B : Finset A) (P : List (Finset A)) (x : A) (hx : x ∈ B) :
    rawLayerMultiplicity (B :: P) x =
      1 + rawLayerMultiplicity P x := by
  simp [rawLayerMultiplicity, hx, Nat.add_comm]

theorem rawLayerMultiplicity_cons_of_not_mem
    (B : Finset A) (P : List (Finset A)) (x : A) (hx : x ∉ B) :
    rawLayerMultiplicity (B :: P) x = rawLayerMultiplicity P x := by
  simp [rawLayerMultiplicity, hx]

theorem rawLayerMultiplicity_pos_iff_mem_layerUnion
    (P : List (Finset A)) (x : A) :
    0 < rawLayerMultiplicity P x ↔ x ∈ layerUnion P := by
  induction P with
  | nil => simp [rawLayerMultiplicity, layerUnion]
  | cons B P ih =>
      by_cases hx : x ∈ B
      · rw [rawLayerMultiplicity_cons_of_mem B P x hx]
        simp [layerUnion, hx]
      · rw [rawLayerMultiplicity_cons_of_not_mem B P x hx, ih]
        simp [layerUnion, hx]

/-- If `x` occurs in more than `n` layers, it can be appended to every
exact-`n` layer sum: among the more than `n` layers containing `x`, at least
one was not used by the given sum.  This is the augmentation step behind the
initial DGM portion. -/
theorem singleton_add_layerSubsumSpectrum_subset_of_lt_multiplicity
    (P : List (Finset A)) (x : A) (n : ℕ)
    (hxn : n < rawLayerMultiplicity P x) :
    ({x} : Finset A) + layerSubsumSpectrum P n ⊆
      layerSubsumSpectrum P (n + 1) := by
  induction P generalizing n with
  | nil => simp [rawLayerMultiplicity] at hxn
  | cons B P ih =>
      obtain rfl | n := n
      · have hxUnion : x ∈ layerUnion (B :: P) :=
          (rawLayerMultiplicity_pos_iff_mem_layerUnion (B :: P) x).1 hxn
        intro z hz
        obtain ⟨u, hu, v, hv, rfl⟩ := Finset.mem_add.mp hz
        simp only [Finset.mem_singleton] at hu
        subst u
        simp only [layerSubsumSpectrum_zero, Finset.mem_singleton] at hv
        subst v
        simpa [layerSubsumSpectrum_one] using hxUnion
      · intro z hz
        obtain ⟨u, hu, y, hy, rfl⟩ := Finset.mem_add.mp hz
        simp only [Finset.mem_singleton] at hu
        subst u
        rw [layerSubsumSpectrum_cons_succ] at hy
        rcases Finset.mem_union.mp hy with hySkip | hyUse
        · by_cases hxB : x ∈ B
          · apply Finset.mem_union_right
            exact Finset.mem_add.mpr ⟨x, hxB, y, hySkip, rfl⟩
          · apply Finset.mem_union_left
            apply ih (n + 1)
            · simpa [rawLayerMultiplicity_cons_of_not_mem B P x hxB] using hxn
            · exact Finset.mem_add.mpr ⟨x, Finset.mem_singleton_self x,
                y, hySkip, rfl⟩
        · obtain ⟨b, hb, s, hs, hys⟩ := Finset.mem_add.mp hyUse
          have htail : n < rawLayerMultiplicity P x := by
            by_cases hxB : x ∈ B
            · rw [rawLayerMultiplicity_cons_of_mem B P x hxB] at hxn
              omega
            · rw [rawLayerMultiplicity_cons_of_not_mem B P x hxB] at hxn
              omega
          have hxs : x + s ∈ layerSubsumSpectrum P (n + 1) := by
            apply ih n htail
            exact Finset.mem_add.mpr ⟨x, Finset.mem_singleton_self x,
              s, hs, rfl⟩
          apply Finset.mem_union_right
          refine Finset.mem_add.mpr ⟨b, hb, x + s, hxs, ?_⟩
          rw [← hys]
          ac_rfl

/-- The head layer together with all values whose layer multiplicity is
already at least `n + 1`.  This is the `X` used in the DGM portion proof. -/
def dgmHeadExtensionSet [Fintype A]
    (B : Finset A) (P : List (Finset A)) (n : ℕ) : Finset A :=
  B ∪ Finset.univ.filter fun x ↦ n + 1 ≤ rawLayerMultiplicity (B :: P) x

/-- Every value in the DGM head-extension set can augment every exact-`n`
tail sum without reusing a layer. -/
theorem dgmHeadExtensionSet_add_tail_subset
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ) :
    dgmHeadExtensionSet B P n + layerSubsumSpectrum P n ⊆
      layerSubsumSpectrum (B :: P) (n + 1) := by
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  rcases Finset.mem_union.mp hx with hxB | hxHeavy
  · apply Finset.mem_union_right
    exact Finset.mem_add.mpr ⟨x, hxB, y, hy, rfl⟩
  · by_cases hxB : x ∈ B
    · apply Finset.mem_union_right
      exact Finset.mem_add.mpr ⟨x, hxB, y, hy, rfl⟩
    · have hmult : n < rawLayerMultiplicity P x := by
        have hxFilter := (Finset.mem_filter.mp hxHeavy).2
        rw [rawLayerMultiplicity_cons_of_not_mem B P x hxB] at hxFilter
        exact Nat.lt_of_succ_le (by simpa [Nat.succ_eq_add_one] using hxFilter)
      apply Finset.mem_union_left
      apply singleton_add_layerSubsumSpectrum_subset_of_lt_multiplicity
        P x n hmult
      exact Finset.mem_add.mpr ⟨x, Finset.mem_singleton_self x, y, hy, rfl⟩

/-- Pointwise capped-multiplicity recurrence.  Passing from cap `n` on the
tail to cap `n+1` after adjoining `B` contributes exactly the indicator of
the DGM head-extension set. -/
theorem min_rawLayerMultiplicity_cons_succ
    [Fintype A] (B : Finset A) (P : List (Finset A)) (x : A) (n : ℕ) :
    min (n + 1) (rawLayerMultiplicity (B :: P) x) =
      (if x ∈ dgmHeadExtensionSet B P n then 1 else 0) +
        min n (rawLayerMultiplicity P x) := by
  classical
  by_cases hxB : x ∈ B
  · rw [rawLayerMultiplicity_cons_of_mem B P x hxB]
    have hxX : x ∈ dgmHeadExtensionSet B P n := by
      exact Finset.mem_union_left _ hxB
    simp only [hxX, if_true]
    omega
  · rw [rawLayerMultiplicity_cons_of_not_mem B P x hxB]
    by_cases hheavy : n + 1 ≤ rawLayerMultiplicity P x
    · have hxX : x ∈ dgmHeadExtensionSet B P n := by
        apply Finset.mem_union_right
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ x, ?_⟩
        rw [rawLayerMultiplicity_cons_of_not_mem B P x hxB]
        exact hheavy
      simp only [hxX, if_true]
      omega
    · have hxX : x ∉ dgmHeadExtensionSet B P n := by
        intro hxX
        rcases Finset.mem_union.mp hxX with hx | hx
        · exact hxB hx
        · apply hheavy
          have hcons := (Finset.mem_filter.mp hx).2
          rw [rawLayerMultiplicity_cons_of_not_mem B P x hxB] at hcons
          exact hcons
      simp only [hxX, if_false]
      omega

noncomputable def rawDgmCappedMultiplicitySum
    [Fintype A] (P : List (Finset A)) (n : ℕ) : ℕ :=
  ∑ x : A, min n (rawLayerMultiplicity P x)

/-- Total capped-multiplicity recurrence corresponding to
`min_rawLayerMultiplicity_cons_succ`. -/
theorem rawDgmCappedMultiplicitySum_cons_succ
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ) :
    rawDgmCappedMultiplicitySum (B :: P) (n + 1) =
      (dgmHeadExtensionSet B P n).card +
        rawDgmCappedMultiplicitySum P n := by
  classical
  unfold rawDgmCappedMultiplicitySum
  simp_rw [min_rawLayerMultiplicity_cons_succ B P]
  rw [Finset.sum_add_distrib]
  congr 1
  rw [← Finset.card_eq_sum_ite
    (s := dgmHeadExtensionSet B P n)
    (t := (Finset.univ : Finset A)) (Finset.subset_univ _)]

/-- Double counting raw layer-value incidences. -/
theorem sum_rawLayerMultiplicity
    [Fintype A] (P : List (Finset A)) :
    (∑ x : A, rawLayerMultiplicity P x) =
      (P.map Finset.card).sum := by
  classical
  induction P with
  | nil => simp [rawLayerMultiplicity]
  | cons B P ih =>
      calc
        (∑ x : A, rawLayerMultiplicity (B :: P) x) =
            ∑ x : A,
              ((if x ∈ B then 1 else 0) + rawLayerMultiplicity P x) := by
                apply Finset.sum_congr rfl
                intro x _
                by_cases hx : x ∈ B
                · simp [hx, rawLayerMultiplicity_cons_of_mem]
                · simp [hx, rawLayerMultiplicity_cons_of_not_mem]
        _ = (∑ x : A, if x ∈ B then 1 else 0) +
              ∑ x : A, rawLayerMultiplicity P x := by
                rw [Finset.sum_add_distrib]
        _ = B.card + (P.map Finset.card).sum := by
                rw [ih, ← Finset.card_eq_sum_ite
                  (s := B) (t := (Finset.univ : Finset A))
                  (Finset.subset_univ _)]
        _ = ((B :: P).map Finset.card).sum := by simp

theorem length_le_sum_layer_card
    (P : List (Finset A)) (hP : IsNonemptySetPartition P) :
    P.length ≤ (P.map Finset.card).sum := by
  induction P with
  | nil => simp
  | cons B P ih =>
      have hB : 1 ≤ B.card := Finset.card_pos.mpr (hP B (by simp))
      have hP' : IsNonemptySetPartition P := by
        intro C hC
        exact hP C (by simp [hC])
      have htail := ih hP'
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      omega

/-- A nonempty setpartition with at least `n` layers has at least `n` raw
incidences even after capping every value multiplicity at `n`. -/
theorem le_rawDgmCappedMultiplicitySum
    [Fintype A] (P : List (Finset A)) (hP : IsNonemptySetPartition P)
    (n : ℕ) (hn : n ≤ P.length) :
    n ≤ rawDgmCappedMultiplicitySum P n := by
  classical
  have htotal : n ≤ ∑ x : A, rawLayerMultiplicity P x := by
    rw [sum_rawLayerMultiplicity]
    exact hn.trans (length_le_sum_layer_card P hP)
  by_cases hbig : ∃ x : A, n ≤ rawLayerMultiplicity P x
  · obtain ⟨x, hx⟩ := hbig
    unfold rawDgmCappedMultiplicitySum
    calc
      n = min n (rawLayerMultiplicity P x) := (min_eq_left hx).symm
      _ ≤ ∑ y : A, min n (rawLayerMultiplicity P y) := by
        exact Finset.single_le_sum
          (s := (Finset.univ : Finset A))
          (f := fun y ↦ min n (rawLayerMultiplicity P y))
          (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ x)
  · push Not at hbig
    unfold rawDgmCappedMultiplicitySum
    simp_rw [min_eq_right (Nat.le_of_lt (hbig _))]
    exact htotal

/-- Well-founded measure used in the DGM induction: requested layer count
plus the size of the corresponding exact-layer spectrum. -/
def dgmInductionMeasure [Fintype A]
    (P : List (Finset A)) (n : ℕ) : ℕ :=
  n + (layerSubsumSpectrum P n).card

/-- If a nonempty left summand plus `Y` is aperiodic, then `Y` itself is
aperiodic.  Translation invariance of `Y` propagates to the whole sumset. -/
theorem addStab_right_eq_singleton_of_addStab_add_eq_singleton
    (X Y : Finset A) (hX : X.Nonempty) (hY : Y.Nonempty)
    (hstab : (X + Y).addStab = {0}) :
    Y.addStab = {0} := by
  apply Finset.eq_singleton_iff_unique_mem.mpr
  refine ⟨hY.zero_mem_addStab, ?_⟩
  intro a ha
  have ha' : a ∈ (X + Y).addStab :=
    Finset.subset_addStab_add_right hX ha
  rw [hstab] at ha'
  simpa using ha'

/-- The aperiodic initial-portion branch of the DGM induction.  Once the
tail satisfies its inductive DGM bound, binary Kneser for
`X + layerSubsumSpectrum P n` and the exact capped-multiplicity recurrence
close the bound for `B :: P`. -/
theorem dgm_cons_bound_of_headExtension_aperiodic
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hB : B.Nonempty) (hP : IsNonemptySetPartition P)
    (hn : n ≤ P.length)
    (hTail : rawDgmCappedMultiplicitySum P n - n + 1 ≤
      (layerSubsumSpectrum P n).card)
    (hC0 : (dgmHeadExtensionSet B P n +
      layerSubsumSpectrum P n).addStab = {0}) :
    rawDgmCappedMultiplicitySum (B :: P) (n + 1) - (n + 1) + 1 ≤
      (layerSubsumSpectrum (B :: P) (n + 1)).card := by
  let X := dgmHeadExtensionSet B P n
  let Y := layerSubsumSpectrum P n
  let C0 := X + Y
  have hX : X.Nonempty := by
    apply hB.mono
    intro x hx
    exact Finset.mem_union_left _ hx
  have hXcard : 1 ≤ X.card := Finset.card_pos.mpr hX
  have hraw : n ≤ rawDgmCappedMultiplicitySum P n :=
    le_rawDgmCappedMultiplicitySum P hP n hn
  have hstabXY : (X + Y).addStab = {0} := by
    simpa [X, Y] using hC0
  have hk := Finset.add_kneser X Y
  have hk' : X.card + Y.card ≤ C0.card + 1 := by
    rw [hstabXY] at hk
    simpa [C0] using hk
  have hC0target : C0 ⊆ layerSubsumSpectrum (B :: P) (n + 1) := by
    simpa [C0, X, Y] using dgmHeadExtensionSet_add_tail_subset B P n
  have hcard : C0.card ≤
      (layerSubsumSpectrum (B :: P) (n + 1)).card :=
    Finset.card_le_card hC0target
  have hrec := rawDgmCappedMultiplicitySum_cons_succ B P n
  change rawDgmCappedMultiplicitySum P n - n + 1 ≤ Y.card at hTail
  change rawDgmCappedMultiplicitySum (B :: P) (n + 1) =
    X.card + rawDgmCappedMultiplicitySum P n at hrec
  omega

/-- The tail exact-`n` problem has strictly smaller DGM induction measure
than the head exact-`n+1` problem.  The nonempty extension set supplies an
injective translate of the tail spectrum inside the initial portion. -/
theorem dgmInductionMeasure_tail_lt
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hB : B.Nonempty) :
    dgmInductionMeasure P n <
      dgmInductionMeasure (B :: P) (n + 1) := by
  let X := dgmHeadExtensionSet B P n
  let Y := layerSubsumSpectrum P n
  let C0 := X + Y
  have hX : X.Nonempty := by
    apply hB.mono
    intro x hx
    exact Finset.mem_union_left _ hx
  have hY_C0 : Y.card ≤ C0.card := by
    exact Finset.card_le_card_add_left hX
  have hC0target : C0 ⊆ layerSubsumSpectrum (B :: P) (n + 1) := by
    simpa [C0, X, Y] using dgmHeadExtensionSet_add_tail_subset B P n
  have hC0card : C0.card ≤
      (layerSubsumSpectrum (B :: P) (n + 1)).card :=
    Finset.card_le_card hC0target
  unfold dgmInductionMeasure
  change n + Y.card <
    n + 1 + (layerSubsumSpectrum (B :: P) (n + 1)).card
  omega

/-- Strong-induction wrapper for the aperiodic initial-portion branch.
It derives the tail aperiodicity and strict measure decrease automatically;
the only branch not handled here is a nontrivial stabilizer of the initial
portion. -/
theorem dgm_cons_bound_of_strongIH_of_headExtension_aperiodic
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hB : B.Nonempty) (hP : IsNonemptySetPartition P)
    (hnpos : 1 ≤ n) (hn : n ≤ P.length)
    (hC0 : (dgmHeadExtensionSet B P n +
      layerSubsumSpectrum P n).addStab = {0})
    (hIH : ∀ (Q : List (Finset A)) (k : ℕ),
      dgmInductionMeasure Q k <
        dgmInductionMeasure (B :: P) (n + 1) →
      IsNonemptySetPartition Q →
      1 ≤ k → k ≤ Q.length →
      (layerSubsumSpectrum Q k).addStab = {0} →
      rawDgmCappedMultiplicitySum Q k - k + 1 ≤
        (layerSubsumSpectrum Q k).card) :
    rawDgmCappedMultiplicitySum (B :: P) (n + 1) - (n + 1) + 1 ≤
      (layerSubsumSpectrum (B :: P) (n + 1)).card := by
  let X := dgmHeadExtensionSet B P n
  let Y := layerSubsumSpectrum P n
  have hX : X.Nonempty := by
    apply hB.mono
    intro x hx
    exact Finset.mem_union_left _ hx
  have hY : Y.Nonempty := by
    exact layerSubsumSpectrum_nonempty P hP n hn
  have hstabXY : (X + Y).addStab = {0} := by
    simpa [X, Y] using hC0
  have hYstab : Y.addStab = {0} :=
    addStab_right_eq_singleton_of_addStab_add_eq_singleton
      X Y hX hY hstabXY
  have hmeasure : dgmInductionMeasure P n <
      dgmInductionMeasure (B :: P) (n + 1) :=
    dgmInductionMeasure_tail_lt B P n hB
  have hTail := hIH P n hmeasure hP hnpos hn (by simpa [Y] using hYstab)
  exact dgm_cons_bound_of_headExtension_aperiodic
    B P n hB hP hn hTail hC0

/-- The canonical initial portion `C₀ = X + Σ_n(P)` in the DGM induction. -/
def dgmInitialPortion [Fintype A]
    (B : Finset A) (P : List (Finset A)) (n : ℕ) : Finset A :=
  dgmHeadExtensionSet B P n + layerSubsumSpectrum P n

/-- Tail layers projected modulo the stabilizer of the canonical initial
portion. -/
def dgmInitialPortionQuotientLayers [Fintype A]
    (B : Finset A) (P : List (Finset A)) (n : ℕ) :=
  P.map fun C ↦ stabilizerQuotientLayer (dgmInitialPortion B P n) C

/-- Stabilizer-aware numerical inequality which says that the canonical
`C₀` is a DGM portion.  It is written without truncated subtraction. -/
def DGMInitialPortionBound [Fintype A]
    (B : Finset A) (P : List (Finset A)) (n : ℕ) : Prop :=
  let X := dgmHeadExtensionSet B P n
  let C0 := dgmInitialPortion B P n
  X.card + C0.addStab.card *
      rawDgmCappedMultiplicitySum
        (dgmInitialPortionQuotientLayers B P n) n ≤
    C0.card + C0.addStab.card * n

/-- The quotient tail spectrum is aperiodic.  The image of the whole initial
portion is aperiodic by construction, and a tail stabilizer would stabilize
its sum with the nonempty projected head-extension set. -/
theorem addStab_initialPortion_quotient_tail_eq_singleton
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hB : B.Nonempty) (hP : IsNonemptySetPartition P)
    (hn : n ≤ P.length) :
    (layerSubsumSpectrum
      (dgmInitialPortionQuotientLayers B P n) n).addStab = {0} := by
  classical
  let X := dgmHeadExtensionSet B P n
  let Y := layerSubsumSpectrum P n
  let C0 := dgmInitialPortion B P n
  let H := AddAction.stabilizer A (C0 : Set A)
  let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
  let Xq := X.image q
  let Yq := Y.image q
  have hX : X.Nonempty := by
    apply hB.mono
    intro x hx
    exact Finset.mem_union_left _ hx
  have hY : Y.Nonempty := layerSubsumSpectrum_nonempty P hP n hn
  have hC0 : C0 = X + Y := by rfl
  have hC0nonempty : C0.Nonempty := by rw [hC0]; exact hX.add hY
  have hsumq : C0.image q = Xq + Yq := by
    calc
      C0.image q = (X + Y).image q :=
        congrArg (fun S : Finset A ↦ S.image q) hC0
      _ = Xq + Yq := by simpa [Xq, Yq] using (Finset.image_add q)
  have hsumqStab : (Xq + Yq).addStab = {0} := by
    rw [← hsumq]
    change (C0.image ((↑) : A → A ⧸
      AddAction.stabilizer A (C0 : Set A))).addStab =
        (0 : Finset (A ⧸ AddAction.stabilizer A (C0 : Set A)))
    simpa [H, q] using Finset.addStab_image_coe_quotient hC0nonempty
  have hXq : Xq.Nonempty := hX.image q
  have hYq : Yq.Nonempty := hY.image q
  have hYqStab : Yq.addStab = {0} :=
    addStab_right_eq_singleton_of_addStab_add_eq_singleton
      Xq Yq hXq hYq hsumqStab
  have hspectrum :
      layerSubsumSpectrum (P.map fun C ↦ C.image q) n = Yq := by
    simpa [Y, Yq] using (image_layerSubsumSpectrum q P n).symm
  change (layerSubsumSpectrum (P.map fun C ↦ C.image q) n).addStab = {0}
  rw [hspectrum]
  exact hYqStab

/-- Conditional construction of the canonical initial portion.  An
inductive DGM bound for the projected tail, together with quotient Kneser,
lifts exactly to `DGMInitialPortionBound`. -/
theorem dgmInitialPortionBound_of_quotient_tail_bound
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hB : B.Nonempty) (hP : IsNonemptySetPartition P)
    (hn : n ≤ P.length)
    (hTailQ :
      rawDgmCappedMultiplicitySum
          (dgmInitialPortionQuotientLayers B P n) n - n + 1 ≤
        (layerSubsumSpectrum
          (dgmInitialPortionQuotientLayers B P n) n).card) :
    DGMInitialPortionBound B P n := by
  classical
  let X := dgmHeadExtensionSet B P n
  let Y := layerSubsumSpectrum P n
  let C0 := dgmInitialPortion B P n
  let H := AddAction.stabilizer A (C0 : Set A)
  let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
  let Pq := dgmInitialPortionQuotientLayers B P n
  let Xq := X.image q
  let Yq := Y.image q
  have hX : X.Nonempty := by
    apply hB.mono
    intro x hx
    exact Finset.mem_union_left _ hx
  have hY : Y.Nonempty := layerSubsumSpectrum_nonempty P hP n hn
  have hC0 : C0 = X + Y := by rfl
  have hC0nonempty : C0.Nonempty := by rw [hC0]; exact hX.add hY
  have hPq : IsNonemptySetPartition Pq := by
    intro D hD
    obtain ⟨C, hCP, rfl⟩ := List.mem_map.mp (by
      simpa [Pq, dgmInitialPortionQuotientLayers] using hD)
    exact (hP C hCP).image q
  have hrawQ : n ≤ rawDgmCappedMultiplicitySum Pq n := by
    apply le_rawDgmCappedMultiplicitySum Pq hPq n
    have hlen : Pq.length = P.length := by
      simp [Pq, dgmInitialPortionQuotientLayers]
    rw [hlen]
    exact hn
  have hspectrum : layerSubsumSpectrum Pq n = Yq := by
    simpa [Pq, H, q, C0, dgmInitialPortionQuotientLayers,
      stabilizerQuotientLayer, Y, Yq] using
        (image_layerSubsumSpectrum q P n).symm
  have hTailQ' : rawDgmCappedMultiplicitySum Pq n - n + 1 ≤ Yq.card := by
    change rawDgmCappedMultiplicitySum Pq n - n + 1 ≤
      (layerSubsumSpectrum Pq n).card at hTailQ
    rw [hspectrum] at hTailQ
    exact hTailQ
  have hsumq : C0.image q = Xq + Yq := by
    calc
      C0.image q = (X + Y).image q :=
        congrArg (fun S : Finset A ↦ S.image q) hC0
      _ = Xq + Yq := by simpa [Xq, Yq] using (Finset.image_add q)
  have hsumqStab : (Xq + Yq).addStab = {0} := by
    rw [← hsumq]
    change (C0.image ((↑) : A → A ⧸
      AddAction.stabilizer A (C0 : Set A))).addStab =
        (0 : Finset (A ⧸ AddAction.stabilizer A (C0 : Set A)))
    simpa [H, q] using Finset.addStab_image_coe_quotient hC0nonempty
  have hk := Finset.add_kneser Xq Yq
  have hk' : Xq.card + Yq.card ≤ (C0.image q).card + 1 := by
    rw [hsumqStab] at hk
    simpa [hsumq] using hk
  clear hk
  have hcardC0 : C0.addStab.card * (C0.image q).card = C0.card := by
    simpa [H, q] using Finset.card_addStab_add_card_image_coe' C0 C0
  have hcardX : C0.addStab.card * Xq.card =
      (X + C0.addStab).card := by
    simpa [H, q, Xq] using Finset.card_addStab_add_card_image_coe' X C0
  have hXle : X.card ≤ C0.addStab.card * Xq.card := by
    rw [hcardX]
    exact Finset.card_le_card_add_right
      ⟨0, hC0nonempty.zero_mem_addStab⟩
  have htailRearr : rawDgmCappedMultiplicitySum Pq n + 1 ≤
      n + Yq.card := by omega
  have htailMul := Nat.mul_le_mul_left C0.addStab.card htailRearr
  have hmul := Nat.mul_le_mul_left C0.addStab.card hk'
  simp only [Nat.mul_add, Nat.mul_one] at htailMul hmul
  unfold DGMInitialPortionBound
  dsimp only
  change X.card + C0.addStab.card *
      rawDgmCappedMultiplicitySum Pq n ≤
    C0.card + C0.addStab.card * n
  omega

/-- The first genuinely new proof obligation after quotienting by the final
stabilizer: the aperiodic DGM core.  `image_layerSubsumSpectrum` and
`addStab_layerSubsumSpectrum_stabilizerQuotient_eq_singleton` close the
transport to this boundary.  What remains is the portion-minimality/extension
argument for arbitrary `n < P.length`; this definition records it explicitly
and does not assert it. -/
def AperiodicDGMSetpartitionCore
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] : Prop :=
  ∀ (P : List (Finset A)) (n : ℕ),
    IsNonemptySetPartition P →
    1 ≤ n → n ≤ P.length →
    (layerSubsumSpectrum P n).addStab = {0} →
    rawDgmCappedMultiplicitySum P n - n + 1 ≤
      (layerSubsumSpectrum P n).card

theorem rawLayerMultiplicity_projected_eq_stabilizerLayerMultiplicity
    (T : Finset A) (P : List (Finset A))
    (q : A ⧸ AddAction.stabilizer A (T : Set A)) :
    rawLayerMultiplicity
        (P.map fun B ↦ stabilizerQuotientLayer T B) q =
      stabilizerLayerMultiplicity T P q := by
  classical
  induction P with
  | nil => simp [rawLayerMultiplicity, stabilizerLayerMultiplicity]
  | cons B P ih =>
      simp only [List.map_cons, rawLayerMultiplicity,
        stabilizerLayerMultiplicity, List.foldr_cons]
      by_cases hq : q ∈ stabilizerQuotientLayer T B
      · simp only [hq, if_true]
        simpa [rawLayerMultiplicity, stabilizerLayerMultiplicity] using ih
      · simp only [hq, if_false]
        simpa [rawLayerMultiplicity, stabilizerLayerMultiplicity] using ih

theorem rawDgmCappedMultiplicitySum_projected
    [Fintype A] (T : Finset A) (P : List (Finset A)) (n : ℕ) :
    rawDgmCappedMultiplicitySum
        (P.map fun B ↦ stabilizerQuotientLayer T B) n =
      stabilizerDgmCappedMultiplicitySum T P n := by
  classical
  unfold rawDgmCappedMultiplicitySum stabilizerDgmCappedMultiplicitySum
  apply Finset.sum_congr rfl
  intro q _
  rw [rawLayerMultiplicity_projected_eq_stabilizerLayerMultiplicity]

/-- Package the aperiodic core on the quotient by the stabilizer of `T`,
hiding the canonical finite quotient instance. -/
noncomputable def AperiodicCoreOnStabilizerQuotient
    [Fintype A] (T : Finset A) : Prop :=
  AperiodicDGMSetpartitionCore
    (A ⧸ AddAction.stabilizer A (T : Set A))

/-- Quotienting an exact-`n` spectrum by its complete stabilizer makes the
projected exact-`n` spectrum aperiodic. -/
theorem addStab_layerSubsumSpectrum_stabilizerQuotient_eq_singleton
    [Fintype A] (P : List (Finset A)) (hP : IsNonemptySetPartition P)
    (n : ℕ) (hn : n ≤ P.length) :
    let T := layerSubsumSpectrum P n
    let H := AddAction.stabilizer A (T : Set A)
    let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
    (layerSubsumSpectrum (P.map fun B ↦ B.image q) n).addStab = {0} := by
  classical
  let T := layerSubsumSpectrum P n
  have hT : T.Nonempty := layerSubsumSpectrum_nonempty P hP n hn
  let H := AddAction.stabilizer A (T : Set A)
  let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
  have himage := image_layerSubsumSpectrum q P n
  dsimp only
  rw [← himage]
  change (T.image q).addStab = (0 : Finset (A ⧸ H))
  simpa [T, H, q] using Finset.addStab_image_coe_quotient hT

/-- Mechanical reduction of the full DGM theorem to the aperiodic core on
stabilizer quotients.  Consequently, the only unproved mathematical boundary
is `AperiodicDGMSetpartitionCore`. -/
theorem generalDGMSetpartitionTheorem_of_aperiodicCoreOnStabilizerQuotient
    [Fintype A]
    (hcore : ∀ T : Finset A, AperiodicCoreOnStabilizerQuotient T) :
    GeneralDGMSetpartitionTheorem A := by
  classical
  intro P n hP hnpos hn
  let T : Finset A := layerSubsumSpectrum P n
  let H : AddSubgroup A := AddAction.stabilizer A (T : Set A)
  let q : A →+ A ⧸ H := QuotientAddGroup.mk' H
  let Pq : List (Finset (A ⧸ H)) :=
    P.map fun B ↦ B.image q
  have hPq : IsNonemptySetPartition Pq := by
    intro C hC
    obtain ⟨B, hBP, rfl⟩ := List.mem_map.mp hC
    exact (hP B hBP).image q
  have hlenq : Pq.length = P.length := by simp [Pq]
  have hstabq : (layerSubsumSpectrum Pq n).addStab = {0} := by
    simpa [Pq, T, H, q, stabilizerQuotientLayer] using
      addStab_layerSubsumSpectrum_stabilizerQuotient_eq_singleton
        P hP n hn
  have hcoreT : AperiodicDGMSetpartitionCore (A ⧸ H) := by
    simpa [AperiodicCoreOnStabilizerQuotient, T, H] using hcore T
  have hineq := hcoreT Pq n hPq hnpos (by simpa [hlenq] using hn) hstabq
  have hspectrum : layerSubsumSpectrum Pq n = T.image q := by
    simpa [Pq, T] using (image_layerSubsumSpectrum q P n).symm
  have hraw : rawDgmCappedMultiplicitySum Pq n =
      stabilizerDgmCappedMultiplicitySum T P n := by
    simpa [Pq, H, q, stabilizerQuotientLayer] using
      rawDgmCappedMultiplicitySum_projected T P n
  rw [hraw, hspectrum] at hineq
  have hmul := Nat.mul_le_mul_left T.addStab.card hineq
  have hcard : T.addStab.card * (T.image q).card = T.card := by
    simpa [H, q] using Finset.card_addStab_add_card_image_coe' T T
  unfold DGMSetpartitionBound
  dsimp only
  change (stabilizerDgmCappedMultiplicitySum T P n - n + 1) *
      T.addStab.card ≤ T.card
  calc
    (stabilizerDgmCappedMultiplicitySum T P n - n + 1) *
          T.addStab.card =
        T.addStab.card *
          (stabilizerDgmCappedMultiplicitySum T P n - n + 1) :=
      Nat.mul_comm _ _
    _ ≤ T.addStab.card * (T.image q).card := hmul
    _ = T.card := hcard

theorem length_le_sum_stabilizerQuotientLayer_card
    (T : Finset A) (P : List (Finset A))
    (hP : IsNonemptySetPartition P) :
    P.length ≤
      (P.map fun B ↦ (stabilizerQuotientLayer T B).card).sum := by
  induction P with
  | nil => simp
  | cons B P ih =>
      have hB : B.Nonempty := hP B (by simp)
      have hP' : IsNonemptySetPartition P := by
        intro C hC
        exact hP C (by simp [hC])
      have hcard : 1 ≤ (stabilizerQuotientLayer T B).card :=
        Finset.card_pos.mpr (hB.image _)
      simp only [List.length_cons, List.map_cons, List.sum_cons]
      simpa [Nat.add_comm] using Nat.add_le_add (ih hP') hcard

/-- The full-layer endpoint of the DeVos--Goddyn--Mohar inequality.

For `n = |P|`, every quotient multiplicity is already at most `n`, so the
cap is inactive.  Iterated Kneser plus quotient-incidence double counting
then gives the exact DGM lower bound.  The general `n < |P|` theorem requires
the genuinely stronger DGM selection argument and is intentionally not
claimed here. -/
theorem fullLayer_dgm_lower_bound
    [Fintype A] (P : List (Finset A))
    (hP : IsNonemptySetPartition P) :
    ((P.map fun B ↦
          (stabilizerQuotientLayer (fullLayerSumSpectrum P) B).card).sum -
          P.length + 1) *
        (fullLayerSumSpectrum P).addStab.card ≤
      (fullLayerSumSpectrum P).card := by
  classical
  let T : Finset A := fullLayerSumSpectrum P
  have hsumEq : T = iteratedFinsetSum P :=
    fullLayerSumSpectrum_eq_iteratedFinsetSum P
  have hT : T.Nonempty := by
    rw [hsumEq]
    exact iteratedFinsetSum_nonempty P hP
  have hk := sum_card_addStab_add_card_addStab_le P hP
  rw [← hsumEq] at hk
  have hterm (B : Finset A) :
      T.addStab.card * (stabilizerQuotientLayer T B).card =
        (B + T.addStab).card := by
    simpa [stabilizerQuotientLayer] using
      Finset.card_addStab_add_card_image_coe' B T
  have hsumTerms :
      T.addStab.card *
          (P.map fun B ↦ (stabilizerQuotientLayer T B).card).sum =
        (P.map fun B ↦ (B + T.addStab).card).sum := by
    rw [← List.sum_map_mul_left]
    congr 1
    exact List.map_congr_left fun B _ ↦ hterm B
  have hlen :
      P.length ≤
        (P.map fun B ↦ (stabilizerQuotientLayer T B).card).sum :=
    length_le_sum_stabilizerQuotientLayer_card T P hP
  dsimp only [T] at hk hsumTerms hlen ⊢
  let incidence :=
    (P.map fun B ↦
      (stabilizerQuotientLayer (fullLayerSumSpectrum P) B).card).sum
  have hrewrite : incidence - P.length + 1 =
      incidence + 1 - P.length := by
    dsimp only [incidence]
    omega
  rw [hrewrite, Nat.sub_mul]
  apply Nat.sub_le_iff_le_add.mpr
  dsimp only [incidence] at hsumTerms ⊢
  rw [Nat.add_mul, one_mul,
    Nat.mul_comm (P.map fun B ↦
      (stabilizerQuotientLayer (fullLayerSumSpectrum P) B).card).sum,
    hsumTerms]
  exact hk

/-- The frozen general DGM statement is proved at its full-layer endpoint. -/
theorem dgmSetpartitionBound_full
    [Fintype A] (P : List (Finset A))
    (hP : IsNonemptySetPartition P) :
    DGMSetpartitionBound P P.length := by
  change
    (stabilizerDgmCappedMultiplicitySum
          (fullLayerSumSpectrum P) P P.length - P.length + 1) *
        (fullLayerSumSpectrum P).addStab.card ≤
      (fullLayerSumSpectrum P).card
  rw [stabilizerDgmCappedMultiplicitySum_length]
  exact fullLayer_dgm_lower_bound P hP

/-- The empty-selection endpoint is also exact.  The source DGM theorem uses
positive `n`; this lemma is retained as a recursion boundary check. -/
theorem dgmSetpartitionBound_zero [Fintype A]
    (P : List (Finset A)) : DGMSetpartitionBound P 0 := by
  classical
  simp [DGMSetpartitionBound, stabilizerDgmCappedMultiplicitySum,
    stabilizerLayerMultiplicity]

/-- The first positive endpoint of general DGM. -/
theorem dgmSetpartitionBound_one [Fintype A]
    (P : List (Finset A)) (hP : IsNonemptySetPartition P)
    (hlen : 1 ≤ P.length) : DGMSetpartitionBound P 1 := by
  classical
  let T := layerUnion P
  have hT : T.Nonempty := by
    change (layerUnion P).Nonempty
    rw [← layerSubsumSpectrum_one P]
    exact layerSubsumSpectrum_nonempty P hP 1 hlen
  have hcap := stabilizerDgmCappedMultiplicitySum_one T P
  have himage : (stabilizerQuotientLayer T T).Nonempty := hT.image _
  have hcapPos : 1 ≤ stabilizerDgmCappedMultiplicitySum T P 1 := by
    rw [hcap]
    exact Finset.card_pos.mpr himage
  have hcard := Finset.card_addStab_add_card_image_coe' T T
  rw [Finset.add_addStab] at hcard
  unfold DGMSetpartitionBound
  dsimp only
  rw [layerSubsumSpectrum_one]
  change (stabilizerDgmCappedMultiplicitySum T P 1 - 1 + 1) *
      T.addStab.card ≤ T.card
  have hsimplify : stabilizerDgmCappedMultiplicitySum T P 1 - 1 + 1 =
      stabilizerDgmCappedMultiplicitySum T P 1 := by omega
  rw [hsimplify, hcap, Nat.mul_comm]
  simpa [stabilizerQuotientLayer] using hcard.le

/-- Two nonempty layers: Kneser's theorem is exactly the two-layer DGM
endpoint, expressed with the stabilizer of their sumset. -/
theorem twoLayer_kneser_lower_bound
    (B C : Finset A) :
    (B + (B + C).addStab).card +
        (C + (B + C).addStab).card - (B + C).addStab.card ≤
      (fullLayerSumSpectrum [B, C]).card := by
  have hk := finset_add_kneser B C
  have hfull : fullLayerSumSpectrum [B, C] = B + C := by
    rw [fullLayerSumSpectrum_cons, fullLayerSumSpectrum_cons,
      fullLayerSumSpectrum_nil]
    have hC0 : C + ({0} : Finset A) = C := by
      change C + (0 : Finset A) = C
      exact add_zero C
    rw [hC0]
  rw [hfull]
  exact Nat.sub_le_iff_le_add.mpr hk

end GaoLean

#print axioms GaoLean.layerSubsumSpectrum_eq_empty_of_length_lt
#print axioms GaoLean.layerSubsumSpectrum_nonempty
#print axioms GaoLean.sum_quotientLayerMultiplicity
#print axioms GaoLean.dgmCappedMultiplicitySum_length
#print axioms GaoLean.stabilizerDgmCappedMultiplicitySum_length
#print axioms GaoLean.image_layerSubsumSpectrum
#print axioms GaoLean.addStab_layerSubsumSpectrum_stabilizerQuotient_eq_singleton
#print axioms GaoLean.generalDGMSetpartitionTheorem_of_aperiodicCoreOnStabilizerQuotient
#print axioms GaoLean.dgmSetpartitionBound_full
#print axioms GaoLean.dgmSetpartitionBound_zero
#print axioms GaoLean.dgmSetpartitionBound_one
#print axioms GaoLean.sum_occurrenceQuotientMultiplicity
#print axioms GaoLean.twoLayer_kneser_lower_bound
