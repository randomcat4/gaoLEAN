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

/-- Proof-relevant exact-layer choice.  Unlike membership in the finite
spectrum, this object retains which recursive layers were skipped or used;
it is the input needed to group a witness choice by stabilizer cosets in the
nontrivial-portion extension. -/
inductive LayerSubsumChoice :
    List (Finset A) → ℕ → A → Type _
  | zero (P : List (Finset A)) : LayerSubsumChoice P 0 0
  | skip {B : Finset A} {P : List (Finset A)} {n : ℕ} {y : A} :
      LayerSubsumChoice P n y → LayerSubsumChoice (B :: P) n y
  | take {B : Finset A} {P : List (Finset A)} {n : ℕ}
      {b y : A} :
      b ∈ B → LayerSubsumChoice P n y →
      LayerSubsumChoice (B :: P) (n + 1) (b + y)

namespace LayerSubsumChoice

/-- The number of selected layers whose chosen value lies in a prescribed
quotient coset.  This counts selected *layers*, as required by the pattern
formalism in DeVos--Goddyn--Mohar, not raw element occurrences. -/
def quotientMultiplicity (K : AddSubgroup A) [DecidableEq (A ⧸ K)] :
    {P : List (Finset A)} → {n : ℕ} → {y : A} →
      LayerSubsumChoice P n y → A ⧸ K → ℕ
  | _, _, _, .zero _ => fun _ ↦ 0
  | _, _, _, .skip h => quotientMultiplicity K h
  | _, _, _, .take (b := b) _ h => fun q ↦
      (if (b : A ⧸ K) = q then 1 else 0) +
        quotientMultiplicity K h q

/-- The quotient multiplicities of a proof-relevant choice sum to the exact
number of selected layers. -/
theorem sum_quotientMultiplicity [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) :
    ∑ q : A ⧸ K, quotientMultiplicity K h q = n := by
  classical
  induction h with
  | zero P => simp [quotientMultiplicity]
  | skip h ih => simpa [quotientMultiplicity] using ih
  | @take B P n b y hb h ih =>
      simp only [quotientMultiplicity, Finset.sum_add_distrib, ih]
      have hone : (∑ q : A ⧸ K,
          if (b : A ⧸ K) = q then 1 else 0) = 1 := by
        simpa [eq_comm]
      rw [hone]
      omega

/-- Every proof-relevant choice contributes its indexed sum to the recursive
exact-layer spectrum. -/
theorem mem_layerSubsumSpectrum
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) : y ∈ layerSubsumSpectrum P n := by
  induction h with
  | zero P => simp
  | @skip B P n y h ih =>
      obtain rfl | n := n
      · simpa using ih
      · exact Finset.mem_union_left _ ih
  | @take B P n b y hb h ih =>
      exact Finset.mem_union_right _
        (Finset.mem_add.mpr ⟨b, hb, y, ih, rfl⟩)

/-- Transporting only the sum index of a choice does not alter its selected
quotient-coset counts. -/
theorem quotientMultiplicity_cast
    {K : AddSubgroup A} [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y y' : A}
    (e : y = y') (h : LayerSubsumChoice P n y) (q : A ⧸ K) :
    quotientMultiplicity K (e ▸ h) q = quotientMultiplicity K h q := by
  subst e
  rfl

end LayerSubsumChoice

/-- A quotient-coset pattern of total weight `n`. -/
structure QuotientPattern (K : AddSubgroup A) (n : ℕ)
    [Fintype (A ⧸ K)] where
  multiplicity : A ⧸ K → ℕ
  weight_eq : ∑ q : A ⧸ K, multiplicity q = n

instance (K : AddSubgroup A) (n : ℕ) [Fintype (A ⧸ K)] :
    CoeFun (QuotientPattern K n) (fun _ ↦ A ⧸ K → ℕ) :=
  ⟨QuotientPattern.multiplicity⟩

/-- A choice realizes `μ` when its selected-layer count in every quotient
coset is exactly prescribed by `μ`. -/
def LayerSubsumChoice.RealizesPattern
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {y : A} (h : LayerSubsumChoice P n y)
    (μ : QuotientPattern K n) : Prop :=
  ∀ q : A ⧸ K, h.quotientMultiplicity K q = μ q

/-- The sums of exact-layer choices which realize a fixed quotient pattern.
This is the finite `Σ_μ(P)` of Theorem 3.1. -/
noncomputable def patternSubsumSpectrum
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n) : Finset A := by
  classical
  exact (layerSubsumSpectrum P n).filter fun y ↦
    Nonempty {h : LayerSubsumChoice P n y // h.RealizesPattern μ}

@[simp]
theorem mem_patternSubsumSpectrum_iff
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n) (y : A) :
    y ∈ patternSubsumSpectrum P μ ↔
      Nonempty {h : LayerSubsumChoice P n y // h.RealizesPattern μ} := by
  classical
  constructor
  · intro hy
    exact (Finset.mem_filter.mp hy).2
  · intro hy
    refine Finset.mem_filter.mpr ⟨?_, hy⟩
    obtain ⟨⟨h, _⟩⟩ := hy
    exact h.mem_layerSubsumSpectrum

theorem patternSubsumSpectrum_subset_layerSubsumSpectrum
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n) :
    patternSubsumSpectrum P μ ⊆ layerSubsumSpectrum P n := by
  classical
  intro y hy
  exact (Finset.mem_filter.mp hy).1

theorem patternSubsumSpectrum_nonempty_iff
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n) :
    (patternSubsumSpectrum P μ).Nonempty ↔
      ∃ y : A, Nonempty
        {h : LayerSubsumChoice P n y // h.RealizesPattern μ} := by
  constructor
  · rintro ⟨y, hy⟩
    exact ⟨y, (mem_patternSubsumSpectrum_iff P μ y).1 hy⟩
  · rintro ⟨y, hy⟩
    exact ⟨y, (mem_patternSubsumSpectrum_iff P μ y).2 hy⟩

/-- The proof-relevant recursive choices represent exactly the elements of
`layerSubsumSpectrum`. -/
theorem nonempty_layerSubsumChoice_iff_mem
    (P : List (Finset A)) (n : ℕ) (y : A) :
    Nonempty (LayerSubsumChoice P n y) ↔
      y ∈ layerSubsumSpectrum P n := by
  constructor
  · rintro ⟨h⟩
    induction h with
    | zero P => simp
    | @skip B P n y h ih =>
        obtain rfl | n := n
        · simpa using ih
        · exact Finset.mem_union_left _ ih
    | @take B P n b y hb h ih =>
        exact Finset.mem_union_right _
          (Finset.mem_add.mpr ⟨b, hb, y, ih, rfl⟩)
  · induction P generalizing n y with
    | nil =>
        obtain rfl | n := n
        · simp only [layerSubsumSpectrum_zero, Finset.mem_singleton]
          intro hy
          subst y
          exact ⟨LayerSubsumChoice.zero []⟩
        · simp
    | cons B P ih =>
        obtain rfl | n := n
        · simp only [layerSubsumSpectrum_zero, Finset.mem_singleton]
          intro hy
          subst y
          exact ⟨LayerSubsumChoice.zero (B :: P)⟩
        · rw [layerSubsumSpectrum_cons_succ, Finset.mem_union]
          rintro (hy | hy)
          · obtain ⟨hchoice⟩ := ih (n + 1) y hy
            exact ⟨LayerSubsumChoice.skip hchoice⟩
          · obtain ⟨b, hb, z, hz, hbzy⟩ := Finset.mem_add.mp hy
            obtain ⟨hchoice⟩ := ih n z hz
            subst y
            exact ⟨LayerSubsumChoice.take hb hchoice⟩

/-- Replacing two layers by their intersection and union cannot create a
new exact-layer sum.  This is the spectrum half of the DGM
intersection--union transform. -/
theorem layerSubsumSpectrum_inter_union_subset
    (B C : Finset A) (P : List (Finset A)) (n : ℕ) :
    layerSubsumSpectrum ((B ∩ C) :: (B ∪ C) :: P) n ⊆
      layerSubsumSpectrum (B :: C :: P) n := by
  classical
  intro y hy
  obtain rfl | n := n
  · simpa using hy
  obtain rfl | k := n
  · simp only [Nat.zero_add, layerSubsumSpectrum_one, layerUnion,
      Finset.mem_union, Finset.mem_inter] at hy ⊢
    tauto
  rw [layerSubsumSpectrum_cons_succ] at hy ⊢
  rcases Finset.mem_union.mp hy with hySkipInter | hyTakeInter
  · rw [layerSubsumSpectrum_cons_succ] at hySkipInter
    rcases Finset.mem_union.mp hySkipInter with hyTail | hyTakeUnion
    · exact Finset.mem_union_left _
        (Finset.mem_union_left _ hyTail)
    · obtain ⟨z, hzUnion, t, ht, rfl⟩ := Finset.mem_add.mp hyTakeUnion
      rcases Finset.mem_union.mp hzUnion with hzB | hzC
      · exact Finset.mem_union_right _
          (Finset.mem_add.mpr ⟨z, hzB, t,
            Finset.mem_union_left _ ht, rfl⟩)
      · exact Finset.mem_union_left _
          (Finset.mem_union_right _
            (Finset.mem_add.mpr ⟨z, hzC, t, ht, rfl⟩))
  · obtain ⟨x, hxInter, s, hs, rfl⟩ := Finset.mem_add.mp hyTakeInter
    have hxB : x ∈ B := (Finset.mem_inter.mp hxInter).1
    have hxC : x ∈ C := (Finset.mem_inter.mp hxInter).2
    rw [layerSubsumSpectrum_cons_succ] at hs
    rcases Finset.mem_union.mp hs with hsTail | hsTakeUnion
    · exact Finset.mem_union_right _
        (Finset.mem_add.mpr ⟨x, hxB, s,
          Finset.mem_union_left _ hsTail, rfl⟩)
    · obtain ⟨z, hzUnion, t, ht, rfl⟩ := Finset.mem_add.mp hsTakeUnion
      rcases Finset.mem_union.mp hzUnion with hzB | hzC
      · exact Finset.mem_union_right _
          (Finset.mem_add.mpr ⟨z, hzB, x + t,
            Finset.mem_union_right _
              (Finset.mem_add.mpr ⟨x, hxC, t, ht, rfl⟩), by
                ac_rfl⟩)
      · exact Finset.mem_union_right _
          (Finset.mem_add.mpr ⟨x, hxB, z + t,
            Finset.mem_union_right _
              (Finset.mem_add.mpr ⟨z, hzC, t, ht, rfl⟩), rfl⟩)

/-- Proof-relevant form of the intersection--union transform: a realizing
choice for the transformed first two layers can be reassigned to the original
two layers without changing its quotient-coset pattern. -/
theorem exists_interUnionChoice_realizing_original
    {K : AddSubgroup A} [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A)) {n : ℕ} {y : A}
    (μ : QuotientPattern K n)
    (h : LayerSubsumChoice ((B ∩ C) :: (B ∪ C) :: P) n y)
    (hμ : h.RealizesPattern μ) :
    ∃ h' : LayerSubsumChoice (B :: C :: P) n y,
      h'.RealizesPattern μ := by
  classical
  cases h with
  | zero Q =>
      exact ⟨LayerSubsumChoice.zero (B :: C :: P), by
        simpa [LayerSubsumChoice.RealizesPattern,
          LayerSubsumChoice.quotientMultiplicity] using hμ⟩
  | @skip D Q k z htail =>
      cases htail with
      | zero Q =>
          exact ⟨LayerSubsumChoice.zero (B :: C :: P), by
            simpa [LayerSubsumChoice.RealizesPattern,
              LayerSubsumChoice.quotientMultiplicity] using hμ⟩
      | @skip E R k z ht =>
          refine ⟨LayerSubsumChoice.skip (B := B)
            (LayerSubsumChoice.skip (B := C) ht), ?_⟩
          simpa [LayerSubsumChoice.RealizesPattern,
            LayerSubsumChoice.quotientMultiplicity] using hμ
      | @take E R k z t hz ht =>
          rcases Finset.mem_union.mp hz with hzB | hzC
          · refine ⟨LayerSubsumChoice.take (B := B) hzB
              (LayerSubsumChoice.skip (B := C) ht), ?_⟩
            simpa [LayerSubsumChoice.RealizesPattern,
              LayerSubsumChoice.quotientMultiplicity] using hμ
          · refine ⟨LayerSubsumChoice.skip (B := B)
              (LayerSubsumChoice.take (B := C) hzC ht), ?_⟩
            simpa [LayerSubsumChoice.RealizesPattern,
              LayerSubsumChoice.quotientMultiplicity] using hμ
  | @take D Q k x s hx htail =>
      have hxB : x ∈ B := (Finset.mem_inter.mp hx).1
      have hxC : x ∈ C := (Finset.mem_inter.mp hx).2
      cases htail with
      | zero Q =>
          refine ⟨LayerSubsumChoice.take (B := B) hxB
            (LayerSubsumChoice.skip (B := C)
              (LayerSubsumChoice.zero P)), ?_⟩
          simpa [LayerSubsumChoice.RealizesPattern,
            LayerSubsumChoice.quotientMultiplicity] using hμ
      | @skip E R k s ht =>
          refine ⟨LayerSubsumChoice.take (B := B) hxB
            (LayerSubsumChoice.skip (B := C) ht), ?_⟩
          simpa [LayerSubsumChoice.RealizesPattern,
            LayerSubsumChoice.quotientMultiplicity] using hμ
      | @take E R k z t hz ht =>
          rcases Finset.mem_union.mp hz with hzB | hzC
          · let hout := LayerSubsumChoice.take (B := B) hzB
                (LayerSubsumChoice.take (B := C) hxC ht)
            have houtMult (q : A ⧸ K) :
                LayerSubsumChoice.quotientMultiplicity K hout q =
                  (if (z : A ⧸ K) = q then 1 else 0) +
                    ((if (x : A ⧸ K) = q then 1 else 0) +
                      LayerSubsumChoice.quotientMultiplicity K ht q) := by
              rfl
            have hsum : z + (x + t) = x + (z + t) := by ac_rfl
            refine ⟨hsum ▸ hout, ?_⟩
            intro q
            rw [LayerSubsumChoice.quotientMultiplicity_cast]
            rw [houtMult]
            have hq := hμ q
            simp only [LayerSubsumChoice.quotientMultiplicity] at hq ⊢
            omega
          · refine ⟨LayerSubsumChoice.take (B := B) hxB
              (LayerSubsumChoice.take (B := C) hzC ht), ?_⟩
            simpa [LayerSubsumChoice.RealizesPattern,
              LayerSubsumChoice.quotientMultiplicity] using hμ

/-- Therefore the intersection--union transform also preserves inclusion for
every fixed quotient pattern, not only for the unrestricted exact spectrum. -/
theorem patternSubsumSpectrum_inter_union_subset
    {K : AddSubgroup A} [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A)) {n : ℕ}
    (μ : QuotientPattern K n) :
    patternSubsumSpectrum ((B ∩ C) :: (B ∪ C) :: P) μ ⊆
      patternSubsumSpectrum (B :: C :: P) μ := by
  intro y hy
  obtain ⟨⟨h, hμ⟩⟩ := (mem_patternSubsumSpectrum_iff _ μ y).1 hy
  obtain ⟨h', hμ'⟩ :=
    exists_interUnionChoice_realizing_original B C P μ h hμ
  exact (mem_patternSubsumSpectrum_iff _ μ y).2 ⟨⟨h', hμ'⟩⟩

/-- The canonical two-layer intersection--union transform used in the
minimal-counterexample proof. -/
def dgmInterUnionLayers (B C : Finset A) (P : List (Finset A)) :
    List (Finset A) := (B ∩ C) :: (B ∪ C) :: P

/-- Total cardinality and square-cardinality are the second and third
coordinates of the faithful inner well-founded measure. -/
def dgmTotalLayerCard (P : List (Finset A)) : ℕ :=
  (P.map Finset.card).sum

def dgmLayerSquareSum (P : List (Finset A)) : ℕ :=
  (P.map fun B ↦ B.card ^ 2).sum

def dgmLayerSquareDefect [Fintype A] (P : List (Finset A)) : ℕ :=
  P.length * (Fintype.card A) ^ 2 - dgmLayerSquareSum P

@[simp]
theorem length_dgmInterUnionLayers (B C : Finset A) (P : List (Finset A)) :
    (dgmInterUnionLayers B C P).length = (B :: C :: P).length := by
  simp [dgmInterUnionLayers]

theorem dgmInterUnionLayers_nonempty
    (B C : Finset A) (P : List (Finset A))
    (hInter : (B ∩ C).Nonempty) (hP : IsNonemptySetPartition P) :
    IsNonemptySetPartition (dgmInterUnionLayers B C P) := by
  intro D hD
  simp only [dgmInterUnionLayers, List.mem_cons] at hD
  rcases hD with rfl | rfl | hDP
  · exact hInter
  · exact hInter.mono Finset.inter_subset_union
  · exact hP D hDP

theorem dgmTotalLayerCard_inter_union
    (B C : Finset A) (P : List (Finset A)) :
    dgmTotalLayerCard (dgmInterUnionLayers B C P) =
      dgmTotalLayerCard (B :: C :: P) := by
  have hcard := Finset.card_inter_add_card_union B C
  simp only [dgmTotalLayerCard, dgmInterUnionLayers, List.map_cons,
    List.sum_cons]
  omega

/-- If the two layers are incomparable, intersection--union strictly
increases the sum of squared layer cardinalities. -/
theorem dgmLayerSquareSum_lt_inter_union
    (B C : Finset A) (P : List (Finset A))
    (hBC : ¬ B ⊆ C) (hCB : ¬ C ⊆ B) :
    dgmLayerSquareSum (B :: C :: P) <
      dgmLayerSquareSum (dgmInterUnionLayers B C P) := by
  have hInterB : (B ∩ C).card < B.card := by
    apply Finset.card_lt_card
    refine ⟨Finset.inter_subset_left, ?_⟩
    intro hBInter
    exact hBC (hBInter.trans Finset.inter_subset_right)
  have hInterC : (B ∩ C).card < C.card := by
    apply Finset.card_lt_card
    refine ⟨Finset.inter_subset_right, ?_⟩
    intro hCInter
    exact hCB (hCInter.trans Finset.inter_subset_left)
  have hcard := Finset.card_inter_add_card_union B C
  simp only [dgmLayerSquareSum, dgmInterUnionLayers, List.map_cons,
    List.sum_cons]
  nlinarith

theorem dgmLayerSquareSum_le_bound [Fintype A]
    (P : List (Finset A)) :
    dgmLayerSquareSum P ≤ P.length * (Fintype.card A) ^ 2 := by
  induction P with
  | nil => simp [dgmLayerSquareSum]
  | cons B P ih =>
      have hcard : B.card ≤ Fintype.card A := by
        simpa using Finset.card_le_univ B
      have hsquare : B.card ^ 2 ≤ (Fintype.card A) ^ 2 := by
        exact Nat.pow_le_pow_left hcard 2
      simp only [dgmLayerSquareSum, List.map_cons, List.sum_cons,
        List.length_cons]
      calc
        B.card ^ 2 + (List.map (fun B ↦ B.card ^ 2) P).sum ≤
            (Fintype.card A) ^ 2 + P.length * (Fintype.card A) ^ 2 :=
          Nat.add_le_add hsquare ih
        _ = (P.length + 1) * (Fintype.card A) ^ 2 := by ring

/-- Thus the bounded square defect, the third lexicographic coordinate,
strictly decreases under an incomparable intersection--union transform. -/
theorem dgmLayerSquareDefect_inter_union_lt [Fintype A]
    (B C : Finset A) (P : List (Finset A))
    (hBC : ¬ B ⊆ C) (hCB : ¬ C ⊆ B) :
    dgmLayerSquareDefect (dgmInterUnionLayers B C P) <
      dgmLayerSquareDefect (B :: C :: P) := by
  have hsquare := dgmLayerSquareSum_lt_inter_union B C P hBC hCB
  have hbound := dgmLayerSquareSum_le_bound
    (A := A) (dgmInterUnionLayers B C P)
  have hlen := length_dgmInterUnionLayers B C P
  unfold dgmLayerSquareDefect
  rw [hlen] at hbound ⊢
  omega

/-- Nested products give a literal four-coordinate lexicographic measure:
pattern-spectrum size, total layer cardinality, bounded square defect, and
number of layers. -/
abbrev DGMPatternInnerMeasure := ℕ × (ℕ × (ℕ × ℕ))

abbrev DGMPatternInnerLt :
    DGMPatternInnerMeasure → DGMPatternInnerMeasure → Prop :=
  Prod.Lex (fun a b : ℕ ↦ a < b)
    (Prod.Lex (fun a b : ℕ ↦ a < b)
      (Prod.Lex (fun a b : ℕ ↦ a < b) (fun a b : ℕ ↦ a < b)))

theorem dgmPatternInnerLt_wellFounded : WellFounded DGMPatternInnerLt :=
  WellFounded.prod_lex wellFounded_lt
    (WellFounded.prod_lex wellFounded_lt
      (WellFounded.prod_lex wellFounded_lt wellFounded_lt))

noncomputable def dgmPatternInnerMeasure
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n) :
    DGMPatternInnerMeasure :=
  ((patternSubsumSpectrum P μ).card,
    (dgmTotalLayerCard P, (dgmLayerSquareDefect P, P.length)))

theorem dgmPatternInnerMeasure_inter_union_lt_of_card_lt
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A)) (μ : QuotientPattern K n)
    (hcard :
      (patternSubsumSpectrum (dgmInterUnionLayers B C P) μ).card <
        (patternSubsumSpectrum (B :: C :: P) μ).card) :
    DGMPatternInnerLt
      (dgmPatternInnerMeasure (dgmInterUnionLayers B C P) μ)
      (dgmPatternInnerMeasure (B :: C :: P) μ) := by
  exact Prod.Lex.left _ _ hcard

theorem dgmPatternInnerMeasure_inter_union_lt_of_spectrum_eq
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A)) (μ : QuotientPattern K n)
    (hBC : ¬ B ⊆ C) (hCB : ¬ C ⊆ B)
    (hspectrum :
      patternSubsumSpectrum (dgmInterUnionLayers B C P) μ =
        patternSubsumSpectrum (B :: C :: P) μ) :
    DGMPatternInnerLt
      (dgmPatternInnerMeasure (dgmInterUnionLayers B C P) μ)
      (dgmPatternInnerMeasure (B :: C :: P) μ) := by
  have htotal := dgmTotalLayerCard_inter_union B C P
  have hdefect := dgmLayerSquareDefect_inter_union_lt B C P hBC hCB
  unfold dgmPatternInnerMeasure
  rw [hspectrum, htotal]
  exact Prod.Lex.right _ (Prod.Lex.right _ (Prod.Lex.left _ _ hdefect))

/-! ## The crossed two-layer objects in the general pattern proof -/

/-- The part of a layer lying in the additive `H`-coset represented by `b`.
This is the finite-set version of the source paper's `Aᵢʲ` notation. -/
noncomputable def dgmCosetSlice (H : AddSubgroup A)
    (B : Finset A) (b : A) : Finset A := by
  classical
  exact B.filter fun x ↦ (x : A ⧸ H) = (b : A ⧸ H)

@[simp]
theorem mem_dgmCosetSlice_iff (H : AddSubgroup A)
    (B : Finset A) (b x : A) :
    x ∈ dgmCosetSlice H B b ↔
      x ∈ B ∧ (x : A ⧸ H) = (b : A ⧸ H) := by
  classical
  simp [dgmCosetSlice]

theorem dgmCosetSlice_subset (H : AddSubgroup A)
    (B : Finset A) (b : A) :
    dgmCosetSlice H B b ⊆ B := by
  intro x hx
  exact (mem_dgmCosetSlice_iff H B b x).1 hx |>.1

theorem mem_dgmCosetSlice_self (H : AddSubgroup A)
    (B : Finset A) {b : A} (hb : b ∈ B) :
    b ∈ dgmCosetSlice H B b := by
  exact (mem_dgmCosetSlice_iff H B b b).2 ⟨hb, rfl⟩

/-- A weight-`k+2` pattern is obtained from a weight-`k` tail pattern by
adjoining one selected layer in each of the two prescribed `H`-cosets.
This proof-relevant equation remains correct when the two cosets coincide. -/
def QuotientPattern.IsTwoStepExtension
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (ν : QuotientPattern H (k + 2))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : Prop :=
  ∀ q : A ⧸ H,
    ν q = (if (b₁ : A ⧸ H) = q then 1 else 0) +
      (if (b₂ : A ⧸ H) = q then 1 else 0) + νtail q

/-- Adding two chosen elements in the prescribed cosets to a tail sum
realizing `νtail` produces a sum realizing the two-step extension `ν`.
This is the basic feasibility bridge used by each of `D₁`, `D₂`, `D₁₂`. -/
theorem mem_patternSubsumSpectrum_cons_cons_of_twoStep
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    {x₁ x₂ t : A}
    (hx₁ : x₁ ∈ dgmCosetSlice H B b₁)
    (hx₂ : x₂ ∈ dgmCosetSlice H C b₂)
    (ht : t ∈ patternSubsumSpectrum P νtail) :
    x₁ + (x₂ + t) ∈ patternSubsumSpectrum (B :: C :: P) ν := by
  obtain ⟨⟨htail, htailPattern⟩⟩ :=
    (mem_patternSubsumSpectrum_iff P νtail t).1 ht
  have hx₁B := (mem_dgmCosetSlice_iff H B b₁ x₁).1 hx₁
  have hx₂C := (mem_dgmCosetSlice_iff H C b₂ x₂).1 hx₂
  let hout : LayerSubsumChoice (B :: C :: P) (k + 2)
      (x₁ + (x₂ + t)) :=
    LayerSubsumChoice.take hx₁B.1
      (LayerSubsumChoice.take hx₂C.1 htail)
  refine (mem_patternSubsumSpectrum_iff _ ν _).2 ⟨⟨hout, ?_⟩⟩
  intro q
  change (if (x₁ : A ⧸ H) = q then 1 else 0) +
      ((if (x₂ : A ⧸ H) = q then 1 else 0) +
        LayerSubsumChoice.quotientMultiplicity H htail q) = ν q
  rw [hx₁B.2, hx₂C.2, htailPattern q, hext q]
  omega

/-- The crossed pair base
`(A₁¹+A₁²) ∪ (A₂¹+A₂²)` from the source proof. -/
noncomputable def dgmCrossedPairBase (H : AddSubgroup A)
    (B C : Finset A) (b₁ b₂ : A) : Finset A :=
  (dgmCosetSlice H B b₁ + dgmCosetSlice H C b₂) ∪
    (dgmCosetSlice H B b₂ + dgmCosetSlice H C b₁)

/-- The source proof's `D₁₂`: the crossed pair base plus the fixed
weight-`k` tail-pattern spectrum. -/
noncomputable def dgmCrossedD12
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : Finset A :=
  dgmCrossedPairBase H B C b₁ b₂ + patternSubsumSpectrum P νtail

/-- `D₁₂` creates no new sums: under the exact two-step pattern equation it
is contained in `Σν(B,C,P)`. -/
theorem dgmCrossedD12_subset_patternSubsumSpectrum
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail) :
    dgmCrossedD12 B C P b₁ b₂ νtail ⊆
      patternSubsumSpectrum (B :: C :: P) ν := by
  intro y hy
  obtain ⟨u, hu, t, ht, rfl⟩ := Finset.mem_add.mp hy
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Finset.mem_add.mp hu
    have hmem := mem_patternSubsumSpectrum_cons_cons_of_twoStep
      B C P ν b₁ b₂ νtail hext hx₁ hx₂ ht
    simpa [add_assoc] using hmem
  · obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := Finset.mem_add.mp hu
    have hext' : ν.IsTwoStepExtension b₂ b₁ νtail := by
      intro q
      rw [hext q] <;> omega
    have hmem := mem_patternSubsumSpectrum_cons_cons_of_twoStep
      B C P ν b₂ b₁ νtail hext' hx₁ hx₂ ht
    simpa [add_assoc] using hmem

/-- The crossed `D₁₂` is nonempty as soon as the selected representatives
belong to the two leading layers and the tail pattern is feasible. -/
theorem dgmCrossedD12_nonempty
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    {b₁ b₂ : A} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (htail : (patternSubsumSpectrum P νtail).Nonempty) :
    (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty := by
  have hslice₁ : (dgmCosetSlice H B b₁).Nonempty :=
    ⟨b₁, mem_dgmCosetSlice_self H B hb₁⟩
  have hslice₂ : (dgmCosetSlice H C b₂).Nonempty :=
    ⟨b₂, mem_dgmCosetSlice_self H C hb₂⟩
  exact ((hslice₁.add hslice₂).mono (Finset.subset_union_left)).add htail

/-- A translation outside the stabilizer of a nonempty finite set moves
some member of the set outside it. -/
theorem exists_mem_add_not_mem_of_not_mem_addStab
    (T : Finset A) (hT : T.Nonempty) (a : A)
    (ha : a ∉ T.addStab) :
    ∃ y ∈ T, a + y ∉ T := by
  classical
  by_contra h
  push Not at h
  have hsubset : a +ᵥ T ⊆ T := by
    intro z hz
    obtain ⟨y, hy, rfl⟩ := (Finset.mem_vadd_finset.mp hz)
    exact h y hy
  have heq : a +ᵥ T = T :=
    Finset.eq_of_subset_of_card_le hsubset (by simp)
  exact ha ((Finset.mem_addStab hT).2 heq)

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

/-- The intersection--union transform preserves, pointwise, the number of
layers containing each group element.  This is the incidence half of the
general DGM transform. -/
theorem rawLayerMultiplicity_inter_union
    (B C : Finset A) (P : List (Finset A)) (x : A) :
    rawLayerMultiplicity ((B ∩ C) :: (B ∪ C) :: P) x =
      rawLayerMultiplicity (B :: C :: P) x := by
  classical
  by_cases hxB : x ∈ B <;> by_cases hxC : x ∈ C <;>
    simp [rawLayerMultiplicity, hxB, hxC, Nat.add_comm]

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

/-- Consequently, the intersection--union transform preserves every capped
incidence sum. -/
theorem rawDgmCappedMultiplicitySum_inter_union
    [Fintype A] (B C : Finset A) (P : List (Finset A)) (n : ℕ) :
    rawDgmCappedMultiplicitySum ((B ∩ C) :: (B ∪ C) :: P) n =
      rawDgmCappedMultiplicitySum (B :: C :: P) n := by
  classical
  unfold rawDgmCappedMultiplicitySum
  apply Finset.sum_congr rfl
  intro x _
  rw [rawLayerMultiplicity_inter_union]

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

/-- Quotienting by the stabilizer of `C` is injective when that stabilizer is
the singleton zero subgroup. -/
theorem stabilizerQuotient_mk_injective_of_addStab_eq_singleton
    (C : Finset A) (hC : C.Nonempty) (hstab : C.addStab = {0}) :
    Function.Injective
      ((↑) : A → A ⧸ AddAction.stabilizer A (C : Set A)) := by
  intro x y hxy
  have hsub : x - y ∈ AddAction.stabilizer A (C : Set A) :=
    QuotientAddGroup.eq_iff_sub_mem.mp hxy
  have hfin : x - y ∈ C.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hC]
    exact hsub
  rw [hstab] at hfin
  have : x - y = 0 := by simpa using hfin
  exact sub_eq_zero.mp this

theorem mem_stabilizerQuotientLayer_mk_iff_of_addStab_eq_singleton
    (C D : Finset A) (hC : C.Nonempty) (hstab : C.addStab = {0})
    (x : A) :
    (x : A ⧸ AddAction.stabilizer A (C : Set A)) ∈
        stabilizerQuotientLayer C D ↔ x ∈ D := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
    have hinj := stabilizerQuotient_mk_injective_of_addStab_eq_singleton
      C hC hstab
    have hy_eq : y = x := hinj hyx
    simpa [hy_eq] using hy
  · intro hx
    exact Finset.mem_image.mpr ⟨x, hx, rfl⟩

/-- If the stabilizer of `C` is trivial, counting the quotient layers which
contain the image of `x` is exactly the same as counting the original layers
which contain `x`. -/
theorem stabilizerLayerMultiplicity_mk_eq_raw_of_addStab_eq_singleton
    (C : Finset A) (hC : C.Nonempty) (hstab : C.addStab = {0})
    (P : List (Finset A)) (x : A) :
    stabilizerLayerMultiplicity C P
        (x : A ⧸ AddAction.stabilizer A (C : Set A)) =
      rawLayerMultiplicity P x := by
  classical
  induction P with
  | nil => simp [stabilizerLayerMultiplicity, rawLayerMultiplicity]
  | cons B P ih =>
      by_cases hx : x ∈ B
      · have hqx :
            (x : A ⧸ AddAction.stabilizer A (C : Set A)) ∈
              stabilizerQuotientLayer C B :=
          (mem_stabilizerQuotientLayer_mk_iff_of_addStab_eq_singleton
            C B hC hstab x).2 hx
        rw [stabilizerLayerMultiplicity_cons_of_mem C B P _ hqx,
          rawLayerMultiplicity_cons_of_mem B P x hx, ih]
      · have hqx :
            (x : A ⧸ AddAction.stabilizer A (C : Set A)) ∉
              stabilizerQuotientLayer C B := by
          simpa using
            (mem_stabilizerQuotientLayer_mk_iff_of_addStab_eq_singleton
              C B hC hstab x).not.mpr hx
        rw [stabilizerLayerMultiplicity_cons_of_not_mem C B P _ hqx,
          rawLayerMultiplicity_cons_of_not_mem B P x hx, ih]

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

/-- Tail layers projected modulo the stabilizer of an arbitrary candidate
portion. -/
def dgmPortionQuotientLayers [Fintype A]
    (C : Finset A) (P : List (Finset A)) :=
  P.map fun B ↦ stabilizerQuotientLayer C B

/-- A DGM portion in the sense needed by the minimal-stabilizer argument.
It contains the canonical initial portion, stays inside the target spectrum,
and satisfies the stabilizer-aware incidence inequality. -/
def DGMPortion [Fintype A]
    (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (C : Finset A) : Prop :=
  dgmInitialPortion B P n ⊆ C ∧
  C ⊆ layerSubsumSpectrum (B :: P) (n + 1) ∧
  C.Nonempty ∧
  let X := dgmHeadExtensionSet B P n
  X.card + C.addStab.card *
      rawDgmCappedMultiplicitySum (dgmPortionQuotientLayers C P) n ≤
    C.card + C.addStab.card * n

/-- The already-proved canonical bound packages the initial set as a genuine
portion. -/
theorem dgmInitialPortion_isPortion
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hB : B.Nonempty) (hP : IsNonemptySetPartition P)
    (hn : n ≤ P.length)
    (hbound : DGMInitialPortionBound B P n) :
    DGMPortion B P n (dgmInitialPortion B P n) := by
  refine ⟨Finset.Subset.rfl, dgmHeadExtensionSet_add_tail_subset B P n,
    ?_, ?_⟩
  · exact (hB.mono fun x hx ↦ Finset.mem_union_left _ hx).add
      (layerSubsumSpectrum_nonempty P hP n hn)
  · simpa [DGMInitialPortionBound, dgmPortionQuotientLayers,
      dgmInitialPortionQuotientLayers] using hbound

/-- The exact remaining combinatorial step in the nontrivial-stabilizer
branch of the aperiodic induction: when the final exact-sum spectrum is
aperiodic, every portion with nontrivial stabilizer admits a portion with
strictly smaller stabilizer.  The aperiodicity hypothesis is essential
(without it the statement already fails in `ZMod 2`).  This proposition is
defined, not assumed. -/
def DGMPortionExtensionProperty [Fintype A]
    (B : Finset A) (P : List (Finset A)) (n : ℕ) : Prop :=
  (layerSubsumSpectrum (B :: P) (n + 1)).addStab = {0} →
    ∀ C : Finset A,
      DGMPortion B P n C → C.addStab ≠ {0} →
      ∃ C' : Finset A,
        DGMPortion B P n C' ∧ C'.addStab.card < C.addStab.card

/-- A nonempty finite family of portions has a member with minimum
stabilizer cardinality. -/
theorem exists_dgmPortion_min_addStab_card
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    {C0 : Finset A} (hC0 : DGMPortion B P n C0) :
    ∃ C : Finset A,
      DGMPortion B P n C ∧
      ∀ C' : Finset A, DGMPortion B P n C' →
        C.addStab.card ≤ C'.addStab.card := by
  classical
  let portions := (Finset.univ : Finset (Finset A)).filter
    fun C ↦ DGMPortion B P n C
  have hportions : portions.Nonempty := by
    exact ⟨C0, Finset.mem_filter.mpr ⟨Finset.mem_univ C0, hC0⟩⟩
  obtain ⟨C, hCmem, hmin⟩ :=
    Finset.exists_min_image portions (fun C ↦ C.addStab.card) hportions
  refine ⟨C, (Finset.mem_filter.mp hCmem).2, ?_⟩
  intro C' hC'
  exact hmin C' (Finset.mem_filter.mpr ⟨Finset.mem_univ C', hC'⟩)

/-- Minimality plus the extension property forces a portion to have trivial
stabilizer. -/
theorem exists_dgmPortion_addStab_eq_singleton_of_extension
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    {C0 : Finset A} (hC0 : DGMPortion B P n C0)
    (hTargetStab :
      (layerSubsumSpectrum (B :: P) (n + 1)).addStab = {0})
    (hext : DGMPortionExtensionProperty B P n) :
    ∃ C : Finset A, DGMPortion B P n C ∧ C.addStab = {0} := by
  obtain ⟨C, hC, hmin⟩ :=
    exists_dgmPortion_min_addStab_card B P n hC0
  refine ⟨C, hC, ?_⟩
  by_contra hnontrivial
  obtain ⟨C', hC', hlt⟩ := hext hTargetStab C hC hnontrivial
  exact (not_lt_of_ge (hmin C' hC')) hlt

/-- For a nontrivial-stabilizer portion inside an aperiodic target, there is
an exact-layer choice whose entire stabilizer coset is not contained in the
target.  The returned proof-relevant choice is the starting point for the
`R_j,d_j,D` coset-pattern construction. -/
theorem exists_escape_layerSubsumChoice_of_nontrivial_portion
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hTargetStab :
      (layerSubsumSpectrum (B :: P) (n + 1)).addStab = {0})
    (C : Finset A) (hC : DGMPortion B P n C)
    (hCnontrivial : C.addStab ≠ {0}) :
    ∃ y : A,
      Nonempty (LayerSubsumChoice (B :: P) (n + 1) y) ∧
      ¬(({y} : Finset A) + C.addStab ⊆
        layerSubsumSpectrum (B :: P) (n + 1)) := by
  classical
  let T := layerSubsumSpectrum (B :: P) (n + 1)
  have hCnonempty : C.Nonempty := hC.2.2.1
  have hTnonempty : T.Nonempty := hCnonempty.mono hC.2.1
  have haexists : ∃ a ∈ C.addStab, a ≠ 0 := by
    by_contra h
    push Not at h
    apply hCnontrivial
    apply Finset.eq_singleton_iff_unique_mem.mpr
    exact ⟨hCnonempty.zero_mem_addStab, h⟩
  obtain ⟨a, haC, ha0⟩ := haexists
  have haT : a ∉ T.addStab := by
    rw [show T.addStab = {0} by simpa [T] using hTargetStab]
    simpa using ha0
  obtain ⟨y, hyT, hayT⟩ :=
    exists_mem_add_not_mem_of_not_mem_addStab T hTnonempty a haT
  refine ⟨y, (nonempty_layerSubsumChoice_iff_mem _ _ _).2 hyT, ?_⟩
  intro hcoset
  apply hayT
  apply hcoset
  exact Finset.mem_add.mpr
    ⟨y, Finset.mem_singleton_self y, a, haC, by ac_rfl⟩

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

/-- With trivial stabilizer, quotienting all layers preserves the total
capped raw multiplicity, not merely each pointwise multiplicity. -/
theorem rawDgmCappedMultiplicitySum_portionQuotient_eq_of_addStab_eq_singleton
    [Fintype A] (C : Finset A) (hC : C.Nonempty)
    (hstab : C.addStab = {0}) (P : List (Finset A)) (n : ℕ) :
    rawDgmCappedMultiplicitySum (dgmPortionQuotientLayers C P) n =
      rawDgmCappedMultiplicitySum P n := by
  classical
  let H : AddSubgroup A := AddAction.stabilizer A (C : Set A)
  let q : A → A ⧸ H := fun x ↦ (x : A ⧸ H)
  have hq_inj : Function.Injective q := by
    simpa [q, H] using
      stabilizerQuotient_mk_injective_of_addStab_eq_singleton C hC hstab
  have hq_surj : Function.Surjective q := by
    simpa [q, H] using QuotientAddGroup.mk'_surjective H
  let e : A ≃ A ⧸ H := Equiv.ofBijective q ⟨hq_inj, hq_surj⟩
  unfold rawDgmCappedMultiplicitySum
  symm
  refine Fintype.sum_equiv e
    (fun x : A ↦ min n (rawLayerMultiplicity P x))
    (fun z : A ⧸ H ↦
      min n (rawLayerMultiplicity (dgmPortionQuotientLayers C P) z)) ?_
  intro x
  congr 1
  change rawLayerMultiplicity P x =
    rawLayerMultiplicity
      (P.map fun B ↦ stabilizerQuotientLayer C B)
      (x : A ⧸ AddAction.stabilizer A (C : Set A))
  symm
  rw [rawLayerMultiplicity_projected_eq_stabilizerLayerMultiplicity]
  exact
    stabilizerLayerMultiplicity_mk_eq_raw_of_addStab_eq_singleton
      C hC hstab P x

/-- A portion whose stabilizer has already been reduced to zero closes the
current successor step of the aperiodic DGM induction. -/
theorem dgm_cons_bound_of_trivialStab_portion
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (C : Finset A) (hportion : DGMPortion B P n C)
    (hstab : C.addStab = {0}) :
    rawDgmCappedMultiplicitySum (B :: P) (n + 1) - (n + 1) + 1 ≤
      (layerSubsumSpectrum (B :: P) (n + 1)).card := by
  rcases hportion with ⟨_, hCsub, hCnonempty, hnum⟩
  have hquot :=
    rawDgmCappedMultiplicitySum_portionQuotient_eq_of_addStab_eq_singleton
      C hCnonempty hstab P n
  change
    (dgmHeadExtensionSet B P n).card + C.addStab.card *
        rawDgmCappedMultiplicitySum (dgmPortionQuotientLayers C P) n ≤
      C.card + C.addStab.card * n at hnum
  rw [hquot, hstab] at hnum
  simp only [Finset.card_singleton, one_mul] at hnum
  have hcard : C.card ≤
      (layerSubsumSpectrum (B :: P) (n + 1)).card :=
    Finset.card_le_card hCsub
  have hCpos : 1 ≤ C.card := Finset.card_pos.mpr hCnonempty
  rw [rawDgmCappedMultiplicitySum_cons_succ]
  omega

/-- The complete minimal-portion closure for one successor step.  Once the
canonical initial portion is known to satisfy its numerical bound, the
aperiodic extension property produces a trivial-stabilizer portion, and the
preceding theorem closes the DGM inequality. -/
theorem dgm_cons_bound_of_initialPortionBound_of_extension
    [Fintype A] (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hB : B.Nonempty) (hP : IsNonemptySetPartition P)
    (hn : n ≤ P.length)
    (hTargetStab :
      (layerSubsumSpectrum (B :: P) (n + 1)).addStab = {0})
    (hInitial : DGMInitialPortionBound B P n)
    (hext : DGMPortionExtensionProperty B P n) :
    rawDgmCappedMultiplicitySum (B :: P) (n + 1) - (n + 1) + 1 ≤
      (layerSubsumSpectrum (B :: P) (n + 1)).card := by
  have hC0 := dgmInitialPortion_isPortion B P n hB hP hn hInitial
  obtain ⟨C, hC, hCstab⟩ :=
    exists_dgmPortion_addStab_eq_singleton_of_extension
      B P n hC0 hTargetStab hext
  exact dgm_cons_bound_of_trivialStab_portion B P n C hC hCstab

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
