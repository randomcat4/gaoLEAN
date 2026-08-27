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

/-- The two descent cases combine without any excluded middle hidden in the
minimal-counterexample argument: inclusion gives either a smaller spectrum,
or equality and hence a smaller square defect. -/
theorem dgmPatternInnerMeasure_inter_union_lt
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A)) (μ : QuotientPattern K n)
    (hBC : ¬ B ⊆ C) (hCB : ¬ C ⊆ B) :
    DGMPatternInnerLt
      (dgmPatternInnerMeasure (dgmInterUnionLayers B C P) μ)
      (dgmPatternInnerMeasure (B :: C :: P) μ) := by
  have hsubset := patternSubsumSpectrum_inter_union_subset B C P μ
  have hcard := Finset.card_le_card hsubset
  rcases lt_or_eq_of_le hcard with hlt | heq
  · exact dgmPatternInnerMeasure_inter_union_lt_of_card_lt
      B C P μ hlt
  · have hspectrum :
        patternSubsumSpectrum (dgmInterUnionLayers B C P) μ =
          patternSubsumSpectrum (B :: C :: P) μ :=
      Finset.eq_of_subset_of_card_le hsubset heq.ge
    exact dgmPatternInnerMeasure_inter_union_lt_of_spectrum_eq
      B C P μ hBC hCB hspectrum

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

/-- The quotient coset in which every sum realizing a fixed pattern lies. -/
noncomputable def QuotientPattern.quotientSum
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    (μ : QuotientPattern K n) : A ⧸ K :=
  ∑ q : A ⧸ K, μ q • q

/-- Before prescribing a pattern, the quotient of a proof-relevant chosen
sum is the multiplicity-weighted sum of its selected quotient cosets. -/
theorem LayerSubsumChoice.coe_eq_sum_quotientMultiplicity
    {K : AddSubgroup A} [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) :
    (y : A ⧸ K) = ∑ q : A ⧸ K,
      h.quotientMultiplicity K q • q := by
  classical
  induction h with
  | zero P => simp [LayerSubsumChoice.quotientMultiplicity]
  | skip h ih => simpa [LayerSubsumChoice.quotientMultiplicity] using ih
  | @take B P n b y hb h ih =>
      rw [show ((b + y : A) : A ⧸ K) = (b : A ⧸ K) + (y : A ⧸ K) by rfl,
        ih]
      simp only [LayerSubsumChoice.quotientMultiplicity, add_nsmul,
        Finset.sum_add_distrib]
      have hindicator :
          (∑ q : A ⧸ K,
            (if (b : A ⧸ K) = q then 1 else 0) • q) =
            (b : A ⧸ K) := by
        simp [eq_comm]
      rw [hindicator]

theorem LayerSubsumChoice.coe_eq_pattern_quotientSum
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {y : A}
    {h : LayerSubsumChoice P n y} {μ : QuotientPattern K n}
    (hμ : h.RealizesPattern μ) :
    (y : A ⧸ K) = μ.quotientSum := by
  rw [h.coe_eq_sum_quotientMultiplicity]
  apply Finset.sum_congr rfl
  intro q _
  rw [hμ q]

/-- Hence a pattern spectrum is contained in one literal quotient fiber. -/
theorem patternSubsumSpectrum_quotient_eq
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n)
    {y : A} (hy : y ∈ patternSubsumSpectrum P μ) :
    (y : A ⧸ K) = μ.quotientSum := by
  obtain ⟨⟨h, hμ⟩⟩ :=
    (mem_patternSubsumSpectrum_iff P μ y).1 hy
  exact h.coe_eq_pattern_quotientSum hμ

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

/-- The two uncrossed/crossed pair-tail sumsets whose union is `D₁₂`. -/
noncomputable def dgmCrossedPairTail1
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : Finset A :=
  (dgmCosetSlice H B b₁ + dgmCosetSlice H C b₂) +
    patternSubsumSpectrum P νtail

noncomputable def dgmCrossedPairTail2
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : Finset A :=
  (dgmCosetSlice H B b₂ + dgmCosetSlice H C b₁) +
    patternSubsumSpectrum P νtail

theorem dgmCrossedPairTail1_subset_D12
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) :
    dgmCrossedPairTail1 B C P b₁ b₂ νtail ⊆
      dgmCrossedD12 B C P b₁ b₂ νtail := by
  intro y hy
  obtain ⟨u, hu, t, ht, rfl⟩ := Finset.mem_add.mp hy
  exact Finset.mem_add.mpr
    ⟨u, Finset.mem_union_left _ hu, t, ht, rfl⟩

theorem dgmCrossedPairTail2_subset_D12
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) :
    dgmCrossedPairTail2 B C P b₁ b₂ νtail ⊆
      dgmCrossedD12 B C P b₁ b₂ νtail := by
  intro y hy
  obtain ⟨u, hu, t, ht, rfl⟩ := Finset.mem_add.mp hy
  exact Finset.mem_add.mpr
    ⟨u, Finset.mem_union_right _ hu, t, ht, rfl⟩

/-- Stabilizer of `D₁₂`, followed by the source paper's saturated `D₁,D₂`.
The direct `+ H₁₂` representation is the one used in equations (1)--(5). -/
noncomputable def dgmCrossedH12
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : AddSubgroup A :=
  AddAction.stabilizer A
    (dgmCrossedD12 B C P b₁ b₂ νtail : Set A)

noncomputable def dgmCrossedD1
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : Finset A :=
  dgmCrossedPairTail1 B C P b₁ b₂ νtail +
    (dgmCrossedD12 B C P b₁ b₂ νtail).addStab

noncomputable def dgmCrossedD2
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : Finset A :=
  dgmCrossedPairTail2 B C P b₁ b₂ νtail +
    (dgmCrossedD12 B C P b₁ b₂ νtail).addStab

/-- Saturating either pair-tail component by `H₁₂` stays inside `D₁₂`,
because `H₁₂` is exactly the stabilizer of `D₁₂`. -/
theorem dgmCrossedD1_subset_D12
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty) :
    dgmCrossedD1 B C P b₁ b₂ νtail ⊆
      dgmCrossedD12 B C P b₁ b₂ νtail := by
  intro y hy
  rw [dgmCrossedD1] at hy
  obtain ⟨x, hx, a, ha, rfl⟩ := Finset.mem_add.mp hy
  have hxD12 := dgmCrossedPairTail1_subset_D12
    B C P b₁ b₂ νtail hx
  have htranslate :=
    (Finset.mem_addStab hD12).1 ha
  have hmem : a + x ∈ a +ᵥ dgmCrossedD12 B C P b₁ b₂ νtail :=
    Finset.mem_vadd_finset.mpr ⟨x, hxD12, rfl⟩
  rw [htranslate] at hmem
  simpa [add_comm] using hmem

theorem dgmCrossedD2_subset_D12
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty) :
    dgmCrossedD2 B C P b₁ b₂ νtail ⊆
      dgmCrossedD12 B C P b₁ b₂ νtail := by
  intro y hy
  rw [dgmCrossedD2] at hy
  obtain ⟨x, hx, a, ha, rfl⟩ := Finset.mem_add.mp hy
  have hxD12 := dgmCrossedPairTail2_subset_D12
    B C P b₁ b₂ νtail hx
  have htranslate :=
    (Finset.mem_addStab hD12).1 ha
  have hmem : a + x ∈ a +ᵥ dgmCrossedD12 B C P b₁ b₂ νtail :=
    Finset.mem_vadd_finset.mpr ⟨x, hxD12, rfl⟩
  rw [htranslate] at hmem
  simpa [add_comm] using hmem

/-- The stabilizer used to saturate a nonempty finite sumset remains in the
stabilizer after saturation.  This is the abstract `H₁₂ ≤ Hᵢ` step. -/
theorem addStab_subset_addStab_add_addStab
    (X Y : Finset A) (hX : X.Nonempty) (hY : Y.Nonempty) :
    X.addStab ⊆ (Y + X.addStab).addStab := by
  intro a ha
  have hsum : (Y + X.addStab).Nonempty :=
    hY.add ⟨0, hX.zero_mem_addStab⟩
  apply (Finset.mem_addStab hsum).2
  apply Finset.eq_of_subset_of_card_le
  · intro z hz
    obtain ⟨w, hw, rfl⟩ := Finset.mem_vadd_finset.mp hz
    obtain ⟨y, hy, s, hs, rfl⟩ := Finset.mem_add.mp hw
    have ha' : a ∈ AddAction.stabilizer A (X : Set A) := by
      have haSet : a ∈ (X.addStab : Set A) := ha
      rwa [Finset.coe_addStab hX] at haSet
    have hs' : s ∈ AddAction.stabilizer A (X : Set A) := by
      have hsSet : s ∈ (X.addStab : Set A) := hs
      rwa [Finset.coe_addStab hX] at hsSet
    have has : a + s ∈ X.addStab := by
      rw [← Finset.mem_coe, Finset.coe_addStab hX]
      exact (AddAction.stabilizer A (X : Set A)).add_mem ha' hs'
    exact Finset.mem_add.mpr ⟨y, hy, a + s, has, by ac_rfl⟩
  · simp

theorem dgmCrossedPairTail1_nonempty
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    {b₁ b₂ : A} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (htail : (patternSubsumSpectrum P νtail).Nonempty) :
    (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty := by
  have hslice₁ : (dgmCosetSlice H B b₁).Nonempty :=
    ⟨b₁, mem_dgmCosetSlice_self H B hb₁⟩
  have hslice₂ : (dgmCosetSlice H C b₂).Nonempty :=
    ⟨b₂, mem_dgmCosetSlice_self H C hb₂⟩
  exact (hslice₁.add hslice₂).add htail

theorem dgmCrossedPairTail2_nonempty
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    {b₁ b₂ : A} (hb₂B : b₂ ∈ B) (hb₁C : b₁ ∈ C)
    (νtail : QuotientPattern H k)
    (htail : (patternSubsumSpectrum P νtail).Nonempty) :
    (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty := by
  have hslice₂B : (dgmCosetSlice H B b₂).Nonempty :=
    ⟨b₂, mem_dgmCosetSlice_self H B hb₂B⟩
  have hslice₁C : (dgmCosetSlice H C b₁).Nonempty :=
    ⟨b₁, mem_dgmCosetSlice_self H C hb₁C⟩
  exact (hslice₂B.add hslice₁C).add htail

/-- The literal finite-stabilizer inclusions `H₁₂ ≤ H₁` and, when the
crossed component is nonempty, `H₁₂ ≤ H₂`. -/
theorem dgmCrossedH12_subset_D1_addStab
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty) :
    (dgmCrossedD12 B C P b₁ b₂ νtail).addStab ⊆
      (dgmCrossedD1 B C P b₁ b₂ νtail).addStab := by
  simpa [dgmCrossedD1] using
    addStab_subset_addStab_add_addStab
      (dgmCrossedD12 B C P b₁ b₂ νtail)
      (dgmCrossedPairTail1 B C P b₁ b₂ νtail) hD12 hpair

theorem dgmCrossedH12_subset_D2_addStab
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty) :
    (dgmCrossedD12 B C P b₁ b₂ νtail).addStab ⊆
      (dgmCrossedD2 B C P b₁ b₂ νtail).addStab := by
  simpa [dgmCrossedD2] using
    addStab_subset_addStab_add_addStab
      (dgmCrossedD12 B C P b₁ b₂ νtail)
      (dgmCrossedPairTail2 B C P b₁ b₂ νtail) hD12 hpair

/-- The bundled subgroup `dgmCrossedH12` is literally the subgroup whose
finite carrier is `(D₁₂).addStab`. -/
theorem coe_dgmCrossedH12_eq_addStab
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty) :
    (dgmCrossedH12 B C P b₁ b₂ νtail : Set A) =
      ((dgmCrossedD12 B C P b₁ b₂ νtail).addStab : Set A) := by
  rw [Finset.coe_addStab hD12]
  rfl

theorem dgmCrossedH12_le_D1_stabilizer
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty) :
    dgmCrossedH12 B C P b₁ b₂ νtail ≤
      AddAction.stabilizer A
        (dgmCrossedD1 B C P b₁ b₂ νtail : Set A) := by
  intro a ha
  have haFin : a ∈ (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
    have haSet : a ∈ (dgmCrossedH12 B C P b₁ b₂ νtail : Set A) := ha
    rw [coe_dgmCrossedH12_eq_addStab B C P b₁ b₂ νtail hD12] at haSet
    exact haSet
  have haD1 := dgmCrossedH12_subset_D1_addStab
    B C P b₁ b₂ νtail hD12 hpair haFin
  have hD1 : (dgmCrossedD1 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD1]
    exact hpair.add ⟨0, hD12.zero_mem_addStab⟩
  have haSet : a ∈
      ((dgmCrossedD1 B C P b₁ b₂ νtail).addStab : Set A) := haD1
  rwa [Finset.coe_addStab hD1] at haSet

theorem dgmCrossedH12_le_D2_stabilizer
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty) :
    dgmCrossedH12 B C P b₁ b₂ νtail ≤
      AddAction.stabilizer A
        (dgmCrossedD2 B C P b₁ b₂ νtail : Set A) := by
  intro a ha
  have haFin : a ∈ (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
    have haSet : a ∈ (dgmCrossedH12 B C P b₁ b₂ νtail : Set A) := ha
    rw [coe_dgmCrossedH12_eq_addStab B C P b₁ b₂ νtail hD12] at haSet
    exact haSet
  have haD2 := dgmCrossedH12_subset_D2_addStab
    B C P b₁ b₂ νtail hD12 hpair haFin
  have hD2 : (dgmCrossedD2 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD2]
    exact hpair.add ⟨0, hD12.zero_mem_addStab⟩
  have haSet : a ∈
      ((dgmCrossedD2 B C P b₁ b₂ νtail).addStab : Set A) := haD2
  rwa [Finset.coe_addStab hD2] at haSet

/-- A nonempty finite set properly contained in one `H`-coset has stabilizer
strictly smaller than `H`.  This is the exact proper-coset argument used for
`H₁₂,H₁,H₂ < H`. -/
theorem stabilizer_lt_of_proper_quotientFiber
    (H : AddSubgroup A) (D : Finset A) (hD : D.Nonempty)
    (q : A ⧸ H)
    (hfiber : ∀ x ∈ D, (x : A ⧸ H) = q)
    {y : A} (hyq : (y : A ⧸ H) = q) (hyD : y ∉ D) :
    AddAction.stabilizer A (D : Set A) < H := by
  have hle : AddAction.stabilizer A (D : Set A) ≤ H := by
    intro a ha
    have hDcopy := hD
    obtain ⟨x, hx⟩ := hDcopy
    have haFin : a ∈ D.addStab := by
      have haSet : a ∈ (AddAction.stabilizer A (D : Set A) : Set A) := ha
      rw [← Finset.coe_addStab hD] at haSet
      exact haSet
    have htranslate := (Finset.mem_addStab hD).1 haFin
    have hax : a + x ∈ D := by
      have : a + x ∈ a +ᵥ D :=
        Finset.mem_vadd_finset.mpr ⟨x, hx, rfl⟩
      rwa [htranslate] at this
    have hqeq : (a + x : A ⧸ H) = (x : A ⧸ H) :=
      (hfiber (a + x) hax).trans (hfiber x hx).symm
    have hzero : (a : A ⧸ H) = 0 := by
      apply add_right_cancel (b := (x : A ⧸ H))
      simpa using hqeq
    exact (QuotientAddGroup.eq_zero_iff a).1 hzero
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hDcopy := hD
  obtain ⟨x, hx⟩ := hDcopy
  let a : A := y - x
  have haH : a ∈ H := by
    exact QuotientAddGroup.eq_iff_sub_mem.mp (hyq.trans (hfiber x hx).symm)
  have ha : a ∈ AddAction.stabilizer A (D : Set A) := by
    rw [heq]
    exact haH
  have haFin : a ∈ D.addStab := by
    have haSet : a ∈ (AddAction.stabilizer A (D : Set A) : Set A) := ha
    rw [← Finset.coe_addStab hD] at haSet
    exact haSet
  have htranslate := (Finset.mem_addStab hD).1 haFin
  have hay : a + x ∈ D := by
    have : a + x ∈ a +ᵥ D :=
      Finset.mem_vadd_finset.mpr ⟨x, hx, rfl⟩
    rwa [htranslate] at this
  apply hyD
  simpa [a] using hay

noncomputable def dgmCrossedH1
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : AddSubgroup A :=
  AddAction.stabilizer A
    (dgmCrossedD1 B C P b₁ b₂ νtail : Set A)

noncomputable def dgmCrossedH2
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k) : AddSubgroup A :=
  AddAction.stabilizer A
    (dgmCrossedD2 B C P b₁ b₂ νtail : Set A)

/-- An escaping point in the same pattern coset proves all three source
stabilizers are proper in `H` (for `D₂`, once its crossed component is
nonempty). -/
theorem dgmCrossedH12_lt_of_escape
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    {y : A} (hy : y ∈ patternSubsumSpectrum (B :: C :: P) ν)
    (hyD12 : y ∉ dgmCrossedD12 B C P b₁ b₂ νtail) :
    dgmCrossedH12 B C P b₁ b₂ νtail < H := by
  apply stabilizer_lt_of_proper_quotientFiber H
    (dgmCrossedD12 B C P b₁ b₂ νtail) hD12 ν.quotientSum
  · intro x hx
    exact patternSubsumSpectrum_quotient_eq _ ν
      (dgmCrossedD12_subset_patternSubsumSpectrum
        B C P ν b₁ b₂ νtail hext hx)
  · exact patternSubsumSpectrum_quotient_eq _ ν hy
  · exact hyD12

theorem dgmCrossedH1_lt_of_escape
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    {y : A} (hy : y ∈ patternSubsumSpectrum (B :: C :: P) ν)
    (hyD12 : y ∉ dgmCrossedD12 B C P b₁ b₂ νtail) :
    dgmCrossedH1 B C P b₁ b₂ νtail < H := by
  have hD1 : (dgmCrossedD1 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD1]
    exact hpair.add ⟨0, hD12.zero_mem_addStab⟩
  apply stabilizer_lt_of_proper_quotientFiber H
    (dgmCrossedD1 B C P b₁ b₂ νtail) hD1 ν.quotientSum
  · intro x hx
    have hxD12 := dgmCrossedD1_subset_D12
      B C P b₁ b₂ νtail hD12 hx
    exact patternSubsumSpectrum_quotient_eq _ ν
      (dgmCrossedD12_subset_patternSubsumSpectrum
        B C P ν b₁ b₂ νtail hext hxD12)
  · exact patternSubsumSpectrum_quotient_eq _ ν hy
  · intro hyD1
    exact hyD12 (dgmCrossedD1_subset_D12
      B C P b₁ b₂ νtail hD12 hyD1)

theorem dgmCrossedH2_lt_of_escape
    [Fintype A]
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty)
    {y : A} (hy : y ∈ patternSubsumSpectrum (B :: C :: P) ν)
    (hyD12 : y ∉ dgmCrossedD12 B C P b₁ b₂ νtail) :
    dgmCrossedH2 B C P b₁ b₂ νtail < H := by
  have hD2 : (dgmCrossedD2 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD2]
    exact hpair.add ⟨0, hD12.zero_mem_addStab⟩
  apply stabilizer_lt_of_proper_quotientFiber H
    (dgmCrossedD2 B C P b₁ b₂ νtail) hD2 ν.quotientSum
  · intro x hx
    have hxD12 := dgmCrossedD2_subset_D12
      B C P b₁ b₂ νtail hD12 hx
    exact patternSubsumSpectrum_quotient_eq _ ν
      (dgmCrossedD12_subset_patternSubsumSpectrum
        B C P ν b₁ b₂ νtail hext hxD12)
  · exact patternSubsumSpectrum_quotient_eq _ ν hy
  · intro hyD2
    exact hyD12 (dgmCrossedD2_subset_D12
      B C P b₁ b₂ νtail hD12 hyD2)

/-! ## The finite sets in the Ξ-difference claim -/

/-- The literal finite carrier of a subgroup of the ambient finite group. -/
noncomputable def dgmSubgroupFinset [Fintype A]
    (L : AddSubgroup A) : Finset A := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  exact (Finset.univ : Finset L).map
    ⟨fun x : L ↦ (x : A), Subtype.val_injective⟩

@[simp]
theorem mem_dgmSubgroupFinset_iff [Fintype A]
    (L : AddSubgroup A) (x : A) :
    x ∈ dgmSubgroupFinset L ↔ x ∈ L := by
  classical
  simp [dgmSubgroupFinset]

@[simp]
theorem card_dgmSubgroupFinset [Fintype A]
    (L : AddSubgroup A) :
    (dgmSubgroupFinset L).card = Nat.card L := by
  classical
  letI : Fintype L := Fintype.ofFinite L
  simp [dgmSubgroupFinset, Nat.card_eq_fintype_card]

/-- A literal `H`-coset, represented as one quotient fiber. -/
noncomputable def dgmCosetFiber [Fintype A]
    (H : AddSubgroup A) (b : A) : Finset A := by
  classical
  exact Finset.univ.filter fun x ↦ (x : A ⧸ H) = (b : A ⧸ H)

@[simp]
theorem mem_dgmCosetFiber_iff [Fintype A]
    (H : AddSubgroup A) (b x : A) :
    x ∈ dgmCosetFiber H b ↔
      (x : A ⧸ H) = (b : A ⧸ H) := by
  classical
  simp [dgmCosetFiber]

noncomputable def dgmSubgroupEquivCosetFiber [Fintype A]
    (H : AddSubgroup A) (b : A) :
    H ≃ {x : A // x ∈ dgmCosetFiber H b} where
  toFun h := ⟨b + (h : A), by
    apply (mem_dgmCosetFiber_iff H b _).2
    rw [show ((b + (h : A) : A) : A ⧸ H) =
        (b : A ⧸ H) + ((h : A) : A ⧸ H) by rfl,
      (QuotientAddGroup.eq_zero_iff (h : A)).2 h.2, add_zero]⟩
  invFun x := ⟨(x : A) - b, by
    exact QuotientAddGroup.eq_iff_sub_mem.mp
      ((mem_dgmCosetFiber_iff H b (x : A)).1 x.2)⟩
  left_inv h := by
    apply Subtype.ext
    simp
  right_inv x := by
    apply Subtype.ext
    simp

@[simp]
theorem card_dgmCosetFiber [Fintype A]
    (H : AddSubgroup A) (b : A) :
    (dgmCosetFiber H b).card = Nat.card H := by
  classical
  letI : Fintype H := Fintype.ofFinite H
  calc
    (dgmCosetFiber H b).card =
        Fintype.card {x : A // x ∈ dgmCosetFiber H b} :=
      (Fintype.card_coe (dgmCosetFiber H b)).symm
    _ = Fintype.card H :=
      Fintype.card_congr (dgmSubgroupEquivCosetFiber H b).symm
    _ = Nat.card H := Nat.card_eq_fintype_card.symm

/-- Saturation of one sliced leading layer by `L`. -/
noncomputable def dgmSingleSliceSaturation [Fintype A]
    (H L : AddSubgroup A) (B : Finset A) (b : A) : Finset A :=
  dgmCosetSlice H B b + dgmSubgroupFinset L

/-- The `H'`-saturation of the portions of both leading layers in one
fixed `H`-coset. -/
noncomputable def dgmPairSliceSaturation [Fintype A]
    (H L : AddSubgroup A) (B C : Finset A) (b : A) : Finset A :=
  (dgmCosetSlice H B b ∪ dgmCosetSlice H C b) +
    dgmSubgroupFinset L

theorem dgmPairSliceSaturation_eq_union [Fintype A]
    (H L : AddSubgroup A) (B C : Finset A) (b : A) :
    dgmPairSliceSaturation H L B C b =
      dgmSingleSliceSaturation H L B b ∪
        dgmSingleSliceSaturation H L C b := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, l, hl, rfl⟩ := Finset.mem_add.mp hy
    rcases Finset.mem_union.mp hx with hx | hx
    · exact Finset.mem_union_left _ (Finset.mem_add.mpr ⟨x, hx, l, hl, rfl⟩)
    · exact Finset.mem_union_right _ (Finset.mem_add.mpr ⟨x, hx, l, hl, rfl⟩)
  · intro hy
    rcases Finset.mem_union.mp hy with hy | hy
    · obtain ⟨x, hx, l, hl, rfl⟩ := Finset.mem_add.mp hy
      exact Finset.mem_add.mpr
        ⟨x, Finset.mem_union_left _ hx, l, hl, rfl⟩
    · obtain ⟨x, hx, l, hl, rfl⟩ := Finset.mem_add.mp hy
      exact Finset.mem_add.mpr
        ⟨x, Finset.mem_union_right _ hx, l, hl, rfl⟩

/-- The source proof's missing sets `X'` and `Y'`. -/
noncomputable def dgmMissingPairCoset [Fintype A]
    (H L : AddSubgroup A) (B C : Finset A) (b : A) : Finset A :=
  dgmCosetFiber H b \ dgmPairSliceSaturation H L B C b

theorem dgmPairSliceSaturation_subset_cosetFiber [Fintype A]
    (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b : A) :
    dgmPairSliceSaturation H L B C b ⊆ dgmCosetFiber H b := by
  intro y hy
  obtain ⟨x, hx, l, hl, rfl⟩ := Finset.mem_add.mp hy
  have hxq : (x : A ⧸ H) = (b : A ⧸ H) := by
    rcases Finset.mem_union.mp hx with hx | hx
    · exact (mem_dgmCosetSlice_iff H B b x).1 hx |>.2
    · exact (mem_dgmCosetSlice_iff H C b x).1 hx |>.2
  have hlH : l ∈ H := hLH ((mem_dgmSubgroupFinset_iff L l).1 hl)
  apply (mem_dgmCosetFiber_iff H b (x + l)).2
  rw [show ((x + l : A) : A ⧸ H) = (x : A ⧸ H) + (l : A ⧸ H) by rfl,
    (QuotientAddGroup.eq_zero_iff l).2 hlH, add_zero, hxq]

theorem dgmCosetFiber_eq_missing_union_saturation [Fintype A]
    (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b : A) :
    dgmCosetFiber H b =
      dgmMissingPairCoset H L B C b ∪
        dgmPairSliceSaturation H L B C b := by
  unfold dgmMissingPairCoset
  exact (Finset.sdiff_union_of_subset
    (dgmPairSliceSaturation_subset_cosetFiber H L hLH B C b)).symm

theorem card_missing_add_pairSaturation [Fintype A]
    (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b : A) :
    (dgmMissingPairCoset H L B C b).card +
        (dgmPairSliceSaturation H L B C b).card = Nat.card H := by
  unfold dgmMissingPairCoset
  rw [Finset.card_sdiff_add_card_eq_card
    (dgmPairSliceSaturation_subset_cosetFiber H L hLH B C b),
    card_dgmCosetFiber]

/-- Cardinal form of the two coset-cover equalities used in the final
contradiction: one full `H`-coset is covered by its missing set and the two
individual `L`-saturated slices. -/
theorem card_cosetFiber_le_missing_add_singleSaturations [Fintype A]
    (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b : A) :
    Nat.card H ≤ (dgmMissingPairCoset H L B C b).card +
      (dgmSingleSliceSaturation H L B b).card +
      (dgmSingleSliceSaturation H L C b).card := by
  rw [← card_dgmCosetFiber H b,
    dgmCosetFiber_eq_missing_union_saturation H L hLH B C b,
    dgmPairSliceSaturation_eq_union]
  calc
    (dgmMissingPairCoset H L B C b ∪
        (dgmSingleSliceSaturation H L B b ∪
          dgmSingleSliceSaturation H L C b)).card ≤
        (dgmMissingPairCoset H L B C b).card +
          (dgmSingleSliceSaturation H L B b ∪
            dgmSingleSliceSaturation H L C b).card :=
      Finset.card_union_le _ _
    _ ≤ (dgmMissingPairCoset H L B C b).card +
          ((dgmSingleSliceSaturation H L B b).card +
            (dgmSingleSliceSaturation H L C b).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = _ := by omega

theorem dgmMissingPairCoset_subset_cosetFiber [Fintype A]
    (H L : AddSubgroup A) (B C : Finset A) (b : A) :
    dgmMissingPairCoset H L B C b ⊆ dgmCosetFiber H b := by
  exact Finset.sdiff_subset

theorem disjoint_dgmMissingPairCoset_of_ne [Fintype A]
    (H L : AddSubgroup A) (B C : Finset A) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H)) :
    Disjoint (dgmMissingPairCoset H L B C b₁)
      (dgmMissingPairCoset H L B C b₂) := by
  rw [Finset.disjoint_left]
  intro x hx₁ hx₂
  have hq₁ := (mem_dgmCosetFiber_iff H b₁ x).1
    (dgmMissingPairCoset_subset_cosetFiber H L B C b₁ hx₁)
  have hq₂ := (mem_dgmCosetFiber_iff H b₂ x).1
    (dgmMissingPairCoset_subset_cosetFiber H L B C b₂ hx₂)
  exact hne (hq₁.symm.trans hq₂)

theorem card_missingUnion_add_pairSaturations [Fintype A]
    (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H)) :
    (dgmMissingPairCoset H L B C b₁ ∪
        dgmMissingPairCoset H L B C b₂).card +
      (dgmPairSliceSaturation H L B C b₁).card +
      (dgmPairSliceSaturation H L B C b₂).card =
        2 * Nat.card H := by
  have h₁ := card_missing_add_pairSaturation H L hLH B C b₁
  have h₂ := card_missing_add_pairSaturation H L hLH B C b₂
  rw [Finset.card_union_of_disjoint
    (disjoint_dgmMissingPairCoset_of_ne H L B C b₁ b₂ hne)]
  omega

/-- The final set-theoretic contradiction on page 14 of the source proof.
Once equations (4)--(5) yield the displayed strict upper bound, the two
coset-cover inequalities force its negation. -/
theorem dgmFinalCosetCoverContradiction [Fintype A]
    (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H))
    (hstrict :
      2 * Nat.card H >
        (dgmSingleSliceSaturation H L B b₁).card +
        (dgmSingleSliceSaturation H L C b₁).card +
        (dgmSingleSliceSaturation H L B b₂).card +
        (dgmSingleSliceSaturation H L C b₂).card +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card + Nat.card L) :
    False := by
  have hcover₁ := card_cosetFiber_le_missing_add_singleSaturations
    H L hLH B C b₁
  have hcover₂ := card_cosetFiber_le_missing_add_singleSaturations
    H L hLH B C b₂
  have hdisjoint := disjoint_dgmMissingPairCoset_of_ne
    H L B C b₁ b₂ hne
  have hunion :
      (dgmMissingPairCoset H L B C b₁ ∪
        dgmMissingPairCoset H L B C b₂).card =
      (dgmMissingPairCoset H L B C b₁).card +
        (dgmMissingPairCoset H L B C b₂).card :=
    Finset.card_union_of_disjoint hdisjoint
  rw [hunion] at hstrict
  omega

/-- Exact non-strict arithmetic remaining after equations (4)--(5).  The
strictness in the source proof is retained by the positive extra subgroup
term `l`; no unjustified conversion of four weak inequalities to a strict
one is used. -/
theorem dgmFourBounds_extra_le_two_mul
    (Hc s₁ s₂ h₁ h₂ l m : ℕ)
    (hh₁ : h₁ ≤ s₁) (hh₂ : h₂ ≤ s₂)
    (h4₁ : s₁ + h₁ ≤ Hc) (h4₂ : s₂ + h₂ ≤ Hc)
    (h5₁ : s₁ - h₁ + l + m ≤ Hc)
    (h5₂ : s₂ - h₂ + l + m ≤ Hc) :
    s₁ + s₂ + l + m ≤ 2 * Hc := by
  omega

/-- Correct final page-14 contradiction in the form actually delivered by
the sum of (4)--(5): the four saturated slice sizes, the missing union, and
one positive `|H₁₂|` fit under `2|H|`.  The two coset covers omit that positive
term, producing the contradiction. -/
theorem dgmFinalCosetCoverContradiction_of_extra_le
    [Fintype A] (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H))
    (hbound :
      (dgmSingleSliceSaturation H L B b₁).card +
        (dgmSingleSliceSaturation H L C b₁).card +
        (dgmSingleSliceSaturation H L B b₂).card +
        (dgmSingleSliceSaturation H L C b₂).card +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card + Nat.card L ≤
          2 * Nat.card H) :
    False := by
  have hcover₁ := card_cosetFiber_le_missing_add_singleSaturations
    H L hLH B C b₁
  have hcover₂ := card_cosetFiber_le_missing_add_singleSaturations
    H L hLH B C b₂
  have hunion :
      (dgmMissingPairCoset H L B C b₁ ∪
        dgmMissingPairCoset H L B C b₂).card =
      (dgmMissingPairCoset H L B C b₁).card +
        (dgmMissingPairCoset H L B C b₂).card :=
    Finset.card_union_of_disjoint
      (disjoint_dgmMissingPairCoset_of_ne H L B C b₁ b₂ hne)
  have hLpos : 0 < Nat.card L := Nat.card_pos
  rw [hunion] at hbound
  omega

/-- Concrete `(4)+(5)` endpoint for the crossed construction.  The first
pair uses `B∩(b₁+H)` with `C∩(b₂+H)` and the second uses the crossed pair;
their sum is exactly the four terms in the final two coset covers. -/
theorem dgmCrossedFourBoundsContradiction
    [Fintype A] (H L H₁ H₂ : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H))
    (hh₁ : Nat.card H₁ ≤
      (dgmSingleSliceSaturation H L B b₁).card +
        (dgmSingleSliceSaturation H L C b₂).card)
    (hh₂ : Nat.card H₂ ≤
      (dgmSingleSliceSaturation H L B b₂).card +
        (dgmSingleSliceSaturation H L C b₁).card)
    (h4₁ :
      (dgmSingleSliceSaturation H L B b₁).card +
          (dgmSingleSliceSaturation H L C b₂).card + Nat.card H₁ ≤
        Nat.card H)
    (h4₂ :
      (dgmSingleSliceSaturation H L B b₂).card +
          (dgmSingleSliceSaturation H L C b₁).card + Nat.card H₂ ≤
        Nat.card H)
    (h5₁ :
      ((dgmSingleSliceSaturation H L B b₁).card +
          (dgmSingleSliceSaturation H L C b₂).card) - Nat.card H₁ +
          Nat.card L +
          (dgmMissingPairCoset H L B C b₁ ∪
            dgmMissingPairCoset H L B C b₂).card ≤ Nat.card H)
    (h5₂ :
      ((dgmSingleSliceSaturation H L B b₂).card +
          (dgmSingleSliceSaturation H L C b₁).card) - Nat.card H₂ +
          Nat.card L +
          (dgmMissingPairCoset H L B C b₁ ∪
            dgmMissingPairCoset H L B C b₂).card ≤ Nat.card H) :
    False := by
  let s₁ := (dgmSingleSliceSaturation H L B b₁).card +
    (dgmSingleSliceSaturation H L C b₂).card
  let s₂ := (dgmSingleSliceSaturation H L B b₂).card +
    (dgmSingleSliceSaturation H L C b₁).card
  let m := (dgmMissingPairCoset H L B C b₁ ∪
    dgmMissingPairCoset H L B C b₂).card
  have hbound' := dgmFourBounds_extra_le_two_mul
    (Nat.card H) s₁ s₂ (Nat.card H₁) (Nat.card H₂) (Nat.card L) m
    (by simpa [s₁] using hh₁) (by simpa [s₂] using hh₂)
    (by simpa [s₁] using h4₁) (by simpa [s₂] using h4₂)
    (by simpa [s₁, m] using h5₁) (by simpa [s₂, m] using h5₂)
  apply dgmFinalCosetCoverContradiction_of_extra_le
    H L hLH B C b₁ b₂ hne
  dsimp only [s₁, s₂, m] at hbound'
  omega

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

theorem quotientLayer_union (K : AddSubgroup A)
    [DecidableEq (A ⧸ K)]
    (B C : Finset A) :
    quotientLayer K (B ∪ C) =
      (quotientLayer K B) ∪ (quotientLayer K C) := by
  classical
  ext q
  simp only [mem_quotientLayer_iff, Finset.mem_union]
  constructor
  · rintro ⟨x, hx, hxq⟩
    rcases hx with hx | hx
    · exact Or.inl ⟨x, hx, hxq⟩
    · exact Or.inr ⟨x, hx, hxq⟩
  · rintro (⟨x, hx, hxq⟩ | ⟨x, hx, hxq⟩)
    · exact ⟨x, Or.inl hx, hxq⟩
    · exact ⟨x, Or.inr hx, hxq⟩

theorem quotientLayer_inter_subset_left (K : AddSubgroup A)
    (B C : Finset A) :
    quotientLayer K (B ∩ C) ⊆ quotientLayer K B := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_quotientLayer_iff K (B ∩ C) q).1 hq
  exact (mem_quotientLayer_iff K B _).2
    ⟨x, (Finset.mem_inter.mp hx).1, rfl⟩

theorem quotientLayer_inter_subset_right (K : AddSubgroup A)
    (B C : Finset A) :
    quotientLayer K (B ∩ C) ⊆ quotientLayer K C := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_quotientLayer_iff K (B ∩ C) q).1 hq
  exact (mem_quotientLayer_iff K C _).2
    ⟨x, (Finset.mem_inter.mp hx).2, rfl⟩

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

/-- Intersection--union can merge two quotient incidences, but never creates
more of them.  This is the exact `Ξ_K(A') ≤ Ξ_K(A)` direction in the source
minimal-counterexample proof. -/
theorem quotientLayerMultiplicity_inter_union_le
    (K : AddSubgroup A) (B C : Finset A)
    (P : List (Finset A)) (q : A ⧸ K) :
    quotientLayerMultiplicity K (dgmInterUnionLayers B C P) q ≤
      quotientLayerMultiplicity K (B :: C :: P) q := by
  classical
  change quotientLayerMultiplicity K ((B ∩ C) :: (B ∪ C) :: P) q ≤ _
  have hU : q ∈ quotientLayer K (B ∪ C) ↔
      q ∈ quotientLayer K B ∨ q ∈ quotientLayer K C := by
    rw [quotientLayer_union, Finset.mem_union]
  have hIB := quotientLayer_inter_subset_left K B C
  have hIC := quotientLayer_inter_subset_right K B C
  by_cases hB : q ∈ quotientLayer K B
  · by_cases hC : q ∈ quotientLayer K C
    · by_cases hI : q ∈ quotientLayer K (B ∩ C)
      · rw [quotientLayerMultiplicity_cons_of_mem K (B ∩ C)
            ((B ∪ C) :: P) q hI,
          quotientLayerMultiplicity_cons_of_mem K (B ∪ C) P q
            (hU.mpr (Or.inl hB)),
          quotientLayerMultiplicity_cons_of_mem K B (C :: P) q hB,
          quotientLayerMultiplicity_cons_of_mem K C P q hC]
      · rw [quotientLayerMultiplicity_cons_of_not_mem K (B ∩ C)
            ((B ∪ C) :: P) q hI,
          quotientLayerMultiplicity_cons_of_mem K (B ∪ C) P q
            (hU.mpr (Or.inl hB)),
          quotientLayerMultiplicity_cons_of_mem K B (C :: P) q hB,
          quotientLayerMultiplicity_cons_of_mem K C P q hC]
        omega
    · have hI : q ∉ quotientLayer K (B ∩ C) := fun h ↦ hC (hIC h)
      rw [quotientLayerMultiplicity_cons_of_not_mem K (B ∩ C)
            ((B ∪ C) :: P) q hI,
          quotientLayerMultiplicity_cons_of_mem K (B ∪ C) P q
            (hU.mpr (Or.inl hB)),
          quotientLayerMultiplicity_cons_of_mem K B (C :: P) q hB,
          quotientLayerMultiplicity_cons_of_not_mem K C P q hC]
  · by_cases hC : q ∈ quotientLayer K C
    · have hI : q ∉ quotientLayer K (B ∩ C) := fun h ↦ hB (hIB h)
      rw [quotientLayerMultiplicity_cons_of_not_mem K (B ∩ C)
            ((B ∪ C) :: P) q hI,
          quotientLayerMultiplicity_cons_of_mem K (B ∪ C) P q
            (hU.mpr (Or.inr hC)),
          quotientLayerMultiplicity_cons_of_not_mem K B (C :: P) q hB,
          quotientLayerMultiplicity_cons_of_mem K C P q hC]
    · have hI : q ∉ quotientLayer K (B ∩ C) := fun h ↦ hB (hIB h)
      have hnotU : q ∉ quotientLayer K (B ∪ C) := by
        exact fun h ↦ (hU.mp h).elim hB hC
      rw [quotientLayerMultiplicity_cons_of_not_mem K (B ∩ C)
            ((B ∪ C) :: P) q hI,
          quotientLayerMultiplicity_cons_of_not_mem K (B ∪ C) P q hnotU,
          quotientLayerMultiplicity_cons_of_not_mem K B (C :: P) q hB,
          quotientLayerMultiplicity_cons_of_not_mem K C P q hC]

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

theorem dgmCappedMultiplicitySum_inter_union_le
    [Fintype A] (K : AddSubgroup A)
    (B C : Finset A) (P : List (Finset A)) (n : ℕ) :
    dgmCappedMultiplicitySum K (dgmInterUnionLayers B C P) n ≤
      dgmCappedMultiplicitySum K (B :: C :: P) n := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  rw [dgmCappedMultiplicitySum, dgmCappedMultiplicitySum]
  apply Finset.sum_le_sum
  intro q _
  exact min_le_min (Nat.le_refl n)
    (quotientLayerMultiplicity_inter_union_le K B C P q)

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

/-- Adding the two leading layers can only increase every quotient-layer
multiplicity. -/
theorem quotientLayerMultiplicity_le_cons
    (K : AddSubgroup A) (B : Finset A)
    (P : List (Finset A)) (q : A ⧸ K) :
    quotientLayerMultiplicity K P q ≤
      quotientLayerMultiplicity K (B :: P) q := by
  classical
  by_cases hqB : q ∈ quotientLayer K B
  · rw [quotientLayerMultiplicity_cons_of_mem K B P q hqB]
    omega
  · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hqB]

theorem quotientLayerMultiplicity_le_cons_cons
    (K : AddSubgroup A) (B C : Finset A)
    (P : List (Finset A)) (q : A ⧸ K) :
    quotientLayerMultiplicity K P q ≤
      quotientLayerMultiplicity K (B :: C :: P) q := by
  exact (quotientLayerMultiplicity_le_cons K C P q).trans
    (quotientLayerMultiplicity_le_cons K B (C :: P) q)

/-- Consequently the capped Ξ-term for the tail at weight `k` is at most
the transformed full term at weight `k+2`; the subtraction defining the
two-layer gain is therefore honest (nontruncated). -/
theorem dgmCappedMultiplicitySum_tail_le_inter_union
    [Fintype A] (K : AddSubgroup A)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) :
    dgmCappedMultiplicitySum K P k ≤
      dgmCappedMultiplicitySum K (dgmInterUnionLayers B C P) (k + 2) := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  rw [dgmCappedMultiplicitySum, dgmCappedMultiplicitySum]
  apply Finset.sum_le_sum
  intro q _
  exact min_le_min (by omega) (by
    simpa [dgmInterUnionLayers] using
      quotientLayerMultiplicity_le_cons_cons K (B ∩ C) (B ∪ C) P q)

noncomputable def dgmXiTwoGain [Fintype A]
    (K : AddSubgroup A) (B C : Finset A)
    (P : List (Finset A)) (k : ℕ) : ℕ :=
  dgmCappedMultiplicitySum K (dgmInterUnionLayers B C P) (k + 2) -
    dgmCappedMultiplicitySum K P k

theorem dgmXiTwoGain_add_tail [Fintype A]
    (K : AddSubgroup A) (B C : Finset A)
    (P : List (Finset A)) (k : ℕ) :
    dgmXiTwoGain K B C P k + dgmCappedMultiplicitySum K P k =
      dgmCappedMultiplicitySum K (dgmInterUnionLayers B C P) (k + 2) := by
  unfold dgmXiTwoGain
  exact Nat.sub_add_cancel
    (dgmCappedMultiplicitySum_tail_le_inter_union K B C P k)

/-- The contribution of one quotient coset to the two-layer `Ξ` gain.  It is
recorded pointwise because the source proof compares these contributions
under a subgroup refinement before summing them. -/
noncomputable def dgmXiLocalTwoGain
    (K : AddSubgroup A) (B C : Finset A) (P : List (Finset A))
    (k : ℕ) (q : A ⧸ K) : ℕ :=
  min (k + 2)
      (quotientLayerMultiplicity K (dgmInterUnionLayers B C P) q) -
    min k (quotientLayerMultiplicity K P q)

/-- Two additional layers raise a quotient-layer multiplicity by at most two.
This deliberately passes through the original two leading layers: the
intersection--union operation can only decrease their incidence count. -/
theorem quotientLayerMultiplicity_inter_union_le_tail_add_two
    (K : AddSubgroup A) (B C : Finset A) (P : List (Finset A))
    (q : A ⧸ K) :
    quotientLayerMultiplicity K (dgmInterUnionLayers B C P) q ≤
      quotientLayerMultiplicity K P q + 2 := by
  have htransform := quotientLayerMultiplicity_inter_union_le K B C P q
  have hcons : quotientLayerMultiplicity K (B :: C :: P) q ≤
      quotientLayerMultiplicity K P q + 2 := by
    classical
    by_cases hB : q ∈ quotientLayer K B
    · rw [quotientLayerMultiplicity_cons_of_mem K B (C :: P) q hB]
      by_cases hC : q ∈ quotientLayer K C
      · rw [quotientLayerMultiplicity_cons_of_mem K C P q hC]
        omega
      · rw [quotientLayerMultiplicity_cons_of_not_mem K C P q hC]
        omega
    · rw [quotientLayerMultiplicity_cons_of_not_mem K B (C :: P) q hB]
      by_cases hC : q ∈ quotientLayer K C
      · rw [quotientLayerMultiplicity_cons_of_mem K C P q hC]
        omega
      · rw [quotientLayerMultiplicity_cons_of_not_mem K C P q hC]
        omega
  exact htransform.trans hcons

/-- Every quotient coset contributes between zero and two to the two-layer
gain.  This is the formal counterpart of the source observation that the
coarse contribution is one of `0`, `|H|`, `2|H|`. -/
theorem dgmXiLocalTwoGain_le_two
    (K : AddSubgroup A) (B C : Finset A) (P : List (Finset A))
    (k : ℕ) (q : A ⧸ K) :
    dgmXiLocalTwoGain K B C P k q ≤ 2 := by
  let t := quotientLayerMultiplicity K P q
  let a := quotientLayerMultiplicity K (dgmInterUnionLayers B C P) q
  have hat : a ≤ t + 2 := by
    simpa [a, t] using
      quotientLayerMultiplicity_inter_union_le_tail_add_two K B C P q
  have hmin : min (k + 2) a ≤ min k t + 2 := by
    rcases le_total t k with htk | hkt
    · rw [min_eq_right htk]
      exact (min_le_right (k + 2) a).trans hat
    · rw [min_eq_left hkt]
      exact min_le_left _ _
  unfold dgmXiLocalTwoGain
  change min (k + 2) a - min k t ≤ 2
  omega

/-- Expose the capped multiplicity sum using a caller-supplied quotient
`Fintype`.  The definition intentionally manufactures this instance from
finiteness, so this bridge removes an otherwise irrelevant instance mismatch
in subsequent quotient-fiber sums. -/
theorem dgmCappedMultiplicitySum_eq_fintype_sum
    (K : AddSubgroup A) [Fintype (A ⧸ K)]
    (P : List (Finset A)) (n : ℕ) :
    dgmCappedMultiplicitySum K P n =
      ∑ q : A ⧸ K, min n (quotientLayerMultiplicity K P q) := by
  classical
  rw [dgmCappedMultiplicitySum]
  congr 1
  ext q
  simp

/-- The aggregate two-layer gain is exactly the sum of its quotient-coset
contributions; in particular, the subtraction in its definition loses no
information. -/
theorem dgmXiTwoGain_eq_sum_localGain [Fintype A]
    (K : AddSubgroup A) [Fintype (A ⧸ K)] (B C : Finset A)
    (P : List (Finset A)) (k : ℕ) :
    dgmXiTwoGain K B C P k =
      ∑ q : A ⧸ K, dgmXiLocalTwoGain K B C P k q := by
  classical
  have hsum :
      (∑ q : A ⧸ K, dgmXiLocalTwoGain K B C P k q) +
          dgmCappedMultiplicitySum K P k =
        dgmCappedMultiplicitySum K (dgmInterUnionLayers B C P) (k + 2) := by
    rw [dgmCappedMultiplicitySum_eq_fintype_sum,
      dgmCappedMultiplicitySum_eq_fintype_sum]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro q _
    unfold dgmXiLocalTwoGain
    exact Nat.sub_add_cancel (min_le_min (by omega) (by
      simpa [dgmInterUnionLayers] using
        quotientLayerMultiplicity_le_cons_cons K (B ∩ C) (B ∪ C) P q))
  have haggregate := dgmXiTwoGain_add_tail K B C P k
  omega

/-! ### Quotient refinement for the strict weighted `Ξ` claim -/

/-- The canonical refinement map `A/L → A/H` for `L ≤ H`. -/
def dgmQuotientRefinementMap (L H : AddSubgroup A) (hLH : L ≤ H) :
    A ⧸ L →+ A ⧸ H :=
  QuotientAddGroup.map L H (AddMonoidHom.id A) (by simpa using hLH)

@[simp]
theorem dgmQuotientRefinementMap_mk
    (L H : AddSubgroup A) (hLH : L ≤ H) (x : A) :
    dgmQuotientRefinementMap L H hLH (x : A ⧸ L) = (x : A ⧸ H) := by
  rfl

/-- A layer incidence modulo the finer subgroup maps to a layer incidence
modulo the coarser subgroup. -/
theorem quotientLayer_mem_map_of_le
    (L H : AddSubgroup A) (hLH : L ≤ H) (D : Finset A)
    {q : A ⧸ L} (hq : q ∈ quotientLayer L D) :
    dgmQuotientRefinementMap L H hLH q ∈ quotientLayer H D := by
  obtain ⟨x, hx, rfl⟩ := (mem_quotientLayer_iff L D q).1 hq
  exact (mem_quotientLayer_iff H D _).2 ⟨x, hx, rfl⟩

/-- Pointwise layer multiplicity cannot decrease after quotienting by the
larger subgroup. -/
theorem quotientLayerMultiplicity_le_map_of_le
    (L H : AddSubgroup A) (hLH : L ≤ H) (P : List (Finset A))
    (q : A ⧸ L) :
    quotientLayerMultiplicity L P q ≤
      quotientLayerMultiplicity H P (dgmQuotientRefinementMap L H hLH q) := by
  classical
  induction P with
  | nil => simp [quotientLayerMultiplicity]
  | cons D P ih =>
      by_cases hqD : q ∈ quotientLayer L D
      · have hmapD := quotientLayer_mem_map_of_le L H hLH D hqD
        rw [quotientLayerMultiplicity_cons_of_mem L D P q hqD,
          quotientLayerMultiplicity_cons_of_mem H D P _ hmapD]
        omega
      · rw [quotientLayerMultiplicity_cons_of_not_mem L D P q hqD]
        by_cases hmapD : dgmQuotientRefinementMap L H hLH q ∈
            quotientLayer H D
        · rw [quotientLayerMultiplicity_cons_of_mem H D P _ hmapD]
          omega
        · rw [quotientLayerMultiplicity_cons_of_not_mem H D P _ hmapD]
          exact ih

/-- Elementary monotonicity of a capped two-step gain.  The extra incidence
parameter is at most two because it comes from the intersection and union
layers. -/
theorem dgmNatTwoGain_mono
    (k t₁ t₂ s₁ s₂ : ℕ) (ht : t₁ ≤ t₂) (hs : s₁ ≤ s₂)
    (hs₂ : s₂ ≤ 2) :
    min (k + 2) (s₁ + t₁) - min k t₁ ≤
      min (k + 2) (s₂ + t₂) - min k t₂ := by
  omega

/-- Every fine quotient-coset contribution is bounded by the contribution
of the coarse quotient coset containing it. -/
theorem dgmXiLocalTwoGain_le_map_of_le
    (L H : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (q : A ⧸ L) :
    dgmXiLocalTwoGain L B C P k q ≤
      dgmXiLocalTwoGain H B C P k
        (dgmQuotientRefinementMap L H hLH q) := by
  classical
  let r := dgmQuotientRefinementMap L H hLH q
  have htail := quotientLayerMultiplicity_le_map_of_le L H hLH P q
  change quotientLayerMultiplicity L P q ≤
      quotientLayerMultiplicity H P r at htail
  have hinterImp : q ∈ quotientLayer L (B ∩ C) →
      r ∈ quotientLayer H (B ∩ C) := by
    exact quotientLayer_mem_map_of_le L H hLH (B ∩ C)
  have hunionImp : q ∈ quotientLayer L (B ∪ C) →
      r ∈ quotientLayer H (B ∪ C) := by
    exact quotientLayer_mem_map_of_le L H hLH (B ∪ C)
  have hinterUnionL : q ∈ quotientLayer L (B ∩ C) →
      q ∈ quotientLayer L (B ∪ C) := by
    intro hq
    obtain ⟨x, hx, rfl⟩ := (mem_quotientLayer_iff L (B ∩ C) q).1 hq
    exact (mem_quotientLayer_iff L (B ∪ C) _).2
      ⟨x, Finset.mem_union_left C (Finset.mem_inter.mp hx).1, rfl⟩
  have hinterUnionH : r ∈ quotientLayer H (B ∩ C) →
      r ∈ quotientLayer H (B ∪ C) := by
    intro hr
    obtain ⟨x, hx, hxr⟩ := (mem_quotientLayer_iff H (B ∩ C) r).1 hr
    exact (mem_quotientLayer_iff H (B ∪ C) _).2
      ⟨x, Finset.mem_union_left C (Finset.mem_inter.mp hx).1, hxr⟩
  by_cases hiL : q ∈ quotientLayer L (B ∩ C)
  · have hiH := hinterImp hiL
    have huL := hinterUnionL hiL
    have huH := hinterUnionH hiH
    unfold dgmXiLocalTwoGain dgmInterUnionLayers
    rw [quotientLayerMultiplicity_cons_of_mem L (B ∩ C) ((B ∪ C) :: P) q hiL,
      quotientLayerMultiplicity_cons_of_mem L (B ∪ C) P q huL,
      quotientLayerMultiplicity_cons_of_mem H (B ∩ C) ((B ∪ C) :: P) r hiH,
      quotientLayerMultiplicity_cons_of_mem H (B ∪ C) P r huH]
    rw [show 1 + (1 + quotientLayerMultiplicity L P q) =
          2 + quotientLayerMultiplicity L P q by omega,
      show 1 + (1 + quotientLayerMultiplicity H P r) =
          2 + quotientLayerMultiplicity H P r by omega]
    simpa [r] using
      dgmNatTwoGain_mono k _ _ 2 2 htail (by omega) (by omega)
  · have hiH_or := Classical.em (r ∈ quotientLayer H (B ∩ C))
    rcases hiH_or with hiH | hiH
    · have huH := hinterUnionH hiH
      unfold dgmXiLocalTwoGain dgmInterUnionLayers
      rw [quotientLayerMultiplicity_cons_of_not_mem L (B ∩ C) ((B ∪ C) :: P) q hiL,
        quotientLayerMultiplicity_cons_of_mem H (B ∩ C) ((B ∪ C) :: P) r hiH,
        quotientLayerMultiplicity_cons_of_mem H (B ∪ C) P r huH]
      by_cases huL : q ∈ quotientLayer L (B ∪ C)
      · rw [quotientLayerMultiplicity_cons_of_mem L (B ∪ C) P q huL]
        rw [show 1 + (1 + quotientLayerMultiplicity H P r) =
            2 + quotientLayerMultiplicity H P r by omega]
        simpa [r] using
          dgmNatTwoGain_mono k _ _ 1 2 htail (by omega) (by omega)
      · rw [quotientLayerMultiplicity_cons_of_not_mem L (B ∪ C) P q huL]
        rw [show 1 + (1 + quotientLayerMultiplicity H P r) =
            2 + quotientLayerMultiplicity H P r by omega]
        simpa [r] using
          dgmNatTwoGain_mono k _ _ 0 2 htail (by omega) (by omega)
    · by_cases huL : q ∈ quotientLayer L (B ∪ C)
      · have huH := hunionImp huL
        unfold dgmXiLocalTwoGain dgmInterUnionLayers
        rw [quotientLayerMultiplicity_cons_of_not_mem L (B ∩ C) ((B ∪ C) :: P) q hiL,
          quotientLayerMultiplicity_cons_of_mem L (B ∪ C) P q huL,
          quotientLayerMultiplicity_cons_of_not_mem H (B ∩ C) ((B ∪ C) :: P) r hiH,
          quotientLayerMultiplicity_cons_of_mem H (B ∪ C) P r huH]
        simpa [r] using
          dgmNatTwoGain_mono k _ _ 1 1 htail (by omega) (by omega)
      · by_cases huH : r ∈ quotientLayer H (B ∪ C)
        · unfold dgmXiLocalTwoGain dgmInterUnionLayers
          rw [quotientLayerMultiplicity_cons_of_not_mem L (B ∩ C) ((B ∪ C) :: P) q hiL,
            quotientLayerMultiplicity_cons_of_not_mem L (B ∪ C) P q huL,
            quotientLayerMultiplicity_cons_of_not_mem H (B ∩ C) ((B ∪ C) :: P) r hiH,
            quotientLayerMultiplicity_cons_of_mem H (B ∪ C) P r huH]
          simpa [r] using
            dgmNatTwoGain_mono k _ _ 0 1 htail (by omega) (by omega)
        · unfold dgmXiLocalTwoGain dgmInterUnionLayers
          rw [quotientLayerMultiplicity_cons_of_not_mem L (B ∩ C) ((B ∪ C) :: P) q hiL,
            quotientLayerMultiplicity_cons_of_not_mem L (B ∪ C) P q huL,
            quotientLayerMultiplicity_cons_of_not_mem H (B ∩ C) ((B ∪ C) :: P) r hiH,
            quotientLayerMultiplicity_cons_of_not_mem H (B ∪ C) P r huH]
          simpa [r] using
            dgmNatTwoGain_mono k _ _ 0 0 htail (by omega) (by omega)

/-- The exact local hypotheses isolated in the source proof for either
exceptional `H`-coset: the intersection layer misses it, the tail contributes
at most `k` incidences, and the union layer hits it.  These are later derived
from infeasibility of the transformed pattern. -/
def DGMXiExceptionalCoset
    (H : AddSubgroup A) (B C : Finset A) (P : List (Finset A))
    (k : ℕ) (b : A) : Prop :=
  (b : A ⧸ H) ∉ quotientLayer H (B ∩ C) ∧
    quotientLayerMultiplicity H P (b : A ⧸ H) ≤ k ∧
      (b : A ⧸ H) ∈ quotientLayer H (B ∪ C)

/-- Under the source's exceptional-coset hypotheses, the coarse local
two-layer gain is exactly one. -/
theorem dgmXiLocalTwoGain_eq_one_of_exceptional
    (H : AddSubgroup A) (B C : Finset A) (P : List (Finset A))
    (k : ℕ) (b : A)
    (hex : DGMXiExceptionalCoset H B C P k b) :
    dgmXiLocalTwoGain H B C P k (b : A ⧸ H) = 1 := by
  rcases hex with ⟨hinter, htail, hunion⟩
  unfold dgmXiLocalTwoGain dgmInterUnionLayers
  rw [quotientLayerMultiplicity_cons_of_not_mem H (B ∩ C)
      ((B ∪ C) :: P) _ hinter,
    quotientLayerMultiplicity_cons_of_mem H (B ∪ C) P _ hunion]
  omega

/-- In a fine `L`-coset lying over an exceptional `H`-coset, the local gain
is the indicator of whether that fine coset meets the union of the two
leading layers.  This is the pointwise heart of the weighted `Ξ` claim. -/
theorem dgmXiLocalTwoGain_eq_indicator_of_refines_exceptional
    (L H : AddSubgroup A) [DecidableEq (A ⧸ L)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (b : A)
    (hex : DGMXiExceptionalCoset H B C P k b)
    (q : A ⧸ L)
    (hq : dgmQuotientRefinementMap L H hLH q = (b : A ⧸ H)) :
    dgmXiLocalTwoGain L B C P k q =
      if q ∈ quotientLayer L (B ∪ C) then 1 else 0 := by
  rcases hex with ⟨hinterH, htailH, hunionH⟩
  have hinterL : q ∉ quotientLayer L (B ∩ C) := by
    intro hinterL
    apply hinterH
    have hmap := quotientLayer_mem_map_of_le L H hLH (B ∩ C) hinterL
    rwa [hq] at hmap
  have htailL : quotientLayerMultiplicity L P q ≤ k := by
    have hrefine := quotientLayerMultiplicity_le_map_of_le L H hLH P q
    rw [hq] at hrefine
    exact hrefine.trans htailH
  unfold dgmXiLocalTwoGain dgmInterUnionLayers
  rw [quotientLayerMultiplicity_cons_of_not_mem L (B ∩ C)
      ((B ∪ C) :: P) q hinterL]
  by_cases hunionL : q ∈ quotientLayer L (B ∪ C)
  · rw [quotientLayerMultiplicity_cons_of_mem L (B ∪ C) P q hunionL,
      if_pos hunionL]
    omega
  · rw [quotientLayerMultiplicity_cons_of_not_mem L (B ∪ C) P q hunionL,
      if_neg hunionL]
    omega

/-- The fine quotient cosets lying over one coarse quotient coset. -/
noncomputable def dgmQuotientRefinementFiber
    (L H : AddSubgroup A) [Fintype (A ⧸ L)] (hLH : L ≤ H)
    (r : A ⧸ H) : Finset (A ⧸ L) := by
  classical
  exact Finset.univ.filter fun q ↦ dgmQuotientRefinementMap L H hLH q = r

@[simp]
theorem mem_dgmQuotientRefinementFiber_iff
    (L H : AddSubgroup A) [Fintype (A ⧸ L)] (hLH : L ≤ H)
    (r : A ⧸ H) (q : A ⧸ L) :
    q ∈ dgmQuotientRefinementFiber L H hLH r ↔
      dgmQuotientRefinementMap L H hLH q = r := by
  classical
  simp [dgmQuotientRefinementFiber]

/-- One `L`-fiber in an `L`-saturated finite set has exactly `|L|` points. -/
theorem card_filter_add_dgmSubgroupFinset_eq
    [Fintype A] (L : AddSubgroup A) [DecidableEq (A ⧸ L)]
    (S : Finset A) (q : A ⧸ L) (hq : q ∈ quotientLayer L S) :
    ((S + dgmSubgroupFinset L).filter fun (y : A) ↦ (y : A ⧸ L) = q).card =
      Nat.card L := by
  classical
  obtain ⟨x, hxS, hxq⟩ := (mem_quotientLayer_iff L S q).1 hq
  have heq :
      (S + dgmSubgroupFinset L).filter (fun (y : A) ↦ (y : A ⧸ L) = q) =
        dgmCosetFiber L x := by
    ext y
    constructor
    · intro hy
      have hyq : (y : A ⧸ L) = q := (Finset.mem_filter.mp hy).2
      exact (mem_dgmCosetFiber_iff L x y).2 (hyq.trans hxq.symm)
    · intro hy
      have hyx := (mem_dgmCosetFiber_iff L x y).1 hy
      have hsub : y - x ∈ L := QuotientAddGroup.eq_iff_sub_mem.mp hyx
      have hadd : y ∈ S + dgmSubgroupFinset L := by
        exact Finset.mem_add.mpr
          ⟨x, hxS, y - x, (mem_dgmSubgroupFinset_iff L _).2 hsub, by abel⟩
      exact Finset.mem_filter.mpr ⟨hadd, hyx.trans hxq⟩
  rw [heq, card_dgmCosetFiber]

/-- Saturating a finite set by `L` has one full `L`-coset for every quotient
value met by the set. -/
theorem card_add_dgmSubgroupFinset_eq
    [Fintype A] (L : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (S : Finset A) :
    (S + dgmSubgroupFinset L).card =
      Nat.card L * (quotientLayer L S).card := by
  classical
  have himage : ∀ y ∈ S + dgmSubgroupFinset L,
      (y : A ⧸ L) ∈ quotientLayer L S := by
    intro y hy
    obtain ⟨x, hxS, l, hl, rfl⟩ := Finset.mem_add.mp hy
    apply (mem_quotientLayer_iff L S _).2
    refine ⟨x, hxS, ?_⟩
    rw [show ((x + l : A) : A ⧸ L) = (x : A ⧸ L) + (l : A ⧸ L) by rfl,
      (QuotientAddGroup.eq_zero_iff l).2
        ((mem_dgmSubgroupFinset_iff L l).1 hl), add_zero]
  have hmaps : Set.MapsTo (fun (y : A) ↦ (y : A ⧸ L))
      (↑(S + dgmSubgroupFinset L) : Set A)
      (↑(quotientLayer L S) : Set (A ⧸ L)) := by
    intro y hy
    exact himage y hy
  have hfiber := Finset.card_eq_sum_card_fiberwise
    (s := S + dgmSubgroupFinset L) (t := quotientLayer L S)
    (f := fun (y : A) ↦ (y : A ⧸ L)) hmaps
  calc
    (S + dgmSubgroupFinset L).card =
        ∑ q ∈ quotientLayer L S,
          ((S + dgmSubgroupFinset L).filter
            fun (y : A) ↦ (y : A ⧸ L) = q).card := hfiber
    _ = ∑ _q ∈ quotientLayer L S, Nat.card L := by
      apply Finset.sum_congr rfl
      intro q hq
      exact card_filter_add_dgmSubgroupFinset_eq L S q hq
    _ = Nat.card L * (quotientLayer L S).card := by
      simp [Nat.mul_comm]

/-- Within a fixed coarse `H`-coset, the fine quotient values met by `B∪C`
are exactly those met by the union of the two literal `H`-slices. -/
theorem refinementFiber_inter_quotientLayer_union_eq
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (hLH : L ≤ H)
    (B C : Finset A) (b : A) :
    dgmQuotientRefinementFiber L H hLH (b : A ⧸ H) ∩
        quotientLayer L (B ∪ C) =
      quotientLayer L (dgmCosetSlice H B b ∪ dgmCosetSlice H C b) := by
  classical
  ext q
  constructor
  · intro hq
    have hfiber := (mem_dgmQuotientRefinementFiber_iff
      L H hLH (b : A ⧸ H) q).1 (Finset.mem_inter.mp hq).1
    obtain ⟨x, hx, hxq⟩ := (mem_quotientLayer_iff L (B ∪ C) q).1
      (Finset.mem_inter.mp hq).2
    have hxH : (x : A ⧸ H) = (b : A ⧸ H) := by
      rw [← hfiber, ← hxq]
      rfl
    apply (mem_quotientLayer_iff L _ q).2
    refine ⟨x, ?_, hxq⟩
    rcases Finset.mem_union.mp hx with hxB | hxC
    · exact Finset.mem_union_left _
        ((mem_dgmCosetSlice_iff H B b x).2 ⟨hxB, hxH⟩)
    · exact Finset.mem_union_right _
        ((mem_dgmCosetSlice_iff H C b x).2 ⟨hxC, hxH⟩)
  · intro hq
    obtain ⟨x, hx, hxq⟩ := (mem_quotientLayer_iff L _ q).1 hq
    have hxUnion : x ∈ B ∪ C := by
      rcases Finset.mem_union.mp hx with hxB | hxC
      · exact Finset.mem_union_left _
          ((mem_dgmCosetSlice_iff H B b x).1 hxB).1
      · exact Finset.mem_union_right _
          ((mem_dgmCosetSlice_iff H C b x).1 hxC).1
    have hxH : (x : A ⧸ H) = (b : A ⧸ H) := by
      rcases Finset.mem_union.mp hx with hxB | hxC
      · exact ((mem_dgmCosetSlice_iff H B b x).1 hxB).2
      · exact ((mem_dgmCosetSlice_iff H C b x).1 hxC).2
    apply Finset.mem_inter.mpr
    constructor
    · apply (mem_dgmQuotientRefinementFiber_iff
        L H hLH (b : A ⧸ H) q).2
      rw [← hxq]
      exact hxH
    · exact (mem_quotientLayer_iff L (B ∪ C) q).2 ⟨x, hxUnion, hxq⟩

/-- The weighted sum of fine local gains over an exceptional coarse coset is
exactly the cardinality of the source proof's saturated pair of slices. -/
theorem weighted_sum_localGain_refinementFiber_eq_pairSaturation
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (b : A)
    (hex : DGMXiExceptionalCoset H B C P k b) :
    Nat.card L *
        (∑ q ∈ dgmQuotientRefinementFiber L H hLH (b : A ⧸ H),
          dgmXiLocalTwoGain L B C P k q) =
      (dgmPairSliceSaturation H L B C b).card := by
  classical
  have hsum :
      (∑ q ∈ dgmQuotientRefinementFiber L H hLH (b : A ⧸ H),
          dgmXiLocalTwoGain L B C P k q) =
        (dgmQuotientRefinementFiber L H hLH (b : A ⧸ H) ∩
          quotientLayer L (B ∪ C)).card := by
    calc
      (∑ q ∈ dgmQuotientRefinementFiber L H hLH (b : A ⧸ H),
          dgmXiLocalTwoGain L B C P k q) =
          ∑ q ∈ dgmQuotientRefinementFiber L H hLH (b : A ⧸ H),
            if q ∈ quotientLayer L (B ∪ C) then 1 else 0 := by
              apply Finset.sum_congr rfl
              intro q hq
              exact dgmXiLocalTwoGain_eq_indicator_of_refines_exceptional
                L H hLH B C P k b hex q
                ((mem_dgmQuotientRefinementFiber_iff
                  L H hLH (b : A ⧸ H) q).1 hq)
      _ = _ := by
        let F := dgmQuotientRefinementFiber L H hLH (b : A ⧸ H)
        let U := quotientLayer L (B ∪ C)
        have hbool : ∀ S : Finset (A ⧸ L),
            (∑ q ∈ S, if q ∈ U then 1 else 0) = (S ∩ U).card := by
          intro S
          induction S using Finset.induction_on with
          | empty => simp
          | @insert a S ha ih =>
              by_cases haU : a ∈ U
              · simp [ha, haU, ih]
              · simp [ha, haU, ih]
        simpa [F, U] using hbool F
  rw [hsum, refinementFiber_inter_quotientLayer_union_eq
    L H hLH B C b]
  rw [dgmPairSliceSaturation,
    card_add_dgmSubgroupFinset_eq L
      (dgmCosetSlice H B b ∪ dgmCosetSlice H C b)]

/-- The refinement fiber over `b+H` is precisely the set of `L`-quotient
values met by that literal `H`-coset. -/
theorem dgmQuotientRefinementFiber_eq_quotientLayer_cosetFiber
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (hLH : L ≤ H) (b : A) :
    dgmQuotientRefinementFiber L H hLH (b : A ⧸ H) =
      quotientLayer L (dgmCosetFiber H b) := by
  classical
  ext q
  constructor
  · intro hq
    induction q using QuotientAddGroup.induction_on with
    | _ x =>
      have hxH := (mem_dgmQuotientRefinementFiber_iff
        L H hLH (b : A ⧸ H) (x : A ⧸ L)).1 hq
      apply (mem_quotientLayer_iff L (dgmCosetFiber H b) _).2
      exact ⟨x, (mem_dgmCosetFiber_iff H b x).2 hxH, rfl⟩
  · intro hq
    obtain ⟨x, hx, hxq⟩ :=
      (mem_quotientLayer_iff L (dgmCosetFiber H b) q).1 hq
    apply (mem_dgmQuotientRefinementFiber_iff
      L H hLH (b : A ⧸ H) q).2
    rw [← hxq]
    exact (mem_dgmCosetFiber_iff H b x).1 hx

/-- An `H`-coset is already saturated by every subgroup `L ≤ H`. -/
theorem dgmCosetFiber_add_dgmSubgroupFinset_eq
    [Fintype A] (L H : AddSubgroup A) (hLH : L ≤ H) (b : A) :
    dgmCosetFiber H b + dgmSubgroupFinset L = dgmCosetFiber H b := by
  classical
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨x, hx, l, hl, rfl⟩ := Finset.mem_add.mp hy
    have hxH := (mem_dgmCosetFiber_iff H b x).1 hx
    have hlH : l ∈ H := hLH ((mem_dgmSubgroupFinset_iff L l).1 hl)
    apply (mem_dgmCosetFiber_iff H b (x + l)).2
    rw [show ((x + l : A) : A ⧸ H) = (x : A ⧸ H) + (l : A ⧸ H) by rfl,
      (QuotientAddGroup.eq_zero_iff l).2 hlH, add_zero, hxH]
  · intro y hy
    exact Finset.mem_add.mpr
      ⟨y, hy, 0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem, by simp⟩

/-- Cardinality of one refinement fiber, in the weighted form used by the
`Ξ` comparison. -/
theorem natCard_mul_card_dgmQuotientRefinementFiber
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (hLH : L ≤ H) (b : A) :
    Nat.card L *
        (dgmQuotientRefinementFiber L H hLH (b : A ⧸ H)).card =
      Nat.card H := by
  have hcard := card_add_dgmSubgroupFinset_eq L (dgmCosetFiber H b)
  rw [dgmCosetFiber_add_dgmSubgroupFinset_eq L H hLH b,
    card_dgmCosetFiber,
    ← dgmQuotientRefinementFiber_eq_quotientLayer_cosetFiber
      L H hLH b] at hcard
  exact hcard.symm

/-- The ordinary (nonexceptional) refinement-fiber inequality: after
weighting by subgroup cardinality, all fine local contributions fit under
the single coarse contribution. -/
theorem weighted_sum_localGain_refinementFiber_le
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (b : A) :
    Nat.card L *
        (∑ q ∈ dgmQuotientRefinementFiber L H hLH (b : A ⧸ H),
          dgmXiLocalTwoGain L B C P k q) ≤
      Nat.card H * dgmXiLocalTwoGain H B C P k (b : A ⧸ H) := by
  classical
  let F := dgmQuotientRefinementFiber L H hLH (b : A ⧸ H)
  let g := dgmXiLocalTwoGain H B C P k (b : A ⧸ H)
  have hsum :
      (∑ q ∈ F, dgmXiLocalTwoGain L B C P k q) ≤ F.card * g := by
    calc
      (∑ q ∈ F, dgmXiLocalTwoGain L B C P k q) ≤
          ∑ _q ∈ F, g := by
            apply Finset.sum_le_sum
            intro q hq
            have hle := dgmXiLocalTwoGain_le_map_of_le L H hLH B C P k q
            have hmap := (mem_dgmQuotientRefinementFiber_iff
              L H hLH (b : A ⧸ H) q).1 hq
            rwa [hmap] at hle
      _ = F.card * g := by simp
  have hweighted := Nat.mul_le_mul_left (Nat.card L) hsum
  have hfiber := natCard_mul_card_dgmQuotientRefinementFiber L H hLH b
  dsimp only [F, g] at hweighted ⊢
  rw [← Nat.mul_assoc, hfiber] at hweighted
  exact hweighted

/-- On an exceptional fiber the ordinary inequality has an exact deficit:
the missing part of the coarse `H`-coset. -/
theorem weighted_sum_localGain_add_missing_eq_of_exceptional
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (b : A)
    (hex : DGMXiExceptionalCoset H B C P k b) :
    Nat.card L *
        (∑ q ∈ dgmQuotientRefinementFiber L H hLH (b : A ⧸ H),
          dgmXiLocalTwoGain L B C P k q) +
        (dgmMissingPairCoset H L B C b).card =
      Nat.card H * dgmXiLocalTwoGain H B C P k (b : A ⧸ H) := by
  have hweighted := weighted_sum_localGain_refinementFiber_eq_pairSaturation
    L H hLH B C P k b hex
  have hpartition := card_missing_add_pairSaturation H L hLH B C b
  have hcoarse := dgmXiLocalTwoGain_eq_one_of_exceptional H B C P k b hex
  rw [hweighted, hcoarse, Nat.mul_one]
  omega

/-- The fine local-gain sum decomposes as the sum over refinement fibers. -/
theorem sum_localGain_eq_sum_refinementFibers
    (L H : AddSubgroup A) [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) :
    (∑ q : A ⧸ L, dgmXiLocalTwoGain L B C P k q) =
      ∑ r : A ⧸ H,
        ∑ q ∈ dgmQuotientRefinementFiber L H hLH r,
          dgmXiLocalTwoGain L B C P k q := by
  classical
  have h := Finset.sum_fiberwise
    (Finset.univ : Finset (A ⧸ L))
    (dgmQuotientRefinementMap L H hLH)
    (fun q ↦ dgmXiLocalTwoGain L B C P k q)
  convert h.symm using 1 <;>
    simp [dgmQuotientRefinementFiber]
  congr 1
  ext r
  congr 1
  ext q
  simp

/-- The weighted two-layer `Ξ` gain is monotone under subgroup refinement. -/
theorem weighted_dgmXiTwoGain_le_of_le
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) :
    Nat.card L * dgmXiTwoGain L B C P k ≤
      Nat.card H * dgmXiTwoGain H B C P k := by
  rw [dgmXiTwoGain_eq_sum_localGain,
    dgmXiTwoGain_eq_sum_localGain,
    sum_localGain_eq_sum_refinementFibers L H hLH B C P k]
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro r _
  induction r using QuotientAddGroup.induction_on with
  | _ b =>
    exact weighted_sum_localGain_refinementFiber_le
      L H hLH B C P k b

/-- The strict weighted `Ξ` claim on page 11 of the source proof.  The two
exceptional coarse cosets contribute their literal missing sets, while every
other refinement fiber uses ordinary weighted monotonicity. -/
theorem weighted_dgmXiTwoGain_add_missingUnion_le
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H))
    (hex₁ : DGMXiExceptionalCoset H B C P k b₁)
    (hex₂ : DGMXiExceptionalCoset H B C P k b₂) :
    Nat.card L * dgmXiTwoGain L B C P k +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card ≤
      Nat.card H * dgmXiTwoGain H B C P k := by
  classical
  let d₁ := (dgmMissingPairCoset H L B C b₁).card
  let d₂ := (dgmMissingPairCoset H L B C b₂).card
  let fine : A ⧸ H → ℕ := fun r ↦
    Nat.card L *
      (∑ q ∈ dgmQuotientRefinementFiber L H hLH r,
        dgmXiLocalTwoGain L B C P k q)
  let coarse : A ⧸ H → ℕ := fun r ↦
    Nat.card H * dgmXiLocalTwoGain H B C P k r
  let bonus : A ⧸ H → ℕ := fun r ↦
    if r = (b₁ : A ⧸ H) then d₁
    else if r = (b₂ : A ⧸ H) then d₂ else 0
  have hpoint : ∀ r : A ⧸ H, fine r + bonus r ≤ coarse r := by
    intro r
    by_cases hr₁ : r = (b₁ : A ⧸ H)
    · subst r
      have hexact := weighted_sum_localGain_add_missing_eq_of_exceptional
        L H hLH B C P k b₁ hex₁
      simpa [fine, coarse, bonus, d₁] using hexact.le
    · by_cases hr₂ : r = (b₂ : A ⧸ H)
      · subst r
        have hexact := weighted_sum_localGain_add_missing_eq_of_exceptional
          L H hLH B C P k b₂ hex₂
        simpa [fine, coarse, bonus, d₂, hne, hr₁] using hexact.le
      · have hordinary : fine r ≤ coarse r := by
          induction r using QuotientAddGroup.induction_on with
          | _ b =>
            exact weighted_sum_localGain_refinementFiber_le
              L H hLH B C P k b
        simpa [bonus, hr₁, hr₂] using hordinary
  have hsum : (∑ r : A ⧸ H, (fine r + bonus r)) ≤
      ∑ r : A ⧸ H, coarse r := by
    exact Finset.sum_le_sum fun r _ ↦ hpoint r
  have hbonus : (∑ r : A ⧸ H, bonus r) = d₁ + d₂ := by
    have hpointBonus : ∀ r : A ⧸ H,
        bonus r =
          (if (b₁ : A ⧸ H) = r then d₁ else 0) +
            (if (b₂ : A ⧸ H) = r then d₂ else 0) := by
      intro r
      by_cases hr₁ : r = (b₁ : A ⧸ H)
      · subst r
        simp [bonus, hne, Ne.symm hne]
      · by_cases hr₂ : r = (b₂ : A ⧸ H)
        · subst r
          simp [bonus, hr₁, hne]
        · simp [bonus, hr₁, hr₂, Ne.symm hr₁, Ne.symm hr₂]
    calc
      (∑ r : A ⧸ H, bonus r) =
          ∑ r : A ⧸ H,
            ((if (b₁ : A ⧸ H) = r then d₁ else 0) +
              (if (b₂ : A ⧸ H) = r then d₂ else 0)) := by
                apply Fintype.sum_congr
                exact hpointBonus
      _ = d₁ + d₂ := by
        rw [Finset.sum_add_distrib, Fintype.sum_ite_eq,
          Fintype.sum_ite_eq]
  have hmissing :
      (dgmMissingPairCoset H L B C b₁ ∪
        dgmMissingPairCoset H L B C b₂).card = d₁ + d₂ := by
    rw [Finset.card_union_of_disjoint
      (disjoint_dgmMissingPairCoset_of_ne H L B C b₁ b₂ hne)]
  rw [Finset.sum_add_distrib, hbonus] at hsum
  rw [dgmXiTwoGain_eq_sum_localGain,
    dgmXiTwoGain_eq_sum_localGain,
    sum_localGain_eq_sum_refinementFibers L H hLH B C P k,
    Finset.mul_sum, Finset.mul_sum, hmissing]
  simpa [fine, coarse] using hsum

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

theorem quotientLayer_eq_stabilizerQuotientLayer
    (T B : Finset A) :
    quotientLayer (AddAction.stabilizer A (T : Set A)) B =
      stabilizerQuotientLayer T B := by
  classical
  ext q
  simp [quotientLayer, stabilizerQuotientLayer]

theorem quotientLayerMultiplicity_stabilizer_eq
    (T : Finset A) (P : List (Finset A))
    (q : A ⧸ AddAction.stabilizer A (T : Set A)) :
    quotientLayerMultiplicity (AddAction.stabilizer A (T : Set A)) P q =
      stabilizerLayerMultiplicity T P q := by
  classical
  induction P with
  | nil => simp [quotientLayerMultiplicity, stabilizerLayerMultiplicity]
  | cons B P ih =>
      by_cases hq : q ∈ quotientLayer
          (AddAction.stabilizer A (T : Set A)) B
      · have hq' : q ∈ stabilizerQuotientLayer T B := by
          rwa [quotientLayer_eq_stabilizerQuotientLayer T B] at hq
        rw [quotientLayerMultiplicity_cons_of_mem _ B P q hq,
          stabilizerLayerMultiplicity_cons_of_mem T B P q hq', ih]
      · have hq' : q ∉ stabilizerQuotientLayer T B := by
          rwa [← quotientLayer_eq_stabilizerQuotientLayer T B]
        rw [quotientLayerMultiplicity_cons_of_not_mem _ B P q hq,
          stabilizerLayerMultiplicity_cons_of_not_mem T B P q hq', ih]

theorem dgmCappedMultiplicitySum_stabilizer_eq
    [Fintype A] (T : Finset A) (P : List (Finset A)) (n : ℕ) :
    dgmCappedMultiplicitySum (AddAction.stabilizer A (T : Set A)) P n =
      stabilizerDgmCappedMultiplicitySum T P n := by
  classical
  letI : Fintype
      (A ⧸ AddAction.stabilizer A (T : Set A)) :=
    Fintype.ofFinite (A ⧸ AddAction.stabilizer A (T : Set A))
  rw [dgmCappedMultiplicitySum, stabilizerDgmCappedMultiplicitySum]
  simp only [quotientLayerMultiplicity_stabilizer_eq]
  congr 1
  ext q
  simp

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

/-- Faithful additive form of Theorem 3.1.  Moving the `K` correction term
to the right avoids integer-valued subtraction while preserving the exact
statement whenever the pattern spectrum is nonempty. -/
def DGMPatternBound [Fintype A]
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n) : Prop :=
  let T := patternSubsumSpectrum P μ
  let J := AddAction.stabilizer A (T : Set A)
  Nat.card J * (stabilizerDgmCappedMultiplicitySum T P n - n + 1) ≤
    T.card + Nat.card K * (dgmCappedMultiplicitySum K P n - n)

/-- Fully quantified generalized pattern theorem used by the faithful
minimal-counterexample proof. -/
def GeneralDGMPatternTheorem
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] : Prop :=
  ∀ (K : AddSubgroup A) (n : ℕ)
    (_ : Fintype (A ⧸ K)) (_ : DecidableEq (A ⧸ K))
    (P : List (Finset A)) (μ : QuotientPattern K n),
    (patternSubsumSpectrum P μ).Nonempty → DGMPatternBound P μ

/-- The unique pattern modulo the top subgroup. -/
theorem quotientTop_subsingleton :
    Subsingleton (A ⧸ (⊤ : AddSubgroup A)) := by
  constructor
  intro x y
  induction x using QuotientAddGroup.induction_on with
  | _ x =>
    induction y using QuotientAddGroup.induction_on with
    | _ y =>
      exact QuotientAddGroup.eq_iff_sub_mem.mpr (by simp)

noncomputable def topQuotientPattern
    [Fintype (A ⧸ (⊤ : AddSubgroup A))]
    (n : ℕ) : QuotientPattern (⊤ : AddSubgroup A) n where
  multiplicity := fun _ ↦ n
  weight_eq := by
    classical
    letI : Subsingleton (A ⧸ (⊤ : AddSubgroup A)) :=
      quotientTop_subsingleton (A := A)
    letI : Unique (A ⧸ (⊤ : AddSubgroup A)) := uniqueOfSubsingleton 0
    simp

@[simp]
theorem topQuotientPattern_apply
    [Fintype (A ⧸ (⊤ : AddSubgroup A))]
    (n : ℕ) (q : A ⧸ (⊤ : AddSubgroup A)) :
    topQuotientPattern (A := A) n q = n := rfl

theorem LayerSubsumChoice.realizes_topQuotientPattern
    [Fintype (A ⧸ (⊤ : AddSubgroup A))]
    [DecidableEq (A ⧸ (⊤ : AddSubgroup A))]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) :
    h.RealizesPattern (topQuotientPattern (A := A) n) := by
  letI : Subsingleton (A ⧸ (⊤ : AddSubgroup A)) :=
    quotientTop_subsingleton (A := A)
  letI : Unique (A ⧸ (⊤ : AddSubgroup A)) := uniqueOfSubsingleton 0
  intro q
  have hsum := h.sum_quotientMultiplicity (K := (⊤ : AddSubgroup A))
  have hq : h.quotientMultiplicity (⊤ : AddSubgroup A) q = n := by
    calc
      h.quotientMultiplicity (⊤ : AddSubgroup A) q =
          h.quotientMultiplicity (⊤ : AddSubgroup A) default := by
        congr 1
        exact Subsingleton.elim _ _
      _ =
          ∑ z, h.quotientMultiplicity (⊤ : AddSubgroup A) z :=
        (Fintype.sum_unique
          (fun z ↦ h.quotientMultiplicity (⊤ : AddSubgroup A) z)).symm
      _ = n := hsum
  simpa using hq

theorem patternSubsumSpectrum_top_eq_layerSubsumSpectrum
    [Fintype (A ⧸ (⊤ : AddSubgroup A))]
    [DecidableEq (A ⧸ (⊤ : AddSubgroup A))]
    (P : List (Finset A)) (n : ℕ) :
    patternSubsumSpectrum P (topQuotientPattern (A := A) n) =
      layerSubsumSpectrum P n := by
  apply Finset.Subset.antisymm
  · exact patternSubsumSpectrum_subset_layerSubsumSpectrum _ _
  · intro y hy
    obtain ⟨h⟩ := (nonempty_layerSubsumChoice_iff_mem P n y).2 hy
    exact (mem_patternSubsumSpectrum_iff _ _ y).2
      ⟨⟨h, h.realizes_topQuotientPattern⟩⟩

theorem dgmCappedMultiplicitySum_top_eq
    [Fintype A]
    [Fintype (A ⧸ (⊤ : AddSubgroup A))]
    [DecidableEq (A ⧸ (⊤ : AddSubgroup A))]
    (P : List (Finset A)) (hP : IsNonemptySetPartition P)
    (n : ℕ) (hn : n ≤ P.length) :
    dgmCappedMultiplicitySum (⊤ : AddSubgroup A) P n = n := by
  letI : Fintype (A ⧸ (⊤ : AddSubgroup A)) :=
    Fintype.ofFinite (A ⧸ (⊤ : AddSubgroup A))
  have hlower := le_dgmCappedMultiplicitySum
    (⊤ : AddSubgroup A) P hP n hn
  apply Nat.le_antisymm ?_ hlower
  classical
  letI : Subsingleton (A ⧸ (⊤ : AddSubgroup A)) :=
    quotientTop_subsingleton (A := A)
  letI : Unique (A ⧸ (⊤ : AddSubgroup A)) := uniqueOfSubsingleton 0
  rw [dgmCappedMultiplicitySum]
  let q : A ⧸ (⊤ : AddSubgroup A) := 0
  calc
    (∑ z, min n (quotientLayerMultiplicity (⊤ : AddSubgroup A) P z)) =
        min n (quotientLayerMultiplicity (⊤ : AddSubgroup A) P default) :=
      Fintype.sum_unique _
    _ = min n (quotientLayerMultiplicity (⊤ : AddSubgroup A) P q) := by
      congr 2
    _ ≤ n := min_le_left _ _

theorem card_addStab_eq_natCard_stabilizer [Fintype A]
    (T : Finset A) (hT : T.Nonempty) :
    T.addStab.card = Nat.card (AddAction.stabilizer A (T : Set A)) := by
  rw [← Set.ncard_coe_finset, Finset.coe_addStab hT,
    ← SetLike.coe_sort_coe, Nat.card_coe_set_eq]

/-- The top-pattern specialization of Theorem 3.1 is mechanically the
frozen general setpartition DGM theorem. -/
theorem generalDGMSetpartitionTheorem_of_generalPatternTheorem
    [Fintype A] (hpattern : GeneralDGMPatternTheorem A) :
    GeneralDGMSetpartitionTheorem A := by
  intro P n hP hnpos hn
  classical
  letI : Fintype (A ⧸ (⊤ : AddSubgroup A)) :=
    Fintype.ofFinite (A ⧸ (⊤ : AddSubgroup A))
  letI : DecidableEq (A ⧸ (⊤ : AddSubgroup A)) := Classical.decEq _
  let μ := topQuotientPattern (A := A) n
  have hμnonempty : (patternSubsumSpectrum P μ).Nonempty := by
    rw [show μ = topQuotientPattern (A := A) n by rfl,
      patternSubsumSpectrum_top_eq_layerSubsumSpectrum]
    exact layerSubsumSpectrum_nonempty P hP n hn
  have hb := hpattern (⊤ : AddSubgroup A) n inferInstance inferInstance
    P μ hμnonempty
  have htop := dgmCappedMultiplicitySum_top_eq P hP n hn
  have hspectrum : patternSubsumSpectrum P μ = layerSubsumSpectrum P n := by
    exact patternSubsumSpectrum_top_eq_layerSubsumSpectrum P n
  unfold DGMPatternBound at hb
  dsimp only at hb
  rw [hspectrum, htop] at hb
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero] at hb
  unfold DGMSetpartitionBound
  let T := layerSubsumSpectrum P n
  have hT : T.Nonempty := layerSubsumSpectrum_nonempty P hP n hn
  have hcard := card_addStab_eq_natCard_stabilizer T hT
  dsimp only [T]
  rw [Nat.mul_comm, hcard]
  exact hb

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
