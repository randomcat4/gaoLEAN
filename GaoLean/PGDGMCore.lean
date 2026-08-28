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

/-- A proof-relevant exact-layer choice can never select more layers than
the source list contains. -/
theorem weight_le_length {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) : n ≤ P.length := by
  induction h with
  | zero => simp
  | skip _ ih => simpa using ih.trans (Nat.le_succ _)
  | take _ _ ih => simpa using Nat.succ_le_succ ih

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

/-- A permutation of the labelled layer list transports every exact-layer
choice without changing either its sum or any quotient-coset multiplicity.
This is proof-relevant: the selected layers are permuted, never collapsed to
an unlabelled union. -/
theorem exists_of_perm
    {P Q : List (Finset A)} (hPQ : P.Perm Q)
    {n : ℕ} {y : A} (h : LayerSubsumChoice P n y)
    (K : AddSubgroup A) [DecidableEq (A ⧸ K)] :
    ∃ h' : LayerSubsumChoice Q n y,
      ∀ q : A ⧸ K,
        quotientMultiplicity K h' q = quotientMultiplicity K h q := by
  induction hPQ generalizing n y with
  | nil =>
      cases h
      exact ⟨LayerSubsumChoice.zero [], by simp [quotientMultiplicity]⟩
  | @cons B P Q hPQ ih =>
      cases h with
      | zero =>
          exact ⟨LayerSubsumChoice.zero (B :: Q), by
            simp [quotientMultiplicity]⟩
      | skip htail =>
          obtain ⟨h', h'mult⟩ := ih htail
          exact ⟨LayerSubsumChoice.skip h', by
            intro q
            simpa [quotientMultiplicity] using h'mult q⟩
      | @take _ _ n b z hb htail =>
          obtain ⟨h', h'mult⟩ := ih htail
          exact ⟨LayerSubsumChoice.take hb h', by
            intro q
            simp only [quotientMultiplicity]
            rw [h'mult q]⟩
  | @swap B C P =>
      cases h with
      | zero =>
          exact ⟨LayerSubsumChoice.zero (B :: C :: P), by
            simp [quotientMultiplicity]⟩
      | skip htail =>
          cases htail with
          | zero =>
              exact ⟨LayerSubsumChoice.zero (B :: C :: P), by
                simp [quotientMultiplicity]⟩
          | skip hrest =>
              exact ⟨LayerSubsumChoice.skip (LayerSubsumChoice.skip hrest), by
                simp [quotientMultiplicity]⟩
          | @take _ _ n c z hc hrest =>
              exact ⟨LayerSubsumChoice.take hc (LayerSubsumChoice.skip hrest), by
                simp [quotientMultiplicity]⟩
      | @take _ _ n b z hb htail =>
          cases htail with
          | zero =>
              exact ⟨LayerSubsumChoice.skip
                (LayerSubsumChoice.take hb (LayerSubsumChoice.zero P)), by
                simp [quotientMultiplicity]⟩
          | skip hrest =>
              exact ⟨LayerSubsumChoice.skip (LayerSubsumChoice.take hb hrest), by
                simp [quotientMultiplicity]⟩
          | @take _ _ m c z hc hrest =>
              have hsum : b + (c + z) = c + (b + z) := by ac_rfl
              let h' : LayerSubsumChoice (B :: C :: P) (m + 1 + 1)
                  (c + (b + z)) :=
                LayerSubsumChoice.take hc (LayerSubsumChoice.take hb hrest)
              refine ⟨hsum ▸ h', ?_⟩
              intro q
              rw [quotientMultiplicity_cast]
              simp only [h', quotientMultiplicity]
              omega
  | @trans P Q R hPQ hQR ihPQ ihQR =>
      obtain ⟨hQ, hQmult⟩ := ihPQ h
      obtain ⟨hR, hRmult⟩ := ihQR hQ
      exact ⟨hR, fun q ↦ (hRmult q).trans (hQmult q)⟩

/-- If a value belongs to every labelled layer and a choice leaves some
layer unused, insert that same value into one unused occurrence. -/
theorem exists_insert_common_value
    {P : List (Finset A)} {n : ℕ} {y b : A}
    (h : LayerSubsumChoice P n y)
    (hall : ∀ C ∈ P, b ∈ C) (hlt : n < P.length)
    (K : AddSubgroup A) [DecidableEq (A ⧸ K)] :
    ∃ h' : LayerSubsumChoice P (n + 1) (b + y),
      ∀ q : A ⧸ K, quotientMultiplicity K h' q =
        (if (b : A ⧸ K) = q then 1 else 0) +
          quotientMultiplicity K h q := by
  induction h with
  | zero P =>
      cases P with
      | nil => simp at hlt
      | cons C P =>
          have hbC : b ∈ C := hall C (by simp)
          exact ⟨LayerSubsumChoice.take hbC (LayerSubsumChoice.zero P), by
            intro q
            simp [quotientMultiplicity]⟩
  | @skip C P n y h ih =>
      have hbC : b ∈ C := hall C (by simp)
      exact ⟨LayerSubsumChoice.take hbC h, by
        intro q
        simp [quotientMultiplicity]⟩
  | @take C P n c y hc h ih =>
      have hallTail : ∀ D ∈ P, b ∈ D := by
        intro D hD
        exact hall D (by simp [hD])
      have hltTail : n < P.length := by simpa using hlt
      obtain ⟨h', h'mult⟩ := ih hallTail hltTail
      have hsum : c + (b + y) = b + (c + y) := by ac_rfl
      let hout : LayerSubsumChoice (C :: P) (n + 1 + 1)
          (c + (b + y)) := LayerSubsumChoice.take hc h'
      refine ⟨hsum ▸ hout, ?_⟩
      intro q
      rw [quotientMultiplicity_cast]
      simp only [hout, quotientMultiplicity]
      rw [h'mult q]
      omega

/-- When the leading cell is contained in every tail cell and fewer than all
layers are selected, every realization using the head can exchange it into
an unused labelled tail occurrence. -/
theorem exists_tail_of_head_subset_all
    {B : Finset A} {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice (B :: P) n y)
    (hall : ∀ C ∈ P, B ⊆ C) (hlt : n < (B :: P).length)
    (K : AddSubgroup A) [DecidableEq (A ⧸ K)] :
    ∃ h' : LayerSubsumChoice P n y,
      ∀ q : A ⧸ K, quotientMultiplicity K h' q =
        quotientMultiplicity K h q := by
  cases h with
  | zero =>
      exact ⟨LayerSubsumChoice.zero P, by
        simp [quotientMultiplicity]⟩
  | skip htail =>
      exact ⟨htail, by simp [quotientMultiplicity]⟩
  | @take _ _ k b z hb htail =>
      have hcommon : ∀ C ∈ P, b ∈ C := by
        intro C hC
        exact hall C hC hb
      have hltTail : k < P.length := by simpa using hlt
      obtain ⟨h', h'mult⟩ :=
        htail.exists_insert_common_value hcommon hltTail K
      exact ⟨h', by
        intro q
        simpa [quotientMultiplicity] using h'mult q⟩

/-- Any exact choice using fewer than all labelled layers survives deletion
of one explicitly unused index. -/
theorem exists_eraseIdx_of_weight_lt_length
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) (hlt : n < P.length)
    (K : AddSubgroup A) [DecidableEq (A ⧸ K)] :
    ∃ (i : ℕ) (hi : i < P.length),
      ∃ h' : LayerSubsumChoice (P.eraseIdx i) n y,
        ∀ q : A ⧸ K, quotientMultiplicity K h' q =
          quotientMultiplicity K h q := by
  induction h with
  | zero P =>
      cases P with
      | nil => simp at hlt
      | cons B P =>
          exact ⟨0, by simp, LayerSubsumChoice.zero P, by
            simp [quotientMultiplicity]⟩
  | @skip B P n y h ih =>
      exact ⟨0, by simp, h, by simp [quotientMultiplicity]⟩
  | @take B P n b y hb h ih =>
      have hltTail : n < P.length := by simpa using hlt
      obtain ⟨i, hi, h', h'mult⟩ := ih hltTail
      refine ⟨i + 1, by simp [hi], LayerSubsumChoice.take hb h', ?_⟩
      intro q
      simp only [quotientMultiplicity]
      rw [h'mult q]

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

/-- The canonical quotient pattern recorded by one proof-relevant choice. -/
noncomputable def LayerSubsumChoice.quotientPattern
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) : QuotientPattern K n where
  multiplicity := h.quotientMultiplicity K
  weight_eq := h.sum_quotientMultiplicity

@[simp]
theorem LayerSubsumChoice.quotientPattern_apply
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) (q : A ⧸ K) :
    h.quotientPattern K q = h.quotientMultiplicity K q := rfl

theorem LayerSubsumChoice.realizes_quotientPattern
    (K : AddSubgroup A) [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) : h.RealizesPattern (h.quotientPattern K) := by
  intro q
  rfl

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

/-- Reordering the labelled layers does not change a prescribed-pattern
spectrum.  The proof transports the proof-relevant choice, so repeated equal
layers remain distinct occurrences throughout. -/
theorem patternSubsumSpectrum_eq_of_perm
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] {P Q : List (Finset A)}
    (hPQ : P.Perm Q) (μ : QuotientPattern K n) :
    patternSubsumSpectrum P μ = patternSubsumSpectrum Q μ := by
  ext y
  constructor
  · intro hy
    obtain ⟨⟨h, hμ⟩⟩ := (mem_patternSubsumSpectrum_iff P μ y).1 hy
    obtain ⟨h', hmult⟩ :=
      LayerSubsumChoice.exists_of_perm hPQ h K
    exact (mem_patternSubsumSpectrum_iff Q μ y).2
      ⟨⟨h', fun q ↦ (hmult q).trans (hμ q)⟩⟩
  · intro hy
    obtain ⟨⟨h, hμ⟩⟩ := (mem_patternSubsumSpectrum_iff Q μ y).1 hy
    obtain ⟨h', hmult⟩ :=
      LayerSubsumChoice.exists_of_perm hPQ.symm h K
    exact (mem_patternSubsumSpectrum_iff P μ y).2
      ⟨⟨h', fun q ↦ (hmult q).trans (hμ q)⟩⟩

/-- Skipping a new leading labelled layer embeds every tail realization. -/
theorem patternSubsumSpectrum_tail_subset_cons
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] (B : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) :
    patternSubsumSpectrum P μ ⊆ patternSubsumSpectrum (B :: P) μ := by
  intro y hy
  obtain ⟨⟨h, hμ⟩⟩ := (mem_patternSubsumSpectrum_iff P μ y).1 hy
  exact (mem_patternSubsumSpectrum_iff (B :: P) μ y).2
    ⟨⟨LayerSubsumChoice.skip h, by
      intro q
      simpa [LayerSubsumChoice.quotientMultiplicity] using hμ q⟩⟩

/-- Enlarging one labelled cell preserves every realization, with the same
selected occurrence and quotient pattern. -/
theorem patternSubsumSpectrum_cons_mono
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] {B C : Finset A} (hBC : B ⊆ C)
    (P : List (Finset A)) (μ : QuotientPattern K n) :
    patternSubsumSpectrum (B :: P) μ ⊆
      patternSubsumSpectrum (C :: P) μ := by
  intro y hy
  obtain ⟨⟨h, hμ⟩⟩ :=
    (mem_patternSubsumSpectrum_iff (B :: P) μ y).1 hy
  cases h with
  | zero =>
      exact (mem_patternSubsumSpectrum_iff (C :: P) μ 0).2
        ⟨⟨LayerSubsumChoice.zero (C :: P), by
          intro q
          simpa [LayerSubsumChoice.quotientMultiplicity] using hμ q⟩⟩
  | skip htail =>
      exact (mem_patternSubsumSpectrum_iff (C :: P) μ y).2
        ⟨⟨LayerSubsumChoice.skip htail, by
          intro q
          simpa [LayerSubsumChoice.quotientMultiplicity] using hμ q⟩⟩
  | @take _ _ k b z hb htail =>
      exact (mem_patternSubsumSpectrum_iff (C :: P) μ (b + z)).2
        ⟨⟨LayerSubsumChoice.take (hBC hb) htail, by
          intro q
          simpa [LayerSubsumChoice.quotientMultiplicity] using hμ q⟩⟩

/-- A realization avoiding `B` remains feasible after the next cell `C` is
replaced by the intersection--union pair. -/
theorem patternSubsumSpectrum_tail_subset_inter_union
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] (B C : Finset A)
    (P : List (Finset A)) (μ : QuotientPattern K n) :
    patternSubsumSpectrum (C :: P) μ ⊆
      patternSubsumSpectrum ((B ∩ C) :: (B ∪ C) :: P) μ := by
  have hCunion : C ⊆ B ∪ C := fun _ hx ↦ Finset.mem_union_right B hx
  exact (patternSubsumSpectrum_cons_mono hCunion P μ).trans
    (patternSubsumSpectrum_tail_subset_cons (B ∩ C) ((B ∪ C) :: P) μ)

/-- Source `ℓ < m` common-cell exchange: deleting a leading cell contained
in every tail cell leaves the complete prescribed-pattern spectrum unchanged.
The strict weight inequality guarantees an unused labelled occurrence. -/
theorem patternSubsumSpectrum_cons_eq_tail_of_head_subset_all
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] (B : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) (hall : ∀ C ∈ P, B ⊆ C)
    (hlt : n < (B :: P).length) :
    patternSubsumSpectrum (B :: P) μ = patternSubsumSpectrum P μ := by
  apply Finset.Subset.antisymm
  · intro y hy
    obtain ⟨⟨h, hμ⟩⟩ :=
      (mem_patternSubsumSpectrum_iff (B :: P) μ y).1 hy
    obtain ⟨h', h'mult⟩ :=
      h.exists_tail_of_head_subset_all hall hlt K
    exact (mem_patternSubsumSpectrum_iff P μ y).2
      ⟨⟨h', fun q ↦ (h'mult q).trans (hμ q)⟩⟩
  · exact patternSubsumSpectrum_tail_subset_cons B P μ

/-- Finite labelled selection of the minimum-cardinality deletable cell.
Existence is not assumed: an actual prescribed-pattern realization with
weight strictly below the list length exposes an unused `eraseIdx`. -/
theorem exists_minimal_deletableIdx
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] (Q : List (Finset A))
    (μ : QuotientPattern K n)
    (hTarget : (patternSubsumSpectrum Q μ).Nonempty)
    (hlt : n < Q.length) :
    ∃ (i : ℕ) (hi : i < Q.length),
      (patternSubsumSpectrum (Q.eraseIdx i) μ).Nonempty ∧
      ∀ (j : ℕ) (hj : j < Q.length),
        (patternSubsumSpectrum (Q.eraseIdx j) μ).Nonempty →
        (Q[i]'hi).card ≤ (Q[j]'hj).card := by
  classical
  obtain ⟨y, hy⟩ := hTarget
  obtain ⟨⟨h, hμ⟩⟩ := (mem_patternSubsumSpectrum_iff Q μ y).1 hy
  obtain ⟨i₀, hi₀, h₀, h₀mult⟩ :=
    h.exists_eraseIdx_of_weight_lt_length hlt K
  have hdelete₀ :
      (patternSubsumSpectrum (Q.eraseIdx i₀) μ).Nonempty := by
    exact ⟨y, (mem_patternSubsumSpectrum_iff (Q.eraseIdx i₀) μ y).2
      ⟨⟨h₀, fun q ↦ (h₀mult q).trans (hμ q)⟩⟩⟩
  let p : ℕ → Prop := fun m ↦
    ∃ (i : ℕ) (hi : i < Q.length),
      (patternSubsumSpectrum (Q.eraseIdx i) μ).Nonempty ∧
      (Q[i]'hi).card = m
  have hp : ∃ m, p m :=
    ⟨(Q[i₀]'hi₀).card, i₀, hi₀, hdelete₀, rfl⟩
  obtain ⟨i, hi, hdelete, hcard⟩ := Nat.find_spec hp
  refine ⟨i, hi, hdelete, ?_⟩
  intro j hj hdeletej
  have hpj : p (Q[j]'hj).card := ⟨j, hj, hdeletej, rfl⟩
  have hle := Nat.find_min' hp hpj
  rw [hcard]
  exact hle

theorem patternSubsumSpectrum_nonempty_weight_le_length
    {K : AddSubgroup A} {n : ℕ} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K n)
    (hS : (patternSubsumSpectrum P μ).Nonempty) :
    n ≤ P.length := by
  obtain ⟨y, hy⟩ := hS
  obtain ⟨⟨h, _⟩⟩ := (mem_patternSubsumSpectrum_iff P μ y).1 hy
  exact h.weight_le_length

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

/-- A weight-zero pattern is pointwise zero. -/
theorem QuotientPattern.eq_zero_of_weight_zero
    {K : AddSubgroup A} [Fintype (A ⧸ K)]
    (μ : QuotientPattern K 0) (q : A ⧸ K) : μ q = 0 := by
  have hle : μ q ≤ ∑ r : A ⧸ K, μ r :=
    Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) (Finset.mem_univ q)
  rw [μ.weight_eq] at hle
  omega

/-- Exact base case for the tail pattern: every weight-zero pattern spectrum
is `{0}`, independently of the number or contents of the unused layers. -/
theorem patternSubsumSpectrum_zero_eq_singleton
    {K : AddSubgroup A} [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K 0) :
    patternSubsumSpectrum P μ = {0} := by
  classical
  ext y
  constructor
  · intro hy
    have hzero : y = 0 := by
      have hraw := patternSubsumSpectrum_subset_layerSubsumSpectrum P μ hy
      simpa using hraw
    simpa [hzero]
  · intro hy
    have hzero : y = 0 := by simpa using hy
    subst y
    apply (mem_patternSubsumSpectrum_iff P μ 0).2
    refine ⟨⟨LayerSubsumChoice.zero P, ?_⟩⟩
    intro q
    simp [LayerSubsumChoice.RealizesPattern,
      LayerSubsumChoice.quotientMultiplicity,
      μ.eq_zero_of_weight_zero q]

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

/-- The remaining three coordinates of the inner measure are also invariant
under permutation of labelled layers. -/
theorem dgmTotalLayerCard_eq_of_perm
    {P Q : List (Finset A)} (hPQ : P.Perm Q) :
    dgmTotalLayerCard P = dgmTotalLayerCard Q := by
  induction hPQ with
  | nil => rfl
  | cons B h ih => simpa [dgmTotalLayerCard] using ih
  | swap B C P => simp [dgmTotalLayerCard, Nat.add_comm, Nat.add_left_comm]
  | trans hPQ hQR ihPQ ihQR => exact ihPQ.trans ihQR

theorem dgmLayerSquareSum_eq_of_perm
    {P Q : List (Finset A)} (hPQ : P.Perm Q) :
    dgmLayerSquareSum P = dgmLayerSquareSum Q := by
  induction hPQ with
  | nil => rfl
  | cons B h ih => simpa [dgmLayerSquareSum] using ih
  | swap B C P => simp [dgmLayerSquareSum, Nat.add_comm, Nat.add_left_comm]
  | trans hPQ hQR ihPQ ihQR => exact ihPQ.trans ihQR

theorem dgmLayerSquareDefect_eq_of_perm [Fintype A]
    {P Q : List (Finset A)} (hPQ : P.Perm Q) :
    dgmLayerSquareDefect P = dgmLayerSquareDefect Q := by
  unfold dgmLayerSquareDefect
  rw [hPQ.length_eq, dgmLayerSquareSum_eq_of_perm hPQ]

/-- Consequently a permutation represents literally the same inner
minimal-counterexample instance. -/
theorem dgmPatternInnerMeasure_eq_of_perm
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P Q : List (Finset A)} (hPQ : P.Perm Q)
    (μ : QuotientPattern K n) :
    dgmPatternInnerMeasure P μ = dgmPatternInnerMeasure Q μ := by
  unfold dgmPatternInnerMeasure
  rw [patternSubsumSpectrum_eq_of_perm hPQ μ,
    dgmTotalLayerCard_eq_of_perm hPQ,
    dgmLayerSquareDefect_eq_of_perm hPQ, hPQ.length_eq]

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

theorem dgmCosetSlice_eq_of_quotient_eq (H : AddSubgroup A)
    (B : Finset A) {b₁ b₂ : A}
    (h : (b₁ : A ⧸ H) = (b₂ : A ⧸ H)) :
    dgmCosetSlice H B b₁ = dgmCosetSlice H B b₂ := by
  ext x
  simp only [mem_dgmCosetSlice_iff]
  rw [h]

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

/-- If the intersection--union transform cannot realize a weight-`k+2`
pattern, then every realizing choice in the original two leading layers must
take both of them.  This is the proof-relevant decomposition used to create
the source's `b₁,b₂,ν''`. -/
theorem exists_twoLeadingChoice_of_interUnion_infeasible
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) {y : A}
    (h : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hν : h.RealizesPattern ν)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    ∃ b₁ ∈ B, ∃ b₂ ∈ C, ∃ t : A,
      ∃ htail : LayerSubsumChoice P k t,
        y = b₁ + (b₂ + t) ∧
        ∀ q : A ⧸ H,
          ν q = (if (b₁ : A ⧸ H) = q then 1 else 0) +
            (if (b₂ : A ⧸ H) = q then 1 else 0) +
              htail.quotientMultiplicity H q := by
  classical
  cases h with
  | skip hC =>
      cases hC with
      | skip htail =>
          let hout : LayerSubsumChoice
              (dgmInterUnionLayers B C P) (k + 2) y :=
            LayerSubsumChoice.skip (LayerSubsumChoice.skip htail)
          have houtν : hout.RealizesPattern ν := by
            intro q
            simpa [hout, LayerSubsumChoice.RealizesPattern,
              LayerSubsumChoice.quotientMultiplicity] using hν q
          have hmem := (mem_patternSubsumSpectrum_iff _ ν _).2
            ⟨⟨hout, houtν⟩⟩
          rw [hinfeasible] at hmem
          simp at hmem
      | take hc htail =>
          let hout : LayerSubsumChoice
              (dgmInterUnionLayers B C P) (k + 2) _ :=
            LayerSubsumChoice.skip
              (LayerSubsumChoice.take (Finset.mem_union_right B hc) htail)
          have houtν : hout.RealizesPattern ν := by
            intro q
            simpa [hout, LayerSubsumChoice.RealizesPattern,
              LayerSubsumChoice.quotientMultiplicity] using hν q
          have hmem := (mem_patternSubsumSpectrum_iff _ ν _).2
            ⟨⟨hout, houtν⟩⟩
          rw [hinfeasible] at hmem
          simp at hmem
  | take hb hC =>
      cases hC with
      | skip htail =>
          let hout : LayerSubsumChoice
              (dgmInterUnionLayers B C P) (k + 2) _ :=
            LayerSubsumChoice.skip
              (LayerSubsumChoice.take (Finset.mem_union_left C hb) htail)
          have houtν : hout.RealizesPattern ν := by
            intro q
            simpa [hout, LayerSubsumChoice.RealizesPattern,
              LayerSubsumChoice.quotientMultiplicity] using hν q
          have hmem := (mem_patternSubsumSpectrum_iff _ ν _).2
            ⟨⟨hout, houtν⟩⟩
          rw [hinfeasible] at hmem
          simp at hmem
      | take hc htail =>
          refine ⟨_, hb, _, hc, _, htail, rfl, ?_⟩
          intro q
          simpa [LayerSubsumChoice.RealizesPattern,
            LayerSubsumChoice.quotientMultiplicity, Nat.add_assoc] using
              (hν q).symm

/-- Packaged faithful output of the previous decomposition: the chosen
leading values lie in the two set differences, the tail pattern is feasible,
and the original pattern is its exact two-step extension. -/
theorem exists_twoStepPattern_of_interUnion_infeasible
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2))
    (hνfeasible : (patternSubsumSpectrum (B :: C :: P) ν).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    ∃ b₁ ∈ B, b₁ ∉ C ∧ ∃ b₂ ∈ C, b₂ ∉ B ∧
      ∃ νtail : QuotientPattern H k,
        (patternSubsumSpectrum P νtail).Nonempty ∧
          ν.IsTwoStepExtension b₁ b₂ νtail := by
  classical
  obtain ⟨y, hy⟩ := hνfeasible
  obtain ⟨⟨h, hreal⟩⟩ := (mem_patternSubsumSpectrum_iff _ ν y).1 hy
  obtain ⟨b₁, hb₁, b₂, hb₂, t, htail, rfl, hext⟩ :=
    exists_twoLeadingChoice_of_interUnion_infeasible
      B C P ν h hreal hinfeasible
  let νtail : QuotientPattern H k := htail.quotientPattern H
  have htwo : ν.IsTwoStepExtension b₁ b₂ νtail := by
    intro q
    simpa [νtail, LayerSubsumChoice.quotientPattern] using hext q
  have htailmem : t ∈ patternSubsumSpectrum P νtail :=
    (mem_patternSubsumSpectrum_iff _ νtail t).2
      ⟨⟨htail, htail.realizes_quotientPattern H⟩⟩
  have hb₁not : b₁ ∉ C := by
    intro hb₁C
    let hout : LayerSubsumChoice (dgmInterUnionLayers B C P) (k + 2)
        (b₁ + (b₂ + t)) :=
      LayerSubsumChoice.take (Finset.mem_inter.mpr ⟨hb₁, hb₁C⟩)
        (LayerSubsumChoice.take (Finset.mem_union_right B hb₂) htail)
    have houtν : hout.RealizesPattern ν := by
      intro q
      change (if (b₁ : A ⧸ H) = q then 1 else 0) +
          ((if (b₂ : A ⧸ H) = q then 1 else 0) + νtail q) = ν q
      rw [htwo q]
      omega
    have hmem := (mem_patternSubsumSpectrum_iff _ ν _).2
      ⟨⟨hout, houtν⟩⟩
    rw [hinfeasible] at hmem
    simp at hmem
  have hb₂not : b₂ ∉ B := by
    intro hb₂B
    let hout : LayerSubsumChoice (dgmInterUnionLayers B C P) (k + 2)
        (b₂ + (b₁ + t)) :=
      LayerSubsumChoice.take (Finset.mem_inter.mpr ⟨hb₂B, hb₂⟩)
        (LayerSubsumChoice.take (Finset.mem_union_left C hb₁) htail)
    have houtν : hout.RealizesPattern ν := by
      intro q
      change (if (b₂ : A ⧸ H) = q then 1 else 0) +
          ((if (b₁ : A ⧸ H) = q then 1 else 0) + νtail q) = ν q
      rw [htwo q]
      omega
    have hmem := (mem_patternSubsumSpectrum_iff _ ν _).2
      ⟨⟨hout, houtν⟩⟩
    rw [hinfeasible] at hmem
    simp at hmem
  exact ⟨b₁, hb₁, hb₁not, b₂, hb₂, hb₂not, νtail,
    ⟨t, htailmem⟩, htwo⟩

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

/-- The proof-relevant decomposition immediately produces nonempty `D₁₂`
and the uncrossed pair-tail.  The crossed second pair is deliberately left
to the later numeric contradiction, as in the source proof. -/
theorem exists_initialCrossedData_of_interUnion_infeasible
    [Fintype A] {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2))
    (hνfeasible : (patternSubsumSpectrum (B :: C :: P) ν).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    ∃ b₁ ∈ B, b₁ ∉ C ∧ ∃ b₂ ∈ C, b₂ ∉ B ∧
      ∃ νtail : QuotientPattern H k,
        ν.IsTwoStepExtension b₁ b₂ νtail ∧
        (patternSubsumSpectrum P νtail).Nonempty ∧
        (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty ∧
        (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty := by
  obtain ⟨b₁, hb₁, hb₁C, b₂, hb₂, hb₂B, νtail, htail, hext⟩ :=
    exists_twoStepPattern_of_interUnion_infeasible
      B C P ν hνfeasible hinfeasible
  refine ⟨b₁, hb₁, hb₁C, b₂, hb₂, hb₂B, νtail, hext, htail,
    dgmCrossedD12_nonempty B C P hb₁ hb₂ νtail htail, ?_⟩
  exact dgmCrossedPairTail1_nonempty B C P hb₁ hb₂ νtail htail

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
theorem stabilizer_le_of_nonempty_subset_quotientFiber
    (H : AddSubgroup A) (D : Finset A) (hD : D.Nonempty)
    (q : A ⧸ H) (hfiber : ∀ x ∈ D, (x : A ⧸ H) = q) :
    AddAction.stabilizer A (D : Set A) ≤ H := by
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

theorem stabilizer_lt_of_proper_quotientFiber
    (H : AddSubgroup A) (D : Finset A) (hD : D.Nonempty)
    (q : A ⧸ H)
    (hfiber : ∀ x ∈ D, (x : A ⧸ H) = q)
    {y : A} (hyq : (y : A ⧸ H) = q) (hyD : y ∉ D) :
    AddAction.stabilizer A (D : Set A) < H := by
  have hle : AddAction.stabilizer A (D : Set A) ≤ H :=
    stabilizer_le_of_nonempty_subset_quotientFiber H D hD q hfiber
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

/-- A fixed quotient pattern forces every realizing sum into one `H`-coset,
so its spectrum has at most `|H|` elements. -/
theorem patternSubsumSpectrum_card_le_natCard_patternGroup
    [Fintype A] (H : AddSubgroup A) [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)] {n : ℕ}
    (P : List (Finset A)) (μ : QuotientPattern H n)
    (hS : (patternSubsumSpectrum P μ).Nonempty) :
    (patternSubsumSpectrum P μ).card ≤ Nat.card H := by
  obtain ⟨s, hs⟩ := hS
  have hsubset : patternSubsumSpectrum P μ ⊆ dgmCosetFiber H s := by
    intro y hy
    apply (mem_dgmCosetFiber_iff H s y).2
    rw [patternSubsumSpectrum_quotient_eq P μ hy,
      patternSubsumSpectrum_quotient_eq P μ hs]
  simpa [card_dgmCosetFiber] using Finset.card_le_card hsubset

/-- Every point of a nonempty `H`-periodic finite set brings its full literal
`H`-coset with it. -/
theorem dgmCosetFiber_subset_of_mem_of_stabilizer_eq
    [Fintype A] (C : Finset A) (hC : C.Nonempty)
    (H : AddSubgroup A)
    (hstab : AddAction.stabilizer A (C : Set A) = H)
    {y : A} (hy : y ∈ C) :
    dgmCosetFiber H y ⊆ C := by
  intro z hz
  have hsub : z - y ∈ H :=
    QuotientAddGroup.eq_iff_sub_mem.mp
      ((mem_dgmCosetFiber_iff H y z).1 hz)
  have hst : z - y ∈ C.addStab := by
    rw [← Finset.mem_coe, Finset.coe_addStab hC, hstab]
    exact hsub
  have htranslate := (Finset.mem_addStab hC).1 hst
  have hmem : (z - y) + y ∈ (z - y) +ᵥ C :=
    Finset.mem_vadd_finset.mpr ⟨y, hy, rfl⟩
  rw [htranslate] at hmem
  simpa using hmem

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

theorem dgmMissingPairCoset_eq_of_quotient_eq [Fintype A]
    (H L : AddSubgroup A) (B C : Finset A) {b₁ b₂ : A}
    (h : (b₁ : A ⧸ H) = (b₂ : A ⧸ H)) :
    dgmMissingPairCoset H L B C b₁ =
      dgmMissingPairCoset H L B C b₂ := by
  have hB := dgmCosetSlice_eq_of_quotient_eq H B h
  have hC := dgmCosetSlice_eq_of_quotient_eq H C h
  have hfiber : dgmCosetFiber H b₁ = dgmCosetFiber H b₂ := by
    ext x
    simp only [mem_dgmCosetFiber_iff]
    rw [h]
  simp only [dgmMissingPairCoset, dgmPairSliceSaturation]
  rw [hfiber, hB, hC]

theorem dgmMissingPairCoset_union_eq_of_quotient_eq [Fintype A]
    (H L : AddSubgroup A) (B C : Finset A) {b₁ b₂ : A}
    (h : (b₁ : A ⧸ H) = (b₂ : A ⧸ H)) :
    dgmMissingPairCoset H L B C b₁ ∪
        dgmMissingPairCoset H L B C b₂ =
      dgmMissingPairCoset H L B C b₁ := by
  rw [dgmMissingPairCoset_eq_of_quotient_eq H L B C h]
  exact Finset.union_self _

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

/-- The stabilizer lower bounds used in the first presentation of the final
arithmetic are in fact redundant: the two equation-(4) bounds and the two
truncated equation-(5) bounds already imply the required averaged upper
bound.  Keeping the subtraction truncated makes this lemma directly usable
without a separate `|Hᵢ| ≤ sᵢ` gate. -/
theorem dgmFourBounds_extra_le_two_mul_without_stab_lower
    (Hc s₁ s₂ h₁ h₂ l m : ℕ)
    (h4₁ : s₁ + h₁ ≤ Hc) (h4₂ : s₂ + h₂ ≤ Hc)
    (h5₁ : s₁ - h₁ + l + m ≤ Hc)
    (h5₂ : s₂ - h₂ + l + m ≤ Hc) :
    s₁ + s₂ + l + m ≤ 2 * Hc := by
  omega

/-- Divisibility rounding used between strict equation (3) and equation (4):
two multiples of a positive subgroup cardinal cannot be strictly ordered
without a full subgroup-cardinality gap. -/
theorem add_le_of_lt_of_dvd
    (d S Hc : ℕ) (hd : 0 < d) (hdS : d ∣ S) (hdH : d ∣ Hc)
    (hlt : S < Hc) :
    S + d ≤ Hc := by
  obtain ⟨s, rfl⟩ := hdS
  obtain ⟨h, hh⟩ := hdH
  rw [hh] at hlt ⊢
  have hsh : s < h := by
    exact (Nat.mul_lt_mul_left hd).mp (by simpa [Nat.mul_comm] using hlt)
  have hsuc : s + 1 ≤ h := hsh
  simpa [Nat.mul_add, Nat.mul_comm, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using Nat.mul_le_mul_left d hsuc

/-- Pure natural-number core of the strict-Xi combination.  This combines
the strict convergent inequality, paper equation (3), and the weighted Xi
claim without turning any weak inequality into a strict one. -/
theorem dgmStrictXiArithmetic
    (l h B D M AL TL AH TH k : ℕ)
    (hkTL : k ≤ TL) (hkTH : k ≤ TH)
    (hweightL : k + 2 ≤ AL) (hweightH : k + 2 ≤ AH)
    (hTLAL : TL ≤ AL) (hTHAH : TH ≤ AH)
    (hstrict : D + h * (AH - (k + 2) + 1) <
      l * (AL - (k + 2) + 1))
    (hthree : B + l * (TL - k) ≤ D + h * (TH - k))
    (hxi : l * (AL - TL) + M ≤ h * (AH - TH)) :
    B + M < h := by
  let tL := TL - k
  let tH := TH - k
  let gL := AL - TL
  let gH := AH - TH
  have hTL : TL = k + tL := by dsimp [tL]; omega
  have hTH : TH = k + tH := by dsimp [tH]; omega
  have hAL : AL = k + tL + gL := by
    dsimp [gL]
    omega
  have hAH : AH = k + tH + gH := by
    dsimp [gH]
    omega
  have hposL : 1 ≤ tL + gL := by omega
  have hposH : 1 ≤ tH + gH := by omega
  have hnormL : k + tL + gL - (k + 2) + 1 = tL + gL - 1 := by
    omega
  have hnormH : k + tH + gH - (k + 2) + 1 = tH + gH - 1 := by
    omega
  have hstrict' : D + h * (tH + gH - 1) <
      l * (tL + gL - 1) := by
    rw [hAL, hAH] at hstrict
    rw [hnormL, hnormH] at hstrict
    exact hstrict
  have hthree' : B + l * tL ≤ D + h * tH := by
    rw [hTL, hTH] at hthree
    simpa only [Nat.add_sub_cancel_left] using hthree
  have hxi' : l * gL + M ≤ h * gH := by
    rw [hAL, hTL, hAH, hTH] at hxi
    have hgainL : k + tL + gL - (k + tL) = gL := by omega
    have hgainH : k + tH + gH - (k + tH) = gH := by omega
    rw [hgainL, hgainH] at hxi
    exact hxi
  have hexpandL : l * (tL + gL - 1) + l = l * tL + l * gL := by
    calc
      l * (tL + gL - 1) + l = l * ((tL + gL - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = l * (tL + gL) := by congr 1 <;> omega
      _ = l * tL + l * gL := by rw [Nat.mul_add]
  have hexpandH : h * (tH + gH - 1) + h = h * tH + h * gH := by
    calc
      h * (tH + gH - 1) + h = h * ((tH + gH - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = h * (tH + gH) := by congr 1 <;> omega
      _ = h * tH + h * gH := by rw [Nat.mul_add]
  omega

/-- Paper equation (4), isolated from its combinatorial inputs.  Dropping
the nonnegative missing-set term from strict equation (3) and rounding
between two `l`-multiples gives one complete extra `l`-coset. -/
theorem dgmEquationFour_of_strictXiArithmetic
    (l h B D M AL TL AH TH k : ℕ)
    (hl : 0 < l) (hlB : l ∣ B) (hlh : l ∣ h)
    (hkTL : k ≤ TL) (hkTH : k ≤ TH)
    (hweightL : k + 2 ≤ AL) (hweightH : k + 2 ≤ AH)
    (hTLAL : TL ≤ AL) (hTHAH : TH ≤ AH)
    (hstrict : D + h * (AH - (k + 2) + 1) <
      l * (AL - (k + 2) + 1))
    (hthree : B + l * (TL - k) ≤ D + h * (TH - k))
    (hxi : l * (AL - TL) + M ≤ h * (AH - TH)) :
    B + l ≤ h := by
  have hBM : B + M < h := dgmStrictXiArithmetic
    l h B D M AL TL AH TH k hkTL hkTH hweightL hweightH
      hTLAL hTHAH hstrict hthree hxi
  exact add_le_of_lt_of_dvd l B h hl hlB hlh (lt_of_le_of_lt
    (Nat.le_add_right B M) hBM)

/-- Paper equation (5), isolated from its combinatorial inputs.  Here the
missing-set term is itself an `l`-multiple, so the strict Xi inequality can
be rounded without discarding it. -/
theorem dgmEquationFive_of_strictXiArithmetic
    (l h B D M AL TL AH TH k : ℕ)
    (hl : 0 < l) (hlB : l ∣ B) (hlM : l ∣ M) (hlh : l ∣ h)
    (hkTL : k ≤ TL) (hkTH : k ≤ TH)
    (hweightL : k + 2 ≤ AL) (hweightH : k + 2 ≤ AH)
    (hTLAL : TL ≤ AL) (hTHAH : TH ≤ AH)
    (hstrict : D + h * (AH - (k + 2) + 1) <
      l * (AL - (k + 2) + 1))
    (hthree : B + l * (TL - k) ≤ D + h * (TH - k))
    (hxi : l * (AL - TL) + M ≤ h * (AH - TH)) :
    B + l + M ≤ h := by
  have hBM : B + M < h := dgmStrictXiArithmetic
    l h B D M AL TL AH TH k hkTL hkTH hweightL hweightH
      hTLAL hTHAH hstrict hthree hxi
  have hround : B + M + l ≤ h :=
    add_le_of_lt_of_dvd l (B + M) h hl (Nat.dvd_add hlB hlM) hlh hBM
  omega

/-- Strict Xi arithmetic in the literal three-summand form delivered by
`dgmEquationThree_threeSummand`.  The two Kneser losses appear as `2*l`;
the `+1` in Claim 1 cancels one loss and the strict convergent inequality
cancels the other. -/
theorem dgmStrictXiArithmetic_threeSummand
    (l h B D M AL TL AH TH k : ℕ)
    (hkTL : k ≤ TL) (hkTH : k ≤ TH)
    (hweightL : k + 2 ≤ AL) (hweightH : k + 2 ≤ AH)
    (hTLAL : TL ≤ AL) (hTHAH : TH ≤ AH)
    (hstrict : D + h * (AH - (k + 2) + 1) <
      l * (AL - (k + 2) + 1))
    (hthree : B + l * (TL - k + 1) ≤
      D + 2 * l + h * (TH - k))
    (hxi : l * (AL - TL) + M ≤ h * (AH - TH)) :
    B + M < h := by
  let tL := TL - k
  let tH := TH - k
  let gL := AL - TL
  let gH := AH - TH
  have hTL : TL = k + tL := by dsimp [tL]; omega
  have hTH : TH = k + tH := by dsimp [tH]; omega
  have hAL : AL = k + tL + gL := by dsimp [gL]; omega
  have hAH : AH = k + tH + gH := by dsimp [gH]; omega
  have hposL : 2 ≤ tL + gL := by omega
  have hposH : 2 ≤ tH + gH := by omega
  have hnormL : k + tL + gL - (k + 2) + 1 = tL + gL - 1 := by
    omega
  have hnormH : k + tH + gH - (k + 2) + 1 = tH + gH - 1 := by
    omega
  have hstrict' : D + h * (tH + gH - 1) <
      l * (tL + gL - 1) := by
    rw [hAL, hAH, hnormL, hnormH] at hstrict
    exact hstrict
  have hthree' : B + l * (tL + 1) ≤ D + 2 * l + h * tH := by
    rw [hTL, hTH] at hthree
    simpa only [Nat.add_sub_cancel_left] using hthree
  have hxi' : l * gL + M ≤ h * gH := by
    rw [hAL, hTL, hAH, hTH] at hxi
    have hgainL : k + tL + gL - (k + tL) = gL := by omega
    have hgainH : k + tH + gH - (k + tH) = gH := by omega
    rw [hgainL, hgainH] at hxi
    exact hxi
  have hexpandL : l * (tL + gL - 1) + l = l * tL + l * gL := by
    calc
      l * (tL + gL - 1) + l = l * ((tL + gL - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = l * (tL + gL) := by congr 1 <;> omega
      _ = l * tL + l * gL := by rw [Nat.mul_add]
  have hexpandH : h * (tH + gH - 1) + h = h * tH + h * gH := by
    calc
      h * (tH + gH - 1) + h = h * ((tH + gH - 1) + 1) := by
        rw [Nat.mul_add, Nat.mul_one]
      _ = h * (tH + gH) := by congr 1 <;> omega
      _ = h * tH + h * gH := by rw [Nat.mul_add]
  rw [Nat.mul_add, Nat.mul_one] at hthree'
  omega

theorem dgmEquationFour_of_threeSummand
    (l h B D M AL TL AH TH k : ℕ)
    (hl : 0 < l) (hlB : l ∣ B) (hlh : l ∣ h)
    (hkTL : k ≤ TL) (hkTH : k ≤ TH)
    (hweightL : k + 2 ≤ AL) (hweightH : k + 2 ≤ AH)
    (hTLAL : TL ≤ AL) (hTHAH : TH ≤ AH)
    (hstrict : D + h * (AH - (k + 2) + 1) <
      l * (AL - (k + 2) + 1))
    (hthree : B + l * (TL - k + 1) ≤
      D + 2 * l + h * (TH - k))
    (hxi : l * (AL - TL) + M ≤ h * (AH - TH)) :
    B + l ≤ h := by
  have hBM := dgmStrictXiArithmetic_threeSummand
    l h B D M AL TL AH TH k hkTL hkTH hweightL hweightH
      hTLAL hTHAH hstrict hthree hxi
  exact add_le_of_lt_of_dvd l B h hl hlB hlh
    (lt_of_le_of_lt (Nat.le_add_right B M) hBM)

theorem dgmEquationFive_of_threeSummand
    (l h B D M AL TL AH TH k : ℕ)
    (hl : 0 < l) (hlB : l ∣ B) (hlM : l ∣ M) (hlh : l ∣ h)
    (hkTL : k ≤ TL) (hkTH : k ≤ TH)
    (hweightL : k + 2 ≤ AL) (hweightH : k + 2 ≤ AH)
    (hTLAL : TL ≤ AL) (hTHAH : TH ≤ AH)
    (hstrict : D + h * (AH - (k + 2) + 1) <
      l * (AL - (k + 2) + 1))
    (hthree : B + l * (TL - k + 1) ≤
      D + 2 * l + h * (TH - k))
    (hxi : l * (AL - TL) + M ≤ h * (AH - TH)) :
    B + l + M ≤ h := by
  have hBM := dgmStrictXiArithmetic_threeSummand
    l h B D M AL TL AH TH k hkTL hkTH hweightL hweightH
      hTLAL hTHAH hstrict hthree hxi
  have hround := add_le_of_lt_of_dvd l (B + M) h hl
    (Nat.dvd_add hlB hlM) hlh hBM
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

/-- Gate-free version of the concrete `(4)+(5)` endpoint: no auxiliary
lower bounds on `|H₁|,|H₂|` are needed. -/
theorem dgmCrossedFourBoundsContradiction_without_stab_lower
    [Fintype A] (H L H₁ H₂ : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H))
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
  have hbound' := dgmFourBounds_extra_le_two_mul_without_stab_lower
    (Nat.card H) s₁ s₂ (Nat.card H₁) (Nat.card H₂) (Nat.card L) m
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

theorem dgmCosetSlice_nonempty_iff_quotientLayer_mem
    (H : AddSubgroup A) (B : Finset A) (b : A) :
    (dgmCosetSlice H B b).Nonempty ↔
      (b : A ⧸ H) ∈ quotientLayer H B := by
  constructor
  · rintro ⟨x, hx⟩
    have hx' := (mem_dgmCosetSlice_iff H B b x).1 hx
    exact (mem_quotientLayer_iff H B _).2 ⟨x, hx'.1, hx'.2⟩
  · intro hq
    obtain ⟨x, hxB, hxq⟩ := (mem_quotientLayer_iff H B _).1 hq
    exact ⟨x, (mem_dgmCosetSlice_iff H B b x).2 ⟨hxB, hxq⟩⟩

/-- Quotient-level nonemptiness for the crossed second pair.  This avoids
the unnecessarily strong requirement that the chosen literal representatives
themselves belong to the opposite leading layers. -/
theorem dgmCrossedPairTail2_nonempty_of_quotientLayer_mem
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A)) {b₁ b₂ : A}
    (hb₂B : (b₂ : A ⧸ H) ∈ quotientLayer H B)
    (hb₁C : (b₁ : A ⧸ H) ∈ quotientLayer H C)
    (νtail : QuotientPattern H k)
    (htail : (patternSubsumSpectrum P νtail).Nonempty) :
    (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty := by
  exact ((dgmCosetSlice_nonempty_iff_quotientLayer_mem H B b₂).2 hb₂B).add
    ((dgmCosetSlice_nonempty_iff_quotientLayer_mem H C b₁).2 hb₁C) |>.add htail

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

/-- A proof-relevant choice cannot use a quotient value in more labelled
layers than the source list contains. -/
theorem LayerSubsumChoice.quotientMultiplicity_le_layerMultiplicity
    {K : AddSubgroup A} [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) (q : A ⧸ K) :
    h.quotientMultiplicity K q ≤ quotientLayerMultiplicity K P q := by
  classical
  induction h with
  | zero P => simp [LayerSubsumChoice.quotientMultiplicity,
      quotientLayerMultiplicity]
  | @skip B P n y h ih =>
      by_cases hq : q ∈ quotientLayer K B
      · rw [quotientLayerMultiplicity_cons_of_mem K B P q hq]
        simp only [LayerSubsumChoice.quotientMultiplicity]
        omega
      · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hq]
        simpa [LayerSubsumChoice.quotientMultiplicity] using ih
  | @take B P n b y hb h ih =>
      by_cases hbq : (b : A ⧸ K) = q
      · have hq : q ∈ quotientLayer K B :=
          (mem_quotientLayer_iff K B q).2 ⟨b, hb, hbq⟩
        rw [quotientLayerMultiplicity_cons_of_mem K B P q hq]
        simp only [LayerSubsumChoice.quotientMultiplicity, hbq, if_pos]
        omega
      · by_cases hq : q ∈ quotientLayer K B
        · rw [quotientLayerMultiplicity_cons_of_mem K B P q hq]
          simp only [LayerSubsumChoice.quotientMultiplicity]
          rw [if_neg hbq]
          omega
        · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hq]
          simp only [LayerSubsumChoice.quotientMultiplicity]
          rw [if_neg hbq]
          simpa using ih

/-- If every labelled layer meets one quotient value, its incidence
multiplicity is exactly the list length. -/
theorem quotientLayerMultiplicity_eq_length_of_mem_all
    (K : AddSubgroup A) (P : List (Finset A)) (q : A ⧸ K)
    (hall : ∀ C ∈ P, q ∈ quotientLayer K C) :
    quotientLayerMultiplicity K P q = P.length := by
  classical
  induction P with
  | nil => simp [quotientLayerMultiplicity]
  | cons C P ih =>
      have hC : q ∈ quotientLayer K C := hall C (by simp)
      have htail : ∀ D ∈ P, q ∈ quotientLayer K D := by
        intro D hD
        exact hall D (by simp [hD])
      rw [quotientLayerMultiplicity_cons_of_mem K C P q hC, ih htail]
      simp only [List.length_cons]
      omega

/-- At full weight every labelled layer is selected.  If each layer has a
singleton image modulo `K`, the choice multiplicity is therefore the raw
quotient-layer incidence multiplicity. -/
theorem LayerSubsumChoice.quotientMultiplicity_eq_layerMultiplicity_of_full
    {K : AddSubgroup A} [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) (hfull : n = P.length)
    (hsingle : ∀ B ∈ P, (quotientLayer K B).card = 1)
    (q : A ⧸ K) :
    h.quotientMultiplicity K q = quotientLayerMultiplicity K P q := by
  classical
  induction h with
  | zero P =>
      cases P with
      | nil => simp [LayerSubsumChoice.quotientMultiplicity,
          quotientLayerMultiplicity]
      | cons B P => simp at hfull
  | @skip B P n y h ih =>
      have hle := h.weight_le_length
      simp only [List.length_cons] at hfull
      omega
  | @take B P n b y hb h ih =>
      have hfullTail : n = P.length := by
        simpa using Nat.succ.inj hfull
      have hsingleTail : ∀ C ∈ P, (quotientLayer K C).card = 1 := by
        intro C hC
        exact hsingle C (by simp [hC])
      have hih := ih hfullTail hsingleTail
      have hcardB := hsingle B (by simp)
      obtain ⟨r, hr⟩ := Finset.card_eq_one.mp hcardB
      have hbmem : (b : A ⧸ K) ∈ quotientLayer K B :=
        (mem_quotientLayer_iff K B _).2 ⟨b, hb, rfl⟩
      have hbr : (b : A ⧸ K) = r := by simpa [hr] using hbmem
      have hiff : q ∈ quotientLayer K B ↔ (b : A ⧸ K) = q := by
        simp [hr, hbr, eq_comm]
      by_cases heq : (b : A ⧸ K) = q
      · rw [quotientLayerMultiplicity_cons_of_mem K B P q (hiff.2 heq)]
        simp [LayerSubsumChoice.quotientMultiplicity, heq, hih, add_comm]
      · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q
          (fun hq ↦ heq (hiff.1 hq))]
        simp [LayerSubsumChoice.quotientMultiplicity, heq, hih]

/-- Quotient-layer incidence multiplicity depends on the multiset of
labelled layers, not their order. -/
theorem quotientLayerMultiplicity_eq_of_perm
    (K : AddSubgroup A) {P Q : List (Finset A)}
    (hPQ : P.Perm Q) (q : A ⧸ K) :
    quotientLayerMultiplicity K P q = quotientLayerMultiplicity K Q q := by
  classical
  induction hPQ with
  | nil => simp [quotientLayerMultiplicity]
  | @cons B P Q hPQ ih =>
      by_cases hB : q ∈ quotientLayer K B
      · rw [quotientLayerMultiplicity_cons_of_mem K B P q hB,
          quotientLayerMultiplicity_cons_of_mem K B Q q hB, ih]
      · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hB,
          quotientLayerMultiplicity_cons_of_not_mem K B Q q hB, ih]
  | @swap B C P =>
      by_cases hB : q ∈ quotientLayer K B
      · by_cases hC : q ∈ quotientLayer K C
        · rw [quotientLayerMultiplicity_cons_of_mem K C (B :: P) q hC,
            quotientLayerMultiplicity_cons_of_mem K B P q hB,
            quotientLayerMultiplicity_cons_of_mem K B (C :: P) q hB,
            quotientLayerMultiplicity_cons_of_mem K C P q hC]
        · rw [quotientLayerMultiplicity_cons_of_not_mem K C (B :: P) q hC,
            quotientLayerMultiplicity_cons_of_mem K B P q hB,
            quotientLayerMultiplicity_cons_of_mem K B (C :: P) q hB,
            quotientLayerMultiplicity_cons_of_not_mem K C P q hC]
      · by_cases hC : q ∈ quotientLayer K C
        · rw [quotientLayerMultiplicity_cons_of_mem K C (B :: P) q hC,
            quotientLayerMultiplicity_cons_of_not_mem K B P q hB,
            quotientLayerMultiplicity_cons_of_not_mem K B (C :: P) q hB,
            quotientLayerMultiplicity_cons_of_mem K C P q hC]
        · rw [quotientLayerMultiplicity_cons_of_not_mem K C (B :: P) q hC,
            quotientLayerMultiplicity_cons_of_not_mem K B P q hB,
            quotientLayerMultiplicity_cons_of_not_mem K B (C :: P) q hB,
            quotientLayerMultiplicity_cons_of_not_mem K C P q hC]
  | @trans P Q R hPQ hQR ihPQ ihQR => exact ihPQ.trans ihQR

/-- If at least one layer meets `q`, there is a one-layer proof-relevant
choice in `q`.  The statement records the complete quotient multiplicity of
the new choice, so it can be inserted into a prescribed pattern. -/
theorem exists_layerSubsumChoice_one_in_quotient
    {K : AddSubgroup A} [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (q : A ⧸ K)
    (hq : 0 < quotientLayerMultiplicity K P q) :
    ∃ y : A, ∃ h : LayerSubsumChoice P 1 y,
      ∀ r : A ⧸ K,
        h.quotientMultiplicity K r = if q = r then 1 else 0 := by
  classical
  induction P with
  | nil => simp [quotientLayerMultiplicity] at hq
  | cons B P ih =>
      by_cases hqB : q ∈ quotientLayer K B
      · obtain ⟨x, hxB, hxq⟩ := (mem_quotientLayer_iff K B q).1 hqB
        refine ⟨x + 0, LayerSubsumChoice.take hxB
          (LayerSubsumChoice.zero P), ?_⟩
        intro r
        simp [LayerSubsumChoice.quotientMultiplicity, hxq]
      · have htail : 0 < quotientLayerMultiplicity K P q := by
          rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hqB] at hq
          exact hq
        obtain ⟨y, h, hmult⟩ := ih htail
        refine ⟨y, LayerSubsumChoice.skip h, ?_⟩
        intro r
        exact hmult r

/-- Proof-relevant unused-layer exchange.  If `q` meets more layers than an
exact-`n` choice uses in total, one of those `q`-layers is unused.  Inserting
a value from it raises only the `q` quotient multiplicity by one. -/
theorem exists_layerSubsumChoice_succ_in_quotient
    {K : AddSubgroup A} [DecidableEq (A ⧸ K)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) (q : A ⧸ K)
    (hq : n < quotientLayerMultiplicity K P q) :
    ∃ z : A, ∃ h' : LayerSubsumChoice P (n + 1) z,
      ∀ r : A ⧸ K,
        h'.quotientMultiplicity K r =
          (if q = r then 1 else 0) + h.quotientMultiplicity K r := by
  classical
  induction h with
  | zero P =>
      obtain ⟨z, h', h'mult⟩ :=
        exists_layerSubsumChoice_one_in_quotient P q hq
      refine ⟨z, h', ?_⟩
      intro r
      simpa [LayerSubsumChoice.quotientMultiplicity] using h'mult r
  | @skip B P n y h ih =>
      by_cases hqB : q ∈ quotientLayer K B
      · obtain ⟨x, hxB, hxq⟩ := (mem_quotientLayer_iff K B q).1 hqB
        refine ⟨x + y, LayerSubsumChoice.take hxB h, ?_⟩
        intro r
        simp only [LayerSubsumChoice.quotientMultiplicity]
        rw [hxq]
      · have htail : n < quotientLayerMultiplicity K P q := by
          rwa [quotientLayerMultiplicity_cons_of_not_mem K B P q hqB] at hq
        obtain ⟨z, h', h'mult⟩ := ih htail
        refine ⟨z, LayerSubsumChoice.skip h', ?_⟩
        intro r
        exact h'mult r
  | @take B P n b y hb h ih =>
      by_cases hqB : q ∈ quotientLayer K B
      · have htail : n < quotientLayerMultiplicity K P q := by
          rw [quotientLayerMultiplicity_cons_of_mem K B P q hqB] at hq
          omega
        obtain ⟨z, h', h'mult⟩ := ih htail
        refine ⟨b + z, LayerSubsumChoice.take hb h', ?_⟩
        intro r
        simp only [LayerSubsumChoice.quotientMultiplicity]
        rw [h'mult r]
        omega
      · have htail : n < quotientLayerMultiplicity K P q := by
          rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hqB] at hq
          omega
        obtain ⟨z, h', h'mult⟩ := ih htail
        refine ⟨b + z, LayerSubsumChoice.take hb h', ?_⟩
        intro r
        simp only [LayerSubsumChoice.quotientMultiplicity]
        rw [h'mult r]
        omega

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

/-- The capped DGM incidence count is invariant under permutation of the
labelled layer list. -/
theorem dgmCappedMultiplicitySum_eq_of_perm
    (K : AddSubgroup A) [Finite (A ⧸ K)]
    {P Q : List (Finset A)} (hPQ : P.Perm Q) (n : ℕ) :
    dgmCappedMultiplicitySum K P n = dgmCappedMultiplicitySum K Q n := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  unfold dgmCappedMultiplicitySum
  apply Finset.sum_congr rfl
  intro q _
  rw [quotientLayerMultiplicity_eq_of_perm K hPQ q]

/-- A single exact-layer witness is enough for every quotient capped-count
lower bound; no nonemptiness of unselected cells is required. -/
theorem le_dgmCappedMultiplicitySum_of_layerSubsumSpectrum_nonempty
    (K : AddSubgroup A) [Fintype (A ⧸ K)]
    (P : List (Finset A)) (n : ℕ)
    (hS : (layerSubsumSpectrum P n).Nonempty) :
    n ≤ dgmCappedMultiplicitySum K P n := by
  classical
  obtain ⟨y, hy⟩ := hS
  obtain ⟨h⟩ := (nonempty_layerSubsumChoice_iff_mem P n y).2 hy
  have hcap : dgmCappedMultiplicitySum K P n =
      ∑ q : A ⧸ K, min n (quotientLayerMultiplicity K P q) := by
    rw [dgmCappedMultiplicitySum]
    congr 1
    ext q
    simp
  rw [hcap]
  calc
    n = ∑ q : A ⧸ K, h.quotientMultiplicity K q :=
      h.sum_quotientMultiplicity.symm
    _ ≤ ∑ q : A ⧸ K, min n (quotientLayerMultiplicity K P q) := by
      apply Finset.sum_le_sum
      intro q _
      apply le_min
      · have hsingle : h.quotientMultiplicity K q ≤
            ∑ r : A ⧸ K, h.quotientMultiplicity K r :=
          Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _)
            (Finset.mem_univ q)
        rw [h.sum_quotientMultiplicity (K := K)] at hsingle
        exact hsingle
      · exact h.quotientMultiplicity_le_layerMultiplicity q

/-- In the common-cell `ℓ < m` branch, deleting the leading labelled cell
does not change any capped quotient incidence: every quotient value lost at
the head still occurs in all `m-1 ≥ ℓ` tail cells. -/
theorem dgmCappedMultiplicitySum_cons_eq_tail_of_head_subset_all
    (K : AddSubgroup A) [Finite (A ⧸ K)]
    (B : Finset A) (P : List (Finset A)) (n : ℕ)
    (hall : ∀ C ∈ P, B ⊆ C) (hlt : n < (B :: P).length) :
    dgmCappedMultiplicitySum K (B :: P) n =
      dgmCappedMultiplicitySum K P n := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  unfold dgmCappedMultiplicitySum
  apply Finset.sum_congr rfl
  intro q _
  by_cases hq : q ∈ quotientLayer K B
  · obtain ⟨b, hbB, hbq⟩ := (mem_quotientLayer_iff K B q).1 hq
    have hqall : ∀ C ∈ P, q ∈ quotientLayer K C := by
      intro C hC
      exact (mem_quotientLayer_iff K C q).2
        ⟨b, hall C hC hbB, hbq⟩
    have htail := quotientLayerMultiplicity_eq_length_of_mem_all
      K P q hqall
    have hn : n ≤ P.length := by simpa using hlt
    have hn' : n ≤ 1 + P.length := hn.trans (by omega)
    rw [quotientLayerMultiplicity_cons_of_mem K B P q hq, htail]
    rw [min_eq_left hn', min_eq_left hn]
  · rw [quotientLayerMultiplicity_cons_of_not_mem K B P q hq]

/-- If full weight is prescribed and every layer lies in one `K`-coset,
the pattern is forced: the prescribed-pattern spectrum is the entire
full-layer sumset. -/
theorem patternSubsumSpectrum_eq_fullLayerSumSpectrum_of_singleton_quotient
    {K : AddSubgroup A} [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)] (P : List (Finset A))
    (μ : QuotientPattern K P.length)
    (hTarget : (patternSubsumSpectrum P μ).Nonempty)
    (hsingle : ∀ B ∈ P, (quotientLayer K B).card = 1) :
    patternSubsumSpectrum P μ = fullLayerSumSpectrum P := by
  obtain ⟨y₀, hy₀⟩ := hTarget
  obtain ⟨⟨h₀, hμ₀⟩⟩ :=
    (mem_patternSubsumSpectrum_iff P μ y₀).1 hy₀
  apply Finset.Subset.antisymm
  · exact patternSubsumSpectrum_subset_layerSubsumSpectrum P μ
  · intro y hy
    obtain ⟨h⟩ := (nonempty_layerSubsumChoice_iff_mem
      P P.length y).2 (by simpa [fullLayerSumSpectrum] using hy)
    have hreal : h.RealizesPattern μ := by
      intro q
      have hh := h.quotientMultiplicity_eq_layerMultiplicity_of_full
        rfl hsingle q
      have hh₀ := h₀.quotientMultiplicity_eq_layerMultiplicity_of_full
        rfl hsingle q
      exact hh.trans (hh₀.symm.trans (hμ₀ q))
    exact (mem_patternSubsumSpectrum_iff P μ y).2 ⟨⟨h, hreal⟩⟩

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

/-- Under the singleton-quotient hypothesis, the full-weight `K` incidence
correction is exactly zero. -/
theorem dgmCappedMultiplicitySum_full_eq_length_of_singleton_quotient
    (K : AddSubgroup A) [Finite (A ⧸ K)]
    (P : List (Finset A))
    (hsingle : ∀ B ∈ P, (quotientLayer K B).card = 1) :
    dgmCappedMultiplicitySum K P P.length = P.length := by
  rw [dgmCappedMultiplicitySum_length]
  induction P with
  | nil => simp
  | cons B P ih =>
      have hB := hsingle B (by simp)
      have htail : ∀ C ∈ P, (quotientLayer K C).card = 1 := by
        intro C hC
        exact hsingle C (by simp [hC])
      simp only [List.map_cons, List.sum_cons, List.length_cons]
      rw [hB, ih htail]
      omega

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

/-- The proof-relevant swap giving the tail part of exceptionality.  If the
tail met `b₁+H` in more than `k` layers, a realizing exact-`k` tail choice
could be augmented in an unused such layer; together with one union-layer
choice in `b₂+H`, this would realize the allegedly infeasible transformed
two-step pattern. -/
theorem quotientLayerMultiplicity_tail_le_of_twoStep_infeasible
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hunion₂ : (b₂ : A ⧸ H) ∈ quotientLayer H (B ∪ C))
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    quotientLayerMultiplicity H P (b₁ : A ⧸ H) ≤ k := by
  classical
  by_contra hnot
  have hmore : k < quotientLayerMultiplicity H P (b₁ : A ⧸ H) :=
    Nat.lt_of_not_ge hnot
  obtain ⟨t, ht⟩ := htail
  obtain ⟨⟨htailChoice, htailPattern⟩⟩ :=
    (mem_patternSubsumSpectrum_iff P νtail t).1 ht
  obtain ⟨z, haug, haugMult⟩ :=
    exists_layerSubsumChoice_succ_in_quotient htailChoice
      (b₁ : A ⧸ H) hmore
  obtain ⟨x₂, hx₂U, hx₂q⟩ :=
    (mem_quotientLayer_iff H (B ∪ C) (b₂ : A ⧸ H)).1 hunion₂
  let hout : LayerSubsumChoice
      ((B ∩ C) :: (B ∪ C) :: P) (k + 2) (x₂ + z) :=
    LayerSubsumChoice.skip (B := B ∩ C)
      (LayerSubsumChoice.take hx₂U haug)
  have houtPattern : hout.RealizesPattern ν := by
    intro q
    change (if (x₂ : A ⧸ H) = q then 1 else 0) +
        haug.quotientMultiplicity H q = ν q
    rw [hx₂q, haugMult q, htailPattern q, hext q]
    omega
  have hmem : x₂ + z ∈ patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν :=
    (mem_patternSubsumSpectrum_iff _ ν _).2 ⟨⟨hout, houtPattern⟩⟩
  rw [hinfeasible] at hmem
  simpa using hmem

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

/-- If the transformed two-leading-layer pattern is infeasible while its
tail pattern is feasible, the intersection layer cannot meet the first
exceptional coset once the union layer meets the second. -/
theorem not_mem_quotientLayer_inter_of_twoStep_infeasible
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hunion₂ : (b₂ : A ⧸ H) ∈ quotientLayer H (B ∪ C))
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    (b₁ : A ⧸ H) ∉ quotientLayer H (B ∩ C) := by
  intro hinter
  obtain ⟨x₁, hx₁, hx₁q⟩ :=
    (mem_quotientLayer_iff H (B ∩ C) (b₁ : A ⧸ H)).1 hinter
  obtain ⟨x₂, hx₂, hx₂q⟩ :=
    (mem_quotientLayer_iff H (B ∪ C) (b₂ : A ⧸ H)).1 hunion₂
  obtain ⟨t, ht⟩ := htail
  have hx₁slice : x₁ ∈ dgmCosetSlice H (B ∩ C) b₁ :=
    (mem_dgmCosetSlice_iff H (B ∩ C) b₁ x₁).2 ⟨hx₁, hx₁q⟩
  have hx₂slice : x₂ ∈ dgmCosetSlice H (B ∪ C) b₂ :=
    (mem_dgmCosetSlice_iff H (B ∪ C) b₂ x₂).2 ⟨hx₂, hx₂q⟩
  have hmem := mem_patternSubsumSpectrum_cons_cons_of_twoStep
    (B ∩ C) (B ∪ C) P ν b₁ b₂ νtail hext
    hx₁slice hx₂slice ht
  have hmem' : x₁ + (x₂ + t) ∈ patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν := by
    simpa [dgmInterUnionLayers] using hmem
  rw [hinfeasible] at hmem'
  simpa using hmem'

/-- Symmetric form for the second exceptional coset. -/
theorem not_mem_quotientLayer_inter_second_of_twoStep_infeasible
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hunion₁ : (b₁ : A ⧸ H) ∈ quotientLayer H (B ∪ C))
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    (b₂ : A ⧸ H) ∉ quotientLayer H (B ∩ C) := by
  have hext' : ν.IsTwoStepExtension b₂ b₁ νtail := by
    intro q
    rw [hext q]
    omega
  exact not_mem_quotientLayer_inter_of_twoStep_infeasible
    B C P ν b₂ b₁ νtail hext' htail hunion₁ hinfeasible

/-- The first crossed coset is exceptional whenever the transformed pattern
is infeasible.  All three clauses are derived: intersection miss, capped tail
multiplicity, and union hit. -/
theorem dgmXiExceptionalCoset_first_of_twoStep_infeasible
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) {b₁ b₂ : A}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    DGMXiExceptionalCoset H B C P k b₁ := by
  have hunion₁ : (b₁ : A ⧸ H) ∈ quotientLayer H (B ∪ C) :=
    (mem_quotientLayer_iff H (B ∪ C) _).2
      ⟨b₁, Finset.mem_union_left C hb₁, rfl⟩
  have hunion₂ : (b₂ : A ⧸ H) ∈ quotientLayer H (B ∪ C) :=
    (mem_quotientLayer_iff H (B ∪ C) _).2
      ⟨b₂, Finset.mem_union_right B hb₂, rfl⟩
  exact ⟨
    not_mem_quotientLayer_inter_of_twoStep_infeasible
      B C P ν b₁ b₂ νtail hext htail hunion₂ hinfeasible,
    quotientLayerMultiplicity_tail_le_of_twoStep_infeasible
      B C P ν b₁ b₂ νtail hext htail hunion₂ hinfeasible,
    hunion₁⟩

/-- Symmetric exceptional-coset conclusion for the second crossed coset. -/
theorem dgmXiExceptionalCoset_second_of_twoStep_infeasible
    {H : AddSubgroup A} {k : ℕ} [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) {b₁ b₂ : A}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    DGMXiExceptionalCoset H B C P k b₂ := by
  have hext' : ν.IsTwoStepExtension b₂ b₁ νtail := by
    intro q
    rw [hext q]
    omega
  have hunion₁ : (b₁ : A ⧸ H) ∈ quotientLayer H (B ∪ C) :=
    (mem_quotientLayer_iff H (B ∪ C) _).2
      ⟨b₁, Finset.mem_union_left C hb₁, rfl⟩
  have hunion₂ : (b₂ : A ⧸ H) ∈ quotientLayer H (B ∪ C) :=
    (mem_quotientLayer_iff H (B ∪ C) _).2
      ⟨b₂, Finset.mem_union_right B hb₂, rfl⟩
  exact ⟨
    not_mem_quotientLayer_inter_second_of_twoStep_infeasible
      B C P ν b₁ b₂ νtail hext htail hunion₁ hinfeasible,
    quotientLayerMultiplicity_tail_le_of_twoStep_infeasible
      B C P ν b₂ b₁ νtail hext' htail hunion₁ hinfeasible,
    hunion₂⟩

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

/-- A proof-relevant choice counted modulo a coarse subgroup is the sum of
its multiplicities over the fine quotient cosets lying above that coarse
coset.  This is the exact pattern-refinement identity used when a DGM
counterexample passes from its original stabilizer to the stabilizer of a
minimal convergent portion. -/
theorem LayerSubsumChoice.quotientMultiplicity_eq_sum_refinementFiber
    (L H : AddSubgroup A) [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) (r : A ⧸ H) :
    h.quotientMultiplicity H r =
      ∑ q ∈ dgmQuotientRefinementFiber L H hLH r,
        h.quotientMultiplicity L q := by
  classical
  induction h with
  | zero P => simp [LayerSubsumChoice.quotientMultiplicity]
  | skip h ih => simpa [LayerSubsumChoice.quotientMultiplicity] using ih
  | @take B P n b y hb h ih =>
      simp only [LayerSubsumChoice.quotientMultiplicity,
        Finset.sum_add_distrib]
      rw [ih]
      simp [dgmQuotientRefinementFiber, dgmQuotientRefinementMap_mk]

/-- A fine quotient pattern induced by an actual choice refines every
coarser pattern realized by that same choice. -/
theorem LayerSubsumChoice.realizesPattern_of_realizes_quotientPattern_of_le
    (L H : AddSubgroup A) [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    {Pbase Pcand : List (Finset A)} {n : ℕ} {y z : A}
    (base : LayerSubsumChoice Pbase n y) (μ : QuotientPattern H n)
    (hbase : base.RealizesPattern μ)
    (candidate : LayerSubsumChoice Pcand n z)
    (hcandidate : candidate.RealizesPattern (base.quotientPattern L)) :
    candidate.RealizesPattern μ := by
  intro r
  calc
    candidate.quotientMultiplicity H r =
        ∑ q ∈ dgmQuotientRefinementFiber L H hLH r,
          candidate.quotientMultiplicity L q :=
      candidate.quotientMultiplicity_eq_sum_refinementFiber L H hLH r
    _ = ∑ q ∈ dgmQuotientRefinementFiber L H hLH r,
          base.quotientMultiplicity L q := by
      apply Finset.sum_congr rfl
      intro q hq
      exact hcandidate q
    _ = base.quotientMultiplicity H r :=
      (base.quotientMultiplicity_eq_sum_refinementFiber L H hLH r).symm
    _ = μ r := hbase r

/-- Every sum realizing the fine pattern canonically induced by one witness
also realizes the witness's original coarse pattern.  Thus refinement never
creates sums outside the source pattern spectrum. -/
theorem patternSubsumSpectrum_quotientPattern_subset_of_realizes_of_le
    (L H : AddSubgroup A) [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    {Pbase Q : List (Finset A)} {n : ℕ} {y : A}
    (base : LayerSubsumChoice Pbase n y) (μ : QuotientPattern H n)
    (hbase : base.RealizesPattern μ) :
    patternSubsumSpectrum Q (base.quotientPattern L) ⊆
      patternSubsumSpectrum Q μ := by
  intro z hz
  obtain ⟨⟨candidate, hcandidate⟩⟩ :=
    (mem_patternSubsumSpectrum_iff Q (base.quotientPattern L) z).1 hz
  exact (mem_patternSubsumSpectrum_iff Q μ z).2
    ⟨⟨candidate,
      LayerSubsumChoice.realizesPattern_of_realizes_quotientPattern_of_le
        L H hLH base μ hbase candidate hcandidate⟩⟩

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

/-- Every literal `L`-saturation has cardinality divisible by `|L|`.  This is
the integrality input used to round a strict inequality between saturated
slice sizes up by one complete `L`-coset. -/
theorem natCard_dvd_card_add_dgmSubgroupFinset
    [Fintype A] (L : AddSubgroup A) [Fintype (A ⧸ L)]
    [DecidableEq (A ⧸ L)] (S : Finset A) :
    Nat.card L ∣ (S + dgmSubgroupFinset L).card := by
  rw [card_add_dgmSubgroupFinset_eq L S]
  exact ⟨(quotientLayer L S).card, rfl⟩

/-- The complement of an `L`-saturated pair of slices inside one `H`-coset
also has cardinality divisible by `|L|`.  This is the integrality input for
the common `X₁₂,Y₁₂` term in paper equation (5). -/
theorem natCard_dvd_card_dgmMissingPairCoset
    [Fintype A] (H L : AddSubgroup A) (hLH : L ≤ H)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (B C : Finset A) (b : A) :
    Nat.card L ∣ (dgmMissingPairCoset H L B C b).card := by
  have hH : Nat.card L ∣ Nat.card H := AddSubgroup.card_dvd_of_le hLH
  have hpair : Nat.card L ∣
      (dgmPairSliceSaturation H L B C b).card := by
    simpa [dgmPairSliceSaturation] using
      natCard_dvd_card_add_dgmSubgroupFinset L
        (dgmCosetSlice H B b ∪ dgmCosetSlice H C b)
  have hcard := card_missing_add_pairSaturation H L hLH B C b
  have heq : (dgmMissingPairCoset H L B C b).card =
      Nat.card H - (dgmPairSliceSaturation H L B C b).card := by
    omega
  rw [heq]
  exact Nat.dvd_sub hH hpair

/-- For distinct coarse cosets the union of the two missing sets is again a
union of complete `L`-cosets, hence its cardinality is divisible by `|L|`. -/
theorem natCard_dvd_card_dgmMissingPairCoset_union
    [Fintype A] (H L : AddSubgroup A) (hLH : L ≤ H)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    (B C : Finset A) (b₁ b₂ : A)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H)) :
    Nat.card L ∣
      (dgmMissingPairCoset H L B C b₁ ∪
        dgmMissingPairCoset H L B C b₂).card := by
  rw [Finset.card_union_of_disjoint
    (disjoint_dgmMissingPairCoset_of_ne H L B C b₁ b₂ hne)]
  exact Nat.dvd_add
    (natCard_dvd_card_dgmMissingPairCoset H L hLH B C b₁)
    (natCard_dvd_card_dgmMissingPairCoset H L hLH B C b₂)

/-- Saturate every layer by a subgroup.  This is the paper's sequence
`(A₃+L, …, Aₘ+L)` used in the inductive tail call of equation (2). -/
noncomputable def dgmSaturateLayers [Fintype A]
    (L : AddSubgroup A) (P : List (Finset A)) : List (Finset A) :=
  P.map fun B ↦ B + dgmSubgroupFinset L

theorem dgmSaturateLayers_nonempty [Fintype A]
    (L : AddSubgroup A) (P : List (Finset A))
    (hP : IsNonemptySetPartition P) :
    IsNonemptySetPartition (dgmSaturateLayers L P) := by
  intro C hC
  obtain ⟨B, hBP, rfl⟩ := List.mem_map.mp (by
    simpa [dgmSaturateLayers] using hC)
  exact (hP B hBP).add
    ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩

/-- Addition of subgroup finsets absorbs the smaller subgroup. -/
theorem dgmSubgroupFinset_add_eq_of_le [Fintype A]
    (L₀ L : AddSubgroup A) (hL₀L : L₀ ≤ L) :
    dgmSubgroupFinset L₀ + dgmSubgroupFinset L = dgmSubgroupFinset L := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    exact (mem_dgmSubgroupFinset_iff L _).2
      (L.add_mem (hL₀L ((mem_dgmSubgroupFinset_iff L₀ x).1 hx))
        ((mem_dgmSubgroupFinset_iff L y).1 hy))
  · intro hz
    exact Finset.mem_add.mpr
      ⟨0, (mem_dgmSubgroupFinset_iff L₀ 0).2 L₀.zero_mem,
        z, hz, zero_add z⟩

/-- A finite subgroup, viewed literally as a finset, is its own additive
stabilizer. -/
theorem addStab_dgmSubgroupFinset_eq [Fintype A]
    (L : AddSubgroup A) :
    (dgmSubgroupFinset L).addStab = dgmSubgroupFinset L := by
  classical
  have hLne : (dgmSubgroupFinset L).Nonempty :=
    ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩
  apply Finset.Subset.antisymm
  · intro a ha
    have htranslate := (Finset.mem_addStab hLne).1 ha
    have ha0 : a ∈ a +ᵥ dgmSubgroupFinset L :=
      Finset.mem_vadd_finset.mpr
        ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem, by simp⟩
    rw [htranslate] at ha0
    exact ha0
  · intro a ha
    apply (Finset.mem_addStab hLne).2
    ext z
    constructor
    · intro hz
      obtain ⟨y, hy, rfl⟩ := Finset.mem_vadd_finset.mp hz
      exact (mem_dgmSubgroupFinset_iff L _).2
        (L.add_mem ((mem_dgmSubgroupFinset_iff L a).1 ha)
          ((mem_dgmSubgroupFinset_iff L y).1 hy))
    · intro hz
      have hza : z - a ∈ dgmSubgroupFinset L :=
        (mem_dgmSubgroupFinset_iff L _).2
          (L.sub_mem ((mem_dgmSubgroupFinset_iff L z).1 hz)
            ((mem_dgmSubgroupFinset_iff L a).1 ha))
      apply Finset.mem_vadd_finset.mpr
      refine ⟨z - a, hza, ?_⟩
      change a + (z - a) = z
      abel

/-- The set identity behind the actual-stabilizer part of Claim 1.  If
`D=(X+T)+L₀` has stabilizer `L` and `L₀≤L`, saturating both `X` and `T` by
`L` reconstructs exactly `D`. -/
theorem baseSat_add_tailSat_eq_of_stabilizer_base_tail
    [Fintype A] (L₀ L : AddSubgroup A) (hL₀L : L₀ ≤ L)
    (X T : Finset A) (hX : X.Nonempty) (hT : T.Nonempty)
    (hstab : AddAction.stabilizer A
      ((((X + T) + dgmSubgroupFinset L₀ : Finset A)) : Set A) = L) :
    (X + dgmSubgroupFinset L) + (T + dgmSubgroupFinset L) =
      (X + T) + dgmSubgroupFinset L₀ := by
  classical
  let D := (X + T) + dgmSubgroupFinset L₀
  have hDne : D.Nonempty :=
    (hX.add hT).add
      ⟨0, (mem_dgmSubgroupFinset_iff L₀ 0).2 L₀.zero_mem⟩
  have hDadd : D.addStab = dgmSubgroupFinset L := by
    ext a
    rw [← Finset.mem_coe, Finset.coe_addStab hDne, hstab]
    exact (mem_dgmSubgroupFinset_iff L a).symm
  have hLL := dgmSubgroupFinset_add_eq_of_le L L le_rfl
  have hL₀Lfin := dgmSubgroupFinset_add_eq_of_le L₀ L hL₀L
  calc
    (X + dgmSubgroupFinset L) + (T + dgmSubgroupFinset L) =
        (X + T) + (dgmSubgroupFinset L + dgmSubgroupFinset L) := by
          ac_rfl
    _ = (X + T) + dgmSubgroupFinset L := by rw [hLL]
    _ = ((X + T) + dgmSubgroupFinset L₀) + dgmSubgroupFinset L := by
      symm
      calc
        ((X + T) + dgmSubgroupFinset L₀) + dgmSubgroupFinset L =
            (X + T) +
              (dgmSubgroupFinset L₀ + dgmSubgroupFinset L) := by ac_rfl
        _ = (X + T) + dgmSubgroupFinset L := by rw [hL₀Lfin]
    _ = D + D.addStab := by rw [hDadd]
    _ = D := Finset.add_addStab D
    _ = (X + T) + dgmSubgroupFinset L₀ := rfl

/-- Actual tail-saturation stabilizer: under the same hypotheses as the set
identity above, `stab(T+L)=L`.  The forward inclusion uses that a stabilizer
of the tail also stabilizes its sum with `X+L`; the reverse inclusion is the
literal `L`-periodicity of `T+L`. -/
theorem stabilizer_tail_saturation_eq_of_stabilizer_base_tail
    [Fintype A] (L₀ L : AddSubgroup A) (hL₀L : L₀ ≤ L)
    (X T : Finset A) (hX : X.Nonempty) (hT : T.Nonempty)
    (hstab : AddAction.stabilizer A
      ((((X + T) + dgmSubgroupFinset L₀ : Finset A)) : Set A) = L) :
    AddAction.stabilizer A
      ((T + dgmSubgroupFinset L : Finset A) : Set A) = L := by
  classical
  let Tsat := T + dgmSubgroupFinset L
  let Xsat := X + dgmSubgroupFinset L
  let D := (X + T) + dgmSubgroupFinset L₀
  have hTsat : Tsat.Nonempty := hT.add
    ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩
  have hXsat : Xsat.Nonempty := hX.add
    ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩
  have hDne : D.Nonempty := (hX.add hT).add
    ⟨0, (mem_dgmSubgroupFinset_iff L₀ 0).2 L₀.zero_mem⟩
  have hsum : Xsat + Tsat = D := by
    simpa [Xsat, Tsat, D] using
      baseSat_add_tailSat_eq_of_stabilizer_base_tail
        L₀ L hL₀L X T hX hT hstab
  ext a
  constructor
  · intro ha
    have haFin : a ∈ Tsat.addStab := by
      rw [← Finset.mem_coe, Finset.coe_addStab hTsat]
      exact ha
    have haSum : a ∈ (Xsat + Tsat).addStab :=
      Finset.subset_addStab_add_right hXsat haFin
    have haDfin : a ∈ D.addStab := by
      simpa [hsum] using haSum
    have haD : a ∈ AddAction.stabilizer A (D : Set A) := by
      rw [← Finset.mem_coe, Finset.coe_addStab hDne] at haDfin
      exact haDfin
    rw [show AddAction.stabilizer A (D : Set A) = L by simpa [D] using hstab] at haD
    exact haD
  · intro ha
    have haFin : a ∈ dgmSubgroupFinset L :=
      (mem_dgmSubgroupFinset_iff L a).2 ha
    have hsub : dgmSubgroupFinset L ⊆ Tsat.addStab := by
      have hraw := addStab_subset_addStab_add_addStab
        (dgmSubgroupFinset L) T
        ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩ hT
      rw [addStab_dgmSubgroupFinset_eq L] at hraw
      simpa [Tsat, add_comm] using hraw
    have haTail : a ∈ Tsat.addStab := hsub haFin
    rw [← Finset.mem_coe, Finset.coe_addStab hTsat] at haTail
    exact haTail

/-- Saturating a layer by `L ≤ H` does not change which `H`-cosets it meets.
Consequently the tail pattern itself needs no alteration in the smaller
instance. -/
theorem quotientLayer_add_dgmSubgroupFinset_eq_of_le
    [Fintype A] (L H : AddSubgroup A) (hLH : L ≤ H) (B : Finset A) :
    quotientLayer H (B + dgmSubgroupFinset L) = quotientLayer H B := by
  classical
  ext q
  constructor
  · intro hq
    obtain ⟨y, hy, hyq⟩ := (mem_quotientLayer_iff H _ q).1 hq
    obtain ⟨x, hxB, l, hlL, rfl⟩ := Finset.mem_add.mp hy
    apply (mem_quotientLayer_iff H B q).2
    refine ⟨x, hxB, ?_⟩
    rw [← hyq]
    change (x : A ⧸ H) = (x : A ⧸ H) + (l : A ⧸ H)
    rw [(QuotientAddGroup.eq_zero_iff l).2
      (hLH ((mem_dgmSubgroupFinset_iff L l).1 hlL)), add_zero]
  · intro hq
    obtain ⟨x, hxB, hxq⟩ := (mem_quotientLayer_iff H B q).1 hq
    apply (mem_quotientLayer_iff H _ q).2
    refine ⟨x + 0, Finset.mem_add.mpr
      ⟨x, hxB, 0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem, rfl⟩, ?_⟩
    simpa using hxq

/-- Layerwise `L`-saturation preserves every raw `H`-coset incidence count
when `L ≤ H`. -/
theorem quotientLayerMultiplicity_dgmSaturateLayers_eq_of_le
    [Fintype A] (L H : AddSubgroup A) (hLH : L ≤ H)
    (P : List (Finset A)) (q : A ⧸ H) :
    quotientLayerMultiplicity H (dgmSaturateLayers L P) q =
      quotientLayerMultiplicity H P q := by
  classical
  induction P with
  | nil => simp [dgmSaturateLayers, quotientLayerMultiplicity]
  | cons B P ih =>
      have hlayer := quotientLayer_add_dgmSubgroupFinset_eq_of_le L H hLH B
      by_cases hq : q ∈ quotientLayer H B
      · have hq' : q ∈ quotientLayer H (B + dgmSubgroupFinset L) := by
          rwa [hlayer]
        change quotientLayerMultiplicity H
          ((B + dgmSubgroupFinset L) :: dgmSaturateLayers L P) q = _
        rw [
          quotientLayerMultiplicity_cons_of_mem H
            (B + dgmSubgroupFinset L) (dgmSaturateLayers L P) q hq',
          quotientLayerMultiplicity_cons_of_mem H B P q hq, ih]
      · have hq' : q ∉ quotientLayer H (B + dgmSubgroupFinset L) := by
          rwa [hlayer]
        change quotientLayerMultiplicity H
          ((B + dgmSubgroupFinset L) :: dgmSaturateLayers L P) q = _
        rw [
          quotientLayerMultiplicity_cons_of_not_mem H
            (B + dgmSubgroupFinset L) (dgmSaturateLayers L P) q hq',
          quotientLayerMultiplicity_cons_of_not_mem H B P q hq, ih]

/-- Every proof-relevant choice lifts to layerwise saturation without changing
its sum or any quotient multiplicity (choose the zero element of `L` in every
selected layer). -/
theorem exists_layerSubsumChoice_dgmSaturateLayers_same
    [Fintype A] (L H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) :
    ∃ h' : LayerSubsumChoice (dgmSaturateLayers L P) n y,
      ∀ q : A ⧸ H,
        h'.quotientMultiplicity H q = h.quotientMultiplicity H q := by
  classical
  induction h with
  | zero P =>
      exact ⟨LayerSubsumChoice.zero (dgmSaturateLayers L P), fun _ ↦ rfl⟩
  | @skip B P n y h ih =>
      obtain ⟨h', h'mult⟩ := ih
      change ∃ hout : LayerSubsumChoice
          ((B + dgmSubgroupFinset L) :: dgmSaturateLayers L P) n y,
        ∀ q : A ⧸ H, hout.quotientMultiplicity H q =
          (LayerSubsumChoice.skip h).quotientMultiplicity H q
      exact ⟨LayerSubsumChoice.skip h', h'mult⟩
  | @take B P n b y hb h ih =>
      obtain ⟨h', h'mult⟩ := ih
      have hb' : b + 0 ∈ B + dgmSubgroupFinset L :=
        Finset.mem_add.mpr
          ⟨b, hb, 0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem, rfl⟩
      let hraw := LayerSubsumChoice.take hb' h'
      have heq : (b + 0) + y = b + y := by simp
      let hout := heq ▸ hraw
      change ∃ hout : LayerSubsumChoice
          ((B + dgmSubgroupFinset L) :: dgmSaturateLayers L P)
            (n + 1) (b + y),
        ∀ q : A ⧸ H, hout.quotientMultiplicity H q =
          (LayerSubsumChoice.take hb h).quotientMultiplicity H q
      refine ⟨hout, ?_⟩
      intro q
      rw [show hout = heq ▸ hraw by rfl,
        LayerSubsumChoice.quotientMultiplicity_cast]
      change (if ((b + 0 : A) : A ⧸ H) = q then 1 else 0) +
          h'.quotientMultiplicity H q =
        (if (b : A ⧸ H) = q then 1 else 0) +
          h.quotientMultiplicity H q
      simpa [h'mult q]

/-- If the exact choice is nonempty, one prescribed `l ∈ L` may be absorbed
into its first selected saturated layer.  Under `L ≤ H` this changes the sum
from `y` to `y+l` while preserving the entire `H`-pattern. -/
theorem exists_layerSubsumChoice_dgmSaturateLayers_add
    [Fintype A] (L H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    (hLH : L ≤ H)
    {P : List (Finset A)} {n : ℕ} {y l : A}
    (h : LayerSubsumChoice P n y) (hn : 0 < n) (hl : l ∈ L) :
    ∃ h' : LayerSubsumChoice (dgmSaturateLayers L P) n (y + l),
      ∀ q : A ⧸ H,
        h'.quotientMultiplicity H q = h.quotientMultiplicity H q := by
  classical
  induction h with
  | zero P => omega
  | @skip B P n y h ih =>
      obtain ⟨h', h'mult⟩ := ih hn
      change ∃ hout : LayerSubsumChoice
          ((B + dgmSubgroupFinset L) :: dgmSaturateLayers L P) n (y + l),
        ∀ q : A ⧸ H, hout.quotientMultiplicity H q =
          (LayerSubsumChoice.skip h).quotientMultiplicity H q
      exact ⟨LayerSubsumChoice.skip h', h'mult⟩
  | @take B P n b y hb h ih =>
      obtain ⟨htail, htailMult⟩ :=
        exists_layerSubsumChoice_dgmSaturateLayers_same L H h
      have hbl : b + l ∈ B + dgmSubgroupFinset L :=
        Finset.mem_add.mpr
          ⟨b, hb, l, (mem_dgmSubgroupFinset_iff L l).2 hl, rfl⟩
      let hraw := LayerSubsumChoice.take hbl htail
      have heq : (b + l) + y = (b + y) + l := by ac_rfl
      let hout := heq ▸ hraw
      change ∃ hout : LayerSubsumChoice
          ((B + dgmSubgroupFinset L) :: dgmSaturateLayers L P)
            (n + 1) ((b + y) + l),
        ∀ q : A ⧸ H, hout.quotientMultiplicity H q =
          (LayerSubsumChoice.take hb h).quotientMultiplicity H q
      refine ⟨hout, ?_⟩
      intro q
      rw [show hout = heq ▸ hraw by rfl,
        LayerSubsumChoice.quotientMultiplicity_cast]
      change (if ((b + l : A) : A ⧸ H) = q then 1 else 0) +
          htail.quotientMultiplicity H q =
        (if (b : A ⧸ H) = q then 1 else 0) +
          h.quotientMultiplicity H q
      have hlq : (l : A ⧸ H) = 0 :=
        (QuotientAddGroup.eq_zero_iff l).2 (hLH hl)
      rw [show ((b + l : A) : A ⧸ H) = (b : A ⧸ H) by
        change (b : A ⧸ H) + (l : A ⧸ H) = (b : A ⧸ H)
        rw [hlq, add_zero], htailMult q]

/-- Conversely, every choice from layerwise `L`-saturation splits into an
original choice plus one aggregate element of `L`; its `H`-pattern is
unchanged when `L ≤ H`. -/
theorem exists_layerSubsumChoice_of_dgmSaturateLayers
    [Fintype A] (L H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    (hLH : L ≤ H) {P : List (Finset A)} {n : ℕ} {z : A}
    (hsat : LayerSubsumChoice (dgmSaturateLayers L P) n z) :
    ∃ y l : A, l ∈ L ∧ z = y + l ∧
      ∃ h : LayerSubsumChoice P n y,
        ∀ q : A ⧸ H,
          h.quotientMultiplicity H q = hsat.quotientMultiplicity H q := by
  classical
  induction P generalizing n z with
  | nil =>
      change LayerSubsumChoice [] n z at hsat
      cases hsat with
      | zero =>
          refine ⟨0, 0, L.zero_mem, by simp,
            LayerSubsumChoice.zero [], ?_⟩
          intro q
          rfl
  | cons B P ih =>
      change LayerSubsumChoice
        ((B + dgmSubgroupFinset L) :: dgmSaturateLayers L P) n z at hsat
      cases hsat with
      | zero =>
          refine ⟨0, 0, L.zero_mem, by simp,
            LayerSubsumChoice.zero (B :: P), ?_⟩
          intro q
          rfl
      | @skip _ _ n y htail =>
          obtain ⟨y₀, l, hl, hy, h, hmult⟩ := ih htail
          refine ⟨y₀, l, hl, hy, LayerSubsumChoice.skip h, ?_⟩
          intro q
          exact hmult q
      | @take _ _ n x y hx htail =>
          obtain ⟨b, hb, l₁, hl₁, rfl⟩ := Finset.mem_add.mp hx
          obtain ⟨y₀, l₂, hl₂, hy, h, hmult⟩ := ih htail
          subst y
          refine ⟨b + y₀, l₁ + l₂,
            L.add_mem ((mem_dgmSubgroupFinset_iff L l₁).1 hl₁) hl₂,
            by ac_rfl, LayerSubsumChoice.take hb h, ?_⟩
          intro q
          simp only [LayerSubsumChoice.quotientMultiplicity]
          rw [hmult q]
          have hl₁q : (l₁ : A ⧸ H) = 0 :=
            (QuotientAddGroup.eq_zero_iff l₁).2
              (hLH ((mem_dgmSubgroupFinset_iff L l₁).1 hl₁))
          rw [show (((b + l₁ : A)) : A ⧸ H) = (b : A ⧸ H) by
            change (b : A ⧸ H) + (l₁ : A ⧸ H) = (b : A ⧸ H)
            rw [hl₁q, add_zero]]

/-- For a positive-weight pattern, saturating every layer by `L ≤ H`
commutes exactly with the pattern spectrum: all inserted subgroup terms
aggregate to one final `L`-summand, and conversely that summand can be
absorbed into the first selected layer. -/
theorem patternSubsumSpectrum_dgmSaturateLayers_eq_add
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (P : List (Finset A)) {n : ℕ} (μ : QuotientPattern H n)
    (hn : 0 < n) :
    patternSubsumSpectrum (dgmSaturateLayers L P) μ =
      patternSubsumSpectrum P μ + dgmSubgroupFinset L := by
  classical
  ext z
  constructor
  · intro hz
    obtain ⟨⟨hsat, hsatPattern⟩⟩ :=
      (mem_patternSubsumSpectrum_iff _ μ z).1 hz
    obtain ⟨y, l, hl, hzy, h, hmult⟩ :=
      exists_layerSubsumChoice_of_dgmSaturateLayers L H hLH hsat
    have hPattern : h.RealizesPattern μ := by
      intro q
      rw [hmult q, hsatPattern q]
    have hy : y ∈ patternSubsumSpectrum P μ :=
      (mem_patternSubsumSpectrum_iff _ μ y).2 ⟨⟨h, hPattern⟩⟩
    exact Finset.mem_add.mpr
      ⟨y, hy, l, (mem_dgmSubgroupFinset_iff L l).2 hl, hzy.symm⟩
  · intro hz
    obtain ⟨y, hy, l, hl, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨⟨h, hPattern⟩⟩ :=
      (mem_patternSubsumSpectrum_iff _ μ y).1 hy
    obtain ⟨hsat, hsatMult⟩ :=
      exists_layerSubsumChoice_dgmSaturateLayers_add L H hLH h hn
        ((mem_dgmSubgroupFinset_iff L l).1 hl)
    have hsatPattern : hsat.RealizesPattern μ := by
      intro q
      rw [hsatMult q, hPattern q]
    exact (mem_patternSubsumSpectrum_iff _ μ _).2
      ⟨⟨hsat, hsatPattern⟩⟩

/-- The corresponding Xi/capped-incidence transport for the tail call. -/
theorem dgmCappedMultiplicitySum_dgmSaturateLayers_eq_of_le
    [Fintype A] (L H : AddSubgroup A) [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (P : List (Finset A)) (n : ℕ) :
    dgmCappedMultiplicitySum H (dgmSaturateLayers L P) n =
      dgmCappedMultiplicitySum H P n := by
  classical
  unfold dgmCappedMultiplicitySum
  apply Finset.sum_congr rfl
  intro q _
  rw [quotientLayerMultiplicity_dgmSaturateLayers_eq_of_le L H hLH P q]

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

theorem weighted_dgmXiTwoGain_add_missing_le_of_exceptional
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (b : A)
    (hex : DGMXiExceptionalCoset H B C P k b) :
    Nat.card L * dgmXiTwoGain L B C P k +
        (dgmMissingPairCoset H L B C b).card ≤
      Nat.card H * dgmXiTwoGain H B C P k := by
  classical
  let d := (dgmMissingPairCoset H L B C b).card
  let fine : A ⧸ H → ℕ := fun r ↦ Nat.card L *
    (∑ q ∈ dgmQuotientRefinementFiber L H hLH r,
      dgmXiLocalTwoGain L B C P k q)
  let coarse : A ⧸ H → ℕ := fun r ↦
    Nat.card H * dgmXiLocalTwoGain H B C P k r
  let bonus : A ⧸ H → ℕ := fun r ↦
    if (b : A ⧸ H) = r then d else 0
  have hpoint : ∀ r : A ⧸ H, fine r + bonus r ≤ coarse r := by
    intro r
    by_cases hr : (b : A ⧸ H) = r
    · subst r
      have hexact := weighted_sum_localGain_add_missing_eq_of_exceptional
        L H hLH B C P k b hex
      simpa [fine, coarse, bonus, d] using hexact.le
    · have hord : fine r ≤ coarse r := by
        induction r using QuotientAddGroup.induction_on with
        | _ a =>
          exact weighted_sum_localGain_refinementFiber_le
            L H hLH B C P k a
      simpa [bonus, hr] using hord
  have hsum : (∑ r : A ⧸ H, (fine r + bonus r)) ≤
      ∑ r : A ⧸ H, coarse r :=
    Finset.sum_le_sum fun r _ ↦ hpoint r
  have hbonus : (∑ r : A ⧸ H, bonus r) = d := by simp [bonus]
  rw [Finset.sum_add_distrib, hbonus] at hsum
  rw [dgmXiTwoGain_eq_sum_localGain, dgmXiTwoGain_eq_sum_localGain,
    sum_localGain_eq_sum_refinementFibers L H hLH B C P k,
    Finset.mul_sum, Finset.mul_sum]
  simpa [fine, coarse, d] using hsum

theorem weighted_dgmXiTwoGain_add_missingUnion_le_of_quotient_eq
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (k : ℕ) (b₁ b₂ : A)
    (hsame : (b₁ : A ⧸ H) = (b₂ : A ⧸ H))
    (hex₁ : DGMXiExceptionalCoset H B C P k b₁) :
    Nat.card L * dgmXiTwoGain L B C P k +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card ≤
      Nat.card H * dgmXiTwoGain H B C P k := by
  rw [dgmMissingPairCoset_union_eq_of_quotient_eq H L B C hsame]
  exact weighted_dgmXiTwoGain_add_missing_le_of_exceptional
    L H hLH B C P k b₁ hex₁

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

/-- The weighted strict-Xi claim in the exact crossed setup, with no
exceptionality hypotheses left to supply: infeasibility of the transformed
pattern and feasibility of its tail produce both exceptional cosets by the
proof-relevant unused-layer exchange above. -/
theorem weighted_dgmXiTwoGain_add_missingUnion_le_of_twoStep_infeasible
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) {k : ℕ}
    (ν : QuotientPattern H (k + 2)) {b₁ b₂ : A}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H)) :
    Nat.card L * dgmXiTwoGain L B C P k +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card ≤
      Nat.card H * dgmXiTwoGain H B C P k := by
  exact weighted_dgmXiTwoGain_add_missingUnion_le
    L H hLH B C P k b₁ b₂ hne
      (dgmXiExceptionalCoset_first_of_twoStep_infeasible
        B C P ν hb₁ hb₂ νtail hext htail hinfeasible)
      (dgmXiExceptionalCoset_second_of_twoStep_infeasible
        B C P ν hb₁ hb₂ νtail hext htail hinfeasible)

theorem weighted_dgmXiTwoGain_add_missingUnion_le_of_twoStep_infeasible_unified
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)] (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) {k : ℕ}
    (ν : QuotientPattern H (k + 2)) {b₁ b₂ : A}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅) :
    Nat.card L * dgmXiTwoGain L B C P k +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card ≤
      Nat.card H * dgmXiTwoGain H B C P k := by
  by_cases hsame : (b₁ : A ⧸ H) = (b₂ : A ⧸ H)
  · exact weighted_dgmXiTwoGain_add_missingUnion_le_of_quotient_eq
      L H hLH B C P k b₁ b₂ hsame
        (dgmXiExceptionalCoset_first_of_twoStep_infeasible
          B C P ν hb₁ hb₂ νtail hext htail hinfeasible)
  · exact weighted_dgmXiTwoGain_add_missingUnion_le_of_twoStep_infeasible
      L H hLH B C P ν hb₁ hb₂ νtail hext htail hinfeasible hsame

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

/-- The target-stabilizer capped term is order-independent as well. -/
theorem stabilizerDgmCappedMultiplicitySum_eq_of_perm
    [Fintype A] (T : Finset A) {P Q : List (Finset A)}
    (hPQ : P.Perm Q) (n : ℕ) :
    stabilizerDgmCappedMultiplicitySum T P n =
      stabilizerDgmCappedMultiplicitySum T Q n := by
  rw [← dgmCappedMultiplicitySum_stabilizer_eq T P n,
    ← dgmCappedMultiplicitySum_stabilizer_eq T Q n]
  exact dgmCappedMultiplicitySum_eq_of_perm
    (AddAction.stabilizer A (T : Set A)) hPQ n

/-- Stabilizer-capped incidence also survives common-cell deletion. -/
theorem stabilizerDgmCappedMultiplicitySum_cons_eq_tail_of_head_subset_all
    [Fintype A] (T : Finset A) (B : Finset A)
    (P : List (Finset A)) (n : ℕ)
    (hall : ∀ C ∈ P, B ⊆ C) (hlt : n < (B :: P).length) :
    stabilizerDgmCappedMultiplicitySum T (B :: P) n =
      stabilizerDgmCappedMultiplicitySum T P n := by
  rw [← dgmCappedMultiplicitySum_stabilizer_eq T (B :: P) n,
    ← dgmCappedMultiplicitySum_stabilizer_eq T P n]
  exact dgmCappedMultiplicitySum_cons_eq_tail_of_head_subset_all
    (AddAction.stabilizer A (T : Set A)) B P n hall hlt

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

/-- The generalized DGM conclusion is invariant under permutation of the
labelled layers. -/
theorem dgmPatternBound_iff_of_perm
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    {P Q : List (Finset A)} (hPQ : P.Perm Q)
    (μ : QuotientPattern K n) :
    DGMPatternBound P μ ↔ DGMPatternBound Q μ := by
  unfold DGMPatternBound
  rw [patternSubsumSpectrum_eq_of_perm hPQ μ]
  simp only
  rw [stabilizerDgmCappedMultiplicitySum_eq_of_perm
      (patternSubsumSpectrum Q μ) hPQ n,
    dgmCappedMultiplicitySum_eq_of_perm K hPQ n]

/-- Fully quantified generalized pattern theorem used by the faithful
minimal-counterexample proof. -/
def GeneralDGMPatternTheorem
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] : Prop :=
  ∀ (K : AddSubgroup A) (n : ℕ)
    (_ : Fintype (A ⧸ K)) (_ : DecidableEq (A ⧸ K))
    (P : List (Finset A)) (μ : QuotientPattern K n),
    (patternSubsumSpectrum P μ).Nonempty → DGMPatternBound P μ

/-- The generalized theorem restricted to all instances at one inner
minimal-counterexample measure.  This is the codomain of the well-founded
strong induction, allowing the subgroup and pattern weight to change. -/
def DGMPatternAtMeasure [Fintype A]
    (M : DGMPatternInnerMeasure) : Prop :=
  ∀ (K : AddSubgroup A) (n : ℕ)
    (_ : Fintype (A ⧸ K)) (_ : DecidableEq (A ⧸ K))
    (P : List (Finset A)) (μ : QuotientPattern K n),
    dgmPatternInnerMeasure P μ = M →
    (patternSubsumSpectrum P μ).Nonempty → DGMPatternBound P μ

theorem dgmPatternInnerMeasure_lt_of_patternSpectrum_card_lt
    [Fintype A]
    {K₁ K₂ : AddSubgroup A} {n₁ n₂ : ℕ}
    [Fintype (A ⧸ K₁)] [DecidableEq (A ⧸ K₁)]
    [Fintype (A ⧸ K₂)] [DecidableEq (A ⧸ K₂)]
    (P₁ : List (Finset A)) (μ₁ : QuotientPattern K₁ n₁)
    (P₂ : List (Finset A)) (μ₂ : QuotientPattern K₂ n₂)
    (hcard : (patternSubsumSpectrum P₁ μ₁).card <
      (patternSubsumSpectrum P₂ μ₂).card) :
    DGMPatternInnerLt (dgmPatternInnerMeasure P₁ μ₁)
      (dgmPatternInnerMeasure P₂ μ₂) := by
  exact Prod.Lex.left _ _ hcard

/-- The saturated tail is genuinely smaller in the first measure coordinate.
The tail pattern lies in one `H`-coset, that coset is no larger than a
nonempty `H`-periodic convergent `C`, and an escaping sum makes `C` a proper
subset of the original pattern spectrum. -/
theorem dgmSaturatedTail_measure_lt_of_escape
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (P : List (Finset A)) {k : ℕ} (νtail : QuotientPattern H k)
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K n)
    (C : Finset A) (hC : C.Nonempty)
    (hCsub : C ⊆ patternSubsumSpectrum Q μ)
    (hCstab : AddAction.stabilizer A (C : Set A) = H)
    {y : A} (hy : y ∈ patternSubsumSpectrum Q μ)
    (hescape : ¬dgmCosetFiber H y ⊆ patternSubsumSpectrum Q μ)
    (hSat : (patternSubsumSpectrum
      (dgmSaturateLayers L P) νtail).Nonempty) :
    DGMPatternInnerLt
      (dgmPatternInnerMeasure (dgmSaturateLayers L P) νtail)
      (dgmPatternInnerMeasure Q μ) := by
  have hyC : y ∉ C := by
    intro hyC
    apply hescape
    exact (dgmCosetFiber_subset_of_mem_of_stabilizer_eq
      C hC H hCstab hyC).trans hCsub
  have hClt : C.card < (patternSubsumSpectrum Q μ).card := by
    apply Finset.card_lt_card
    refine ⟨hCsub, ?_⟩
    intro hback
    exact hyC (hback hy)
  obtain ⟨c, hc⟩ := hC
  have hHleC : Nat.card H ≤ C.card := by
    have hcoset := Finset.card_le_card
      (dgmCosetFiber_subset_of_mem_of_stabilizer_eq C ⟨c, hc⟩ H hCstab hc)
    simpa [card_dgmCosetFiber] using hcoset
  have hSatLeH :
      (patternSubsumSpectrum (dgmSaturateLayers L P) νtail).card ≤
        Nat.card H :=
    patternSubsumSpectrum_card_le_natCard_patternGroup
      H (dgmSaturateLayers L P) νtail hSat
  apply dgmPatternInnerMeasure_lt_of_patternSpectrum_card_lt
  exact hSatLeH.trans_lt (hHleC.trans_lt hClt)

/-- Exact inductive tail call used in equation (2).  Once the genuinely
smaller saturated-tail instance satisfies the generalized pattern bound and
its spectrum stabilizer is identified as `L`, the result transports back to
the unsaturated tail Xi terms at both `L` and `H`. -/
theorem dgmTailPatternBound_of_saturatedPatternBound
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [Fintype (A ⧸ H)]
    [DecidableEq (A ⧸ L)] [DecidableEq (A ⧸ H)]
    (hLH : L ≤ H) (P : List (Finset A)) {n : ℕ}
    (μ : QuotientPattern H n) (hn : 0 < n)
    (hbound : DGMPatternBound (dgmSaturateLayers L P) μ)
    (hstab : AddAction.stabilizer A
      (patternSubsumSpectrum (dgmSaturateLayers L P) μ : Set A) = L) :
    Nat.card L * (dgmCappedMultiplicitySum L P n - n + 1) ≤
      (patternSubsumSpectrum P μ + dgmSubgroupFinset L).card +
        Nat.card H * (dgmCappedMultiplicitySum H P n - n) := by
  classical
  let Tsat := patternSubsumSpectrum (dgmSaturateLayers L P) μ
  have hcapStab : stabilizerDgmCappedMultiplicitySum Tsat
      (dgmSaturateLayers L P) n =
      dgmCappedMultiplicitySum L (dgmSaturateLayers L P) n := by
    rw [← dgmCappedMultiplicitySum_stabilizer_eq Tsat
      (dgmSaturateLayers L P) n]
    simpa [Tsat] using congrArg
      (fun J : AddSubgroup A ↦
        dgmCappedMultiplicitySum J (dgmSaturateLayers L P) n) hstab
  have hb := hbound
  unfold DGMPatternBound at hb
  dsimp only at hb
  change Nat.card (AddAction.stabilizer A (Tsat : Set A)) *
      (stabilizerDgmCappedMultiplicitySum Tsat
        (dgmSaturateLayers L P) n - n + 1) ≤
    Tsat.card + Nat.card H *
      (dgmCappedMultiplicitySum H (dgmSaturateLayers L P) n - n) at hb
  rw [hstab, hcapStab,
    dgmCappedMultiplicitySum_dgmSaturateLayers_eq_of_le L L le_rfl P n,
    dgmCappedMultiplicitySum_dgmSaturateLayers_eq_of_le L H hLH P n,
    show Tsat = patternSubsumSpectrum P μ + dgmSubgroupFinset L by
      simpa [Tsat] using
        patternSubsumSpectrum_dgmSaturateLayers_eq_add L H hLH P μ hn] at hb
  exact hb

/-- Claim 1 from the actual well-founded strong induction.  The saturated
tail instance is proved strictly smaller by the escape chain, its stabilizer
is derived (not assumed) from the crossed base-tail sum, and the smaller
instance theorem is then transported back to the original tail Xi terms. -/
theorem dgmClaimOne_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    (L₀ L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (hL₀L : L₀ ≤ L) (hLH : L ≤ H)
    (P : List (Finset A)) {k : ℕ} (νtail : QuotientPattern H k)
    (hk : 0 < k)
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K n)
    (hmeasure : dgmPatternInnerMeasure Q μ = M)
    (C : Finset A) (hC : C.Nonempty)
    (hCsub : C ⊆ patternSubsumSpectrum Q μ)
    (hCstab : AddAction.stabilizer A (C : Set A) = H)
    {y : A} (hy : y ∈ patternSubsumSpectrum Q μ)
    (hescape : ¬dgmCosetFiber H y ⊆ patternSubsumSpectrum Q μ)
    (hTail : (patternSubsumSpectrum P νtail).Nonempty)
    (X : Finset A) (hX : X.Nonempty)
    (hDstab : AddAction.stabilizer A
      ((((X + patternSubsumSpectrum P νtail) +
        dgmSubgroupFinset L₀ : Finset A)) : Set A) = L) :
    Nat.card L * (dgmCappedMultiplicitySum L P k - k + 1) ≤
      (patternSubsumSpectrum P νtail + dgmSubgroupFinset L).card +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
  classical
  let Psat := dgmSaturateLayers L P
  let Ssat := patternSubsumSpectrum Psat νtail
  have hSatEq : Ssat = patternSubsumSpectrum P νtail +
      dgmSubgroupFinset L := by
    simpa [Psat, Ssat] using
      patternSubsumSpectrum_dgmSaturateLayers_eq_add L H hLH P νtail hk
  have hSat : Ssat.Nonempty := by
    rw [hSatEq]
    exact hTail.add
      ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩
  have hlt := dgmSaturatedTail_measure_lt_of_escape
    L H P νtail Q μ C hC hCsub hCstab hy hescape (by simpa [Psat, Ssat] using hSat)
  have hltM : DGMPatternInnerLt (dgmPatternInnerMeasure Psat νtail) M := by
    rw [← hmeasure]
    simpa [Psat] using hlt
  have hsmall := ih (dgmPatternInnerMeasure Psat νtail) hltM
  have hbound : DGMPatternBound Psat νtail :=
    hsmall H k inferInstance inferInstance Psat νtail rfl (by
      simpa [Ssat] using hSat)
  have hTailStab : AddAction.stabilizer A
      ((patternSubsumSpectrum P νtail + dgmSubgroupFinset L : Finset A) : Set A) = L :=
    stabilizer_tail_saturation_eq_of_stabilizer_base_tail
      L₀ L hL₀L X (patternSubsumSpectrum P νtail) hX hTail hDstab
  have hSatStab : AddAction.stabilizer A (Ssat : Set A) = L := by
    rw [hSatEq]
    exact hTailStab
  have hout := dgmTailPatternBound_of_saturatedPatternBound
    L H hLH P νtail hk hbound (by simpa [Psat, Ssat] using hSatStab)
  exact hout

/-- The separate `k=0` Claim 1 base.  No positive-weight saturation
transport is used: the tail pattern spectrum is exactly `{0}` and both Xi
corrections vanish. -/
theorem dgmClaimOne_zero
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (P : List (Finset A)) (νtail : QuotientPattern H 0) :
    Nat.card L * (dgmCappedMultiplicitySum L P 0 - 0 + 1) ≤
      (patternSubsumSpectrum P νtail + dgmSubgroupFinset L).card +
        Nat.card H * (dgmCappedMultiplicitySum H P 0 - 0) := by
  classical
  rw [patternSubsumSpectrum_zero_eq_singleton P νtail]
  simp [dgmCappedMultiplicitySum, card_dgmSubgroupFinset]

/-- Paper equation (3) in its source shape.  One Kneser step combines the
saturated crossed base with the saturated tail; Claim 1 supplies the tail
cardinality.  The strict/non-strict boundary is kept in additive form. -/
theorem dgmEquationThree_of_claimOne
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (B T D : Finset A) (hB : B.Nonempty) (hT : T.Nonempty)
    (hD : (B + dgmSubgroupFinset L) +
      (T + dgmSubgroupFinset L) = D)
    (hstab : AddAction.stabilizer A (D : Set A) = L)
    (P : List (Finset A)) (k : ℕ)
    (hclaim1 : Nat.card L *
        (dgmCappedMultiplicitySum L P k - k + 1) ≤
      (T + dgmSubgroupFinset L).card +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k)) :
    (B + dgmSubgroupFinset L).card +
        Nat.card L * (dgmCappedMultiplicitySum L P k - k) ≤
      D.card + Nat.card H *
        (dgmCappedMultiplicitySum H P k - k) := by
  classical
  let Bsat := B + dgmSubgroupFinset L
  let Tsat := T + dgmSubgroupFinset L
  have hBsat : Bsat.Nonempty := hB.add
    ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩
  have hTsat : Tsat.Nonempty := hT.add
    ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩
  have hDne : D.Nonempty := by
    rw [← hD]
    exact hBsat.add hTsat
  have hDadd : D.addStab = dgmSubgroupFinset L := by
    ext a
    rw [← Finset.mem_coe, Finset.coe_addStab hDne, hstab]
    exact (mem_dgmSubgroupFinset_iff L a).symm
  have hsat (S : Finset A) :
      (S + dgmSubgroupFinset L) + dgmSubgroupFinset L =
        S + dgmSubgroupFinset L := by
    calc
      (S + dgmSubgroupFinset L) + dgmSubgroupFinset L =
          S + (dgmSubgroupFinset L + dgmSubgroupFinset L) := by ac_rfl
      _ = S + dgmSubgroupFinset L := by
        rw [dgmSubgroupFinset_add_eq_of_le L L le_rfl]
  have hk := Finset.add_kneser Bsat Tsat
  have hk' : Bsat.card + Tsat.card ≤ D.card + Nat.card L := by
    rw [show Bsat + Tsat = D by simpa [Bsat, Tsat] using hD,
      hDadd, card_dgmSubgroupFinset] at hk
    simpa [Bsat, Tsat, hsat] using hk
  rw [Nat.mul_add, Nat.mul_one] at hclaim1
  dsimp only [Bsat, Tsat] at hk'
  omega

/-- Combined three-summand form of paper equation (3), after one additional
Kneser step for the two leading slices.  Iterated Kneser supplies the two
`|L|` losses, while the genuine smaller-instance Claim 1 tail bound supplies
the third summand. -/
theorem dgmEquationThree_threeSummand
    [Fintype A] (L : AddSubgroup A) (S₁ S₂ T : Finset A)
    (hS₁ : S₁.Nonempty) (hS₂ : S₂.Nonempty) (hT : T.Nonempty)
    (hstab : (iteratedFinsetSum [S₁, S₂, T]).addStab =
      dgmSubgroupFinset L)
    (a correction : ℕ)
    (htail : Nat.card L * a ≤
      (T + dgmSubgroupFinset L).card + correction) :
    (S₁ + dgmSubgroupFinset L).card +
        (S₂ + dgmSubgroupFinset L).card + Nat.card L * a ≤
      (iteratedFinsetSum [S₁, S₂, T]).card +
        2 * Nat.card L + correction := by
  have hnonempty : ∀ S ∈ [S₁, S₂, T], S.Nonempty := by
    intro S hS
    have hcases : S = S₁ ∨ S = S₂ ∨ S = T := by
      simpa using hS
    rcases hcases with rfl | rfl | rfl
    · exact hS₁
    · exact hS₂
    · exact hT
  have hk := sum_card_addStab_add_card_addStab_le
    [S₁, S₂, T] hnonempty
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
    List.length_cons, List.length_nil] at hk
  rw [hstab, card_dgmSubgroupFinset] at hk
  omega

/-- The crossed strict-`Ξ` estimate before any divisibility rounding.  This
is the literal strict numerical gate supplied by the convergent inequality,
paper equation (3), and the unified exceptional-fiber estimate.  Keeping the
missing union in the conclusion is what rules out both a common coarse coset
and an empty crossed second component. -/
theorem dgmCrossedStrictSlicesMissing_lt_of_threeSummand
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (hLH : L ≤ H) (B C : Finset A) (P : List (Finset A)) {k : ℕ}
    (ν : QuotientPattern H (k + 2)) {b₁ b₂ : A}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅)
    (hP : IsNonemptySetPartition P)
    (hFeasible : (layerSubsumSpectrum
      (dgmInterUnionLayers B C P) (k + 2)).Nonempty)
    (S₁ S₂ D : Finset A)
    (hstrict : D.card + Nat.card H *
        (dgmCappedMultiplicitySum H
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1) <
      Nat.card L *
        (dgmCappedMultiplicitySum L
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1))
    (hthree :
      (S₁ + dgmSubgroupFinset L).card +
          (S₂ + dgmSubgroupFinset L).card + Nat.card L *
            (dgmCappedMultiplicitySum L P k - k + 1) ≤
        D.card + 2 * Nat.card L + Nat.card H *
          (dgmCappedMultiplicitySum H P k - k)) :
    (S₁ + dgmSubgroupFinset L).card +
        (S₂ + dgmSubgroupFinset L).card +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card < Nat.card H := by
  have hklen : k ≤ P.length :=
    patternSubsumSpectrum_nonempty_weight_le_length P νtail htail
  have hkTL := le_dgmCappedMultiplicitySum L P hP k hklen
  have hkTH := le_dgmCappedMultiplicitySum H P hP k hklen
  have hweightL :=
    le_dgmCappedMultiplicitySum_of_layerSubsumSpectrum_nonempty L
      (dgmInterUnionLayers B C P) (k + 2) hFeasible
  have hweightH :=
    le_dgmCappedMultiplicitySum_of_layerSubsumSpectrum_nonempty H
      (dgmInterUnionLayers B C P) (k + 2) hFeasible
  have hTLAL := dgmCappedMultiplicitySum_tail_le_inter_union
    L B C P k
  have hTHAH := dgmCappedMultiplicitySum_tail_le_inter_union
    H B C P k
  have hxi :=
    weighted_dgmXiTwoGain_add_missingUnion_le_of_twoStep_infeasible_unified
      L H hLH B C P ν hb₁ hb₂ νtail hext htail hinfeasible
  apply dgmStrictXiArithmetic_threeSummand
    (Nat.card L) (Nat.card H)
    ((S₁ + dgmSubgroupFinset L).card +
      (S₂ + dgmSubgroupFinset L).card)
    D.card
    ((dgmMissingPairCoset H L B C b₁ ∪
      dgmMissingPairCoset H L B C b₂).card)
    (dgmCappedMultiplicitySum L (dgmInterUnionLayers B C P) (k + 2))
    (dgmCappedMultiplicitySum L P k)
    (dgmCappedMultiplicitySum H (dgmInterUnionLayers B C P) (k + 2))
    (dgmCappedMultiplicitySum H P k) k hkTL hkTH hweightL hweightH
      hTLAL hTHAH hstrict hthree
  simpa [dgmXiTwoGain] using hxi

/-- The strict pre-rounding estimate cannot hold when the two exceptional
representatives lie in the same coarse `H`-coset: in that case the one
missing set together with the two displayed saturated slices covers a full
`H`-coset. -/
theorem dgmStrictSlicesMissing_false_of_quotient_eq
    [Fintype A] (H L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (b₁ b₂ : A)
    (hsame : (b₁ : A ⧸ H) = (b₂ : A ⧸ H))
    (hstrict :
      (dgmSingleSliceSaturation H L B b₁).card +
          (dgmSingleSliceSaturation H L C b₂).card +
          (dgmMissingPairCoset H L B C b₁ ∪
            dgmMissingPairCoset H L B C b₂).card < Nat.card H) :
    False := by
  have hC : dgmSingleSliceSaturation H L C b₁ =
      dgmSingleSliceSaturation H L C b₂ := by
    unfold dgmSingleSliceSaturation
    rw [dgmCosetSlice_eq_of_quotient_eq H C hsame]
  have hpair :
      (dgmPairSliceSaturation H L B C b₁).card ≤
        (dgmSingleSliceSaturation H L B b₁).card +
          (dgmSingleSliceSaturation H L C b₂).card := by
    rw [dgmPairSliceSaturation_eq_union, hC]
    exact Finset.card_union_le _ _
  have hfull := card_missing_add_pairSaturation H L hLH B C b₁
  rw [dgmMissingPairCoset_union_eq_of_quotient_eq
    H L B C hsame] at hstrict
  omega

/-- If the crossed second pair-tail is empty, one of its two crossed slices
is empty (the tail itself is nonempty).  The corresponding missing set and
the remaining displayed slice then cover a full `H`-coset, contradicting the
strict pre-rounding estimate. -/
theorem dgmStrictSlicesMissing_false_of_pairTail2_eq_empty
    [Fintype A] {H : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hempty : dgmCrossedPairTail2 B C P b₁ b₂ νtail = ∅)
    (hstrict :
      (dgmSingleSliceSaturation H L B b₁).card +
          (dgmSingleSliceSaturation H L C b₂).card +
          (dgmMissingPairCoset H L B C b₁ ∪
            dgmMissingPairCoset H L B C b₂).card < Nat.card H) :
    False := by
  have hemptySlices : dgmCosetSlice H B b₂ = ∅ ∨
      dgmCosetSlice H C b₁ = ∅ := by
    by_contra h
    push Not at h
    have hB : (dgmCosetSlice H B b₂).Nonempty := h.1
    have hC : (dgmCosetSlice H C b₁).Nonempty := h.2
    have hpair :
        (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty :=
      (hB.add hC).add htail
    rw [hempty] at hpair
    simpa using hpair
  rcases hemptySlices with hB | hC
  · have hpair : dgmPairSliceSaturation H L B C b₂ =
        dgmSingleSliceSaturation H L C b₂ := by
      rw [dgmPairSliceSaturation_eq_union]
      simp [dgmSingleSliceSaturation, hB]
    have hfull := card_missing_add_pairSaturation H L hLH B C b₂
    rw [hpair] at hfull
    have hmissing : (dgmMissingPairCoset H L B C b₂).card ≤
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card :=
      Finset.card_le_card Finset.subset_union_right
    omega
  · have hpair : dgmPairSliceSaturation H L B C b₁ =
        dgmSingleSliceSaturation H L B b₁ := by
      rw [dgmPairSliceSaturation_eq_union]
      simp [dgmSingleSliceSaturation, hC]
    have hfull := card_missing_add_pairSaturation H L hLH B C b₁
    rw [hpair] at hfull
    have hmissing : (dgmMissingPairCoset H L B C b₁).card ≤
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card :=
      Finset.card_le_card Finset.subset_union_left
    omega

/-- The two structural gates required after strict equation (3): the crossed
second component is genuinely nonempty, and the two exceptional coarse
cosets are distinct. -/
theorem dgmCrossedNumericGates_of_strictSlicesMissing
    [Fintype A] {H : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (L : AddSubgroup A) (hLH : L ≤ H)
    (B C : Finset A) (P : List (Finset A)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hstrict :
      (dgmSingleSliceSaturation H L B b₁).card +
          (dgmSingleSliceSaturation H L C b₂).card +
          (dgmMissingPairCoset H L B C b₁ ∪
            dgmMissingPairCoset H L B C b₂).card < Nat.card H) :
    (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty ∧
      (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H) := by
  constructor
  · by_contra hpair
    have hempty : dgmCrossedPairTail2 B C P b₁ b₂ νtail = ∅ :=
      Finset.not_nonempty_iff_eq_empty.1 hpair
    exact dgmStrictSlicesMissing_false_of_pairTail2_eq_empty
      L hLH B C P b₁ b₂ νtail htail hempty hstrict
  · intro hsame
    exact dgmStrictSlicesMissing_false_of_quotient_eq
      H L hLH B C b₁ b₂ hsame hstrict

/-- Concrete paper equation (4) assembler.  Pattern feasibility supplies
all cap lower bounds, the exceptional-coset theorem supplies the weighted
Xi inequality, and literal saturations supply every divisibility premise.
Only the strict convergent inequality and the already-derived three-summand
lower bound remain as mathematical inputs. -/
theorem dgmCrossedEquationFour_of_threeSummand
    [Fintype A] (L H : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (hLH : L ≤ H) (B C : Finset A) (P : List (Finset A)) {k : ℕ}
    (ν : QuotientPattern H (k + 2)) {b₁ b₂ : A}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅)
    (hP : IsNonemptySetPartition P)
    (hFeasible : (layerSubsumSpectrum
      (dgmInterUnionLayers B C P) (k + 2)).Nonempty)
    (S₁ S₂ D : Finset A)
    (hstrict : D.card + Nat.card H *
        (dgmCappedMultiplicitySum H
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1) <
      Nat.card L *
        (dgmCappedMultiplicitySum L
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1))
    (hthree :
      (S₁ + dgmSubgroupFinset L).card +
          (S₂ + dgmSubgroupFinset L).card + Nat.card L *
            (dgmCappedMultiplicitySum L P k - k + 1) ≤
        D.card + 2 * Nat.card L + Nat.card H *
          (dgmCappedMultiplicitySum H P k - k)) :
    (S₁ + dgmSubgroupFinset L).card +
        (S₂ + dgmSubgroupFinset L).card + Nat.card L ≤ Nat.card H := by
  have hklen : k ≤ P.length :=
    patternSubsumSpectrum_nonempty_weight_le_length P νtail htail
  have hkTL := le_dgmCappedMultiplicitySum L P hP k hklen
  have hkTH := le_dgmCappedMultiplicitySum H P hP k hklen
  have hweightL :=
    le_dgmCappedMultiplicitySum_of_layerSubsumSpectrum_nonempty L
      (dgmInterUnionLayers B C P) (k + 2) hFeasible
  have hweightH :=
    le_dgmCappedMultiplicitySum_of_layerSubsumSpectrum_nonempty H
      (dgmInterUnionLayers B C P) (k + 2) hFeasible
  have hTLAL := dgmCappedMultiplicitySum_tail_le_inter_union
    L B C P k
  have hTHAH := dgmCappedMultiplicitySum_tail_le_inter_union
    H B C P k
  have hxi :=
    weighted_dgmXiTwoGain_add_missingUnion_le_of_twoStep_infeasible_unified
      L H hLH B C P ν hb₁ hb₂ νtail hext htail hinfeasible
  have hlB : Nat.card L ∣
      (S₁ + dgmSubgroupFinset L).card +
        (S₂ + dgmSubgroupFinset L).card :=
    Nat.dvd_add (natCard_dvd_card_add_dgmSubgroupFinset L S₁)
      (natCard_dvd_card_add_dgmSubgroupFinset L S₂)
  have hlH : Nat.card L ∣ Nat.card H := AddSubgroup.card_dvd_of_le hLH
  apply dgmEquationFour_of_threeSummand
    (Nat.card L) (Nat.card H)
    ((S₁ + dgmSubgroupFinset L).card +
      (S₂ + dgmSubgroupFinset L).card)
    D.card
    ((dgmMissingPairCoset H L B C b₁ ∪
      dgmMissingPairCoset H L B C b₂).card)
    (dgmCappedMultiplicitySum L (dgmInterUnionLayers B C P) (k + 2))
    (dgmCappedMultiplicitySum L P k)
    (dgmCappedMultiplicitySum H (dgmInterUnionLayers B C P) (k + 2))
    (dgmCappedMultiplicitySum H P k) k Nat.card_pos hlB hlH
    hkTL hkTH hweightL hweightH hTLAL hTHAH hstrict hthree
  simpa [dgmXiTwoGain] using hxi

/-- Concrete paper equation (5) assembler for the common subgroup `L=H₁₂`.
The leading term is the Kneser correction
`|S₁+L|+|S₂+L|-|Hᵢ|`; its cardinality and the common missing union are both
`|L|`-multiples, so strictness rounds to the displayed non-strict bound. -/
theorem dgmCrossedEquationFive_of_threeSummand
    [Fintype A] (L H Hε : AddSubgroup A)
    [Fintype (A ⧸ L)] [DecidableEq (A ⧸ L)]
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (hLH : L ≤ H) (hLHε : L ≤ Hε)
    (B C : Finset A) (P : List (Finset A)) {k : ℕ}
    (ν : QuotientPattern H (k + 2)) {b₁ b₂ : A}
    (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅)
    (hne : (b₁ : A ⧸ H) ≠ (b₂ : A ⧸ H))
    (hP : IsNonemptySetPartition P)
    (hFeasible : (layerSubsumSpectrum
      (dgmInterUnionLayers B C P) (k + 2)).Nonempty)
    (S₁ S₂ D : Finset A)
    (hstrict : D.card + Nat.card H *
        (dgmCappedMultiplicitySum H
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1) <
      Nat.card L *
        (dgmCappedMultiplicitySum L
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1))
    (hthree :
      ((S₁ + dgmSubgroupFinset L).card +
          (S₂ + dgmSubgroupFinset L).card - Nat.card Hε) +
            Nat.card L * (dgmCappedMultiplicitySum L P k - k + 1) ≤
        D.card + 2 * Nat.card L + Nat.card H *
          (dgmCappedMultiplicitySum H P k - k)) :
    ((S₁ + dgmSubgroupFinset L).card +
          (S₂ + dgmSubgroupFinset L).card) - Nat.card Hε +
        Nat.card L +
        (dgmMissingPairCoset H L B C b₁ ∪
          dgmMissingPairCoset H L B C b₂).card ≤ Nat.card H := by
  have hklen : k ≤ P.length :=
    patternSubsumSpectrum_nonempty_weight_le_length P νtail htail
  have hkTL := le_dgmCappedMultiplicitySum L P hP k hklen
  have hkTH := le_dgmCappedMultiplicitySum H P hP k hklen
  have hweightL :=
    le_dgmCappedMultiplicitySum_of_layerSubsumSpectrum_nonempty L
      (dgmInterUnionLayers B C P) (k + 2) hFeasible
  have hweightH :=
    le_dgmCappedMultiplicitySum_of_layerSubsumSpectrum_nonempty H
      (dgmInterUnionLayers B C P) (k + 2) hFeasible
  have hTLAL := dgmCappedMultiplicitySum_tail_le_inter_union L B C P k
  have hTHAH := dgmCappedMultiplicitySum_tail_le_inter_union H B C P k
  have hxi := weighted_dgmXiTwoGain_add_missingUnion_le_of_twoStep_infeasible
    L H hLH B C P ν hb₁ hb₂ νtail hext htail hinfeasible hne
  have hlSlices : Nat.card L ∣
      (S₁ + dgmSubgroupFinset L).card +
        (S₂ + dgmSubgroupFinset L).card :=
    Nat.dvd_add (natCard_dvd_card_add_dgmSubgroupFinset L S₁)
      (natCard_dvd_card_add_dgmSubgroupFinset L S₂)
  have hlB : Nat.card L ∣
      (S₁ + dgmSubgroupFinset L).card +
        (S₂ + dgmSubgroupFinset L).card - Nat.card Hε :=
    Nat.dvd_sub hlSlices (AddSubgroup.card_dvd_of_le hLHε)
  have hlM := natCard_dvd_card_dgmMissingPairCoset_union
    H L hLH B C b₁ b₂ hne
  have hlH : Nat.card L ∣ Nat.card H := AddSubgroup.card_dvd_of_le hLH
  apply dgmEquationFive_of_threeSummand
    (Nat.card L) (Nat.card H)
    ((S₁ + dgmSubgroupFinset L).card +
      (S₂ + dgmSubgroupFinset L).card - Nat.card Hε)
    D.card
    ((dgmMissingPairCoset H L B C b₁ ∪
      dgmMissingPairCoset H L B C b₂).card)
    (dgmCappedMultiplicitySum L (dgmInterUnionLayers B C P) (k + 2))
    (dgmCappedMultiplicitySum L P k)
    (dgmCappedMultiplicitySum H (dgmInterUnionLayers B C P) (k + 2))
    (dgmCappedMultiplicitySum H P k) k Nat.card_pos hlB hlM hlH
    hkTL hkTH hweightL hweightH hTLAL hTHAH hstrict hthree
  simpa [dgmXiTwoGain] using hxi

/-! ### Faithful convergents for the generalized minimal-counterexample proof -/

/-- The source paper's general-case convergent, in additive natural-number
form.  Its lower endpoint is the transformed intersection--union spectrum,
its upper endpoint is the original spectrum, and its correction term keeps
the original `K`-incidence count exactly as on page 9. -/
def DGMPatternConvergent
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) (D : Finset A) : Prop :=
  let P' := dgmInterUnionLayers B C P
  let T' := patternSubsumSpectrum P' μ
  let T := patternSubsumSpectrum (B :: C :: P) μ
  let H := AddAction.stabilizer A (D : Set A)
  D.Nonempty ∧ T' ⊆ D ∧ D ⊆ T ∧
    Nat.card H *
        (stabilizerDgmCappedMultiplicitySum D P' n - n + 1) ≤
      D.card + Nat.card K *
        (dgmCappedMultiplicitySum K (B :: C :: P) n - n)

/-- The stabilizer of a nonempty convergent is contained in the original
pattern subgroup.  Indeed, the convergent lies inside one quotient coset of
that subgroup.  This supplies the genuine refinement map `A/H → A/K` used
below; it is not an additional hypothesis on the crossed construction. -/
theorem dgmPatternConvergent_stabilizer_le_original
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) (D : Finset A)
    (hD : DGMPatternConvergent B C P μ D) :
    AddAction.stabilizer A (D : Set A) ≤ K := by
  unfold DGMPatternConvergent at hD
  dsimp only at hD
  rcases hD with ⟨hDne, _, hDupper, _⟩
  apply stabilizer_le_of_nonempty_subset_quotientFiber
    K D hDne μ.quotientSum
  intro x hx
  exact patternSubsumSpectrum_quotient_eq _ μ (hDupper hx)

/-- In an aperiodic pattern target, a convergent with nontrivial stabilizer
supplies an actual target choice whose stabilizer coset escapes the target.
The proof-relevant choice is retained so that its quotient pattern can be
used for the crossed two-layer construction. -/
theorem exists_escape_patternChoice_of_nontrivial_convergent
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n)
    (hTargetStab :
      (patternSubsumSpectrum (B :: C :: P) μ).addStab = {0})
    (E : Finset A) (hE : DGMPatternConvergent B C P μ E)
    (hEnontrivial :
      AddAction.stabilizer A (E : Set A) ≠ ⊥) :
    ∃ (y : A) (base : LayerSubsumChoice (B :: C :: P) n y),
      base.RealizesPattern μ ∧
      ¬dgmCosetFiber (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ := by
  classical
  let T := patternSubsumSpectrum (B :: C :: P) μ
  let H := AddAction.stabilizer A (E : Set A)
  have hEdata := hE
  unfold DGMPatternConvergent at hEdata
  dsimp only at hEdata
  rcases hEdata with ⟨hEne, _, hEupper, _⟩
  have hTne : T.Nonempty := hEne.mono hEupper
  have haexists : ∃ a : A, a ∈ H ∧ a ≠ 0 := by
    by_contra h
    push Not at h
    apply hEnontrivial
    apply le_antisymm
    · intro a ha
      show a ∈ (⊥ : AddSubgroup A)
      simpa using h a ha
    · exact bot_le
  obtain ⟨a, haH, ha0⟩ := haexists
  have haT : a ∉ T.addStab := by
    rw [show T.addStab = {0} by simpa [T] using hTargetStab]
    simpa using ha0
  obtain ⟨y, hyT, hayT⟩ :=
    exists_mem_add_not_mem_of_not_mem_addStab T hTne a haT
  obtain ⟨⟨base, hbase⟩⟩ :=
    (mem_patternSubsumSpectrum_iff (B :: C :: P) μ y).1
      (by simpa [T] using hyT)
  refine ⟨y, base, hbase, ?_⟩
  intro hcoset
  apply hayT
  apply hcoset
  apply (mem_dgmCosetFiber_iff H y (a + y)).2
  change (a : A ⧸ H) + (y : A ⧸ H) = (y : A ⧸ H)
  rw [(QuotientAddGroup.eq_zero_iff a).2 haH, zero_add]

/-- The transformed pattern spectrum is the initial convergent whenever the
strictly smaller transformed instance satisfies Theorem 3.1. -/
theorem patternSubsumSpectrum_inter_union_isConvergent
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n)
    (hT' : (patternSubsumSpectrum
      (dgmInterUnionLayers B C P) μ).Nonempty)
    (hbound : DGMPatternBound (dgmInterUnionLayers B C P) μ) :
    DGMPatternConvergent B C P μ
      (patternSubsumSpectrum (dgmInterUnionLayers B C P) μ) := by
  let P' := dgmInterUnionLayers B C P
  let T' := patternSubsumSpectrum P' μ
  have hxi : dgmCappedMultiplicitySum K P' n ≤
      dgmCappedMultiplicitySum K (B :: C :: P) n := by
    simpa [P'] using dgmCappedMultiplicitySum_inter_union_le
      K B C P n
  have hcorr : Nat.card K * (dgmCappedMultiplicitySum K P' n - n) ≤
      Nat.card K *
        (dgmCappedMultiplicitySum K (B :: C :: P) n - n) := by
    apply Nat.mul_le_mul_left
    omega
  unfold DGMPatternBound at hbound
  dsimp only at hbound
  unfold DGMPatternConvergent
  dsimp only
  refine ⟨by simpa [T', P'] using hT', Finset.Subset.rfl,
    ?_, ?_⟩
  · simpa [P', dgmInterUnionLayers] using
      patternSubsumSpectrum_inter_union_subset B C P μ
  · have hbound' :
        Nat.card (AddAction.stabilizer A (T' : Set A)) *
            (stabilizerDgmCappedMultiplicitySum T' P' n - n + 1) ≤
          T'.card + Nat.card K * (dgmCappedMultiplicitySum K P' n - n) := by
      simpa [T', P'] using hbound
    exact hbound'.trans (Nat.add_le_add_left hcorr T'.card)

/-- A nonempty finite family of convergents contains one whose stabilizer has
minimum cardinality, exactly matching the source's choice of `C`. -/
theorem exists_dgmPatternConvergent_min_stabilizer_card
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) {D₀ : Finset A}
    (hD₀ : DGMPatternConvergent B C P μ D₀) :
    ∃ D : Finset A, DGMPatternConvergent B C P μ D ∧
      ∀ D' : Finset A, DGMPatternConvergent B C P μ D' →
        Nat.card (AddAction.stabilizer A (D : Set A)) ≤
          Nat.card (AddAction.stabilizer A (D' : Set A)) := by
  classical
  let convergents := (Finset.univ : Finset (Finset A)).filter
    fun D ↦ DGMPatternConvergent B C P μ D
  have hconvergents : convergents.Nonempty := by
    exact ⟨D₀, Finset.mem_filter.mpr ⟨Finset.mem_univ D₀, hD₀⟩⟩
  obtain ⟨D, hDmem, hmin⟩ := Finset.exists_min_image convergents
    (fun D ↦ Nat.card (AddAction.stabilizer A (D : Set A))) hconvergents
  refine ⟨D, (Finset.mem_filter.mp hDmem).2, ?_⟩
  intro D' hD'
  exact hmin D' (Finset.mem_filter.mpr ⟨Finset.mem_univ D', hD'⟩)

/-- A strict inclusion of additive subgroups of a finite ambient group is
also strict on cardinalities. -/
theorem natCard_lt_natCard_of_addSubgroup_lt
    [Fintype A] {L H : AddSubgroup A} (hLH : L < H) :
    Nat.card L < Nat.card H := by
  have hsets : (L : Set A) ⊂ (H : Set A) := hLH
  have hcard := Set.Finite.card_lt_card (Set.toFinite (H : Set A)) hsets
  simpa only [SetLike.coe_sort_coe] using hcard

/-- If an `H`-periodic set lies in a target which does not contain one full
`H`-coset, then that set is disjoint from the deficient coset.  This is the
source argument `R ∩ C = ∅`, with the whole coset rather than only the chosen
crossed subset retained. -/
theorem disjoint_cosetFiber_of_periodic_subset_of_not_subset
    [Fintype A] (C T : Finset A) (hC : C.Nonempty)
    (H : AddSubgroup A)
    (hCstab : AddAction.stabilizer A (C : Set A) = H)
    (hCT : C ⊆ T) (y : A)
    (hescape : ¬dgmCosetFiber H y ⊆ T) :
    Disjoint (C : Set A) (dgmCosetFiber H y : Set A) := by
  rw [Set.disjoint_left]
  intro x hxC hxy
  apply hescape
  intro z hzy
  apply hCT
  apply dgmCosetFiber_subset_of_mem_of_stabilizer_eq C hC H hCstab hxC
  apply (mem_dgmCosetFiber_iff H x z).2
  exact ((mem_dgmCosetFiber_iff H y z).1 hzy).trans
    ((mem_dgmCosetFiber_iff H y x).1 hxy).symm

/-- Let `C` be `H`-periodic and let `D` be a nonempty proper part of one
`H`-coset disjoint from `C`.  Then the sole partial coarse coset prevents a
translation outside `H` from stabilizing `C ∪ D`; consequently the union has
exactly the stabilizer of `D`.  This is the set-theoretic stabilizer identity
used for each of `C₁,C₂,C₁₂` in the source proof. -/
theorem stabilizer_union_eq_right_of_periodic_left_proper_fiber
    [Fintype A] (H : AddSubgroup A) (C D : Finset A)
    (hC : C.Nonempty) (hD : D.Nonempty)
    (hCstab : AddAction.stabilizer A (C : Set A) = H)
    (b : A)
    (hDfiber : ∀ x ∈ D, (x : A ⧸ H) = (b : A ⧸ H))
    (hdisj : Disjoint (C : Set A) (dgmCosetFiber H b : Set A))
    {y : A} (hyfiber : (y : A ⧸ H) = (b : A ⧸ H))
    (hyD : y ∉ D) :
    AddAction.stabilizer A ((C ∪ D : Finset A) : Set A) =
      AddAction.stabilizer A (D : Set A) := by
  have hDlt : AddAction.stabilizer A (D : Set A) < H :=
    stabilizer_lt_of_proper_quotientFiber H D hD (b : A ⧸ H)
      hDfiber hyfiber hyD
  have hCD : Disjoint (C : Set A) (D : Set A) := by
    rw [Set.disjoint_left] at hdisj ⊢
    intro x hxC hxD
    apply hdisj hxC
    exact (mem_dgmCosetFiber_iff H b x).2 (hDfiber x hxD)
  have hUnionNe : (C ∪ D).Nonempty := hC.mono Finset.subset_union_left
  have hUnionLe :
      AddAction.stabilizer A ((C ∪ D : Finset A) : Set A) ≤ H := by
    intro a ha
    obtain ⟨x, hxD⟩ := hD
    have haFin : a ∈ (C ∪ D).addStab := by
      have haSet : a ∈
          (AddAction.stabilizer A ((C ∪ D : Finset A) : Set A) : Set A) := ha
      rw [← Finset.coe_addStab hUnionNe] at haSet
      exact haSet
    have htranslate := (Finset.mem_addStab hUnionNe).1 haFin
    have hax : a + x ∈ C ∪ D := by
      have : a + x ∈ a +ᵥ (C ∪ D) :=
        Finset.mem_vadd_finset.mpr
          ⟨x, Finset.mem_union_right C hxD, rfl⟩
      rwa [htranslate] at this
    rcases Finset.mem_union.mp hax with haxC | haxD
    · have haxFiber := dgmCosetFiber_subset_of_mem_of_stabilizer_eq
        C hC H hCstab haxC
      have hayFiber : a + y ∈ dgmCosetFiber H (a + x) := by
        apply (mem_dgmCosetFiber_iff H (a + x) (a + y)).2
        change (a : A ⧸ H) + (y : A ⧸ H) =
          (a : A ⧸ H) + (x : A ⧸ H)
        rw [hyfiber, hDfiber x hxD]
      have hayC : a + y ∈ C := haxFiber hayFiber
      have hayUnion : a + y ∈ C ∪ D := Finset.mem_union_left D hayC
      have hneg : -a ∈
          AddAction.stabilizer A ((C ∪ D : Finset A) : Set A) :=
        (AddAction.stabilizer A ((C ∪ D : Finset A) : Set A)).neg_mem ha
      have hnegFin : -a ∈ (C ∪ D).addStab := by
        have hnegSet : -a ∈
            (AddAction.stabilizer A ((C ∪ D : Finset A) : Set A) : Set A) :=
          hneg
        rw [← Finset.coe_addStab hUnionNe] at hnegSet
        exact hnegSet
      have htranslateNeg := (Finset.mem_addStab hUnionNe).1 hnegFin
      have hyUnion : y ∈ C ∪ D := by
        have : -a + (a + y) ∈ (-a) +ᵥ (C ∪ D) :=
          Finset.mem_vadd_finset.mpr ⟨a + y, hayUnion, rfl⟩
        rw [htranslateNeg] at this
        simpa using this
      rcases Finset.mem_union.mp hyUnion with hyC | hyD'
      · exact False.elim ((Set.disjoint_left.1 hdisj) hyC
          ((mem_dgmCosetFiber_iff H b y).2 hyfiber))
      · exact False.elim (hyD hyD')
    · have hquot : ((a + x : A) : A ⧸ H) = (x : A ⧸ H) :=
        (hDfiber (a + x) haxD).trans (hDfiber x hxD).symm
      have hsub := QuotientAddGroup.eq_iff_sub_mem.mp hquot
      simpa using hsub
  have hUnionLeC :
      AddAction.stabilizer A ((C ∪ D : Finset A) : Set A) ≤
        AddAction.stabilizer A (C : Set A) := by
    rw [hCstab]
    exact hUnionLe
  have hUnionLeSet :
      AddAction.stabilizer A ((C : Set A) ∪ (D : Set A)) ≤
        AddAction.stabilizer A (C : Set A) := by
    simpa only [Finset.coe_union] using hUnionLeC
  simpa only [Finset.coe_union] using
    AddAction.stabilizer_union_eq_right hCD
      (by simpa [hCstab] using hDlt.le) hUnionLeSet

/-- Minimality of the convergent stabilizer turns every proper one-coset
extension into the exact nonconvergence hypothesis needed by strict equation
(2).  No numerical conclusion is assumed: properness of the crossed piece
and the deficient ambient coset produce the smaller union stabilizer. -/
theorem dgmPatternConvergent_union_not_convergent_of_minimal
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B₀ C₀ : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) (C D : Finset A)
    (hCconv : DGMPatternConvergent B₀ C₀ P μ C)
    (hmin : ∀ C' : Finset A, DGMPatternConvergent B₀ C₀ P μ C' →
      Nat.card (AddAction.stabilizer A (C : Set A)) ≤
        Nat.card (AddAction.stabilizer A (C' : Set A)))
    (hD : D.Nonempty) (y : A)
    (hDfiber : ∀ x ∈ D,
      (x : A ⧸ AddAction.stabilizer A (C : Set A)) =
        (y : A ⧸ AddAction.stabilizer A (C : Set A)))
    (hyD : y ∉ D)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (C : Set A)) y ⊆
        patternSubsumSpectrum (B₀ :: C₀ :: P) μ) :
    ¬DGMPatternConvergent B₀ C₀ P μ (C ∪ D) := by
  let H := AddAction.stabilizer A (C : Set A)
  have hCdata := hCconv
  unfold DGMPatternConvergent at hCdata
  dsimp only at hCdata
  rcases hCdata with ⟨hCne, _, hCupper, _⟩
  have hdisj : Disjoint (C : Set A) (dgmCosetFiber H y : Set A) :=
    disjoint_cosetFiber_of_periodic_subset_of_not_subset
      C (patternSubsumSpectrum (B₀ :: C₀ :: P) μ) hCne H rfl
        hCupper y (by simpa [H] using hescape)
  have hUnionStab :
      AddAction.stabilizer A ((C ∪ D : Finset A) : Set A) =
        AddAction.stabilizer A (D : Set A) :=
    stabilizer_union_eq_right_of_periodic_left_proper_fiber
      H C D hCne hD rfl y (by simpa [H] using hDfiber) hdisj rfl hyD
  have hDlt : AddAction.stabilizer A (D : Set A) < H :=
    stabilizer_lt_of_proper_quotientFiber H D hD
      (y : A ⧸ H) (by simpa [H] using hDfiber) rfl hyD
  have hcardlt : Nat.card (AddAction.stabilizer A (D : Set A)) <
      Nat.card H := natCard_lt_natCard_of_addSubgroup_lt hDlt
  intro hUnionConv
  have hminimum := hmin (C ∪ D) hUnionConv
  rw [hUnionStab] at hminimum
  exact (not_le_of_gt (by simpa [H] using hcardlt)) hminimum

/-- Choose the actual minimum-stabilizer convergent and simultaneously
record its source-faithful behavior under every proper extension inside a
deficient stabilizer coset.  This is the reusable `C` selected on page 13,
not a provider carrying the desired crossed conclusion as a field. -/
theorem exists_dgmPatternConvergent_min_with_extension_hnot
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) {D₀ : Finset A}
    (hD₀ : DGMPatternConvergent B C P μ D₀) :
    ∃ E : Finset A,
      DGMPatternConvergent B C P μ E ∧
      (∀ E' : Finset A, DGMPatternConvergent B C P μ E' →
        Nat.card (AddAction.stabilizer A (E : Set A)) ≤
          Nat.card (AddAction.stabilizer A (E' : Set A))) ∧
      ∀ (D : Finset A) (y : A),
        D.Nonempty →
        (∀ x ∈ D,
          (x : A ⧸ AddAction.stabilizer A (E : Set A)) =
            (y : A ⧸ AddAction.stabilizer A (E : Set A))) →
        y ∉ D →
        (¬dgmCosetFiber (AddAction.stabilizer A (E : Set A)) y ⊆
          patternSubsumSpectrum (B :: C :: P) μ) →
        ¬DGMPatternConvergent B C P μ (E ∪ D) := by
  obtain ⟨E, hE, hmin⟩ :=
    exists_dgmPatternConvergent_min_stabilizer_card B C P μ hD₀
  refine ⟨E, hE, hmin, ?_⟩
  intro D y hD hDfiber hyD hescape
  exact dgmPatternConvergent_union_not_convergent_of_minimal
    B C P μ E D hE hmin hD y hDfiber hyD hescape

/-- Strict additive form of the paper's convergent inequality (equation (2)
in the strict-Xi chain).  A convergent `D`, together with a
disjoint extension `E` whose union satisfies the endpoint conditions but is
not convergent, gives a genuinely strict inequality.  This is the strictness
which must survive the later `(1)--(5)` chain. -/
theorem dgmEquationOne_of_convergent_union_not_convergent
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) (D E : Finset A)
    (hD : DGMPatternConvergent B C P μ D)
    (hDE : Disjoint D E)
    (hEupper : E ⊆ patternSubsumSpectrum (B :: C :: P) μ)
    (hnot : ¬DGMPatternConvergent B C P μ (D ∪ E)) :
    E.card +
        Nat.card (AddAction.stabilizer A (D : Set A)) *
          (stabilizerDgmCappedMultiplicitySum D
              (dgmInterUnionLayers B C P) n - n + 1) <
      Nat.card (AddAction.stabilizer A ((D ∪ E : Finset A) : Set A)) *
        (stabilizerDgmCappedMultiplicitySum (D ∪ E)
            (dgmInterUnionLayers B C P) n - n + 1) := by
  unfold DGMPatternConvergent at hD hnot
  dsimp only at hD hnot
  rcases hD with ⟨hDne, hDlower, hDupper, hDbound⟩
  have hUnionNe : (D ∪ E).Nonempty := hDne.mono (Finset.subset_union_left)
  have hUnionLower : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) μ ⊆ D ∪ E :=
    fun x hx ↦ Finset.mem_union_left E (hDlower hx)
  have hUnionUpper : D ∪ E ⊆
      patternSubsumSpectrum (B :: C :: P) μ := by
    intro x hx
    rcases Finset.mem_union.mp hx with hxD | hxE
    · exact hDupper hxD
    · exact hEupper hxE
  have hnotBound : ¬(
      Nat.card (AddAction.stabilizer A ((D ∪ E : Finset A) : Set A)) *
          (stabilizerDgmCappedMultiplicitySum (D ∪ E)
              (dgmInterUnionLayers B C P) n - n + 1) ≤
        (D ∪ E).card + Nat.card K *
          (dgmCappedMultiplicitySum K (B :: C :: P) n - n)) := by
    intro hbound
    exact hnot ⟨hUnionNe, hUnionLower, hUnionUpper, hbound⟩
  have hstrict :
      (D ∪ E).card + Nat.card K *
          (dgmCappedMultiplicitySum K (B :: C :: P) n - n) <
        Nat.card (AddAction.stabilizer A ((D ∪ E : Finset A) : Set A)) *
          (stabilizerDgmCappedMultiplicitySum (D ∪ E)
              (dgmInterUnionLayers B C P) n - n + 1) :=
    Nat.lt_of_not_ge hnotBound
  rw [Finset.card_union_of_disjoint hDE] at hstrict
  omega

alias dgmEquationTwo_of_convergent_union_not_convergent :=
  dgmEquationOne_of_convergent_union_not_convergent

/-- The transformed spectrum of the fine pattern induced by an escaping
source choice is empty.  Fine-to-coarse pattern transport puts it inside the
original transformed spectrum, convergence puts that spectrum inside `E`,
and `E` is disjoint from the deficient stabilizer coset.  This is the exact
gate used to invoke the crossed two-leading-layer decomposition. -/
theorem patternSubsumSpectrum_interUnion_quotientPattern_eq_empty_of_escape
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) n y)
    (hbase : base.RealizesPattern μ)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    patternSubsumSpectrum (dgmInterUnionLayers B C P)
      (base.quotientPattern (AddAction.stabilizer A (E : Set A))) = ∅ := by
  classical
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  let T := patternSubsumSpectrum (B :: C :: P) μ
  have hEdata := hE
  unfold DGMPatternConvergent at hEdata
  dsimp only at hEdata
  rcases hEdata with ⟨hEne, hElower, hEupper, _⟩
  have hHle : H ≤ K := by
    simpa [H] using dgmPatternConvergent_stabilizer_le_original
      B C P μ E hE
  have hfineUpper :
      patternSubsumSpectrum (dgmInterUnionLayers B C P) ν ⊆
        patternSubsumSpectrum (dgmInterUnionLayers B C P) μ := by
    simpa [ν] using
      (patternSubsumSpectrum_quotientPattern_subset_of_realizes_of_le
        H K hHle base μ hbase :
          patternSubsumSpectrum (dgmInterUnionLayers B C P)
              (base.quotientPattern H) ⊆
            patternSubsumSpectrum (dgmInterUnionLayers B C P) μ)
  have hyfine : y ∈ patternSubsumSpectrum (B :: C :: P) ν :=
    (mem_patternSubsumSpectrum_iff _ ν y).2
      ⟨⟨base, base.realizes_quotientPattern H⟩⟩
  have hdisj : Disjoint (E : Set A) (dgmCosetFiber H y : Set A) :=
    disjoint_cosetFiber_of_periodic_subset_of_not_subset
      E T hEne H rfl (by simpa [T] using hEupper) y
        (by simpa [H, T] using hescape)
  apply Finset.not_nonempty_iff_eq_empty.mp
  rintro ⟨x, hx⟩
  have hxE : x ∈ E := hElower (hfineUpper hx)
  have hxquot : (x : A ⧸ H) = (y : A ⧸ H) :=
    (patternSubsumSpectrum_quotient_eq _ ν hx).trans
      (patternSubsumSpectrum_quotient_eq _ ν hyfine).symm
  exact (Set.disjoint_left.1 hdisj) hxE
    ((mem_dgmCosetFiber_iff H y x).2 hxquot)

/-- The aperiodic/nontrivial convergent branch now reaches the paper's
actual initial crossed data without assuming a fine pattern or its
infeasibility.  Both are extracted from one retained source choice. -/
theorem exists_initialCrossedData_of_nontrivial_convergent
    [Fintype A] {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2))
    (hTargetStab :
      (patternSubsumSpectrum (B :: C :: P) μ).addStab = {0})
    (E : Finset A) (hE : DGMPatternConvergent B C P μ E)
    (hEnontrivial : AddAction.stabilizer A (E : Set A) ≠ ⊥) :
    ∃ (y : A) (base : LayerSubsumChoice (B :: C :: P) (k + 2) y),
      base.RealizesPattern μ ∧
      (¬dgmCosetFiber (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) ∧
      ∃ b₁ ∈ B, b₁ ∉ C ∧ ∃ b₂ ∈ C, b₂ ∉ B ∧
        ∃ νtail : QuotientPattern
            (AddAction.stabilizer A (E : Set A)) k,
          QuotientPattern.IsTwoStepExtension
              (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
              b₁ b₂ νtail ∧
          (patternSubsumSpectrum P νtail).Nonempty ∧
          (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty ∧
          (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty := by
  classical
  obtain ⟨y, base, hbase, hescape⟩ :=
    exists_escape_patternChoice_of_nontrivial_convergent
      B C P μ hTargetStab E hE hEnontrivial
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  have hνfeasible :
      (patternSubsumSpectrum (B :: C :: P) ν).Nonempty := by
    exact ⟨y, (mem_patternSubsumSpectrum_iff _ ν y).2
      ⟨⟨base, base.realizes_quotientPattern H⟩⟩⟩
  have hinfeasible :
      patternSubsumSpectrum (dgmInterUnionLayers B C P) ν = ∅ := by
    simpa [H, ν] using
      patternSubsumSpectrum_interUnion_quotientPattern_eq_empty_of_escape
        B C P μ E hE base hbase hescape
  obtain ⟨b₁, hb₁, hb₁C, b₂, hb₂, hb₂B, νtail,
      hext, htail, hD12, hpair1⟩ :=
    exists_initialCrossedData_of_interUnion_infeasible
      B C P ν hνfeasible hinfeasible
  exact ⟨y, base, hbase, hescape, b₁, hb₁, hb₁C,
    b₂, hb₂, hb₂B, νtail, hext, htail, hD12, hpair1⟩

/-- Source-faithful strict equation (2) for any nonempty piece of the fine
pattern spectrum in the deficient stabilizer coset.  The fine pattern is not
an arbitrary interface: it is canonically induced by the retained original
choice `base`, and the refinement theorem above proves that the piece still
lies in the original `μ`-target. -/
theorem dgmStrictEquationTwo_of_minimal_convergent_refined_piece
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmin : ∀ E' : Finset A, DGMPatternConvergent B C P μ E' →
      Nat.card (AddAction.stabilizer A (E : Set A)) ≤
        Nat.card (AddAction.stabilizer A (E' : Set A)))
    {y : A} (base : LayerSubsumChoice (B :: C :: P) n y)
    (hbase : base.RealizesPattern μ)
    (D : Finset A) (hD : D.Nonempty)
    (hDfine : D ⊆ patternSubsumSpectrum (B :: C :: P)
      (base.quotientPattern (AddAction.stabilizer A (E : Set A))))
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    D.card + Nat.card (AddAction.stabilizer A (E : Set A)) *
        (dgmCappedMultiplicitySum
          (AddAction.stabilizer A (E : Set A))
          (dgmInterUnionLayers B C P) n - n + 1) <
      Nat.card (AddAction.stabilizer A (D : Set A)) *
        (dgmCappedMultiplicitySum
          (AddAction.stabilizer A (D : Set A))
          (dgmInterUnionLayers B C P) n - n + 1) := by
  classical
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  let T := patternSubsumSpectrum (B :: C :: P) μ
  have hHle : H ≤ K := by
    simpa [H] using dgmPatternConvergent_stabilizer_le_original
      B C P μ E hE
  have hfineUpper : patternSubsumSpectrum (B :: C :: P) ν ⊆ T := by
    simpa [ν, T] using
      (patternSubsumSpectrum_quotientPattern_subset_of_realizes_of_le
        H K hHle base μ hbase :
          patternSubsumSpectrum (B :: C :: P) (base.quotientPattern H) ⊆
            patternSubsumSpectrum (B :: C :: P) μ)
  have hyfine : y ∈ patternSubsumSpectrum (B :: C :: P) ν := by
    exact (mem_patternSubsumSpectrum_iff _ ν y).2
      ⟨⟨base, base.realizes_quotientPattern H⟩⟩
  have hDfiber : ∀ x ∈ D, (x : A ⧸ H) = (y : A ⧸ H) := by
    intro x hx
    exact (patternSubsumSpectrum_quotient_eq _ ν (hDfine hx)).trans
      (patternSubsumSpectrum_quotient_eq _ ν hyfine).symm
  have hex : ∃ z : A, z ∈ dgmCosetFiber H y ∧ z ∉ T := by
    by_contra h
    apply hescape
    intro z hzfiber
    by_contra hzT
    exact h ⟨z, hzfiber, hzT⟩
  obtain ⟨z, hzfiber, hzT⟩ := hex
  have hzquot : (z : A ⧸ H) = (y : A ⧸ H) :=
    (mem_dgmCosetFiber_iff H y z).1 hzfiber
  have hDupper : D ⊆ T := fun x hx ↦ hfineUpper (hDfine hx)
  have hzD : z ∉ D := fun hz ↦ hzT (hDupper hz)
  have hnot : ¬DGMPatternConvergent B C P μ (E ∪ D) := by
    apply dgmPatternConvergent_union_not_convergent_of_minimal
      B C P μ E D hE hmin hD z
    · intro x hx
      exact (hDfiber x hx).trans hzquot.symm
    · exact hzD
    · simpa [H, T] using
        (show ¬dgmCosetFiber H z ⊆ T from by
          intro hzcoset
          apply hzT
          exact hzcoset (by
            apply (mem_dgmCosetFiber_iff H z z).2
            rfl))
  have hEdata := hE
  unfold DGMPatternConvergent at hEdata
  dsimp only at hEdata
  rcases hEdata with ⟨hEne, _, hEupper, _⟩
  have hdisjCoset : Disjoint (E : Set A) (dgmCosetFiber H y : Set A) :=
    disjoint_cosetFiber_of_periodic_subset_of_not_subset
      E T hEne H rfl (by simpa [T] using hEupper) y
        (by simpa [H, T] using
          (show ¬dgmCosetFiber H y ⊆ T from by
            intro hsub
            exact hzT (hsub hzfiber)))
  have hdisj : Disjoint E D := by
    rw [Finset.disjoint_left]
    intro x hxE hxD
    exact (Set.disjoint_left.1 hdisjCoset) hxE
      ((mem_dgmCosetFiber_iff H y x).2 (hDfiber x hxD))
  have hUnionStab :
      AddAction.stabilizer A ((E ∪ D : Finset A) : Set A) =
        AddAction.stabilizer A (D : Set A) := by
    apply stabilizer_union_eq_right_of_periodic_left_proper_fiber
      H E D hEne hD rfl y
    · intro x hx
      exact hDfiber x hx
    · exact hdisjCoset
    · exact hzquot
    · exact hzD
  have hstrict := dgmEquationOne_of_convergent_union_not_convergent
    B C P μ E D hE hdisj (by simpa [T] using hDupper) hnot
  rw [← dgmCappedMultiplicitySum_stabilizer_eq E
      (dgmInterUnionLayers B C P) n,
    ← dgmCappedMultiplicitySum_stabilizer_eq (E ∪ D)
      (dgmInterUnionLayers B C P) n,
    hUnionStab] at hstrict
  simpa [H] using hstrict

/-- The three crossed pieces `D₁,D₂,D₁₂` satisfy the paper's strict
equation (2).  All three inequalities are instances of the preceding
source-faithful lemma; the second crossed component is required only through
the nonemptiness already forced by the numeric gate. -/
theorem dgmCrossedStrictEquationTwo_three
    [Fintype A] {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmin : ∀ E' : Finset A, DGMPatternConvergent B C P μ E' →
      Nat.card (AddAction.stabilizer A (E : Set A)) ≤
        Nat.card (AddAction.stabilizer A (E' : Set A)))
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    (b₁ b₂ : A)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hpair2 : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    let H := AddAction.stabilizer A (E : Set A)
    let Q := dgmInterUnionLayers B C P
    let common := Nat.card H *
      (dgmCappedMultiplicitySum H Q (k + 2) - (k + 2) + 1)
    (dgmCrossedD1 B C P b₁ b₂ νtail).card + common <
        Nat.card (dgmCrossedH1 B C P b₁ b₂ νtail) *
          (dgmCappedMultiplicitySum
            (dgmCrossedH1 B C P b₁ b₂ νtail) Q (k + 2) -
              (k + 2) + 1) ∧
      (dgmCrossedD2 B C P b₁ b₂ νtail).card + common <
        Nat.card (dgmCrossedH2 B C P b₁ b₂ νtail) *
          (dgmCappedMultiplicitySum
            (dgmCrossedH2 B C P b₁ b₂ νtail) Q (k + 2) -
              (k + 2) + 1) ∧
      (dgmCrossedD12 B C P b₁ b₂ νtail).card + common <
        Nat.card (dgmCrossedH12 B C P b₁ b₂ νtail) *
          (dgmCappedMultiplicitySum
            (dgmCrossedH12 B C P b₁ b₂ νtail) Q (k + 2) -
              (k + 2) + 1) := by
  classical
  dsimp only
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  have hD12fine : dgmCrossedD12 B C P b₁ b₂ νtail ⊆
      patternSubsumSpectrum (B :: C :: P) ν := by
    intro x hx
    exact dgmCrossedD12_subset_patternSubsumSpectrum
      B C P ν b₁ b₂ νtail hext hx
  have hD1ne : (dgmCrossedD1 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD1]
    exact hpair1.add ⟨0, hD12.zero_mem_addStab⟩
  have hD2ne : (dgmCrossedD2 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD2]
    exact hpair2.add ⟨0, hD12.zero_mem_addStab⟩
  have hstrict1 :=
    dgmStrictEquationTwo_of_minimal_convergent_refined_piece
      B C P μ E hE hmin base hbase
      (dgmCrossedD1 B C P b₁ b₂ νtail) hD1ne
      (fun x hx ↦ hD12fine
        (dgmCrossedD1_subset_D12 B C P b₁ b₂ νtail hD12 hx))
      hescape
  have hstrict2 :=
    dgmStrictEquationTwo_of_minimal_convergent_refined_piece
      B C P μ E hE hmin base hbase
      (dgmCrossedD2 B C P b₁ b₂ νtail) hD2ne
      (fun x hx ↦ hD12fine
        (dgmCrossedD2_subset_D12 B C P b₁ b₂ νtail hD12 hx))
      hescape
  have hstrict12 :=
    dgmStrictEquationTwo_of_minimal_convergent_refined_piece
      B C P μ E hE hmin base hbase
      (dgmCrossedD12 B C P b₁ b₂ νtail) hD12 hD12fine hescape
  exact ⟨by simpa [H, ν, dgmCrossedH1] using hstrict1,
    by simpa [H, ν, dgmCrossedH2] using hstrict2,
    by simpa [H, ν, dgmCrossedH12] using hstrict12⟩

/-- All stabilizer inclusions needed by equations (3)--(5), derived from
the literal crossed sets.  In particular `Hᵢ ≤ H` is not assumed: each
`Dᵢ` lies in the single `H`-coset prescribed by the fine pattern. -/
theorem dgmCrossedStabilizerGeometry
    [Fintype A] {H : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (ν : QuotientPattern H (k + 2)) (b₁ b₂ : A)
    (νtail : QuotientPattern H k)
    (hext : ν.IsTwoStepExtension b₁ b₂ νtail)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hpair2 : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty) :
    dgmCrossedH12 B C P b₁ b₂ νtail ≤ H ∧
      dgmCrossedH1 B C P b₁ b₂ νtail ≤ H ∧
      dgmCrossedH2 B C P b₁ b₂ νtail ≤ H ∧
      dgmCrossedH12 B C P b₁ b₂ νtail ≤
        dgmCrossedH1 B C P b₁ b₂ νtail ∧
      dgmCrossedH12 B C P b₁ b₂ νtail ≤
        dgmCrossedH2 B C P b₁ b₂ νtail := by
  classical
  have hD12fiber : ∀ x ∈ dgmCrossedD12 B C P b₁ b₂ νtail,
      (x : A ⧸ H) = ν.quotientSum := by
    intro x hx
    exact patternSubsumSpectrum_quotient_eq _ ν
      (dgmCrossedD12_subset_patternSubsumSpectrum
        B C P ν b₁ b₂ νtail hext hx)
  have hD1ne : (dgmCrossedD1 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD1]
    exact hpair1.add ⟨0, hD12.zero_mem_addStab⟩
  have hD2ne : (dgmCrossedD2 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD2]
    exact hpair2.add ⟨0, hD12.zero_mem_addStab⟩
  have h12H : dgmCrossedH12 B C P b₁ b₂ νtail ≤ H := by
    simpa [dgmCrossedH12] using
      stabilizer_le_of_nonempty_subset_quotientFiber H
        (dgmCrossedD12 B C P b₁ b₂ νtail) hD12 ν.quotientSum hD12fiber
  have h1H : dgmCrossedH1 B C P b₁ b₂ νtail ≤ H := by
    simpa [dgmCrossedH1] using
      stabilizer_le_of_nonempty_subset_quotientFiber H
        (dgmCrossedD1 B C P b₁ b₂ νtail) hD1ne ν.quotientSum
        (fun x hx ↦ hD12fiber x
          (dgmCrossedD1_subset_D12 B C P b₁ b₂ νtail hD12 hx))
  have h2H : dgmCrossedH2 B C P b₁ b₂ νtail ≤ H := by
    simpa [dgmCrossedH2] using
      stabilizer_le_of_nonempty_subset_quotientFiber H
        (dgmCrossedD2 B C P b₁ b₂ νtail) hD2ne ν.quotientSum
        (fun x hx ↦ hD12fiber x
          (dgmCrossedD2_subset_D12 B C P b₁ b₂ νtail hD12 hx))
  have h121 : dgmCrossedH12 B C P b₁ b₂ νtail ≤
      dgmCrossedH1 B C P b₁ b₂ νtail := by
    simpa [dgmCrossedH1] using
      dgmCrossedH12_le_D1_stabilizer
        B C P b₁ b₂ νtail hD12 hpair1
  have h122 : dgmCrossedH12 B C P b₁ b₂ νtail ≤
      dgmCrossedH2 B C P b₁ b₂ νtail := by
    simpa [dgmCrossedH2] using
      dgmCrossedH12_le_D2_stabilizer
        B C P b₁ b₂ νtail hD12 hpair2
  exact ⟨h12H, h1H, h2H, h121, h122⟩

/-- Finite-carrier form of the definition of `H₁₂`, used in the literal
set identities for the crossed Claim 1 instances. -/
theorem dgmSubgroupFinset_dgmCrossedH12_eq_addStab
    [Fintype A] {H : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty) :
    dgmSubgroupFinset (dgmCrossedH12 B C P b₁ b₂ νtail) =
      (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
  ext x
  rw [mem_dgmSubgroupFinset_iff, ← Finset.mem_coe]
  change x ∈ (dgmCrossedH12 B C P b₁ b₂ νtail : Set A) ↔
    x ∈ ((dgmCrossedD12 B C P b₁ b₂ νtail).addStab : Set A)
  rw [coe_dgmCrossedH12_eq_addStab B C P b₁ b₂ νtail hD12]

/-- Equation (3)'s three-summand bound for a crossed set which was first
saturated by `L₀`.  Claim 1 is the only numerical input.  The identity
`L₀ + L = L` transports its tail term to the literal three summands, and
the actual stabilizer of `D` supplies the Kneser correction. -/
theorem dgmCrossedThreeSummand_of_claimOne
    [Fintype A] (L₀ L H : AddSubgroup A) (hL₀L : L₀ ≤ L)
    (S₁ S₂ T D : Finset A)
    (hS₁ : S₁.Nonempty) (hS₂ : S₂.Nonempty) (hT : T.Nonempty)
    (hD : iteratedFinsetSum
      [S₁, S₂, T + dgmSubgroupFinset L₀] = D)
    (hstab : AddAction.stabilizer A (D : Set A) = L)
    (a correction : ℕ)
    (hclaim1 : Nat.card L * a ≤
      (T + dgmSubgroupFinset L).card + correction) :
    (S₁ + dgmSubgroupFinset L).card +
        (S₂ + dgmSubgroupFinset L).card + Nat.card L * a ≤
      D.card + 2 * Nat.card L + correction := by
  classical
  let T₀ := T + dgmSubgroupFinset L₀
  have hT₀ : T₀.Nonempty := hT.add
    ⟨0, (mem_dgmSubgroupFinset_iff L₀ 0).2 L₀.zero_mem⟩
  have hDne : D.Nonempty := by
    rw [← hD]
    apply iteratedFinsetSum_nonempty
    intro S hS
    have hcases : S = S₁ ∨ S = S₂ ∨ S = T₀ := by
      simpa using hS
    rcases hcases with rfl | rfl | rfl
    · exact hS₁
    · exact hS₂
    · exact hT₀
  have hDadd : D.addStab = dgmSubgroupFinset L := by
    ext x
    rw [← Finset.mem_coe, Finset.coe_addStab hDne, hstab]
    exact (mem_dgmSubgroupFinset_iff L x).symm
  have hiterStab :
      (iteratedFinsetSum [S₁, S₂, T₀]).addStab =
        dgmSubgroupFinset L := by
    rw [show iteratedFinsetSum [S₁, S₂, T₀] = D by simpa [T₀] using hD]
    exact hDadd
  have hT₀sat : T₀ + dgmSubgroupFinset L =
      T + dgmSubgroupFinset L := by
    calc
      T₀ + dgmSubgroupFinset L =
          T + (dgmSubgroupFinset L₀ + dgmSubgroupFinset L) := by
        simp only [T₀]
        ac_rfl
      _ = T + dgmSubgroupFinset L := by
        rw [dgmSubgroupFinset_add_eq_of_le L₀ L hL₀L]
  have hclaim1' : Nat.card L * a ≤
      (T₀ + dgmSubgroupFinset L).card + correction := by
    rw [hT₀sat]
    exact hclaim1
  have hout := dgmEquationThree_threeSummand
    L S₁ S₂ T₀ hS₁ hS₂ hT₀ hiterStab a correction hclaim1'
  simpa [T₀, hD] using hout

/-- Kneser's two-summand inequality in the form needed for the leading
crossed pair.  If the stabilizer of the saturated pair-sum is contained in
`Hε`, subtracting `|Hε|` pays for the entire Kneser correction.  The
ambient set `U` is allowed to contain the pair-sum; in the crossed
application it is the union of the two possible leading pair-sums. -/
theorem dgmLeadingPairKneser_sub_card_of_stabilizer_le
    [Fintype A] (L Hε : AddSubgroup A)
    (S₁ S₂ U : Finset A) (hS₁ : S₁.Nonempty) (hS₂ : S₂.Nonempty)
    (hpair : S₁ + S₂ ⊆ U)
    (hstab : AddAction.stabilizer A
      ((((S₁ + dgmSubgroupFinset L) +
        (S₂ + dgmSubgroupFinset L) : Finset A)) : Set A) ≤ Hε) :
    (S₁ + dgmSubgroupFinset L).card +
          (S₂ + dgmSubgroupFinset L).card - Nat.card Hε ≤
      (U + dgmSubgroupFinset L).card := by
  classical
  let R₁ := S₁ + dgmSubgroupFinset L
  let R₂ := S₂ + dgmSubgroupFinset L
  let R := R₁ + R₂
  have hLne : (dgmSubgroupFinset L).Nonempty :=
    ⟨0, (mem_dgmSubgroupFinset_iff L 0).2 L.zero_mem⟩
  have hR₁ : R₁.Nonempty := hS₁.add hLne
  have hR₂ : R₂.Nonempty := hS₂.add hLne
  have hR : R.Nonempty := hR₁.add hR₂
  have hzero : 0 ∈ R.addStab := hR.zero_mem_addStab
  have hR₁sub : R₁ ⊆ R₁ + R.addStab := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hR₂sub : R₂ ⊆ R₂ + R.addStab := by
    intro x hx
    exact Finset.mem_add.mpr ⟨x, hx, 0, hzero, by simp⟩
  have hstabFin : R.addStab ⊆ dgmSubgroupFinset Hε := by
    intro a ha
    apply (mem_dgmSubgroupFinset_iff Hε a).2
    apply hstab
    have haSet : a ∈ (R.addStab : Set A) := ha
    rw [Finset.coe_addStab hR] at haSet
    simpa [R, R₁, R₂] using haSet
  have hKcard : R.addStab.card ≤ Nat.card Hε := by
    rw [← card_dgmSubgroupFinset Hε]
    exact Finset.card_le_card hstabFin
  have hk := Finset.add_kneser R₁ R₂
  have hpairCard : R₁.card + R₂.card ≤ R.card + Nat.card Hε := by
    have hleft : R₁.card + R₂.card ≤
        (R₁ + R.addStab).card + (R₂ + R.addStab).card :=
      Nat.add_le_add (Finset.card_le_card hR₁sub)
        (Finset.card_le_card hR₂sub)
    have hk' : (R₁ + R.addStab).card + (R₂ + R.addStab).card ≤
        R.card + R.addStab.card := by
      simpa [R] using hk
    omega
  have hRsub : R ⊆ U + dgmSubgroupFinset L := by
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
    obtain ⟨s₁, hs₁, l₁, hl₁, rfl⟩ := Finset.mem_add.mp hx
    obtain ⟨s₂, hs₂, l₂, hl₂, rfl⟩ := Finset.mem_add.mp hy
    apply Finset.mem_add.mpr
    refine ⟨s₁ + s₂, hpair (Finset.mem_add.mpr
      ⟨s₁, hs₁, s₂, hs₂, rfl⟩), l₁ + l₂, ?_, ?_⟩
    · exact (mem_dgmSubgroupFinset_iff L _).2
        (L.add_mem ((mem_dgmSubgroupFinset_iff L l₁).1 hl₁)
          ((mem_dgmSubgroupFinset_iff L l₂).1 hl₂))
    · ac_rfl
  have hRcard := Finset.card_le_card hRsub
  dsimp only [R₁, R₂] at hpairCard ⊢
  omega

/-- The genuine leading-pair Kneser estimate for both crossed branches.
The correction subgroup `Hε` is not supplied abstractly: it is the actual
stabilizer of `Dε`.  The two branches are then compared with their common
union base, and a second Kneser step uses the actual stabilizer `H₁₂` of
`D₁₂`. -/
theorem dgmCrossedLeadingPairTail_bounds
    [Fintype A] {H : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ H)] [DecidableEq (A ⧸ H)]
    (B C : Finset A) (P : List (Finset A))
    (b₁ b₂ : A) (νtail : QuotientPattern H k)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hpair2 : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty) :
    let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
    let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
    let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
    let T := patternSubsumSpectrum P νtail
    let U := dgmCrossedPairBase H B C b₁ b₂
    let S11 := dgmCosetSlice H B b₁
    let S12 := dgmCosetSlice H C b₂
    let S21 := dgmCosetSlice H B b₂
    let S22 := dgmCosetSlice H C b₁
    ((S11 + dgmSubgroupFinset H12).card +
          (S12 + dgmSubgroupFinset H12).card - Nat.card H1) +
          (T + dgmSubgroupFinset H12).card ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + Nat.card H12 ∧
      ((S21 + dgmSubgroupFinset H12).card +
          (S22 + dgmSubgroupFinset H12).card - Nat.card H2) +
          (T + dgmSubgroupFinset H12).card ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + Nat.card H12 := by
  classical
  dsimp only
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
  let T := patternSubsumSpectrum P νtail
  let U := dgmCrossedPairBase H B C b₁ b₂
  let S11 := dgmCosetSlice H B b₁
  let S12 := dgmCosetSlice H C b₂
  let S21 := dgmCosetSlice H B b₂
  let S22 := dgmCosetSlice H C b₁
  have hS11 : S11.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨u, by simpa [S11, dgmCrossedPairTail1] using hu⟩
  have hS12 : S12.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨v, by simpa [S12, dgmCrossedPairTail1] using hv⟩
  have hS21 : S21.Nonempty := by
    obtain ⟨z, hz⟩ := hpair2
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨u, by simpa [S21, dgmCrossedPairTail2] using hu⟩
  have hS22 : S22.Nonempty := by
    obtain ⟨z, hz⟩ := hpair2
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨v, by simpa [S22, dgmCrossedPairTail2] using hv⟩
  have hUtail :
      (U + dgmSubgroupFinset H12).card +
          (T + dgmSubgroupFinset H12).card ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + Nat.card H12 := by
    have hH12fin :
        (dgmCrossedD12 B C P b₁ b₂ νtail).addStab =
          dgmSubgroupFinset H12 := by
      symm
      simpa [H12] using dgmSubgroupFinset_dgmCrossedH12_eq_addStab
        B C P b₁ b₂ νtail hD12
    have hk := Finset.add_kneser U T
    have hsum : U + T = dgmCrossedD12 B C P b₁ b₂ νtail := by
      rfl
    rw [hsum, hH12fin, card_dgmSubgroupFinset] at hk
    simpa [U, T] using hk
  have hstab1 : AddAction.stabilizer A
      ((((S11 + dgmSubgroupFinset H12) +
        (S12 + dgmSubgroupFinset H12) : Finset A)) : Set A) ≤ H1 := by
    let R := (S11 + dgmSubgroupFinset H12) +
      (S12 + dgmSubgroupFinset H12)
    have hR : R.Nonempty :=
      (hS11.add ⟨0, (mem_dgmSubgroupFinset_iff H12 0).2 H12.zero_mem⟩).add
        (hS12.add ⟨0, (mem_dgmSubgroupFinset_iff H12 0).2 H12.zero_mem⟩)
    have hD1ne : (dgmCrossedD1 B C P b₁ b₂ νtail).Nonempty := by
      rw [dgmCrossedD1]
      exact hpair1.add ⟨0, hD12.zero_mem_addStab⟩
    intro a ha
    have haFin : a ∈ R.addStab := by
      have haSet : a ∈ (AddAction.stabilizer A (R : Set A) : Set A) := by
        simpa [R] using ha
      rw [← Finset.coe_addStab hR] at haSet
      exact haSet
    have haSum : a ∈ (T + R).addStab :=
      Finset.subset_addStab_add_right htail haFin
    have hTR : T + R = dgmCrossedD1 B C P b₁ b₂ νtail := by
      rw [dgmCrossedD1]
      have hH12fin := dgmSubgroupFinset_dgmCrossedH12_eq_addStab
        B C P b₁ b₂ νtail hD12
      rw [← hH12fin]
      calc
        T + R = dgmCrossedPairTail1 B C P b₁ b₂ νtail +
            (dgmSubgroupFinset H12 + dgmSubgroupFinset H12) := by
          simp only [R, T, S11, S12, dgmCrossedPairTail1]
          ac_rfl
        _ = dgmCrossedPairTail1 B C P b₁ b₂ νtail +
            dgmSubgroupFinset H12 := by
          rw [dgmSubgroupFinset_add_eq_of_le H12 H12 le_rfl]
    rw [hTR] at haSum
    have haSet : a ∈
        (AddAction.stabilizer A
          (dgmCrossedD1 B C P b₁ b₂ νtail : Set A) : Set A) := by
      rw [← Finset.coe_addStab hD1ne]
      exact haSum
    exact haSet
  have hstab2 : AddAction.stabilizer A
      ((((S21 + dgmSubgroupFinset H12) +
        (S22 + dgmSubgroupFinset H12) : Finset A)) : Set A) ≤ H2 := by
    let R := (S21 + dgmSubgroupFinset H12) +
      (S22 + dgmSubgroupFinset H12)
    have hR : R.Nonempty :=
      (hS21.add ⟨0, (mem_dgmSubgroupFinset_iff H12 0).2 H12.zero_mem⟩).add
        (hS22.add ⟨0, (mem_dgmSubgroupFinset_iff H12 0).2 H12.zero_mem⟩)
    have hD2ne : (dgmCrossedD2 B C P b₁ b₂ νtail).Nonempty := by
      rw [dgmCrossedD2]
      exact hpair2.add ⟨0, hD12.zero_mem_addStab⟩
    intro a ha
    have haFin : a ∈ R.addStab := by
      have haSet : a ∈ (AddAction.stabilizer A (R : Set A) : Set A) := by
        simpa [R] using ha
      rw [← Finset.coe_addStab hR] at haSet
      exact haSet
    have haSum : a ∈ (T + R).addStab :=
      Finset.subset_addStab_add_right htail haFin
    have hTR : T + R = dgmCrossedD2 B C P b₁ b₂ νtail := by
      rw [dgmCrossedD2]
      have hH12fin := dgmSubgroupFinset_dgmCrossedH12_eq_addStab
        B C P b₁ b₂ νtail hD12
      rw [← hH12fin]
      calc
        T + R = dgmCrossedPairTail2 B C P b₁ b₂ νtail +
            (dgmSubgroupFinset H12 + dgmSubgroupFinset H12) := by
          simp only [R, T, S21, S22, dgmCrossedPairTail2]
          ac_rfl
        _ = dgmCrossedPairTail2 B C P b₁ b₂ νtail +
            dgmSubgroupFinset H12 := by
          rw [dgmSubgroupFinset_add_eq_of_le H12 H12 le_rfl]
    rw [hTR] at haSum
    have haSet : a ∈
        (AddAction.stabilizer A
          (dgmCrossedD2 B C P b₁ b₂ νtail : Set A) : Set A) := by
      rw [← Finset.coe_addStab hD2ne]
      exact haSum
    exact haSet
  have hlead1 := dgmLeadingPairKneser_sub_card_of_stabilizer_le
    H12 H1 S11 S12 U hS11 hS12
      (fun x hx ↦ Finset.mem_union_left _ hx) hstab1
  have hlead2 := dgmLeadingPairKneser_sub_card_of_stabilizer_le
    H12 H2 S21 S22 U hS21 hS22
      (fun x hx ↦ Finset.mem_union_right _ hx) hstab2
  have hout1 :
      ((S11 + dgmSubgroupFinset H12).card +
          (S12 + dgmSubgroupFinset H12).card - Nat.card H1) +
          (T + dgmSubgroupFinset H12).card ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + Nat.card H12 := by
    omega
  have hout2 :
      ((S21 + dgmSubgroupFinset H12).card +
          (S22 + dgmSubgroupFinset H12).card - Nat.card H2) +
          (T + dgmSubgroupFinset H12).card ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + Nat.card H12 := by
    omega
  exact ⟨by simpa [H12, H1, T, S11, S12] using hout1,
    by simpa [H12, H2, T, S21, S22] using hout2⟩

/-- Claim 1 at the common crossed stabilizer `H₁₂`.  This is the tail
term needed in equation (5); for positive weight it is obtained from the
same genuinely smaller saturated-tail instance as the `H₁,H₂` claims,
and weight zero is discharged separately. -/
theorem dgmCrossedClaimOne_H12_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    (b₁ b₂ : A)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hpair2 : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    let H := AddAction.stabilizer A (E : Set A)
    let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
    Nat.card H12 * (dgmCappedMultiplicitySum H12 P k - k + 1) ≤
      (patternSubsumSpectrum P νtail + dgmSubgroupFinset H12).card +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
  classical
  dsimp only
  let H := AddAction.stabilizer A (E : Set A)
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let T := patternSubsumSpectrum P νtail
  let U := dgmCrossedPairBase H B C b₁ b₂
  have hgeom := dgmCrossedStabilizerGeometry
    B C P (base.quotientPattern H) b₁ b₂ νtail hext
      hD12 hpair1 hpair2
  rcases hgeom with ⟨h12H, h1H, h2H, h121, h122⟩
  have hEdata := hE
  unfold DGMPatternConvergent at hEdata
  dsimp only at hEdata
  rcases hEdata with ⟨hEne, _, hEupper, _⟩
  have hy : y ∈ patternSubsumSpectrum (B :: C :: P) μ :=
    (mem_patternSubsumSpectrum_iff _ μ y).2 ⟨⟨base, hbase⟩⟩
  have hU : U.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    have hxU : x ∈ U := by
      simpa [H, U, dgmCrossedPairBase, dgmCrossedPairTail1] using
        (Finset.mem_union_left
          (dgmCosetSlice H B b₂ + dgmCosetSlice H C b₁) hx)
    exact ⟨x, hxU⟩
  have hH12fin : dgmSubgroupFinset H12 =
      (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
    simpa [H12] using dgmSubgroupFinset_dgmCrossedH12_eq_addStab
      B C P b₁ b₂ νtail hD12
  have hDstab : AddAction.stabilizer A
      ((((U + T) + dgmSubgroupFinset H12 : Finset A)) : Set A) = H12 := by
    have hsum : (U + T) + dgmSubgroupFinset H12 =
        dgmCrossedD12 B C P b₁ b₂ νtail := by
      rw [show U + T = dgmCrossedD12 B C P b₁ b₂ νtail by rfl,
        hH12fin]
      exact Finset.add_addStab _
    rw [hsum]
    rfl
  by_cases hk : k = 0
  · subst k
    simpa [H12, H, T] using dgmClaimOne_zero H12 H P νtail
  · have hout := dgmClaimOne_of_strongIH M ih H12 H12 H le_rfl
        (by simpa [H12, H] using h12H) P νtail (Nat.pos_of_ne_zero hk)
        (B :: C :: P) μ hmeasure E hEne hEupper (by rfl) hy
        (by simpa [H] using hescape) htail U hU hDstab
    simpa [H12, H, T] using hout

/-- Both equation-(5) three-summand bounds, with the leading-pair Kneser
correction and the `H₁₂` Claim 1 generated internally. -/
theorem dgmCrossedD12_threeSummand_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    (b₁ b₂ : A)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hpair2 : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    let H := AddAction.stabilizer A (E : Set A)
    let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
    let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
    let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
    let S11 := dgmCosetSlice H B b₁
    let S12 := dgmCosetSlice H C b₂
    let S21 := dgmCosetSlice H B b₂
    let S22 := dgmCosetSlice H C b₁
    (((S11 + dgmSubgroupFinset H12).card +
          (S12 + dgmSubgroupFinset H12).card - Nat.card H1) +
        Nat.card H12 * (dgmCappedMultiplicitySum H12 P k - k + 1) ≤
      (dgmCrossedD12 B C P b₁ b₂ νtail).card + 2 * Nat.card H12 +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k)) ∧
    (((S21 + dgmSubgroupFinset H12).card +
          (S22 + dgmSubgroupFinset H12).card - Nat.card H2) +
        Nat.card H12 * (dgmCappedMultiplicitySum H12 P k - k + 1) ≤
      (dgmCrossedD12 B C P b₁ b₂ νtail).card + 2 * Nat.card H12 +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k)) := by
  classical
  dsimp only
  let H := AddAction.stabilizer A (E : Set A)
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
  let T := patternSubsumSpectrum P νtail
  let S11 := dgmCosetSlice H B b₁
  let S12 := dgmCosetSlice H C b₂
  let S21 := dgmCosetSlice H B b₂
  let S22 := dgmCosetSlice H C b₁
  have hlead := dgmCrossedLeadingPairTail_bounds
    B C P b₁ b₂ νtail htail hD12 hpair1 hpair2
  have hclaim := dgmCrossedClaimOne_H12_of_strongIH
    M ih B C P μ E hE hmeasure base hbase b₁ b₂ νtail hext
      htail hD12 hpair1 hpair2 hescape
  rcases hlead with ⟨hlead1, hlead2⟩
  have hlead1' :
      ((S11 + dgmSubgroupFinset H12).card +
          (S12 + dgmSubgroupFinset H12).card - Nat.card H1) +
          (T + dgmSubgroupFinset H12).card ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + Nat.card H12 := by
    simpa [H, H12, H1, T, S11, S12] using hlead1
  have hlead2' :
      ((S21 + dgmSubgroupFinset H12).card +
          (S22 + dgmSubgroupFinset H12).card - Nat.card H2) +
          (T + dgmSubgroupFinset H12).card ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + Nat.card H12 := by
    simpa [H, H12, H2, T, S21, S22] using hlead2
  have hclaim' : Nat.card H12 *
      (dgmCappedMultiplicitySum H12 P k - k + 1) ≤
    (T + dgmSubgroupFinset H12).card +
      Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
    simpa [H, H12, T] using hclaim
  constructor
  · simpa [H, H12, H1, S11, S12] using
      (show ((S11 + dgmSubgroupFinset H12).card +
            (S12 + dgmSubgroupFinset H12).card - Nat.card H1) +
          Nat.card H12 * (dgmCappedMultiplicitySum H12 P k - k + 1) ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + 2 * Nat.card H12 +
          Nat.card H * (dgmCappedMultiplicitySum H P k - k) by omega)
  · simpa [H, H12, H2, S21, S22] using
      (show ((S21 + dgmSubgroupFinset H12).card +
            (S22 + dgmSubgroupFinset H12).card - Nat.card H2) +
          Nat.card H12 * (dgmCappedMultiplicitySum H12 P k - k + 1) ≤
        (dgmCrossedD12 B C P b₁ b₂ νtail).card + 2 * Nat.card H12 +
          Nat.card H * (dgmCappedMultiplicitySum H P k - k) by omega)

/-- Claim 1 instantiated for the two actual crossed stabilizers `H₁,H₂`.
The `k=0` endpoint is discharged by the literal zero-pattern calculation;
for `k>0` the well-founded IH is called only after the existing escape
measure proof. -/
theorem dgmCrossedClaimOne_pair_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    (b₁ b₂ : A)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hpair2 : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    Nat.card (dgmCrossedH1 B C P b₁ b₂ νtail) *
        (dgmCappedMultiplicitySum
          (dgmCrossedH1 B C P b₁ b₂ νtail) P k - k + 1) ≤
      (patternSubsumSpectrum P νtail +
        dgmSubgroupFinset (dgmCrossedH1 B C P b₁ b₂ νtail)).card +
        Nat.card (AddAction.stabilizer A (E : Set A)) *
          (dgmCappedMultiplicitySum
            (AddAction.stabilizer A (E : Set A)) P k - k) ∧
    Nat.card (dgmCrossedH2 B C P b₁ b₂ νtail) *
        (dgmCappedMultiplicitySum
          (dgmCrossedH2 B C P b₁ b₂ νtail) P k - k + 1) ≤
      (patternSubsumSpectrum P νtail +
        dgmSubgroupFinset (dgmCrossedH2 B C P b₁ b₂ νtail)).card +
        Nat.card (AddAction.stabilizer A (E : Set A)) *
          (dgmCappedMultiplicitySum
            (AddAction.stabilizer A (E : Set A)) P k - k) := by
  classical
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
  let Ttail := patternSubsumSpectrum P νtail
  let X1 := dgmCosetSlice H B b₁ + dgmCosetSlice H C b₂
  let X2 := dgmCosetSlice H B b₂ + dgmCosetSlice H C b₁
  have hgeom := dgmCrossedStabilizerGeometry
    B C P ν b₁ b₂ νtail hext hD12 hpair1 hpair2
  rcases hgeom with ⟨h12H, h1H, h2H, h121, h122⟩
  have hEdata := hE
  unfold DGMPatternConvergent at hEdata
  dsimp only at hEdata
  rcases hEdata with ⟨hEne, _, hEupper, _⟩
  have hy : y ∈ patternSubsumSpectrum (B :: C :: P) μ :=
    (mem_patternSubsumSpectrum_iff _ μ y).2 ⟨⟨base, hbase⟩⟩
  have hX1 : X1.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    exact ⟨x, by simpa [H, X1, dgmCrossedPairTail1] using hx⟩
  have hX2 : X2.Nonempty := by
    obtain ⟨z, hz⟩ := hpair2
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    exact ⟨x, by simpa [H, X2, dgmCrossedPairTail2] using hx⟩
  have hH12fin : dgmSubgroupFinset H12 =
      (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
    simpa [H12] using
      dgmSubgroupFinset_dgmCrossedH12_eq_addStab
        B C P b₁ b₂ νtail hD12
  have hDstab1 : AddAction.stabilizer A
      ((((X1 + Ttail) + dgmSubgroupFinset H12 : Finset A)) : Set A) = H1 := by
    simpa [H, X1, Ttail, H12, H1, dgmCrossedH1,
      dgmCrossedD1, dgmCrossedPairTail1, hH12fin]
  have hDstab2 : AddAction.stabilizer A
      ((((X2 + Ttail) + dgmSubgroupFinset H12 : Finset A)) : Set A) = H2 := by
    simpa [H, X2, Ttail, H12, H2, dgmCrossedH2,
      dgmCrossedD2, dgmCrossedPairTail2, hH12fin]
  have hclaim1 : Nat.card H1 *
      (dgmCappedMultiplicitySum H1 P k - k + 1) ≤
    (Ttail + dgmSubgroupFinset H1).card +
      Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
    by_cases hk : k = 0
    · subst k
      simpa [H1, H, Ttail] using dgmClaimOne_zero H1 H P νtail
    · apply dgmClaimOne_of_strongIH M ih H12 H1 H
        (by simpa [H12, H1] using h121) (by simpa [H1, H] using h1H)
        P νtail (Nat.pos_of_ne_zero hk) (B :: C :: P) μ hmeasure E hEne hEupper
        (by rfl) hy (by simpa [H] using hescape) htail X1 hX1 hDstab1
  have hclaim2 : Nat.card H2 *
      (dgmCappedMultiplicitySum H2 P k - k + 1) ≤
    (Ttail + dgmSubgroupFinset H2).card +
      Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
    by_cases hk : k = 0
    · subst k
      simpa [H2, H, Ttail] using dgmClaimOne_zero H2 H P νtail
    · apply dgmClaimOne_of_strongIH M ih H12 H2 H
        (by simpa [H12, H2] using h122) (by simpa [H2, H] using h2H)
        P νtail (Nat.pos_of_ne_zero hk) (B :: C :: P) μ hmeasure E hEne hEupper
        (by rfl) hy (by simpa [H] using hescape) htail X2 hX2 hDstab2
  exact ⟨by simpa [H1, H, Ttail] using hclaim1,
    by simpa [H2, H, Ttail] using hclaim2⟩

/-- The two equation-(3) three-summand inequalities needed for equation (4),
with Claim 1 generated internally from the well-founded IH. -/
theorem dgmCrossedD1D2_threeSummand_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    (b₁ b₂ : A)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hpair2 : (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    let H := AddAction.stabilizer A (E : Set A)
    let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
    let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
    (dgmCosetSlice H B b₁ + dgmSubgroupFinset H1).card +
        (dgmCosetSlice H C b₂ + dgmSubgroupFinset H1).card +
        Nat.card H1 * (dgmCappedMultiplicitySum H1 P k - k + 1) ≤
      (dgmCrossedD1 B C P b₁ b₂ νtail).card + 2 * Nat.card H1 +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k) ∧
    (dgmCosetSlice H B b₂ + dgmSubgroupFinset H2).card +
        (dgmCosetSlice H C b₁ + dgmSubgroupFinset H2).card +
        Nat.card H2 * (dgmCappedMultiplicitySum H2 P k - k + 1) ≤
      (dgmCrossedD2 B C P b₁ b₂ νtail).card + 2 * Nat.card H2 +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
  classical
  dsimp only
  let H := AddAction.stabilizer A (E : Set A)
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
  let Ttail := patternSubsumSpectrum P νtail
  let S11 := dgmCosetSlice H B b₁
  let S12 := dgmCosetSlice H C b₂
  let S21 := dgmCosetSlice H B b₂
  let S22 := dgmCosetSlice H C b₁
  have hclaims := dgmCrossedClaimOne_pair_of_strongIH
    M ih B C P μ E hE hmeasure base hbase b₁ b₂ νtail hext htail
      hD12 hpair1 hpair2 hescape
  rcases hclaims with ⟨hclaim1, hclaim2⟩
  have hgeom := dgmCrossedStabilizerGeometry
    B C P (base.quotientPattern H) b₁ b₂ νtail hext
      hD12 hpair1 hpair2
  rcases hgeom with ⟨h12H, h1H, h2H, h121, h122⟩
  have hS11 : S11.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨u, by simpa [H, S11, dgmCrossedPairTail1] using hu⟩
  have hS12 : S12.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨v, by simpa [H, S12, dgmCrossedPairTail1] using hv⟩
  have hS21 : S21.Nonempty := by
    obtain ⟨z, hz⟩ := hpair2
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨u, by simpa [H, S21, dgmCrossedPairTail2] using hu⟩
  have hS22 : S22.Nonempty := by
    obtain ⟨z, hz⟩ := hpair2
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨v, by simpa [H, S22, dgmCrossedPairTail2] using hv⟩
  have hH12fin : dgmSubgroupFinset H12 =
      (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
    simpa [H12] using
      dgmSubgroupFinset_dgmCrossedH12_eq_addStab
        B C P b₁ b₂ νtail hD12
  have hD1eq : iteratedFinsetSum
      [S11, S12, Ttail + dgmSubgroupFinset H12] =
        dgmCrossedD1 B C P b₁ b₂ νtail := by
    simp only [iteratedFinsetSum_cons, iteratedFinsetSum_nil]
    rw [dgmCrossedD1, dgmCrossedPairTail1, ← hH12fin]
    simp [H, S11, S12, Ttail]
    ac_rfl
  have hD2eq : iteratedFinsetSum
      [S21, S22, Ttail + dgmSubgroupFinset H12] =
        dgmCrossedD2 B C P b₁ b₂ νtail := by
    simp only [iteratedFinsetSum_cons, iteratedFinsetSum_nil]
    rw [dgmCrossedD2, dgmCrossedPairTail2, ← hH12fin]
    simp [H, S21, S22, Ttail]
    ac_rfl
  have hthree1 := dgmCrossedThreeSummand_of_claimOne
    H12 H1 H (by simpa [H12, H1] using h121)
      S11 S12 Ttail (dgmCrossedD1 B C P b₁ b₂ νtail)
      hS11 hS12 htail hD1eq rfl
      (dgmCappedMultiplicitySum H1 P k - k + 1)
      (Nat.card H * (dgmCappedMultiplicitySum H P k - k))
      (by simpa [H1, H, Ttail] using hclaim1)
  have hthree2 := dgmCrossedThreeSummand_of_claimOne
    H12 H2 H (by simpa [H12, H2] using h122)
      S21 S22 Ttail (dgmCrossedD2 B C P b₁ b₂ νtail)
      hS21 hS22 htail hD2eq rfl
      (dgmCappedMultiplicitySum H2 P k - k + 1)
      (Nat.card H * (dgmCappedMultiplicitySum H P k - k))
      (by simpa [H2, H, Ttail] using hclaim2)
  exact ⟨by simpa [H, H1, S11, S12] using hthree1,
    by simpa [H, H2, S21, S22] using hthree2⟩

/-- Claim 1 for the first crossed branch alone.  This deliberately does not
assume the second crossed branch is nonempty: it is the input used to prove
that nonemptiness at the numeric gate. -/
theorem dgmCrossedClaimOne_H1_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    (b₁ b₂ : A)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    let H := AddAction.stabilizer A (E : Set A)
    let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
    Nat.card H1 * (dgmCappedMultiplicitySum H1 P k - k + 1) ≤
      (patternSubsumSpectrum P νtail + dgmSubgroupFinset H1).card +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
  classical
  dsimp only
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let T := patternSubsumSpectrum P νtail
  let X1 := dgmCosetSlice H B b₁ + dgmCosetSlice H C b₂
  have hD12fiber : ∀ x ∈ dgmCrossedD12 B C P b₁ b₂ νtail,
      (x : A ⧸ H) = ν.quotientSum := by
    intro x hx
    exact patternSubsumSpectrum_quotient_eq _ ν
      (dgmCrossedD12_subset_patternSubsumSpectrum
        B C P ν b₁ b₂ νtail hext hx)
  have hD1ne : (dgmCrossedD1 B C P b₁ b₂ νtail).Nonempty := by
    rw [dgmCrossedD1]
    exact hpair1.add ⟨0, hD12.zero_mem_addStab⟩
  have h12H : H12 ≤ H := by
    change AddAction.stabilizer A
      (dgmCrossedD12 B C P b₁ b₂ νtail : Set A) ≤ H
    exact stabilizer_le_of_nonempty_subset_quotientFiber H
      (dgmCrossedD12 B C P b₁ b₂ νtail) hD12 ν.quotientSum hD12fiber
  have h1H : H1 ≤ H := by
    change AddAction.stabilizer A
      (dgmCrossedD1 B C P b₁ b₂ νtail : Set A) ≤ H
    exact stabilizer_le_of_nonempty_subset_quotientFiber H
      (dgmCrossedD1 B C P b₁ b₂ νtail) hD1ne ν.quotientSum
      (fun x hx ↦ hD12fiber x
        (dgmCrossedD1_subset_D12 B C P b₁ b₂ νtail hD12 hx))
  have h121 : H12 ≤ H1 := by
    change dgmCrossedH12 B C P b₁ b₂ νtail ≤
      AddAction.stabilizer A
        (dgmCrossedD1 B C P b₁ b₂ νtail : Set A)
    exact dgmCrossedH12_le_D1_stabilizer
      B C P b₁ b₂ νtail hD12 hpair1
  have hEdata := hE
  unfold DGMPatternConvergent at hEdata
  dsimp only at hEdata
  rcases hEdata with ⟨hEne, _, hEupper, _⟩
  have hy : y ∈ patternSubsumSpectrum (B :: C :: P) μ :=
    (mem_patternSubsumSpectrum_iff _ μ y).2 ⟨⟨base, hbase⟩⟩
  have hX1 : X1.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    exact ⟨x, by simpa [H, X1, dgmCrossedPairTail1] using hx⟩
  have hH12fin : dgmSubgroupFinset H12 =
      (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
    simpa [H12] using dgmSubgroupFinset_dgmCrossedH12_eq_addStab
      B C P b₁ b₂ νtail hD12
  have hDstab : AddAction.stabilizer A
      ((((X1 + T) + dgmSubgroupFinset H12 : Finset A)) : Set A) = H1 := by
    simpa [H, X1, T, H12, H1, dgmCrossedH1,
      dgmCrossedD1, dgmCrossedPairTail1, hH12fin]
  by_cases hk : k = 0
  · subst k
    simpa [H1, H, T] using dgmClaimOne_zero H1 H P νtail
  · have hout := dgmClaimOne_of_strongIH M ih H12 H1 H h121 h1H
        P νtail (Nat.pos_of_ne_zero hk) (B :: C :: P) μ hmeasure
        E hEne hEupper (by rfl) hy (by simpa [H] using hescape)
        htail X1 hX1 hDstab
    simpa [H1, H, T] using hout

/-- Equation (3) for the first crossed branch, before the proof knows that
the second branch is nonempty. -/
theorem dgmCrossedD1_threeSummand_of_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    (b₁ b₂ : A)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    let H := AddAction.stabilizer A (E : Set A)
    let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
    (dgmCosetSlice H B b₁ + dgmSubgroupFinset H1).card +
        (dgmCosetSlice H C b₂ + dgmSubgroupFinset H1).card +
        Nat.card H1 * (dgmCappedMultiplicitySum H1 P k - k + 1) ≤
      (dgmCrossedD1 B C P b₁ b₂ νtail).card + 2 * Nat.card H1 +
        Nat.card H * (dgmCappedMultiplicitySum H P k - k) := by
  classical
  dsimp only
  let H := AddAction.stabilizer A (E : Set A)
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let T := patternSubsumSpectrum P νtail
  let S11 := dgmCosetSlice H B b₁
  let S12 := dgmCosetSlice H C b₂
  have hclaim := dgmCrossedClaimOne_H1_of_strongIH
    M ih B C P μ E hE hmeasure base hbase b₁ b₂ νtail hext
      htail hD12 hpair1 hescape
  have h121 : H12 ≤ H1 := by
    change dgmCrossedH12 B C P b₁ b₂ νtail ≤
      AddAction.stabilizer A
        (dgmCrossedD1 B C P b₁ b₂ νtail : Set A)
    exact dgmCrossedH12_le_D1_stabilizer
      B C P b₁ b₂ νtail hD12 hpair1
  have hS11 : S11.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨u, by simpa [H, S11, dgmCrossedPairTail1] using hu⟩
  have hS12 : S12.Nonempty := by
    obtain ⟨z, hz⟩ := hpair1
    obtain ⟨x, hx, t, ht, hxt⟩ := Finset.mem_add.mp hz
    obtain ⟨u, hu, v, hv, huv⟩ := Finset.mem_add.mp hx
    exact ⟨v, by simpa [H, S12, dgmCrossedPairTail1] using hv⟩
  have hH12fin : dgmSubgroupFinset H12 =
      (dgmCrossedD12 B C P b₁ b₂ νtail).addStab := by
    simpa [H12] using dgmSubgroupFinset_dgmCrossedH12_eq_addStab
      B C P b₁ b₂ νtail hD12
  have hD1eq : iteratedFinsetSum
      [S11, S12, T + dgmSubgroupFinset H12] =
        dgmCrossedD1 B C P b₁ b₂ νtail := by
    simp only [iteratedFinsetSum_cons, iteratedFinsetSum_nil]
    rw [dgmCrossedD1, dgmCrossedPairTail1, ← hH12fin]
    simp [H, S11, S12, T]
    ac_rfl
  have hout := dgmCrossedThreeSummand_of_claimOne
    H12 H1 H h121 S11 S12 T (dgmCrossedD1 B C P b₁ b₂ νtail)
      hS11 hS12 htail hD1eq rfl
      (dgmCappedMultiplicitySum H1 P k - k + 1)
      (Nat.card H * (dgmCappedMultiplicitySum H P k - k))
      (by simpa [H1, H, T] using hclaim)
  simpa [H, H1, S11, S12] using hout

/-- The source initial crossed data forces the second crossed component to
be nonempty and the two exceptional coarse cosets to be distinct.  Neither
gate is assumed: strict equation (2), first-branch Claim 1/equation (3), and
the already-proved numeric contradiction generate both. -/
theorem dgmCrossedNumericGates_of_minimalConvergent_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (hP : IsNonemptySetPartition P)
    (hFeasible : (layerSubsumSpectrum
      (dgmInterUnionLayers B C P) (k + 2)).Nonempty)
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmin : ∀ E' : Finset A, DGMPatternConvergent B C P μ E' →
      Nat.card (AddAction.stabilizer A (E : Set A)) ≤
        Nat.card (AddAction.stabilizer A (E' : Set A)))
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    {b₁ b₂ : A} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    (dgmCrossedPairTail2 B C P b₁ b₂ νtail).Nonempty ∧
      (b₁ : A ⧸ AddAction.stabilizer A (E : Set A)) ≠
        (b₂ : A ⧸ AddAction.stabilizer A (E : Set A)) := by
  classical
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let S11 := dgmCosetSlice H B b₁
  let S12 := dgmCosetSlice H C b₂
  let D1 := dgmCrossedD1 B C P b₁ b₂ νtail
  have hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅ := by
    simpa [H, ν] using
      patternSubsumSpectrum_interUnion_quotientPattern_eq_empty_of_escape
        B C P μ E hE base hbase hescape
  have hD12fine : dgmCrossedD12 B C P b₁ b₂ νtail ⊆
      patternSubsumSpectrum (B :: C :: P) ν :=
    dgmCrossedD12_subset_patternSubsumSpectrum
      B C P ν b₁ b₂ νtail hext
  have hD1ne : D1.Nonempty := by
    simp only [D1, dgmCrossedD1]
    exact hpair1.add ⟨0, hD12.zero_mem_addStab⟩
  have hD1fine : D1 ⊆ patternSubsumSpectrum (B :: C :: P) ν :=
    fun x hx ↦ hD12fine
      (dgmCrossedD1_subset_D12 B C P b₁ b₂ νtail hD12 hx)
  have hstrict := dgmStrictEquationTwo_of_minimal_convergent_refined_piece
    B C P μ E hE hmin base hbase D1 hD1ne hD1fine hescape
  have hthree := dgmCrossedD1_threeSummand_of_strongIH
    M ih B C P μ E hE hmeasure base hbase b₁ b₂ νtail hext
      htail hD12 hpair1 hescape
  have hD1fiber : ∀ x ∈ D1, (x : A ⧸ H) = ν.quotientSum := by
    intro x hx
    exact patternSubsumSpectrum_quotient_eq _ ν (hD1fine hx)
  have h1H : H1 ≤ H := by
    change AddAction.stabilizer A (D1 : Set A) ≤ H
    exact stabilizer_le_of_nonempty_subset_quotientFiber H
      D1 hD1ne ν.quotientSum hD1fiber
  have hstrict' : D1.card + Nat.card H *
        (dgmCappedMultiplicitySum H
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1) <
      Nat.card H1 *
        (dgmCappedMultiplicitySum H1
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1) := by
    change D1.card + Nat.card (AddAction.stabilizer A (E : Set A)) *
        (dgmCappedMultiplicitySum (AddAction.stabilizer A (E : Set A))
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1) <
      Nat.card (AddAction.stabilizer A (D1 : Set A)) *
        (dgmCappedMultiplicitySum (AddAction.stabilizer A (D1 : Set A))
          (dgmInterUnionLayers B C P) (k + 2) - (k + 2) + 1)
    exact hstrict
  have hslices := dgmCrossedStrictSlicesMissing_lt_of_threeSummand
    H1 H h1H B C P ν hb₁ hb₂ νtail hext htail hinfeasible
      hP hFeasible S11 S12 D1
      hstrict'
      (by simpa [H, H1, S11, S12, D1] using hthree)
  have hgates := dgmCrossedNumericGates_of_strictSlicesMissing
    H1 h1H B C P b₁ b₂ νtail htail
      (by simpa [H, H1, S11, S12, dgmSingleSliceSaturation] using hslices)
  simpa [H] using hgates

/-- Saturating a fixed coarse-coset slice is cardinal-monotone in the
saturating subgroup.  This is the exact `H₁₂ ≤ Hε` transport needed to
compare equation (4), proved at `Hε`, with equation (5), proved at the common
subgroup `H₁₂`. -/
theorem card_dgmSingleSliceSaturation_le_of_le
    [Fintype A] (H L K : AddSubgroup A) (hLK : L ≤ K)
    (B : Finset A) (b : A) :
    (dgmSingleSliceSaturation H L B b).card ≤
      (dgmSingleSliceSaturation H K B b).card := by
  apply Finset.card_le_card
  intro x hx
  obtain ⟨s, hs, l, hl, rfl⟩ := Finset.mem_add.mp hx
  apply Finset.mem_add.mpr
  exact ⟨s, hs, l,
    (mem_dgmSubgroupFinset_iff K l).2
      (hLK ((mem_dgmSubgroupFinset_iff L l).1 hl)), rfl⟩

/-- Complete crossed-branch contradiction for a minimum nontrivial
convergent.  Starting only with the source initial data (`D₁₂` and the
first pair-tail nonempty), this theorem internally derives the second
pair-tail and quotient-separation gates, all three strict equation-(2)
bounds, equations (4)--(5), and the final two-coset contradiction. -/
theorem dgmCrossedContradiction_of_minimalConvergent_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (hP : IsNonemptySetPartition P)
    (hFeasible : (layerSubsumSpectrum
      (dgmInterUnionLayers B C P) (k + 2)).Nonempty)
    (μ : QuotientPattern K (k + 2)) (E : Finset A)
    (hE : DGMPatternConvergent B C P μ E)
    (hmin : ∀ E' : Finset A, DGMPatternConvergent B C P μ E' →
      Nat.card (AddAction.stabilizer A (E : Set A)) ≤
        Nat.card (AddAction.stabilizer A (E' : Set A)))
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    {y : A} (base : LayerSubsumChoice (B :: C :: P) (k + 2) y)
    (hbase : base.RealizesPattern μ)
    {b₁ b₂ : A} (hb₁ : b₁ ∈ B) (hb₂ : b₂ ∈ C)
    (νtail : QuotientPattern
      (AddAction.stabilizer A (E : Set A)) k)
    (hext : QuotientPattern.IsTwoStepExtension
      (base.quotientPattern (AddAction.stabilizer A (E : Set A)))
      b₁ b₂ νtail)
    (htail : (patternSubsumSpectrum P νtail).Nonempty)
    (hD12 : (dgmCrossedD12 B C P b₁ b₂ νtail).Nonempty)
    (hpair1 : (dgmCrossedPairTail1 B C P b₁ b₂ νtail).Nonempty)
    (hescape : ¬dgmCosetFiber
      (AddAction.stabilizer A (E : Set A)) y ⊆
        patternSubsumSpectrum (B :: C :: P) μ) :
    False := by
  classical
  let H := AddAction.stabilizer A (E : Set A)
  let ν := base.quotientPattern H
  let H12 := dgmCrossedH12 B C P b₁ b₂ νtail
  let H1 := dgmCrossedH1 B C P b₁ b₂ νtail
  let H2 := dgmCrossedH2 B C P b₁ b₂ νtail
  let S11 := dgmCosetSlice H B b₁
  let S12 := dgmCosetSlice H C b₂
  let S21 := dgmCosetSlice H B b₂
  let S22 := dgmCosetSlice H C b₁
  let D1 := dgmCrossedD1 B C P b₁ b₂ νtail
  let D2 := dgmCrossedD2 B C P b₁ b₂ νtail
  let D12 := dgmCrossedD12 B C P b₁ b₂ νtail
  have hgates := dgmCrossedNumericGates_of_minimalConvergent_strongIH
    M ih B C P hP hFeasible μ E hE hmin hmeasure base hbase hb₁ hb₂
      νtail hext htail hD12 hpair1 hescape
  rcases hgates with ⟨hpair2, hne⟩
  have hinfeasible : patternSubsumSpectrum
      (dgmInterUnionLayers B C P) ν = ∅ := by
    simpa [H, ν] using
      patternSubsumSpectrum_interUnion_quotientPattern_eq_empty_of_escape
        B C P μ E hE base hbase hescape
  have hgeom := dgmCrossedStabilizerGeometry
    B C P ν b₁ b₂ νtail hext hD12 hpair1 hpair2
  rcases hgeom with ⟨h12H, h1H, h2H, h121, h122⟩
  have hstrict := dgmCrossedStrictEquationTwo_three
    B C P μ E hE hmin base hbase b₁ b₂ νtail hext
      hD12 hpair1 hpair2 hescape
  rcases hstrict with ⟨hstrict1, hstrict2, hstrict12⟩
  have hthree4 := dgmCrossedD1D2_threeSummand_of_strongIH
    M ih B C P μ E hE hmeasure base hbase b₁ b₂ νtail hext
      htail hD12 hpair1 hpair2 hescape
  rcases hthree4 with ⟨hthree1, hthree2⟩
  have hthree5 := dgmCrossedD12_threeSummand_of_strongIH
    M ih B C P μ E hE hmeasure base hbase b₁ b₂ νtail hext
      htail hD12 hpair1 hpair2 hescape
  rcases hthree5 with ⟨hthree51, hthree52⟩
  have h4₁ := dgmCrossedEquationFour_of_threeSummand
    H1 H h1H B C P ν hb₁ hb₂ νtail hext htail hinfeasible
      hP hFeasible S11 S12 D1
      (by simpa [H, H1, D1] using hstrict1)
      (by simpa [H, H1, S11, S12, D1] using hthree1)
  have h4₂ := dgmCrossedEquationFour_of_threeSummand
    H2 H h2H B C P ν hb₁ hb₂ νtail hext htail hinfeasible
      hP hFeasible S21 S22 D2
      (by simpa [H, H2, D2] using hstrict2)
      (by simpa [H, H2, S21, S22, D2] using hthree2)
  have h5₁ := dgmCrossedEquationFive_of_threeSummand
    H12 H H1 h12H h121 B C P ν hb₁ hb₂ νtail hext htail
      hinfeasible (by simpa [H] using hne) hP hFeasible S11 S12 D12
      (by simpa [H, H12, D12] using hstrict12)
      (by simpa [H, H12, H1, S11, S12, D12] using hthree51)
  have h5₂ := dgmCrossedEquationFive_of_threeSummand
    H12 H H2 h12H h122 B C P ν hb₁ hb₂ νtail hext htail
      hinfeasible (by simpa [H] using hne) hP hFeasible S21 S22 D12
      (by simpa [H, H12, D12] using hstrict12)
      (by simpa [H, H12, H2, S21, S22, D12] using hthree52)
  have h4₁common :
      (dgmSingleSliceSaturation H H12 B b₁).card +
          (dgmSingleSliceSaturation H H12 C b₂).card + Nat.card H1 ≤
        Nat.card H := by
    have hmB := card_dgmSingleSliceSaturation_le_of_le
      H H12 H1 h121 B b₁
    have hmC := card_dgmSingleSliceSaturation_le_of_le
      H H12 H1 h121 C b₂
    have h4₁' :
        (dgmSingleSliceSaturation H H1 B b₁).card +
            (dgmSingleSliceSaturation H H1 C b₂).card + Nat.card H1 ≤
          Nat.card H := by
      simpa [H, H1, S11, S12, dgmSingleSliceSaturation] using h4₁
    omega
  have h4₂common :
      (dgmSingleSliceSaturation H H12 B b₂).card +
          (dgmSingleSliceSaturation H H12 C b₁).card + Nat.card H2 ≤
        Nat.card H := by
    have hmB := card_dgmSingleSliceSaturation_le_of_le
      H H12 H2 h122 B b₂
    have hmC := card_dgmSingleSliceSaturation_le_of_le
      H H12 H2 h122 C b₁
    have h4₂' :
        (dgmSingleSliceSaturation H H2 B b₂).card +
            (dgmSingleSliceSaturation H H2 C b₁).card + Nat.card H2 ≤
          Nat.card H := by
      simpa [H, H2, S21, S22, dgmSingleSliceSaturation] using h4₂
    omega
  apply dgmCrossedFourBoundsContradiction_without_stab_lower
    H H12 H1 H2 h12H B C b₁ b₂ (by simpa [H] using hne)
  · exact h4₁common
  · exact h4₂common
  · simpa [H, H12, H1, S11, S12,
      dgmSingleSliceSaturation] using h5₁
  · simpa [H, H12, H2, S21, S22,
      dgmSingleSliceSaturation] using h5₂

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

/-- With trivial finite stabilizer, the stabilizer-quotient capped incidence
sum is exactly the raw capped incidence sum on the ambient group. -/
theorem dgmStabilizerCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
    [Fintype A] (C : Finset A) (hC : C.Nonempty)
    (hstab : C.addStab = {0}) (P : List (Finset A)) (n : ℕ) :
    stabilizerDgmCappedMultiplicitySum C P n =
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
  unfold stabilizerDgmCappedMultiplicitySum rawDgmCappedMultiplicitySum
  symm
  refine Fintype.sum_equiv e
    (fun x : A ↦ min n (rawLayerMultiplicity P x))
    (fun z : A ⧸ H ↦ min n (stabilizerLayerMultiplicity C P z)) ?_
  intro x
  congr 1
  symm
  simpa [H, q, e] using
    stabilizerLayerMultiplicity_mk_eq_raw_of_addStab_eq_singleton
      C hC hstab P x

/-- In a genuine counterexample with aperiodic target, every convergent has
nontrivial stabilizer.  Otherwise the convergent inequality, the exact
intersection--union incidence identity, and `C ⊆ T` already prove the target
pattern bound. -/
theorem dgmPatternConvergent_stabilizer_ne_bot_of_target_failure
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n)
    (hTargetStab :
      (patternSubsumSpectrum (B :: C :: P) μ).addStab = {0})
    (hfailure : ¬DGMPatternBound (B :: C :: P) μ)
    (E : Finset A) (hEconv : DGMPatternConvergent B C P μ E) :
    AddAction.stabilizer A (E : Set A) ≠ ⊥ := by
  intro hEbot
  have hEdata := hEconv
  unfold DGMPatternConvergent at hEdata
  dsimp only at hEdata
  rcases hEdata with ⟨hEne, _, hEupper, hEbound⟩
  let T := patternSubsumSpectrum (B :: C :: P) μ
  have hTne : T.Nonempty := hEne.mono (by simpa [T] using hEupper)
  have hEadd : E.addStab = {0} := by
    ext a
    have hcoe := Finset.coe_addStab hEne
    rw [← Finset.mem_coe, hcoe, hEbot]
    simp
  have hEcap :=
    dgmStabilizerCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
      E hEne hEadd (dgmInterUnionLayers B C P) n
  have hTcap :=
    dgmStabilizerCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
      T hTne (by simpa [T] using hTargetStab) (B :: C :: P) n
  have hraw := rawDgmCappedMultiplicitySum_inter_union B C P n
  have hEcard : E.card ≤ T.card :=
    Finset.card_le_card (by simpa [T] using hEupper)
  have hEgroupCard : Nat.card (AddAction.stabilizer A (E : Set A)) = 1 := by
    rw [hEbot]
    exact Nat.card_unique
  have hTgroupCard : Nat.card (AddAction.stabilizer A (T : Set A)) = 1 := by
    rw [← card_addStab_eq_natCard_stabilizer T hTne,
      show T.addStab = {0} by simpa [T] using hTargetStab]
    simp
  apply hfailure
  unfold DGMPatternBound
  dsimp only
  change Nat.card (AddAction.stabilizer A (T : Set A)) *
      (stabilizerDgmCappedMultiplicitySum T (B :: C :: P) n - n + 1) ≤
    T.card + Nat.card K * (dgmCappedMultiplicitySum K (B :: C :: P) n - n)
  rw [hTgroupCard, one_mul, hTcap]
  rw [hEgroupCard, one_mul, hEcap] at hEbound
  change rawDgmCappedMultiplicitySum
      ((B ∩ C) :: (B ∪ C) :: P) n - n + 1 ≤
    E.card + Nat.card K *
      (dgmCappedMultiplicitySum K (B :: C :: P) n - n) at hEbound
  rw [hraw] at hEbound
  exact hEbound.trans (Nat.add_le_add_right hEcard _)

/-- The minimum convergent selected in the crossed counterexample is
simultaneously nontrivial and has the exact extension nonconvergence property
used in equation (2). -/
theorem exists_dgmPatternConvergent_min_nontrivial_with_extension_hnot
    [Fintype A] {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (μ : QuotientPattern K n) {D₀ : Finset A}
    (hD₀ : DGMPatternConvergent B C P μ D₀)
    (hTargetStab :
      (patternSubsumSpectrum (B :: C :: P) μ).addStab = {0})
    (hfailure : ¬DGMPatternBound (B :: C :: P) μ) :
    ∃ E : Finset A,
      DGMPatternConvergent B C P μ E ∧
      AddAction.stabilizer A (E : Set A) ≠ ⊥ ∧
      (∀ E' : Finset A, DGMPatternConvergent B C P μ E' →
        Nat.card (AddAction.stabilizer A (E : Set A)) ≤
          Nat.card (AddAction.stabilizer A (E' : Set A))) ∧
      ∀ (D : Finset A) (y : A),
        D.Nonempty →
        (∀ x ∈ D,
          (x : A ⧸ AddAction.stabilizer A (E : Set A)) =
            (y : A ⧸ AddAction.stabilizer A (E : Set A))) →
        y ∉ D →
        (¬dgmCosetFiber (AddAction.stabilizer A (E : Set A)) y ⊆
          patternSubsumSpectrum (B :: C :: P) μ) →
        ¬DGMPatternConvergent B C P μ (E ∪ D) := by
  obtain ⟨E, hE, hmin, hext⟩ :=
    exists_dgmPatternConvergent_min_with_extension_hnot B C P μ hD₀
  exact ⟨E, hE,
    dgmPatternConvergent_stabilizer_ne_bot_of_target_failure
      B C P μ hTargetStab hfailure E hE,
    hmin, hext⟩

/-- The fully prepared general branch of the source minimal-counterexample
classification.  Incomparable overlapping leading layers with feasible
intersection--union transform cannot be a counterexample: the transform is
strictly smaller, hence gives the initial convergent, and the complete
crossed contradiction eliminates its minimum nontrivial extension. -/
theorem dgmPatternBound_of_preparedCrossed_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (B C : Finset A) (P : List (Finset A))
    (hP : IsNonemptySetPartition P)
    (hBC : ¬B ⊆ C) (hCB : ¬C ⊆ B)
    (μ : QuotientPattern K (k + 2))
    (hmeasure : dgmPatternInnerMeasure (B :: C :: P) μ = M)
    (hTarget : (patternSubsumSpectrum (B :: C :: P) μ).Nonempty)
    (hTargetStab :
      (patternSubsumSpectrum (B :: C :: P) μ).addStab = {0})
    (hTransformed :
      (patternSubsumSpectrum (dgmInterUnionLayers B C P) μ).Nonempty) :
    DGMPatternBound (B :: C :: P) μ := by
  classical
  have hlt := dgmPatternInnerMeasure_inter_union_lt
    B C P μ hBC hCB
  have hltM : DGMPatternInnerLt
      (dgmPatternInnerMeasure (dgmInterUnionLayers B C P) μ) M := by
    rw [← hmeasure]
    exact hlt
  have hsmall := ih
    (dgmPatternInnerMeasure (dgmInterUnionLayers B C P) μ) hltM
  have hboundTransformed :
      DGMPatternBound (dgmInterUnionLayers B C P) μ :=
    hsmall K (k + 2) inferInstance inferInstance
      (dgmInterUnionLayers B C P) μ rfl hTransformed
  have hD₀ : DGMPatternConvergent B C P μ
      (patternSubsumSpectrum (dgmInterUnionLayers B C P) μ) :=
    patternSubsumSpectrum_inter_union_isConvergent
      B C P μ hTransformed hboundTransformed
  by_contra hfailure
  obtain ⟨E, hE, hEnontrivial, hmin, hextension⟩ :=
    exists_dgmPatternConvergent_min_nontrivial_with_extension_hnot
      B C P μ hD₀ hTargetStab hfailure
  obtain ⟨y, base, hbase, hescape, b₁, hb₁, hb₁C,
      b₂, hb₂, hb₂B, νtail, hext, htail, hD12, hpair1⟩ :=
    exists_initialCrossedData_of_nontrivial_convergent
      B C P μ hTargetStab E hE hEnontrivial
  have hFeasible : (layerSubsumSpectrum
      (dgmInterUnionLayers B C P) (k + 2)).Nonempty :=
    hTransformed.mono
      (patternSubsumSpectrum_subset_layerSubsumSpectrum _ μ)
  exact dgmCrossedContradiction_of_minimalConvergent_strongIH
    M ih B C P hP hFeasible μ E hE hmin hmeasure base hbase hb₁ hb₂
      νtail hext htail hD12 hpair1 hescape

/-- Nonemptiness of every labelled cell is invariant under reordering. -/
theorem isNonemptySetPartition_of_perm
    {P Q : List (Finset A)} (hPQ : P.Perm Q)
    (hP : IsNonemptySetPartition P) : IsNonemptySetPartition Q := by
  intro B hB
  exact hP B (hPQ.mem_iff.mpr hB)

/-- Two distinct labelled cells can be moved to the leading positions.  The
tail erases exactly one occurrence of each value; this is sufficient for the
source use because incomparable cells are necessarily distinct. -/
theorem exists_two_head_perm
    (P : List (Finset A)) {B C : Finset A}
    (hB : B ∈ P) (hC : C ∈ P) (hBC : B ≠ C) :
    ∃ R : List (Finset A), P.Perm (B :: C :: R) := by
  classical
  have hCerase : C ∈ P.erase B := by
    exact (List.mem_erase_of_ne (Ne.symm hBC)).2 hC
  refine ⟨(P.erase B).erase C, ?_⟩
  exact (List.perm_cons_erase hB).trans
    (List.Perm.cons B (List.perm_cons_erase hCerase))

/-- Faithful labelled `ℓ < m` preparation.  Starting with a deletable cell
at index `i` of minimum cardinality among all deletable indices, any remaining
cell which does not contain it can be moved to the second position.  Minimality
rules out reverse containment, and the deleted-spectrum witness embeds in the
intersection--union transform, including when the intersection is empty. -/
theorem exists_incomparable_two_head_of_minimal_deletableIdx
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K n)
    (i : ℕ) (hi : i < Q.length)
    (hdelete : (patternSubsumSpectrum (Q.eraseIdx i) μ).Nonempty)
    (hmin : ∀ (j : ℕ) (hj : j < Q.length),
      (patternSubsumSpectrum (Q.eraseIdx j) μ).Nonempty →
      (Q[i]'hi).card ≤ (Q[j]'hj).card)
    (hnotCommon : ∃ C ∈ Q.eraseIdx i, ¬Q[i]'hi ⊆ C) :
    ∃ (C : Finset A) (R : List (Finset A)),
      Q.Perm (Q[i]'hi :: C :: R) ∧
      ¬Q[i]'hi ⊆ C ∧ ¬C ⊆ Q[i]'hi ∧
      (patternSubsumSpectrum
        (dgmInterUnionLayers (Q[i]'hi) C R) μ).Nonempty := by
  classical
  let B := Q[i]'hi
  obtain ⟨C, hCtail, hBC⟩ := hnotCommon
  have hBCne : B ≠ C := by
    intro h
    apply hBC
    change Q[i]'hi = C at h
    rw [← h]
  let R := (Q.eraseIdx i).erase C
  have htailPerm : (Q.eraseIdx i).Perm (C :: R) := by
    simpa [R] using List.perm_cons_erase hCtail
  have hfull : Q.Perm (B :: C :: R) := by
    exact (List.getElem_cons_eraseIdx_perm hi).symm.trans
      (List.Perm.cons B htailPerm)
  have htail : (patternSubsumSpectrum (C :: R) μ).Nonempty := by
    rw [← patternSubsumSpectrum_eq_of_perm htailPerm μ]
    exact hdelete
  have hCB : ¬C ⊆ B := by
    intro hCB
    have hBR : (patternSubsumSpectrum (B :: R) μ).Nonempty :=
      htail.mono (patternSubsumSpectrum_cons_mono hCB R μ)
    have hCmemQ : C ∈ Q := List.mem_of_mem_eraseIdx hCtail
    obtain ⟨j, hj, hCeq⟩ := List.getElem_of_mem hCmemQ
    have hidxErase : (Q.eraseIdx j).Perm (Q.erase C) := by
      have h := (List.erase_getElem hj).symm
      rwa [hCeq] at h
    have hvalueErase : (Q.erase C).Perm (B :: R) := by
      have h := hfull.erase C
      simpa [hBCne, B] using h
    have hEraseC : (Q.eraseIdx j).Perm (B :: R) :=
      hidxErase.trans hvalueErase
    have hdeleteC :
        (patternSubsumSpectrum (Q.eraseIdx j) μ).Nonempty := by
      rw [patternSubsumSpectrum_eq_of_perm hEraseC μ]
      exact hBR
    have hle := hmin j hj hdeleteC
    rw [hCeq] at hle
    change B.card ≤ C.card at hle
    have hlt : C.card < B.card := by
      apply Finset.card_lt_card
      exact ⟨hCB, hBC⟩
    omega
  have htransformed : (patternSubsumSpectrum
      (dgmInterUnionLayers B C R) μ).Nonempty := by
    apply htail.mono
    simpa [dgmInterUnionLayers] using
      patternSubsumSpectrum_tail_subset_inter_union B C R μ
  exact ⟨C, R, by simpa [B] using hfull, by simpa [B] using hBC,
    by simpa [B] using hCB, by simpa [B] using htransformed⟩

/-- Prepared-crossed is independent of where the eligible pair occurs in
the labelled layer list.  This wrapper contains no classification premise:
the transformed-spectrum nonemptiness is exactly the already isolated
prepared endpoint, now stated for the actual reordered tail. -/
theorem dgmPatternBound_of_perm_preparedCrossed_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (B C : Finset A) (P : List (Finset A))
    (hperm : Q.Perm (B :: C :: P))
    (hQ : IsNonemptySetPartition Q)
    (hBC : ¬B ⊆ C) (hCB : ¬C ⊆ B)
    (μ : QuotientPattern K (k + 2))
    (hmeasure : dgmPatternInnerMeasure Q μ = M)
    (hTarget : (patternSubsumSpectrum Q μ).Nonempty)
    (hTargetStab : (patternSubsumSpectrum Q μ).addStab = {0})
    (hTransformed :
      (patternSubsumSpectrum (dgmInterUnionLayers B C P) μ).Nonempty) :
    DGMPatternBound Q μ := by
  have hspec := patternSubsumSpectrum_eq_of_perm hperm μ
  have hP : IsNonemptySetPartition P := by
    have hhead := isNonemptySetPartition_of_perm hperm hQ
    intro D hD
    exact hhead D (by simp [hD])
  have hmeasureHead :
      dgmPatternInnerMeasure (B :: C :: P) μ = M :=
    (dgmPatternInnerMeasure_eq_of_perm hperm μ).symm.trans hmeasure
  have hTargetHead :
      (patternSubsumSpectrum (B :: C :: P) μ).Nonempty := by
    rwa [← hspec]
  have hTargetStabHead :
      (patternSubsumSpectrum (B :: C :: P) μ).addStab = {0} := by
    rwa [← hspec]
  have hboundHead := dgmPatternBound_of_preparedCrossed_strongIH
    M ih B C P hP hBC hCB μ hmeasureHead hTargetHead
      hTargetStabHead hTransformed
  exact (dgmPatternBound_iff_of_perm hperm μ).2 hboundHead

/-- Complete `ℓ < m`, non-common-cell branch of the source classification.
The only data supplied are the genuinely selected minimum deletable index and
the fact that its cell is not contained in every remaining labelled cell;
all prepared-crossed hypotheses are constructed internally. -/
theorem dgmPatternBound_of_minimal_deletableIdx_not_common_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K (k + 2))
    (hQ : IsNonemptySetPartition Q)
    (i : ℕ) (hi : i < Q.length)
    (hdelete : (patternSubsumSpectrum (Q.eraseIdx i) μ).Nonempty)
    (hmin : ∀ (j : ℕ) (hj : j < Q.length),
      (patternSubsumSpectrum (Q.eraseIdx j) μ).Nonempty →
      (Q[i]'hi).card ≤ (Q[j]'hj).card)
    (hnotCommon : ∃ C ∈ Q.eraseIdx i, ¬Q[i]'hi ⊆ C)
    (hmeasure : dgmPatternInnerMeasure Q μ = M)
    (hTarget : (patternSubsumSpectrum Q μ).Nonempty)
    (hTargetStab : (patternSubsumSpectrum Q μ).addStab = {0}) :
    DGMPatternBound Q μ := by
  obtain ⟨C, R, hperm, hBC, hCB, hTransformed⟩ :=
    exists_incomparable_two_head_of_minimal_deletableIdx
      Q μ i hi hdelete hmin hnotCommon
  exact dgmPatternBound_of_perm_preparedCrossed_strongIH
    M ih Q (Q[i]'hi) C R hperm hQ hBC hCB μ hmeasure hTarget
      hTargetStab hTransformed

/-- Complete `ℓ < m`, common-cell branch.  Exact-layer exchange proves that
deleting the selected labelled occurrence preserves the pattern spectrum;
the same common-cell hypothesis makes both capped incidence corrections
identical.  Positive head cardinality then strictly lowers the second inner
measure coordinate, so the strong induction hypothesis gives the conclusion. -/
theorem dgmPatternBound_of_minimal_deletableIdx_common_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {n : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K n)
    (hQ : IsNonemptySetPartition Q)
    (i : ℕ) (hi : i < Q.length) (hlt : n < Q.length)
    (hdelete : (patternSubsumSpectrum (Q.eraseIdx i) μ).Nonempty)
    (hcommon : ∀ C ∈ Q.eraseIdx i, Q[i]'hi ⊆ C)
    (hmeasure : dgmPatternInnerMeasure Q μ = M) :
    DGMPatternBound Q μ := by
  classical
  let B := Q[i]'hi
  let P := Q.eraseIdx i
  have hperm : Q.Perm (B :: P) := by
    exact (List.getElem_cons_eraseIdx_perm hi).symm
  have hltHead : n < (B :: P).length := by
    rw [← hperm.length_eq]
    exact hlt
  have hspec : patternSubsumSpectrum (B :: P) μ =
      patternSubsumSpectrum P μ :=
    patternSubsumSpectrum_cons_eq_tail_of_head_subset_all
      B P μ (by simpa [B, P] using hcommon) hltHead
  have hBne : B.Nonempty := by
    exact hQ B (by simpa [B] using List.getElem_mem hi)
  have hmeasureLt : DGMPatternInnerLt
      (dgmPatternInnerMeasure P μ)
      (dgmPatternInnerMeasure (B :: P) μ) := by
    unfold dgmPatternInnerMeasure
    rw [hspec]
    exact Prod.Lex.right _ (Prod.Lex.left _ _ (by
      simp only [dgmTotalLayerCard, List.map_cons, List.sum_cons]
      have hpos : 0 < B.card := Finset.card_pos.mpr hBne
      omega))
  have hheadM : dgmPatternInnerMeasure (B :: P) μ = M :=
    (dgmPatternInnerMeasure_eq_of_perm hperm μ).symm.trans hmeasure
  have hltM : DGMPatternInnerLt (dgmPatternInnerMeasure P μ) M := by
    rw [← hheadM]
    exact hmeasureLt
  have hsmall := ih (dgmPatternInnerMeasure P μ) hltM
  have hboundTail : DGMPatternBound P μ :=
    hsmall K n inferInstance inferInstance P μ rfl
      (by simpa [P] using hdelete)
  have hboundHead : DGMPatternBound (B :: P) μ := by
    unfold DGMPatternBound at hboundTail ⊢
    rw [hspec]
    simp only at hboundTail ⊢
    rw [stabilizerDgmCappedMultiplicitySum_cons_eq_tail_of_head_subset_all
      (patternSubsumSpectrum P μ) B P n
      (by simpa [B, P] using hcommon) hltHead]
    rw [dgmCappedMultiplicitySum_cons_eq_tail_of_head_subset_all
      K B P n (by simpa [B, P] using hcommon) hltHead]
    exact hboundTail
  exact (dgmPatternBound_iff_of_perm hperm μ).2 hboundHead

/-- Full source `ℓ < m` branch for weights at least two.  The minimum
deletable labelled cell is selected internally from an actual target choice;
the common and non-common alternatives are then discharged by the two
preceding faithful branches. -/
theorem dgmPatternBound_of_weight_lt_length_strongIH
    [Fintype A] (M : DGMPatternInnerMeasure)
    (ih : ∀ M', DGMPatternInnerLt M' M → DGMPatternAtMeasure (A := A) M')
    {K : AddSubgroup A} {k : ℕ}
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (Q : List (Finset A)) (μ : QuotientPattern K (k + 2))
    (hQ : IsNonemptySetPartition Q)
    (hlt : k + 2 < Q.length)
    (hmeasure : dgmPatternInnerMeasure Q μ = M)
    (hTarget : (patternSubsumSpectrum Q μ).Nonempty)
    (hTargetStab : (patternSubsumSpectrum Q μ).addStab = {0}) :
    DGMPatternBound Q μ := by
  obtain ⟨i, hi, hdelete, hmin⟩ :=
    exists_minimal_deletableIdx Q μ hTarget hlt
  by_cases hcommon : ∀ C ∈ Q.eraseIdx i, Q[i]'hi ⊆ C
  · exact dgmPatternBound_of_minimal_deletableIdx_common_strongIH
      M ih Q μ hQ i hi hlt hdelete hcommon hmeasure
  · push Not at hcommon
    exact dgmPatternBound_of_minimal_deletableIdx_not_common_strongIH
      M ih Q μ hQ i hi hdelete hmin hcommon hmeasure hTarget hTargetStab

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

/-- Full-weight generalized DGM when every layer lies in one `K`-coset.
The pattern is forced, its `K` correction vanishes, and the result is exactly
the already proved full-layer Kneser/DGM endpoint. -/
theorem dgmPatternBound_full_of_singleton_quotient
    [Fintype A] (K : AddSubgroup A)
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (μ : QuotientPattern K P.length)
    (hP : IsNonemptySetPartition P)
    (hTarget : (patternSubsumSpectrum P μ).Nonempty)
    (hsingle : ∀ B ∈ P, (quotientLayer K B).card = 1) :
    DGMPatternBound P μ := by
  have hspec :=
    patternSubsumSpectrum_eq_fullLayerSumSpectrum_of_singleton_quotient
      P μ hTarget hsingle
  have hcap :=
    dgmCappedMultiplicitySum_full_eq_length_of_singleton_quotient
      K P hsingle
  have hfullTarget : (fullLayerSumSpectrum P).Nonempty := by
    rw [← hspec]
    exact hTarget
  have hfull := dgmSetpartitionBound_full P hP
  unfold DGMSetpartitionBound at hfull
  unfold DGMPatternBound
  rw [hspec, hcap]
  simp only [Nat.sub_self, Nat.mul_zero, Nat.add_zero]
  rw [← card_addStab_eq_natCard_stabilizer _ hfullTarget]
  simpa [fullLayerSumSpectrum, Nat.mul_comm] using hfull

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
