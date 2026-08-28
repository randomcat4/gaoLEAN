import GaoLean.PGGMOSpectrum
import GaoLean.PGDavenportBridge

/-!
# Occurrence-faithful complement and quotient bridges for ordinary DGM

This module records the literal labelled complement duality used by the
ordinary prescribed-length argument.  If the whole source has length
`n + r`, complementing an `n`-selection gives an `r`-selection and reverses
its sum around the total source sum.  Consequently the two exact spectra are
affine reflections of one another and have the same additive stabilizer.

The second half transports ordinary exact spectra through an additive
homomorphism.  In particular, a quotient occurrence is never identified with
an original occurrence: selections are transported through the canonical
equivalence of positions induced by `List.map`.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

variable {A : Type u} [AddCommGroup A] [Fintype A]

noncomputable local instance ordinaryDGMComplementQuotientFintype
    (K : AddSubgroup A) : Fintype (A ⧸ K) :=
  Fintype.ofFinite (A ⧸ K)

/-- The sum of all labelled occurrences of a source list. -/
noncomputable def ordinaryOccurrenceTotal (xs : List A) : A :=
  ∑ i : Occurrence xs, occurrenceValue xs i

/-- Literal complement of a labelled selection inside the full occurrence
universe. -/
noncomputable def complementSelection {xs : List A}
    (I : Selection xs) : Selection xs := by
  classical
  exact Finset.univ \ I

theorem card_complementSelection
    {xs : List A} {n r : ℕ}
    (hlen : xs.length = n + r)
    (I : Selection xs) (hIcard : I.card = n) :
    (complementSelection I).card = r := by
  classical
  rw [complementSelection,
    Finset.card_sdiff_of_subset (Finset.subset_univ I)]
  have huniv : (Finset.univ : Selection xs).card = xs.length := by simp
  rw [huniv, hlen, hIcard]
  omega

theorem disjoint_complementSelection_left
    {xs : List A} (I : Selection xs) :
    Disjoint I (complementSelection I) := by
  classical
  simp [complementSelection, Finset.disjoint_left]

theorem union_complementSelection
    {xs : List A} (I : Selection xs) :
    I ∪ complementSelection I = Finset.univ := by
  classical
  simp [complementSelection]

/-- The sum of the literal complement is the total occurrence sum minus the
selected sum.  This is the central labelled ledger identity. -/
theorem sum_complementSelection
    {xs : List A} (I : Selection xs) :
    (∑ i ∈ complementSelection I, occurrenceValue xs i) =
      ordinaryOccurrenceTotal xs -
        ∑ i ∈ I, occurrenceValue xs i := by
  classical
  have hsplit :=
    (Finset.univ : Selection xs).sum_inter_add_sum_sdiff I
      (occurrenceValue xs)
  rw [Finset.inter_eq_right.mpr (Finset.subset_univ I)] at hsplit
  calc
    (∑ i ∈ complementSelection I, occurrenceValue xs i) =
        ((∑ i ∈ I, occurrenceValue xs i) +
          ∑ i ∈ complementSelection I, occurrenceValue xs i) -
            ∑ i ∈ I, occurrenceValue xs i := by abel
    _ = ordinaryOccurrenceTotal xs -
          ∑ i ∈ I, occurrenceValue xs i := by
      rw [complementSelection, hsplit]
      rfl

/-- One direction of exact-spectrum complement duality, retaining the
realizing occurrence complement. -/
theorem exists_complement_selection_of_mem_ordinaryExactSpectrum
    {xs : List A} {n r : ℕ}
    (hlen : xs.length = n + r) {y : A}
    (hy : y ∈ ordinaryExactSpectrum xs n) :
    ∃ J : Selection xs,
      J.card = r ∧
        (∑ i ∈ J, occurrenceValue xs i) =
          ordinaryOccurrenceTotal xs - y := by
  classical
  obtain ⟨I, hIcard, hIsum⟩ :=
    (mem_ordinaryExactSpectrum_iff xs n y).1 hy
  refine ⟨complementSelection I,
    card_complementSelection hlen I hIcard, ?_⟩
  rw [sum_complementSelection, hIsum]

/-- Exact membership duality between complementary occurrence spectra. -/
theorem mem_ordinaryExactSpectrum_complement_iff
    {xs : List A} {n r : ℕ}
    (hlen : xs.length = n + r) (y : A) :
    y ∈ ordinaryExactSpectrum xs n ↔
      ordinaryOccurrenceTotal xs - y ∈ ordinaryExactSpectrum xs r := by
  classical
  constructor
  · intro hy
    obtain ⟨J, hJcard, hJsum⟩ :=
      exists_complement_selection_of_mem_ordinaryExactSpectrum hlen hy
    exact (mem_ordinaryExactSpectrum_iff xs r _).2
      ⟨J, hJcard, hJsum⟩
  · intro hy
    have hlen' : xs.length = r + n := by
      simpa [Nat.add_comm] using hlen
    obtain ⟨I, hIcard, hIsum⟩ :=
      exists_complement_selection_of_mem_ordinaryExactSpectrum
        hlen' hy
    apply (mem_ordinaryExactSpectrum_iff xs n y).2
    refine ⟨I, hIcard, ?_⟩
    calc
      (∑ i ∈ I, occurrenceValue xs i) =
          ordinaryOccurrenceTotal xs -
            (ordinaryOccurrenceTotal xs - y) := hIsum
      _ = y := by abel

/-- Finite-spectrum form of the affine complement relation. -/
theorem ordinaryExactSpectrum_eq_image_complement
    [DecidableEq A] {xs : List A} {n r : ℕ}
    (hlen : xs.length = n + r) :
    ordinaryExactSpectrum xs n =
      (ordinaryExactSpectrum xs r).image
        (fun y ↦ ordinaryOccurrenceTotal xs - y) := by
  classical
  ext y
  constructor
  · intro hy
    apply Finset.mem_image.mpr
    refine ⟨ordinaryOccurrenceTotal xs - y,
      (mem_ordinaryExactSpectrum_complement_iff hlen y).1 hy, ?_⟩
    abel
  · intro hy
    obtain ⟨z, hz, hzy⟩ := Finset.mem_image.mp hy
    have hcomp :=
      (mem_ordinaryExactSpectrum_complement_iff hlen y).2
    apply hcomp
    have hyz : ordinaryOccurrenceTotal xs - y = z := by
      rw [← hzy]
      abel
    simpa [hyz] using hz

private theorem mem_addStab_of_affine_reflection
    [DecidableEq A] (S T : Finset A) (c a : A)
    (hS : S.Nonempty) (hT : T.Nonempty)
    (hreflect : ∀ x : A, x ∈ S ↔ c - x ∈ T)
    (ha : a ∈ S.addStab) :
    a ∈ T.addStab := by
  classical
  have htranslate : a +ᵥ S = S :=
    (Finset.mem_addStab hS).1 ha
  have haMem : ∀ x : A, a + x ∈ S ↔ x ∈ S := by
    intro x
    have hx : a + x ∈ a +ᵥ S ↔ x ∈ S := by
      simp [Finset.mem_vadd_finset, vadd_eq_add]
    rw [htranslate] at hx
    exact hx
  have hreflect' : ∀ x : A, x ∈ T ↔ c - x ∈ S := by
    intro x
    simpa only [sub_sub_cancel] using (hreflect (c - x)).symm
  apply (Finset.mem_addStab hT).2
  ext x
  rw [Finset.mem_vadd_finset]
  constructor
  · rintro ⟨y, hy, hay⟩
    apply (hreflect' x).2
    have hcy : c - y ∈ S := (hreflect' y).1 hy
    apply (haMem (c - x)).1
    have heq : a + (c - x) = c - y := by
      rw [← hay]
      simp only [vadd_eq_add]
      abel
    rw [heq]
    exact hcy
  · intro hx
    refine ⟨-a + x, ?_, ?_⟩
    · apply (hreflect' (-a + x)).2
      have hcx : c - x ∈ S := (hreflect' x).1 hx
      have heq : c - (-a + x) = a + (c - x) := by abel
      rw [heq]
      exact (haMem (c - x)).2 hcx
    · simp [vadd_eq_add]

/-- Affine reflection does not change the additive stabilizer. -/
theorem ordinarySpectrumStabilizer_complement
    {xs : List A} {n r : ℕ}
    (hlen : xs.length = n + r) :
    ordinarySpectrumStabilizer xs n =
      ordinarySpectrumStabilizer xs r := by
  classical
  have hnle : n ≤ xs.length := by omega
  have hrle : r ≤ xs.length := by omega
  have hN := ordinaryExactSpectrum_nonempty xs n hnle
  have hR := ordinaryExactSpectrum_nonempty xs r hrle
  have hreflect : ∀ y : A,
      y ∈ ordinaryExactSpectrum xs n ↔
        ordinaryOccurrenceTotal xs - y ∈ ordinaryExactSpectrum xs r :=
    mem_ordinaryExactSpectrum_complement_iff hlen
  apply SetLike.ext
  intro a
  change a ∈ AddAction.stabilizer A
      (ordinaryExactSpectrum xs n : Set A) ↔
    a ∈ AddAction.stabilizer A
      (ordinaryExactSpectrum xs r : Set A)
  constructor
  · intro ha
    have haFin : a ∈ (ordinaryExactSpectrum xs n).addStab := by
      rw [← Finset.mem_coe, Finset.coe_addStab hN]
      exact ha
    have haFin' := mem_addStab_of_affine_reflection
      (ordinaryExactSpectrum xs n) (ordinaryExactSpectrum xs r)
      (ordinaryOccurrenceTotal xs) a hN hR hreflect haFin
    rw [← Finset.mem_coe, Finset.coe_addStab hR] at haFin'
    exact haFin'
  · have hreflect' : ∀ y : A,
        y ∈ ordinaryExactSpectrum xs r ↔
          ordinaryOccurrenceTotal xs - y ∈
            ordinaryExactSpectrum xs n := by
      intro y
      simpa only [sub_sub_cancel] using
        (hreflect (ordinaryOccurrenceTotal xs - y)).symm
    intro ha
    have haFin : a ∈ (ordinaryExactSpectrum xs r).addStab := by
      rw [← Finset.mem_coe, Finset.coe_addStab hR]
      exact ha
    have haFin' := mem_addStab_of_affine_reflection
      (ordinaryExactSpectrum xs r) (ordinaryExactSpectrum xs n)
      (ordinaryOccurrenceTotal xs) a hR hN hreflect' haFin
    rw [← Finset.mem_coe, Finset.coe_addStab hN] at haFin'
    exact haFin'

section MapTransport

variable {B : Type v} [AddCommGroup B] [Fintype B]

/-- Pullback through `List.map` preserves the number of labelled positions. -/
theorem card_pullbackMapSelection
    (f : A → B) (xs : List A)
    (I : Selection (xs.map f)) :
    (ConcreteGDihedral.pullbackMapSelection f xs I).card = I.card := by
  classical
  simp [ConcreteGDihedral.pullbackMapSelection]

/-- For an additive homomorphism, the sum of a pulled-back labelled
selection maps to the original projected sum. -/
theorem map_sum_pullbackMapSelection
    (f : A →+ B) (xs : List A)
    (I : Selection (xs.map f)) :
    f (∑ i ∈ ConcreteGDihedral.pullbackMapSelection f xs I,
        occurrenceValue xs i) =
      ∑ i ∈ I, occurrenceValue (xs.map f) i := by
  classical
  rw [map_sum]
  simp only [ConcreteGDihedral.pullbackMapSelection, Finset.sum_map]
  apply Finset.sum_congr rfl
  intro i hi
  exact ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv_symm f xs i

/-- Exact labelled transport of ordinary spectra through an additive
homomorphism.  No injectivity of the homomorphism is required: the reverse
direction pulls selected positions back through `List.map`, not through the
map on values. -/
theorem image_ordinaryExactSpectrum_addMonoidHom
    [DecidableEq B] (f : A →+ B) (xs : List A) (n : ℕ) :
    (ordinaryExactSpectrum xs n).image f =
      ordinaryExactSpectrum (xs.map f) n := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨I, hIcard, hIsum⟩ :=
      (mem_ordinaryExactSpectrum_iff xs n z).1 hz
    let e := ConcreteGDihedral.mapOccurrenceEquiv f xs
    let J : Selection (xs.map f) := I.map e.toEmbedding
    apply (mem_ordinaryExactSpectrum_iff (xs.map f) n (f z)).2
    refine ⟨J, by simpa [J] using hIcard, ?_⟩
    calc
      (∑ i ∈ J, occurrenceValue (xs.map f) i) =
          ∑ i ∈ I, f (occurrenceValue xs i) := by
        simp only [J, Finset.sum_map]
        apply Finset.sum_congr rfl
        intro i hi
        exact ConcreteGDihedral.occurrenceValue_mapOccurrenceEquiv f xs i
      _ = f (∑ i ∈ I, occurrenceValue xs i) := by rw [map_sum]
      _ = f z := by rw [hIsum]
  · intro hy
    obtain ⟨I, hIcard, hIsum⟩ :=
      (mem_ordinaryExactSpectrum_iff (xs.map f) n y).1 hy
    let J : Selection xs :=
      ConcreteGDihedral.pullbackMapSelection f xs I
    let z : A := ∑ i ∈ J, occurrenceValue xs i
    have hz : z ∈ ordinaryExactSpectrum xs n := by
      apply (mem_ordinaryExactSpectrum_iff xs n z).2
      refine ⟨J, ?_, rfl⟩
      simpa only [J, card_pullbackMapSelection] using hIcard
    apply Finset.mem_image.mpr
    refine ⟨z, hz, ?_⟩
    calc
      f z = ∑ i ∈ I, occurrenceValue (xs.map f) i := by
        exact map_sum_pullbackMapSelection f xs I
      _ = y := hIsum

/-- Quotient specialization of exact ordinary spectrum transport. -/
theorem image_ordinaryExactSpectrum_quotient
    (xs : List A) (n : ℕ) (K : AddSubgroup A)
    [DecidableEq (A ⧸ K)] :
    (ordinaryExactSpectrum xs n).image (QuotientAddGroup.mk' K) =
      ordinaryExactSpectrum
        (xs.map (QuotientAddGroup.mk' K)) n :=
  image_ordinaryExactSpectrum_addMonoidHom
    (QuotientAddGroup.mk' K) xs n

/-- A projected exact-spectrum witness pulls back to genuine source labels,
with exact cardinality and the expected quotient sum. -/
theorem exists_pullback_selection_of_mem_ordinaryExactSpectrum_map
    (f : A →+ B) (xs : List A) (n : ℕ) {y : B}
    (hy : y ∈ ordinaryExactSpectrum (xs.map f) n) :
    ∃ I : Selection xs,
      I.card = n ∧
        f (∑ i ∈ I, occurrenceValue xs i) = y := by
  classical
  obtain ⟨J, hJcard, hJsum⟩ :=
    (mem_ordinaryExactSpectrum_iff (xs.map f) n y).1 hy
  refine ⟨ConcreteGDihedral.pullbackMapSelection f xs J,
    ?_, ?_⟩
  · simpa only [card_pullbackMapSelection] using hJcard
  · rw [map_sum_pullbackMapSelection, hJsum]

end MapTransport

end GaoLean

#print axioms GaoLean.mem_ordinaryExactSpectrum_complement_iff
#print axioms GaoLean.ordinaryExactSpectrum_eq_image_complement
#print axioms GaoLean.ordinarySpectrumStabilizer_complement
#print axioms GaoLean.map_sum_pullbackMapSelection
#print axioms GaoLean.image_ordinaryExactSpectrum_addMonoidHom
#print axioms GaoLean.image_ordinaryExactSpectrum_quotient
#print axioms GaoLean.exists_pullback_selection_of_mem_ordinaryExactSpectrum_map
