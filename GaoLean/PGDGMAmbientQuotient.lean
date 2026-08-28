import GaoLean.PGDGMCore

/-!
# Ambient-stabilizer quotient transport for the generalized DGM theorem

This module contains only the mechanical quotient layer.  Its eventual
consumer is the outer induction on the cardinality of the ambient group.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u v

variable {A : Type u} [AddCommGroup A] [DecidableEq A]

/-- The stabilizer of a nonempty prescribed-pattern spectrum lies in the
subgroup defining the pattern, since the whole spectrum is contained in one
literal quotient fiber. -/
theorem patternSpectrum_stabilizer_le_patternSubgroup
    [Fintype A] (K : AddSubgroup A) (n : ℕ)
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    (P : List (Finset A)) (mu : QuotientPattern K n)
    (hT : (patternSubsumSpectrum P mu).Nonempty) :
    AddAction.stabilizer A
        (patternSubsumSpectrum P mu : Set A) ≤ K := by
  exact stabilizer_le_of_nonempty_subset_quotientFiber
    K (patternSubsumSpectrum P mu) hT mu.quotientSum
      (fun _x hx ↦ patternSubsumSpectrum_quotient_eq P mu hx)

/-- Membership in a layer quotient is unchanged after first quotienting by
`J ≤ K` and identifying the resulting double quotient with `A/K`. -/
theorem mem_quotientLayer_image_ambientQuotient_iff
    (J K : AddSubgroup A) [DecidableEq (A ⧸ J)]
    (hJK : J ≤ K) (B : Finset A)
    (r : (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) :
    r ∈ quotientLayer (K.map (QuotientAddGroup.mk' J))
        (B.image (QuotientAddGroup.mk' J)) ↔
      (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r ∈
        quotientLayer K B := by
  classical
  let qJ : A →+ A ⧸ J := QuotientAddGroup.mk' J
  let e : ((A ⧸ J) ⧸ K.map qJ) ≃+ A ⧸ K :=
    QuotientAddGroup.quotientQuotientEquivQuotient J K hJK
  constructor
  · intro hr
    obtain ⟨z, hz, hzr⟩ :=
      (mem_quotientLayer_iff (K.map qJ) (B.image qJ) r).1 hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp hz
    apply (mem_quotientLayer_iff K B (e r)).2
    refine ⟨x, hx, ?_⟩
    rw [← hzr]
    change (x : A ⧸ K) =
      (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK)
        ((x : A ⧸ J) :
          (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))
    exact (QuotientAddGroup.quotientQuotientEquivQuotientAux_mk_mk
      J K hJK x).symm
  · intro hr
    obtain ⟨x, hx, hxe⟩ :=
      (mem_quotientLayer_iff K B (e r)).1 hr
    apply (mem_quotientLayer_iff (K.map qJ) (B.image qJ) r).2
    refine ⟨qJ x, Finset.mem_image.mpr ⟨x, hx, rfl⟩, ?_⟩
    apply e.injective
    calc
      e ((qJ x : A ⧸ J) : (A ⧸ J) ⧸ K.map qJ) =
          (x : A ⧸ K) := by
        exact QuotientAddGroup.quotientQuotientEquivQuotientAux_mk_mk
          J K hJK x
      _ = e r := hxe

/-- Representative form of the preceding quotient-layer equivalence. -/
theorem mk_ambientQuotient_eq_iff
    (J K : AddSubgroup A) (hJK : J ≤ K) (x : A)
    (r : (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) :
    (((x : A ⧸ J) :
        (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) = r) ↔
      (x : A ⧸ K) =
        (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r := by
  let e := QuotientAddGroup.quotientQuotientEquivQuotient J K hJK
  constructor
  · intro h
    rw [← h]
    exact QuotientAddGroup.quotientQuotientEquivQuotientAux_mk_mk
      J K hJK x
  · intro h
    apply e.injective
    exact (QuotientAddGroup.quotientQuotientEquivQuotientAux_mk_mk
      J K hJK x).trans h

/-- Mapping a proof-relevant choice through `A → A/J` retains every
labelled-layer decision and transports its selected-coset counts through the
third-isomorphism equivalence. -/
theorem LayerSubsumChoice.exists_map_ambientQuotient
    (J K : AddSubgroup A) [DecidableEq (A ⧸ J)]
    [DecidableEq ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    [DecidableEq (A ⧸ K)] (hJK : J ≤ K)
    {P : List (Finset A)} {n : ℕ} {y : A}
    (h : LayerSubsumChoice P n y) :
    ∃ hbar : LayerSubsumChoice
        (P.map fun C ↦ C.image (QuotientAddGroup.mk' J)) n
        (QuotientAddGroup.mk' J y),
      ∀ r : (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J),
        hbar.quotientMultiplicity
            (K.map (QuotientAddGroup.mk' J)) r =
          h.quotientMultiplicity K
            ((QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r) := by
  induction h with
  | zero P =>
      refine ⟨(by simpa using (LayerSubsumChoice.zero
        (P.map fun C ↦ C.image (QuotientAddGroup.mk' J)))), ?_⟩
      intro r
      simp [LayerSubsumChoice.quotientMultiplicity]
  | skip h ih =>
      obtain ⟨hbar, hbarMult⟩ := ih
      refine ⟨by simpa only [List.map_cons] using
        LayerSubsumChoice.skip hbar, ?_⟩
      intro r
      simpa [LayerSubsumChoice.quotientMultiplicity] using hbarMult r
  | @take B P n b y hb h ih =>
      let qJ : A →+ A ⧸ J := QuotientAddGroup.mk' J
      change ∃ hbar : LayerSubsumChoice
          (B.image qJ :: P.map fun C ↦ C.image qJ) (n + 1) (qJ (b + y)),
        ∀ r : (A ⧸ J) ⧸ K.map qJ,
          hbar.quotientMultiplicity (K.map qJ) r =
            (LayerSubsumChoice.take hb h).quotientMultiplicity K
              ((QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r)
      obtain ⟨hbarTail, hbarTailMult⟩ := ih
      let Kbar : AddSubgroup (A ⧸ J) := K.map qJ
      let hraw : LayerSubsumChoice
          (B.image qJ :: P.map fun C ↦ C.image qJ) (n + 1)
          (qJ b + qJ y) :=
        LayerSubsumChoice.take
          (Finset.mem_image.mpr ⟨b, hb, rfl⟩) hbarTail
      have hsum : qJ b + qJ y = qJ (b + y) := (qJ.map_add b y).symm
      let hbar : LayerSubsumChoice
          (B.image qJ :: P.map fun C ↦ C.image qJ) (n + 1)
          (qJ (b + y)) := hsum ▸ hraw
      refine ⟨hbar, ?_⟩
      intro r
      have hcast : hbar.quotientMultiplicity Kbar r =
          hraw.quotientMultiplicity Kbar r := by
        exact LayerSubsumChoice.quotientMultiplicity_cast hsum hraw r
      rw [hcast]
      change
        (if (((b : A ⧸ J) :
              (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) = r)
            then 1 else 0) +
            hbarTail.quotientMultiplicity
              (K.map (QuotientAddGroup.mk' J)) r =
          (if (b : A ⧸ K) =
              (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r
            then 1 else 0) +
            h.quotientMultiplicity K
              ((QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r)
      rw [hbarTailMult r]
      by_cases hbq : (((b : A ⧸ J) :
          (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) = r)
      · have hbq' : (b : A ⧸ K) =
            (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r :=
          (mk_ambientQuotient_eq_iff J K hJK b r).1 hbq
        simp [hbq, hbq']
      · have hbq' : (b : A ⧸ K) ≠
            (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r :=
          (mk_ambientQuotient_eq_iff J K hJK b r).not.mp hbq
        simp [hbq, hbq']

/-- Conversely, every proof-relevant choice in quotient-image layers lifts
to a choice in the original labelled layers, with the same induced pattern.
Surjectivity is used only through literal membership in each `Finset.image`.
-/
theorem LayerSubsumChoice.exists_lift_ambientQuotient
    (J K : AddSubgroup A) [DecidableEq (A ⧸ J)]
    [DecidableEq ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    [DecidableEq (A ⧸ K)] (hJK : J ≤ K)
    {P : List (Finset A)} {n : ℕ} {z : A ⧸ J}
    (hbar : LayerSubsumChoice
      (P.map fun C ↦ C.image (QuotientAddGroup.mk' J)) n z) :
    ∃ y : A, ∃ h : LayerSubsumChoice P n y,
      QuotientAddGroup.mk' J y = z ∧
      ∀ r : (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J),
        hbar.quotientMultiplicity
            (K.map (QuotientAddGroup.mk' J)) r =
          h.quotientMultiplicity K
            ((QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r) := by
  induction P generalizing n z with
  | nil =>
      cases hbar with
      | zero =>
          refine ⟨0, LayerSubsumChoice.zero [], by simp, ?_⟩
          intro r
          simp [LayerSubsumChoice.quotientMultiplicity]
  | cons B P ih =>
      change LayerSubsumChoice
        (B.image (QuotientAddGroup.mk' J) ::
          P.map fun C ↦ C.image (QuotientAddGroup.mk' J)) n z at hbar
      cases hbar with
      | zero =>
          refine ⟨0, LayerSubsumChoice.zero (B :: P), by simp, ?_⟩
          intro r
          simp [LayerSubsumChoice.quotientMultiplicity]
      | skip htail =>
          obtain ⟨y, h, hy, hmult⟩ := ih htail
          refine ⟨y, LayerSubsumChoice.skip h, hy, ?_⟩
          intro r
          simpa [LayerSubsumChoice.quotientMultiplicity] using hmult r
      | @take _ _ k bbar ztail hbbar htail =>
          obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hbbar
          obtain ⟨y, h, hy, hmult⟩ := ih htail
          refine ⟨b + y, LayerSubsumChoice.take hb h, ?_, ?_⟩
          · rw [map_add]
            exact congrArg (fun t : A ⧸ J ↦ (b : A ⧸ J) + t) hy
          · intro r
            change
              (if (((b : A ⧸ J) :
                    (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) = r)
                  then 1 else 0) +
                  htail.quotientMultiplicity
                    (K.map (QuotientAddGroup.mk' J)) r =
                (if (b : A ⧸ K) =
                    (QuotientAddGroup.quotientQuotientEquivQuotient
                      J K hJK) r then 1 else 0) +
                  h.quotientMultiplicity K
                    ((QuotientAddGroup.quotientQuotientEquivQuotient
                      J K hJK) r)
            rw [hmult r]
            by_cases hbq : (((b : A ⧸ J) :
                (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) = r)
            · have hbq' : (b : A ⧸ K) =
                  (QuotientAddGroup.quotientQuotientEquivQuotient
                    J K hJK) r :=
                (mk_ambientQuotient_eq_iff J K hJK b r).1 hbq
              simp [hbq, hbq']
            · have hbq' : (b : A ⧸ K) ≠
                  (QuotientAddGroup.quotientQuotientEquivQuotient
                    J K hJK) r :=
                (mk_ambientQuotient_eq_iff J K hJK b r).not.mp hbq
              simp [hbq, hbq']
/-- The pattern on `(A/J)/(K/J)` corresponding through the third
isomorphism theorem to a pattern on `A/K`. -/
noncomputable def QuotientPattern.ambientQuotient
    (J K : AddSubgroup A) (hJK : J ≤ K) {n : ℕ}
    [Fintype (A ⧸ K)] [Fintype ((A ⧸ J) ⧸
      K.map (QuotientAddGroup.mk' J))]
    (mu : QuotientPattern K n) :
    QuotientPattern (K.map (QuotientAddGroup.mk' J)) n where
  multiplicity := fun r ↦
    mu ((QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r)
  weight_eq := by
    classical
    let e : ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) ≃
        A ⧸ K :=
      (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK).toEquiv
    calc
      (∑ r, mu (e r)) = ∑ q : A ⧸ K, mu q := by
        exact Fintype.sum_equiv e _ _ (fun _ ↦ rfl)
      _ = n := mu.weight_eq

@[simp]
theorem QuotientPattern.ambientQuotient_apply
    (J K : AddSubgroup A) (hJK : J ≤ K) {n : ℕ}
    [Fintype (A ⧸ K)] [Fintype ((A ⧸ J) ⧸
      K.map (QuotientAddGroup.mk' J))]
    (mu : QuotientPattern K n)
    (r : (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) :
    mu.ambientQuotient J K hJK r =
      mu ((QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r) := rfl

/-- Prescribed-pattern spectra commute exactly with quotienting the ambient
group by a subgroup of the pattern subgroup.  Both inclusions transport the
proof-relevant labelled-layer choice, rather than only raw spectrum
membership. -/
theorem image_patternSubsumSpectrum_ambientQuotient
    [Fintype A] (J K : AddSubgroup A) [DecidableEq (A ⧸ J)]
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    [Fintype ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    [DecidableEq ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    (hJK : J ≤ K) (P : List (Finset A)) {n : ℕ}
    (mu : QuotientPattern K n) :
    (patternSubsumSpectrum P mu).image (QuotientAddGroup.mk' J) =
      patternSubsumSpectrum
        (P.map fun B ↦ B.image (QuotientAddGroup.mk' J))
        (mu.ambientQuotient J K hJK) := by
  classical
  let qJ : A →+ A ⧸ J := QuotientAddGroup.mk' J
  let Kbar : AddSubgroup (A ⧸ J) := K.map qJ
  let e : ((A ⧸ J) ⧸ Kbar) ≃+ A ⧸ K :=
    QuotientAddGroup.quotientQuotientEquivQuotient J K hJK
  ext z
  constructor
  · intro hz
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hz
    obtain ⟨⟨h, hmu⟩⟩ :=
      (mem_patternSubsumSpectrum_iff P mu y).1 hy
    obtain ⟨hbar, hmult⟩ :=
      h.exists_map_ambientQuotient J K hJK
    apply (mem_patternSubsumSpectrum_iff _
      (mu.ambientQuotient J K hJK) (qJ y)).2
    refine ⟨⟨hbar, ?_⟩⟩
    intro r
    calc
      hbar.quotientMultiplicity Kbar r =
          h.quotientMultiplicity K (e r) := hmult r
      _ = mu (e r) := hmu (e r)
      _ = mu.ambientQuotient J K hJK r := rfl
  · intro hz
    obtain ⟨⟨hbar, hbarmu⟩⟩ :=
      (mem_patternSubsumSpectrum_iff _
        (mu.ambientQuotient J K hJK) z).1 hz
    obtain ⟨y, h, hy, hmult⟩ :=
      hbar.exists_lift_ambientQuotient J K hJK
    apply Finset.mem_image.mpr
    refine ⟨y, (mem_patternSubsumSpectrum_iff P mu y).2 ?_, hy⟩
    refine ⟨⟨h, ?_⟩⟩
    intro q
    let r : (A ⧸ J) ⧸ Kbar := e.symm q
    calc
      h.quotientMultiplicity K q =
          h.quotientMultiplicity K (e r) := by simp [r]
      _ = hbar.quotientMultiplicity Kbar r := (hmult r).symm
      _ = mu.ambientQuotient J K hJK r := hbarmu r
      _ = mu q := by simp [QuotientPattern.ambientQuotient, r, e, Kbar]

/-- Raw multiplicity in quotient-image layers is exactly layer-incidence
multiplicity modulo the subgroup used for the ambient quotient. -/
theorem rawLayerMultiplicity_image_quotient_eq
    (J : AddSubgroup A) [DecidableEq (A ⧸ J)]
    (P : List (Finset A)) (z : A ⧸ J) :
    rawLayerMultiplicity
        (P.map fun B ↦ B.image (QuotientAddGroup.mk' J)) z =
      quotientLayerMultiplicity J P z := by
  classical
  induction P with
  | nil => simp [rawLayerMultiplicity, quotientLayerMultiplicity]
  | cons B P ih =>
      by_cases hz : z ∈ B.image (QuotientAddGroup.mk' J)
      · have hzq : z ∈ quotientLayer J B := by
          simpa [quotientLayer] using hz
        rw [List.map_cons,
          rawLayerMultiplicity_cons_of_mem _ _ _ hz,
          quotientLayerMultiplicity_cons_of_mem J B P z hzq, ih]
      · have hzq : z ∉ quotientLayer J B := by
          simpa [quotientLayer] using hz
        rw [List.map_cons,
          rawLayerMultiplicity_cons_of_not_mem _ _ _ hz,
          quotientLayerMultiplicity_cons_of_not_mem J B P z hzq, ih]

/-- Target-stabilizer capped incidence becomes raw capped incidence after
quotienting every layer by that stabilizer. -/
theorem rawDgmCappedMultiplicitySum_image_quotient_eq
    [Fintype A] (J : AddSubgroup A) [Fintype (A ⧸ J)]
    [DecidableEq (A ⧸ J)] (P : List (Finset A)) (n : ℕ) :
    @rawDgmCappedMultiplicitySum (A ⧸ J) inferInstance
        (Fintype.ofFinite (A ⧸ J))
        (P.map fun B ↦ B.image (QuotientAddGroup.mk' J)) n =
      dgmCappedMultiplicitySum J P n := by
  classical
  unfold rawDgmCappedMultiplicitySum dgmCappedMultiplicitySum
  simp_rw [rawLayerMultiplicity_image_quotient_eq J P]

/-- Pointwise pattern-subgroup incidence is unchanged by the ambient
quotient, after identifying `(A/J)/(K/J)` with `A/K`. -/
theorem quotientLayerMultiplicity_image_ambientQuotient_eq
    (J K : AddSubgroup A) [DecidableEq (A ⧸ J)]
    [DecidableEq ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    [DecidableEq (A ⧸ K)] (hJK : J ≤ K)
    (P : List (Finset A))
    (r : (A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) :
    quotientLayerMultiplicity (K.map (QuotientAddGroup.mk' J))
        (P.map fun B ↦ B.image (QuotientAddGroup.mk' J)) r =
      quotientLayerMultiplicity K P
        ((QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r) := by
  induction P with
  | nil => simp [quotientLayerMultiplicity]
  | cons B P ih =>
      by_cases hr : r ∈ quotientLayer
          (K.map (QuotientAddGroup.mk' J))
          (B.image (QuotientAddGroup.mk' J))
      · have hre :
            (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r ∈
              quotientLayer K B :=
          (mem_quotientLayer_image_ambientQuotient_iff
            J K hJK B r).1 hr
        rw [List.map_cons,
          quotientLayerMultiplicity_cons_of_mem _ _ _ _ hr,
          quotientLayerMultiplicity_cons_of_mem K B P _ hre, ih]
      · have hre :
            (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK) r ∉
              quotientLayer K B := by
          exact (mem_quotientLayer_image_ambientQuotient_iff
            J K hJK B r).not.mp hr
        rw [List.map_cons,
          quotientLayerMultiplicity_cons_of_not_mem _ _ _ _ hr,
          quotientLayerMultiplicity_cons_of_not_mem K B P _ hre, ih]

/-- The `K/J` capped correction term in the quotient theorem is exactly the
original `K` capped correction term. -/
theorem dgmCappedMultiplicitySum_image_ambientQuotient_eq
    [Fintype A] (J K : AddSubgroup A) [DecidableEq (A ⧸ J)]
    [Fintype (A ⧸ K)] [DecidableEq (A ⧸ K)]
    [Fintype ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    [DecidableEq ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    (hJK : J ≤ K) (P : List (Finset A)) (n : ℕ) :
    dgmCappedMultiplicitySum (K.map (QuotientAddGroup.mk' J))
        (P.map fun B ↦ B.image (QuotientAddGroup.mk' J)) n =
      dgmCappedMultiplicitySum K P n := by
  classical
  letI : Fintype (A ⧸ K) := Fintype.ofFinite (A ⧸ K)
  letI : Fintype ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) :=
    Fintype.ofFinite ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))
  let e : ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J)) ≃
      A ⧸ K :=
    (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK).toEquiv
  unfold dgmCappedMultiplicitySum
  exact Fintype.sum_equiv e
    (fun r ↦ min n (quotientLayerMultiplicity
      (K.map (QuotientAddGroup.mk' J))
      (P.map fun B ↦ B.image (QuotientAddGroup.mk' J)) r))
    (fun q ↦ min n (quotientLayerMultiplicity K P q))
    (fun r ↦ by
      rw [quotientLayerMultiplicity_image_ambientQuotient_eq J K hJK P r]
      rfl)

/-- A finite nonempty set is a disjoint union of full stabilizer fibers, so
its cardinal is the stabilizer cardinal times the cardinal of its image in
the stabilizer quotient. -/
theorem natCard_stabilizer_mul_card_image_quotient
    [Fintype A] (T : Finset A) (hT : T.Nonempty) :
    Nat.card (AddAction.stabilizer A (T : Set A)) *
        (T.image (QuotientAddGroup.mk'
          (AddAction.stabilizer A (T : Set A)))).card =
      T.card := by
  have h := Finset.card_addStab_add_card_image_coe' T T
  rw [card_addStab_eq_natCard_stabilizer T hT] at h
  simpa using h

/-- For `J ≤ K`, the image subgroup `K/J` has the expected cardinal.
The proof uses the third isomorphism theorem plus the three ambient Lagrange
factorizations, avoiding a separate hand-built equivalence `K/J ≃ Kbar`.
-/
theorem natCard_mul_natCard_map_quotient
    [Fintype A] (J K : AddSubgroup A) (hJK : J ≤ K) :
    Nat.card J * Nat.card (K.map (QuotientAddGroup.mk' J)) =
      Nat.card K := by
  let qJ : A →+ A ⧸ J := QuotientAddGroup.mk' J
  let Kbar : AddSubgroup (A ⧸ J) := K.map qJ
  let e : ((A ⧸ J) ⧸ Kbar) ≃ A ⧸ K :=
    (QuotientAddGroup.quotientQuotientEquivQuotient J K hJK).toEquiv
  have hAJ := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup J
  have hAK := AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup K
  have hAJK :=
    AddSubgroup.card_eq_card_quotient_mul_card_addSubgroup Kbar
  have he : Nat.card ((A ⧸ J) ⧸ Kbar) = Nat.card (A ⧸ K) :=
    Nat.card_congr e
  have hfactor : Nat.card A =
      Nat.card (A ⧸ K) * (Nat.card Kbar * Nat.card J) := by
    calc
      Nat.card A = Nat.card (A ⧸ J) * Nat.card J := hAJ
      _ = (Nat.card ((A ⧸ J) ⧸ Kbar) * Nat.card Kbar) *
          Nat.card J := by rw [hAJK]
      _ = (Nat.card (A ⧸ K) * Nat.card Kbar) * Nat.card J := by
        rw [he]
      _ = Nat.card (A ⧸ K) *
          (Nat.card Kbar * Nat.card J) := by simp [Nat.mul_assoc]
  have hmul : Nat.card (A ⧸ K) * Nat.card K =
      Nat.card (A ⧸ K) * (Nat.card Kbar * Nat.card J) :=
    hAK.symm.trans hfactor
  have hc : Nat.card K = Nat.card Kbar * Nat.card J :=
    Nat.mul_left_cancel Nat.card_pos hmul
  exact (Nat.mul_comm _ _).trans hc.symm

end GaoLean
