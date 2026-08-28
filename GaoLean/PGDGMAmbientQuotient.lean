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

/-- Instance-polymorphic form of the preceding equality.  This is useful
inside a theorem whose quotient `Fintype` instance is already fixed by a
projected pattern. -/
theorem rawDgmCappedMultiplicitySum_image_quotient_eq'
    [Fintype A] (J : AddSubgroup A) [Fintype (A ⧸ J)]
    [DecidableEq (A ⧸ J)] (P : List (Finset A)) (n : ℕ) :
    rawDgmCappedMultiplicitySum
        (P.map fun B ↦ B.image (QuotientAddGroup.mk' J)) n =
      dgmCappedMultiplicitySum J P n := by
  classical
  unfold rawDgmCappedMultiplicitySum dgmCappedMultiplicitySum
  simp_rw [rawLayerMultiplicity_image_quotient_eq J P]
  congr 1
  ext z
  simp

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

/-- `Finset.image` is propositionally independent of the chosen
`DecidableEq` instance on its codomain. -/
theorem finset_image_eq_of_decidableEq
    {X Y : Type*} (d₁ d₂ : DecidableEq Y) (f : X → Y) (s : Finset X) :
    @Finset.image X Y d₁ f s = @Finset.image X Y d₂ f s := by
  ext y
  simp

/-- Lift the generalized DGM inequality from the quotient by the complete
stabilizer of its target spectrum.  No combinatorial DGM input is hidden
here: the sole substantive premise is the already-proved quotient bound.
-/
theorem dgmPatternBound_of_ambientStabilizerQuotient
    [Fintype A] (J K : AddSubgroup A) [Fintype (A ⧸ J)]
    [DecidableEq (A ⧸ J)] [Fintype (A ⧸ K)]
    [DecidableEq (A ⧸ K)]
    [Fintype ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    [DecidableEq ((A ⧸ J) ⧸ K.map (QuotientAddGroup.mk' J))]
    (hJK : J ≤ K) (P : List (Finset A)) {n : ℕ}
    (mu : QuotientPattern K n)
    (hT : (patternSubsumSpectrum P mu).Nonempty)
    (hJ : J = AddAction.stabilizer A
      (patternSubsumSpectrum P mu : Set A))
    (hQ : DGMPatternBound
      (P.map fun B ↦ B.image (QuotientAddGroup.mk' J))
      (mu.ambientQuotient J K hJK)) :
    DGMPatternBound P mu := by
  classical
  subst J
  let J : AddSubgroup A := AddAction.stabilizer A
    (patternSubsumSpectrum P mu : Set A)
  let T : Finset A := patternSubsumSpectrum P mu
  let qJ : A →+ A ⧸ J := QuotientAddGroup.mk' J
  let q0 : A →+ A ⧸ AddAction.stabilizer A
      (patternSubsumSpectrum P mu : Set A) :=
    QuotientAddGroup.mk' _
  let Pbar : List (Finset (A ⧸ J)) :=
    P.map fun B ↦ B.image qJ
  let Kbar : AddSubgroup (A ⧸ J) := K.map qJ
  let mubar : QuotientPattern Kbar n := mu.ambientQuotient J K hJK
  let Tbar : Finset (A ⧸ J) := patternSubsumSpectrum Pbar mubar
  have hspec : Tbar = T.image qJ := by
    simpa [T, Tbar, Pbar, Kbar, mubar, qJ] using
      (image_patternSubsumSpectrum_ambientQuotient
        J K hJK P mu).symm
  have hTbar : Tbar.Nonempty := by
    rw [hspec]
    exact hT.image qJ
  have himageEq : T.image qJ = T.image q0 := by
    ext z
    simp [T, qJ, q0, J]
  have hdec : (inferInstance : DecidableEq
      (A ⧸ AddAction.stabilizer A
        (patternSubsumSpectrum P mu : Set A))) =
      QuotientAddGroup.instDecidableEqQuotientAddSubgroupOfDecidablePredMem _ :=
    Subsingleton.elim _ _
  cases hdec
  have hTbarStab : Tbar.addStab = {0} := by
    change Tbar.addStab = (0 : Finset (A ⧸ J))
    rw [hspec, himageEq]
    have himage := Finset.addStab_image_coe_quotient hT
    simpa [T, q0, J] using himage
  have hTbarGroupCard :
      Nat.card (AddAction.stabilizer (A ⧸ J) (Tbar : Set (A ⧸ J))) = 1 := by
    rw [← card_addStab_eq_natCard_stabilizer Tbar hTbar, hTbarStab]
    simp
  have hTbarCap : stabilizerDgmCappedMultiplicitySum Tbar Pbar n =
      rawDgmCappedMultiplicitySum Pbar n :=
    dgmStabilizerCappedMultiplicitySum_eq_raw_of_addStab_eq_singleton
      Tbar hTbar hTbarStab Pbar n
  have hraw : rawDgmCappedMultiplicitySum Pbar n =
      dgmCappedMultiplicitySum J P n := by
    simpa [Pbar, qJ] using
      rawDgmCappedMultiplicitySum_image_quotient_eq' J P n
  have hKcap : dgmCappedMultiplicitySum Kbar Pbar n =
      dgmCappedMultiplicitySum K P n := by
    simpa [Kbar, Pbar, qJ] using
      dgmCappedMultiplicitySum_image_ambientQuotient_eq J K hJK P n
  have hTcap : stabilizerDgmCappedMultiplicitySum T P n =
      dgmCappedMultiplicitySum J P n := by
    have h := (dgmCappedMultiplicitySum_stabilizer_eq T P n).symm
    simpa [T, J] using h
  have hTcard : Nat.card J * Tbar.card = T.card := by
    rw [hspec, himageEq]
    have h := natCard_stabilizer_mul_card_image_quotient T hT
    simpa [T, J, q0] using h
  have hKcard : Nat.card J * Nat.card Kbar = Nat.card K := by
    simpa [Kbar, qJ] using natCard_mul_natCard_map_quotient J K hJK
  unfold DGMPatternBound at hQ
  dsimp only at hQ
  have hQ' : Nat.card
        (AddAction.stabilizer (A ⧸ J) (Tbar : Set (A ⧸ J))) *
      (stabilizerDgmCappedMultiplicitySum Tbar Pbar n - n + 1) ≤
        Tbar.card + Nat.card Kbar *
          (dgmCappedMultiplicitySum Kbar Pbar n - n) := by
    simpa [Tbar, mubar, Kbar, Pbar, qJ, J] using hQ
  rw [hTbarGroupCard, one_mul, hTbarCap, hraw, hKcap] at hQ'
  have hmul := Nat.mul_le_mul_left (Nat.card J) hQ'
  unfold DGMPatternBound
  dsimp only
  change Nat.card (AddAction.stabilizer A (T : Set A)) *
      (stabilizerDgmCappedMultiplicitySum T P n - n + 1) ≤
        T.card + Nat.card K * (dgmCappedMultiplicitySum K P n - n)
  rw [hTcap]
  calc
    Nat.card J * (dgmCappedMultiplicitySum J P n - n + 1) ≤
        Nat.card J *
          (Tbar.card + Nat.card Kbar *
            (dgmCappedMultiplicitySum K P n - n)) := hmul
    _ = T.card + Nat.card K *
          (dgmCappedMultiplicitySum K P n - n) := by
      rw [Nat.mul_add, hTcard, ← Nat.mul_assoc, hKcard]

/-- Quotienting a finite additive group by a nontrivial subgroup strictly
decreases its cardinality. -/
theorem natCard_quotient_lt_of_ne_bot [Fintype A]
    (J : AddSubgroup A) (hJ : J ≠ ⊥) :
    Nat.card (A ⧸ J) < Nat.card A := by
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hJone : Nat.card J ≠ 1 := by
    simpa using hJ
  have hJgt : 1 < Nat.card J := by omega
  rw [J.card_eq_card_quotient_mul_card_addSubgroup]
  exact lt_mul_of_one_lt_right Nat.card_pos hJgt

/-- The generalized pattern theorem restricted to targets with trivial
stabilizer.  This remains an explicit input to the outer quotient driver. -/
def AperiodicGeneralDGMPatternTheorem
    (A : Type*) [AddCommGroup A] [Fintype A] [DecidableEq A] : Prop :=
  ∀ (K : AddSubgroup A) (n : ℕ)
    (_ : Fintype (A ⧸ K)) (_ : DecidableEq (A ⧸ K))
    (P : List (Finset A)) (μ : QuotientPattern K n),
    (patternSubsumSpectrum P μ).Nonempty →
    (patternSubsumSpectrum P μ).addStab = {0} →
    DGMPatternBound P μ

/-- Universe-polymorphic outer induction predicate, indexed only by the
finite cardinality of the ambient group. -/
def DGMPatternAtGroupCard (m : ℕ) : Prop :=
  ∀ (B : Type u) [AddCommGroup B] [Fintype B] [DecidableEq B],
    Nat.card B = m → GeneralDGMPatternTheorem B

/-- Mechanical outer quotient driver.  Its explicit `haper` premise is the
only generalized DGM input: the theorem removes only a nontrivial final
target stabilizer by strong induction on the ambient group cardinality. -/
theorem generalDGMPatternTheorem_of_aperiodic
    (haper : ∀ (B : Type u) [AddCommGroup B] [Fintype B] [DecidableEq B],
      AperiodicGeneralDGMPatternTheorem B) :
    ∀ (B : Type u) [AddCommGroup B] [Fintype B] [DecidableEq B],
      GeneralDGMPatternTheorem B := by
  have outer : ∀ m : ℕ, DGMPatternAtGroupCard.{u} m := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
        intro B _instGroup _instFintype _instDecEq hm
        intro K n instQFintype instQDecEq P μ hT
        let T : Finset B := patternSubsumSpectrum P μ
        let J : AddSubgroup B := AddAction.stabilizer B (T : Set B)
        have hJK : J ≤ K := by
          simpa [J, T] using
            patternSpectrum_stabilizer_le_patternSubgroup K n P μ hT
        by_cases hJbot : J = ⊥
        · apply haper B K n instQFintype instQDecEq P μ hT
          apply Finset.ext
          intro x
          rw [← Finset.mem_coe, Finset.coe_addStab hT]
          change x ∈ J ↔ x ∈ ({0} : Finset B)
          rw [hJbot]
          simp
        · letI : Fintype (B ⧸ J) := Fintype.ofFinite _
          letI : DecidableEq (B ⧸ J) := Classical.decEq _
          let qJ : B →+ B ⧸ J := QuotientAddGroup.mk' J
          let Kbar : AddSubgroup (B ⧸ J) := K.map qJ
          letI : Fintype ((B ⧸ J) ⧸ Kbar) := Fintype.ofFinite _
          letI : DecidableEq ((B ⧸ J) ⧸ Kbar) := Classical.decEq _
          let Pbar : List (Finset (B ⧸ J)) :=
            P.map fun C ↦ C.image qJ
          let μbar : QuotientPattern Kbar n :=
            μ.ambientQuotient J K hJK
          have hsmall : Nat.card (B ⧸ J) < m := by
            rw [← hm]
            exact natCard_quotient_lt_of_ne_bot J hJbot
          have hgeneralBar : GeneralDGMPatternTheorem (B ⧸ J) :=
            ih (Nat.card (B ⧸ J)) hsmall (B ⧸ J) rfl
          have hTbar : (patternSubsumSpectrum Pbar μbar).Nonempty := by
            have himage := hT.image qJ
            rw [image_patternSubsumSpectrum_ambientQuotient
              J K hJK P μ] at himage
            simpa [Pbar, μbar, Kbar, qJ] using himage
          have hQ : DGMPatternBound Pbar μbar :=
            hgeneralBar Kbar n inferInstance inferInstance Pbar μbar hTbar
          exact dgmPatternBound_of_ambientStabilizerQuotient
            J K hJK P μ hT (by simp [J, T]) (by
              simpa [Pbar, μbar, Kbar, qJ] using hQ)
  intro B _instGroup _instFintype _instDecEq
  exact outer (Nat.card B) B rfl

/-- Setpartition endpoint of the same outer driver.  The only unresolved
mathematical input remains the explicitly displayed aperiodic generalized
pattern theorem. -/
theorem generalDGMSetpartitionTheorem_of_aperiodicPattern
    (haper : ∀ (B : Type u) [AddCommGroup B] [Fintype B] [DecidableEq B],
      AperiodicGeneralDGMPatternTheorem B) :
    ∀ (B : Type u) [AddCommGroup B] [Fintype B] [DecidableEq B],
      GeneralDGMSetpartitionTheorem B := by
  intro B _instGroup _instFintype _instDecEq
  exact generalDGMSetpartitionTheorem_of_generalPatternTheorem
    (generalDGMPatternTheorem_of_aperiodic haper B)

end GaoLean
