import GaoLean.PGGMOClaimBCounting
import GaoLean.PGGMOClaimBSubgroup
import GaoLean.PGGMOClaimBIndexing
import GaoLean.PGGMOClaimBCase1Inputs

/-!
# Exact saturation for ordinary GMO Claim B

This module supplies the additive-combinatorial part of the Claim-B
saturation argument.  A thick pair in one common-core `H`-fiber first
covers a full `H`-coset.  Further genuine core cells pad that block, and
affine spanning in the generated quotient subgroup `L` is lifted back to
the intermediate subgroup `K`.

No saturation statement is assumed.  The final cell indexing is kept
separate: it is supplied by `PGGMOClaimBIndexing` once the four concrete
blocks of distinct original cells are available.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

noncomputable local instance saturationQuotientFintype (H : AddSubgroup A) :
    Fintype (A ⧸ H) := Fintype.ofFinite (A ⧸ H)

section FiniteCosetAddition

/-- Two finite subsets of prescribed additive cosets add inside the sum
coset. -/
theorem finset_add_subset_addCosetFinset
    (H : AddSubgroup A) (a b : A) (X Y : Finset A)
    (hX : X ⊆ addCosetFinset H a)
    (hY : Y ⊆ addCosetFinset H b) :
    X + Y ⊆ addCosetFinset H (a + b) := by
  classical
  intro z hz
  obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
  have hxH : x - a ∈ H := (mem_addCosetFinset_iff H a x).1 (hX hx)
  have hyH : y - b ∈ H := (mem_addCosetFinset_iff H b y).1 (hY hy)
  apply (mem_addCosetFinset_iff H (a + b) (x + y)).2
  convert H.add_mem hxH hyH using 1 <;> abel

/-- Elementary finite-group pigeonhole: two subsets of cosets whose
cardinalities sum to more than `|H|` fill the sum coset. -/
theorem finset_add_eq_addCosetFinset_of_card_lt_add
    (H : AddSubgroup A) (a b : A) (X Y : Finset A)
    (hX : X ⊆ addCosetFinset H a)
    (hY : Y ⊆ addCosetFinset H b)
    (hcard : Nat.card H < X.card + Y.card) :
    X + Y = addCosetFinset H (a + b) := by
  classical
  apply Finset.Subset.antisymm
  · exact finset_add_subset_addCosetFinset H a b X Y hX hY
  · intro z hz
    by_contra hzsum
    let Z : Finset A := Y.image fun y ↦ z - y
    have hZcard : Z.card = Y.card := by
      dsimp [Z]
      rw [Finset.card_image_of_injective]
      intro x y hxy
      exact sub_right_injective hxy
    have hdisjoint : Disjoint X Z := by
      rw [Finset.disjoint_left]
      intro x hx hxZ
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hxZ
      apply hzsum
      apply Finset.mem_add.mpr
      refine ⟨x, hx, y, hy, ?_⟩
      rw [← hyx]
      abel
    have hZ : Z ⊆ addCosetFinset H a := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.mp hx
      have hzH : z - (a + b) ∈ H :=
        (mem_addCosetFinset_iff H (a + b) z).1 hz
      have hyH : y - b ∈ H :=
        (mem_addCosetFinset_iff H b y).1 (hY hy)
      apply (mem_addCosetFinset_iff H a x).2
      rw [← hyx]
      convert H.sub_mem hzH hyH using 1 <;> abel
    have hunion : X ∪ Z ⊆ addCosetFinset H a :=
      Finset.union_subset hX hZ
    have hle : X.card + Z.card ≤ Nat.card H := by
      calc
        X.card + Z.card = (X ∪ Z).card :=
          (Finset.card_union_of_disjoint hdisjoint).symm
        _ ≤ (addCosetFinset H a).card := Finset.card_le_card hunion
        _ = Nat.card H := card_addCosetFinset H a
    rw [hZcard] at hle
    omega

end FiniteCosetAddition

section CommonCoreFiber

/-- A fiber above the common-core class of `g` lies in the literal
common-core part of the cell. -/
theorem Theorem21SetPartition.cosetValueSlice_subset_coreValueCell
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (g : A)
    (hg : g ∈ P.commonCore H) :
    P.cosetValueSlice H c (QuotientAddGroup.mk' H g) ⊆
      P.coreValueCell H c := by
  classical
  intro x hx
  have hx' := (P.mem_cosetValueSlice_iff H c
    (QuotientAddGroup.mk' H g) x).1 hx
  have hxH : x - g ∈ H :=
    QuotientAddGroup.eq_iff_sub_mem.mp hx'.2
  have hxCore : x ∈ P.commonCore H := by
    have hadd := P.add_mem_commonCore H hxH hg
    simpa [sub_add_cancel] using hadd
  exact (P.mem_coreValueCell_iff H c x).2 ⟨hx'.1, hxCore⟩

/-- The same fiber lies in the literal coset `g + H`. -/
theorem Theorem21SetPartition.cosetValueSlice_subset_addCosetFinset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (c : Fin n) (g : A) :
    P.cosetValueSlice H c (QuotientAddGroup.mk' H g) ⊆
      addCosetFinset H g := by
  classical
  intro x hx
  have hxq := (P.mem_cosetValueSlice_iff H c
    (QuotientAddGroup.mk' H g) x).1 hx |>.2
  exact (mem_addCosetFinset_iff H g x).2
    (QuotientAddGroup.eq_iff_sub_mem.mp hxq)

/-- The paper's thick-pair inequality gives an exact full `H`-coset
sum for the two literal quotient fibers. -/
theorem Theorem21SetPartition.cosetValueSlice_add_eq_two_g_addCoset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (j k : Fin n)
    (hthick : Nat.card H + 1 ≤
      (P.cosetValueSlice H j (QuotientAddGroup.mk' H g)).card +
        (P.cosetValueSlice H k (QuotientAddGroup.mk' H g)).card) :
    P.cosetValueSlice H j (QuotientAddGroup.mk' H g) +
        P.cosetValueSlice H k (QuotientAddGroup.mk' H g) =
      addCosetFinset H (2 • g) := by
  have hcard : Nat.card H <
      (P.cosetValueSlice H j (QuotientAddGroup.mk' H g)).card +
        (P.cosetValueSlice H k (QuotientAddGroup.mk' H g)).card := by
    omega
  simpa [two_nsmul] using
    finset_add_eq_addCosetFinset_of_card_lt_add H g g
      (P.cosetValueSlice H j (QuotientAddGroup.mk' H g))
      (P.cosetValueSlice H k (QuotientAddGroup.mk' H g))
      (P.cosetValueSlice_subset_addCosetFinset H j g)
      (P.cosetValueSlice_subset_addCosetFinset H k g) hcard

/-- Enlarging the two thick fibers to the actual common-core value cells
preserves the full `H`-coset coverage. -/
theorem Theorem21SetPartition.two_g_addCoset_subset_pair_coreValueCell_sum
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H)
    (j k : Fin n)
    (hthick : Nat.card H + 1 ≤
      (P.cosetValueSlice H j (QuotientAddGroup.mk' H g)).card +
        (P.cosetValueSlice H k (QuotientAddGroup.mk' H g)).card) :
    addCosetFinset H (2 • g) ⊆
      P.coreValueCell H j + P.coreValueCell H k := by
  intro z hz
  have hz' : z ∈
      P.cosetValueSlice H j (QuotientAddGroup.mk' H g) +
        P.cosetValueSlice H k (QuotientAddGroup.mk' H g) := by
    rw [P.cosetValueSlice_add_eq_two_g_addCoset H g j k hthick]
    exact hz
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.mem_add.mp hz'
  apply Finset.mem_add.mpr
  exact ⟨x, P.cosetValueSlice_subset_coreValueCell H j g hg hx,
    y, P.cosetValueSlice_subset_coreValueCell H k g hg hy, hxy⟩

end CommonCoreFiber

section RepeatedCenters

/-- Repeating one available element gives its repeated sum in the
corresponding iterated finite sumset. -/
theorem nsmul_mem_iteratedFinsetSum_replicate
    (U : Finset A) {x : A} (hx : x ∈ U) (r : ℕ) :
    r • x ∈ iteratedFinsetSum (List.replicate r U) := by
  induction r with
  | zero => simp [iteratedFinsetSum]
  | succ r ih =>
      simp only [List.replicate_succ, iteratedFinsetSum_cons]
      apply Finset.mem_add.mpr
      refine ⟨x, hx, r • x, ih, ?_⟩
      simpa [succ_nsmul] using (add_comm x (r • x))

/-- Once a full `H`-coset is covered, a block whose quotient layers all
contain `ḡ` pads the center by the block length while retaining full
`H`-coset coverage. -/
theorem addCosetFinset_subset_append_of_repeated_quotient_center
    (H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    (R Q : List (Finset A)) (a g : A) (U : Finset (A ⧸ H))
    (hbase : addCosetFinset H a ⊆ iteratedFinsetSum R)
    (hquot : Q.map (quotientLayer H) = List.replicate Q.length U)
    (hgU : QuotientAddGroup.mk' H g ∈ U) :
    addCosetFinset H (a + Q.length • g) ⊆
      iteratedFinsetSum (R ++ Q) := by
  have hqrep : Q.length • QuotientAddGroup.mk' H g ∈
      iteratedFinsetSum (List.replicate Q.length U) :=
    nsmul_mem_iteratedFinsetSum_replicate U hgU Q.length
  have hq : Q.length • QuotientAddGroup.mk' H g ∈
      iteratedFinsetSum (Q.map (quotientLayer H)) := by
    rw [hquot]
    exact hqrep
  obtain ⟨y, hy, hyq, hlift⟩ :=
    exists_addCosetFinset_subset_iteratedFinsetSum_append_of_quotient_mem
      H R Q a hbase (Q.length • QuotientAddGroup.mk' H g) hq
  intro z hz
  apply hlift
  apply (mem_addCosetFinset_iff H (a + y) z).2
  have hzH : z - (a + Q.length • g) ∈ H :=
    (mem_addCosetFinset_iff H (a + Q.length • g) z).1 hz
  have hyq' : QuotientAddGroup.mk' H y =
      QuotientAddGroup.mk' H (Q.length • g) := by
    simpa using hyq
  have hyH : y - Q.length • g ∈ H :=
    QuotientAddGroup.eq_iff_sub_mem.mp hyq'
  convert H.sub_mem hzH hyH using 1 <;> abel

end RepeatedCenters

section IntermediateLift

/-- Any list of genuine cell indices has the same ordered quotient-layer
ledger: every core value cell projects to the common-core quotient layer. -/
theorem Theorem21SetPartition.map_quotientLayer_coreValueCells
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (cs : List (Fin n)) :
    (cs.map fun c ↦ P.coreValueCell H c).map (quotientLayer H) =
      List.replicate cs.length (quotientLayer H (P.commonCore H)) := by
  classical
  induction cs with
  | nil => rfl
  | cons c cs ih =>
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      rw [P.quotientLayer_coreValueCell_eq_commonCore H c, ih]

/-- A list consisting of actual core value cells has the constant common-
core quotient ledger. -/
theorem Theorem21SetPartition.map_quotientLayer_eq_replicate_of_coreValueCells
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (cells : List (Finset A))
    (hcells : ∀ C ∈ cells, ∃ c : Fin n, C = P.coreValueCell H c) :
    cells.map (quotientLayer H) =
      List.replicate cells.length (quotientLayer H (P.commonCore H)) := by
  induction cells with
  | nil => rfl
  | cons C cells ih =>
      obtain ⟨c, hc⟩ := hcells C (by simp)
      simp only [List.map_cons, List.length_cons, List.replicate_succ]
      rw [hc, P.quotientLayer_coreValueCell_eq_commonCore H c]
      congr 1
      exact ih fun D hD ↦ hcells D (by simp [hD])

/-- Every entry of an embedded ledger is one of the genuine original core
value cells. -/
theorem Theorem21SetPartition.exists_eq_coreValueCell_of_mem_embedded
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) (C : Finset A)
    (hC : C ∈ P.embeddedCoreValueCells H e) :
    ∃ c : Fin n, C = P.coreValueCell H c := by
  obtain ⟨q, hq⟩ : ∃ q : Fin r, P.coreValueCell H (e q) = C := by
    simpa [Theorem21SetPartition.embeddedCoreValueCells] using hC
  exact ⟨e q, hq.symm⟩

/-- Every slice block of the embedded ledger inherits the same quotient-
layer ledger. -/
theorem Theorem21SetPartition.map_quotientLayer_eq_replicate_of_sublist_embedded
    {xs : List A} {n m r : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (e : Fin r ↪ Fin n) (cells : List (Finset A))
    (hsub : ∀ C ∈ cells, C ∈ P.embeddedCoreValueCells H e) :
    cells.map (quotientLayer H) =
      List.replicate cells.length (quotientLayer H (P.commonCore H)) := by
  apply P.map_quotientLayer_eq_replicate_of_coreValueCells H cells
  intro C hC
  exact P.exists_eq_coreValueCell_of_mem_embedded H e C (hsub C hC)

/-- The chosen center class occurs in the common-core quotient layer. -/
theorem Theorem21SetPartition.mk_mem_quotientLayer_commonCore
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H) :
    QuotientAddGroup.mk' H g ∈ quotientLayer H (P.commonCore H) :=
  (mem_quotientLayer_iff H (P.commonCore H) _).2 ⟨g, hg, rfl⟩

/-- A full `H`-coset block followed by sufficiently many genuine common-
core quotient layers covers the corresponding full coset of the generated
intermediate subgroup `K`. -/
theorem claimBIntermediate_addCoset_subset_append_of_affine_quotient
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) [DecidableEq (A ⧸ H)]
    (g : A) (hg : g ∈ P.commonCore H)
    (R Q : List (Finset A)) (a : A)
    (hbase : addCosetFinset H a ⊆ iteratedFinsetSum R)
    (hquot : Q.map (quotientLayer H) =
      List.replicate Q.length (quotientLayer H (P.commonCore H)))
    (hk : pGroupDStar (claimBIntermediateQuotientSubgroup P H g) ≤
      Q.length) :
    addCosetFinset (claimBIntermediateSubgroup P H g)
        (a + Q.length • g) ⊆
      iteratedFinsetSum (R ++ Q) := by
  intro z hz
  let q : A ⧸ H := QuotientAddGroup.mk' H (z - a)
  have hzK : z - (a + Q.length • g) ∈
      claimBIntermediateSubgroup P H g :=
    (mem_addCosetFinset_iff
      (claimBIntermediateSubgroup P H g)
      (a + Q.length • g) z).1 hz
  have hqL : q ∈ addCosetFinset
      (claimBIntermediateQuotientSubgroup P H g)
      (Q.length • QuotientAddGroup.mk' H g) := by
    apply (mem_addCosetFinset_iff
      (claimBIntermediateQuotientSubgroup P H g)
      (Q.length • QuotientAddGroup.mk' H g) q).2
    change QuotientAddGroup.mk' H (z - a) -
        Q.length • QuotientAddGroup.mk' H g ∈
      claimBIntermediateQuotientSubgroup P H g
    have hzK' : QuotientAddGroup.mk' H
        (z - (a + Q.length • g)) ∈
      claimBIntermediateQuotientSubgroup P H g := by
      change QuotientAddGroup.mk' H
        (z - (a + Q.length • g)) ∈
          claimBIntermediateQuotientSubgroup P H g at hzK
      exact hzK
    have heq : QuotientAddGroup.mk' H (z - a) -
          Q.length • QuotientAddGroup.mk' H g =
        QuotientAddGroup.mk' H (z - (a + Q.length • g)) := by
      simp only [map_sub, map_add, map_nsmul]
      abel
    rw [heq]
    exact hzK'
  have hqrep : q ∈ iteratedFinsetSum
      (List.replicate Q.length
        (quotientLayer H (P.commonCore H))) :=
    (quotientLayer_commonCore_affine_spanning
      P H g hg Q.length hk) hqL
  have hq : q ∈ iteratedFinsetSum (Q.map (quotientLayer H)) := by
    rw [hquot]
    exact hqrep
  obtain ⟨y, hy, hyq, hlift⟩ :=
    exists_addCosetFinset_subset_iteratedFinsetSum_append_of_quotient_mem
      H R Q a hbase q hq
  apply hlift
  apply (mem_addCosetFinset_iff H (a + y) z).2
  have hqy : QuotientAddGroup.mk' H (z - a) =
      QuotientAddGroup.mk' H y := by
    exact hyq.symm
  have hdiff : (z - a) - y ∈ H :=
    QuotientAddGroup.eq_iff_sub_mem.mp hqy
  convert hdiff using 1 <;> abel

/-- If every summand lies in `g + K`, their iterated sum lies in the
length-scaled coset. -/
theorem iteratedFinsetSum_subset_addCosetFinset_of_each_subset
    (K : AddSubgroup A) (g : A) (cells : List (Finset A))
    (hcells : ∀ C ∈ cells, C ⊆ addCosetFinset K g) :
    iteratedFinsetSum cells ⊆ addCosetFinset K (cells.length • g) := by
  induction cells with
  | nil =>
      intro z hz
      have hz0 : z = 0 := by simpa using hz
      subst z
      simpa using K.zero_mem
  | cons C cells ih =>
      intro z hz
      obtain ⟨x, hx, y, hy, rfl⟩ := Finset.mem_add.mp hz
      have hxK : x - g ∈ K :=
        (mem_addCosetFinset_iff K g x).1
          (hcells C (by simp) hx)
      have hyK : y - cells.length • g ∈ K :=
        (mem_addCosetFinset_iff K (cells.length • g) y).1
          (ih (fun D hD ↦ hcells D (by simp [hD])) hy)
      apply (mem_addCosetFinset_iff K
        ((C :: cells).length • g) (x + y)).2
      convert K.add_mem hxK hyK using 1 <;> simp [succ_nsmul] <;> abel

/-- Every actual common-core value cell lies in the single intermediate
coset `g + K`. -/
theorem Theorem21SetPartition.coreValueCell_subset_intermediate_addCoset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H)
    (c : Fin n) :
    P.coreValueCell H c ⊆
      addCosetFinset (claimBIntermediateSubgroup P H g) g := by
  intro x hx
  exact commonCore_subset_addCosetFinset_claimBIntermediateSubgroup
    P H g hg ((P.mem_coreValueCell_iff H c x).1 hx |>.2)

/-- Consequently, an ordered list of genuine common-core value cells has
no sums outside the predicted intermediate coset. -/
theorem Theorem21SetPartition.iterated_coreValueCells_subset_intermediate_addCoset
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (H : AddSubgroup A) (g : A) (hg : g ∈ P.commonCore H)
    (cs : List (Fin n)) :
    iteratedFinsetSum (cs.map fun c ↦ P.coreValueCell H c) ⊆
      addCosetFinset (claimBIntermediateSubgroup P H g)
        (cs.length • g) := by
  have hsub := iteratedFinsetSum_subset_addCosetFinset_of_each_subset
    (claimBIntermediateSubgroup P H g) g
    (cs.map fun c ↦ P.coreValueCell H c) (by
      intro C hC
      obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hC
      exact P.coreValueCell_subset_intermediate_addCoset H g hg c)
  simpa using hsub

end IntermediateLift

section ExactSaturation

/-- Exact Claim-B saturation from the paper's thick pair, using only
distinct genuine original cells.  The nontriviality of `H` supplies the two
front positions through the odd `p`-group lower bound; subgroup--quotient
convolution supplies enough remaining positions for affine spanning in
`L`; every leftover position is honest zero-padding inside that affine
argument. -/
theorem Theorem21SetPartition.exists_pairFrontEmbedding_exact_saturation
    {xs : List A} {n m : ℕ} (P : Theorem21SetPartition xs n m)
    (p : ℕ) (hp : p.Prime) (hpTwo : p ≠ 2)
    (hA : IsPGroup p (Multiplicative A))
    (H : AddSubgroup A) (hH : H ≠ ⊥)
    (g : A) (hg : g ∈ P.commonCore H)
    (j k : Fin n) (hjk : j ≠ k)
    (hthick : Nat.card H + 1 ≤
      (P.cosetValueSlice H j (QuotientAddGroup.mk' H g)).card +
        (P.cosetValueSlice H k (QuotientAddGroup.mk' H g)).card)
    (hr : pGroupDStar (claimBIntermediateSubgroup P H g) ≤ n) :
    ∃ e : Fin (pGroupDStar (claimBIntermediateSubgroup P H g)) ↪ Fin n,
      (∀ q : Fin (pGroupDStar (claimBIntermediateSubgroup P H g)),
        (P.insideCoreCell H (e q)).Nonempty) ∧
      P.claimBFrontBlock H e =
        [P.coreValueCell H j, P.coreValueCell H k] ∧
      P.insideCoreEmbeddedIteratedSum H e =
        addCosetFinset (claimBIntermediateSubgroup P H g)
          (pGroupDStar (claimBIntermediateSubgroup P H g) • g) := by
  classical
  let K := claimBIntermediateSubgroup P H g
  let L := claimBIntermediateQuotientSubgroup P H g
  let dH := pGroupDStar H
  let dL := pGroupDStar L
  let r := pGroupDStar K
  let hLen := dH - 2
  let lLen := dL
  let padLen := r - dH - dL
  letI : Nontrivial H :=
    (AddSubgroup.nontrivial_iff_ne_bot H).2 hH
  have hdHtwo : 2 ≤ dH := by
    dsimp [dH]
    exact two_le_pGroupDStar_of_odd_pGroup p hp hpTwo
      (isPGroup_multiplicative_addSubgroup p hA H)
  have hconv : dH + dL ≤ r := by
    simpa [dH, dL, r, K, L] using
      pGroupDStar_H_add_intermediateQuotient_le_intermediate P H g
  have hrtwo : 2 ≤ r := by omega
  have hsum : 2 + hLen + lLen + padLen = r := by
    dsimp [hLen, lLen, padLen]
    omega
  let e : Fin r ↪ Fin n := pairFrontEmbedding hr hrtwo j k hjk
  let front := P.claimBFrontBlock H e
  let hBlock := P.claimBHBlock H e hLen
  let lBlock := P.claimBLBlock H e hLen lLen
  let padBlock := P.claimBPaddingBlock H e hLen lLen padLen
  let qBlock := lBlock ++ padBlock
  let hStage := front ++ hBlock
  have hfrontEq : front =
      [P.coreValueCell H j, P.coreValueCell H k] := by
    simpa [front, e] using
      P.claimBFrontBlock_pairFront H hr hrtwo j k hjk
  have hfront : addCosetFinset H (2 • g) ⊆
      iteratedFinsetSum front := by
    rw [hfrontEq]
    have hzero : P.coreValueCell H k + ({0} : Finset A) =
        P.coreValueCell H k := by
      rw [add_comm, singleton_zero_add_finset]
    simpa only [iteratedFinsetSum_cons, iteratedFinsetSum_nil, hzero] using
      P.two_g_addCoset_subset_pair_coreValueCell_sum H g hg j k hthick
  have hhBlockSub : ∀ C ∈ hBlock,
      C ∈ P.embeddedCoreValueCells H e := by
    intro C hC
    have hdrop : C ∈ (P.embeddedCoreValueCells H e).drop 2 :=
      List.mem_of_mem_take hC
    exact List.mem_of_mem_drop hdrop
  have hhQuot : hBlock.map (quotientLayer H) =
      List.replicate hBlock.length
        (quotientLayer H (P.commonCore H)) :=
    P.map_quotientLayer_eq_replicate_of_sublist_embedded
      H e hBlock hhBlockSub
  have hhLen : hBlock.length = hLen := by
    simpa [hBlock] using P.length_claimBHBlock H e hsum
  have hcenterH : 2 • g + hBlock.length • g = dH • g := by
    rw [hhLen, ← add_nsmul]
    congr 1
    dsimp [hLen]
    omega
  have hHstage0 : addCosetFinset H
      (2 • g + hBlock.length • g) ⊆
      iteratedFinsetSum hStage := by
    exact addCosetFinset_subset_append_of_repeated_quotient_center
      H front hBlock (2 • g) g
      (quotientLayer H (P.commonCore H)) hfront hhQuot
      (P.mk_mem_quotientLayer_commonCore H g hg)
  have hHstage : addCosetFinset H (dH • g) ⊆
      iteratedFinsetSum hStage := by
    rw [← hcenterH]
    exact hHstage0
  have hlBlockSub : ∀ C ∈ lBlock,
      C ∈ P.embeddedCoreValueCells H e := by
    intro C hC
    have hdrop : C ∈
        (P.embeddedCoreValueCells H e).drop (2 + hLen) :=
      List.mem_of_mem_take hC
    exact List.mem_of_mem_drop hdrop
  have hpadBlockSub : ∀ C ∈ padBlock,
      C ∈ P.embeddedCoreValueCells H e := by
    intro C hC
    have hdrop : C ∈
        (P.embeddedCoreValueCells H e).drop (2 + hLen + lLen) :=
      List.mem_of_mem_take hC
    exact List.mem_of_mem_drop hdrop
  have hqBlockSub : ∀ C ∈ qBlock,
      C ∈ P.embeddedCoreValueCells H e := by
    intro C hC
    rcases List.mem_append.mp hC with hC | hC
    · exact hlBlockSub C hC
    · exact hpadBlockSub C hC
  have hqQuot : qBlock.map (quotientLayer H) =
      List.replicate qBlock.length
        (quotientLayer H (P.commonCore H)) :=
    P.map_quotientLayer_eq_replicate_of_sublist_embedded
      H e qBlock hqBlockSub
  have hlLen : lBlock.length = lLen := by
    simpa [lBlock] using P.length_claimBLBlock H e hsum
  have hpadLen : padBlock.length = padLen := by
    simpa [padBlock] using
      P.length_claimBPaddingBlock H e hsum
  have hqLen : qBlock.length = lLen + padLen := by
    simp [qBlock, hlLen, hpadLen]
  have hdLq : dL ≤ qBlock.length := by
    rw [hqLen]
    simp [lLen]
  have hlower0 : addCosetFinset K
      (dH • g + qBlock.length • g) ⊆
      iteratedFinsetSum (hStage ++ qBlock) := by
    exact claimBIntermediate_addCoset_subset_append_of_affine_quotient
      P H g hg hStage qBlock (dH • g) hHstage hqQuot
        (by simpa [dL, L] using hdLq)
  have htotalLen : dH + qBlock.length = r := by
    rw [hqLen]
    dsimp [hLen, lLen, padLen] at hsum ⊢
    omega
  have hcenterK : dH • g + qBlock.length • g = r • g := by
    rw [← add_nsmul, htotalLen]
  have hblocks : hStage ++ qBlock =
      P.embeddedCoreValueCells H e := by
    dsimp [hStage, qBlock, front, hBlock, lBlock, padBlock]
    simpa only [List.append_assoc] using
      P.claimB_blocks_append H e hsum
  have hlower : addCosetFinset K (r • g) ⊆
      iteratedFinsetSum (P.embeddedCoreValueCells H e) := by
    rw [← hcenterK, ← hblocks]
    exact hlower0
  have hupper : iteratedFinsetSum (P.embeddedCoreValueCells H e) ⊆
      addCosetFinset K (r • g) := by
    have hlen : (P.embeddedCoreValueCells H e).length = r :=
      P.length_embeddedCoreValueCells H e
    have hsub := iteratedFinsetSum_subset_addCosetFinset_of_each_subset
      K g (P.embeddedCoreValueCells H e) (by
        intro C hC
        obtain ⟨c, rfl⟩ :=
          P.exists_eq_coreValueCell_of_mem_embedded H e C hC
        exact P.coreValueCell_subset_intermediate_addCoset H g hg c)
    simpa only [hlen] using hsub
  refine ⟨e, ?_, hfrontEq, ?_⟩
  · intro q
    exact P.insideCoreCell_nonempty_of_mem_commonCore H g hg (e q)
  · have hledger : P.insideCoreEmbeddedIteratedSum H e =
        iteratedFinsetSum (P.embeddedCoreValueCells H e) := by
      unfold Theorem21SetPartition.insideCoreEmbeddedIteratedSum
      unfold Theorem21SetPartition.embeddedCoreValueCells
      exact congrArg
        (fun d : DecidableEq A =>
          @iteratedFinsetSum A _ d
            (List.ofFn fun q : Fin r => P.coreValueCell H (e q)))
        (Subsingleton.elim (Classical.decEq A)
          (inferInstance : DecidableEq A))
    have hsaturation : P.insideCoreEmbeddedIteratedSum H e =
        addCosetFinset K (r • g) := by
      rw [hledger]
      exact Finset.Subset.antisymm hupper hlower
    simpa [K, r] using hsaturation

end ExactSaturation

end GaoLean

#print axioms GaoLean.finset_add_eq_addCosetFinset_of_card_lt_add
#print axioms GaoLean.Theorem21SetPartition.two_g_addCoset_subset_pair_coreValueCell_sum
#print axioms GaoLean.addCosetFinset_subset_append_of_repeated_quotient_center
#print axioms GaoLean.claimBIntermediate_addCoset_subset_append_of_affine_quotient
#print axioms GaoLean.iteratedFinsetSum_subset_addCosetFinset_of_each_subset
#print axioms GaoLean.Theorem21SetPartition.iterated_coreValueCells_subset_intermediate_addCoset
#print axioms GaoLean.Theorem21SetPartition.exists_pairFrontEmbedding_exact_saturation
