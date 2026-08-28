import GaoLean.PGGMOClaimBHighMultiplicityAssembly

/-!
# Quotient saturation for the honest high-multiplicity block

This module proves only the internal-quotient part of the proper-subgroup
enlargement.  The two labelled occurrences in every paired cell project to
the same literal two-point set `{a, 0}` in `L / K`, where `a` is the fixed
class of the selected nonzero quotient representative.  That class is
nonzero and generates the internal quotient, so the exact `d* (L / K)` paired
cells saturate the whole internal quotient by ordinary Lemma 4.2.

No lift back to an `A`-valued sumset, remaining-occurrence estimate, or
enlarged Claim-B witness is asserted here.
-/

namespace GaoLean

open scoped BigOperators Pointwise

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- The internal quotient `L / K` for the cyclic high-multiplicity extension.
This is a reducible name for the already constructed honest subgroup data. -/
abbrev OrdinaryGMOClaimBOutput.HighMultiplicityInternalQuotient
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) : Type u :=
  W.highMultiplicityExtensionSubgroup z ⧸
    internalAddSubgroup W.K (W.highMultiplicityExtensionSubgroup z)

/-- The fixed centered representative class in `L / K`. -/
noncomputable def
    OrdinaryGMOClaimBOutput.highMultiplicityInternalRepresentative
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    W.HighMultiplicityInternalQuotient z :=
  QuotientAddGroup.mk'
    (internalAddSubgroup W.K (W.highMultiplicityExtensionSubgroup z))
    (⟨W.quotientRepresentative z - W.g,
      W.centeredRepresentative_mem_extension z⟩ :
      W.highMultiplicityExtensionSubgroup z)

/-- The fixed two-point generator, behind a stable noncomputable interface so
public statements do not require a chosen `DecidableEq` instance. -/
noncomputable def OrdinaryGMOClaimBOutput.pairInternalGenerator
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    Finset (W.HighMultiplicityInternalQuotient z) := by
  classical
  exact {W.highMultiplicityInternalRepresentative z, 0}

/-- Center an ambient value at `g` and project it to `L / K` when it belongs
to the honest extension coset.  The outside branch is used only to make this
a total function; every use on a paired value proves the inside branch. -/
noncomputable def
    OrdinaryGMOClaimBOutput.centeredExtensionQuotientValue
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) (x : A) :
    W.HighMultiplicityInternalQuotient z := by
  classical
  by_cases hx : x - W.g ∈ W.highMultiplicityExtensionSubgroup z
  · exact QuotientAddGroup.mk'
      (internalAddSubgroup W.K (W.highMultiplicityExtensionSubgroup z))
      (⟨x - W.g, hx⟩ : W.highMultiplicityExtensionSubgroup z)
  · exact 0

/-- Every selected high value projects to the fixed representative class. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.highSource_centeredExtension_eq
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    E.W.centeredExtensionQuotientValue z
        (occurrenceValue xs (D.highSource t)) =
      E.W.highMultiplicityInternalRepresentative z := by
  have hL : occurrenceValue xs (D.highSource t) - E.W.g ∈
      E.W.highMultiplicityExtensionSubgroup z :=
    (mem_addCosetFinset_iff
      (E.W.highMultiplicityExtensionSubgroup z) E.W.g _).1
      (D.highSource_value_mem_extensionCoset t)
  simp only [OrdinaryGMOClaimBOutput.centeredExtensionQuotientValue,
    dif_pos hL]
  exact D.highSource_internalQuotient_eq_representative t

/-- Every selected reserve value is genuinely in the zero class of `L / K`.
The proof uses its labelled membership in the old `g + K` reserve. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.reserveSource_centeredExtension_eq_zero
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    E.W.centeredExtensionQuotientValue z
        (occurrenceValue xs (D.reserveSource t)) = 0 := by
  have hcoset :=
    (E.W.partition.mem_unusedInAddCoset_iff E.W.K E.W.g
      (D.reserveSource t)).1 (D.reserve_mem t) |>.2
  have hK : occurrenceValue xs (D.reserveSource t) - E.W.g ∈ E.W.K :=
    (mem_addCosetFinset_iff E.W.K E.W.g _).1 hcoset
  have hL : occurrenceValue xs (D.reserveSource t) - E.W.g ∈
      E.W.highMultiplicityExtensionSubgroup z :=
    E.W.K_le_highMultiplicityExtensionSubgroup z hK
  simp only [OrdinaryGMOClaimBOutput.centeredExtensionQuotientValue,
    dif_pos hL]
  exact (QuotientAddGroup.eq_zero_iff _).2 hK

/-- The literal projection of one genuine paired occurrence cell to `L / K`.
It is defined from the occurrence cell itself, not from an unlabelled source
value set. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCell
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    Finset (E.W.HighMultiplicityInternalQuotient z) := by
  classical
  exact (D.pairCell t).image fun i ↦
    E.W.centeredExtensionQuotientValue z (occurrenceValue xs i)

/-- Each paired cell projects exactly to `{a, 0}`. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCell_eq
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z)
    (t : Fin (E.W.highMultiplicityPairLength z)) :
    D.pairInternalQuotientValueCell t =
      E.W.pairInternalGenerator z := by
  classical
  simp only [OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCell,
    OrdinaryGMOClaimBHighMultiplicityCore.pairCell,
    OrdinaryGMOClaimBOutput.pairInternalGenerator,
    Finset.image_insert, Finset.image_singleton]
  rw [D.highSource_centeredExtension_eq t,
    D.reserveSource_centeredExtension_eq_zero t]

/-- The fixed representative is nonzero; otherwise its ambient class would
force the original selected quotient value `z` to be zero. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.internalRepresentative_ne_zero
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    E.W.highMultiplicityInternalRepresentative z ≠ 0 := by
  intro ha
  have haK : E.W.quotientRepresentative z - E.W.g ∈ E.W.K := by
    have hmem := (QuotientAddGroup.eq_zero_iff _).1 ha
    exact hmem
  apply D.nonzero
  rw [← E.W.centeredQuotientValue_representative z]
  exact (QuotientAddGroup.eq_zero_iff _).2 haK

/-- Under the established first-isomorphism equivalence, the fixed internal
class is exactly the generator `z` of the cyclic quotient subgroup. -/
theorem OrdinaryGMOClaimBOutput.highMultiplicityInternalRepresentative_equiv
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    W.highMultiplicityInternalQuotientEquiv z
        (W.highMultiplicityInternalRepresentative z) =
      (⟨z, AddSubgroup.subset_closure (Set.mem_singleton z)⟩ :
        W.highMultiplicityQuotientSubgroup z) := by
  let x : W.highMultiplicityExtensionSubgroup z :=
    ⟨W.quotientRepresentative z - W.g,
      W.centeredRepresentative_mem_extension z⟩
  have hfirst :
      (QuotientAddGroup.quotientAddEquivOfEq
          (W.highMultiplicityExtensionMap_ker z).symm)
          (QuotientAddGroup.mk'
            (internalAddSubgroup W.K
              (W.highMultiplicityExtensionSubgroup z)) x) =
        QuotientAddGroup.mk' (W.highMultiplicityExtensionMap z).ker x := by
    exact QuotientAddGroup.quotientAddEquivOfEq_mk _ x
  apply Subtype.ext
  change ↑((QuotientAddGroup.quotientKerEquivOfSurjective
      (W.highMultiplicityExtensionMap z)
      (W.highMultiplicityExtensionMap_surjective z))
    ((QuotientAddGroup.quotientAddEquivOfEq
      (W.highMultiplicityExtensionMap_ker z).symm)
      (QuotientAddGroup.mk'
        (internalAddSubgroup W.K (W.highMultiplicityExtensionSubgroup z))
        x))) = z
  rw [hfirst]
  change QuotientAddGroup.mk' W.K x.1 = z
  simpa only [x] using W.centeredQuotientValue_representative z

/-- The singleton fixed representative generates all of `L / K`.  This is
proved by transporting the defining closure induction for `closure {z}`
through the honest first-isomorphism equivalence. -/
theorem OrdinaryGMOClaimBOutput.closure_internalRepresentative_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    AddSubgroup.closure
        ({W.highMultiplicityInternalRepresentative z} :
          Set (W.HighMultiplicityInternalQuotient z)) = ⊤ := by
  apply top_unique
  intro q _
  let Q := W.HighMultiplicityInternalQuotient z
  let H := W.highMultiplicityQuotientSubgroup z
  let e : Q ≃+ H := W.highMultiplicityInternalQuotientEquiv z
  let a : Q := W.highMultiplicityInternalRepresentative z
  let b : H :=
    ⟨z, AddSubgroup.subset_closure (Set.mem_singleton z)⟩
  have hea : e a = b := by
    simpa only [e, a, b] using
      W.highMultiplicityInternalRepresentative_equiv z
  have hq : (e q).1 ∈ AddSubgroup.closure ({z} : Set (A ⧸ W.K)) :=
    (e q).2
  have hind : e.symm (e q) ∈ AddSubgroup.closure ({a} : Set Q) := by
    refine AddSubgroup.closure_induction
      (p := fun y hy ↦
        e.symm (⟨y, hy⟩ : H) ∈
          AddSubgroup.closure ({a} : Set Q))
      (fun y hy ↦ ?_) ?_ (fun x y hx hy hxi hyi ↦ ?_)
      (fun x hx hxi ↦ ?_) hq
    · have hyz : y = z := Set.mem_singleton_iff.mp hy
      have hb : (⟨y, AddSubgroup.subset_closure hy⟩ : H) = b := by
        apply Subtype.ext
        exact hyz
      have hba : e.symm b = a := by
        rw [← hea]
        exact e.symm_apply_apply a
      rw [hb, hba]
      exact AddSubgroup.subset_closure (Set.mem_singleton a)
    · have hz : (⟨0, AddSubgroup.zero_mem H⟩ : H) = 0 := rfl
      rw [hz, e.symm.map_zero]
      exact AddSubgroup.zero_mem _
    · have hxy :
          (⟨x + y, AddSubgroup.add_mem H hx hy⟩ : H) =
            (⟨x, hx⟩ : H) + (⟨y, hy⟩ : H) := rfl
      rw [hxy, e.symm.map_add]
      exact AddSubgroup.add_mem _ hxi hyi
    · have hxneg :
          (⟨-x, AddSubgroup.neg_mem H hx⟩ : H) = -(⟨x, hx⟩ : H) := rfl
      rw [hxneg, e.symm.map_neg]
      exact AddSubgroup.neg_mem _ hxi
  have heq : e.symm (e q) = q := e.symm_apply_apply q
  rw [heq] at hind
  simpa only [a] using hind

/-- The projected paired-cell list, retaining its exact source-derived order. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCells
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    List (Finset (E.W.HighMultiplicityInternalQuotient z)) :=
  List.ofFn fun t : Fin (E.W.highMultiplicityPairLength z) ↦
    D.pairInternalQuotientValueCell t

/-- All projected paired cells are the same literal two-point generating set. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCells_eq_replicate
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    D.pairInternalQuotientValueCells =
      List.replicate (E.W.highMultiplicityPairLength z)
        (E.W.pairInternalGenerator z) := by
  classical
  calc
    D.pairInternalQuotientValueCells =
        List.ofFn (fun _ : Fin (E.W.highMultiplicityPairLength z) ↦
          E.W.pairInternalGenerator z) := by
      unfold OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCells
      exact congrArg List.ofFn
        (funext fun t ↦ D.pairInternalQuotientValueCell_eq t)
    _ = _ := List.ofFn_const _ _

/-- The two-point projected cell generates the internal quotient. -/
theorem OrdinaryGMOClaimBOutput.closure_pairInternalGenerator_eq_top
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    AddSubgroup.closure
        ((W.pairInternalGenerator z :
          Finset (W.HighMultiplicityInternalQuotient z)) :
          Set (W.HighMultiplicityInternalQuotient z)) = ⊤ := by
  classical
  apply top_unique
  intro q _
  have hq : q ∈ AddSubgroup.closure
      ({W.highMultiplicityInternalRepresentative z} :
        Set (W.HighMultiplicityInternalQuotient z)) := by
    rw [W.closure_internalRepresentative_eq_top z]
    trivial
  apply AddSubgroup.closure_mono ?_ hq
  intro x hx
  have hx' : x = W.highMultiplicityInternalRepresentative z :=
    Set.mem_singleton_iff.mp hx
  subst x
  simp [OrdinaryGMOClaimBOutput.pairInternalGenerator]

/-- Iterated sum of the source-derived paired quotient cells, with the
classical finite-set operations hidden from public statements. -/
noncomputable def
    OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientIteratedSum
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    Finset (E.W.HighMultiplicityInternalQuotient z) := by
  classical
  exact iteratedFinsetSum D.pairInternalQuotientValueCells

/-- Literal full finite carrier of `L / K`, again behind a stable interface. -/
noncomputable def OrdinaryGMOClaimBOutput.fullHighMultiplicityInternalQuotient
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    Finset (W.HighMultiplicityInternalQuotient z) := by
  classical
  letI : Fintype (W.HighMultiplicityInternalQuotient z) :=
    Fintype.ofFinite (W.HighMultiplicityInternalQuotient z)
  exact Finset.univ

/-- The full top coset in the internal quotient as a stable finite set. -/
noncomputable def OrdinaryGMOClaimBOutput.fullHighMultiplicityInternalCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    (W : OrdinaryGMOClaimBOutput xs seed n) (z : A ⧸ W.K) :
    Finset (W.HighMultiplicityInternalQuotient z) := by
  classical
  letI : Fintype (W.HighMultiplicityInternalQuotient z) :=
    Fintype.ofFinite (W.HighMultiplicityInternalQuotient z)
  exact addCosetFinset
    (⊤ : AddSubgroup (W.HighMultiplicityInternalQuotient z)) 0

/-- Exact quotient saturation of the genuine paired block.  Its length is
definitionally `d* (L / K)`, and ordinary Lemma 4.2 therefore gives the full
internal quotient. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.iterated_pairInternalQuotientValueCells_eq_univ
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    D.pairInternalQuotientIteratedSum =
      E.W.fullHighMultiplicityInternalQuotient z := by
  classical
  letI : Fintype (E.W.HighMultiplicityInternalQuotient z) :=
    Fintype.ofFinite (E.W.HighMultiplicityInternalQuotient z)
  unfold OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientIteratedSum
  unfold OrdinaryGMOClaimBOutput.fullHighMultiplicityInternalQuotient
  rw [D.pairInternalQuotientValueCells_eq_replicate]
  have hzero : (0 : E.W.HighMultiplicityInternalQuotient z) ∈
      E.W.pairInternalGenerator z := by
    simp [OrdinaryGMOClaimBOutput.pairInternalGenerator]
  have hgen := E.W.closure_pairInternalGenerator_eq_top z
  simpa only [OrdinaryGMOClaimBOutput.highMultiplicityPairLength,
    OrdinaryGMOClaimBOutput.highMultiplicityLength,
    OrdinaryGMOClaimBOutput.HighMultiplicityInternalQuotient] using
      iteratedFinsetSum_replicate_pGroupDStar_eq_univ
        (E.W.pairInternalGenerator z) hzero hgen

/-- Coset form of the same exact quotient saturation endpoint. -/
theorem OrdinaryGMOClaimBHighMultiplicityCore.iterated_pairInternalQuotientValueCells_eq_fullCoset
    {xs : List A} {seed : Selection xs} {n : ℕ}
    {E : OrdinaryGMOClaimBEnvelope xs seed n} {z : A ⧸ E.W.K}
    (D : OrdinaryGMOClaimBHighMultiplicityCore E z) :
    D.pairInternalQuotientIteratedSum =
      E.W.fullHighMultiplicityInternalCoset z := by
  classical
  letI : Fintype (E.W.HighMultiplicityInternalQuotient z) :=
    Fintype.ofFinite (E.W.HighMultiplicityInternalQuotient z)
  rw [D.iterated_pairInternalQuotientValueCells_eq_univ]
  unfold OrdinaryGMOClaimBOutput.fullHighMultiplicityInternalQuotient
  unfold OrdinaryGMOClaimBOutput.fullHighMultiplicityInternalCoset
  ext q
  simp

end GaoLean

#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityCore.pairInternalQuotientValueCell_eq
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityCore.internalRepresentative_ne_zero
#print axioms GaoLean.OrdinaryGMOClaimBOutput.closure_internalRepresentative_eq_top
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityCore.iterated_pairInternalQuotientValueCells_eq_univ
#print axioms GaoLean.OrdinaryGMOClaimBHighMultiplicityCore.iterated_pairInternalQuotientValueCells_eq_fullCoset
