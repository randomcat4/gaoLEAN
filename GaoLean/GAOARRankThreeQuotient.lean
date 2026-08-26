import GaoLean.GAOARRankThreeLineAux
import GaoLean.PGLowerBound
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Projection

/-!
# Rank-three quotient small-Davenport lift

This module formalizes the complement-lifting argument used in the
rank-three line lemma.  In particular, the quotient bound is derived from
the ambient small-Davenport bound; it is not assumed as an extra result.
-/

namespace GaoLean

namespace ConcreteGDihedral

section MapSelections

variable {X B : Type*}

/-- Send a labelled selection forward along a list map. -/
noncomputable def pushforwardMapSelection (f : X → B) (s : List X)
    (I : Selection s) : Selection (s.map f) := by
  classical
  exact I.map (mapOccurrenceEquiv f s).toEmbedding

theorem card_pushforwardMapSelection (f : X → B) (s : List X)
    (I : Selection s) :
    (pushforwardMapSelection f s I).card = I.card := by
  classical
  simp [pushforwardMapSelection]

theorem selectedMultiset_pushforwardMapSelection (f : X → B) (s : List X)
    (I : Selection s) :
    selectedMultiset (s.map f) (pushforwardMapSelection f s I) =
      (selectedMultiset s I).map f := by
  classical
  simp [selectedMultiset, pushforwardMapSelection,
    occurrenceValue_mapOccurrenceEquiv]

/-- Transport a labelled selection across literal equality of source lists. -/
noncomputable def castSelection {s t : List X} (h : s = t)
    (I : Selection s) : Selection t := by
  subst t
  exact I

/-- The matching occurrence transport across equality of source lists. -/
noncomputable def castOccurrence {s t : List X} (h : s = t) :
    Occurrence s ≃ Occurrence t := by
  subst t
  exact Equiv.refl _

@[simp] theorem castOccurrence_val {s t : List X} (h : s = t)
    (i : Occurrence s) : (castOccurrence h i).1 = i.1 := by
  subst t
  rfl

theorem mem_castSelection_iff {s t : List X} (h : s = t)
    (I : Selection s) (i : Occurrence s) :
    castOccurrence h i ∈ castSelection h I ↔ i ∈ I := by
  subst t
  rfl

theorem isProductOneSelection_castSelection {G : Type*} [Monoid G]
    {s t : List G} (h : s = t) (I : Selection s)
    (hI : IsProductOneSelection s I) :
    IsProductOneSelection t (castSelection h I) := by
  subst t
  exact hI

end MapSelections

variable {A B : Type*} [AddCommGroup A] [AddCommGroup B]

/-- The generalized-dihedral homomorphism induced by any additive map. -/
def inducedMap (f : A →+ B) : Group A →* Group B :=
  SemidirectProduct.map
    (normalMap f)
    (MonoidHom.id (Multiplicative (ZMod 2)))
    (naturality f)

@[simp] theorem inducedMap_rotation (f : A →+ B) (a : A) :
    inducedMap f (rotation A (Multiplicative.ofAdd a)) =
      rotation B (Multiplicative.ofAdd (f a)) := by
  unfold inducedMap
  apply SemidirectProduct.ext <;> rfl

@[simp] theorem inducedMap_flip (f : A →+ B) :
    inducedMap f (flip A) = flip B := by
  simp [inducedMap, flip]

/-- An additive right inverse of the quotient map induces a group-theoretic
right inverse on generalized dihedral groups. -/
theorem quotientMap_inducedMap_of_rightInverse
    (K : AddSubgroup A) (f : (A ⧸ K) →+ A)
    (hf : Function.RightInverse f (QuotientAddGroup.mk' K))
    (g : Group (A ⧸ K)) :
    quotientMap K (inducedMap f g) = g := by
  apply SemidirectProduct.ext
  · change Multiplicative.ofAdd
        (QuotientAddGroup.mk' K (f (Multiplicative.toAdd g.left))) = g.left
    rw [hf]
    rfl
  · rfl

/-- Every quotient of a vector space by an additive subgroup admits the
additive section furnished by a linear complement. -/
theorem exists_quotientAddSection
    (q : ℕ) [Fact q.Prime]
    (A : Type*) [AddCommGroup A] [Module (ZMod q) A]
    (K : AddSubgroup A) :
    ∃ f : (A ⧸ K) →+ A,
      Function.RightInverse f (QuotientAddGroup.mk' K) := by
  let p : Submodule (ZMod q) A := AddSubgroup.toZModSubmodule q K
  obtain ⟨W, hW⟩ := p.exists_isCompl
  let f : (A ⧸ K) →+ A :=
    (W.subtype.comp (p.quotientEquivOfIsCompl W hW).toLinearMap).toAddMonoidHom
  refine ⟨f, ?_⟩
  intro x
  exact p.mk_quotientEquivOfIsCompl_apply hW x

/-- Product one plus rotation type forces the labelled coordinate sum to
vanish.  This is the converse direction needed for the adjoined line copies. -/
theorem coordinateSum_eq_zero_of_allRotation_productOne
    [Fintype A] (s : List (Group A)) (I : Selection s)
    (hall : ∀ i ∈ I, IsRotation (occurrenceValue s i))
    (hprod : IsProductOneSelection s I) :
    coordinateSum s I = 0 := by
  rcases hprod with ⟨word, hword, hwordprod⟩
  have hallWord : ∀ g ∈ word, IsRotation g := by
    intro g hg
    have hgsel : g ∈ selectedMultiset s I := by
      rw [← hword]
      simpa using hg
    rw [selectedMultiset] at hgsel
    rcases Multiset.mem_map.mp hgsel with ⟨i, hi, rfl⟩
    exact hall i hi
  have hsum := sum_coordinate_eq_zero_of_prod_one word hallWord hwordprod
  have hmapped := congrArg
    (fun M : Multiset (Group A) => (M.map coordinate).sum) hword
  have heq : (word.map coordinate).sum = coordinateSum s I := by
    simpa [coordinateSum, selectedMultiset] using hmapped
  rw [← heq]
  exact hsum

/-- The manuscript's complement-lifting proof: the ambient bound
`d(G(F_q^3)) ≤ 3q-2` implies `d(G(F_q^3/J)) ≤ 2q-1` for every nonzero line
`J`. -/
theorem rankThree_quotientSmallDavenport_of_ambient
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q)
    (J : AddSubgroup (PrimeVectorSpace q 3)) (hJne : J ≠ ⊥)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2)) :
    SmallDavenportProductOneFreeAtMost
      (Group (PrimeVectorSpace q 3 ⧸ J)) (2 * q - 1) := by
  classical
  letI : Fact (Nat.Prime q) := ⟨hqPrime⟩
  let A := PrimeVectorSpace q 3
  intro w R hfree
  by_contra hbound
  have hqpos : 0 < q := hqPrime.pos
  have hlarge : 2 * q ≤ R.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hlarge
  let u : List (Group (A ⧸ J)) := occurrenceSubsequence w T
  have hulen : u.length = 2 * q := by
    simp [u, occurrenceSubsequence, hTcard]
  have hufree : IsProductOneFreeSelection u Finset.univ := by
    intro K _hKuniv hKne hKprod
    let I : Selection w := liftOccurrenceSubsequenceSelection w T K
    have hIsub : I ⊆ R :=
      (liftOccurrenceSubsequenceSelection_subset w T K).trans hTsub
    have hIne : I.Nonempty := by
      apply Finset.card_pos.mp
      rw [card_liftOccurrenceSubsequenceSelection]
      exact Finset.card_pos.mpr hKne
    exact hfree I hIsub hIne
      (isProductOneSelection_liftOccurrenceSubsequence w T K hKprod)
  obtain ⟨f, hf⟩ := exists_quotientAddSection q A J
  obtain ⟨e, heJ, he0⟩ : ∃ e : A, e ∈ J ∧ e ≠ 0 := by
    simpa [Ne, AddSubgroup.eq_bot_iff_forall] using hJne
  let lifted : List (Group A) := u.map (inducedMap f)
  let erot : Group A := rotation A (Multiplicative.ofAdd e)
  let tail : List (Group A) := List.replicate (q - 1) erot
  let v : List (Group A) := lifted ++ tail
  have hvlen : v.length = 3 * q - 1 := by
    simp [v, lifted, tail, hulen]
    omega
  have hnotfree : ¬IsProductOneFreeSelection v Finset.univ := by
    intro hvfree
    have hvbound := hsmallAmbient v Finset.univ hvfree
    have hvbound' : v.length ≤ 3 * q - 2 := by simpa using hvbound
    rw [hvlen] at hvbound'
    omega
  simp only [IsProductOneFreeSelection] at hnotfree
  push Not at hnotfree
  obtain ⟨I, _hIuniv, hIne, hIprod⟩ := hnotfree
  let Iq : Selection (v.map (quotientMap J)) :=
    pushforwardMapSelection (quotientMap J) v I
  have hIqprod : IsProductOneSelection (v.map (quotientMap J)) Iq := by
    change HasProductOneOrdering
      (selectedMultiset (v.map (quotientMap J)) Iq)
    rw [selectedMultiset_pushforwardMapSelection]
    exact hasProductOneOrdering_map (quotientMap J) hIprod
  have hliftmap : lifted.map (quotientMap J) = u := by
    simp only [lifted, List.map_map]
    have hfun : (quotientMap J : Group A → Group (A ⧸ J)) ∘
        (inducedMap f : Group (A ⧸ J) → Group A) = id := by
      funext g
      exact quotientMap_inducedMap_of_rightInverse J f hf g
    rw [hfun, List.map_id]
  have hetail : tail.map (quotientMap J) =
      List.replicate (q - 1) (1 : Group (A ⧸ J)) := by
    have heq : quotientMap J erot = 1 := by
      apply (quotientMap_eq_one_iff J erot).2
      constructor
      · rfl
      · change e ∈ J
        exact heJ
    simp [tail, heq]
  have hvmap : v.map (quotientMap J) =
      u ++ List.replicate (q - 1) (1 : Group (A ⧸ J)) := by
    simp only [v, List.map_append, hliftmap, hetail]
  let oneTail : List (Group (A ⧸ J)) :=
    List.replicate (q - 1) (1 : Group (A ⧸ J))
  have hvmap' : v.map (quotientMap J) = u ++ oneTail := by
    simpa [oneTail] using hvmap
  let Iq' : Selection (u ++ oneTail) :=
    castSelection hvmap' Iq
  have hIqprod' : IsProductOneSelection (u ++ oneTail) Iq' :=
    isProductOneSelection_castSelection hvmap' Iq hIqprod
  let Pq : Selection (u ++ oneTail) := prefixOccurrences u oneTail
  let Jq : Selection (u ++ oneTail) := Iq' ∩ Pq
  have hJqprod : IsProductOneSelection (u ++ oneTail) Jq := by
    apply hIqprod'.sdiff_of_all_one Finset.inter_subset_left
    intro i hi
    have hiI : i ∈ Iq' := (Finset.mem_sdiff.mp hi).1
    have hiNotJ : i ∉ Jq := (Finset.mem_sdiff.mp hi).2
    have hiNotP : i ∉ Pq := by
      intro hiP
      exact hiNotJ (Finset.mem_inter.mpr ⟨hiI, hiP⟩)
    exact occurrenceValue_eq_one_of_mem_compl_prefixOccurrences u (q - 1) i
      (Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by simpa [Pq, oneTail] using hiNotP⟩)
  let K : Selection u := prefixSelection u oneTail Iq'
  have hKmap : K.map (appendLeftOccurrenceEmbedding u oneTail) = Jq := by
    exact map_prefixSelection_eq_inter u oneTail Iq'
  have hKprod : IsProductOneSelection u K := by
    have hselected : selectedMultiset u K =
        selectedMultiset (u ++ oneTail) Jq := by
      simpa [K, Jq, Pq] using selectedMultiset_prefixSelection u oneTail Iq'
    change HasProductOneOrdering (selectedMultiset u K)
    rw [hselected]
    exact hJqprod
  have hKempty : K = ∅ := by
    by_contra hne
    have hKne : K.Nonempty := Finset.nonempty_iff_ne_empty.mpr hne
    exact hufree K (Finset.subset_univ K) hKne hKprod
  have hIpast : ∀ i ∈ I, lifted.length ≤ i.1 := by
    intro i hiI
    by_contra hnot
    have hilt : i.1 < lifted.length := by omega
    let iq : Occurrence (v.map (quotientMap J)) :=
      mapOccurrenceEquiv (quotientMap J) v i
    have hiqI : iq ∈ pushforwardMapSelection (quotientMap J) v I := by
      exact Finset.mem_map.mpr ⟨i, hiI, rfl⟩
    let iq' : Occurrence (u ++ oneTail) := castOccurrence hvmap' iq
    have hiqI' : iq' ∈ Iq' := by
      exact (mem_castSelection_iff hvmap' Iq iq).2 (by simpa [Iq] using hiqI)
    have hlength : lifted.length = u.length := by simp [lifted]
    have hiqPrefix : iq' ∈ Pq := by
      simp [Pq, prefixOccurrences, iq', iq]
      omega
    have hiqNotJ : iq' ∉ Jq := by
      rw [← hKmap, hKempty]
      simp
    exact hiqNotJ (Finset.mem_inter.mpr ⟨hiqI', hiqPrefix⟩)
  have hIvalue : ∀ i ∈ I, occurrenceValue v i = erot := by
    intro i hiI
    have hge := hIpast i hiI
    simp only [v, occurrenceValue, List.get_eq_getElem]
    rw [List.getElem_append_right hge]
    simp [tail]
  have hallI : ∀ i ∈ I, IsRotation (occurrenceValue v i) := by
    intro i hiI
    rw [hIvalue i hiI]
    rfl
  have hsumzero : coordinateSum v I = 0 :=
    coordinateSum_eq_zero_of_allRotation_productOne v I hallI hIprod
  have hsumcard : coordinateSum v I = I.card • e := by
    simp only [coordinateSum]
    calc
      (∑ i ∈ I, coordinate (occurrenceValue v i)) =
          ∑ _i ∈ I, e := by
        apply Finset.sum_congr rfl
        intro i hiI
        rw [hIvalue i hiI]
        rfl
      _ = I.card • e := by simp
  have hIpos : 0 < I.card := Finset.card_pos.mpr hIne
  have hItail : I ⊆
      (Finset.univ : Selection v) \ prefixOccurrences lifted tail := by
    intro i hiI
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, by
      simpa [prefixOccurrences, not_lt] using hIpast i hiI⟩
  have htailcard :
      ((Finset.univ : Selection v) \ prefixOccurrences lifted tail).card =
        q - 1 := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [v, card_prefixOccurrences, tail]
  have hIupper : I.card ≤ q - 1 := by
    have := Finset.card_le_card hItail
    rwa [htailcard] at this
  have hIq : I.card < q := by omega
  have hcast : (I.card : ZMod q) ≠ 0 := by
    intro hc
    have hdvd : q ∣ I.card :=
      (ZMod.natCast_eq_zero_iff I.card q).1 hc
    exact (Nat.not_dvd_of_pos_of_lt hIpos hIq) hdvd
  have hnsmul : I.card • e = 0 := by rw [← hsumcard, hsumzero]
  have hsmul : (I.card : ZMod q) • e = 0 := by
    simpa [Nat.cast_smul_eq_nsmul] using hnsmul
  exact he0 ((smul_eq_zero.mp hsmul).resolve_left hcast)

/-- Source-occurrence form consumed by the quotient extraction controller. -/
theorem rankThree_quotientSmallDavenportProductOneFreeAtMost_of_ambient
    (q : ℕ) [NeZero q] (hqPrime : Nat.Prime q)
    (J : AddSubgroup (PrimeVectorSpace q 3)) (hJne : J ≠ ⊥)
    (hsmallAmbient : SmallDavenportProductOneFreeAtMost
      (PrimeVectorDihedral q 3) (3 * q - 2)) :
    QuotientSmallDavenportProductOneFreeAtMost J (2 * q - 1) :=
  quotientSmallDavenportProductOneFreeAtMost_of_smallDavenport J (2 * q - 1)
    (rankThree_quotientSmallDavenport_of_ambient q hqPrime J hJne
      hsmallAmbient)

end ConcreteGDihedral

end GaoLean

#print axioms GaoLean.ConcreteGDihedral.exists_quotientAddSection
#print axioms GaoLean.ConcreteGDihedral.rankThree_quotientSmallDavenport_of_ambient
#print axioms GaoLean.ConcreteGDihedral.rankThree_quotientSmallDavenportProductOneFreeAtMost_of_ambient
