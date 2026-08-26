import GaoLean.PGReflectionExtraction
import GaoLean.PGDavenportBound
import GaoLean.PGDavenportBridge
import GaoLean.PGSynthesis
import Mathlib.Combinatorics.Additive.CauchyDavenport

/-!
# Prime dihedral blocks for GAO-AR

This module formalizes the manuscript's Cauchy--Davenport argument for
reflection-containing blocks in `D₂q`.  It proves the internal upper bound
`d(D₂q) ≤ q`, preserves source occurrences through quotient projection, and
supplies the reflection-containing quotient block used by the rank-two and
rank-three line branches.
-/

namespace GaoLean

open scoped Pointwise

variable {q : ℕ} [Fact q.Prime]
variable {A : Type*} [AddCommGroup A]

/-- A finite additive group of prime cardinality is (noncanonically)
additively equivalent to the prime cyclic group. -/
noncomputable def addEquivZModOfPrimeCard
    (hcard : Nat.card A = q) : A ≃+ ZMod q :=
  (zmodAddCyclicAddEquiv (isAddCyclic_of_prime_card hcard)).symm.trans
    (ZMod.ringEquivCongr hcard).toAddEquiv

noncomputable def ternarySignedSums : List (ZMod q) → Finset (ZMod q)
  | [] => ({0} : Finset (ZMod q))
  | y :: ys => ternarySignedSums ys + ({0, y, -y} : Finset (ZMod q))

theorem zero_mem_ternarySignedSums (ys : List (ZMod q)) :
    0 ∈ ternarySignedSums ys := by
  induction ys with
  | nil => simp [ternarySignedSums]
  | cons y ys ih =>
      rw [ternarySignedSums, Finset.mem_add]
      exact ⟨0, ih, 0, by simp, by simp⟩

theorem card_triple_of_nonzero (hqodd : Odd q) {y : ZMod q} (hy : y ≠ 0) :
    ({0, y, -y} : Finset (ZMod q)).card = 3 := by
  have htwo : (2 : ZMod q) ≠ 0 := by
    have hqne : q ≠ 2 := by
      intro h
      subst q
      norm_num at hqodd
    have hqthree : 3 ≤ q := by
      have := (Fact.out : q.Prime).two_le
      omega
    apply (ZMod.natCast_eq_zero_iff 2 q).not.mpr
    intro hdiv
    have := Nat.le_of_dvd (by omega : 0 < 2) hdiv
    omega
  have hyneg : y ≠ -y := by
    intro h
    have hzero : (2 : ZMod q) * y = 0 := by
      calc
        (2 : ZMod q) * y = y + y := by ring
        _ = y + -y := congrArg (fun z => y + z) h
        _ = 0 := add_neg_cancel y
    exact hy (mul_eq_zero.mp hzero |>.resolve_left htwo)
  have h0 : 0 ∉ ({y, -y} : Finset (ZMod q)) := by
    simp [hy, Ne.symm hy]
  have hyn : y ∉ ({-y} : Finset (ZMod q)) := by
    simp [hyneg]
  rw [Finset.card_insert_of_notMem h0,
    Finset.card_insert_of_notMem hyn]
  simp

theorem ternarySignedSums_card_lower
    (hqodd : Odd q) (ys : List (ZMod q))
    (hnonzero : ∀ y ∈ ys, y ≠ 0) :
    min q (2 * ys.length + 1) ≤ (ternarySignedSums ys).card := by
  induction ys with
  | nil => simp [ternarySignedSums]
  | cons y ys ih =>
      have hy : y ≠ 0 := hnonzero y (by simp)
      have htail : ∀ z ∈ ys, z ≠ 0 := by
        intro z hz
        exact hnonzero z (by simp [hz])
      have hcd := ZMod.cauchy_davenport (Fact.out : q.Prime)
        (show (ternarySignedSums ys).Nonempty from
          ⟨0, zero_mem_ternarySignedSums ys⟩)
        (show ({0, y, -y} : Finset (ZMod q)).Nonempty from by simp)
      rw [card_triple_of_nonzero hqodd hy] at hcd
      rw [ternarySignedSums]
      have hih := ih htail
      have holdpos : 1 ≤ (ternarySignedSums ys).card :=
        Finset.one_le_card.mpr ⟨0, zero_mem_ternarySignedSums ys⟩
      have hcd' :
          min q ((ternarySignedSums ys).card + 2) ≤
            (ternarySignedSums ys + {0, y, -y}).card := by
        omega
      by_cases hqold : q ≤ 2 * ys.length + 1
      · have hqcard : q ≤ (ternarySignedSums ys).card := by
          rw [min_eq_left hqold] at hih
          exact hih
        rw [min_eq_left (by simp; omega)]
        rw [min_eq_left (by omega)] at hcd'
        exact hcd'
      · have hbase : 2 * ys.length + 1 ≤
            (ternarySignedSums ys).card := by
          rw [min_eq_right (Nat.le_of_not_ge hqold)] at hih
          exact hih
        exact (min_le_min le_rfl (by simp; omega)).trans hcd'

noncomputable def nonzeroDifferences (X : Finset (ZMod q)) : Finset (ZMod q) :=
  (X - X).erase 0

theorem zero_mem_self_sub (X : Finset (ZMod q)) (hX : X.Nonempty) :
    0 ∈ X - X := by
  obtain ⟨x, hx⟩ := hX
  rw [Finset.mem_sub]
  exact ⟨x, hx, x, hx, sub_self x⟩

theorem self_add_neg_eq_self_sub (X : Finset (ZMod q)) :
    X + -X = X - X := by
  ext z
  simp only [Finset.mem_add, Finset.mem_neg, Finset.mem_sub]
  constructor
  · rintro ⟨x, hx, ny, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x, hx, y, hy, sub_eq_add_neg x y⟩
  · rintro ⟨x, hx, y, hy, rfl⟩
    exact ⟨x, hx, -y, ⟨y, hy, rfl⟩, (sub_eq_add_neg x y).symm⟩

theorem nonzeroDifferences_card_lower (X : Finset (ZMod q))
    (hX : X.Nonempty) :
    min (q - 1) (2 * X.card - 2) ≤ (nonzeroDifferences X).card := by
  have hneg : (-X).Nonempty := by
    obtain ⟨x, hx⟩ := hX
    exact ⟨-x, Finset.neg_mem_neg hx⟩
  have hcd := ZMod.cauchy_davenport (Fact.out : q.Prime) hX hneg
  rw [Finset.card_neg, self_add_neg_eq_self_sub] at hcd
  have hzero : 0 ∈ X - X := zero_mem_self_sub X hX
  have herase : (nonzeroDifferences X).card = (X - X).card - 1 := by
    exact Finset.card_erase_of_mem hzero
  have hupper : (X - X).card ≤ q := by
    simpa using Finset.card_le_univ (X - X)
  rw [herase]
  by_cases hsat : q ≤ X.card + X.card - 1
  · rw [min_eq_left hsat] at hcd
    have hd : (X - X).card = q := Nat.le_antisymm hupper hcd
    rw [hd]
    exact min_le_left _ _
  · rw [min_eq_right (Nat.le_of_not_ge hsat)] at hcd
    omega

theorem nonzeroDifference_meets_ternarySignedSums
    (hqodd : Odd q) (X : Finset (ZMod q)) (ys : List (ZMod q))
    (ha : 2 ≤ X.card) (hnonzero : ∀ y ∈ ys, y ≠ 0)
    (htotal : q < X.card + ys.length) :
    ∃ d ∈ nonzeroDifferences X, d ∈ ternarySignedSums ys := by
  have hqthree : 3 ≤ q := by
    have hqne : q ≠ 2 := by
      intro h
      subst q
      norm_num at hqodd
    have := (Fact.out : q.Prime).two_le
    omega
  have hX : X.Nonempty := by
    exact Finset.card_pos.mp (by omega)
  have hd := nonzeroDifferences_card_lower X hX
  have hr := ternarySignedSums_card_lower hqodd ys hnonzero
  have hsum : q < (nonzeroDifferences X).card +
      (ternarySignedSums ys).card := by
    by_cases hrfull : q ≤ 2 * ys.length + 1
    · rw [min_eq_left hrfull] at hr
      have hdpos : 1 ≤ (nonzeroDifferences X).card := by
        have : 1 ≤ min (q - 1) (2 * X.card - 2) := by omega
        omega
      omega
    · rw [min_eq_right (Nat.le_of_not_ge hrfull)] at hr
      by_cases hdfull : q - 1 ≤ 2 * X.card - 2
      · rw [min_eq_left hdfull] at hd
        have hXle : X.card ≤ q := by
          simpa using Finset.card_le_univ X
        have hyspos : 1 ≤ ys.length := by omega
        omega
      · rw [min_eq_right (Nat.le_of_not_ge hdfull)] at hd
        omega
  have hnotdis : ¬Disjoint (nonzeroDifferences X) (ternarySignedSums ys) := by
    intro hdis
    have hunion := Finset.card_union_of_disjoint hdis
    have hle : ((nonzeroDifferences X) ∪ (ternarySignedSums ys)).card ≤ q := by
      simpa using Finset.card_le_univ
        ((nonzeroDifferences X) ∪ (ternarySignedSums ys))
    omega
  exact Finset.not_disjoint_iff.mp hnotdis

section LabelledSignedSums

variable {Ω : Type*} [DecidableEq Ω]

noncomputable def ternarySignedSumsBy (f : Ω → ZMod q) :
    List Ω → Finset (ZMod q)
  | [] => ({0} : Finset (ZMod q))
  | x :: xs =>
      ternarySignedSumsBy f xs + ({0, f x, -f x} : Finset (ZMod q))

theorem ternarySignedSumsBy_eq_map (f : Ω → ZMod q) (xs : List Ω) :
    ternarySignedSumsBy f xs = ternarySignedSums (xs.map f) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [ternarySignedSumsBy, ternarySignedSums, ih]

theorem exists_signedSubselection_of_mem
    (f : Ω → ZMod q) (xs : List Ω) (hxs : xs.Nodup) {d : ZMod q}
    (hd : d ∈ ternarySignedSumsBy f xs) :
    ∃ P N : Finset Ω,
      Disjoint P N ∧ P ∪ N ⊆ xs.toFinset ∧
        (∑ i ∈ P, f i) - (∑ i ∈ N, f i) = d := by
  induction xs generalizing d with
  | nil =>
      simp [ternarySignedSumsBy] at hd
      subst d
      exact ⟨∅, ∅, by simp, by simp, by simp⟩
  | cons x xs ih =>
      have hx : x ∉ xs := (List.nodup_cons.mp hxs).1
      have htail : xs.Nodup := (List.nodup_cons.mp hxs).2
      rw [ternarySignedSumsBy, Finset.mem_add] at hd
      obtain ⟨a, ha, b, hb, hab⟩ := hd
      obtain ⟨P, N, hPN, hsub, hsum⟩ := ih htail ha
      simp only [Finset.mem_insert, Finset.mem_singleton] at hb
      rcases hb with rfl | rfl | rfl
      · refine ⟨P, N, hPN, ?_, ?_⟩
        · intro i hi
          simp only [List.toFinset_cons, Finset.mem_insert]
          exact Or.inr (hsub hi)
        · rw [← hab]
          simpa using hsum
      · have hxP : x ∉ P := by
          intro hxP
          exact hx (by simpa using hsub (Finset.mem_union_left N hxP))
        have hxN : x ∉ N := by
          intro hxN
          exact hx (by simpa using hsub (Finset.mem_union_right P hxN))
        refine ⟨insert x P, N, ?_, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro z hz hzn
          rcases Finset.mem_insert.mp hz with rfl | hzP
          · exact hxN hzn
          · exact (Finset.disjoint_left.mp hPN hzP) hzn
        · intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · rcases Finset.mem_insert.mp hz with rfl | hzP
            · simp
            · simp [hsub (Finset.mem_union_left N hzP)]
          · simp [hsub (Finset.mem_union_right P hz)]
        · rw [Finset.sum_insert hxP]
          calc
            f x + (∑ i ∈ P, f i) - (∑ i ∈ N, f i) =
                ((∑ i ∈ P, f i) - (∑ i ∈ N, f i)) + f x := by abel
            _ = a + f x := by rw [hsum]
            _ = d := hab
      · have hxP : x ∉ P := by
          intro hxP
          exact hx (by simpa using hsub (Finset.mem_union_left N hxP))
        have hxN : x ∉ N := by
          intro hxN
          exact hx (by simpa using hsub (Finset.mem_union_right P hxN))
        refine ⟨P, insert x N, ?_, ?_, ?_⟩
        · rw [Finset.disjoint_left]
          intro z hzP hz
          rcases Finset.mem_insert.mp hz with rfl | hzN
          · exact hxP hzP
          · exact (Finset.disjoint_left.mp hPN hzP) hzN
        · intro z hz
          rcases Finset.mem_union.mp hz with hz | hz
          · simp [hsub (Finset.mem_union_left N hz)]
          · rcases Finset.mem_insert.mp hz with rfl | hzN
            · simp
            · simp [hsub (Finset.mem_union_right P hzN)]
        · rw [Finset.sum_insert hxN]
          calc
            (∑ i ∈ P, f i) - (f x + ∑ i ∈ N, f i) =
                ((∑ i ∈ P, f i) - (∑ i ∈ N, f i)) + -f x := by abel
            _ = a + -f x := by rw [hsum]
            _ = d := hab

end LabelledSignedSums

end GaoLean

namespace GaoLean.ConcreteGDihedral

variable {A : Type*} [AddCommGroup A] [Fintype A]

theorem isProductOneSelection_of_twoReflections_signedRotations
    (s : List (Group A)) (P N : Selection s) (rp rm : Occurrence s)
    (hPN : Disjoint P N)
    (hPtyped : ∀ i ∈ P, IsRotation (occurrenceValue s i))
    (hNtyped : ∀ i ∈ N, IsRotation (occurrenceValue s i))
    (hrptyped : ¬IsRotation (occurrenceValue s rp))
    (hrmtyped : ¬IsRotation (occurrenceValue s rm))
    (hrpP : rp ∉ P) (hrpN : rp ∉ N)
    (hrmP : rm ∉ P) (hrmN : rm ∉ N) (hrne : rp ≠ rm)
    (hsum :
      (∑ i ∈ P, coordinate (occurrenceValue s i)) -
          (∑ i ∈ N, coordinate (occurrenceValue s i)) +
          coordinate (occurrenceValue s rp) -
          coordinate (occurrenceValue s rm) = 0) :
    IsProductOneSelection s
      (P.toList ++ N.toList ++ [rp] ++ [rm]).toFinset := by
  classical
  let endpoints := P.toList ++ N.toList ++ [rp] ++ [rm]
  have hPNlist : ∀ a ∈ P.toList, ∀ b ∈ N.toList, a ≠ b := by
    intro a ha b hb hab
    subst b
    exact (Finset.disjoint_left.mp hPN
      (Finset.mem_toList.mp ha)) (Finset.mem_toList.mp hb)
  have hbase : (P.toList ++ N.toList).Nodup :=
    List.nodup_append.mpr
      ⟨P.nodup_toList, N.nodup_toList, hPNlist⟩
  have hrpnot : rp ∉ P.toList ++ N.toList := by
    simp [hrpP, hrpN]
  have hwithRp : (P.toList ++ N.toList ++ [rp]).Nodup :=
    List.nodup_append.mpr
      ⟨hbase, by simp, by
        intro a ha b hb hab
        simp only [List.mem_singleton] at hb
        exact hrpnot ((hab.trans hb) ▸ ha)⟩
  have hrmnot : rm ∉ P.toList ++ N.toList ++ [rp] := by
    simp [hrmP, hrmN, Ne.symm hrne]
  have hnodup : endpoints.Nodup := by
    dsimp [endpoints]
    exact List.nodup_append.mpr
      ⟨hwithRp, by simp, by
        intro a ha b hb hab
        simp only [List.mem_singleton] at hb
        exact hrmnot ((hab.trans hb) ▸ ha)⟩
  let assignment : BalancedSignedAssignment
      (selectedMultiset s endpoints.toFinset) := {
    rotationPlus := occurrenceCoordinates s P.toList
    rotationMinus := occurrenceCoordinates s N.toList
    reflectionPlus := [coordinate (occurrenceValue s rp)]
    reflectionMinus := [coordinate (occurrenceValue s rm)]
    reflectionLengthEq := by simp
    reflectionPlusNonempty := by simp
    carrier_eq := by
      rw [selectedMultiset_toFinset_of_nodup s endpoints hnodup]
      dsimp [endpoints]
      simp only [List.map_append, ← Multiset.coe_add]
      rw [map_occurrenceValue_eq_rot s P.toList (by simpa using hPtyped),
        map_occurrenceValue_eq_rot s N.toList (by simpa using hNtyped)]
      have hmrp : Multiset.ofList [occurrenceValue s rp] =
          Multiset.ofList [(data A).refl
            (coordinate (occurrenceValue s rp))] := by
        exact congrArg (fun g => Multiset.ofList [g])
          (eq_refl_coordinate_of_not_isRotation _ hrptyped)
      have hmrm : Multiset.ofList [occurrenceValue s rm] =
          Multiset.ofList [(data A).refl
            (coordinate (occurrenceValue s rm))] := by
        exact congrArg (fun g => Multiset.ofList [g])
          (eq_refl_coordinate_of_not_isRotation _ hrmtyped)
      simp only [List.map_cons, List.map_nil, occurrenceCoordinates]
      rw [hmrp, hmrm]
      rfl
    signedSum_eq_zero := by
      simpa [occurrenceCoordinates] using hsum
  }
  exact isProductOneSelection_of_balancedSignedAssignment s _ assignment

end GaoLean.ConcreteGDihedral

namespace GaoLean

variable {G : Type*}

/-- The value list carried by a labelled subselection. -/
noncomputable def occurrenceSubsequence (s : List G) (R : Selection s) : List G :=
  R.toList.map (occurrenceValue s)

/-- Send an occurrence of a subselection value list back to its exact source
occurrence. -/
noncomputable def occurrenceSubsequenceSource (s : List G) (R : Selection s) :
    Occurrence (occurrenceSubsequence s R) → Occurrence s := fun i =>
  R.toList.get ⟨i.1, by simpa [occurrenceSubsequence] using i.2⟩

theorem occurrenceSubsequenceSource_injective (s : List G) (R : Selection s) :
    Function.Injective (occurrenceSubsequenceSource s R) := by
  intro i j hij
  apply Fin.ext
  have hget :
      R.toList.get ⟨i.1, by simpa [occurrenceSubsequence] using i.2⟩ =
        R.toList.get ⟨j.1, by simpa [occurrenceSubsequence] using j.2⟩ := hij
  have hidx := R.nodup_toList.injective_get hget
  exact congrArg (fun k : Fin R.toList.length => k.1) hidx

theorem occurrenceSubsequenceSource_mem (s : List G) (R : Selection s)
    (i : Occurrence (occurrenceSubsequence s R)) :
    occurrenceSubsequenceSource s R i ∈ R := by
  exact Finset.mem_toList.mp (R.toList.get_mem _)

theorem occurrenceValue_occurrenceSubsequence (s : List G) (R : Selection s)
    (i : Occurrence (occurrenceSubsequence s R)) :
    occurrenceValue (occurrenceSubsequence s R) i =
      occurrenceValue s (occurrenceSubsequenceSource s R i) := by
  simp [occurrenceSubsequence, occurrenceSubsequenceSource,
    occurrenceValue, List.get_eq_getElem]

noncomputable def liftOccurrenceSubsequenceSelection
    (s : List G) (R : Selection s)
    (I : Selection (occurrenceSubsequence s R)) : Selection s :=
  I.map ⟨occurrenceSubsequenceSource s R,
    occurrenceSubsequenceSource_injective s R⟩

theorem liftOccurrenceSubsequenceSelection_subset
    (s : List G) (R : Selection s)
    (I : Selection (occurrenceSubsequence s R)) :
    liftOccurrenceSubsequenceSelection s R I ⊆ R := by
  intro i hi
  rcases Finset.mem_map.mp hi with ⟨j, _hj, rfl⟩
  exact occurrenceSubsequenceSource_mem s R j

theorem card_liftOccurrenceSubsequenceSelection
    (s : List G) (R : Selection s)
    (I : Selection (occurrenceSubsequence s R)) :
    (liftOccurrenceSubsequenceSelection s R I).card = I.card := by
  exact Finset.card_map _

theorem selectedMultiset_liftOccurrenceSubsequenceSelection
    (s : List G) (R : Selection s)
    (I : Selection (occurrenceSubsequence s R)) :
    selectedMultiset s (liftOccurrenceSubsequenceSelection s R I) =
      selectedMultiset (occurrenceSubsequence s R) I := by
  classical
  unfold liftOccurrenceSubsequenceSelection selectedMultiset
  rw [Finset.map_val, Multiset.map_map]
  apply Multiset.map_congr rfl
  intro i hi
  exact occurrenceValue_occurrenceSubsequence s R i |>.symm

theorem isProductOneSelection_liftOccurrenceSubsequence
    [Monoid G] (s : List G) (R : Selection s)
    (I : Selection (occurrenceSubsequence s R))
    (hI : IsProductOneSelection (occurrenceSubsequence s R) I) :
    IsProductOneSelection s (liftOccurrenceSubsequenceSelection s R I) := by
  rw [IsProductOneSelection,
    selectedMultiset_liftOccurrenceSubsequenceSelection]
  exact hI

end GaoLean

namespace GaoLean.ConcreteGDihedral

open scoped Pointwise

variable {A : Type*} [AddCommGroup A] [Fintype A]
variable {q : ℕ} [Fact q.Prime]

/-- Part (1) of the manuscript's dihedral-block lemma, stated for any
additive group identified with the prime cyclic group. -/
theorem exists_reflection_productOne_of_card_sum_gt_prime
    (hqodd : Odd q) (e : A ≃+ ZMod q) (s : List (Group A))
    (href : 2 ≤ (reflectionOccurrences s).card)
    (htotal : q < (reflectionOccurrences s).card +
      (rotationOccurrencesOutside s (⊥ : AddSubgroup A)).card) :
    ∃ I : Selection s,
      I ⊆ reflectionOccurrences s ∪
        rotationOccurrencesOutside s (⊥ : AddSubgroup A) ∧
      (∃ i ∈ I, ¬IsRotation (occurrenceValue s i)) ∧
      IsProductOneSelection s I := by
  classical
  let F := reflectionOccurrences s
  let C := rotationOccurrencesOutside s (⊥ : AddSubgroup A)
  let f : Occurrence s → ZMod q :=
    fun i => e (coordinate (occurrenceValue s i))
  let fF : F → ZMod q := fun i => f i.1
  by_cases hinj : Function.Injective fF
  · let X : Finset (ZMod q) := F.image f
    have hXcard : X.card = F.card := by
      apply (Finset.card_image_iff.mpr ?_)
      intro i hi j hj hij
      have hsub : (⟨i, hi⟩ : F) = ⟨j, hj⟩ := hinj hij
      exact congrArg Subtype.val hsub
    let cs : List (Occurrence s) := C.toList
    let g : Occurrence s → ZMod q :=
      fun i => e (coordinate (occurrenceValue s i))
    have hnonzero : ∀ y ∈ cs.map g, y ≠ 0 := by
      intro y hy
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hy
      have hiC : i ∈ C := Finset.mem_toList.mp hi
      have hcoord : coordinate (occurrenceValue s i) ≠ 0 := by
        intro hz
        have : coordinate (occurrenceValue s i) ∈ (⊥ : AddSubgroup A) := by
          simpa [hz]
        exact ((mem_rotationOccurrencesOutside_iff s (⊥ : AddSubgroup A) i).1
          (by simpa [C] using hiC)).2 this
      intro hezero
      apply hcoord
      apply e.injective
      change e (coordinate (occurrenceValue s i)) = e 0
      simpa [g] using hezero
    have hmeet := nonzeroDifference_meets_ternarySignedSums
      hqodd X (cs.map g) (by simpa [hXcard, F] using href) hnonzero (by
        simpa [hXcard, X, F, C, cs] using htotal)
    obtain ⟨d, hdDiff, hdSigned⟩ := hmeet
    have hdne : d ≠ 0 := (Finset.mem_erase.mp hdDiff).1
    have hdsub : d ∈ X - X := (Finset.mem_erase.mp hdDiff).2
    obtain ⟨x, hxX, y, hyX, hxy⟩ := Finset.mem_sub.mp hdsub
    obtain ⟨rp, hrpF, hrpval⟩ := Finset.mem_image.mp hxX
    obtain ⟨rm, hrmF, hrmval⟩ := Finset.mem_image.mp hyX
    have hrptyped : ¬IsRotation (occurrenceValue s rp) := by
      simpa [F, reflectionOccurrences] using hrpF
    have hrmtyped : ¬IsRotation (occurrenceValue s rm) := by
      simpa [F, reflectionOccurrences] using hrmF
    have hrne : rp ≠ rm := by
      intro hre
      subst rm
      have hxeq : x = y := hrpval.symm.trans hrmval
      apply hdne
      rw [← hxy, hxeq, sub_self]
    have hdBy : d ∈ ternarySignedSumsBy g cs := by
      rw [ternarySignedSumsBy_eq_map]
      exact hdSigned
    obtain ⟨P, N, hPN, hPC, hsumZ⟩ :=
      exists_signedSubselection_of_mem g cs C.nodup_toList hdBy
    have hPtyped : ∀ i ∈ P, IsRotation (occurrenceValue s i) := by
      intro i hi
      have hiC : i ∈ C := by
        simpa [cs] using hPC (Finset.mem_union_left N hi)
      exact ((mem_rotationOccurrencesOutside_iff s (⊥ : AddSubgroup A) i).1
        (by simpa [C] using hiC)).1
    have hNtyped : ∀ i ∈ N, IsRotation (occurrenceValue s i) := by
      intro i hi
      have hiC : i ∈ C := by
        simpa [cs] using hPC (Finset.mem_union_right P hi)
      exact ((mem_rotationOccurrencesOutside_iff s (⊥ : AddSubgroup A) i).1
        (by simpa [C] using hiC)).1
    have hFC : ∀ r ∈ F, r ∉ C := by
      intro r hrF hrC
      have hreflect : ¬IsRotation (occurrenceValue s r) := by
        simpa [F, reflectionOccurrences] using hrF
      have hrotate := ((mem_rotationOccurrencesOutside_iff
        s (⊥ : AddSubgroup A) r).1 (by simpa [C] using hrC)).1
      exact hreflect hrotate
    have hrpP : rp ∉ P := by
      intro h
      exact hFC rp hrpF (by
        simpa [cs] using hPC (Finset.mem_union_left N h))
    have hrpN : rp ∉ N := by
      intro h
      exact hFC rp hrpF (by
        simpa [cs] using hPC (Finset.mem_union_right P h))
    have hrmP : rm ∉ P := by
      intro h
      exact hFC rm hrmF (by
        simpa [cs] using hPC (Finset.mem_union_left N h))
    have hrmN : rm ∉ N := by
      intro h
      exact hFC rm hrmF (by
        simpa [cs] using hPC (Finset.mem_union_right P h))
    have hsumA :
        (∑ i ∈ P, coordinate (occurrenceValue s i)) -
            (∑ i ∈ N, coordinate (occurrenceValue s i)) +
            coordinate (occurrenceValue s rm) -
            coordinate (occurrenceValue s rp) = 0 := by
      apply e.injective
      simp only [map_sub, map_add, map_sum, map_zero, g, f]
      rw [hsumZ]
      change d + f rm - f rp = 0
      rw [hrmval, hrpval, ← hxy]
      abel
    let I : Selection s :=
      (P.toList ++ N.toList ++ [rm] ++ [rp]).toFinset
    refine ⟨I, ?_, ?_, ?_⟩
    · intro i hi
      have hi' : i = rm ∨ i = rp ∨ i ∈ P ∨ i ∈ N := by
        simpa [I] using hi
      rcases hi' with rfl | rfl | hiP | hiN
      · exact Finset.mem_union_left _ (by simpa [F] using hrmF)
      · exact Finset.mem_union_left _ (by simpa [F] using hrpF)
      · exact Finset.mem_union_right _ (by
          simpa [C, cs] using hPC (Finset.mem_union_left N hiP))
      · exact Finset.mem_union_right _ (by
          simpa [C, cs] using hPC (Finset.mem_union_right P hiN))
    · exact ⟨rm, by simp [I], hrmtyped⟩
    · simpa [I] using
        (isProductOneSelection_of_twoReflections_signedRotations
          s P N rm rp hPN hPtyped hNtyped hrmtyped hrptyped
          hrmP hrmN hrpP hrpN hrne.symm hsumA)
  · obtain ⟨rp, rm, heq, hrneSub⟩ :=
      Function.not_injective_iff.mp hinj
    have hrne : rp.1 ≠ rm.1 := by
      intro h
      exact hrneSub (Subtype.ext h)
    have hrptyped : ¬IsRotation (occurrenceValue s rp.1) := by
      have hrpMem : rp.1 ∈ reflectionOccurrences s := by
        simpa [F] using rp.2
      simpa only [reflectionOccurrences, Finset.mem_filter,
        Finset.mem_univ, true_and] using hrpMem
    have hrmtyped : ¬IsRotation (occurrenceValue s rm.1) := by
      have hrmMem : rm.1 ∈ reflectionOccurrences s := by
        simpa [F] using rm.2
      simpa only [reflectionOccurrences, Finset.mem_filter,
        Finset.mem_univ, true_and] using hrmMem
    have hcoord : coordinate (occurrenceValue s rp.1) =
        coordinate (occurrenceValue s rm.1) :=
      e.injective heq
    let I : Selection s := ([rp.1, rm.1] : List (Occurrence s)).toFinset
    refine ⟨I, ?_, ?_, ?_⟩
    · intro i hi
      have hi' : i = rp.1 ∨ i = rm.1 := by simpa [I] using hi
      rcases hi' with rfl | rfl
      · exact Finset.mem_union_left _ (by simpa [F] using rp.2)
      · exact Finset.mem_union_left _ (by simpa [F] using rm.2)
    · exact ⟨rp.1, by simp [I], hrptyped⟩
    · simpa [I] using
        (isProductOneSelection_of_twoReflections_signedRotations
          s ∅ ∅ rp.1 rm.1 (by simp) (by simp) (by simp)
          hrptyped hrmtyped (by simp) (by simp) (by simp) (by simp)
          hrne (by simp [hcoord]))

/-- Part (2), upper-bound direction: every `q+1`-term sequence over the
dihedral group has a nonempty product-one subsequence. -/
theorem hasNonemptyProductOne_of_length_prime_add_one
    (hqodd : Odd q) (e : A ≃+ ZMod q) (s : List (Group A))
    (hlen : s.length = q + 1) :
    ∃ I : Selection s, I.Nonempty ∧ IsProductOneSelection s I := by
  classical
  by_cases hid : ∃ i : Occurrence s, occurrenceValue s i = 1
  · obtain ⟨i, hi⟩ := hid
    refine ⟨{i}, by simp, ?_⟩
    refine ⟨[occurrenceValue s i], ?_, by simp [hi]⟩
    simp [selectedMultiset]
  · have hnoid : ∀ i : Occurrence s, occurrenceValue s i ≠ 1 := by
      simpa only [not_exists] using hid
    by_cases href : 2 ≤ (reflectionOccurrences s).card
    · have hout : rotationOccurrencesOutside s (⊥ : AddSubgroup A) =
          rotationOccurrences s := by
        ext i
        rw [mem_rotationOccurrencesOutside_iff]
        constructor
        · rintro ⟨hrot, _hout⟩
          simpa [rotationOccurrences] using hrot
        · intro hrotMem
          have hrot : IsRotation (occurrenceValue s i) := by
            simpa [rotationOccurrences] using hrotMem
          refine ⟨hrot, ?_⟩
          intro hbot
          have hcoord : coordinate (occurrenceValue s i) = 0 := by
            simpa using hbot
          exact hnoid i
            ((isRotation_and_coordinate_eq_zero_iff_eq_one
              (occurrenceValue s i)).1 ⟨hrot, hcoord⟩)
      have htotal : q < (reflectionOccurrences s).card +
          (rotationOccurrencesOutside s (⊥ : AddSubgroup A)).card := by
        rw [hout, card_reflectionOccurrences_add_card_rotationOccurrences, hlen]
        omega
      obtain ⟨I, _hsub, ⟨i, hiI, _hiref⟩, hprod⟩ :=
        exists_reflection_productOne_of_card_sum_gt_prime hqodd e s href htotal
      exact ⟨I, ⟨i, hiI⟩, hprod⟩
    · have hrefle : (reflectionOccurrences s).card ≤ 1 := by omega
      have hrotcard : q ≤ (rotationOccurrences s).card := by
        have hpartition := card_reflectionOccurrences_add_card_rotationOccurrences s
        omega
      obtain ⟨T, hTsub, hTcard⟩ :=
        Finset.exists_subset_card_eq hrotcard
      let t : List (Group A) := occurrenceSubsequence s T
      let coords : List A := t.map coordinate
      have hcoords : coords.length = Nat.card A := by
        have hcardA : Nat.card A = q := by
          calc
            Nat.card A = Nat.card (ZMod q) := Nat.card_congr e.toEquiv
            _ = q := by simp
        simp [coords, t, occurrenceSubsequence, hTcard,
          ← Nat.card_eq_fintype_card, hcardA]
      obtain ⟨J, hJne, hJsum⟩ :=
        hasNonemptyZeroSum_of_length_natCard coords hcoords
      let Jt : Selection t := pullbackMapSelection coordinate t J
      have hJtne : Jt.Nonempty := by
        have hcard : Jt.card = J.card := Finset.card_map _
        exact Finset.card_pos.mp (by
          rw [hcard]
          exact Finset.card_pos.mpr hJne)
      have hallt : ∀ i ∈ Jt, IsRotation (occurrenceValue t i) := by
        intro i hi
        have hiT : occurrenceSubsequenceSource s T i ∈ T :=
          occurrenceSubsequenceSource_mem s T i
        have hsourceRot : IsRotation
            (occurrenceValue s (occurrenceSubsequenceSource s T i)) := by
          simpa [rotationOccurrences] using hTsub hiT
        simpa [t, occurrenceValue_occurrenceSubsequence] using hsourceRot
      have hsumt : coordinateSum t Jt = 0 := by
        have hmapped := selectedMultiset_pullbackMapSelection coordinate t J
        have hmulti : (selectedMultiset coords J).sum = 0 := by
          simpa [selectedMultiset] using hJsum
        rw [← hmapped] at hmulti
        simpa [coordinateSum, selectedMultiset] using hmulti
      have hprodt : IsProductOneSelection t Jt :=
        isProductOneSelection_of_allRotation_coordinateSum_eq_zero
          t Jt hallt hsumt
      let I := liftOccurrenceSubsequenceSelection s T Jt
      refine ⟨I, ?_, ?_⟩
      · have hcard := card_liftOccurrenceSubsequenceSelection s T Jt
        exact Finset.card_pos.mp (by
          rw [hcard]
          exact Finset.card_pos.mpr hJtne)
      · exact isProductOneSelection_liftOccurrenceSubsequence s T Jt hprodt

/-- The manuscript-internal upper bound `d(D₂q) ≤ q`. -/
theorem smallDavenportProductOneFreeAtMost_primeDihedral
    (hqodd : Odd q) (e : A ≃+ ZMod q) :
    SmallDavenportProductOneFreeAtMost (Group A) q := by
  intro s R hfree
  by_contra hle
  have hlarge : q + 1 ≤ R.card := by omega
  obtain ⟨T, hTsub, hTcard⟩ := Finset.exists_subset_card_eq hlarge
  let t : List (Group A) := occurrenceSubsequence s T
  have htlen : t.length = q + 1 := by
    simp [t, occurrenceSubsequence, hTcard]
  obtain ⟨J, hJne, hJprod⟩ :=
    hasNonemptyProductOne_of_length_prime_add_one hqodd e t htlen
  let I := liftOccurrenceSubsequenceSelection s T J
  have hIsub : I ⊆ R :=
    (liftOccurrenceSubsequenceSelection_subset s T J).trans hTsub
  have hIne : I.Nonempty := by
    have hcard := card_liftOccurrenceSubsequenceSelection s T J
    exact Finset.card_pos.mp (by
      rw [hcard]
      exact Finset.card_pos.mpr hJne)
  have hIprod : IsProductOneSelection s I :=
    isProductOneSelection_liftOccurrenceSubsequence s T J hJprod
  exact hfree I hIsub hIne hIprod

theorem smallDavenportProductOneFreeAtMost_of_prime_card
    (hqodd : Odd q) (hcard : Nat.card A = q) :
    SmallDavenportProductOneFreeAtMost (Group A) q :=
  smallDavenportProductOneFreeAtMost_primeDihedral
    hqodd (addEquivZModOfPrimeCard hcard)

theorem card_reflectionOccurrences_map_quotientMap
    (K : AddSubgroup A) (t : List (Group A)) :
    (reflectionOccurrences (t.map (quotientMap K))).card =
      (reflectionOccurrences t).card := by
  classical
  let emb := (mapOccurrenceEquiv (quotientMap K) t).toEmbedding
  have heq : (reflectionOccurrences t).map emb =
      reflectionOccurrences (t.map (quotientMap K)) := by
    ext j
    rw [Finset.mem_map]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : ¬IsRotation (occurrenceValue t i) :=
        (Finset.mem_filter.mp hi).2
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [show emb i = mapOccurrenceEquiv (quotientMap K) t i by rfl,
        occurrenceValue_mapOccurrenceEquiv, quotientMap_isRotation_iff]
      exact hi'
    · intro hj
      let i := (mapOccurrenceEquiv (quotientMap K) t).symm j
      refine ⟨i, ?_, ?_⟩
      · have hj' : ¬IsRotation
            (occurrenceValue (t.map (quotientMap K)) j) :=
          (Finset.mem_filter.mp hj).2
        apply Finset.mem_filter.mpr
        refine ⟨Finset.mem_univ _, ?_⟩
        intro hrot
        apply hj'
        rw [← occurrenceValue_mapOccurrenceEquiv_symm
          (quotientMap K) t j]
        exact (quotientMap_isRotation_iff K _).2 hrot
      · simp [emb, i]
  rw [← heq, Finset.card_map]

theorem hasReflectionContainingQuotientProductOne_of_prime_card
    (hqodd : Odd q) (K : AddSubgroup A)
    (hcard : Nat.card (A ⧸ K) = q) (s : List (Group A))
    (href : 2 ≤ (reflectionOccurrences s).card)
    (htotal : q < (reflectionOccurrences s).card +
      (rotationOccurrencesOutside s K).card) :
    HasReflectionContainingQuotientProductOne s K := by
  classical
  let T := reflectionQuotientCarrier s K
  let t : List (Group A) := occurrenceSubsequence s T
  let qt : List (Group (A ⧸ K)) := t.map (quotientMap K)
  have hdis : Disjoint (reflectionOccurrences s)
      (rotationOccurrencesOutside s K) := by
    rw [Finset.disjoint_left]
    intro i hiref hirot
    have hnrot : ¬IsRotation (occurrenceValue s i) := by
      simpa [reflectionOccurrences] using hiref
    exact hnrot ((mem_rotationOccurrencesOutside_iff s K i).1 hirot).1
  have hTcard : T.card = (reflectionOccurrences s).card +
      (rotationOccurrencesOutside s K).card := by
    rw [show T = reflectionOccurrences s ∪ rotationOccurrencesOutside s K by
      rfl, Finset.card_union_of_disjoint hdis]
  have hqtlen : qt.length = T.card := by
    simp [qt, t, occurrenceSubsequence]
  have hnoid : ∀ j : Occurrence qt, occurrenceValue qt j ≠ 1 := by
    intro j
    let jt := (mapOccurrenceEquiv (quotientMap K) t).symm j
    let i := occurrenceSubsequenceSource s T jt
    have hiT : i ∈ T := occurrenceSubsequenceSource_mem s T jt
    have hiCarrier : i ∈ quotientCarrierOccurrences s K := by
      simpa [T, reflectionQuotientCarrier_eq_quotientCarrierOccurrences]
        using hiT
    have hqne := (mem_quotientCarrierOccurrences_iff s K i).1 hiCarrier
    intro hjone
    apply hqne
    have hmap := occurrenceValue_mapOccurrenceEquiv_symm
      (quotientMap K) t j
    calc
      quotientMap K (occurrenceValue s i) =
          quotientMap K (occurrenceValue t jt) := by
        rw [occurrenceValue_occurrenceSubsequence]
      _ = occurrenceValue qt j := hmap
      _ = 1 := hjone
  have hout : rotationOccurrencesOutside qt
      (⊥ : AddSubgroup (A ⧸ K)) = rotationOccurrences qt := by
    ext j
    rw [mem_rotationOccurrencesOutside_iff]
    constructor
    · rintro ⟨hrot, _⟩
      simpa [rotationOccurrences] using hrot
    · intro hjrot
      have hrot : IsRotation (occurrenceValue qt j) := by
        simpa [rotationOccurrences] using hjrot
      refine ⟨hrot, ?_⟩
      intro hbot
      have hcoord : coordinate (occurrenceValue qt j) = 0 := by
        simpa using hbot
      exact hnoid j
        ((isRotation_and_coordinate_eq_zero_iff_eq_one
          (occurrenceValue qt j)).1 ⟨hrot, hcoord⟩)
  obtain ⟨r1, hr1F, r2, hr2F, hrne⟩ :=
    Finset.one_lt_card.mp (by omega : 1 < (reflectionOccurrences s).card)
  have hr1T : r1 ∈ T := by
    exact Finset.mem_union_left _ (by simpa [T] using hr1F)
  have hr2T : r2 ∈ T := by
    exact Finset.mem_union_left _ (by simpa [T] using hr2F)
  obtain ⟨n1, hn1⟩ := List.get_of_mem (Finset.mem_toList.mpr hr1T)
  obtain ⟨n2, hn2⟩ := List.get_of_mem (Finset.mem_toList.mpr hr2T)
  let j1 : Occurrence t :=
    ⟨n1.1, by simpa [t, occurrenceSubsequence] using n1.2⟩
  let j2 : Occurrence t :=
    ⟨n2.1, by simpa [t, occurrenceSubsequence] using n2.2⟩
  have hj1source : occurrenceSubsequenceSource s T j1 = r1 := by
    simpa [occurrenceSubsequenceSource, j1, t] using hn1
  have hj2source : occurrenceSubsequenceSource s T j2 = r2 := by
    simpa [occurrenceSubsequenceSource, j2, t] using hn2
  let k1 : Occurrence qt := mapOccurrenceEquiv (quotientMap K) t j1
  let k2 : Occurrence qt := mapOccurrenceEquiv (quotientMap K) t j2
  have hkne : k1 ≠ k2 := by
    intro h
    have hj : j1 = j2 := (mapOccurrenceEquiv (quotientMap K) t).injective h
    apply hrne
    rw [← hj1source, ← hj2source, hj]
  have hk1 : k1 ∈ reflectionOccurrences qt := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [show occurrenceValue qt k1 =
        quotientMap K (occurrenceValue t j1) by
      exact occurrenceValue_mapOccurrenceEquiv (quotientMap K) t j1]
    rw [quotientMap_isRotation_iff]
    rw [occurrenceValue_occurrenceSubsequence, hj1source]
    simpa [reflectionOccurrences] using hr1F
  have hk2 : k2 ∈ reflectionOccurrences qt := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [show occurrenceValue qt k2 =
        quotientMap K (occurrenceValue t j2) by
      exact occurrenceValue_mapOccurrenceEquiv (quotientMap K) t j2]
    rw [quotientMap_isRotation_iff]
    rw [occurrenceValue_occurrenceSubsequence, hj2source]
    simpa [reflectionOccurrences] using hr2F
  have hrefqt : 2 ≤ (reflectionOccurrences qt).card := by
    have hsub : ({k1, k2} : Finset (Occurrence qt)) ⊆
        reflectionOccurrences qt := by
      intro k hk
      rcases Finset.mem_insert.mp hk with rfl | hk
      · exact hk1
      · have hkeq : k = k2 := by simpa using hk
        subst k
        exact hk2
    have hcardpair : ({k1, k2} : Finset (Occurrence qt)).card = 2 := by
      simp [hkne]
    rw [← hcardpair]
    exact Finset.card_le_card hsub
  have htotalqt : q < (reflectionOccurrences qt).card +
      (rotationOccurrencesOutside qt (⊥ : AddSubgroup (A ⧸ K))).card := by
    rw [hout, card_reflectionOccurrences_add_card_rotationOccurrences,
      hqtlen, hTcard]
    exact htotal
  obtain ⟨J, _hJcarrier, ⟨k, hkJ, hkref⟩, hJprod⟩ :=
    exists_reflection_productOne_of_card_sum_gt_prime hqodd
      (addEquivZModOfPrimeCard hcard) qt hrefqt htotalqt
  let Jt : Selection t := pullbackMapSelection (quotientMap K) t J
  let I : Selection s := liftOccurrenceSubsequenceSelection s T Jt
  refine ⟨I, ?_, ?_, ?_⟩
  · intro i hi
    have hiT := liftOccurrenceSubsequenceSelection_subset s T Jt hi
    simpa [T, reflectionQuotientCarrier_eq_quotientCarrierOccurrences]
      using hiT
  · let kt := (mapOccurrenceEquiv (quotientMap K) t).symm k
    let i := occurrenceSubsequenceSource s T kt
    have hktJt : kt ∈ Jt := by
      exact Finset.mem_map.mpr ⟨k, hkJ, by simp [Jt, kt, pullbackMapSelection]⟩
    have hiI : i ∈ I := by
      exact Finset.mem_map.mpr ⟨kt, hktJt, rfl⟩
    refine ⟨i, hiI, ?_⟩
    intro hirot
    apply hkref
    have hqrot : IsRotation
        (quotientMap K (occurrenceValue t kt)) := by
      rw [quotientMap_isRotation_iff]
      simpa [i, kt, t, occurrenceValue_occurrenceSubsequence] using hirot
    have hval := occurrenceValue_mapOccurrenceEquiv_symm
      (quotientMap K) t k
    rw [hval] at hqrot
    exact hqrot
  · change HasProductOneOrdering
      ((selectedMultiset s I).map (quotientMap K))
    rw [selectedMultiset_liftOccurrenceSubsequenceSelection]
    rw [selectedMultiset_pullbackMapSelection]
    exact hJprod

end GaoLean.ConcreteGDihedral

#print axioms GaoLean.ternarySignedSums_card_lower
#print axioms GaoLean.nonzeroDifferences_card_lower
#print axioms GaoLean.nonzeroDifference_meets_ternarySignedSums
#print axioms GaoLean.ConcreteGDihedral.exists_reflection_productOne_of_card_sum_gt_prime
#print axioms GaoLean.ConcreteGDihedral.smallDavenportProductOneFreeAtMost_of_prime_card
#print axioms GaoLean.ConcreteGDihedral.hasReflectionContainingQuotientProductOne_of_prime_card
