/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Algebra.Polynomial.MaximalMinor.LaplaceStraightening

/-!
# Duplicating two ordered finite subsets

The rectangular two-minor argument places a tagged copy of each of two row
sets into one finite linear order.  Equal underlying values are ordered with
the left copy first.  This file packages that construction independently of
determinants.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`DuplicatedFinsetOrder.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027]. This general algebra is intended for
Mathlib; its placement exception is recorded in `UPSTREAM.md`.
-/

public section

namespace Cslib

noncomputable section

namespace GenericMaximalMinor

/-- Tagged disjoint union of two finite subsets.

This is a wrapper rather than an abbreviation for `S ⊕ T`: `Sum` already has
an unrelated order instance, whereas below we need the order induced by the
underlying value first and the tag second. -/
structure DuplicatedSubset {n : ℕ} (S T : Finset (Fin n)) where
  /-- The tagged member of the left or right subset. -/
  toSum : S ⊕ T
  deriving DecidableEq

/-- The tagged union is equivalent to the ordinary disjoint union. -/
def duplicatedEquivSum {n : ℕ} (S T : Finset (Fin n)) :
    DuplicatedSubset S T ≃ S ⊕ T where
  toFun := DuplicatedSubset.toSum
  invFun := DuplicatedSubset.mk
  left_inv := by intro x; cases x; rfl
  right_inv := by intro x; rfl

instance {n : ℕ} (S T : Finset (Fin n)) : Fintype (DuplicatedSubset S T) :=
  Fintype.ofEquiv (S ⊕ T) (duplicatedEquivSum S T).symm

/-- Forget the tag of an element in a duplicated subset. -/
def duplicatedValue {n : ℕ} {S T : Finset (Fin n)} :
    DuplicatedSubset S T → Fin n
  | ⟨Sum.inl i⟩ => i
  | ⟨Sum.inr i⟩ => i

/-- Left tags precede right tags when the underlying values agree. -/
def duplicatedTag {n : ℕ} {S T : Finset (Fin n)} :
    DuplicatedSubset S T → Fin 2
  | ⟨Sum.inl _⟩ => 0
  | ⟨Sum.inr _⟩ => 1

/-- The value-and-copy-tag key used to order a duplicated finite subset. -/
def duplicatedKey {n : ℕ} {S T : Finset (Fin n)}
    (x : DuplicatedSubset S T) : Fin n × Fin 2 :=
  (duplicatedValue x, duplicatedTag x)

lemma duplicatedKey_injective {n : ℕ} {S T : Finset (Fin n)} :
    Function.Injective (duplicatedKey (S := S) (T := T)) := by
  rintro ⟨x⟩ ⟨y⟩ h
  cases x with
  | inl x =>
      cases y with
      | inl y =>
          congr
          exact Subtype.ext (congrArg Prod.fst h)
      | inr y =>
          have htag := congrArg (fun q : Fin n × Fin 2 ↦ q.2.val) h
          simp [duplicatedKey, duplicatedTag] at htag
  | inr x =>
      cases y with
      | inl y =>
          have htag := congrArg (fun q : Fin n × Fin 2 ↦ q.2.val) h
          simp [duplicatedKey, duplicatedTag] at htag
      | inr y =>
          congr
          exact Subtype.ext (congrArg Prod.fst h)

instance duplicatedSubsetLinearOrder {n : ℕ} (S T : Finset (Fin n)) :
    LinearOrder (DuplicatedSubset S T) :=
  LinearOrder.lift' (fun x ↦ toLex (duplicatedKey x))
    (toLex.injective.comp duplicatedKey_injective)

lemma duplicated_lt_iff {n : ℕ} {S T : Finset (Fin n)}
    (x y : DuplicatedSubset S T) :
    x < y ↔ toLex (duplicatedKey x) < toLex (duplicatedKey y) := by
  rfl

lemma duplicated_le_iff {n : ℕ} {S T : Finset (Fin n)}
    (x y : DuplicatedSubset S T) :
    x ≤ y ↔ toLex (duplicatedKey x) ≤ toLex (duplicatedKey y) := by
  rfl

/-- Increasing enumeration of the tagged disjoint union. -/
def duplicatedOrderIso {n : ℕ} (S T : Finset (Fin n)) :
    Fin (S.card + T.card) ≃o DuplicatedSubset S T :=
  Fintype.orderIsoFinOfCardEq (DuplicatedSubset S T) (by
    calc
      Fintype.card (DuplicatedSubset S T) = Fintype.card (S ⊕ T) :=
        Fintype.card_congr (duplicatedEquivSum S T)
      _ = S.card + T.card := by simp)

/-- Position occupied by a member of the left subset. -/
@[expose] def duplicatedLeftPosition {n : ℕ} (S T : Finset (Fin n)) :
    S ↪o Fin (S.card + T.card) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (duplicatedOrderIso S T).symm ⟨Sum.inl i⟩) <| by
      intro a b hab
      apply (duplicatedOrderIso S T).symm.strictMono
      rw [duplicated_lt_iff]
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hab

/-- Position occupied by a member of the right subset. -/
@[expose] def duplicatedRightPosition {n : ℕ} (S T : Finset (Fin n)) :
    T ↪o Fin (S.card + T.card) :=
  OrderEmbedding.ofStrictMono
    (fun i ↦ (duplicatedOrderIso S T).symm ⟨Sum.inr i⟩) <| by
      intro a b hab
      apply (duplicatedOrderIso S T).symm.strictMono
      rw [duplicated_lt_iff]
      rw [Prod.Lex.toLex_lt_toLex]
      exact Or.inl hab

/-- The positions of the left tagged copy. -/
@[expose] def duplicatedLeftSet {n : ℕ} (S T : Finset (Fin n)) :
    Finset (Fin (S.card + T.card)) :=
  Finset.univ.map (duplicatedLeftPosition S T).toEmbedding

/-- The positions of the right tagged copy. -/
@[expose] def duplicatedRightSet {n : ℕ} (S T : Finset (Fin n)) :
    Finset (Fin (S.card + T.card)) :=
  Finset.univ.map (duplicatedRightPosition S T).toEmbedding

@[simp] lemma card_duplicatedLeftSet {n : ℕ} (S T : Finset (Fin n)) :
    (duplicatedLeftSet S T).card = S.card := by
  simp [duplicatedLeftSet]

@[simp] lemma card_duplicatedRightSet {n : ℕ} (S T : Finset (Fin n)) :
    (duplicatedRightSet S T).card = T.card := by
  simp [duplicatedRightSet]

/-- Forget the tag at a position of the duplicated order. -/
@[expose] def duplicatedForget {n : ℕ} (S T : Finset (Fin n))
    (i : Fin (S.card + T.card)) : Fin n :=
  duplicatedValue (duplicatedOrderIso S T i)

lemma duplicatedForget_mono {n : ℕ} (S T : Finset (Fin n)) :
    Monotone (duplicatedForget S T) := by
  intro i j hij
  have htagged := (duplicatedOrderIso S T).monotone hij
  rw [duplicated_le_iff] at htagged
  exact Prod.Lex.monotone_fst _ _ htagged

@[simp] lemma duplicatedForget_left {n : ℕ} (S T : Finset (Fin n)) (i : S) :
    duplicatedForget S T (duplicatedLeftPosition S T i) = i := by
  change duplicatedValue
      ((duplicatedOrderIso S T)
        ((duplicatedOrderIso S T).symm ⟨Sum.inl i⟩)) = i
  rw [OrderIso.apply_symm_apply]
  rfl

@[simp] lemma duplicatedForget_right {n : ℕ} (S T : Finset (Fin n)) (i : T) :
    duplicatedForget S T (duplicatedRightPosition S T i) = i := by
  change duplicatedValue
      ((duplicatedOrderIso S T)
        ((duplicatedOrderIso S T).symm ⟨Sum.inr i⟩)) = i
  rw [OrderIso.apply_symm_apply]
  rfl

lemma duplicatedLeftPosition_lt_rightPosition_of_same_value
    {n : ℕ} (S T : Finset (Fin n)) (i : S) (j : T)
    (hij : (i : Fin n) = j) :
    duplicatedLeftPosition S T i < duplicatedRightPosition S T j := by
  apply (duplicatedOrderIso S T).symm.strictMono
  rw [duplicated_lt_iff]
  rw [Prod.Lex.toLex_lt_toLex]
  refine Or.inr ⟨hij, ?_⟩
  exact Fin.zero_lt_one

/-- Positions strictly before the first tagged value which is at least `r`. -/
def duplicatedCutoff {n : ℕ} (S T : Finset (Fin n)) (r : Fin (n + 1)) :
    Fin (S.card + T.card + 1) :=
  ⟨(Finset.univ.filter fun i : Fin (S.card + T.card) ↦
      (duplicatedForget S T i).val < r.val).card,
    Nat.lt_succ_of_le (by
      calc
        (Finset.univ.filter fun i : Fin (S.card + T.card) ↦
            (duplicatedForget S T i).val < r.val).card
            ≤ (Finset.univ : Finset (Fin (S.card + T.card))).card :=
              Finset.card_le_card (Finset.filter_subset _ _)
        _ = S.card + T.card := Finset.card_fin _)⟩

lemma lt_duplicatedCutoff_iff {n : ℕ} (S T : Finset (Fin n))
    (r : Fin (n + 1)) (i : Fin (S.card + T.card)) :
    i.val < (duplicatedCutoff S T r).val ↔
      (duplicatedForget S T i).val < r.val := by
  simpa [duplicatedCutoff] using
    (Fin.lt_card_filter_univ_iff_apply_of_imp
      (fun j : Fin (S.card + T.card) ↦
        (duplicatedForget S T j).val < r.val)
      (by
        intro a b hba ha
        exact lt_of_le_of_lt
          (Fin.mk_le_mk.mpr (duplicatedForget_mono S T hba)) ha)
      (j := i))

/-- Forget the tags of all positions in `P`. -/
@[expose] def duplicatedImage {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card))) : Finset (Fin n) :=
  P.image (duplicatedForget S T)

lemma prefixCard_duplicatedImage {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P) (r : Fin (n + 1)) :
    prefixCard (duplicatedImage S T P) r =
      (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card := by
  unfold prefixCard duplicatedImage
  rw [Finset.filter_image, Finset.card_image_iff.mpr]
  exact Set.InjOn.mono (by
    intro i hi
    exact (Finset.mem_filter.mp
      (show i ∈ P.filter (fun j ↦ (duplicatedForget S T j).val < r.val)
        from hi)).1) hinj

lemma prefixCard_duplicatedCutoff {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card))) (r : Fin (n + 1)) :
    prefixCard P (duplicatedCutoff S T r) =
      (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card := by
  apply congrArg Finset.card
  ext i
  simp only [Finset.mem_filter]
  rw [lt_duplicatedCutoff_iff]

lemma duplicatedImage_leftSet {n : ℕ} (S T : Finset (Fin n)) :
    duplicatedImage S T (duplicatedLeftSet S T) = S := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    rcases Finset.mem_map.mp hp with ⟨j, -, rfl⟩
    change duplicatedForget S T (duplicatedLeftPosition S T j) = i at hpi
    rw [duplicatedForget_left] at hpi
    rw [← hpi]
    exact j.property
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨duplicatedLeftPosition S T ⟨i, hi⟩, ?_, ?_⟩
    · simp [duplicatedLeftSet]
    · simp

lemma duplicatedImage_rightSet {n : ℕ} (S T : Finset (Fin n)) :
    duplicatedImage S T (duplicatedRightSet S T) = T := by
  ext i
  constructor
  · intro hi
    rcases Finset.mem_image.mp hi with ⟨p, hp, hpi⟩
    rcases Finset.mem_map.mp hp with ⟨j, -, rfl⟩
    change duplicatedForget S T (duplicatedRightPosition S T j) = i at hpi
    rw [duplicatedForget_right] at hpi
    rw [← hpi]
    exact j.property
  · intro hi
    apply Finset.mem_image.mpr
    refine ⟨duplicatedRightPosition S T ⟨i, hi⟩, ?_, ?_⟩
    · simp [duplicatedRightSet]
    · simp

lemma duplicatedForget_injOn_leftSet {n : ℕ} (S T : Finset (Fin n)) :
    Set.InjOn (duplicatedForget S T) (duplicatedLeftSet S T) := by
  intro p hp q hq hpq
  rcases Finset.mem_map.mp hp with ⟨i, -, rfl⟩
  rcases Finset.mem_map.mp hq with ⟨j, -, rfl⟩
  change duplicatedForget S T (duplicatedLeftPosition S T i) =
    duplicatedForget S T (duplicatedLeftPosition S T j) at hpq
  rw [duplicatedForget_left, duplicatedForget_left] at hpq
  exact congrArg (duplicatedLeftPosition S T) (Subtype.ext hpq)

lemma duplicatedForget_injOn_rightSet {n : ℕ} (S T : Finset (Fin n)) :
    Set.InjOn (duplicatedForget S T) (duplicatedRightSet S T) := by
  intro p hp q hq hpq
  rcases Finset.mem_map.mp hp with ⟨i, -, rfl⟩
  rcases Finset.mem_map.mp hq with ⟨j, -, rfl⟩
  change duplicatedForget S T (duplicatedRightPosition S T i) =
    duplicatedForget S T (duplicatedRightPosition S T j) at hpq
  rw [duplicatedForget_right, duplicatedForget_right] at hpq
  exact congrArg (duplicatedRightPosition S T) (Subtype.ext hpq)

lemma duplicatedLeftPosition_ne_rightPosition {n : ℕ}
    (S T : Finset (Fin n)) (i : S) (j : T) :
    duplicatedLeftPosition S T i ≠ duplicatedRightPosition S T j := by
  intro hij
  have htag := congrArg (duplicatedOrderIso S T) hij
  unfold duplicatedLeftPosition duplicatedRightPosition at htag
  simp only [OrderEmbedding.coe_ofStrictMono, OrderIso.apply_symm_apply] at htag
  cases congrArg DuplicatedSubset.toSum htag

lemma duplicatedLeftSet_compl {n : ℕ} (S T : Finset (Fin n)) :
    (duplicatedLeftSet S T)ᶜ = duplicatedRightSet S T := by
  ext p
  let x := duplicatedOrderIso S T p
  have hp : (duplicatedOrderIso S T).symm x = p :=
    (duplicatedOrderIso S T).symm_apply_apply p
  rcases x with ⟨i | j⟩
  · have hpleft : duplicatedLeftPosition S T i = p := by
      unfold duplicatedLeftPosition
      simp only [OrderEmbedding.coe_ofStrictMono]
      exact hp
    subst p
    constructor
    · intro hcomp
      apply (Finset.mem_compl.mp hcomp).elim
      exact Finset.mem_map.mpr ⟨i, Finset.mem_univ i, hpleft⟩
    · intro hright
      rcases Finset.mem_map.mp hright with ⟨j, -, hj⟩
      exact (duplicatedLeftPosition_ne_rightPosition S T i j
        (hpleft.trans hj.symm)).elim
  · have hpright : duplicatedRightPosition S T j = p := by
      unfold duplicatedRightPosition
      simp only [OrderEmbedding.coe_ofStrictMono]
      exact hp
    subst p
    constructor
    · intro _
      exact Finset.mem_map.mpr ⟨j, Finset.mem_univ j, hpright⟩
    · intro _
      apply Finset.mem_compl.mpr
      intro hleft
      rcases Finset.mem_map.mp hleft with ⟨i, -, hi⟩
      exact duplicatedLeftPosition_ne_rightPosition S T i j
        (hi.trans hpright.symm)

lemma prefixCard_leftSet_cutoff {n : ℕ} (S T : Finset (Fin n))
    (r : Fin (n + 1)) :
    prefixCard (duplicatedLeftSet S T) (duplicatedCutoff S T r) =
      prefixCard S r := by
  rw [prefixCard_duplicatedCutoff]
  rw [← prefixCard_duplicatedImage S T (duplicatedLeftSet S T)
    (duplicatedForget_injOn_leftSet S T) r]
  rw [duplicatedImage_leftSet]

lemma duplicatedImage_prefixLE {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P)
    (hP : P ≼ₚ duplicatedLeftSet S T) :
    duplicatedImage S T P ≼ₚ S := by
  intro r
  calc
    prefixCard S r =
        prefixCard (duplicatedLeftSet S T) (duplicatedCutoff S T r) :=
      (prefixCard_leftSet_cutoff S T r).symm
    _ ≤ prefixCard P (duplicatedCutoff S T r) :=
      hP (duplicatedCutoff S T r)
    _ = (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card :=
      prefixCard_duplicatedCutoff S T P r
    _ = prefixCard (duplicatedImage S T P) r :=
      (prefixCard_duplicatedImage S T P hinj r).symm

lemma duplicatedImage_prefixLE_of_prefixLE {n : ℕ}
    (S T : Finset (Fin n))
    (P Q : Finset (Fin (S.card + T.card)))
    (hinjP : Set.InjOn (duplicatedForget S T) P)
    (hinjQ : Set.InjOn (duplicatedForget S T) Q)
    (hPQ : P ≼ₚ Q) :
    duplicatedImage S T P ≼ₚ duplicatedImage S T Q := by
  intro r
  calc
    prefixCard (duplicatedImage S T Q) r =
        (Q.filter fun i ↦ (duplicatedForget S T i).val < r.val).card :=
      prefixCard_duplicatedImage S T Q hinjQ r
    _ = prefixCard Q (duplicatedCutoff S T r) :=
      (prefixCard_duplicatedCutoff S T Q r).symm
    _ ≤ prefixCard P (duplicatedCutoff S T r) :=
      hPQ (duplicatedCutoff S T r)
    _ = (P.filter fun i ↦ (duplicatedForget S T i).val < r.val).card :=
      prefixCard_duplicatedCutoff S T P r
    _ = prefixCard (duplicatedImage S T P) r :=
      (prefixCard_duplicatedImage S T P hinjP r).symm

lemma duplicatedLeftPosition_le_of_forget_mem {n : ℕ}
    (S T : Finset (Fin n)) (p : Fin (S.card + T.card))
    (hp : duplicatedForget S T p ∈ S) :
    duplicatedLeftPosition S T ⟨duplicatedForget S T p, hp⟩ ≤ p := by
  unfold duplicatedLeftPosition
  simp only [OrderEmbedding.coe_ofStrictMono]
  have htagged :
      (⟨Sum.inl ⟨duplicatedForget S T p, hp⟩⟩ : DuplicatedSubset S T) ≤
        duplicatedOrderIso S T p := by
    rw [duplicated_le_iff]
    rw [Prod.Lex.toLex_le_toLex]
    refine Or.inr ⟨rfl, ?_⟩
    exact Fin.zero_le _
  have h := (duplicatedOrderIso S T).symm.monotone htagged
  simpa only [OrderIso.symm_apply_apply] using h

/-- If an injective choice of tags forgets to exactly `S`, choosing left tags
instead can only move its positions earlier. -/
lemma duplicatedLeftSet_prefixLE_of_image_eq {n : ℕ}
    (S T : Finset (Fin n)) (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P)
    (himage : duplicatedImage S T P = S) :
    duplicatedLeftSet S T ≼ₚ P := by
  have forget_mem (p : Fin (S.card + T.card)) (hp : p ∈ P) :
      duplicatedForget S T p ∈ S := by
    have hmem : duplicatedForget S T p ∈ duplicatedImage S T P :=
      Finset.mem_image.mpr ⟨p, hp, rfl⟩
    simpa only [himage] using hmem
  intro r
  let source := P.filter fun p ↦ p.val < r.val
  let target := (duplicatedLeftSet S T).filter fun p ↦ p.val < r.val
  let f : source → target := fun p ↦
    ⟨duplicatedLeftPosition S T
        ⟨duplicatedForget S T p,
          forget_mem p (Finset.mem_filter.mp p.property).1⟩,
      Finset.mem_filter.mpr ⟨by
        simp only [duplicatedLeftSet, Finset.univ_eq_attach, Finset.mem_map, Finset.mem_attach,
    RelEmbedding.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq, true_and, exists_eq], by
        exact lt_of_le_of_lt
          (duplicatedLeftPosition_le_of_forget_mem S T p
            (forget_mem p (Finset.mem_filter.mp p.property).1))
          (Finset.mem_filter.mp p.property).2⟩⟩
  exact Finset.card_le_card_of_injective (f := f) (by
    intro p q hpq
    apply Subtype.ext
    apply hinj
    · exact (Finset.mem_filter.mp p.property).1
    · exact (Finset.mem_filter.mp q.property).1
    · have hpos := congrArg Subtype.val hpq
      change duplicatedLeftPosition S T
          ⟨duplicatedForget S T p,
            forget_mem p (Finset.mem_filter.mp p.property).1⟩ =
        duplicatedLeftPosition S T
          ⟨duplicatedForget S T q,
            forget_mem q (Finset.mem_filter.mp q.property).1⟩ at hpos
      have hsub := (duplicatedLeftPosition S T).injective hpos
      exact congrArg Subtype.val hsub)

/-- Strict prefix descent survives forgetting tags, provided no underlying
value is repeated on the chosen subset. -/
lemma duplicatedImage_prefixLT {n : ℕ} (S T : Finset (Fin n))
    (P : Finset (Fin (S.card + T.card)))
    (hinj : Set.InjOn (duplicatedForget S T) P)
    (hP : P ≺ₚ duplicatedLeftSet S T) :
    duplicatedImage S T P ≺ₚ S := by
  refine ⟨duplicatedImage_prefixLE S T P hinj hP.1, ?_⟩
  intro himage
  apply hP.2
  exact prefixLE_antisymm hP.1
    (duplicatedLeftSet_prefixLE_of_image_eq S T P hinj himage)

end GenericMaximalMinor

end

end Cslib
