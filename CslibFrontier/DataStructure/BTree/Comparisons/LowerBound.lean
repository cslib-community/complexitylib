/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, AI Assistant
-/

module
-- upstream: local-only (new development for M7)

public import CslibFrontier.DataStructure.BTree.Comparisons.Query
public import Cslib.Algorithms.Lean.Query.Sort.LowerBound

/-!
# Search Lower Bounds for B-trees

This file defines the correctness predicates for comparison-based rank and lookup programs,
and proves the `⌈log₂(n + 1)⌉` comparison lower bound for `rank` on an infinite key type.
-/

public section

variable {α : Type} {β : Type}

namespace Cslib.DataStructure.BTree

open Cslib.Query
open scoped Cardinal

/-- A correct comparison-based rank program returns the number of elements strictly less
    than `k`. -/
def CorrectRank (rankProg : α → BTree α β → FreeM (LEQuery α) ℕ) : Prop :=
  ∀ (k : α) (tree : BTree α β) (O : α → α → Prop) [DecidableRel O],
    IsLinearOrder α O →
    (rankProg k tree).eval (LEQuery.oracleOf (fun a b => decide (O a b))) =
      (tree.toList.filter (fun x => O x.1 k ∧ ¬ O k x.1)).length

private def listEmbedding {L : List α} (h : L.Nodup) : Fin L.length ↪ α :=
  ⟨fun i => L.get i, fun _ _ hij => List.Nodup.get_inj_iff h |>.mp hij⟩

private noncomputable def listPrefix {L : List α} (h : L.Nodup) : α → Fin L.length ⊕ α :=
  Function.extend (listEmbedding h) .inl .inr

@[simp] private lemma listPrefix_embedded {L : List α} (h : L.Nodup) (i : Fin L.length) :
    listPrefix h L[i.val] = .inl i :=
  (listEmbedding h).injective.extend_apply _ _ _

private theorem listPrefix_injective {L : List α} (h : L.Nodup) :
    Function.Injective (listPrefix h) :=
  (listEmbedding h).injective.extend_of_disjoint Sum.inl_injective Sum.inr_injective
    Set.isCompl_range_inl_range_inr.disjoint

private noncomputable def PrefixOrder {L : List α} (h : L.Nodup) : α → α → Prop :=
  let _ := IsWellOrder.linearOrder (α := α) WellOrderingRel
  InvImage (Sum.Lex (· ≤ · : Fin L.length → Fin L.length → Prop) (· ≤ ·)) (listPrefix h)

private noncomputable instance {L : List α} (h : L.Nodup) :
    DecidableRel (PrefixOrder h) := Classical.decRel _

private instance {L : List α} (h : L.Nodup) :
    IsTrans α (PrefixOrder h) := by
  unfold PrefixOrder; infer_instance

private instance {L : List α} (h : L.Nodup) :
    Std.Total (PrefixOrder h) := by
  unfold PrefixOrder; infer_instance

private instance {L : List α} (h : L.Nodup) :
    Std.Antisymm (PrefixOrder h) := by
  let _ := IsWellOrder.linearOrder (α := α) WellOrderingRel
  have : Std.Antisymm (Sum.Lex (· ≤ · : Fin L.length → Fin L.length → Prop)
      (· ≤ · : α → α → Prop)) :=
    inferInstance
  exact listPrefix_injective h |>.antisymm_onFun _

private instance {L : List α} (h : L.Nodup) :
    IsLinearOrder α (PrefixOrder h) where

private lemma prefixOrder_get_iff {L : List α} (h : L.Nodup) (a b : Fin L.length) :
    PrefixOrder h L[a.val] L[b.val] ↔ a ≤ b := by
  simp only [PrefixOrder, InvImage, listPrefix_embedded]
  exact ⟨by rintro ⟨h⟩; exact h, Sum.Lex.inl⟩

private lemma prefixOrder_lt_getElem_iff {L : List α} (h : L.Nodup) (a b : ℕ)
    (ha : a < L.length) (hb : b < L.length) :
    (PrefixOrder h L[a] L[b] ∧ ¬PrefixOrder h L[b] L[a]) ↔ a < b := by
  have h1 := prefixOrder_get_iff h ⟨a, ha⟩ ⟨b, hb⟩
  have h2 := prefixOrder_get_iff h ⟨b, hb⟩ ⟨a, ha⟩
  simp only [Fin.mk_le_mk] at h1 h2
  rw [h1, h2]
  omega

private lemma length_filter_PrefixOrder {xs : List α} {k : α} (h_nodup : xs.Nodup) (hk : k ∉ xs)
    (i : ℕ) (hi : i ≤ xs.length) :
    let L_i := xs.insertIdx i k
    have h_nodup_i : L_i.Nodup := (List.perm_insertIdx k xs hi).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hk, h_nodup⟩)
    (xs.filter (fun x => PrefixOrder h_nodup_i x k ∧ ¬PrefixOrder h_nodup_i k x)).length = i := by
  intro L_i h_nodup_i
  let p : α → Bool := fun x => decide (PrefixOrder h_nodup_i x k ∧ ¬PrefixOrder h_nodup_i k x)
  have hp_eq : (xs.filter (fun x => PrefixOrder h_nodup_i x k ∧
      ¬PrefixOrder h_nodup_i k x)).length =
      (xs.filter (fun x => p x)).length := by
    rfl
  rw [hp_eq]
  have hL_len : L_i.length = xs.length + 1 := List.length_insertIdx_of_le_length hi k
  have hi_lt : i < L_i.length := by omega
  have hLi : L_i[i] = k := List.getElem_insertIdx_self hi_lt
  have h_take : (xs.take i).filter p = xs.take i := by
    rw [List.filter_eq_self]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [List.length_take_of_le hi] at hj
    have hj_lt_L : j < L_i.length := by omega
    have hLj : L_i[j] = (xs.take i)[j] := by
      rw [List.getElem_take, List.getElem_insertIdx_of_lt hj]
    simp only [p, decide_eq_true_eq, ← hLj, ← hLi]
    exact (prefixOrder_lt_getElem_iff h_nodup_i j i hj_lt_L hi_lt).mpr hj
  have h_drop : (xs.drop i).filter p = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rw [List.mem_iff_getElem] at hx
    rcases hx with ⟨j, hj, rfl⟩
    rw [List.length_drop] at hj
    have hj_lt_L : i + j + 1 < L_i.length := by omega
    have hLj : L_i[i + j + 1] = (xs.drop i)[j] := by
      rw [List.getElem_drop, List.getElem_insertIdx_of_gt (by omega)]
      rfl
    simp only [p, decide_eq_true_eq, ← hLj, ← hLi,
      prefixOrder_lt_getElem_iff h_nodup_i (i + j + 1) i hj_lt_L hi_lt]
    omega
  have h_split : xs.filter p = (xs.take i).filter p ++ (xs.drop i).filter p := by
    rw [← List.filter_append, List.take_append_drop]
  rw [h_split, h_take, h_drop, List.append_nil, List.length_take_of_le hi]


private lemma filter_fst_length {γ δ : Type} (l : List (γ × δ)) (P : γ → Prop) [DecidablePred P] :
    (l.filter (fun x => P x.1)).length = ((l.map Prod.fst).filter P).length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    simp only [List.filter_cons, List.map_cons]
    split <;> simp [ih]

/-- Any correct comparison rank program on an infinite type has query complexity at least
    `⌈log₂(n + 1)⌉`
    for a tree of size `n`. -/
theorem rank_lowerBound_infinite [Infinite α]
    {rankProg : α → BTree α β → FreeM (LEQuery α) ℕ} (h_corr : CorrectRank rankProg)
    (tree : BTree α β) (h_nodup : (tree.toList.map Prod.fst).Nodup) :
    ∃ (k : α) (O : {ι : Type} → LEQuery α ι → ι),
      (rankProg k tree).countQueries O ≥ Nat.clog 2 (tree.size + 1) := by
  let xs := tree.toList.map Prod.fst
  have hxs : xs.length = tree.size := by
    change (tree.toList.map Prod.fst).length = tree.toList.length
    rw [List.length_map]
  have ⟨k, hk⟩ : ∃ k : α, k ∉ xs := by
    by_contra h
    push Not at h
    let _ := Classical.decEq α
    have h_fin : Fintype α := Fintype.ofList xs h
    let _ := @Fintype.finite α h_fin
    exact not_finite α
  let n := tree.size
  let progOracles : Fin (n + 1) → ({ι : Type} → LEQuery α ι → ι) := fun i =>
    let L_i := xs.insertIdx (i : ℕ) k
    have hi_le : (i : ℕ) ≤ xs.length := by omega
    have h_nodup_i : L_i.Nodup := (List.perm_insertIdx k xs hi_le).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hk, h_nodup⟩)
    LEQuery.oracleOf (fun a b => decide (PrefixOrder h_nodup_i a b))
  have eval_eq (i : Fin (n + 1)) : (rankProg k tree).eval (progOracles i) = i := by
    let L_i := xs.insertIdx (i : ℕ) k
    have hi_le : (i : ℕ) ≤ xs.length := by omega
    have h_nodup_i : L_i.Nodup := (List.perm_insertIdx k xs hi_le).nodup_iff.mpr
      (List.nodup_cons.mpr ⟨hk, h_nodup⟩)
    have h_corr_i := h_corr k tree (PrefixOrder h_nodup_i) (by infer_instance)
    dsimp [progOracles]
    rw [h_corr_i]
    let P := fun y => PrefixOrder h_nodup_i y k ∧ ¬PrefixOrder h_nodup_i k y
    have h_filter : (tree.toList.filter (fun x => PrefixOrder h_nodup_i x.1 k ∧
      ¬PrefixOrder h_nodup_i k x.1)).length =
      (xs.filter P).length := filter_fst_length tree.toList P
    -- rw [h_filter]
    exact Eq.trans h_filter (length_filter_PrefixOrder h_nodup hk (↑i) hi_le)
  have h_inj : Function.Injective (fun i => (rankProg k tree).eval (progOracles i)) := by
    intro i j h
    have h1 := eval_eq i
    have h2 := eval_eq j
    dsimp only at h
    rw [h1, h2] at h
    exact Fin.ext h
  obtain ⟨i, hi⟩ := FreeM.exists_countQueries_ge_clog 2
    LEQuery.cardResponse_le_two
    (rankProg k tree) progOracles (by omega) h_inj
  exact ⟨k, progOracles i, hi⟩

end Cslib.DataStructure.BTree
