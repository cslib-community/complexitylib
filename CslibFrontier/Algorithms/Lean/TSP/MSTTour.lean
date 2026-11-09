/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.Kruskal.Basic
public import CslibFrontier.Algorithms.Lean.TSP.Walk
import Mathlib.Algebra.Order.Group.Nat
import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.Zip

/-!
# A minimum-spanning-tree 2-approximation for metric TSP

This module formalizes a 2-approximation for the metric traveling salesman problem built on a
minimum spanning tree ([WilliamsonShmoys2011], Section 2.4). The algorithm computes a minimum
spanning tree of the complete graph with Kruskal's algorithm (`kruskalEdges`), then grows a tour
from vertex `0`: while some tree edge has exactly one endpoint on the tour, the other endpoint is
inserted immediately after it.

## Model

Vertices are `Fin n` and `δ : Fin n → Fin n → ℕ` is an arbitrary cost function. The cost of a
closed walk visiting the entries of a list in order is `cycleCost δ t`
(`CslibFrontier.Algorithms.Lean.TSP.Walk`). The approximation bound
assumes only that `δ` is symmetric and satisfies the triangle inequality for all triples, including
`i = k`, so each diagonal entry is at most twice any cost from its vertex; diagonal entries need not
be zero. Costs are natural numbers, hence nonnegative.

## Source mapping

[WilliamsonShmoys2011], Section 2.4, proves Lemma 2.10 (a minimum spanning tree costs at most an
optimal tour) by deleting an edge of the tour. Here `totalWeight_kruskalEdges_le_cycleCost` instead
compares Kruskal's tree with a spanning forest of the tour's edges, which needs no edge deletion.
Theorem 2.11 (nearest addition is a 2-approximation) charges each insertion of a city `j` after `i`
at most `c_ij + c_ji = 2 c_ij`, by the triangle inequality; summed over the edges of the spanning
tree built by Prim's algorithm, the tour costs at most twice the tree. The same charging argument
applies to any spanning tree whose edges guide the insertions, so `mstTour` uses the tree computed
by the library's Kruskal implementation (`cycleCost_insertAfter_le`,
`cycleCost_mstTour_le_two_mul_totalWeight`). Like the double-tree algorithm of Theorem 2.12, it
computes the tree first and then derives the tour from it.

## Limitations

The algorithm is a pure Lean function; no machine-level running time is certified. The bound is
stated against every tour, in particular an optimal one.

## Main definitions

* `Cslib.Algorithms.Lean.TSP.insertAfter`: insertion immediately after a given vertex.
* `Cslib.Algorithms.Lean.TSP.growTour`: grow a tour along the edges of a forest.
* `Cslib.Algorithms.Lean.TSP.completeEdges`: the complete graph weighted by `δ`.
* `Cslib.Algorithms.Lean.TSP.mstTour`: the tour grown along Kruskal's minimum spanning tree.

## Main results

* `cycleCost_insertAfter_le`: an insertion costs at most `δ u v + δ v u` (triangle inequality).
* `mstTour_perm`: `mstTour δ` visits every vertex exactly once.
* `totalWeight_kruskalEdges_completeEdges_le`: Kruskal's tree on the complete graph weighs at most
  any duplicate-free connected list of its edges.
* `totalWeight_kruskalEdges_le_cycleCost`: the minimum spanning tree costs at most any tour.
* `cycleCost_mstTour_le_two_mul_totalWeight`: for `n ≥ 2`, the tour costs at most twice the tree.
* `cycleCost_mstTour_le_two_mul`: for symmetric `δ` with the triangle inequality, the tour costs
  at most twice any tour.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.4.
-/

public section

namespace Cslib.Algorithms.Lean.TSP

open Cslib.DataStructure.DisjointSet Cslib.Algorithms.Lean.Kruskal

/-! ### Closed walks and insertion -/

section Cycle

variable {α : Type*}

private theorem walkCost_le (δ : α → α → ℕ) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (u v : α) (L : List α) : walkCost δ v L u ≤ δ v u + walkCost δ u L u := by
  cases L with
  | nil =>
    simp only [walkCost]
    omega
  | cons x L =>
    simp only [walkCost]
    have := htri v u x
    omega

/-- **The insertion step** ([WilliamsonShmoys2011], proof of Theorem 2.11): inserting `v` right
after `u` in a closed walk costs at most `δ u v + δ v u`, by the triangle inequality. -/
theorem cycleCost_append_cons_cons_le (δ : α → α → ℕ) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    (A B : List α) (u v : α) :
    cycleCost δ (A ++ u :: v :: B) ≤ cycleCost δ (A ++ u :: B) + (δ u v + δ v u) := by
  rw [cycleCost_append_comm δ A, cycleCost_append_comm δ A]
  simp only [List.cons_append]
  rw [cycleCost_cons, cycleCost_cons]
  simp only [walkCost]
  have := walkCost_le δ htri u v (B ++ A)
  omega

variable [DecidableEq α]

/-- Insert `v` immediately after the first occurrence of `u` in `t` (at the end if `u ∉ t`). -/
@[expose] def insertAfter (u v : α) : List α → List α
  | [] => [v]
  | x :: t => if x = u then x :: v :: t else x :: insertAfter u v t

/-- Inserting after a vertex of the walk splits the walk at that vertex. -/
theorem exists_eq_insertAfter {u : α} (v : α) {t : List α} (hu : u ∈ t) :
    ∃ A B, t = A ++ u :: B ∧ insertAfter u v t = A ++ u :: v :: B := by
  induction t with
  | nil => simp at hu
  | cons x t ih =>
    by_cases hx : x = u
    · subst hx
      exact ⟨[], t, rfl, by simp [insertAfter]⟩
    · obtain ⟨A, B, rfl, h⟩ := ih ((List.mem_cons.1 hu).resolve_left (Ne.symm hx))
      exact ⟨x :: A, B, rfl, by simp [insertAfter, hx, h]⟩

/-- Inserting after a vertex of the walk adds exactly the inserted vertex. -/
theorem insertAfter_perm {u : α} (v : α) {t : List α} (hu : u ∈ t) :
    (insertAfter u v t).Perm (v :: t) := by
  obtain ⟨A, B, rfl, h⟩ := exists_eq_insertAfter v hu
  rw [h]
  have h1 : A ++ u :: v :: B = (A ++ [u]) ++ v :: B := by simp
  have h2 : A ++ u :: B = (A ++ [u]) ++ B := by simp
  rw [h1, h2]
  exact List.perm_middle

/-- **The insertion bound** ([WilliamsonShmoys2011], proof of Theorem 2.11): inserting `v` after a
vertex `u` of a closed walk raises its cost by at most `δ u v + δ v u`. -/
theorem cycleCost_insertAfter_le (δ : α → α → ℕ) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {u : α} (v : α) {t : List α} (hu : u ∈ t) :
    cycleCost δ (insertAfter u v t) ≤ cycleCost δ t + (δ u v + δ v u) := by
  obtain ⟨A, B, rfl, h⟩ := exists_eq_insertAfter v hu
  rw [h]
  exact cycleCost_append_cons_cons_le δ htri A B u v

end Cycle

/-! ### Growing a tour along a forest -/

variable {n : ℕ}

/-- Whether exactly one endpoint of `e` is on the tour `t`. -/
@[expose] def crosses {W : Type} (t : List (Fin n)) (e : WeightedEdge n W) : Bool :=
  decide (e.u ∈ t) != decide (e.v ∈ t)

theorem crosses_eq_true_iff {W : Type} {t : List (Fin n)} {e : WeightedEdge n W} :
    crosses t e = true ↔ ¬(e.u ∈ t ↔ e.v ∈ t) := by
  simp [crosses]

/-- Insert the endpoint of `e` that is off the tour immediately after the endpoint on it. -/
@[expose] def growStep {W : Type} (t : List (Fin n)) (e : WeightedEdge n W) : List (Fin n) :=
  if e.u ∈ t then insertAfter e.u e.v t else insertAfter e.v e.u t

/-- **Growing a tour along `F`**: while some edge of `F` has exactly one endpoint on the tour,
insert its other endpoint right after it, the first such edge of `F` first; at most `k`
insertions. -/
@[expose] def growTour {W : Type} (F : List (WeightedEdge n W)) :
    ℕ → List (Fin n) → List (Fin n)
  | 0, t => t
  | k + 1, t =>
    match F.find? (crosses t) with
    | none => t
    | some e => growTour F k (growStep t e)

/-- A crossing step inserts the endpoint `b` off the tour right after the endpoint `a` on it. -/
theorem growStep_spec {W : Type} {t : List (Fin n)} {e : WeightedEdge n W}
    (he : crosses t e = true) :
    ∃ a b, (a = e.u ∧ b = e.v ∨ a = e.v ∧ b = e.u) ∧ a ∈ t ∧ b ∉ t ∧
      growStep t e = insertAfter a b t := by
  rw [crosses_eq_true_iff] at he
  unfold growStep
  by_cases hu : e.u ∈ t
  · exact ⟨e.u, e.v, Or.inl ⟨rfl, rfl⟩, hu, fun hv => he ⟨fun _ => hv, fun _ => hu⟩,
      ite_eq_left hu⟩
  · have hv : e.v ∈ t := by
      by_contra hv
      exact he ⟨fun h => absurd h hu, fun h => absurd h hv⟩
    exact ⟨e.v, e.u, Or.inr ⟨rfl, rfl⟩, hv, hu, ite_eq_right hu⟩

/-- Growing keeps the tour free of repetitions. -/
theorem nodup_growTour {W : Type} (F : List (WeightedEdge n W)) (k : ℕ) {t : List (Fin n)}
    (ht : t.Nodup) : (growTour F k t).Nodup := by
  induction k generalizing t with
  | zero => exact ht
  | succ k ih =>
    cases h : F.find? (crosses t) with
    | none => simpa only [growTour, h] using ht
    | some e =>
      simp only [growTour, h]
      obtain ⟨a, b, -, ha, hb, heq⟩ := growStep_spec (List.find?_some h)
      rw [heq]
      exact ih ((insertAfter_perm b ha).nodup_iff.2 (List.nodup_cons.2 ⟨hb, ht⟩))

/-- **Coverage.** If the edges of `F` connect all of `Fin n` and there is fuel for `n` vertices,
growing a nonempty tour without repetitions reaches every vertex. -/
theorem mem_growTour {W : Type} {F : List (WeightedEdge n W)}
    (hF : ∀ a b : Fin n, Relation.EqvGen (fun x y => ∃ e ∈ F, x = e.u ∧ y = e.v) a b)
    {k : ℕ} {t : List (Fin n)} (ht : t.Nodup) (hne : t ≠ []) (hk : n ≤ t.length + k)
    (x : Fin n) : x ∈ growTour F k t := by
  induction k generalizing t with
  | zero =>
    simp only [growTour]
    by_contra hx
    have := (List.nodup_cons.2 ⟨hx, ht⟩).length_le_card
    simp only [List.length_cons, Fintype.card_fin] at this
    omega
  | succ k ih =>
    cases h : F.find? (crosses t) with
    | none =>
      simp only [growTour, h]
      have hnone := List.find?_eq_none.1 h
      have key : ∀ a b, Relation.EqvGen (fun x y => ∃ e ∈ F, x = e.u ∧ y = e.v) a b →
          (a ∈ t ↔ b ∈ t) := by
        intro a b hab
        induction hab with
        | rel a b hab =>
          obtain ⟨e, he, rfl, rfl⟩ := hab
          have := hnone e he
          rw [crosses_eq_true_iff, not_not] at this
          exact this
        | refl => exact Iff.rfl
        | symm _ _ _ ih => exact ih.symm
        | trans _ _ _ _ _ ih₁ ih₂ => exact ih₁.trans ih₂
      obtain ⟨r, hr⟩ := List.exists_mem_of_ne_nil t hne
      exact (key r x (hF r x)).1 hr
    | some e =>
      simp only [growTour, h]
      obtain ⟨a, b, -, ha, hb, heq⟩ := growStep_spec (List.find?_some h)
      have hperm := insertAfter_perm b ha
      rw [heq]
      refine ih (hperm.nodup_iff.2 (List.nodup_cons.2 ⟨hb, ht⟩)) ?_ ?_
      · intro h0
        have := hperm.length_eq
        simp [h0] at this
      · have := hperm.length_eq
        simp only [List.length_cons] at this
        omega

/-! ### The charging argument -/

/-- The total weight of the edges of `F` with both endpoints on `t`. -/
private def insideWeight (F : List (WeightedEdge n ℕ)) (t : List (Fin n)) : ℕ :=
  (F.map fun e => if e.u ∈ t ∧ e.v ∈ t then e.weight else 0).sum

private theorem sum_map_inside_mono {t t' : List (Fin n)} (hsub : t ⊆ t')
    (L : List (WeightedEdge n ℕ)) :
    (L.map fun e => if e.u ∈ t ∧ e.v ∈ t then e.weight else 0).sum ≤
      (L.map fun e => if e.u ∈ t' ∧ e.v ∈ t' then e.weight else 0).sum := by
  induction L with
  | nil => exact le_rfl
  | cons f L ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (if f.u ∈ t ∧ f.v ∈ t then f.weight else 0) ≤
        (if f.u ∈ t' ∧ f.v ∈ t' then f.weight else 0) := by
      split_ifs with h1 h2
      · exact le_rfl
      · exact absurd ⟨hsub h1.1, hsub h1.2⟩ h2
      · exact Nat.zero_le _
      · exact le_rfl
    omega

private theorem insideWeight_add_le {F : List (WeightedEdge n ℕ)} {t t' : List (Fin n)}
    (hsub : t ⊆ t') {e : WeightedEdge n ℕ} (he : e ∈ F) (hin : ¬(e.u ∈ t ∧ e.v ∈ t))
    (hin' : e.u ∈ t' ∧ e.v ∈ t') : insideWeight F t + e.weight ≤ insideWeight F t' := by
  obtain ⟨A, B, rfl⟩ := List.append_of_mem he
  simp only [insideWeight, List.map_append, List.map_cons, List.sum_append, List.sum_cons,
    ite_eq_right hin, ite_eq_left hin']
  have hA := sum_map_inside_mono hsub A
  have hB := sum_map_inside_mono hsub B
  omega

private theorem insideWeight_le_totalWeight (F : List (WeightedEdge n ℕ)) (t : List (Fin n)) :
    insideWeight F t ≤ totalWeight F := by
  unfold insideWeight totalWeight
  induction F with
  | nil => exact le_rfl
  | cons f F ih =>
    simp only [List.map_cons, List.sum_cons]
    have : (if f.u ∈ t ∧ f.v ∈ t then f.weight else 0) ≤ f.weight := by
      split_ifs
      · exact le_rfl
      · exact Nat.zero_le _
    omega

/-- The charging invariant: once the tour has two vertices, it costs at most twice the tree
edges inside it. -/
private theorem cycleCost_growTour_le {δ : Fin n → Fin n → ℕ} (hsymm : ∀ x y, δ x y = δ y x)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) {F : List (WeightedEdge n ℕ)}
    (hw : ∀ e ∈ F, e.weight = δ e.u e.v) (k : ℕ) {t : List (Fin n)}
    (ht : 2 ≤ t.length → cycleCost δ t ≤ 2 * insideWeight F t) :
    2 ≤ (growTour F k t).length →
      cycleCost δ (growTour F k t) ≤ 2 * insideWeight F (growTour F k t) := by
  induction k generalizing t with
  | zero => exact ht
  | succ k ih =>
    cases h : F.find? (crosses t) with
    | none => simpa only [growTour, h] using ht
    | some e =>
      simp only [growTour, h]
      apply ih
      intro _
      have heF := List.mem_of_find?_eq_some h
      obtain ⟨a, b, hab, ha, hb, heq⟩ := growStep_spec (List.find?_some h)
      have hperm := insertAfter_perm b ha
      have hsub : t ⊆ growStep t e := fun x hx => by
        rw [heq]
        exact hperm.symm.subset (List.mem_cons_of_mem _ hx)
      have hbin : b ∈ growStep t e := by
        rw [heq]
        exact hperm.symm.subset List.mem_cons_self
      have hw2 : δ a b + δ b a = 2 * e.weight := by
        rw [hw e heF]
        have := hsymm e.u e.v
        rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      have hinside := insideWeight_add_le hsub heF
        (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> tauto)
        (by rcases hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact ⟨by tauto, by tauto⟩)
      have hcost : cycleCost δ (insertAfter a b t) ≤ 2 * insideWeight F t + (δ a b + δ b a) := by
        by_cases h2 : 2 ≤ t.length
        · have := cycleCost_insertAfter_le δ htri b ha
          have := ht h2
          omega
        · obtain ⟨A, B, rfl, hins⟩ := exists_eq_insertAfter b ha
          simp only [List.length_append, List.length_cons] at h2
          rw [hins, List.eq_nil_of_length_eq_zero (show A.length = 0 by omega),
            List.eq_nil_of_length_eq_zero (show B.length = 0 by omega), List.nil_append,
            cycleCost_pair]
          omega
      rw [← heq] at hcost
      omega

/-! ### The algorithm -/

/-- The complete graph on `Fin n`, the edge from `i` to `j` weighted by `δ i j`. -/
@[expose] def completeEdges (δ : Fin n → Fin n → ℕ) : List (WeightedEdge n ℕ) :=
  (List.finRange n).flatMap fun i => (List.finRange n).map fun j => ⟨i, j, δ i j⟩

theorem mem_completeEdges {δ : Fin n → Fin n → ℕ} {e : WeightedEdge n ℕ} :
    e ∈ completeEdges δ ↔ e.weight = δ e.u e.v := by
  cases e with
  | mk u v w => simp [completeEdges, eq_comm]

/-- **The MST tour**: grow a tour from vertex `0` along the minimum spanning tree that Kruskal's
algorithm computes on the complete graph weighted by `δ`. -/
@[expose] def mstTour (δ : Fin n → Fin n → ℕ) : List (Fin n) :=
  if h : 0 < n then growTour (kruskalEdges (completeEdges δ)) n [⟨0, h⟩] else []

theorem mstTour_of_pos (δ : Fin n → Fin n → ℕ) (h : 0 < n) :
    mstTour δ = growTour (kruskalEdges (completeEdges δ)) n [⟨0, h⟩] :=
  dite_eq_left h

/-- Kruskal's tree on the complete graph connects all vertices. -/
theorem eqvGen_kruskalEdges_completeEdges (δ : Fin n → Fin n → ℕ) (a b : Fin n) :
    Relation.EqvGen (fun x y => ∃ e ∈ kruskalEdges (completeEdges δ), x = e.u ∧ y = e.v) a b := by
  rw [← rel_edgePartition_iff_eqvGen, edgePartition_kruskalEdges, rel_edgePartition_iff_eqvGen]
  exact .rel _ _ ⟨⟨a, b, δ a b⟩, mem_completeEdges.2 rfl, rfl, rfl⟩

/-- **Feasibility.** The MST tour visits every vertex exactly once. -/
theorem mstTour_perm (δ : Fin n → Fin n → ℕ) : (mstTour δ).Perm (List.finRange n) := by
  by_cases h : 0 < n
  · rw [mstTour_of_pos δ h]
    refine (List.perm_ext_iff_of_nodup (nodup_growTour _ n (List.nodup_singleton _))
      (List.nodup_finRange n)).2 fun x => ?_
    simp only [List.mem_finRange, iff_true]
    exact mem_growTour (eqvGen_kruskalEdges_completeEdges δ) (List.nodup_singleton _)
      (List.cons_ne_nil _ _) (by simp only [List.length_singleton]; omega) x
  · obtain rfl : n = 0 := by omega
    simp [mstTour]

/-- **The upper bound** ([WilliamsonShmoys2011], proof of Theorem 2.11): for symmetric `δ` with
the triangle inequality and at least two vertices, the MST tour costs at most twice the tree. -/
theorem cycleCost_mstTour_le_two_mul_totalWeight {δ : Fin n → Fin n → ℕ}
    (hsymm : ∀ x y, δ x y = δ y x) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) (hn : 2 ≤ n) :
    cycleCost δ (mstTour δ) ≤ 2 * totalWeight (kruskalEdges (completeEdges δ)) := by
  have hlen : (mstTour δ).length = n := by
    rw [(mstTour_perm δ).length_eq, List.length_finRange]
  have h0 : 0 < n := by omega
  have hw : ∀ e ∈ kruskalEdges (completeEdges δ), e.weight = δ e.u e.v := fun e he =>
    mem_completeEdges.1 ((kruskalEdges_subperm _).subset he)
  have := cycleCost_growTour_le hsymm htri hw n (t := [⟨0, h0⟩])
    (fun h => absurd h (by simp))
  rw [← mstTour_of_pos δ h0] at this
  have hle := insideWeight_le_totalWeight (kruskalEdges (completeEdges δ)) (mstTour δ)
  have := this (by omega)
  omega

/-! ### The lower bound -/

private theorem eqvGen_getElem_zero {α : Type*} {R : α → α → Prop} {q : List α}
    (hR : ∀ i (h : i + 1 < q.length), R q[i] q[i + 1]) (h0 : 0 < q.length) (i : ℕ)
    (hi : i < q.length) : Relation.EqvGen R (q[0]'h0) (q[i]'hi) := by
  induction i with
  | zero => exact .refl _
  | succ i ih => exact .trans _ _ _ (ih (by omega)) (.rel _ _ (hR i hi))

/-- Kruskal's tree on the complete graph weighs at most any duplicate-free list of its edges that
connects all vertices. -/
theorem totalWeight_kruskalEdges_completeEdges_le (δ : Fin n → Fin n → ℕ)
    {H : List (WeightedEdge n ℕ)} (hHnd : H.Nodup) (hHw : ∀ e ∈ H, e.weight = δ e.u e.v)
    (hconn : ∀ x y : Fin n, Relation.EqvGen (fun a b => ∃ e ∈ H, a = e.u ∧ b = e.v) x y) :
    totalWeight (kruskalEdges (completeEdges δ)) ≤ totalWeight H := by
  have hHsub : H.Subperm (completeEdges δ) :=
    hHnd.subperm fun e he => mem_completeEdges.2 (hHw e he)
  have hpart : edgePartition H = edgePartition (completeEdges δ) := by
    ext x y
    rw [(rel_edgePartition_iff_eqvGen _ x y).2 (hconn x y),
      (rel_edgePartition_iff_eqvGen _ x y).2
        (.rel _ _ ⟨⟨x, y, δ x y⟩, mem_completeEdges.2 rfl, rfl, rfl⟩)]
  have hsf : IsSpanningForest (completeEdges δ) (kruskalEdges H) :=
    ⟨(kruskalEdges_subperm H).trans hHsub, kruskalEdges_isAcyclic H,
      (edgePartition_kruskalEdges H).trans hpart⟩
  calc totalWeight (kruskalEdges (completeEdges δ)) ≤ totalWeight (kruskalEdges H) :=
        (kruskalEdges_isMinSpanningForest _).2 _ hsf
    _ ≤ totalWeight H := totalWeight_kruskalEdges_le H fun _ _ => Nat.zero_le _

/-- **The lower bound** ([WilliamsonShmoys2011], Lemma 2.10): the minimum spanning tree of the
complete graph costs at most any closed walk visiting every vertex exactly once. The tour's edges
form a connected subgraph of the complete graph, so Kruskal's forest of them is a spanning forest,
which weighs at least the minimum spanning tree and at most the tour. -/
theorem totalWeight_kruskalEdges_le_cycleCost (δ : Fin n → Fin n → ℕ) {q : List (Fin n)}
    (hq : q.Nodup) (hcov : ∀ x, x ∈ q) :
    totalWeight (kruskalEdges (completeEdges δ)) ≤ cycleCost δ q := by
  set H : List (WeightedEdge n ℕ) :=
    (q.zip (q.rotate 1)).map fun p => ⟨p.1, p.2, δ p.1 p.2⟩ with hH
  have hHw : totalWeight H = cycleCost δ q := by
    simp only [totalWeight, hH, cycleCost, List.map_map]
    rw [← List.map_uncurry_zip_eq_zipWith]
    rfl
  rw [← hHw]
  refine totalWeight_kruskalEdges_completeEdges_le δ ?_ ?_ ?_
  · have hmap : H.map WeightedEdge.u = q := by
      simp only [hH, List.map_map]
      exact List.map_fst_zip (by simp)
    exact List.Nodup.of_map _ (hmap ▸ hq)
  · intro e he
    obtain ⟨p, -, rfl⟩ := List.mem_map.1 he
    rfl
  · -- the tour's consecutive vertices are joined by its edges, so all vertices are connected
    intro x y
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem (hcov x)
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (hcov y)
    have h0 : 0 < q.length := by omega
    have hR : ∀ k (hk : k + 1 < q.length), ∃ e ∈ H, q[k] = e.u ∧ q[k + 1] = e.v := by
      intro k hk
      refine ⟨H[k]'(by simp [hH]; omega), List.getElem_mem _, ?_, ?_⟩
      · simp [hH]
      · simp [hH, List.getElem_rotate, Nat.mod_eq_of_lt hk]
    exact .trans _ _ _ (.symm _ _ (eqvGen_getElem_zero hR h0 i hi))
      (eqvGen_getElem_zero hR h0 j hj)

/-! ### The factor 2 -/

/-- **The MST 2-approximation for metric TSP** ([WilliamsonShmoys2011], Section 2.4): for
symmetric `δ` with the triangle inequality, the MST tour costs at most twice any closed walk
visiting every vertex exactly once, in particular an optimal tour. -/
theorem cycleCost_mstTour_le_two_mul {δ : Fin n → Fin n → ℕ} (hsymm : ∀ x y, δ x y = δ y x)
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) {q : List (Fin n)} (hq : q.Nodup)
    (hcov : ∀ x, x ∈ q) : cycleCost δ (mstTour δ) ≤ 2 * cycleCost δ q := by
  rcases Nat.lt_or_ge n 2 with hn | hn
  · have hperm : (mstTour δ).Perm q := (mstTour_perm δ).trans
      ((List.perm_ext_iff_of_nodup (List.nodup_finRange n) hq).2 (by simp [hcov]))
    have hlen : q.length ≤ n := by simpa using hq.length_le_card
    have hm : mstTour δ = q := by
      match q, hperm, hlen with
      | [], hperm, _ => exact hperm.eq_nil
      | [_], hperm, _ => exact List.perm_singleton.1 hperm
      | _ :: _ :: _, _, hlen =>
        simp only [List.length_cons] at hlen
        omega
    rw [hm]
    omega
  · have := totalWeight_kruskalEdges_le_cycleCost δ hq hcov
    have := cycleCost_mstTour_le_two_mul_totalWeight hsymm htri hn
    omega

end Cslib.Algorithms.Lean.TSP
