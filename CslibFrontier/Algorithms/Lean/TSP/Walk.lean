/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Group.List.Defs
public import Mathlib.Data.List.Rotate
import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# Costs of walks and closed walks

The traveling salesman modules measure a route through a cost function `δ : α → α → W` in two
ways: `walkCost δ a L b` is the cost of the walk from `a` through the entries of `L` in order to
`b`, and `cycleCost δ t` is the cost of the closed walk visiting the entries of `t` in order and
returning to the first. A closed walk is a walk from its first vertex back to itself
(`cycleCost_cons`), and its cost does not depend on the starting point (`cycleCost_rotate`).

## Main definitions

* `Cslib.Algorithms.Lean.TSP.walkCost`: the cost of a walk through a list of vertices.
* `Cslib.Algorithms.Lean.TSP.cycleCost`: the cost of a closed walk.

## Main results

* `walkCost_append_singleton`, `walkCost_map`: extending a walk at its end, relabeling vertices.
* `cycleCost_cons`: a closed walk from `a` is the walk from `a` through the rest back to `a`.
* `cycleCost_rotate`, `cycleCost_append_comm`: a closed walk costs the same from any starting
  point.
-/

public section

namespace Cslib.Algorithms.Lean.TSP

variable {α W : Type*}

/-- The cost `δ a x₀ + δ x₀ x₁ + ⋯ + δ xₖ b` of the walk from `a` through the entries
`x₀, …, xₖ` of `L` in order to `b`. -/
@[expose] def walkCost [Add W] (δ : α → α → W) : α → List α → α → W
  | a, [], b => δ a b
  | a, x :: L, b => δ a x + walkCost δ x L b

/-- Extending a walk by one vertex at its end adds one step. -/
theorem walkCost_append_singleton [AddSemigroup W] (δ : α → α → W) (a : α) (L : List α)
    (x b : α) : walkCost δ a (L ++ [x]) b = walkCost δ a L x + δ x b := by
  induction L generalizing a with
  | nil => rfl
  | cons y L ih => simp only [List.cons_append, walkCost, ih, add_assoc]

/-- Relabeling the vertices of a walk relabels its costs. -/
theorem walkCost_map {β : Type*} [Add W] (f : α → β) (δ : β → β → W) (a : α) (L : List α)
    (b : α) : walkCost δ (f a) (L.map f) (f b) = walkCost (fun x y => δ (f x) (f y)) a L b := by
  induction L generalizing a with
  | nil => rfl
  | cons x L ih => simp only [List.map_cons, walkCost, ih]

/-- The cost of the closed walk visiting the entries of `t` in order and returning to the first:
`δ t₀ t₁ + δ t₁ t₂ + ⋯ + δ tₖ t₀`. A single vertex `a` costs `δ a a`; the empty walk costs `0`. -/
@[expose] def cycleCost (δ : α → α → ℕ) (t : List α) : ℕ :=
  (List.zipWith δ t (t.rotate 1)).sum

/-- A closed walk costs the same from any starting point. -/
theorem cycleCost_rotate (δ : α → α → ℕ) (t : List α) (k : ℕ) :
    cycleCost δ (t.rotate k) = cycleCost δ t := by
  unfold cycleCost
  rw [List.rotate_rotate, Nat.add_comm, ← List.rotate_rotate,
    ← List.zipWith_rotate_distrib _ _ _ _ (List.length_rotate t 1).symm]
  exact (List.rotate_perm _ _).sum_eq

/-- A closed walk through `A` and then `X` costs the same as one through `X` and then `A`. -/
theorem cycleCost_append_comm (δ : α → α → ℕ) (A X : List α) :
    cycleCost δ (A ++ X) = cycleCost δ (X ++ A) := by
  rw [← cycleCost_rotate δ (A ++ X) A.length, List.rotate_append_length_eq]

/-- A closed walk on two vertices goes there and back. -/
theorem cycleCost_pair (δ : α → α → ℕ) (u v : α) : cycleCost δ [u, v] = δ u v + δ v u :=
  rfl

private theorem sum_zipWith_append_singleton (δ : α → α → ℕ) (a x : α) (L : List α) :
    (List.zipWith δ (x :: L) (L ++ [a])).sum = walkCost δ x L a := by
  induction L generalizing x with
  | nil => simp [walkCost]
  | cons y L ih =>
    simp only [List.cons_append, List.zipWith_cons_cons, List.sum_cons, ih, walkCost]

/-- A closed walk from `a` is the walk from `a` through the remaining vertices back to `a`. -/
theorem cycleCost_cons (δ : α → α → ℕ) (a : α) (L : List α) :
    cycleCost δ (a :: L) = walkCost δ a L a := by
  rw [cycleCost, (List.rotate_cons_succ L a 0).trans (List.rotate_zero _),
    sum_zipWith_append_singleton]

end Cslib.Algorithms.Lean.TSP
