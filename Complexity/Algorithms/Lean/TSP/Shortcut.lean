/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Euler.Circuit
public import Complexity.Algorithms.Lean.TSP.MSTTour

/-!
# Shortcutting closed walks

Under the triangle inequality, skipping vertices of a closed walk does not increase its cost
([WilliamsonShmoys2011], Section 2.4, proof of Theorem 2.12). In particular, the distinct vertices
of an Euler circuit of a multigraph `H`, visited in order, form a closed walk costing at most the
total weight of `H`. This is the last step of the double-tree algorithm and of Christofides'
algorithm.

## Model

Closed walks are lists of vertices with cost `Cslib.Algorithms.Lean.TSP.cycleCost`; walks along
consecutive pairs and Euler circuits are those of `Cslib.Algorithms.Lean.Euler`. Shortcutting is
modelled by `List.Sublist`: any subsequence of a closed walk is a shortcut of it. Mathlib's
`List.dedup` keeps the *last* occurrence of each vertex, whereas [WilliamsonShmoys2011] keeps the
first; both are subsequences, and the cost bound only uses that.

## Main results

* `cycleCost_cons_eq_sum_consecutivePairs`: the cost of a closed walk from `a` is the cost of the
  walk `a :: L ++ [a]` along its consecutive pairs.
* `cycleCost_le_of_sublist`: shortcutting does not increase the cost.
* `cycleCost_dedup_le_of_isEulerCircuit`: for a symmetric cost, the shortcut Euler circuit costs at
  most its multigraph.

## References

* [D. P. Williamson and D. B. Shmoys, *The Design of Approximation
  Algorithms*][WilliamsonShmoys2011], Section 2.4.
-/

public section

namespace Cslib.Algorithms.Lean.TSP

open Cslib.Algorithms.Lean.Euler

variable {α : Type*}

/-- The cost of a closed walk from `a` is the cost of the walk `a :: L ++ [a]` along consecutive
pairs. -/
theorem cycleCost_cons_eq_sum_consecutivePairs (δ : α → α → ℕ) (a : α) (L : List α) :
    cycleCost δ (a :: L) = ((a :: L ++ [a]).consecutivePairs.map fun e => δ e.1 e.2).sum := by
  have hrot : (a :: L).rotate 1 = L ++ [a] := by simp [List.rotate_cons_succ]
  have hz := List.zip_append (r₁ := [a]) (r₂ := ([] : List α))
    (show (a :: L).length = (L ++ [a]).length by simp)
  rw [List.append_nil, List.zip_nil_right, List.append_nil] at hz
  have ht : (a :: L ++ [a]).tail = L ++ [a] := rfl
  rw [cycleCost, hrot, ← List.map_uncurry_zip_eq_zipWith, List.consecutivePairs, ht, hz]
  rfl

private theorem sum_walk_le_of_sublist (δ : α → α → ℕ) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {l₁ l₂ : List α} (h : l₁.Sublist l₂) (a b : α) :
    ((a :: l₁ ++ [b]).consecutivePairs.map fun e => δ e.1 e.2).sum ≤
      ((a :: l₂ ++ [b]).consecutivePairs.map fun e => δ e.1 e.2).sum := by
  induction h generalizing a with
  | slnil => exact le_rfl
  | cons x _ ih =>
    refine (ih a).trans ?_
    rename_i l₁ l₂ _
    simp only [List.cons_append, consecutivePairs_cons_cons, List.map_cons, List.sum_cons]
    cases l₂ with
    | nil =>
      simp only [List.nil_append, consecutivePairs_cons_cons, consecutivePairs_singleton,
        List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
      have := htri a x b
      omega
    | cons y l₂ =>
      simp only [List.cons_append, consecutivePairs_cons_cons, List.map_cons, List.sum_cons]
      have := htri a x y
      omega
  | cons_cons x _ ih =>
    simp only [List.cons_append, consecutivePairs_cons_cons, List.map_cons, List.sum_cons]
    have := ih x
    simp only [List.cons_append] at this
    omega

/-- **Shortcutting** ([WilliamsonShmoys2011], Section 2.4): under the triangle inequality,
skipping vertices of a closed walk does not increase its cost. -/
theorem cycleCost_le_of_sublist (δ : α → α → ℕ) (htri : ∀ x y z, δ x z ≤ δ x y + δ y z)
    {l₁ l₂ : List α} (h : l₁.Sublist l₂) : cycleCost δ l₁ ≤ cycleCost δ l₂ := by
  cases l₁ with
  | nil => exact Nat.zero_le _
  | cons a l =>
    obtain ⟨r₁, r₂, rfl, ha, hl⟩ := List.cons_sublist_iff.1 h
    obtain ⟨P, Q, rfl⟩ := List.append_of_mem ha
    have hrot : cycleCost δ (P ++ a :: Q ++ r₂) = cycleCost δ (a :: (Q ++ r₂ ++ P)) := by
      rw [← cycleCost_rotate δ _ P.length, List.append_assoc, List.rotate_append_length_eq]
      simp
    rw [hrot, cycleCost_cons_eq_sum_consecutivePairs, cycleCost_cons_eq_sum_consecutivePairs]
    exact sum_walk_le_of_sublist δ htri
      ((hl.trans (List.sublist_append_right Q r₂)).trans (List.sublist_append_left _ P)) a a

variable [DecidableEq α]

/-- **Shortcutting an Euler circuit**: under symmetry and the triangle inequality, the closed walk
visiting the distinct vertices of an Euler circuit of a nonempty multigraph `H` (in order of last
occurrence) costs at most the total weight of `H`. -/
theorem cycleCost_dedup_le_of_isEulerCircuit {δ : α → α → ℕ}
    (htri : ∀ x y z, δ x z ≤ δ x y + δ y z) (hsymm : ∀ x y, δ x y = δ y x)
    {H : List (α × α)} {u : α} {w : List α} (hw : IsEulerCircuit H u w) (hH : H ≠ []) :
    cycleCost δ w.dedup ≤ (H.map fun e => δ e.1 e.2).sum := by
  rw [← sum_map_consecutivePairs_eq hsymm hw]
  obtain ⟨w', rfl⟩ := List.head?_eq_some_iff.mp hw.head
  obtain ⟨R, hR⟩ : ∃ R, w' = R ++ [u] := by
    cases w' with
    | nil =>
      have := hw.perm
      simp only [consecutivePairs_singleton, List.map_nil] at this
      exact absurd (List.map_eq_nil_iff.1 this.symm.eq_nil) hH
    | cons b w' =>
      have := hw.getLast
      rw [List.getLast?_cons_cons] at this
      exact List.getLast?_eq_some_iff.1 this
  subst hR
  rw [List.dedup_cons_of_mem (by simp)]
  refine (cycleCost_le_of_sublist δ htri (List.dedup_sublist _)).trans ?_
  rw [show R ++ [u] = (u :: R).rotate 1 by simp [List.rotate_cons_succ], cycleCost_rotate,
    cycleCost_cons_eq_sum_consecutivePairs]
  simp

end Cslib.Algorithms.Lean.TSP
