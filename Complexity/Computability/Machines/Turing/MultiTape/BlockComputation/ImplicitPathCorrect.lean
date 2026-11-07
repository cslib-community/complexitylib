/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitPath
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputationTree
import Mathlib.Data.List.GetD
import Complexity.Foundations.Data.List.Lookup

/-!
# Correct implicit block-tree navigation

Numeric child selection agrees with the existing descending block tree, including source
padding and out-of-horizon indices. Every child is no later than its parent, and a positive
parent strictly decreases. Folding typed child paths preserves that exact interpretation.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ImplicitPath

/-- A provider is either the source or the successor of an earlier interval. -/
theorem provider_le (k σ n : ℕ) (p : Fin (k * 3)) : provider k (σ, n) p ≤ n := by
  unfold provider
  rcases finProdFinEquiv.symm p with ⟨h, δ⟩
  cases hs : ScheduleRead.search k (h + 1) (σ, n, δ) with
  | none => simp [hs]
  | some j =>
    have hj := ScheduleRead.searchIterate_latest_bound k (h + 1) (σ, n, δ) n j hs
    simp only [hs, Option.map_some, Option.getD_some]
    omega

/-- Every numeric child of a positive parent is strictly earlier, even malformed requests. -/
theorem child_lt (k σ q n j : ℕ) (hn : 0 < n) : child k (σ, q, n, j) < n := by
  cases n with
  | zero => omega
  | succ n =>
    simp only [child]
    split_ifs with h hzero
    · omega
    · have hindex : j - 1 < k * 3 := by omega
      rw [providers, List.getD_ofFn_of_lt _ hindex]
      have hp := provider_le k σ n ⟨j - 1, hindex⟩
      omega
    · omega

/-- No child advances the current interval. -/
theorem child_le (k σ q n j : ℕ) : child k (σ, q, n, j) ≤ n := by
  cases n with
  | zero => simp [child]
  | succ n => exact (child_lt k σ q (n + 1) j (by omega)).le

/-- Numeric navigation agrees with the existing functional tree's typed child map. -/
theorem child_eq {k q : ℕ} (σ : ℕ) (n : ℕ) (j : Fin (k * 3 + 1)) :
    child k (σ, q, n, j) =
      BlockComputation.child (scheduleOfNat k q σ) n j := by
  cases n with
  | zero => rfl
  | succ n =>
    by_cases hn : n < q
    · simp only [child, hn, j.isLt, and_self, ↓reduceIte, BlockComputation.child]
      refine Fin.cases ?_ (fun p => ?_) j
      · simp
      · simp only [Fin.val_succ, Fin.cases_succ, Nat.add_sub_cancel_right]
        have hp : (p.val + 1 ≠ 0) := by omega
        simp only [hp, ↓reduceIte, providers]
        rw [List.getD_ofFn_of_lt _ p.isLt]
        unfold provider
        rcases hd : finProdFinEquiv.symm p with ⟨h, δ⟩
        simp only [↓reduceDIte]
        rw [ScheduleRead.search_eq_lastBefore σ ⟨n, hn⟩ h δ]
        cases lastBefore (InWindow (scheduleOfNat k q σ) h
          (portBlock (scheduleOfNat k q σ) ⟨n, hn⟩ h δ)) ⟨n, hn⟩ <;> rfl
    · simp [child, hn, BlockComputation.child]

private theorem foldl_child_eq {k q : ℕ} (σ : ℕ) (path : List (Fin (k * 3 + 1))) (n : ℕ) :
    (path.map Fin.val).foldl (fun index j => child k (σ, q, index, j)) n =
      path.foldl (BlockComputation.child (scheduleOfNat k q σ)) n := by
  induction path generalizing n with
  | nil => rfl
  | cons j path ih =>
    simp only [List.map_cons, List.foldl_cons, child_eq]
    exact ih _

/-- Walking the stored numeric path is exactly walking the existing descending tree's path. -/
theorem walk_eq {k q : ℕ} (σ : ℕ) (path : List (Fin (k * 3 + 1))) :
    walk k (σ, q, path.map Fin.val) =
      path.foldl (BlockComputation.child (scheduleOfNat k q σ)) q :=
  foldl_child_eq σ path q

/-- A walked interval stays within its initial horizon. -/
theorem walk_le (k σ q : ℕ) (path : List ℕ) : walk k (σ, q, path) ≤ q := by
  unfold walk
  have hfold (path : List ℕ) (n : ℕ) :
      path.foldl (fun index j => child k (σ, q, index, j)) n ≤ n := by
    induction path generalizing n with
    | nil => exact le_rfl
    | cons j path ih =>
      exact (ih _).trans (child_le k σ q n j)
  exact hfold path q

end Turing.MultiTapePTM.BlockComputation.ImplicitPath
