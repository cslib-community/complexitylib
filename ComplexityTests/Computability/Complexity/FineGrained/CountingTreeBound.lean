/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Complexity.FineGrained.CountingTreeBound

/-!
# Tests for `CountingBounds` and `CountingTreeBound`
-/

@[expose] public section

namespace Cslib.Complexity.CountingTreeBoundTests

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Sparsification Cslib.Logic.PL.ClauseSet.Sparsification
open Cslib.Complexity.CountingSparsify Turing.MultiTapeTM

example : countingDepthCoeff 1 2 = 0 := by decide

example : countingBChoiceCoeff 1 = 0 := by decide

example : countingDepthCoeff 2 2 = 4 := by decide

example : countingBChoiceCoeff 2 = 4 := by decide

example : countingDepthCoeff 3 2 = 28 := by decide

example : countingBChoiceCoeff 3 = 16 := by decide

/-- Unconditional `CountingTreeBound` witness for `K = 1, B = 1, M = 2`. -/
example : CountingTreeBound 2 1 1 (countingDepthCoeff 1 2) (by decide) (by decide) :=
  countingTreeBound_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional `CountingTreeBound` witness for 2-CNF (`K = 2, B = 1, M = 64`), verified by
`decide` on the integer parameter budget `4 * Nat.clog 2 (4 * 4 * 64) = 40 ≤ 64`. -/
example : CountingTreeBound 64 2 1 (countingDepthCoeff 2 64) (by decide) (by decide) :=
  countingTreeBound_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional `CountingTreeBound` witness for 3-CNF (`K = 3, B = 1, M = 512`), verified by
`decide` on the integer parameter budget `16 * Nat.clog 2 (4 * 6148 * 512) = 384 ≤ 512`. -/
example : CountingTreeBound 512 3 1 (countingDepthCoeff 3 512) (by decide) (by decide) :=
  countingTreeBound_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)

/-- Unconditional `CountingTreeBound` witness for 3-CNF at `countingThresholdBase 3 1`. -/
example :
    CountingTreeBound (countingThresholdBase 3 1) 3 1
      (countingDepthCoeff 3 (countingThresholdBase 3 1))
      ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase 3 1)) (by decide) :=
  countingTreeBound_countingThresholdBase (by decide) (by decide)

/-- Model-count correctness of `CountingSparsify.search` on 3-CNF at `(M, K, k, B) = (512, 3, 3, 1)`
without an external `CountingTreeBound` hypothesis. -/
example {g : CNF ℕ → ℕ}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ 3) →
      isSparse (countingThreshold 512) 3 ψ = true → g ψ = ψ.modelCount)
    {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    search 512 3 3 1 g φ = φ.modelCount :=
  search_eq_modelCount_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hg hφ

/-! ### Acceptance controls for `searchDeclaredWith` and `normalizeDeclaredLeaf` -/

/-- Exact occurring-variable leaf counter for concrete test evaluation. -/
def occurringLeafCounter : ℕ × CNF ℕ → ℕ :=
  fun x => x.2.modelCount

/-- Exact declared-range (`Finset.range N`) leaf counter for concrete test evaluation. -/
def declaredLeafCounter : ℕ × CNF ℕ → ℕ :=
  fun x => x.2.modelCountOn (Finset.range x.1)

/-- `N = 0` with the empty formula `[]` returns `1`. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 0 [] = 1 := by
  decide

/-- `N = 3` with the empty formula `[]` returns `2 ^ 3 = 8`. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [] = 8 := by
  decide

/-- The unit formula `[[(0, true)]]` gives `1` at `N = 1` and `4` at `N = 3`. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 1 [[(0, true)]] = 1 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [[(0, true)]] = 4 := by
  decide

/-- Distinguishing occurring-variable leaf counts from declared-`N` leaf counts on `[[(0, true)]]`
at `N = 3`: feeding the unnormalized declared-`N` count `4` directly into `searchDeclaredWith`
hits the internal cap `2 ^ 1 = 2` and scales by `2 ^ (3 - 1) = 4` to yield `8`, whereas
normalizing via `normalizeDeclaredLeaf` yields `1` internally and the exact declared count `4`. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      declaredLeafCounter 3 [[(0, true)]] = 8 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [[(0, true)]] = 4 ∧
    CNF.modelCountOn [[(0, true)]] (Finset.range 3) = 4 := by
  decide

/-- Empty clauses return `0` even when `N = 3`. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [[]] = 0 := by
  decide

/-- A tautological clause `[[(0, true), (0, false)]]` disappearing during normalization retains its
declared-variable contribution at `N = 3` and returns `8`. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [[(0, true), (0, false)]] = 8 := by
  decide

/-- A variable label outside `Finset.range 3` (`[[(3, true)]]`) and an excessive-width clause
(`k = 2` on width `3`) take the guard's zero branch. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      occurringLeafCounter 3 [[(3, true)]] = 0 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      occurringLeafCounter 3 [[(0, true), (1, true), (2, true)]] = 0 := by
  decide

end Cslib.Complexity.CountingTreeBoundTests
