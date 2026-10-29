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
open Cslib.Logic.PL.CNF (normalizeDeclaredLeaf)
open Cslib.Complexity.CountingSparsify Turing.MultiTapeTM

/-- Concrete `countingDepthCoeff` and `countingBChoiceCoeff` values and unconditional
`CountingTreeBound` witnesses across `K = 1, 2, 3`. -/
example :
    countingDepthCoeff 1 2 = 0 ∧
    countingBChoiceCoeff 1 = 0 ∧
    countingDepthCoeff 2 2 = 4 ∧
    countingBChoiceCoeff 2 = 4 ∧
    countingDepthCoeff 3 2 = 28 ∧
    countingBChoiceCoeff 3 = 16 ∧
    Nonempty (CountingTreeBound 2 1 1 (countingDepthCoeff 1 2) (by decide) (by decide)) ∧
    -- The 2-CNF budget is 4 * Nat.clog 2 (4 * 4 * 64) = 40 ≤ 64.
    Nonempty (CountingTreeBound 64 2 1 (countingDepthCoeff 2 64) (by decide) (by decide)) ∧
    -- The 3-CNF budget is 16 * Nat.clog 2 (4 * 6148 * 512) = 384 ≤ 512.
    Nonempty (CountingTreeBound 512 3 1 (countingDepthCoeff 3 512) (by decide) (by decide)) ∧
    Nonempty (CountingTreeBound (countingThresholdBase 3 1) 3 1
      (countingDepthCoeff 3 (countingThresholdBase 3 1))
      ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase 3 1)) (by decide)) :=
  ⟨by decide, by decide, by decide, by decide, by decide, by decide,
    ⟨countingTreeBound_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
    ⟨countingTreeBound_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
    ⟨countingTreeBound_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)⟩,
    ⟨countingTreeBound_countingThresholdBase (by decide) (by decide)⟩⟩

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

/-- Acceptance controls for `searchDeclaredWith` and `normalizeDeclaredLeaf` across `N = 0, 1, 3`,
unit clauses, unnormalized vs normalized declared counts, empty/tautological clauses, and
out-of-range / excessive-width rejections. -/
example :
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 0 [] = 1 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [] = 8 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 1 [[(0, true)]] = 1 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [[(0, true)]] = 4 ∧
    -- Without normalization the declared count 4 hits the internal cap 2^1 = 2,
    -- then scaling by 2^(3 - 1) = 4 gives 8. Normalization gives internal count 1
    -- and the exact declared count 4, including the two unused variables.
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      declaredLeafCounter 3 [[(0, true)]] = 8 ∧
    CNF.modelCountOn [[(0, true)]] (Finset.range 3) = 4 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [[]] = 0 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      (normalizeDeclaredLeaf id declaredLeafCounter) 3 [[(0, true), (0, false)]] = 8 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      occurringLeafCounter 3 [[(3, true)]] = 0 ∧
    searchDeclaredWith id (fun _ => 2) (fun _ => 1) 2 2
      occurringLeafCounter 3 [[(0, true), (1, true), (2, true)]] = 0 := by
  decide

end Cslib.Complexity.CountingTreeBoundTests
