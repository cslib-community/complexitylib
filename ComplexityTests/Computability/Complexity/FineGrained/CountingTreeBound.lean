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

/-- Unconditional `CountingTreeBound` witness for arbitrary `1 ≤ K` and `1 ≤ B` at
`countingThresholdBase K B`. -/
example {K B : ℕ} (hK : 1 ≤ K) (hB : 1 ≤ B) :
    CountingTreeBound (countingThresholdBase K B) K B
      (countingDepthCoeff K (countingThresholdBase K B))
      ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase K B)) hK :=
  countingTreeBound_countingThresholdBase hK hB

/-- Model-count correctness of `CountingSparsify.search` on 3-CNF at `(M, K, k, B) = (512, 3, 3, 1)`
without an external `CountingTreeBound` hypothesis. -/
example {g : CNF ℕ → ℕ}
    (hg : ∀ ψ : CNF ℕ, (∀ c ∈ ψ, c.length ≤ 3) →
      isSparse (countingThreshold 512) 3 ψ = true → g ψ = ψ.modelCount)
    {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length ≤ 3) :
    search 512 3 3 1 g φ = φ.modelCount :=
  search_eq_modelCount_of_budget (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) hg hφ

/-- Unconditional end-to-end counting-sparsification reduction from a dense 3-occurrence model
counter for arbitrary `2 ≤ k ≤ K` and `1 ≤ B` at `countingThresholdBase K B`. -/
example {K k B : ℕ} (hK : 1 ≤ K) (hk2 : 2 ≤ k) (hkK : k ≤ K) (hB : 1 ≤ B)
    {f : CNF ℕ → ℕ} {tf : CNF ℕ → ℕ} (hf : ComputableInO f encCNF encNat tf tf)
    (hf_eq : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars → f χ = χ.modelCount)
    {δ : ℝ} (hδ : 0 ≤ δ) {c e : ℕ}
    (ht : ∀ χ : CNF ℕ, (∀ c ∈ χ, c.length ≤ k) → (∀ v, χ.vars.count v ≤ 3) →
      χ.vars.toFinset = Finset.range χ.numVars →
      (tf χ : ℝ) ≤ c * (2 ^ (δ * χ.numVars) * ((encCNF χ).length + 1) ^ e) + c) :
    (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) →
      search (countingThresholdBase K B) K k B (guardOccurrenceCounter k f) φ = φ.modelCount) ∧
    ∃ T : CNF ℕ → ℕ, ∃ C₀ E : ℕ,
      ComputableInO
        (search (countingThresholdBase K B) K k B (guardOccurrenceCounter k f)) encCNF encNat T T ∧
      ∀ φ : CNF ℕ, (T φ : ℝ) ≤
        C₀ * ((2 : ℝ) ^
            ((1 / B + occBound K (countingThresholdBase K B) * (k * δ)) * φ.numVars) *
          (((encCNF φ).length : ℝ) + 1) ^ E) + C₀ :=
  exists_computableInO_search_threeOccurrence_thresholdBase
    hK hk2 hkK hB hf hf_eq hδ ht

end Cslib.Complexity.CountingTreeBoundTests
