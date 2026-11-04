/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.DensityBranchCounting
import Complexity.Computability.Complexity.FineGrained.CountingNativeModelCount

/-! # One model counter with both bounds of Theorem 1.1: checked instances

The threshold `n ⌈log₂ ⌈log₂ n⌉⌉` at small sizes, formulas on either side of it, and the two
earlier counters recovered from the single one: its bound on every formula gives the
interpolation-scale counter, and its fixed-density bound gives the shape of the
tensor-contraction counter. -/

namespace ComplexityTests.DensityBranchCounting

open Cslib.Logic.PL Cslib.Complexity Cslib.Complexity.DensityBranchCounting
  Cslib.Complexity.SubexponentialSAT Turing.MultiTapeTM

-- `λ = ⌈log₂ n⌉` and `ν = ⌈log₂ λ⌉`: `ν = 0` below three variables, then `1, 2, 3, …`.
example : threshold 2 = 0 ∧ threshold 3 = 3 ∧ threshold 4 = 4 ∧ threshold 16 = 32 ∧
    threshold 20 = 60 ∧ threshold 256 = 768 ∧ threshold 257 = 1028 := by decide

/-- Four clauses on four variables: at the threshold, so the contraction branch. -/
def sparse : CNF ℕ := [[(0, true), (1, true)], [(1, false), (2, true)], [(2, false), (3, true)],
  [(3, false), (0, false)]]

example : sparse.length ≤ threshold sparse.numVars := by decide

/-- Three clauses on two variables: above the threshold `0`, so the dense branch. -/
def dense : CNF ℕ := [[(0, true), (1, true)], [(0, false), (1, true)], [(0, true), (1, false)]]

example : threshold dense.numVars < dense.length := by decide

-- The single counter has the interpolation-scale bound of the Section 6.4 counter.
example (k : ℕ) : ∃ (count : CNF ℕ → ℕ) (A e b : ℕ),
    (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
    ComputableInO count encCNF encNat
      (fun φ => ⌈(2 : ℝ) ^ ((A : ℝ) * interpolationScale φ.numVars)⌉₊ *
        ((encCNF φ).length + 1) ^ e)
      (fun φ => ((encCNF φ).length + 1) ^ b) := by
  obtain ⟨count, T, S, A, e, b, hcount, hc, hS, hT, -, -⟩ := exists_modelCounter k
  exact ⟨count, A, e, b, hcount, hc.mono_le hT fun φ => (hS φ).le⟩

-- The same counter, at each density, has the exponent `A (n + 1) / √⌊log₂ (n + 2)⌋` of the
-- fixed-density tensor-contraction counter.
example (k : ℕ) : ∃ (count : CNF ℕ → ℕ) (T S : CNF ℕ → ℕ) (e b : ℕ),
    (∀ φ : CNF ℕ, (∀ c ∈ φ, c.length ≤ k) → count φ = φ.modelCount) ∧
    ComputableInO count encCNF encNat T S ∧
    (∀ φ, S φ = ((encCNF φ).length + 1) ^ b) ∧
    ∀ D : ℕ, ∃ A : ℕ, ∀ φ : CNF ℕ, φ.length ≤ D * φ.numVars →
      T φ ≤ 2 ^ (A * (φ.numVars + 1) / Nat.sqrt (Nat.log 2 (φ.numVars + 2))) *
        ((encCNF φ).length + 1) ^ e := by
  obtain ⟨count, T, S, A, e, b, hcount, hc, hS, -, -, hD⟩ := exists_modelCounter k
  refine ⟨count, T, S, e, b, hcount, hc, hS, fun D => ?_⟩
  obtain ⟨A', hA'⟩ := hD D
  exact ⟨A', fun φ hφ => (hA' φ hφ).trans (Nat.mul_le_mul_right _
    (Nat.pow_le_pow_right (by norm_num) (Nat.div_le_div_right (Nat.mul_le_mul_left _
      (Nat.le_succ _)))))⟩

end ComplexityTests.DensityBranchCounting
