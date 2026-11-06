/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Probability.StochasticOracle.AdaptiveComparison
public import Mathlib.Probability.Distributions.Binomial
import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Tactic

/-!
# Binomial identification of adaptive comparison

`bernoulliExpectation_eq_sum` identifies the existing recurrence with the actual
binomial masses, and `bernoulliExpectation_eq_integral` with Mathlib's binomial law.
These are the finite-horizon comparison variables in [Wang2027], Appendix A.5,
PDF p. 16. Actual progress events remain history dependent.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Finset MeasureTheory

/-- Closed finite-binomial expansion of the independent comparison recurrence. -/
theorem bernoulliExpectation_eq_sum (p : ℝ) (f : ℕ → ℝ) (n k : ℕ) :
    bernoulliExpectation p f n k =
      ∑ i ∈ range (n + 1), (n.choose i : ℝ) * p ^ i * (1 - p) ^ (n - i) * f (k + i) := by
  induction n generalizing k with
  | zero => simp [bernoulliExpectation]
  | succ n ih =>
    rw [bernoulliExpectation, ih, ih]
    symm
    calc
      _ = ∑ i ∈ range (n + 2), ((n + 1).choose i : ℝ) *
          (p ^ i * (1 - p) ^ (n + 1 - i) * f (k + i)) := by
        apply sum_congr rfl
        intro i _
        ring
      _ = _ := Finset.sum_choose_succ_mul
        (fun i j => p ^ i * (1 - p) ^ j * f (k + i)) n
      _ = _ := by
        rw [mul_sum, mul_sum]
        congr 1
        · apply sum_congr rfl
          intro i hi
          have hi' : i ≤ n := by simpa only [mem_range, Nat.lt_succ_iff] using hi
          rw [show n + 1 - i = (n - i) + 1 by omega, pow_succ]
          ring
        · apply sum_congr rfl
          intro i _
          rw [pow_succ]
          rw [show k + 1 + i = k + (i + 1) by omega]
          ring

/-- The comparison recurrence is expectation under Mathlib's actual binomial law. -/
theorem bernoulliExpectation_eq_integral (p : Set.Icc (0 : ℝ) 1)
    (f : ℕ → ℝ) (n k : ℕ) :
    bernoulliExpectation p f n k =
      ∫ i, f (k + i) ∂ProbabilityTheory.binomial n p := by
  rw [ProbabilityTheory.integral_binomial, bernoulliExpectation_eq_sum,
    ← Nat.range_succ_eq_Iic]
  simp only [smul_eq_mul]

/-- A full-history upper envelope bounds actual count tails by binomial tails. -/
theorem progress_tail_le {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (b : List Ω → Ω → Bool) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, (law h).mean (fun x => if b h x then 1 else 0) ≤ p)
    (n r : ℕ) :
    progressExpectation law b (fun k => if r ≤ k then 1 else 0) n [] 0 ≤
      ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial n p := by
  have hm : Monotone (fun k : ℕ => if r ≤ k then (1 : ℝ) else 0) := by
    intro a c hac
    dsimp only
    split_ifs <;> norm_num; omega
  have h := progressExpectation_le law b p p.property.1 p.property.2 hp _ hm n [] 0
  rw [bernoulliExpectation_eq_integral] at h
  simpa only [Nat.zero_add] using h

/-- A lower conditional envelope gives the reverse actual-binomial tail comparison. -/
theorem le_progress_tail {Ω : Type} [Fintype Ω]
    (law : List Ω → Cslib.Optimization.OneConstraint.Distribution Ω ℝ)
    (b : List Ω → Ω → Bool) (p : Set.Icc (0 : ℝ) 1)
    (hp : ∀ h, (p : ℝ) ≤ (law h).mean (fun x => if b h x then 1 else 0))
    (n r : ℕ) :
    (∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial n p) ≤
      progressExpectation law b (fun k => if r ≤ k then 1 else 0) n [] 0 := by
  have hm : Monotone (fun k : ℕ => if r ≤ k then (1 : ℝ) else 0) := by
    intro a c hac
    dsimp only
    split_ifs <;> norm_num; omega
  have h := le_progressExpectation law b p p.property.1 p.property.2 hp _ hm n [] 0
  rw [bernoulliExpectation_eq_integral] at h
  simpa only [Nat.zero_add] using h

end Cslib.Probability.StochasticOracle
