/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteTable
import Mathlib.Tactic

/-!
# History-dependent progress comparison

Finite conditional response kernels may depend on the entire preceding transcript.
`progressExpectation` evaluates a terminal payoff of the number of productive turns.
`bernoulliExpectation` evaluates the same payoff for independent comparison trials.
`progressExpectation_le` proves stochastic domination from a conditional bound at
EVERY history, without assuming independent actual responses.

This is a finite-kernel probability component of [Wang2027], Appendix A.5,
PDF p. 16. It does not implement selection-only cover executions, identify the
comparison with Mathlib's binomial distribution, or prove Theorem 5 in full.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle
open Cslib.Optimization.OneConstraint Finset

/-- Independent Bernoulli comparison, applied to a terminal count payoff. -/
@[expose] def bernoulliExpectation (p : ℝ) (f : ℕ → ℝ) : ℕ → ℕ → ℝ
  | 0, k => f k
  | n + 1, k => (1 - p) * bernoulliExpectation p f n k +
      p * bernoulliExpectation p f n (k + 1)

/-- Full-response conditional execution. Histories are stored newest response first;
responses may encode batches, costs and arbitrary auxiliary information. -/
@[expose] def progressExpectation {Ω : Type} [Fintype Ω]
    (law : List Ω → Distribution Ω ℝ) (productive : List Ω → Ω → Bool)
    (f : ℕ → ℝ) : ℕ → List Ω → ℕ → ℝ
  | 0, _, k => f k
  | n + 1, h, k => (law h).mean fun x =>
      progressExpectation law productive f n (x :: h) (k + if productive h x then 1 else 0)

/-- Monotone terminal payoffs remain monotone after independent comparison trials. -/
theorem bernoulliExpectation_mono (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (f : ℕ → ℝ) (hf : Monotone f) (n : ℕ) :
    Monotone (bernoulliExpectation p f n) := by
  induction n with
  | zero => exact hf
  | succ n ih =>
    intro a b hab
    exact add_le_add (mul_le_mul_of_nonneg_left (ih hab) (by linarith))
      (mul_le_mul_of_nonneg_left (ih (Nat.add_le_add_right hab 1)) hp)

private theorem mean_binary {Ω : Type} [Fintype Ω] (w : Distribution Ω ℝ)
    (b : Ω → Bool) (a c : ℝ) :
    w.mean (fun x => if b x then c else a) =
      a + (c - a) * w.mean (fun x => if b x then 1 else 0) := by
  have heq : (fun x => if b x then c else a) =
      (fun x => a + (c - a) * (if b x then 1 else 0)) := by
    funext x
    split_ifs <;> ring
  rw [heq, Distribution.mean_add, Distribution.mean_const, Distribution.mean_mul]

/-- Every increasing payoff of the actual progress count is bounded by its
independent Bernoulli counterpart if every conditional progress probability is at
most `p`. The law can change with every response and includes correlations. -/
theorem progressExpectation_le {Ω : Type} [Fintype Ω]
    (law : List Ω → Distribution Ω ℝ) (productive : List Ω → Ω → Bool)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hprob : ∀ h, (law h).mean (fun x => if productive h x then 1 else 0) ≤ p)
    (f : ℕ → ℝ) (hf : Monotone f) (n : ℕ) (h : List Ω) (k : ℕ) :
    progressExpectation law productive f n h k ≤ bernoulliExpectation p f n k := by
  induction n generalizing h k with
  | zero => exact le_rfl
  | succ n ih =>
    have hm := bernoulliExpectation_mono p hp hp' f hf n
    calc
      progressExpectation law productive f (n + 1) h k ≤
          (law h).mean (fun x => bernoulliExpectation p f n
            (k + if productive h x then 1 else 0)) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ih _ _) ((law h).nonneg x)
      _ = bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) *
            (law h).mean (fun x => if productive h x then 1 else 0) := by
        have heq : (fun x => bernoulliExpectation p f n
            (k + if productive h x then 1 else 0)) =
            (fun x => if productive h x then bernoulliExpectation p f n (k + 1)
              else bernoulliExpectation p f n k) := by
          funext x
          split_ifs <;> simp
        rw [heq, mean_binary]
      _ ≤ bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) * p :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hprob h)
          (sub_nonneg.mpr (hm (Nat.le_succ k)))) _
      _ = bernoulliExpectation p f (n + 1) k := by
        simp only [bernoulliExpectation]
        ring

/-- A conditional lower progress envelope gives the reverse comparison for every
increasing terminal payoff. No independence of actual responses is required. -/
theorem le_progressExpectation {Ω : Type} [Fintype Ω]
    (law : List Ω → Distribution Ω ℝ) (productive : List Ω → Ω → Bool)
    (p : ℝ) (hp : 0 ≤ p) (hp' : p ≤ 1)
    (hprob : ∀ h, (law h).mean (fun x => if productive h x then 1 else 0) ≥ p)
    (f : ℕ → ℝ) (hf : Monotone f) (n : ℕ) (h : List Ω) (k : ℕ) :
    progressExpectation law productive f n h k ≥ bernoulliExpectation p f n k := by
  induction n generalizing h k with
  | zero => exact le_rfl
  | succ n ih =>
    have hm := bernoulliExpectation_mono p hp hp' f hf n
    calc
      progressExpectation law productive f (n + 1) h k ≥
          (law h).mean (fun x => bernoulliExpectation p f n
            (k + if productive h x then 1 else 0)) :=
        sum_le_sum fun x _ => mul_le_mul_of_nonneg_left (ih _ _) ((law h).nonneg x)
      _ = bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) *
            (law h).mean (fun x => if productive h x then 1 else 0) := by
        have heq : (fun x => bernoulliExpectation p f n
            (k + if productive h x then 1 else 0)) =
            (fun x => if productive h x then bernoulliExpectation p f n (k + 1)
              else bernoulliExpectation p f n k) := by
          funext x
          split_ifs <;> simp
        rw [heq, mean_binary]
      _ ≥ bernoulliExpectation p f n k +
          (bernoulliExpectation p f n (k + 1) - bernoulliExpectation p f n k) * p :=
        add_le_add_right (mul_le_mul_of_nonneg_left (hprob h)
          (sub_nonneg.mpr (hm (Nat.le_succ k)))) _
      _ = bernoulliExpectation p f (n + 1) k := by
        simp only [bernoulliExpectation]
        ring

end Cslib.Probability.StochasticOracle
