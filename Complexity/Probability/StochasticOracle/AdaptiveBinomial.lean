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
`tsum_binomialFailure` derives the untruncated tail-sum mean `r / p`
for positive productivity; finite truncations are bounded without limit assumptions.
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

/-- Probability of fewer than `r` independent comparison successes after `n` turns.
This is a tail observable of the existing binomial law, not a new distribution. -/
def binomialFailure (p : ℝ) (r n : ℕ) : ℝ :=
  bernoulliExpectation p (fun k => if k < r then 1 else 0) n 0

private theorem bernoulliExpectation_shift (p : ℝ) (f : ℕ → ℝ) (n k : ℕ) :
    bernoulliExpectation p f n (k + 1) =
      bernoulliExpectation p (fun j => f (j + 1)) n k := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih => simp only [bernoulliExpectation, ih]

@[simp] theorem binomialFailure_zero (p : ℝ) (n : ℕ) :
    binomialFailure p 0 n = 0 := by
  have hz : ∀ n k, bernoulliExpectation p (fun _ => (0 : ℝ)) n k = 0 := by
    intro n
    induction n with
    | zero => intro k; rfl
    | succ n ih => intro k; simp only [bernoulliExpectation, ih, mul_zero, add_zero]
  simpa only [binomialFailure, Nat.not_lt_zero, ite_false] using hz n 0

/-- First-step decomposition of a negative-binomial survival probability. -/
theorem binomialFailure_succ (p : ℝ) (r n : ℕ) :
    binomialFailure p (r + 1) (n + 1) =
      (1 - p) * binomialFailure p (r + 1) n + p * binomialFailure p r n := by
  unfold binomialFailure
  rw [bernoulliExpectation, bernoulliExpectation_shift]
  simp only [Nat.add_lt_add_iff_right]

/-- Every finite tail sum is bounded by the untruncated negative-binomial mean.
The proof uses first-step accounting, without assuming a mean or a limit. -/
theorem sum_binomialFailure_le (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ))
    (n r : ℕ) :
    ∑ t ∈ range n, binomialFailure p r t ≤ (r : ℝ) / p := by
  induction n generalizing r with
  | zero => simpa using div_nonneg (Nat.cast_nonneg r) hp.le
  | succ n ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [sum_range_succ']
      simp only [binomialFailure_succ, sum_add_distrib, ← mul_sum]
      have h0 : binomialFailure p (r + 1) 0 = 1 := by
        simp [binomialFailure, bernoulliExpectation]
      rw [h0]
      have h1 := mul_le_mul_of_nonneg_left (ih (r + 1)) (sub_nonneg.mpr p.property.2)
      have h2 := mul_le_mul_of_nonneg_left (ih r) p.property.1
      have he : (1 - (p : ℝ)) * (((r + 1 : ℕ) : ℝ) / p) +
          (p : ℝ) * ((r : ℝ) / p) + 1 = ((r + 1 : ℕ) : ℝ) / p := by
        push_cast
        field_simp
        ring
      nlinarith

/-- Binomial survival probabilities are nonnegative. -/
theorem binomialFailure_nonneg (p : Set.Icc (0 : ℝ) 1) (r n : ℕ) :
    0 ≤ binomialFailure p r n := by
  induction n generalizing r with
  | zero => simp only [binomialFailure, bernoulliExpectation]; split_ifs <;> norm_num
  | succ n ih =>
    cases r with
    | zero => simp
    | succ r =>
      rw [binomialFailure_succ]
      exact add_nonneg (mul_nonneg (sub_nonneg.mpr p.property.2) (ih _))
        (mul_nonneg p.property.1 (ih _))

/-- Positive productivity makes the negative-binomial survival series summable. -/
theorem summable_binomialFailure (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ))
    (r : ℕ) : Summable (binomialFailure p r) :=
  summable_of_sum_range_le (binomialFailure_nonneg p r) (fun n =>
    sum_binomialFailure_le p hp n r)

/-- The untruncated negative-binomial tail sum is exactly `r / p`.
Summability is derived, including `r = 0` and `p = 1`. -/
theorem tsum_binomialFailure (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ))
    (r : ℕ) : ∑' t, binomialFailure p r t = (r : ℝ) / p := by
  induction r with
  | zero => simp
  | succ r ih =>
    have hs := summable_binomialFailure p hp (r + 1)
    have ht := summable_binomialFailure p hp r
    have he := hs.sum_add_tsum_nat_add 1
    simp only [sum_range_one] at he
    have h0 : binomialFailure p (r + 1) 0 = 1 := by
      simp [binomialFailure, bernoulliExpectation]
    rw [h0] at he
    simp only [binomialFailure_succ] at he
    rw [(hs.mul_left _).tsum_add (ht.mul_left _), tsum_mul_left, tsum_mul_left, ih] at he
    have hd : (p : ℝ) * ((r : ℝ) / p) = r := mul_div_cancel₀ _ (ne_of_gt hp)
    rw [hd] at he
    apply (eq_div_iff (ne_of_gt hp)).2
    push_cast
    nlinarith

/-- Survival is the complement of the actual Mathlib binomial upper tail. -/
theorem binomialFailure_eq_complement (p : Set.Icc (0 : ℝ) 1) (r n : ℕ) :
    binomialFailure p r n =
      1 - ∫ i, (if r ≤ i then (1 : ℝ) else 0) ∂ProbabilityTheory.binomial n p := by
  have hi := bernoulliExpectation_eq_integral p (fun i => if r ≤ i then (1 : ℝ) else 0) n 0
  simp only [Nat.zero_add] at hi
  rw [← hi]
  have he : ∀ n k, bernoulliExpectation p (fun i => if i < r then 1 else 0) n k +
      bernoulliExpectation p (fun i => if r ≤ i then 1 else 0) n k = 1 := by
    intro n
    induction n with
    | zero => intro k; simp only [bernoulliExpectation]; split_ifs <;> norm_num <;> omega
    | succ n ih =>
      intro k
      simp only [bernoulliExpectation]
      calc
        _ = (1 - (p : ℝ)) * (bernoulliExpectation p (fun i => if i < r then 1 else 0) n k +
            bernoulliExpectation p (fun i => if r ≤ i then 1 else 0) n k) +
          p * (bernoulliExpectation p (fun i => if i < r then 1 else 0) n (k + 1) +
            bernoulliExpectation p (fun i => if r ≤ i then 1 else 0) n (k + 1)) := by ring
        _ = 1 := by rw [ih, ih]; ring
  have h := he n 0
  simpa only [binomialFailure, Nat.zero_add] using (eq_sub_iff_add_eq.mpr h)

/-- The survival series tends to zero; this supplies a tail-based termination
criterion rather than assuming termination or exchanging a limit and expectation. -/
theorem tendsto_binomialFailure_zero (p : Set.Icc (0 : ℝ) 1) (hp : 0 < (p : ℝ))
    (r : ℕ) : Filter.Tendsto (binomialFailure p r) Filter.atTop (nhds 0) :=
  (summable_binomialFailure p hp r).tendsto_atTop_zero

end Cslib.Probability.StochasticOracle
