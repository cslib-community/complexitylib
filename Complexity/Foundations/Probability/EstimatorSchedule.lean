/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.EstimatorPrecision
public import Complexity.Foundations.Probability.RootMetric.ConditionalWalk
public import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Slack cutoffs and telescoping for additive estimation

This is the integer logarithmic-rate-grid specialization of [OpenAI2026LogSpace,
Sections 7.4–7.5, (7.11)–(7.12), printed pp. 38–40], revision `7ef5c0cc`.
For an integer scale offset `h` and a positive integer cutoff coefficient `c`, the cutoff is
exactly `c * (1 + |h|)`; no ceiling is needed. A prefix through slack `d` includes differences
at budgets `1` through `M - max d cutoff`. This includes empty groups and wholly omitted bins.
The same endpoint function is used at both budgets before taking a difference.

The schedule strictly decreases recursive budgets. Its mean differences telescope, including
zero-budget boundary terms. With precision constant `16 * c`, the existing fourth-moment
scale compensation leaves a summable `2 ^ (-|h|/8)` majorant for actual last-budget child
errors. The source uses eighth moments and has margin `3/8`; our initial margin is `1/4`.
The available-bin estimate does not require activity or positive last budget.

This is the available-scale part of Lemma 7.6, rather than the full mean-prefix theorem.
It does not bound the true contributions of wholly omitted bins, assemble the child norm
comparisons for actual hierarchy tasks, or choose the conditional walks and sum their noise
(Lemmas 7.7–7.8). Those and the recursive estimator remain separate obligations.

## Main definitions

* `Cslib.LogSpaceEstimation.scaleCutoff`: slack reserved for a logarithmic scale.
* `Cslib.LogSpaceEstimation.lastBudget`: the exact budget reached by a prefix.
* `Cslib.LogSpaceEstimation.slackGroup`: difference layers of one dyadic slack group.

## Main results

* `Cslib.LogSpaceEstimation.sum_lastBudget_differences`: endpointwise telescoping.
* `Cslib.LogSpaceEstimation.lastBudget_lt`: strict recursive budget decrease.
* `Cslib.LogSpaceEstimation.scheduled_child_cost_le`: precision compensation on this schedule.
* `Cslib.LogSpaceEstimation.summable_scaleMajorant`: convergence over both scale directions.
* `Cslib.LogSpaceEstimation.tsum_scaleMajorant`: its explicit geometric-series value.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  Sections 7.4–7.5, (7.8)–(7.12), Lemma 7.6, revision `7ef5c0cc`
  (23 September 2026, preprint, not peer reviewed).
-/

public section

namespace Cslib.LogSpaceEstimation

open Finset
open scoped BigOperators

/-- Integer-grid form of the scale-dependent ceiling cutoff. -/
@[expose] def scaleCutoff (c : ℕ) (h : ℤ) : ℕ := c * (1 + h.natAbs)

/-- Last included child budget after all layers of slack at least `d`. -/
@[expose] def lastBudget (M d c : ℕ) (h : ℤ) : ℕ := M - max d (scaleCutoff c h)

/-- Both the prefix slack and the scale cutoff constrain each included positive budget. -/
theorem le_lastBudget_iff {M d c m : ℕ} {h : ℤ} (hm : 0 < m) :
    m ≤ lastBudget M d c h ↔ m + d ≤ M ∧ m + scaleCutoff c h ≤ M := by
  unfold lastBudget
  omega

/-- A scale with cutoff at least the parent budget has no layers in any prefix. -/
theorem lastBudget_eq_zero_of_cutoff_le {M d c : ℕ} {h : ℤ}
    (hM : M ≤ scaleCutoff c h) : lastBudget M d c h = 0 := by
  unfold lastBudget
  omega

/-- Increasing the required slack can only shorten the prefix. -/
theorem lastBudget_antitone (M c : ℕ) (h : ℤ) : Antitone fun d => lastBudget M d c h := by
  intro d e hde
  dsimp only [lastBudget]
  omega

/-- Every included child, including both budgets of each difference, is strictly earlier. -/
theorem lastBudget_lt {M d c : ℕ} {h : ℤ} (hM : 0 < M) (hc : 0 < c) :
    lastBudget M d c h < M := by
  have : 0 < scaleCutoff c h := Nat.mul_pos hc (by omega)
  unfold lastBudget
  omega

/-- The loss at the last budget is bounded even when that budget is zero. -/
theorem budget_loss_le (M d c : ℕ) (h : ℤ) :
    M - lastBudget M d c h ≤ d + scaleCutoff c h := by
  unfold lastBudget
  omega

/-- The paired differences telescope at each actual endpoint. The zero-budget value is
explicit: clients may discard it only after proving that their budget-zero sample is zero. -/
theorem sum_lastBudget_differences {A : Type*} [AddCommGroup A]
    (T : ℕ → A) (M d c : ℕ) (h : ℤ) :
    (∑ m ∈ range (lastBudget M d c h), (T (m + 1) - T m)) =
      T (lastBudget M d c h) - T 0 :=
  sum_range_sub T (lastBudget M d c h)

/-- A dyadic slack group consists of exactly the new difference layers between the prefixes
through `2*d` and `d`. An index `m` denotes the paired child budgets `m+1` and `m`. -/
@[expose] def slackGroup (M d c : ℕ) (h : ℤ) : Finset ℕ :=
  Ico (lastBudget M (2 * d) c h) (lastBudget M d c h)

/-- Membership agrees with the source's interval `d ≤ M-(m+1) < 2*d` and scale cutoff. -/
theorem mem_slackGroup_iff {M d c m : ℕ} {h : ℤ} :
    m ∈ slackGroup M d c h ↔
      m + 1 + scaleCutoff c h ≤ M ∧ d ≤ M - (m + 1) ∧ M - (m + 1) < 2 * d := by
  simp only [slackGroup, mem_Ico, lastBudget]
  omega

/-- One complete group's exact endpoint contribution is a difference of its last-budget
samples. This includes empty groups, which contribute zero. -/
theorem sum_slackGroup_differences {A : Type*} [AddCommGroup A]
    (T : ℕ → A) (M d c : ℕ) (h : ℤ) :
    (∑ m ∈ slackGroup M d c h, (T (m + 1) - T m)) =
      T (lastBudget M d c h) - T (lastBudget M (2 * d) c h) := by
  rw [slackGroup, sum_Ico_eq_sub _ (lastBudget_antitone M c h (by omega)),
    sum_lastBudget_differences, sum_lastBudget_differences]
  abel

/-- Conditional means telescope on each endpoint's actual retained-pair slice. Contributions
at both budgets are already grouped at that same endpoint; there is no pathwise subtraction
or independence assumption. Empty slices and a zero last budget are included. -/
theorem sum_rowSliceMean_differences {Ω V : Type*} [Fintype Ω]
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (T : ℕ → Ω → V → V → ℝ) (M d c : ℕ) (h : ℤ) (x y : V) :
    (∑ m ∈ range (lastBudget M d c h),
      rowSliceMean X Y (fun σ x y => T (m + 1) σ x y - T m σ x y) x y) =
      rowSliceMean X Y (T (lastBudget M d c h)) x y - rowSliceMean X Y (T 0) x y := by
  simp only [rowSliceMean, expect_sub_distrib]
  exact sum_lastBudget_differences
    (fun m => 𝔼 σ ∈ ({σ | X σ x ∧ Y σ y} : Finset Ω), T m σ x y) M d c h

/-- Positive precision forces every coarse bin to be available, with explicit constants.
This is the coarse-bin exclusion step of Lemma 7.6: omitted bins must instead be fine.
The full omitted-bin error estimate still needs their true-mass bound. -/
theorem coarse_scale_available {A a a' u : ℝ} (M c i : ℕ) (h : ℤ)
    (hc : 0 < c) (hA : 1 ≤ A) (hi : 1 ≤ i) (hh : 0 ≤ h)
    (ha : 0 < a) (ha1 : a ≤ 1) (ha' : 0 < a') (ha'1 : a' ≤ 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hscale : Real.logb 2 (a' / a) = (h : ℝ))
    (hactive : 0 < precision (16 * c) A M i a u) : scaleCutoff c h < M := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hla := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) ha.le ha1
  have hla' := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) ha'.le ha'1
  have hlu := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu.le hu1
  rw [Real.logb_div ha'.ne' ha.ne'] at hscale
  have habs : (h.natAbs : ℝ) = (h : ℝ) := by
    have heq : |(h : ℝ)| = (h.natAbs : ℝ) := by simp
    rw [abs_of_nonneg (show (0 : ℝ) ≤ h by exact_mod_cast hh)] at heq
    exact heq.symm
  have hhR : (0 : ℝ) ≤ h := by exact_mod_cast hh
  have hAi : 1 ≤ A * (i : ℝ) := one_le_mul_of_one_le_of_one_le hA hiR
  have hp : (16 * c : ℝ) * (-(Real.logb 2 a) / 2 + 1) < M := by
    have hdiv : -Real.logb 2 a / 2 + 1 < (M : ℝ) / (16 * c) := by
      dsimp only [precision] at hactive
      linarith
    simpa only [mul_comm] using
      (lt_div_iff₀ (show (0 : ℝ) < 16 * c by positivity)).mp hdiv
  have hcut : (c : ℝ) * (1 + (h : ℝ)) < M := by
    have hcNonneg : (0 : ℝ) ≤ c * (-(Real.logb 2 a)) := mul_nonneg hcR.le (by linarith)
    have hscaleCost := mul_le_mul_of_nonneg_left (show (h : ℝ) ≤ -Real.logb 2 a by linarith) hcR.le
    nlinarith
  have hcast : ((scaleCutoff c h : ℕ) : ℝ) < M := by
    simpa only [scaleCutoff, Nat.cast_mul, Nat.cast_add, Nat.cast_one, habs] using hcut
  exact_mod_cast hcast

/-- Nonnegative geometric majorant for both directions of the logarithmic scale grid. -/
@[expose] noncomputable def scaleMajorant (h : ℤ) : ℝ :=
  (2 : ℝ) ^ (-(h.natAbs : ℝ) / 8)

theorem scaleMajorant_nonneg (h : ℤ) : 0 ≤ scaleMajorant h := by
  unfold scaleMajorant
  positivity

/-- The actual last child budget leaves at least one eighth of scale decay in fourth-moment
norm. `K = 16*c` is explicit; the source may be retained or broadened. -/
theorem scheduled_child_cost_le {A a a' u u' : ℝ} (hA : 0 ≤ A)
    (M d c i i' : ℕ) (hc : 0 < c) (h : ℤ) (hi : i' + 1 ≤ i)
    (ha : 0 < a) (ha' : 0 < a') (hu : 0 < u) (huu' : u ≤ u')
    (hscale : Real.logb 2 (a' / a) = (h : ℝ)) :
    binNormCost 4 (h : ℝ) * (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4) *
        (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c h) i' a' u') ≤
      (2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * scaleMajorant h := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hloss : (M : ℝ) - lastBudget M d c h ≤ d + c * (1 + (h.natAbs : ℝ)) := by
    have hnat := budget_loss_le M d c h
    have hle : lastBudget M d c h ≤ M := Nat.sub_le _ _
    exact_mod_cast hnat
  have habs : |(h : ℝ)| = (h.natAbs : ℝ) := by simp
  have hbase := child_cost_mul_accuracy_le (s := 4) (K := 16 * c)
    (by norm_num) hA M (lastBudget M d c h) i i' hi ha ha' hu huu'
  rw [hscale, scaleMargin_four, habs] at hbase
  refine hbase.trans ?_
  rw [scaleMajorant, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2),
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  have hdiv := (div_le_div_iff_of_pos_right (show (0 : ℝ) < 16 * c by positivity)).2 hloss
  have heq : ((d : ℝ) + c * (1 + (h.natAbs : ℝ))) / (16 * c) =
      (d : ℝ) / (16 * c) + (1 + (h.natAbs : ℝ)) / 16 := by field_simp
  rw [heq] at hdiv
  have hn : (0 : ℝ) ≤ h.natAbs := Nat.cast_nonneg _
  linarith

/-- The scale budget is summable on the full two-sided integer grid, independently of the
finite set of bins present in a hierarchy. -/
theorem summable_scaleMajorant : Summable scaleMajorant := by
  have hq0 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(1 : ℝ) / 8) := by positivity
  have hq1 : (2 : ℝ) ^ (-(1 : ℝ) / 8) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have hgeom := summable_geometric_of_lt_one hq0 hq1
  rw [summable_int_iff_summable_nat_and_neg]
  have heq (n : ℕ) : scaleMajorant (n : ℤ) = ((2 : ℝ) ^ (-(1 : ℝ) / 8)) ^ n := by
    simp only [scaleMajorant, Int.natAbs_natCast]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  constructor
  · simpa only [heq] using hgeom
  · simpa only [scaleMajorant, Int.natAbs_neg, Int.natAbs_natCast, ← heq] using hgeom

/-- The two-sided scale sum has an explicit finite value. The zero scale is counted once. -/
theorem tsum_scaleMajorant : (∑' h, scaleMajorant h) =
    2 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 8)) - 1 := by
  let q : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 8)
  have hq0 : 0 ≤ q := by positivity
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)
  have heq (n : ℕ) : scaleMajorant (n : ℤ) = q ^ n := by
    simp only [scaleMajorant, Int.natAbs_natCast, q]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  have hnat := (summable_int_iff_summable_nat_and_neg.mp summable_scaleMajorant).1
  have hsum : (∑' n : ℕ, scaleMajorant (n : ℤ)) = 1 / (1 - q) := by
    simp_rw [heq]
    simpa only [one_div] using tsum_geometric_of_lt_one hq0 hq1
  have hboth := tsum_nat_add_neg summable_scaleMajorant
  have hneg (n : ℕ) : scaleMajorant (-(n : ℤ)) = scaleMajorant (n : ℤ) := by
    simp only [scaleMajorant, Int.natAbs_neg]
  simp_rw [hneg] at hboth
  rw [hnat.tsum_add hnat, hsum] at hboth
  have hzero : scaleMajorant 0 = 1 := by norm_num [scaleMajorant]
  rw [hzero] at hboth
  dsimp only [q] at hboth
  calc
    _ = 1 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 8)) +
        1 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 8)) - 1 := by linarith
    _ = _ := by ring

/-- Finite actual scale sets have a uniform total child-error budget. This is the scalar
payment used after the task-specific norm comparisons and Minkowski, without a factor
counting available scales. The rates and dependency ranks may vary with the scale. -/
theorem sum_scheduled_child_cost_le {A a u : ℝ} (hA : 0 ≤ A)
    (M d c i : ℕ) (hc : 0 < c) (s : Finset ℤ) (a' u' : ℤ → ℝ) (i' : ℤ → ℕ)
    (ha : 0 < a) (hu : 0 < u)
    (hi : ∀ h ∈ s, i' h + 1 ≤ i) (ha' : ∀ h ∈ s, 0 < a' h)
    (huu' : ∀ h ∈ s, u ≤ u' h)
    (hscale : ∀ h ∈ s, Real.logb 2 (a' h / a) = (h : ℝ)) :
    (∑ h ∈ s, binNormCost 4 (h : ℝ) * (2 : ℝ) ^ (Real.logb 2 (u' h / u) / 4) *
      (2 : ℝ) ^ (-precision (16 * c) A (lastBudget M d c h) (i' h) (a' h) (u' h))) ≤
      (2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * ∑' h, scaleMajorant h := by
  calc
    _ ≤ ∑ h ∈ s, (2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * scaleMajorant h :=
      sum_le_sum fun h hh => scheduled_child_cost_le hA M d c i (i' h) hc h
        (hi h hh) ha (ha' h hh) hu (huu' h hh) (hscale h hh)
    _ = (2 : ℝ) ^ (-precision (16 * c) A M i a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * ∑ h ∈ s, scaleMajorant h := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (summable_scaleMajorant.sum_le_tsum s (fun h _ => scaleMajorant_nonneg h)) (by positivity)

end Cslib.LogSpaceEstimation
