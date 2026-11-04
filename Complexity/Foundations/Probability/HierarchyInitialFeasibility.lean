/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyBudgetEvaluator
import Mathlib.NumberTheory.Bertrand

/-!
# Explicit depth, budget and field feasibility

The grid has rate 16⁻ᵏ, hence scale offset 4(ka-bin) and precision
M/(16*slack)-2(ka+ks)-rankCharge*rank. A slow linear retained depth is compatible with
these guards. Bertrand's postulate supplies a prime of bounded size for a depth horizon
and identifiers below 2ⁿ. These guards alone do not pay the full output error: in particular
rank and source exponents must be tracked separately when using the omitted-depth rate.

## Main results

* `requestPrecision_grid`: exact actual-request precision on the grid.
* `requestPrecision_initial_raw_pay`: ordinary direct-child scale/budget/rank cancellation.
* `requestPrecision_initial_scheduled_raw_pay`: explicit payment at actual scheduled budgets.
* `sampleScale_grid`: exact integer scale offset.
* `retained_scaleCutoff_lt`: every retained cutoff is below a sufficient budget.
* `slow_depth_guards`: depth M/(128*slack) pays cutoffs and positive precision.
* `fixed_request_depth_guards`: fix all three exponents before increasing depth.
* `exists_bounded_depth_prime`: bounded prime admitting the depth and identifier horizon.
* `bounded_width_omission`: two width factors paid by the omitted fourth moment.
* `bounded_width_precision`: one width factor paid by the precision fourth moment.
* `bounded_width_precision_sq`: both preparation width factors paid by precision.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Cslib
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

private theorem logb_rate (k : ℕ) : Real.logb 2 (rate k) = -4 * k := by
  rw [rate, Real.logb_pow, Real.logb_inv, Real.logb_pow]
  norm_num

/-- Usage changes leave precision unchanged: the formula uses source and terminal rates,
which must still be paid separately in moment estimates. -/
theorem requestPrecision_grid (B : BudgetData HP P) (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka) :
    B.requestPrecision M r = (M : ℝ) / (16 * B.slack) -
      2 * ((ka : ℝ) + ks) - B.rankCharge * r.task.rank := by
  rw [requestPrecision, LogSpaceEstimation.precision, hs, ht, logb_rate, logb_rate]
  ring

/-- Ordinary-progress payment for the actual direct pilot request. The source is literally
inherited and rank decrease comes from `rawRequests_rank_lt`; no precision relation is
assumed. The budget-loss and scale-window premises still need a scheduled allocation.
This norm-level estimate must be raised to the fourth power for moment consumers. -/
theorem requestPrecision_initial_raw_pay (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (M m ks ka bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (w : ℝ) (hw : 1 ≤ w) (hgap : (M : ℝ) - m ≤ w + 1)
    (hdist : |(bin : ℝ) - ka| < w) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|) * (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (8 * w) * (2 : ℝ) ^ (-|(bin : ℝ) - ka| / 2) := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  have hq := B.requestPrecision_grid m ks bin Q.direct hs (by
    dsimp only [Q, HierarchyTask.rawRequests]
    exact congrFun hrate bin)
  have hp := B.requestPrecision_grid M ks ka r hs ht
  have hrank : Q.direct.task.rank < r.task.rank := by
    rw [htask]
    exact HierarchyTask.rawRequests_rank_lt 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin) Q.direct
      (by simp only [Q, HierarchyTask.RawRequests.calls, List.mem_append, List.mem_cons,
        true_or, true_or, true_or])
  have hrank' : (Q.direct.task.rank : ℝ) + 1 ≤ r.task.rank := by exact_mod_cast hrank
  have hslack : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
  have hden : (0 : ℝ) < 16 * B.slack := by positivity
  have hbudget : ((M : ℝ) - m) / (16 * B.slack) ≤ (w + 1) / 16 :=
    (div_le_div_of_nonneg_right hgap hden.le).trans
      (div_le_div_of_nonneg_left (by linarith) (by norm_num) (by linarith))
  have hr := mul_le_mul_of_nonneg_left hrank' hcharge
  have habs := le_abs_self ((bin : ℝ) - ka)
  have he : 4 * |(bin : ℝ) - ka| - B.requestPrecision m Q.direct ≤
      -B.requestPrecision M r - B.rankCharge + 8 * w - |(bin : ℝ) - ka| / 2 := by
    rw [hq, hp]
    rw [sub_div] at hbudget
    nlinarith
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  linarith

/-- The preceding ordinary-progress rule at the literal scheduled endpoint. The displayed
window is an explicit finite cost, not a claim that the parent's walks absorb it. It applies
to both endpoint slacks (including exhausted budgets); equal endpoints are cancelled by
`pairedSample`, rather than charged twice. Structural charge is fixed before all exponents. -/
theorem requestPrecision_initial_scheduled_raw_pay (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (M d ks ka bin : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) :
    let cost := max d (Cslib.LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)))
    let m := Cslib.LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let w := (cost : ℝ) + |(bin : ℝ) - ka| + 1
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    m < M ∧
    (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|) * (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (8 * w) * (2 : ℝ) ^ (-|(bin : ℝ) - ka| / 2) := by
  dsimp only
  constructor
  · exact LogSpaceEstimation.lastBudget_lt hM B.slack_pos
  · apply B.requestPrecision_initial_raw_pay hcharge hrate M _ ks ka bin r hs ht htask
    · linarith [Nat.cast_nonneg (α := ℝ)
        (max d (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)))),
        abs_nonneg ((bin : ℝ) - ka)]
    · have hnat : M ≤ LogSpaceEstimation.lastBudget M d B.slack
          (B.sampleScale r (some bin)) +
          max d (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin))) := by
        unfold LogSpaceEstimation.lastBudget
        omega
      have hreal : (M : ℝ) ≤ (LogSpaceEstimation.lastBudget M d B.slack
          (B.sampleScale r (some bin)) : ℝ) +
          (max d (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin))) : ℝ) :=
        by exact_mod_cast hnat
      simp only [Nat.cast_max] at hreal ⊢
      linarith [abs_nonneg ((bin : ℝ) - ka)]
    · linarith [Nat.cast_nonneg (α := ℝ)
        (max d (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin))))]

/-- The actual logarithmic scale is integral on the fourth-power dyadic grid. -/
theorem sampleScale_grid (B : BudgetData HP P)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ka bin : ℕ)
    (hrate : B.binRate = rate) (ht : r.terminal.rate = rate ka) :
    B.sampleScale r (some bin) = 4 * ((ka : ℤ) - bin) := by
  have he : Real.logb 2 (rate bin / rate ka) = ((4 * ((ka : ℤ) - bin) : ℤ) : ℝ) := by
    rw [Real.logb_div (rate_pos bin).ne' (rate_pos ka).ne', logb_rate, logb_rate]
    push_cast
    ring
  simp only [sampleScale, Option.map_some, Option.getD_some, hrate, ht, he, Int.floor_intCast]

/-- A concrete sufficient cutoff bound, retaining both the bin and terminal exponents. -/
theorem retained_scaleCutoff_lt (B : BudgetData HP P)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (M n ka : ℕ)
    (hrate : B.binRate = rate) (ht : r.terminal.rate = rate ka)
    (hbudget : B.slack * (1 + 4 * (n + ka)) < M) :
    ∀ bin ≤ n, LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)) < M := by
  intro bin hbin
  rw [sampleScale_grid B r ka bin hrate ht, LogSpaceEstimation.scaleCutoff,
    Int.natAbs_mul]
  norm_num only [Int.natAbs_natCast]
  have hd : ((ka : ℤ) - bin).natAbs ≤ n + ka := by
    have hh := Int.natAbs_sub_le (ka : ℤ) (bin : ℤ)
    simpa only [Int.natAbs_natCast] using hh.trans (by omega : ka + bin ≤ n + ka)
  exact (Nat.mul_le_mul_left B.slack (by omega : 1 + 4 * ((ka : ℤ) - bin).natAbs ≤
    1 + 4 * (n + ka))).trans_lt hbudget

/-- The literal slow linear depth pays all retained cutoffs and leaves a quantitative
precision margin. Structural rank cost is exposed, rather than silently absorbed.
This proves guard feasibility only, not arbitrary accuracy of the compressed output. -/
theorem slow_depth_guards (B : BudgetData HP P) (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ks ka : ℕ)
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka)
    (hdepth : 1 ≤ M / (128 * B.slack))
    (hks : ks ≤ M / (128 * B.slack)) (hka : ka ≤ M / (128 * B.slack))
    (hrank : B.rankCharge * r.task.rank ≤ (M / (128 * B.slack) : ℕ)) :
    (∀ bin ≤ M / (128 * B.slack),
      LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)) < M) ∧
    (M : ℝ) / (64 * B.slack) ≤ B.requestPrecision M r := by
  let n := M / (128 * B.slack)
  have hn : 128 * B.slack * n ≤ M := Nat.mul_div_le M (128 * B.slack)
  have hc := B.slack_pos
  constructor
  · apply B.retained_scaleCutoff_lt r M n ka hrate ht
    have hh : B.slack * (1 + 4 * (n + ka)) < 128 * B.slack * n := by
      dsimp only [n] at *
      nlinarith
    exact hh.trans_le hn
  · rw [B.requestPrecision_grid M ks ka r hs ht]
    have hn' : 128 * (B.slack : ℝ) * n ≤ M := by exact_mod_cast hn
    have hks' : (ks : ℝ) ≤ n := by exact_mod_cast hks
    have hka' : (ka : ℝ) ≤ n := by exact_mod_cast hka
    have hc' : (0 : ℝ) < B.slack := by exact_mod_cast hc
    have hn0 : (0 : ℝ) ≤ n := Nat.cast_nonneg _
    have hbudget : (5 : ℝ) * n ≤ (M : ℝ) / (16 * B.slack) -
        (M : ℝ) / (64 * B.slack) := by
      field_simp
      nlinarith
    linarith

/-- Fix source, terminal and usage exponents, identifiers and structural rank BEFORE taking
larger retained depths. The explicit budgets have literal depth floor M/(128*slack)=n.
This is eventual guard feasibility, not convergence of the complete output payment. -/
theorem fixed_request_depth_guards (B : BudgetData HP P)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ks ka ku idMax : ℕ)
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) :
    ∃ N : ℕ, ∀ n ≥ N,
      let M := 128 * B.slack * n
      M / (128 * B.slack) = n ∧ ks ≤ n ∧ ka ≤ n ∧ ku ≤ n ∧ idMax < 2 ^ n ∧
      (∀ bin ≤ n, LogSpaceEstimation.scaleCutoff B.slack
        (B.sampleScale r (some bin)) < M) ∧
      2 * (n : ℝ) ≤ B.requestPrecision M r := by
  obtain ⟨rankBound, hrank⟩ := exists_nat_gt (B.rankCharge * r.task.rank)
  refine ⟨max (max 1 (max ks (max ka (max ku rankBound)))) idMax, ?_⟩
  intro n hn
  have hid : idMax ≤ n := (le_max_right _ _).trans hn
  have hn := (le_max_left _ _).trans hn
  have hn1 : 1 ≤ n := (le_max_left _ _).trans hn
  have hks : ks ≤ n := (le_max_left _ _).trans ((le_max_right _ _).trans hn)
  have hka : ka ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hn))
  have hku : ku ≤ n := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hrn : rankBound ≤ n := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans ((le_max_right _ _).trans hn)))
  have hc : 0 < 128 * B.slack := Nat.mul_pos (by decide) B.slack_pos
  have hdiv : (128 * B.slack * n) / (128 * B.slack) = n :=
    Nat.mul_div_cancel_left n hc
  have hg := B.slow_depth_guards (128 * B.slack * n) r ks ka hrate hs ht
    (by rwa [hdiv]) (by rwa [hdiv]) (by rwa [hdiv])
    (by rw [hdiv]; exact hrank.le.trans (by exact_mod_cast hrn))
  refine ⟨hdiv, hks, hka, hku, hid.trans_lt Nat.lt_two_pow_self,
    by simpa only [hdiv] using hg.1, ?_⟩
  apply le_trans _ hg.2
  have hc' : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  push_cast
  field_simp
  nlinarith

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData

namespace Matrix.HierarchyParams.H4RankEnvironment

/-- A bounded prime, chosen after the retained depth. Identifiers must already fit below
2ⁿ; arbitrary stage/copy identifier growth is not supplied by this theorem. -/
theorem exists_bounded_depth_prime (n idMax : ℕ) (hid : idMax < 2 ^ n) :
    ∃ P, P.Prime ∧ 2 ^ n < P ∧ P ≤ 2 ^ (n + 1) ∧
      ∃ H : Horizon P, H.maxExponent = n ∧ H.maxIdentifier = idMax := by
  obtain ⟨P, hP, hlo, hhi⟩ := Nat.exists_prime_lt_and_le_two_mul (2 ^ n) (by positivity)
  refine ⟨P, hP, hlo, ?_, ⟨n, idMax, hlo.le, hid.trans hlo⟩, rfl, rfl⟩
  simpa only [pow_succ, Nat.mul_comm] using hhi

/-- The bounded-prime choice pays two unnormalized width factors against the fourth
power of the omitted rate. Source and terminal inverse rates remain separate costs. -/
theorem bounded_width_omission (P n : ℕ) (hP : P ≤ 2 ^ (n + 1)) :
    (P : ℝ) ^ 2 * rate n ^ 4 ≤ 4 * (1 / 16384 : ℝ) ^ n := by
  have hp : (P : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast hP
  calc
    _ ≤ ((2 : ℝ) ^ (n + 1)) ^ 2 * rate n ^ 4 :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg P) hp 2)
        (by positivity)
    _ = _ := by
      have htwo : ((2 : ℝ) ^ (n + 1)) ^ 2 = 4 * (4 : ℝ) ^ n := by
        rw [← pow_mul, Nat.add_mul, Nat.one_mul, pow_add, Nat.mul_comm n 2, pow_mul]
        norm_num
        ring
      have hrate : rate n ^ 4 = ((1 / 16 : ℝ) ^ 4) ^ n := by
        rw [rate_eq_source_grid, ← pow_mul, Nat.mul_comm n 4, pow_mul]
        norm_num
      rw [htwo, hrate, mul_assoc, ← mul_pow]
      norm_num

/-- A precision margin of twice the retained depth pays the preparation's width factor.
The slow-depth guard supplies this margin since M ≥ 128*slack*n. Inverse source/rank
rates and fixed sensitivity constants are not included in this scalar inequality. -/
theorem bounded_width_precision (P n : ℕ) {p : ℝ} (hP : P ≤ 2 ^ (n + 1))
    (hp : 2 * (n : ℝ) ≤ p) :
    (P : ℝ) * ((2 : ℝ) ^ (-p)) ^ 4 ≤ 2 * (1 / 128 : ℝ) ^ n := by
  have hacc : (2 : ℝ) ^ (-p) ≤ (1 / 4 : ℝ) ^ n := by
    calc
      _ ≤ (2 : ℝ) ^ ((-2) * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by
        rw [Real.rpow_mul_natCast (by norm_num)]
        norm_num
  have hP' : (P : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast hP
  calc
    _ ≤ (2 : ℝ) ^ (n + 1) * ((1 / 4 : ℝ) ^ n) ^ 4 :=
      mul_le_mul hP' (pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) _).le hacc 4)
        (by positivity) (by positivity)
    _ = _ := by
      rw [show (2 : ℝ) ^ (n + 1) = 2 * (2 : ℝ) ^ n by rw [pow_succ, mul_comm],
        ← pow_mul, Nat.mul_comm n 4, pow_mul, mul_assoc, ← mul_pow]
      norm_num

/-- The preparation precision payment has TWO width factors: its sensitivity supplies
one and the repeated row moment can supply the other. A margin p ≥ 2n pays both. -/
theorem bounded_width_precision_sq (P n : ℕ) {p : ℝ} (hP : P ≤ 2 ^ (n + 1))
    (hp : 2 * (n : ℝ) ≤ p) :
    (P : ℝ) ^ 2 * ((2 : ℝ) ^ (-p)) ^ 4 ≤ 4 * (1 / 64 : ℝ) ^ n := by
  have hacc : (2 : ℝ) ^ (-p) ≤ (1 / 4 : ℝ) ^ n := by
    calc
      _ ≤ (2 : ℝ) ^ ((-2) * (n : ℝ)) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ = _ := by
        rw [Real.rpow_mul_natCast (by norm_num)]
        norm_num
  have hP' : (P : ℝ) ≤ (2 : ℝ) ^ (n + 1) := by exact_mod_cast hP
  calc
    _ ≤ ((2 : ℝ) ^ (n + 1)) ^ 2 * ((1 / 4 : ℝ) ^ n) ^ 4 :=
      mul_le_mul (pow_le_pow_left₀ (Nat.cast_nonneg P) hP' 2)
        (pow_le_pow_left₀ (Real.rpow_pos_of_pos (by norm_num) _).le hacc 4)
        (by positivity) (by positivity)
    _ = _ := by
      rw [show ((2 : ℝ) ^ (n + 1)) ^ 2 = 4 * (4 : ℝ) ^ n by
        rw [← pow_mul, Nat.add_mul, Nat.one_mul, pow_add, Nat.mul_comm n 2, pow_mul]
        norm_num
        ring,
        ← pow_mul, Nat.mul_comm n 4, pow_mul, mul_assoc, ← mul_pow]
      norm_num

end Matrix.HierarchyParams.H4RankEnvironment
