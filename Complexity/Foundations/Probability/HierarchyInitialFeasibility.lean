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

* `initial_active_pair_losses`: literal active cutoff and both endpoint losses.
* `requestPrecision_initial_active_pay`: sharp active-pair ordinary payment below spectral salary.
* `requestPrecision_grid`: exact actual-request precision on the grid.
* `requestPrecision_initial_clipped_transfer`: sharp piecewise scale/source/rank transport.
* `requestPrecision_initial_clipped_scheduled`: actual child-budget loss window.
* `requestPrecision_initial_clipped_adjust`: divide actual scale loss by the precision salary.
* `requestPrecision_initial_raw_pay`: ordinary direct-child scale/budget/rank cancellation.
* `requestPrecision_initial_scheduled_raw_pay`: explicit payment at actual scheduled budgets.
* `requestPrecision_le_omitted_depth_iff`: exact maximum-budget interface.
* `bounded_family_depth_guards`: joint cutoff-fit and parent-precision payment.
* `bounded_family_omission_row`: bounded width paid at parent precision.
* `initial_dyadicSlack_half`: literal first slack is at least half the budget.
* `bounded_family_initial_row_decay`: exceptional width paid with the rank salary retained.
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

/-- Sharp clipped-mean scale transport at the literal own request. The rate-16 grid
has norm scale exponent `a-i` in the coarse case and `-3(i-a)` in the fine case.
Combining either with the actual terminal precision penalty leaves `-|i-a|`.
The inherited source cancels exactly; structural charge is fixed in `B` first. -/
theorem requestPrecision_initial_clipped_transfer (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (M m ks ka bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) :
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    (2 : ℝ) ^ (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka)) *
        (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (((M : ℝ) - m) / (16 * B.slack) - |(bin : ℝ) - ka|) := by
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
  have hr := mul_le_mul_of_nonneg_left hrank' hcharge
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  change (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka)) -
    B.requestPrecision m Q.direct ≤ _
  rw [hq, hp, sub_div]
  split_ifs with h
  · have hh : (bin : ℝ) ≤ ka := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr hh)]
    nlinarith
  · have hh : (ka : ℝ) ≤ bin := by exact_mod_cast (Nat.le_of_lt (Nat.lt_of_not_ge h))
    rw [abs_of_nonneg (sub_nonneg.mpr hh)]
    nlinarith

/-- Exact budget-loss window for sharp clipped transport. This retains the actual
`max d scaleCutoff`; its cost is not silently absorbed by a free parent accuracy premise.
Apply separately at `d` and `2*d`, with equal endpoints cancelled by the paired consumer. -/
theorem requestPrecision_initial_clipped_scheduled (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (M d ks ka bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) :
    let cost := max d (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)))
    let m := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    (2 : ℝ) ^ (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka)) *
        (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ ((cost : ℝ) / (16 * B.slack) - |(bin : ℝ) - ka|) := by
  dsimp only
  apply (B.requestPrecision_initial_clipped_transfer hcharge hrate M _ ks ka bin
    r hs ht htask).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  apply sub_le_sub_right
  apply div_le_div_of_nonneg_right _ (by positivity)
  have hh : M ≤ LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) +
      max d (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin))) := by
    unfold LogSpaceEstimation.lastBudget
    omega
  have hr : (M : ℝ) ≤ (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) : ℝ) +
      (max d (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin))) : ℝ) :=
    by exact_mod_cast hh
  simp only [Nat.cast_max]
  linarith

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

/-- An unequal literal pair forces the cutoff below its coarse slack. Both endpoint
losses are at most `2*d`, including a zero coarse endpoint. No admissibility is assumed. -/
theorem initial_active_pair_losses (B : BudgetData HP P) (M d ka bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (ht : r.terminal.rate = rate ka)
    (hne : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) ≠
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))) :
    (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)) : ℝ) =
        B.slack * (1 + 4 * |(bin : ℝ) - ka|) ∧
      B.slack * (1 + 4 * |(bin : ℝ) - ka|) < 2 * d ∧
      ∀ e ∈ ({d, 2 * d} : Finset ℕ),
        M - LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin)) ≤ 2 * d := by
  have hcut : LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)) < 2 * d := by
    unfold LogSpaceEstimation.lastBudget at hne
    omega
  have heq : (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some bin)) : ℝ) =
      B.slack * (1 + 4 * |(bin : ℝ) - ka|) := by
    have habs : (((ka : ℤ) - bin).natAbs : ℝ) = |(bin : ℝ) - ka| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
      push_cast
      exact abs_sub_comm _ _
    rw [B.sampleScale_grid r ka bin hrate ht, LogSpaceEstimation.scaleCutoff,
      Int.natAbs_mul]
    norm_num only [Int.natAbs_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, habs]
  refine ⟨heq, ?_, ?_⟩
  · rw [← heq]
    exact_mod_cast hcut
  · intro e he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    unfold LogSpaceEstimation.lastBudget
    rcases he with rfl | rfl <;> omega

/-- Sharp ordinary scale plus own-precision payment at either endpoint of an active pair.
The inherited source cancels and the actual direct rank drops. The exponent is at most
`25*d/(8*slack)`, strictly below the norm-level spectral salary `6*d`. This does not
pay bin sums, range constants or the remaining structural allocation. -/
theorem requestPrecision_initial_active_pay (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (M d ks ka bin e : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩))
    (hne : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) ≠
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)))
    (he : e ∈ ({d, 2 * d} : Finset ℕ)) :
    let m := LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    (2 : ℝ) ^ (4 * |(bin : ℝ) - ka|) * (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ (25 * (d : ℝ) / (8 * B.slack)) ∧
      25 * (d : ℝ) / (8 * B.slack) < 6 * d := by
  dsimp only
  let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  let m := LogSpaceEstimation.lastBudget M e B.slack (B.sampleScale r (some bin))
  obtain ⟨_, hcut, hloss⟩ := B.initial_active_pair_losses M d ka bin r hrate ht hne
  have hslack : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
  have hden : (0 : ℝ) < 16 * B.slack := by positivity
  have hd : 0 < (d : ℝ) := by nlinarith [abs_nonneg ((bin : ℝ) - ka)]
  have hl : (M : ℝ) - m ≤ 2 * d := by
    have hn := hloss e he
    have hm : m ≤ M := Nat.sub_le _ _
    exact_mod_cast hn
  have hbudget := (div_le_div_of_nonneg_right hl hden.le)
  have hdist : 6 * |(bin : ℝ) - ka| + 2 * d / (16 * B.slack) ≤
      25 * d / (8 * B.slack) := by
    apply (le_div_iff₀ (show (0 : ℝ) < 8 * B.slack by positivity)).mpr
    have hid : (2 * (d : ℝ) / (16 * B.slack)) * (8 * B.slack) = d := by
      field_simp
      ring
    nlinarith
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
  have hr := mul_le_mul_of_nonneg_left hrank' hcharge
  constructor
  · simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    change 4 * |(bin : ℝ) - ka| - B.requestPrecision m Q.direct ≤ _
    rw [hq, hp]
    rw [sub_div] at hbudget
    nlinarith [le_abs_self ((bin : ℝ) - ka)]
  · apply (div_lt_iff₀ (show (0 : ℝ) < 8 * B.slack by positivity)).mpr
    nlinarith

/-- Divide the literal scale-cutoff loss by the evaluator's `16*slack` precision salary.
On the rate-16 grid the remaining norm decay is `2^(-3|i-a|/4)`, with the explicit
prefix-slack cost `2^(d/(16*slack)+1/16)`. This is not an ordinary-noise payment. -/
theorem requestPrecision_initial_clipped_adjust (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (hrate : B.binRate = rate)
    (M d ks ka bin : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (htask : r.task = .row 0 (.pilotInput ⟨0, HP.k_pos⟩)) :
    let m := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let Q := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    (2 : ℝ) ^ (if bin ≤ ka then (ka : ℝ) - bin else -3 * ((bin : ℝ) - ka)) *
        (2 : ℝ) ^ (-B.requestPrecision m Q.direct) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) * (2 : ℝ) ^ (-B.rankCharge) *
        (2 : ℝ) ^ ((d : ℝ) / (16 * B.slack) + 1 / 16 - 3 * |(bin : ℝ) - ka| / 4) := by
  dsimp only
  apply (B.requestPrecision_initial_clipped_scheduled hcharge hrate M d ks ka bin
    r hs ht htask).trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hslack : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have habs : (((ka : ℤ) - bin).natAbs : ℝ) = |(bin : ℝ) - ka| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    exact abs_sub_comm _ _
  have hcost : (max d (LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale r (some bin))) : ℝ) ≤
      d + B.slack * (1 + 4 * |(bin : ℝ) - ka|) := by
    rw [sampleScale_grid B r ka bin hrate ht, LogSpaceEstimation.scaleCutoff,
      Int.natAbs_mul]
    norm_num only [Int.natAbs_natCast, Nat.cast_max, Nat.cast_mul, Nat.cast_add,
      Nat.cast_one, Nat.cast_ofNat, habs]
    apply max_le <;> nlinarith [abs_nonneg ((bin : ℝ) - ka)]
  have hh := div_le_div_of_nonneg_right hcost (show (0 : ℝ) ≤ 16 * B.slack by positivity)
  have he : ((d : ℝ) + B.slack * (1 + 4 * |(bin : ℝ) - ka|)) / (16 * B.slack) =
      (d : ℝ) / (16 * B.slack) + 1 / 16 + |(bin : ℝ) - ka| / 4 := by
    field_simp [hslack.ne']
    ring
  rw [he] at hh
  simp only [Nat.cast_max]
  linarith

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

/-- Exact maximum-budget interface for the omitted-depth exponent. In particular,
fixed retained depth cannot support this comparison at arbitrarily large budgets.
The source and rank terms are explicit, not constants chosen after a request. -/
theorem requestPrecision_le_omitted_depth_iff (B : BudgetData HP P) (M n ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka) :
    B.requestPrecision M r ≤ 4 * ((n : ℝ) - ka) ↔
      (M : ℝ) ≤ 16 * B.slack *
        (4 * (n : ℝ) - 2 * ka + 2 * ks + B.rankCharge * r.task.rank) := by
  rw [B.requestPrecision_grid M ks ka r hs ht]
  have hs : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hc : (0 : ℝ) < 16 * B.slack := by positivity
  rw [sub_le_iff_le_add, sub_le_iff_le_add, div_le_iff₀ hc]
  constructor <;> intro h <;> nlinarith

/-- A fixed evaluator can serve a bounded budget family. The maximum budget is chosen
jointly with retained depth, rather than sending the budget to infinity at fixed bins.
The terminal exponent is restricted to half the retained depth to leave a width margin.
No positivity of parent precision, or accuracy of recursive children, is assumed. -/
theorem bounded_family_depth_guards (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (n M ks ka : ℕ)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M)
    (hhi : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) :
    (∀ bin ≤ n, LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale r (some bin)) < M) ∧
    B.requestPrecision M r ≤ 2 * (n : ℝ) - 2 * ((ka : ℝ) + ks) ∧
    rate n / rate ka ≤ (2 : ℝ) ^ (-B.requestPrecision M r) := by
  have hc : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hm : (M : ℝ) ≤ 32 * (B.slack : ℝ) * n := by exact_mod_cast hhi
  have hp : B.requestPrecision M r ≤ 2 * (n : ℝ) - 2 * ((ka : ℝ) + ks) := by
    rw [B.requestPrecision_grid M ks ka r hs ht]
    have hd : (M : ℝ) / (16 * B.slack) ≤ 2 * (n : ℝ) :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    nlinarith [mul_nonneg hcharge (Nat.cast_nonneg (α := ℝ) r.task.rank)]
  refine ⟨B.retained_scaleCutoff_lt r M n ka hrate ht hlo, hp, ?_⟩
  have ha' : 2 * (ka : ℝ) ≤ n := by exact_mod_cast ha
  have hr (k : ℕ) : rate k = (2 : ℝ) ^ (-4 * (k : ℝ)) := by
    rw [Real.rpow_mul_natCast (by norm_num)]
    norm_num [rate_eq_source_grid]
  rw [hr n, hr ka, ← Real.rpow_sub (by norm_num)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  nlinarith [Nat.cast_nonneg (α := ℝ) ks]

/-- The same bounded family pays the row-width factor of the omitted fourth moment.
This uses a bounded prime horizon; it is stronger than a matrix-entry estimate. -/
theorem bounded_family_omission_row (B : BudgetData HP P)
    (hcharge : 0 ≤ B.rankCharge) (n M ks ka : ℕ)
    (hM : M ≤ 32 * B.slack * n) (ha : 2 * ka ≤ n)
    (hP : P ≤ 2 ^ (n + 1))
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka) :
    16 * (P : ℝ) * (rate n / rate ka) ^ 4 ≤
      32 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))) ^ 4 := by
  have _ := hcharge
  have hc : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have hm : (M : ℝ) ≤ 32 * (B.slack : ℝ) * n := by exact_mod_cast hM
  have hp : B.requestPrecision M r + B.rankCharge * r.task.rank ≤
      2 * (n : ℝ) - 2 * ((ka : ℝ) + ks) := by
    rw [B.requestPrecision_grid M ks ka r hs ht]
    have hd : (M : ℝ) / (16 * B.slack) ≤ 2 * (n : ℝ) :=
      (div_le_iff₀ (by positivity)).mpr (by nlinarith)
    nlinarith [mul_nonneg hcharge (Nat.cast_nonneg (α := ℝ) r.task.rank)]
  have ha' : 2 * (ka : ℝ) ≤ n := by exact_mod_cast ha
  have hP' : (P : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + 1) := by
    have he : (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) := by push_cast; rfl
    rw [he, Real.rpow_natCast]
    exact_mod_cast hP
  have hr (k : ℕ) : rate k = (2 : ℝ) ^ (-4 * (k : ℝ)) := by
    rw [Real.rpow_mul_natCast (by norm_num)]
    norm_num [rate_eq_source_grid]
  apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP' (by norm_num))
    (pow_nonneg (div_nonneg (rate_pos n).le (rate_pos ka).le) 4)).trans
  rw [hr n, hr ka, ← Real.rpow_sub (by norm_num),
    ← Real.rpow_mul_natCast (by norm_num), mul_assoc,
    ← Real.rpow_add (by norm_num)]
  rw [← Real.rpow_add (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
  have he : (n : ℝ) + 1 + (-4 * (n : ℝ) - -4 * (ka : ℝ)) * 4 ≤
      1 + (-B.requestPrecision M r + -(B.rankCharge * r.task.rank)) * 4 := by
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) ks]
  calc
    _ ≤ 16 * (2 : ℝ) ^ (1 + (-B.requestPrecision M r + -(B.rankCharge * r.task.rank)) * 4) :=
      mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by norm_num)
    _ = _ := by rw [Real.rpow_add (by norm_num)]; norm_num; ring

/-- The literal first slack is at least half the parent budget. -/
theorem initial_dyadicSlack_half (M : ℕ) :
    M ≤ 2 * Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) 0 := by
  have h := Nat.lt_pow_succ_log_self (b := 2) (by decide) M
  rw [← Nat.log2_eq_log_two] at h
  simpa only [Cslib.RowCompression.dyadicSlack, Nat.add_sub_cancel,
    Nat.pow_succ, Nat.mul_comm] using h.le

/-- Even the slow decay 2⁻ᵈ at the exceptional first group pays its entire rounded
row width. The structural rank salary is retained as a factor, chosen before request
exponents. Only cutoff fit and the bounded width are used; no accuracy is assumed. -/
theorem bounded_family_initial_row_decay (B : BudgetData HP P)
    (n M ks ka : ℕ)
    (hlo : B.slack * (1 + 4 * (n + ka)) < M) (hP : P ≤ 2 ^ (n + 1))
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka) :
    16 * (P : ℝ) * (2 : ℝ) ^
        (-(Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) 0 : ℝ)) ≤
      32 * ((2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (-(B.rankCharge * r.task.rank))) ^ 4 := by
  let d := Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) 0
  have hc : (1 : ℝ) ≤ B.slack := by exact_mod_cast B.slack_pos
  have hm : (B.slack : ℝ) * (1 + 4 * ((n : ℝ) + ka)) < M := by exact_mod_cast hlo
  have hd : (M : ℝ) ≤ 2 * d := by exact_mod_cast initial_dyadicSlack_half M
  have hn : (n : ℝ) ≤ (M : ℝ) / (4 * B.slack) := by
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith [Nat.cast_nonneg (α := ℝ) ka]
  have hb : (M : ℝ) / (4 * B.slack) ≤ (M : ℝ) / 4 :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg M) (by norm_num) (by linarith)
  have hp := B.requestPrecision_grid M ks ka r hs ht
  have he : (n : ℝ) - d ≤
      (-B.requestPrecision M r - B.rankCharge * r.task.rank) * 4 := by
    have hh : (M : ℝ) / (16 * B.slack) * 4 = (M : ℝ) / (4 * B.slack) := by ring
    nlinarith [Nat.cast_nonneg (α := ℝ) ks, Nat.cast_nonneg (α := ℝ) ka]
  have hP' : (P : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) + 1) := by
    rw [show (n : ℝ) + 1 = ((n + 1 : ℕ) : ℝ) by push_cast; rfl,
      Real.rpow_natCast]
    exact_mod_cast hP
  calc
    _ ≤ 16 * (2 : ℝ) ^ ((n : ℝ) + 1) * (2 : ℝ) ^ (-(d : ℝ)) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hP' (by norm_num))
        (by positivity)
    _ = 32 * (2 : ℝ) ^ ((n : ℝ) - d) := by
      rw [mul_assoc, ← Real.rpow_add (by norm_num)]
      rw [show (n : ℝ) + 1 + -(d : ℝ) = 1 + ((n : ℝ) - d) by ring,
        Real.rpow_add (by norm_num)]
      norm_num
      ring
    _ ≤ 32 * (2 : ℝ) ^ ((-B.requestPrecision M r -
        B.rankCharge * r.task.rank) * 4) := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by norm_num) he) (by norm_num)
    _ = _ := by
      rw [← Real.rpow_add (by norm_num), ← Real.rpow_mul_natCast (by norm_num)]
      congr 2

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
