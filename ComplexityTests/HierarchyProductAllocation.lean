/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: local-only (tests of actual product allocation domains)
import Complexity.Foundations.Probability.HierarchyProductAllocation
import all ComplexityTests.HierarchyProductMean
import all ComplexityTests.HierarchyProductTransport

/-! The existing clients retain genuine nonzero products, correlated errors, unequal
source/usage rates and supplied-history execution. This file adds a fixed-charge family
with arbitrary finite horizon and positive actual bin-zero child precision. Its nominal
scalar IH allowance exceeds the conservative mean consumer's sufficient reserve.
No recursively successful compressed family is constructed or claimed. -/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
namespace ProductAllocationRegression
variable (HP : FourthRootHierarchyParams 16 1 16 32 8)

private def data (P A n : ℕ) : BudgetData HP P where
  padding := 1
  base := 1
  bins := range (n + 1)
  binRate := rate
  cutoff := fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate 1 i (fun _ => 1)
  auxiliary := fun _ => polynomialPrepCutoff4 HP.θ
  slack := 1
  slack_pos := by decide
  rankCharge := A
  binCap := 16
  binCap_nonneg := by norm_num
  cutoff_bounds := by
    intro i d
    have hstep (j : ℕ) : rate j = 16 * rate (j + 1) := by
      simp only [rate, pow_succ, _root_.mul_inv_rev]
      ring
    simpa only [DenseBinRecipe.polynomialUnrouted,
      show max (1 : ℝ) 16 = 16 by norm_num] using
      (DenseBinRecipe.polynomialUnrouted_numerator_laws HP rate_pos hstep
        (by norm_num : (0 : ℝ) ≤ 1) i d).1

private def request (P : ℕ) : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  ⟨.residual 0, gridChannel 0 0 [1], gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩
private def budget (A n : ℕ) : ℕ := 64 * (n + A * (HierarchyTask.residual (k := HP.k) 0).rank + 1)

private lemma budget_zero {P : ℕ} (A n : ℕ) :
    (data HP P A n).binBudget (budget HP A n) 0 (request HP P) = budget HP A n - 1 ∧
    (data HP P A n).childBudget (budget HP A n) = budget HP A n - 1 := by
  simp [BudgetData.binBudget, BudgetData.childBudget, LogSpaceEstimation.lastBudget,
    LogSpaceEstimation.scaleCutoff, data, request, gridChannel, rate]

-- Both actual bin-zero and negative budgets decrease, and the actual constructor rank
-- guard holds. Source reset preserves the whole suffix, not just its rate.
example {P : ℕ} [Fact P.Prime] (A n : ℕ) :
    let B := data HP P A n
    let r := request HP P
    let M := budget HP A n
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source
      (BudgetData.midpoint r) r.terminal (B.binRate 0)
    B.binBudget M 0 r < M ∧ B.childBudget M < M ∧
      Q.direct.task.rank < r.task.rank ∧ Q.right.source = BudgetData.midpoint r ∧
      Q.right.source.suffix = [] ∧ r.source.suffix = [1] := by
  dsimp only
  have hM : 0 < budget HP A n := by unfold budget; omega
  refine ⟨(data HP P A n).binBudget_lt hM 0 _,
    (data HP P A n).childBudget_lt hM, ?_, rfl, rfl, rfl⟩
  exact HierarchyTask.rawRequests_rank_lt 0 0 .residual (request HP P).source
    (BudgetData.midpoint (request HP P)) (request HP P).terminal ((data HP P A n).binRate 0)
    _ (by simp [HierarchyTask.RawRequests.calls])

private lemma bin_zero_active {P : ℕ} (A n : ℕ) :
    let B := data HP P A n
    let r := request HP P
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source
      (BudgetData.midpoint r) r.terminal (B.binRate 0)).direct
    0 < B.requestPrecision (budget HP A n) r ∧
      0 < B.requestPrecision (B.binBudget (budget HP A n) 0 r) q := by
  dsimp only
  rw [(budget_zero HP A n).1]
  rw [(data HP P A n).requestPrecision_grid _ 0 0 _ rfl rfl,
    (data HP P A n).requestPrecision_grid _ 0 0 _ rfl rfl]
  have hM : 1 ≤ budget HP A n := by unfold budget; omega
  have hc : ((budget HP A n - 1 : ℕ) : ℝ) = budget HP A n - 1 := by
    rw [Nat.cast_sub hM]; norm_num
  have hr : ((HierarchyTask.baseNormalized (k := HP.k) 0 0).rank : ℝ) ≤
      (HierarchyTask.residual (k := HP.k) 0).rank := by
    simp only [HierarchyTask.rank, mul_zero, zero_add]
    exact_mod_cast (show 14 ≤ 4 * (20 * HP.k + 27) by omega)
  simp only [data, request, HierarchyTask.rawRequests, Nat.cast_zero, add_zero, mul_zero,
    sub_zero, Nat.cast_one]
  rw [hc]
  have hb : (budget HP A n : ℝ) =
      64 * ((n : ℝ) + A * (HierarchyTask.residual (k := HP.k) 0).rank + 1) := by
    simp only [budget, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one]
  rw [hb]
  constructor <;> nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) A,
    Nat.cast_nonneg (α := ℝ) (HierarchyTask.residual (k := HP.k) 0).rank,
    mul_le_mul_of_nonneg_left hr (Nat.cast_nonneg (α := ℝ) A)]

-- Fix the charge A before n and P. Arbitrarily large admitted horizons still contain
-- an active actual direct call whose nominal IH cannot fit the old sufficient reserve.
example (A n : ℕ) :
    ∃ (P : ℕ) (hP : P.Prime),
      let : Fact P.Prime := ⟨hP⟩
      ∃ H : Horizon P, n ≤ H.maxExponent ∧
      let B := data HP P A n
      let r := request HP P
      let M := budget HP A n
      let q := (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source
        (BudgetData.midpoint r) r.terminal (B.binRate 0)).direct
      let scale := (P : ℝ) ^ 2 / (P * r.source.rate) *
        HierarchyTask.residualCostCoefficient (k := HP.k) (V := ZMod P) (channels B.padding)
          B.bins 0 r.source (BudgetData.midpoint r) r.terminal B.binRate 1 1
      M ≤ 32 * H.maxExponent ∧
        0 < B.requestPrecision M r ∧ 0 < B.requestPrecision (B.binBudget M 0 r) q ∧
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 / (1 + scale) <
          ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M 0 r) q)) ^ 4 := by
  let R := (HierarchyTask.residual (k := HP.k) 0).rank
  let depth := 4 * (n + A * R + 1) + 4 * A * R + 2
  obtain ⟨P, hP, hlo, _, H, hH, _⟩ := exists_bounded_depth_prime depth 0 (by positivity)
  let : Fact P.Prime := ⟨hP⟩
  refine ⟨P, hP, H, ?_, ?_⟩
  · rw [hH]; dsimp only [depth]; omega
  dsimp only
  refine ⟨?_, (bin_zero_active HP A n).1, (bin_zero_active HP A n).2, ?_⟩
  · rw [hH]
    dsimp only [budget, depth, R]
    omega
  · apply (data HP P A n).residual_mean_coarse_allowance_lt_nominal
      (budget HP A n) _ (Nat.le_of_lt ((data HP P A n).binBudget_lt
        (by unfold budget; omega) 0 _)) _ 0 2 [1] [2, 3] rfl rfl rfl
      (Nat.cast_nonneg (α := ℝ) A) 1 1
    have hpow : (2 : ℝ) ^ (4 * (A : ℝ) * R) ≤ (2 : ℝ) ^ depth := by
      rw [← Real.rpow_natCast]
      apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
      dsimp only [depth]
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) A,
        Nat.cast_nonneg (α := ℝ) R]
    have hp : (2 : ℝ) ^ depth < P := by exact_mod_cast hlo
    have hp1 : (1 : ℝ) ≤ P := by exact_mod_cast hP.one_lt.le
    change (2 : ℝ) ^ (4 * (A : ℝ) * R) < 8 * (P : ℝ) ^ 2
    nlinarith [hpow.trans_lt hp]

-- Positive bin one and the special negative use genuinely different budgets.
example {P : ℕ} [Fact P.Prime] (A n : ℕ) :
    (data HP P A n).binBudget (budget HP A n) 1 (request HP P) = budget HP A n - 5 ∧
    (data HP P A n).childBudget (budget HP A n) = budget HP A n - 1 := by
  constructor
  · have hscale := (data HP P A n).sampleScale_grid (request HP P) 0 1 rfl rfl
    norm_num only [Nat.cast_zero, Nat.cast_one, zero_sub, mul_neg, mul_one] at hscale
    change ⌊Real.logb 2 ((data HP P A n).binRate 1 / (request HP P).terminal.rate)⌋ = -4
      at hscale
    unfold BudgetData.binBudget
    rw [hscale]
    norm_num [LogSpaceEstimation.lastBudget, LogSpaceEstimation.scaleCutoff, data]
  · exact (budget_zero HP A n).2

-- Unequal inherited and reset sources produce a real precision gain even though both
-- children have the same finer usage channel. The original nonempty suffix is retained.
example {P : ℕ} [Fact P.Prime] (A m : ℕ) :
    let B := data HP P A 3
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.residual 0, gridChannel 0 3 [1], gridChannel 2 1 [2, 3], gridChannel 2 2 [2, 3]⟩
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 2 .residual r.source
      (BudgetData.midpoint r) r.terminal (B.binRate 2)
    B.requestPrecision m Q.right - B.requestPrecision m Q.direct = 4 ∧
      Q.right.source.suffix = [] ∧ Q.direct.source.suffix = [1] ∧
      Q.right.usage = Q.direct.usage := by
  dsimp only
  refine ⟨?_, rfl, rfl, rfl⟩
  rw [(data HP P A 3).requestPrecision_grid m 1 2 _ rfl rfl,
    (data HP P A 3).requestPrecision_grid m 3 2 _ rfl rfl]
  simp only [HierarchyTask.rawRequests]
  ring

-- A literal successful normalized constructor from supplied row/vector children.
-- This executes normalization only; it is not recursive evaluate/compressed availability.
example :
    let P := 5
    let B := data HP P 1 1
    let r : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨.row 0 (.normalized ⟨0, HP.k_pos⟩), gridChannel 0 1 [1],
        gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩
    let history := fun (_ : ℕ) (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) =>
      match q.task with
      | .row _ (.maximum _) => some (BudgetValue.vector (fun _ _ => 0))
      | _ => some (BudgetValue.row (fun _ => 1))
    let : Fact (Nat.Prime P) := ⟨by decide⟩
    ∃ A, B.normalized history 3 r false ⟨0, HP.k_pos⟩ = some A ∧
      ∀ σ z, #{x ∈ ({x | r.source.retains (channels B.padding) σ x} : Finset _) |
        A σ x z ≠ 0} < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
  dsimp only
  let : Fact (Nat.Prime 5) := ⟨by decide⟩
  let r : HierarchyTask.Request HP.k (Fin 3) (ZMod 5) :=
    ⟨.row 0 (.normalized ⟨0, HP.k_pos⟩), gridChannel 0 1 [1],
      gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩
  let history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod 5) → Option (BudgetValue 5) :=
    fun _ q =>
    match q.task with
    | .row _ (.maximum _) => some (BudgetValue.vector (fun _ _ => 0))
    | _ => some (BudgetValue.row (fun _ => 1))
  have he : ∃ A, (data HP 5 1 1).normalized history 3 r false ⟨0, HP.k_pos⟩ = some A := by
    simp only [BudgetData.normalized, BudgetData.row, BudgetData.vector, history,
      Bool.false_eq_true, ↓reduceIte, Option.bind_some, BudgetValue.row?, BudgetValue.vector?,
      pure]
    exact ⟨_, rfl⟩
  obtain ⟨A, hA⟩ := he
  refine ⟨A, hA, ?_⟩
  intro σ z
  exact (data HP 5 1 1).normalized_col_support history 3 r
    ⟨by change (0 : Fin 3) ≠ 2; decide, rfl, rfl⟩ false ⟨0, HP.k_pos⟩ A hA σ z

end ProductAllocationRegression
