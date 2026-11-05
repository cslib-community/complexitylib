/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of incoming PREP coarse salary)
import Complexity.Foundations.Probability.HierarchyPreparationSalary
import Complexity.Foundations.Probability.UnroutedBinRegularity

/-!
A growing bounded-prime family has exhaustive nonempty polynomial bins, canonical
nonzero identity base, actual PREP/pilot PREP requests, full terminal usage and positive
own-input precision. The joint scalar guards hold while every fixed positive coarse
coefficient eventually fails. This is an envelope counterexample only. No recursively
successful input or its accuracy is asserted for this growing family. The separately
checked `HierarchyIncomingPreparationBias` client supplies actual nonconstant RAW33/PREP34
execution and positive canonical error; that half-bin fixture is not used here as a
uniform polynomial salary witness.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
attribute [local implicit_reducible] Matrix
namespace PreparationSalaryRegression

/-- The standard exhaustive polynomial-bin data, with identity stage-zero input. -/
private def data (HP : FourthRootHierarchyParams 16 1 16 32 8) (P n : ℕ)
    (charge : ℝ) : BudgetData HP P where
  padding := 1
  base := fun x y => if x = y then 1 else 0
  bins := range (n + 1)
  binRate := rate
  cutoff := fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) rate 1 i (fun _ => 1)
  auxiliary := fun _ => polynomialPrepCutoff4 HP.θ
  slack := 1
  slack_pos := by decide
  rankCharge := charge
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

private def request (HP : FourthRootHierarchyParams 16 1 16 32 8) (P : ℕ)
    (pilot : Bool) : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
  ⟨.row 0 (if pilot then .pilotPreparation ⟨0, HP.k_pos⟩ else .preparation ⟨0, HP.k_pos⟩),
    gridChannel 0 0 [1], gridChannel 2 0 [2, 3], gridChannel 2 0 [2, 3]⟩

-- The full family is independent of successful executions. Charge, floor/sensitivity
-- coefficient and exponents are fixed before growing the field. Both pilot choices
-- and every larger charge satisfy the same obstruction, not just charge zero.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (c charge : ℝ)
    (hc : 0 < c) (hcharge : 1 ≤ charge) (A : ℕ) (pilot : Bool) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀,
      let M := 2 ^ N
      let n := M / 8 + 1
      ∃ P, P.Prime ∧ 2 ^ n < P ∧ P ≤ 2 ^ (n + 1) ∧
        let B := data HP P n charge
        let r := request HP P pilot
        let q := {r with task := .row 0 (if pilot then
          .pilotInput ⟨0, HP.k_pos⟩ else .input ⟨0, HP.k_pos⟩)}
        Admissible r ∧ r.usage = r.terminal ∧ B.bins = range (n + 1) ∧
        B.bins.Nonempty ∧ B.base 0 0 = 1 ∧
        B.base 0 1 = 0 ∧
        (∃ H : Horizon P, H.maxExponent = n ∧ H.maxIdentifier = 3) ∧
        B.slack * (1 + 4 * n) < M ∧ M ≤ 32 * B.slack * n ∧
        16 * (B.slack : ℝ) * (B.rankCharge * r.task.rank +
          A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M ∧
        0 < B.requestPrecision M r ∧
        0 < B.requestPrecision (B.childBudget M) q ∧
        B.childBudget M < M ∧
        ¬ c * (P : ℝ) ^ 2 * ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
          ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  let B₀ := data HP 5 0 charge
  let r₀ := request HP 5 pilot
  obtain ⟨N₀, hfamily⟩ := BudgetData.exists_joint_preparation_envelope_obstruction
    B₀ rfl A 0 0 0 3 pilot ⟨0, HP.k_pos⟩ r₀ rfl rfl rfl c hc
  refine ⟨N₀, ?_⟩
  intro N hN
  have hg := hfamily N hN
  obtain ⟨P, hP, hlo, hhi, hH, hfail⟩ := hg.2.2.2.2.2.2.2.2
  let n := 2 ^ N / 8 + 1
  let B := data HP P n charge
  let r := request HP P pilot
  have hh := hfail B r rfl rfl rfl rfl rfl
  have hM : 0 < 2 ^ N := by positivity
  have hchild := B.requestPrecision_preparation_input_pos rfl hcharge (2 ^ N) hM
    pilot ⟨0, HP.k_pos⟩ r rfl hh.1
  have hP1 : 1 < P := hP.one_lt
  have hz : (0 : ZMod P) ≠ 1 := by
    have : Fact P.Prime := ⟨hP⟩
    exact zero_ne_one
  refine ⟨P, hP, hlo, hhi, ?_⟩
  dsimp only
  refine ⟨by change (0 : Fin 3) ≠ 2 ∧ (2 : Fin 3) = 2 ∧
      ([2, 3] : List (ZMod P)) = [2, 3]; exact ⟨by decide, rfl, rfl⟩, rfl, rfl, ?_, by simp [data],
    by simp [data, hz], hH, ?_, ?_, ?_, hh.1, hchild, B.childBudget_lt hM, hh.2⟩
  · exact ⟨0, by simp [data]⟩
  · simpa only [B₀, data, Nat.add_zero] using hg.2.2.2.2.1
  · exact hg.2.2.2.2.2.1
  · simpa only [B₀, r₀, data, request, Nat.cast_zero, add_zero, zero_add, mul_zero] using
      hg.2.2.2.2.2.2.1

-- Match the coefficient from rooted normalizer sensitivity, with a fixed positive
-- relative floor. This remains an envelope test, not an actual-error lower bound.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (C L scale charge : ℝ)
    (hC : 0 < C) (hL : 0 < L) (hscale : 0 < scale) (pilot : Bool) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, ∀ P : ℕ, 2 ^ n < P → ∀ M : ℕ,
      let B := data HP P n charge
      let r := request HP P pilot
      let q := {r with task := .row 0 (if pilot then
        .pilotInput ⟨0, HP.k_pos⟩ else .input ⟨0, HP.k_pos⟩)}
      ¬ C ^ 4 * (L / (rate 0 * scale)) ^ 4 * (P : ℝ) ^ 2 *
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
          ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  have hc : 0 < C ^ 4 * (L / (rate 0 * scale)) ^ 4 := by
    exact mul_pos (pow_pos hC _) (pow_pos (div_pos hL (mul_pos (rate_pos 0) hscale)) _)
  obtain ⟨n₀, hfail⟩ := BudgetData.exists_preparation_envelope_depth _ charge hc pilot
  refine ⟨n₀, ?_⟩
  intro n hn P hP M
  exact (data HP P n charge).preparation_envelope_unpaid M pilot ⟨0, HP.k_pos⟩
    (request HP P pilot) rfl _ (hfail n hn P hP)

-- The exception c=0 is real; the obstruction cannot be stated with c≥0.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (P n M : ℕ) (pilot : Bool) :
    let B := data HP P n 1
    let r := request HP P pilot
    let q := {r with task := .row 0 (if pilot then
          .pilotInput ⟨0, HP.k_pos⟩ else .input ⟨0, HP.k_pos⟩)}
    0 * (P : ℝ) ^ 2 * ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4 ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  dsimp only
  simpa only [zero_mul] using
    pow_nonneg (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le 4

end PreparationSalaryRegression
