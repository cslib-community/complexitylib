/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.FineGrained.CountingSparsificationUniform
public import CslibFrontier.Foundations.Data.Nat.LogLogSqrtLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryLog
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Sqrt
import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Log

/-!
# The sharper counting-sparsification schedule and its actual binary clock

Compute the Appendix D.3, p. 57 divisor `ceil(sqrt(clog₂ n))` of [OpenAI2026ETH], using one
at exceptional sizes with zero logarithm. Discharge the existing disjoint counting-tree budget
at its computed first-success threshold, and bound the actual traversal clock by the
single-loglog scale. The companion `IncidenceGeneralCounter` already connects sparse leaves
to the native parity counter semantically. Whole-search resource certification is supplied
separately by `IncidenceGeneralResources`, toward Lemma 3.2 in [ChenJiangZhu2027].
The old replacement-matrix schedule is not used.
-/

public section

namespace Cslib.Complexity.CountingSparsify

open Cslib.Logic.PL Cslib.Logic.PL.ClauseSet.Sparsification Turing.MultiTapeTM

/-- The source divisor, rounded up; zero-logarithm inputs use the total value one. -/
@[expose] def sharpSearchDivisor (n : ℕ) : ℕ := (Nat.clog 2 n - 1).sqrt + 1

/-- The exact integer characterization of the source ceiling square root. -/
theorem sharpSearchDivisor_bounds {n : ℕ} (hn : 2 ≤ n) :
    (sharpSearchDivisor n - 1) ^ 2 < Nat.clog 2 n ∧
      Nat.clog 2 n ≤ sharpSearchDivisor n ^ 2 := by
  have hlog : 1 ≤ Nat.clog 2 n := Nat.clog_pos Nat.one_lt_two (by omega)
  have hlo := Nat.sqrt_le (Nat.clog 2 n - 1)
  have hhi := Nat.lt_succ_sqrt (Nat.clog 2 n - 1)
  simp only [Nat.succ_eq_add_one] at hhi
  simp only [sharpSearchDivisor, Nat.add_sub_cancel, pow_two]
  constructor <;> omega

/-- The divisor is positive, so the disjoint counting-tree budget has no zero-divisor premise. -/
theorem sharpSearchDivisor_pos (n : ℕ) : 1 ≤ sharpSearchDivisor n := by
  unfold sharpSearchDivisor
  omega

/-- The actual schedule is computed in polynomial binary time from declared unary size. -/
@[fun_prop] theorem sharpSearchDivisor_polytime :
    ComputableInPolyTime sharpSearchDivisor encUnary encNat := by
  have hc := ComputableInPolyTime.binary_clog_two_nat.comp
    ComputableInPolyTime.unary_to_binary
  unfold sharpSearchDivisor
  fun_prop

/-- An unconditional disjoint counting-tree budget at the source schedule's computed threshold.
No faster sparsification procedure or tree-budget contract is supplied. -/
theorem sharp_countingTreeBound {K : ℕ} (hK : 1 ≤ K) (n : ℕ) :
    CountingTreeBound (countingThresholdBase K (sharpSearchDivisor n)) K (sharpSearchDivisor n)
      (countingDepthCoeff K (countingThresholdBase K (sharpSearchDivisor n)))
      ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase K (sharpSearchDivisor n))) hK :=
  countingTreeBound_countingThresholdBase hK (sharpSearchDivisor_pos n)

/-- The exponential traversal clock is constructed in binary, with polynomial time and space.
This is computation of the clock, not a claim that exponentially many steps take polynomial time. -/
theorem sharp_rounds_polytime :
    ComputableInPolyTime (fun x : ℕ × CNF ℕ => rounds (sharpSearchDivisor x.1) x.2)
      (encPair encUnary encCNF) encNat :=
  computableInPolyTime_roundsWith sharpSearchDivisor_polytime

/-- The computed first-success threshold, depth coefficient and leaf occurrence bound are
polynomials in the ceiling logarithm. This bounds numerical depth, not merely its binary length. -/
theorem sharp_parameters_polylog {K : ℕ} (hK : 2 ≤ K) :
    ∃ p : ℕ → ℕ, Cslib.PolynomiallyBounded p ∧ ∀ n,
      let M := countingThresholdBase K (sharpSearchDivisor n)
      countingDepthCoeff K M ≤ p (Nat.clog 2 n) ∧
        occBound K M + 1 ≤ p (Nat.clog 2 n) := by
  obtain ⟨A, hA⟩ := exists_countingThresholdBase_le_mul_clog hK
  let u (t : ℕ) := 2 * A * (t + 1) ^ 2
  let p (t : ℕ) := countingBChoiceCoeff K * u t ^ (K - 2) +
    2 * K * u t ^ (K - 1) + 1
  have hp : Cslib.PolynomiallyBounded p := by dsimp only [p, u]; fun_prop
  refine ⟨p, hp, fun n => ?_⟩
  let M := countingThresholdBase K (sharpSearchDivisor n)
  have hM1 : 1 ≤ M := (by decide : 1 ≤ 2).trans (two_le_countingThresholdBase _ _)
  have hB : sharpSearchDivisor n ≤ Nat.clog 2 n + 1 := by
    exact Nat.add_le_add_right ((Nat.sqrt_le_self _).trans (Nat.sub_le _ _)) 1
  have hc : Nat.clog 2 (sharpSearchDivisor n) ≤ Nat.clog 2 n + 1 :=
    ((Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
      (Nat.lt_two_pow_self (n := sharpSearchDivisor n)).le).trans hB
  have hM : M ≤ u (Nat.clog 2 n) := by
    calc
      _ ≤ A * sharpSearchDivisor n * (Nat.clog 2 (sharpSearchDivisor n) + 1) :=
        hA _ (sharpSearchDivisor_pos n)
      _ ≤ A * (Nat.clog 2 n + 1) * (Nat.clog 2 n + 2) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left A hB) (Nat.add_le_add_right hc 1)
      _ ≤ A * (Nat.clog 2 n + 1) * (2 * (Nat.clog 2 n + 1)) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by dsimp only [u]; ring
  have hd := (countingDepthCoeff_le_mul_pow hM1).trans
    (Nat.mul_le_mul_left (countingBChoiceCoeff K) (Nat.pow_le_pow_left hM (K - 2)))
  have ho : occBound K M ≤ 2 * K * u (Nat.clog 2 n) ^ (K - 1) := by
    calc
      _ ≤ 2 * ∑ _j ∈ Finset.range K, M ^ (K - 1) := by
        apply Nat.mul_le_mul_left 2
        apply Finset.sum_le_sum
        intro j hj
        exact Nat.pow_le_pow_right hM1 (by have := Finset.mem_range.mp hj; omega)
      _ = 2 * K * M ^ (K - 1) := by simp [Nat.mul_assoc]
      _ ≤ _ := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hM (K - 1))
  dsimp only [M] at hd ho
  dsimp only [p]
  constructor <;> omega

/-- The actual source-schedule leaf density eventually fits a fixed parity density exponent. -/
theorem exists_sharp_leaf_density {K : ℕ} (hK : 2 ≤ K) :
    ∃ β N : ℕ, ∀ n, N ≤ n →
      occBound K (countingThresholdBase K (sharpSearchDivisor n)) + 1 ≤ Nat.clog 2 n ^ β := by
  obtain ⟨p, hp, hb⟩ := sharp_parameters_polylog hK
  obtain ⟨β, hβ⟩ := hp
  have ht : Filter.Tendsto (Nat.clog 2) Filter.atTop Filter.atTop :=
    Filter.tendsto_atTop_mono (fun n => Nat.log_le_clog 2 n)
      (Nat.tendsto_log_atTop Nat.one_lt_two)
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (ht.eventually hβ)
  exact ⟨β, N, fun n hn => (hb n).2.trans (hN n hn)⟩

/-- The actual depth-first traversal clock fits the sharp exponent for every supported formula,
independently of clause density and including unused declared variables. -/
theorem sharp_rounds_le {n : ℕ} (hn : 4 ≤ n) {φ : CNF ℕ}
    (hv : φ.vars.toFinset ⊆ Finset.range n) :
    rounds (sharpSearchDivisor n) φ ≤ 4 * 2 ^ Nat.logLogSqrtLogScale n := by
  have hnvars : φ.numVars ≤ n := by
    simpa only [CNF.numVars, Finset.card_range] using Finset.card_le_card hv
  have hroot : (Nat.log 2 n).sqrt ≤ sharpSearchDivisor n :=
    (Nat.sqrt_le_sqrt (Nat.log_le_clog 2 n)).trans
      ((Nat.sqrt_le_sqrt (sharpSearchDivisor_bounds (by omega : 2 ≤ n)).2).trans_eq
        (Nat.sqrt_eq' _))
  have hdiv : φ.numVars / sharpSearchDivisor n ≤ Nat.logLogSqrtLogScale n :=
    ((Nat.div_le_div_right hnvars).trans
      (Nat.div_le_div_left hroot (Nat.one_le_sqrt_log_two (by omega)))).trans
      (Nat.div_sqrt_log_two_le_logLogSqrtLogScale hn)
  calc
    rounds (sharpSearchDivisor n) φ = 2 ^ (φ.numVars / sharpSearchDivisor n + 2) := by
      rw [rounds, CNF.length_distinctVars]
    _ ≤ 2 ^ (Nat.logLogSqrtLogScale n + 2) :=
      Nat.pow_le_pow_right (by decide) (Nat.add_le_add_right hdiv 2)
    _ = _ := by rw [pow_add]; ring

end Cslib.Complexity.CountingSparsify
