/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.CircuitLowerBoundBudget
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.SqrtLog.Budget
import Complexity.Foundations.Data.Nat.SqrtLog.Budget
import Complexity.Foundations.Data.Nat.SqrtLog.LowerBound
import ComplexityTests.ContractionCircuitCounting
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt

/-!
# Checked instances of the quantitative circuit lower-bound budget

These examples exercise rounding, the explicit starting length, rescaling at infinitely many
lengths, computability of the size cap, and the existing counter on a concrete circuit.
-/

namespace ComplexityTests.CircuitLowerBoundBudget

open Cslib.Circuits Cslib.Circuits.Frontier Cslib.Complexity.ContractionCounting
  Turing.MultiTapeTM Filter

-- With `A = 1`, the size cap at `n = 512` is exactly 64. Integer rounding persists until 520.
example : 512 * Nat.sqrt (Nat.log 2 (512 + 2)) / (12 * (1 + 1)) = 64 ∧
    519 * Nat.sqrt (Nat.log 2 (519 + 2)) / (12 * (1 + 1)) = 64 ∧
    520 * Nat.sqrt (Nat.log 2 (520 + 2)) / (12 * (1 + 1)) = 65 := by norm_num

-- Linear overhead can violate the target exponent at small lengths, so the threshold matters.
example : ¬2 * (1 * (21 + 1) / Nat.sqrt (Nat.log 2 (21 + 2))) ≤ 1 := by norm_num

-- The explicit threshold for `A = 1, D = 0` controls the maximal allowed padded size.
example {n : ℕ} (hn : 1 ≤ n) (hpow : 2 ^ 64 ≤ n + 2) :
    let M := 3 * (n * Nat.sqrt (Nat.log 2 (n + 2)) / 24) + n
    2 * ((M + 1) / Nat.sqrt (Nat.log 2 (M + 2))) ≤ n := by
  let M := 3 * (n * Nat.sqrt (Nat.log 2 (n + 2)) / 24) + n
  change 2 * ((M + 1) / Nat.sqrt (Nat.log 2 (M + 2))) ≤ n
  have h := Nat.two_mul_mul_succ_div_sqrt_log_two_le_of_pow_le
    (A := 1) (D := 0) (n := n) (M := M) hn (Nat.le_add_left _ _)
    (by simp only [Nat.reduceAdd, Nat.reduceMul, Nat.zero_mul, Nat.add_zero]; exact le_rfl)
    hpow
  simpa only [Nat.one_mul] using h

-- The natural lower bound `64 < 65` transfers from length 512 to framed length 1024.
example : (1024 : ℝ) * Real.sqrt (Real.logb 2 1024) / 96 < 65 := by
  have h := Nat.mul_sqrt_logb_div_lt_of_div_lt (K := 24) (d := 2) (n := 512) (v := 65)
    (by decide) (by decide) (by decide) (by decide) (by norm_num)
  simpa only [Nat.cast_mul, Nat.cast_ofNat, show (2 : ℝ) * 512 = 1024 by norm_num,
    show (2 : ℝ) * 24 * 2 = 96 by norm_num] using h

-- A concrete unbounded family supplies a nonvacuous instance of the frequent rescaling API.
example : ∃ᶠ N : ℕ in atTop, (N : ℝ) * Real.sqrt (Real.logb 2 N) / 96 <
    ((N * (N + 2) + 1 : ℕ) : ℝ) := by
  have h : ∃ᶠ n : ℕ in atTop,
      n * Nat.sqrt (Nat.log 2 (n + 2)) / 24 < (2 * n) * (2 * n + 2) + 1 := by
    apply (Eventually.of_forall fun n => ?_).frequently
    have hq : Nat.sqrt (Nat.log 2 (n + 2)) ≤ n + 2 :=
      (Nat.sqrt_le_self _).trans (Nat.log_le_self 2 (n + 2))
    have hdiv := Nat.div_le_self (n * Nat.sqrt (Nat.log 2 (n + 2))) 24
    nlinarith [Nat.mul_le_mul_left n hq]
  simpa only [Nat.cast_ofNat, show (2 : ℝ) * 24 * 2 = 96 by norm_num] using
    Nat.frequently_mul_sqrt_logb_div_lt (f := fun N => N * (N + 2) + 1)
      (K := 24) (d := 2) (by decide) (by decide) h

-- The size cap can be computed before nondeterministically guessing a circuit of that size.
example (A : ℕ) : ComputableInPolyTime
    (fun n : ℕ => n * Nat.sqrt (Nat.log 2 (n + 2)) / (12 * (A + 1))) encUnary encUnary :=
  ComputableInPolyTime.unary_mul_sqrt_log_two_div _

-- Reuse the four-gate circuit with ten satisfying inputs from the counting tests. Its small
-- size needs no padding: one fixed counter satisfies the budget at every sufficiently large n.
example : ∃ (count T S : (Σ k, Circuit Boolean.signature k 1) → ℕ) (A e : ℕ),
    count ⟨4, ContractionCircuitCounting.sample⟩ = 10 ∧
    ComputableInO count (Boolean.encCircuit 1) encNat T S ∧
    ∀ n : ℕ, 4 ≤ n → 2 ^ ((16 * A) ^ 2) ≤ n + 2 →
      T ⟨4, ContractionCircuitCounting.sample⟩ ≤ 2 ^ (n / 2) *
        ((Boolean.encCircuit 1 ⟨4, ContractionCircuitCounting.sample⟩).length + 1) ^ e := by
  obtain ⟨count, T, S, A, e, b, hspec, hinO, -, hT⟩ :=
    exists_circuitSatCounter_sizeBudget Boolean.encOp Boolean.interpretation
  refine ⟨count, T, S, A, e, ?_, hinO, fun n hn hpow => ?_⟩
  · rw [hspec]
    decide
  · apply hT 1 n (by omega)
    · apply Nat.le_sqrt'.2
      have := Nat.le_log_of_pow_le Nat.one_lt_two hpow
      convert this using 1; ring
    · have hsize : ContractionCircuitCounting.sample.size = 4 := by decide
      change ContractionCircuitCounting.sample.size ≤ _
      rw [hsize]
      omega

end ComplexityTests.CircuitLowerBoundBudget
