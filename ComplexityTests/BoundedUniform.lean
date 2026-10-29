/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.BoundedUniform
import Mathlib.Tactic.NormNum

/-! Finite-attempt laws retain failure, and both unary boxes and exponentially large binary
intervals have uniform certificates with runtime-varying budgets. -/

namespace ComplexityTests.BoundedUniform

open Cslib Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

example (attempts bound : ℕ) :
    ProbComp.eval (sampleUniformInterval 0 attempts) = PMF.pure none ∧
    sampleUniformInterval bound 0 = pure none := by
  exact ⟨by simp, rfl⟩

-- Three accepted indices each have dyadic mass 1/4; the remaining 1/4 is explicit failure.
example :
    (ProbComp.eval (sampleUniformInterval 3 1) (some 0)).toReal = 1 / 4 ∧
    (ProbComp.eval (sampleUniformInterval 3 1) (some 2)).toReal = 1 / 4 ∧
    (ProbComp.eval (sampleUniformInterval 3 1) (some 3)) = 0 ∧
    (ProbComp.eval (sampleUniformInterval 3 3) none).toReal = 1 / 64 := by
  refine ⟨?_, ?_, by simp [eval_sampleUniformInterval_some], ?_⟩
  · rw [eval_sampleUniformInterval_some_toReal (by decide : 0 < 3)]
    norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]
  · rw [eval_sampleUniformInterval_some_toReal (by decide : 0 < 3)]
    norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]
  · rw [eval_sampleUniformInterval_none]
    norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

-- Conditional 1/3 is not asserted to be the unconditional mass or an exact PPT sampler.
example : (ProbComp.eval (sampleUniformInterval 3 1) (some 0)).toReal /
    (((ProbComp.eval (sampleUniformInterval 3 1)).map Option.isSome) true).toReal = 1 / 3 :=
  sampleUniformInterval_conditional (by decide) (by decide) (by decide)

-- Radius zero is a singleton reference box, but the generic finite-attempt sampler can fail.
example (radius : ℕ) :
    sampleIntegerBox radius 0 0 = pure (some []) ∧
    (ProbComp.eval (sampleIntegerBox 1 2 0) none).toReal = 1 ∧
    (ProbComp.eval (sampleIntegerBox 1 2 1) none).toReal = 7 / 16 ∧
    (ProbComp.eval (sampleIntegerBox 1 2 1) (some [-1, 1])).toReal = 1 / 16 ∧
    (ProbComp.eval (sampleIntegerBox 0 1 1) none).toReal = 1 / 2 := by
  refine ⟨rfl, ?_, ?_, ?_, ?_⟩
  · rw [eval_sampleIntegerBox_none]
    norm_num
  · rw [eval_sampleIntegerBox_none]
    norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]
  · have href : integerBoxLaw 1 2 [-1, 1] = (3 : ℝ≥0∞)⁻¹ ^ 2 := by
      simpa using integerBoxLaw_apply_index 1 2 ![0, 2]
    rw [eval_sampleIntegerBox_some_toReal, href]
    norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]
  · rw [eval_sampleIntegerBox_none]
    norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

-- Radius, dimension and attempts are all runtime parameters, not fixed Lean constants.
example : IsPPTOn (encPair encUnary (encPair encUnary encUnary)) (encOption (encList encInt))
    (fun p : ℕ × ℕ × ℕ => sampleIntegerBox p.1 p.2.1 p.2.2) := by
  apply isPPTOn_sampleIntegerBox <;> polytime

-- The same sampler supports an exponentially large binary bound; no unary 2^width is charged.
example : IsPPTOn (encPair encUnary encUnary) (encOption encNat)
    (fun p : ℕ × ℕ => sampleUniformInterval (2 ^ p.1) p.2) := by
  apply isPPTOn_sampleUniformInterval_binary (width := fun p => p.1 + 1)
  · exact ComputableInPolyTime.binary_two_pow.comp (by fun_prop)
  · polytime
  · polytime
  · intro p
    simp [Nat.log_pow Nat.one_lt_two]

-- Every supported outcome of `sampleIntegerBox 1 2 1` has encoded length at most `2 * 5 + 1 = 11`.
example {out : Option (List ℤ)}
    (h : out ∈ (ProbComp.eval (sampleIntegerBox 1 2 1)).support) :
    (encOption (encList encInt) out).length ≤ 11 := by
  have := length_enc_sampleIntegerBox h
  omega

end ComplexityTests.BoundedUniform
