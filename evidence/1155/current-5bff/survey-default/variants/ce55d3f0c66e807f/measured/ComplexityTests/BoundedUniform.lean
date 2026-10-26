/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.BoundedUniform
import Mathlib.Tactic.NormNum


import Diag1155.Measure
/-! Finite-attempt laws retain failure, and both unary boxes and exponentially large binary
intervals have uniform certificates with runtime-varying budgets. -/


diag1155_install
namespace ComplexityTests.BoundedUniform

open Cslib Cslib.ProbComp Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal NNReal

example (attempts : ℕ) :
    ProbComp.eval (sampleUniformInterval 0 attempts) = PMF.pure none := by simp

example (bound : ℕ) : sampleUniformInterval bound 0 = pure none := rfl

-- Three accepted indices each have dyadic mass 1/4; the remaining 1/4 is explicit failure.
example : (ProbComp.eval (sampleUniformInterval 3 1) (some 0)).toReal = 1 / 4 := by
  rw [eval_sampleUniformInterval_some_toReal (by decide : 0 < 3)]
  norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

example : (ProbComp.eval (sampleUniformInterval 3 1) (some 2)).toReal = 1 / 4 := by
  rw [eval_sampleUniformInterval_some_toReal (by decide : 0 < 3)]
  norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

example : (ProbComp.eval (sampleUniformInterval 3 1) (some 3)) = 0 := by
  simp [eval_sampleUniformInterval_some]

example : (ProbComp.eval (sampleUniformInterval 3 3) none).toReal = 1 / 64 := by
  rw [eval_sampleUniformInterval_none]
  norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

-- Conditional 1/3 is not asserted to be the unconditional mass or an exact PPT sampler.
example : (ProbComp.eval (sampleUniformInterval 3 1) (some 0)).toReal /
    (((ProbComp.eval (sampleUniformInterval 3 1)).map Option.isSome) true).toReal = 1 / 3 :=
  sampleUniformInterval_conditional (by decide) (by decide) (by decide)

example (test : Option ℕ → Bool) :
    |(((ProbComp.eval (sampleUniformInterval 3 8)).map test) true).toReal -
      ((((PMF.uniformOfFintype (Fin 3)).map Fin.val).map
        (fun value => test (some value))) true).toReal| ≤ 1 / 256 := by
  convert sampleUniformInterval_test_error_le 3 8 test using 1; norm_num

example (radius : ℕ) : sampleIntegerBox radius 0 0 = pure (some []) := rfl

example : (ProbComp.eval (sampleIntegerBox 1 2 0) none).toReal = 1 := by
  rw [eval_sampleIntegerBox_none]
  norm_num

example : (ProbComp.eval (sampleIntegerBox 1 2 1) none).toReal = 7 / 16 := by
  rw [eval_sampleIntegerBox_none]
  norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

example : (ProbComp.eval (sampleIntegerBox 1 2 1) (some [-1, 1])).toReal = 1 / 16 := by
  have href : integerBoxLaw 1 2 [-1, 1] = (3 : ℝ≥0∞)⁻¹ ^ 2 := by
    simpa using integerBoxLaw_apply_index 1 2 ![0, 2]
  rw [eval_sampleIntegerBox_some_toReal, href]
  norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

-- Radius zero is a singleton reference box, but the generic finite-attempt sampler can fail.
example : (ProbComp.eval (sampleIntegerBox 0 1 1) none).toReal = 1 / 2 := by
  rw [eval_sampleIntegerBox_none]
  norm_num [intervalFailure, dyadicSize, show Nat.log 2 3 = 1 by decide]

example (test : Option (List ℤ) → Bool) :
    |(((ProbComp.eval (sampleIntegerBox 1 2 8)).map test) true).toReal -
      (((integerBoxLaw 1 2).map (fun out => test (some out))) true).toReal| ≤ 1 / 128 := by
  convert sampleIntegerBox_test_error_le 1 2 8 test using 1; norm_num

-- Radius, dimension and attempts are all runtime parameters, not fixed Lean constants.
example : IsPPTOn (encPair encUnary (encPair encUnary encUnary)) (encOption (encList encInt))
    (fun p : ℕ × ℕ × ℕ => sampleIntegerBox p.1 p.2.1 p.2.2) := by
  apply isPPTOn_sampleIntegerBox <;> polytime

-- The same sampler supports an exponentially large binary bound; no unary 2^width is charged.
example : IsPPTOn (encPair encUnary encUnary) (encOption encNat)
    (fun p : ℕ × ℕ => sampleUniformInterval (2 ^ p.1) p.2) := by
  apply isPPTOn_sampleUniformInterval_binary (width := fun p => p.1 + 1)
  · exact .of_tidy (ComputableTidilyInPolyTime.binary_two_pow.comp (by fun_prop))
  · polytime
  · polytime
  · intro p
    simp [Nat.log_pow Nat.one_lt_two]

example {radius dimension attempts : ℕ} {out : Option (List ℤ)}
    (h : out ∈ (ProbComp.eval (sampleIntegerBox radius dimension attempts)).support) :
    (encOption (encList encInt) out).length ≤ dimension * (2 * radius + 3) + 1 :=
  length_enc_sampleIntegerBox h

end ComplexityTests.BoundedUniform
