/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Probabilistic.Sampling.F4
import Complexity.Computability.Probabilistic.Repeat
import Mathlib.Tactic.NormNum

/-! The fixed quadratic field, exact probabilities and variable-size native sampling clients. -/

namespace ComplexityTests.F4Sampling

open Cslib Cslib.Probability Turing.MultiTapeTM
open scoped ENNReal

private abbrev F := QuadraticAlgebra (ZMod 2) 1 1
private def theta : F := ⟨0, 1⟩

-- These are four distinct values, and the generator uses field multiplication, not Boolean AND.
example : ([0, 1, theta, theta + 1] : List F).Nodup := by decide
example : theta ^ 2 = theta + 1 := by decide
example : theta ^ 3 = 1 := by decide
example : theta ^ 2 ≠ theta := by decide
example (x : F) (hx : x ≠ 0) : x * x⁻¹ = 1 := mul_inv_cancel₀ hx

-- The encoding keeps both coordinates; the two basis vectors cannot collapse to one word.
example : F4.encoding theta ≠ F4.encoding 1 := by decide
example : F4.equivBits theta = (false, true) := rfl
example : F4.equivBits (theta + 1) = (true, true) := rfl

-- Every scalar has mass 1/4, including the two values outside the prime subfield.
example (x : F) : ProbComp.eval F4.sample x = (1 / 4 : ℝ≥0∞) := by
  rw [F4.eval_sample, PMF.uniformOfFintype_apply, F4.card]
  norm_num

-- A fresh scalar multiplied by θ remains exactly uniform; this consumes nontrivial arithmetic.
example : ProbComp.eval ((theta * ·) <$> F4.sample) = PMF.uniformOfFintype F := by
  rw [ProbComp.eval_map, F4.eval_sample]
  exact PMF.uniformOfFintype_map_equiv (Equiv.mulLeft₀ theta (by decide))

example : IsPPTOn encUnit F4.encoding (fun _ => F4.sample) := F4.isPPTOn_sample
example : ComputableInPolyTime (fun p : F × F => p.1 * p.2)
    (encPair F4.encoding F4.encoding) F4.encoding := F4.computableInPolyTime_mul

-- One machine samples runtime-varying lists, with unary length and all field outputs charged.
example : IsPPTOn encUnary (encList F4.encoding)
    (fun n => OracleComp.replicate n F4.sample) :=
  (F4.isPPTOn_sample.preprocess (ComputableInPolyTime.const ())).replicate
    ComputableInPolyTime.id'

-- Repetition has the actual independent uniform vector law, not just uniform marginals.
example (n : ℕ) : ProbComp.eval (OracleComp.replicate n F4.sample) =
    (PMF.uniformOfFintype (Fin n → F)).map List.ofFn := by
  rw [ProbComp.eval_replicate]
  simp only [F4.eval_sample, PMF.pi_uniformOfFintype]

end ComplexityTests.F4Sampling
