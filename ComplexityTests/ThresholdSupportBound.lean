/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.WeightedThreshold.SupportBoundAsymptotics
import Complexity.Computability.Circuit.Frontier.TwoSidedWitness

/-! Quantitative regressions separating the direct-support bounds from the balanced-cut bound.
The incidence bound also improves the earlier random-cut bound at the same dimension and
rectangle threshold. The hypothesis has an existential witness, with no efficiency claim. -/

open Cslib Cslib.Circuits Cslib.Circuits.Boolean.WeightedThreshold

-- The hypotheses used in the large finite lower-bound client below are jointly satisfiable.
example : ∃ f : Cslib.BooleanFunction 2000000,
    ∀ b : Bool, Frontier.RectangleFree {x | f x = b} 32000016 := by
  simpa using Frontier.exists_twoSided_rectangleFree 2000000

-- The old bound is compatible with 1,050,000 input-reading gates.
example : 2000000 ≤ 2 * (1050000 + 25) := by norm_num

-- The random-cut theorem rules out that budget and forces at least 1,052,028 gates.
example {g : ℕ} (p : Program signature 2000000 g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction 2000000}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} 32000016)
    (hsupport : ∀ gate, (inputSupport p gate).card ≤ 3) :
    1052028 ≤ (inputGates p).card := by
  have h := le_inputGates_of_inputSupport_card_le p readout hreadout hf hsupport 39
    (k := 25) (by norm_num)
  norm_num at h
  have hsqrt : Real.sqrt 4000000 = 2000 := by
    apply (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr
    norm_num
  rw [hsqrt] at h
  by_contra! hsmall
  have hq : (inputGates p).card ≤ 1052027 := by omega
  have hqR : ((inputGates p).card : ℝ) ≤ 1052027 := by exact_mod_cast hq
  linarith

-- The generic random-cut coefficient is a strict improvement over one half.
example : (1 : ℝ) / (2 * (1 - (1 / 2 : ℝ) ^ 3)) = 4 / 7 ∧ (1 / 2 : ℝ) < 4 / 7 := by
  norm_num

-- The incidence theorem at the same witnessed parameters forces at least 1,321,177 gates.
example {g : ℕ} (p : Program signature 2000000 g)
    (readout : (Fin g → Bool) → Bool) {f : Cslib.BooleanFunction 2000000}
    (hreadout : ∀ x, readout (p.eval interpretation x) = f x)
    (hf : ∀ b : Bool, Frontier.RectangleFree {x | f x = b} 32000016)
    (hsupport : ∀ gate, (inputSupport p gate).card ≤ 3) :
    1321177 ≤ (inputGates p).card := by
  have h := two_mul_lt_inputGates_of_inputSupport_card_le_three
    p readout hreadout hf hsupport 255 (k := 25) (by norm_num)
  by_contra! hsmall
  have hq : (inputGates p).card ≤ 1321176 := by omega
  have hlog : Nat.log 2 (2000000 + (inputGates p).card) ≤ 21 := by
    have h := Nat.log_mono_right (b := 2) (show 2000000 + (inputGates p).card ≤ 3321176
      by omega)
    exact h.trans (by decide)
  have hqR : ((inputGates p).card : ℝ) ≤ 1321176 := by exact_mod_cast hq
  have hlogR : (Nat.log 2 (2000000 + (inputGates p).card) : ℝ) ≤ 21 :=
    by exact_mod_cast hlog
  norm_num at h
  linarith

-- The incidence coefficient exceeds both the previous library endpoint and the transversal
-- comparison obtained by combining the classical rank-three transversal bound with rank two.
example : (4 / 7 : ℝ) < 2 / 3 ∧ (3 / 5 : ℝ) < 2 / 3 := by
  norm_num
