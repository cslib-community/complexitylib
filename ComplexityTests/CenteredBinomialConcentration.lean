/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Languages.Probabilistic.CenteredBinomial.Concentration
import Complexity.Computability.Probabilistic.CenteredBinomial
import Complexity.Probability.PMF.Event

/-! Actual CBD sampler tails: endpoint atoms, width zero, and a growing native program. -/

namespace ComplexityTests.CenteredBinomialConcentration

open Cslib ProbComp Probability Turing.MultiTapeTM

/-- Width zero is deterministic: the non-strict zero cutoff includes its only outcome. -/
example : (eval (sampleCenteredBinomial 0)).toOuterMeasure {z | (0 : ℝ) ≤ |(z : ℝ)|} = 1 := by
  simp

/-- Strictness matters even at width zero. -/
example : (eval (sampleCenteredBinomial 0)).toOuterMeasure {z | (0 : ℝ) < |(z : ℝ)|} = 0 := by
  simp

example : (eval (sampleCenteredBinomial 0)).toOuterMeasure {z | (1 : ℝ) ≤ |(z : ℝ)|} = 0 := by
  simp

/-- Both endpoint signs occur in the actual fair-coin program. -/
example : (8 : ℤ) ∈ (eval (sampleCenteredBinomial 8)).support :=
  (mem_support_sampleCenteredBinomial_iff 8 8).mpr (by decide)

example : (-8 : ℤ) ∈ (eval (sampleCenteredBinomial 8)).support :=
  (mem_support_sampleCenteredBinomial_iff 8 (-8)).mpr (by decide)

/-- The non-strict endpoint tail has positive probability, so the theorem is not vacuous. -/
example : 0 < ((eval (sampleCenteredBinomial 8)).toOuterMeasure
    {z | (8 : ℝ) ≤ |(z : ℝ)|}).toReal := by
  rw [PMF.toOuterMeasure_toReal_pos_iff]
  exact ⟨8, by norm_num, (mem_support_sampleCenteredBinomial_iff 8 8).mpr (by decide)⟩

/-- The same endpoint cutoff has an empty strict tail. -/
example : (eval (sampleCenteredBinomial 8)).toOuterMeasure {z | (8 : ℝ) < |(z : ℝ)|} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  intro z hz hbad
  have hnat := (mem_support_sampleCenteredBinomial_iff 8 z).mp hz
  have hint : |z| ≤ (8 : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast hnat
  have hreal : |(z : ℝ)| ≤ 8 := by exact_mod_cast hint
  exact not_lt_of_ge hreal hbad

/-- The actual positive tail also has a strict upper bound below one. -/
example : ((eval (sampleCenteredBinomial 8)).toOuterMeasure
    {z | (8 : ℝ) ≤ |(z : ℝ)|}).toReal < 1 := by
  have h := sampleCenteredBinomial_tail_le (η := 8) (B := 8) (by decide) (by norm_num)
  norm_num only [Nat.cast_ofNat, neg_div, pow_succ, pow_zero, mul_one] at h
  have h' : ((eval (sampleCenteredBinomial 8)).toOuterMeasure
      {z | (8 : ℝ) ≤ |(z : ℝ)|}).toReal ≤ 4 * Real.exp (-4) := by
    apply (ENNReal.le_ofReal_iff_toReal_le (PMF.toOuterMeasure_ne_top _ _)
      (by positivity)).mp
    convert h using 1
  apply h'.trans_lt
  rw [Real.exp_neg, mul_inv_lt_iff₀ (Real.exp_pos 4)]
  linarith [Real.add_one_le_exp (4 : ℝ)]

/-- One certified native program samples every growing width from a unary parameter. -/
example : IsPPTOn encUnary encIntBin
    (fun l : ℕ => sampleCenteredBinomial (8 * (l + 1))) := by
  fun_prop

/-- This growing-width tail is the scalar input to the later polynomial-coordinate union bound.
The declaration concerns the actual native program's law, not a fresh noise distribution. -/
example (l : ℕ) :
    (eval (sampleCenteredBinomial (8 * (l + 1)))).toOuterMeasure
      {z | (4 * (l + 1) : ℝ) < |(z : ℝ)|} ≤
        ENNReal.ofReal (4 * Real.exp (-(l + 1 : ℕ))) := by
  have h := sampleCenteredBinomial_strict_tail_le
    (η := 8 * (l + 1)) (B := 4 * (l + 1)) (by positivity) (by positivity)
  have he : -(4 * ((l : ℝ) + 1)) ^ 2 / (2 * (8 * ((l : ℝ) + 1))) =
      -((l : ℝ) + 1) := by
    field_simp
    ring
  simpa only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one, he] using h

end ComplexityTests.CenteredBinomialConcentration
