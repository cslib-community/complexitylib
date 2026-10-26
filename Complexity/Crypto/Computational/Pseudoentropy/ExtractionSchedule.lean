/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Negligible.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
import Complexity.Tactic.PolyTime

/-!
# A polynomial repetition schedule for label extraction

The information bound is the sampler's seed length plus `n + 2`. Repeating
`32 * (n + 1) * informationBits^2 * (inverseSlack + 1)^2` times makes the concentration
error exponentially small. Reserving two entropy slacks also pays for leftover hashing.
Neither choice depends on the distinguisher's polynomial degree.

## Main definitions

* `count`, `slack`: polynomially computable repetition and entropy budgets.
* `error`: one negligible bound for concentration and leftover hashing.

## Main results

* `error_le`: the entropy budget implies the common extraction-error bound.
* `error_negligible`: that bound decays faster than every inverse polynomial.

## References

* Thomas Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*, TCC 2006, Sections 3.3 and 5.
  [Holenstein2006].
  These explicit constants instantiate our seed-information concentration bound; they are not
  the optimized seed-length parameters in the write-up.

Adapted from the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using typed certificates and nonnegative errors.
-/

@[expose] public section

namespace Cslib.Crypto.Pseudoentropy.ExtractionSchedule

open Turing.MultiTapeTM
open scoped NNReal

/-- A polynomial number of copies, fixed independently of the sequence distinguisher. -/
def count (n sourceBits inverseSlack : ℕ) : ℕ :=
  32 * (n + 1) * (sourceBits + n + 2) ^ 2 * (inverseSlack + 1) ^ 2

/-- Integer entropy slack for concentration; extraction reserves twice this amount. -/
def slack (n sourceBits inverseSlack : ℕ) : ℕ :=
  8 * (n + 1) * (sourceBits + n + 2) ^ 2 * (inverseSlack + 1)

/-- The repetition count is available in unary with polynomial cost. -/
theorem isPolyTime_count {α : Type} {input : α ↪ List Bool} {n sourceBits inverseSlack : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hslack : ComputableInPolyTime inverseSlack input encUnary) :
    ComputableInPolyTime (fun a => count (n a) (sourceBits a) (inverseSlack a))
      input encUnary := by
  unfold count
  polytime

/-- The integer slack is available in unary with polynomial cost. -/
theorem isPolyTime_slack {α : Type} {input : α ↪ List Bool} {n sourceBits inverseSlack : α → ℕ}
    (hn : ComputableInPolyTime n input encUnary)
    (hsource : ComputableInPolyTime sourceBits input encUnary)
    (hslack : ComputableInPolyTime inverseSlack input encUnary) :
    ComputableInPolyTime (fun a => slack (n a) (sourceBits a) (inverseSlack a))
      input encUnary := by
  unfold slack
  polytime

attribute [program_certificate] isPolyTime_count isPolyTime_slack

/-- Reserving two slacks costs exactly `1 / (2 * (inverseSlack + 1))` bits per sample. -/
theorem two_slack_eq (n sourceBits inverseSlack : ℕ) :
    2 * (slack n sourceBits inverseSlack : ℝ) =
      count n sourceBits inverseSlack / (2 * (inverseSlack + 1)) := by
  apply (eq_div_iff (by positivity : (2 * ((inverseSlack : ℝ) + 1)) ≠ 0)).mpr
  unfold count slack
  push_cast
  ring

/-- One common exponential bound covers concentration and leftover hashing. -/
noncomputable def error (n : ℕ) : ℝ≥0 :=
  ⟨2 * Real.exp (-4 * ((n : ℝ) + 1)) + (1 / 2 : ℝ) ^ n, by positivity⟩

/-- The explicit extraction error is negligible. -/
theorem error_negligible : Negligible error := by
  apply negligible_iff_coe.mpr
  have hgeom : Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ))
      (fun n => Real.exp (-4 : ℝ) ^ n) := negligible_iff_coe.mp (negligible_geometric
    (ratio := ⟨Real.exp (-4), (Real.exp_pos _).le⟩)
    (by change Real.exp (-4) < 1; rw [Real.exp_lt_one_iff]; norm_num))
  have hexp (n : ℕ) : Real.exp (-4 * ((n : ℝ) + 1)) =
      Real.exp (-4) ^ n * Real.exp (-4) := by
    rw [show -4 * ((n : ℝ) + 1) = n * (-4) + (-4) by ring,
      Real.exp_add, Real.exp_nat_mul]
  apply (((hgeom.mul_const (Real.exp (-4))).const_mul 2).add
    (negligible_iff_coe.mp (negligible_geometric (ratio := (1 / 2 : ℝ≥0)) (by norm_num)))).congr
  intro n
  change 2 * (Real.exp (-4) ^ n * Real.exp (-4)) + (1 / 2 : ℝ) ^ n = _
  exact congrArg (fun x => 2 * x + (1 / 2 : ℝ) ^ n) (hexp n).symm

private theorem slack_ge (n sourceBits inverseSlack : ℕ) :
    2 * n + 1 ≤ slack n sourceBits inverseSlack := by
  have hproduct : 1 ≤ (sourceBits + n + 2) ^ 2 * (inverseSlack + 1) :=
    Nat.succ_le_of_lt (by positivity)
  calc
    2 * n + 1 ≤ 8 * (n + 1) := by lia
    _ = 8 * (n + 1) * 1 := by ring
    _ ≤ 8 * (n + 1) * ((sourceBits + n + 2) ^ 2 * (inverseSlack + 1)) :=
      Nat.mul_le_mul_left _ hproduct
    _ = slack n sourceBits inverseSlack := by unfold slack; ring

/-- This schedule extracts below the density by two slacks with negligible error. The output
length is an ordinary natural number; the density occurs only in the correctness premise. -/
theorem error_le (n sourceBits inverseSlack outputBits : ℕ) (density : ℝ)
    (hlength : outputBits + 2 * (slack n sourceBits inverseSlack : ℝ) ≤
      count n sourceBits inverseSlack * density) :
    2 * Real.exp (-2 * (slack n sourceBits inverseSlack : ℝ) ^ 2 /
        (count n sourceBits inverseSlack * (sourceBits + n + 2 : ℕ) ^ 2)) +
      Real.sqrt ((2 : ℝ) ^ outputBits * (2 * (2 : ℝ) ^
        (-(count n sourceBits inverseSlack * density - slack n sourceBits inverseSlack)))) / 2 ≤
      (error n : ℝ) := by
  have hexponent : -2 * (slack n sourceBits inverseSlack : ℝ) ^ 2 /
      (count n sourceBits inverseSlack * (sourceBits + n + 2 : ℕ) ^ 2) =
        -4 * ((n : ℝ) + 1) := by
    apply (div_eq_iff (by unfold count; positivity)).mpr
    unfold slack count
    push_cast
    ring
  have hslack : 2 * (n : ℝ) + 1 ≤ slack n sourceBits inverseSlack := by
    exact_mod_cast slack_ge n sourceBits inverseSlack
  have hpower : (2 : ℝ) ^ outputBits * (2 * (2 : ℝ) ^
      (-(count n sourceBits inverseSlack * density - slack n sourceBits inverseSlack))) =
        (2 : ℝ) ^ ((outputBits : ℝ) + 1 -
          (count n sourceBits inverseSlack * density - slack n sourceBits inverseSlack)) := by
    rw [Real.rpow_sub (by norm_num), Real.rpow_add (by norm_num),
      Real.rpow_natCast, Real.rpow_one, Real.rpow_neg (by norm_num)]
    ring
  have hsmall : (2 : ℝ) ^ (-(2 * (n : ℝ))) = ((1 / 2 : ℝ) ^ n) ^ 2 := by
    rw [Real.rpow_neg (by norm_num), show 2 * (n : ℝ) = ((n * 2 : ℕ) : ℝ) by push_cast; ring,
      Real.rpow_natCast, pow_mul]
    simp only [one_div, inv_pow]
  have hroot : Real.sqrt ((2 : ℝ) ^ outputBits * (2 * (2 : ℝ) ^
      (-(count n sourceBits inverseSlack * density - slack n sourceBits inverseSlack)))) ≤
        (1 / 2 : ℝ) ^ n := by
    apply (Real.sqrt_le_left (by positivity)).mpr
    rw [hpower, ← hsmall]
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    linarith
  rw [hexponent]
  change _ ≤ 2 * Real.exp (-4 * ((n : ℝ) + 1)) + (1 / 2 : ℝ) ^ n
  have hnonneg : (0 : ℝ) ≤ (1 / 2 : ℝ) ^ n := by positivity
  linarith

end Cslib.Crypto.Pseudoentropy.ExtractionSchedule
