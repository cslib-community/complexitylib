/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.AndreevThresholdAbstract

/-! # Concrete clients and non-vacuity checks for the Andreev threshold-circuit abstract

Verifies that the public definitions of `AndreevThresholdAbstract` match the library's
(`WeightedThreshold.interpretation`, `Circuit.wireCount`, `Boolean.andreev`,
`WeightedThreshold.andreevSimultaneousTail`), checks `exact_upper_bound` at `b = 2, m = 2`
(`n = 8`), and checks at `b = 14, m = 1156` (`n = 32568`, `α = 2048`) that the simultaneous tail
bound `andreevSimultaneousTail 14 2048 ≤ 1 / 2` is discharged unconditionally and yields strictly
positive gate and wire lower bounds (`9 ≤ c.size` and `52405 ≤ wireCount c`).
-/

namespace ComplexityTests.Abstracts.AndreevThresholdTests

open ComplexityAbstracts.AndreevThresholdAbstract
open Cslib.Circuits Cslib.Circuits.Boolean Cslib.Circuits.Boolean.WeightedThreshold Finset

example {n : ℕ} (c : ThrCircuit n) (x : Fin n → Bool) :
    evaluate c x = c.eval interpretation x 0 :=
  rfl

example {n : ℕ} (c : ThrCircuit n) :
    ComplexityAbstracts.AndreevThresholdAbstract.wireCount c = c.wireCount :=
  rfl

example (b m : ℕ) :
    ComplexityAbstracts.AndreevThresholdAbstract.andreev b m =
      Cslib.Circuits.Boolean.andreev b m :=
  rfl

example (b : ℕ) (α : ℝ) :
    ComplexityAbstracts.AndreevThresholdAbstract.andreevSimultaneousTail b α =
      Cslib.Circuits.Boolean.WeightedThreshold.andreevSimultaneousTail b α :=
  rfl

/-- At `b = 2, m = 2` (`n = 8` bits), `exact_upper_bound` gives a depth-two weighted threshold
circuit of `81` gates (`80` bottom gates and `1` top gate) and at most `720` active wires computing
`andreev 2 2` on all `256` inputs. -/
example :
    ∃ c : ThrCircuit 8,
      c.depth ≤ 2 ∧
      c.size = 81 ∧
      ComplexityAbstracts.AndreevThresholdAbstract.wireCount c ≤ 720 ∧
      (∀ x, evaluate c x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 2 2 x) :=
  exact_upper_bound 2 2

/-- At `b = 14, m = 1156` (`n = 2 ^ 14 + 14 * 1156 = 32568` bits) and scale
`α = (14 + 2) * √(2 ^ 14) = 2048`, `andreevSimultaneousTail_scale_le 14` unconditionally discharges
`andreevSimultaneousTail 14 2048 ≤ 1 / 2`, the lower-bound numerator
`((2 : ℝ) ^ 14 * (1 / 2 - andreevSimultaneousTail 14 2048)) ^ 2 - 2048 ^ 2` is strictly positive,
and `gate_lower_bound_of_le_eps` / `wire_lower_bound_of_le_eps` establish `9 ≤ c.size` and
`52405 ≤ wireCount c` for every depth-two threshold circuit computing `andreev 14 1156`. -/
example :
    ComplexityAbstracts.AndreevThresholdAbstract.andreevSimultaneousTail 14 2048 ≤ 1 / 2 ∧
    0 < ((2 : ℝ) ^ 14 * (1 / 2 -
      ComplexityAbstracts.AndreevThresholdAbstract.andreevSimultaneousTail 14 2048)) ^ 2 -
      (2048 : ℝ) ^ 2 ∧
    ∃ c : ThrCircuit (2 ^ 14 + 14 * 1156),
      c.depth ≤ 2 ∧
      (∀ x, evaluate c x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 14 1156 x) ∧
      9 ≤ c.size ∧
      52405 ≤ ComplexityAbstracts.AndreevThresholdAbstract.wireCount c := by
  have hsqrt14 : Real.sqrt ((2 : ℝ) ^ 14) = 128 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hα_eq : (((14 : ℕ) : ℝ) + 2) * Real.sqrt ((2 : ℝ) ^ 14) = 2048 := by
    rw [hsqrt14]; norm_num
  have hε : 3 * (((14 : ℕ) : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ 14) ≤ (1 / 2 : ℝ) := by
    rw [hsqrt14]; norm_num
  obtain ⟨htail, hexcess⟩ := sq_sub_ge_of_three_mul_div_sqrt_le hε
  rw [hα_eq] at htail hexcess
  refine ⟨htail, (by norm_num : (0 : ℝ) < 1 / 3 * ((2 : ℝ) ^ 14 * (1 / 2)) ^ 2).trans_le hexcess,
    ?_⟩
  obtain ⟨c, hd, _, _, hcomp⟩ := exact_upper_bound 14 1156
  have hcorr : (2 : ℝ) ^ (2 ^ 14 + 14 * 1156) * (1 / 2 + 1 / 2) ≤
      (#{w : Fin (2 ^ 14 + 14 * 1156) → Bool |
        evaluate c w = ComplexityAbstracts.AndreevThresholdAbstract.andreev 14 1156 w} : ℝ) := by
    have hall : (univ.filter fun w : Fin (2 ^ 14 + 14 * 1156) → Bool =>
        evaluate c w = ComplexityAbstracts.AndreevThresholdAbstract.andreev 14 1156 w) = univ :=
      filter_true_of_mem fun w _ => hcomp w
    rw [hall, card_univ, Fintype.card_fun, Fintype.card_fin, Fintype.card_bool, Nat.cast_pow,
      Nat.cast_ofNat, add_halves, mul_one]
  have hgate := gate_lower_bound_of_le_eps (b := 14) (m := 1156) (by decide) hε c hd hcorr
  have hwire := wire_lower_bound_of_le_eps (b := 14) (m := 1156) (by decide) hε c hd hcorr
  have hsqrt_n : Real.sqrt (((2 ^ 14 + 14 * 1156 : ℕ) : ℝ)) ≤ 181 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsize_gt : (8 : ℝ) < (c.size : ℝ) := by
    have hgate' := hgate.trans (mul_le_mul_of_nonneg_left hsqrt_n
      (by positivity : (0 : ℝ) ≤ 12 * (((14 : ℕ) : ℝ) + 2) ^ 2 * (c.size : ℝ)))
    norm_num at hgate'
    linarith
  have hwire_gt :
      (52404 : ℝ) < (ComplexityAbstracts.AndreevThresholdAbstract.wireCount c : ℝ) := by
    have hsqrt_m : Real.sqrt ((1156 : ℕ) : ℝ) = 34 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    rw [hsqrt_m] at hwire
    norm_num at hwire
    linarith
  exact ⟨c, hd, hcomp, by exact_mod_cast hsize_gt, by exact_mod_cast hwire_gt⟩

end ComplexityTests.Abstracts.AndreevThresholdTests
