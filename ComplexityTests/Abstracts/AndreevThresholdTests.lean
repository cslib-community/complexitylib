/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.AndreevThresholdAbstract

/-! # Concrete clients and non-vacuity checks for the Andreev threshold-circuit abstract

Checks the public evaluation, wire and Andreev definitions, the exact upper-bound witness on
8 bits, and positive improved gate and wire lower bounds for an actual circuit on 32568 bits.
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

/-- The improved explicit bounds are nonvacuous on an actual circuit: at `b = 14, m = 1156`
they force at least 12 gates and 69874 active wires (the previous bounds gave 9 and 52405). -/
example : ∃ c : ThrCircuit (2 ^ 14 + 14 * 1156),
    c.depth ≤ 2 ∧
    (∀ x, evaluate c x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 14 1156 x) ∧
    12 ≤ c.size ∧ 69874 ≤ ComplexityAbstracts.AndreevThresholdAbstract.wireCount c := by
  have hsqrt14 : Real.sqrt ((2 : ℝ) ^ 14) = 128 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hε : 3 * (((14 : ℕ) : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ 14) ≤ (1 / 2 : ℝ) := by
    rw [hsqrt14]; norm_num
  obtain ⟨c, hd, _, _, hcomp⟩ := exact_upper_bound 14 1156
  have hgate := exact_gate_lower_bound (b := 14) (m := 1156) (by decide) (by decide) hε c hd hcomp
  have hwire := exact_wire_lower_bound (b := 14) (m := 1156) (by decide) (by decide) hε c hd hcomp
  have hsqrt_n : Real.sqrt (((2 ^ 14 + 14 * 1156 : ℕ) : ℝ)) ≤ 181 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsize_gt : (11 : ℝ) < (c.size : ℝ) := by
    have hgate' := hgate.trans (mul_le_mul_of_nonneg_left hsqrt_n
      (by positivity : (0 : ℝ) ≤ 144 * (((14 : ℕ) : ℝ) + 2) * (c.size : ℝ)))
    norm_num at hgate'
    linarith
  have hwire_gt : (69873 : ℝ) <
      (ComplexityAbstracts.AndreevThresholdAbstract.wireCount c : ℝ) := by
    have hsqrt_m : Real.sqrt ((1156 : ℕ) : ℝ) = 34 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    rw [hsqrt_m] at hwire
    norm_num at hwire
    linarith
  exact ⟨c, hd, hcomp, by exact_mod_cast hsize_gt, by exact_mod_cast hwire_gt⟩

end ComplexityTests.Abstracts.AndreevThresholdTests
