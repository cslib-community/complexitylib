/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger, Christian Reitwiessner
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.AndreevThresholdAbstract

/-! # Concrete clients and non-vacuity checks for the Andreev threshold-circuit abstract

Checks the public evaluation, wire and Andreev definitions, the exact upper-bound witness and its
gate weights on 8 bits, positive improved gate and wire lower bounds for an actual circuit on
32568 bits, and positive top fan-in bounds for an actual three-member majority vote on 521344 bits.
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
circuit of `49` gates and at most `432` active wires computing `andreev 2 2` on all `256` inputs.
Each gate reads only inputs, with integer weights in `{-2, …, 2}`, or only gates, with odd integer
weights of absolute value below `16`. -/
example :
    ∃ c : ThrCircuit 8,
      c.depth ≤ 2 ∧
      c.size = 49 ∧
      ComplexityAbstracts.AndreevThresholdAbstract.wireCount c ≤ 432 ∧
      (∀ x, evaluate c x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 2 2 x) ∧
      ∀ gate : Fin c.size,
        ((∀ a, ∃ i, (c.program.lines gate).wires a = Wire.input i) ∧
          ∀ a, ∃ z : ℤ, |z| ≤ 2 ∧ (c.program.lines gate).op.weight a = z) ∨
        ((∀ a, ∃ g, (c.program.lines gate).wires a = Wire.gate g) ∧
          ∀ a, ∃ z : ℤ, Odd z ∧ |z| < 16 ∧ (c.program.lines gate).op.weight a = z) :=
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
  obtain ⟨c, hd, _, _, hcomp, -⟩ := exact_upper_bound 14 1156
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

/-- The top fan-in bounds are nonvacuous on an actual majority vote: three copies of the exact
circuit at `b = 18, m = 14400` satisfy `3 (b + 2) / sqrt(2 ^ b) ≤ 1 / (2 t)` for `t = 3`, and the
bounds force each copy to have at least 51 gates and 4369067 active wires. -/
example : ∃ C : Fin 3 → ThrCircuit (2 ^ 18 + 18 * 14400),
    (∀ i, (C i).depth ≤ 2) ∧
    (∀ x, 3 < 2 * (Finset.univ.filter fun i =>
      evaluate (C i) x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 18 14400 x).card) ∧
    51 ≤ (C 0).size ∧ 4369067 ≤ ComplexityAbstracts.AndreevThresholdAbstract.wireCount (C 0) := by
  have hsqrt18 : Real.sqrt ((2 : ℝ) ^ 18) = 512 :=
    (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
  have hb : 3 * (((18 : ℕ) : ℝ) + 2) / Real.sqrt ((2 : ℝ) ^ 18) ≤ 1 / (2 * ((3 : ℕ) : ℝ)) := by
    rw [hsqrt18]; norm_num
  set c := andreevCircuit 18 14400
  have hvote : ∀ x, 3 < 2 * (Finset.univ.filter fun _ : Fin 3 =>
      evaluate c x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 18 14400 x).card := by
    intro x
    have hx : evaluate c x = ComplexityAbstracts.AndreevThresholdAbstract.andreev 18 14400 x :=
      congrFun (computes_andreevCircuit 18 14400 x) 0
    simp [hx]
  have hd : ∀ _ : Fin 3, c.depth ≤ 2 := fun _ => depth_andreevCircuit_le 18 14400
  clear_value c
  have hgate := majority_vote_gate_lower_bound (b := 18) (m := 14400) (t := 3) (by norm_num)
    (by norm_num) hb (fun _ => c) hd c.size (fun _ => le_rfl) hvote
  have hwire := majority_vote_wire_lower_bound (b := 18) (m := 14400) (t := 3) (by norm_num)
    (by norm_num) hb (fun _ => c) hd _ (fun _ => le_rfl) hvote
  have hsqrt_n : Real.sqrt (((2 ^ 18 + 18 * 14400 : ℕ) : ℝ)) ≤ 723 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by norm_num⟩
  have hsize_gt : (50 : ℝ) < (c.size : ℝ) := by
    have hgate' := hgate.trans (mul_le_mul_of_nonneg_left hsqrt_n
      (by positivity : (0 : ℝ) ≤ 576 * (((18 : ℕ) : ℝ) + 2) * ((3 : ℕ) : ℝ) ^ 2 * (c.size : ℝ)))
    norm_num at hgate'
    linarith
  have hwire_gt : (4369066 : ℝ) <
      (ComplexityAbstracts.AndreevThresholdAbstract.wireCount c : ℝ) := by
    have hsqrt_m : Real.sqrt ((14400 : ℕ) : ℝ) = 120 :=
      (Real.sqrt_eq_iff_eq_sq (by norm_num) (by norm_num)).mpr (by norm_num)
    rw [hsqrt_m] at hwire
    norm_num at hwire
    linarith
  exact ⟨fun _ => c, hd, hvote, by exact_mod_cast hsize_gt, by exact_mod_cast hwire_gt⟩

end ComplexityTests.Abstracts.AndreevThresholdTests
