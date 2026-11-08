/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Arithmetic.Rigidity

/-!
# Matrix rigidity and Valiant's criterion

Checked instances: the rigidity of identity matrices, zero rigidity when the rank is already low,
rigidity at target rank zero, a one-gate fan-in-`2` affine circuit (with `t = D` and `t < D`) and
the zero-gate identity circuit (depth `0`) satisfying every hypothesis of
`Circuit.Computes.rigidity_le`, a one-gate arithmetic
circuit satisfying every hypothesis of `Circuit.Computes.rigidity_le_of_isPolynomial`, and a matrix
satisfying the rigidity and size hypotheses of `Circuit.Computes.mul_log_log_lt_size`.
-/

namespace ComplexityTests.MatrixRigidity

open Cslib.Circuits Matrix

/-! ### Rigidity -/

-- The `5 × 5` identity has rigidity `5 - r`; target ranks at least `5` need no changes.
example : (1 : Matrix (Fin 5) (Fin 5) ℚ).rigidity 2 = 3 := by
  rw [rigidity_one, Fintype.card_fin]

example : (1 : Matrix (Fin 5) (Fin 5) ℚ).rigidity 7 = 0 := by
  rw [rigidity_one, Fintype.card_fin]

-- Positive rigidity: a full-rank matrix cannot be made rank `0` for free.
example : 0 < (1 : Matrix (Fin 3) (Fin 3) ℚ).rigidity 0 := by
  rw [rigidity_one, Fintype.card_fin]
  decide

-- Zero rigidity: the zero matrix already has rank at most `0`.
example : (0 : Matrix (Fin 3) (Fin 4) ℚ).rigidity 0 = 0 :=
  rigidity_eq_zero_iff.2 (by simp)

-- At target rank `0`, rigidity counts the nonzero entries: all `16 * 16` for the all-ones matrix.
theorem rigidity_ones : (of fun _ _ => 1 : Matrix (Fin 16) (Fin 16) ℚ).rigidity 0 = 256 := by
  rw [rigidity_zero, diffCount_eq_card_filter]
  simp

/-! ### A circuit satisfying the hypotheses of the quantitative criterion -/

/-- One affine gate `x₀ + x₁`, of fan-in `2`. -/
private abbrev sumCircuit : Circuit (affineSignature ℚ) 2 1 :=
  ⟨Program.empty.gate ⟨⟨2, fun _ => 1, 0⟩, Wire.input⟩, fun _ => .gate 0⟩

private theorem sumCircuit_computes :
    sumCircuit.Computes (affineInterpretation ℚ) (!![(1 : ℚ), 1] *ᵥ ·) := by
  intro x
  funext o
  fin_cases o
  change (Program.empty.gate _).eval (affineInterpretation ℚ) x (Fin.last 0) = _
  rw [Program.eval_gate_last]
  simp [Line.eval, mulVec, dotProduct, Fin.sum_univ_two]

private theorem sumCircuit_fanIn : sumCircuit.FanInAtMost 2 := by
  decide

private theorem sumCircuit_depth : sumCircuit.depth < 2 ^ 1 := by
  decide

-- Every hypothesis holds: one gate, fan-in `2`, depth `1 < 2 ^ 1`, and `t = 1 ≤ D = 1`.
example : (!![(1 : ℚ), 1]).rigidity (2 * 1 * 1 / 1) ≤ 1 * 2 ^ (2 ^ (1 - 1)) :=
  sumCircuit_computes.rigidity_le sumCircuit_fanIn sumCircuit_depth le_rfl

-- With slack in the depth, `0 < t < D`: depth `1 < 2 ^ 2`, `t = 1`, `D = 2`.
example : (!![(1 : ℚ), 1]).rigidity (2 * 1 * 1 / 2) ≤ 1 * 2 ^ (2 ^ (2 - 1)) :=
  sumCircuit_computes.rigidity_le sumCircuit_fanIn (by decide) (by norm_num)

-- The zero-gate identity circuit computes the identity matrix with depth `0 < 2 ^ 0`.
example (n : ℕ) :
    (1 : Matrix (Fin n) (Fin n) ℚ).rigidity (2 * 0 * 0 / 0) ≤ n * 2 ^ (2 ^ (0 - 0)) := by
  have hc : (Circuit.id (affineSignature ℚ) n).Computes (affineInterpretation ℚ)
      ((1 : Matrix (Fin n) (Fin n) ℚ) *ᵥ ·) := fun x => by
    simp
  exact hc.rigidity_le (Circuit.fanInAtMost_wiring _ 2) (by simp) le_rfl

/-! ### The criterion for arithmetic circuits over an infinite field -/

/-- One addition gate `x₀ + x₁` over the arithmetic basis. -/
private abbrev addCircuit : Circuit (arithSignature ℚ) 2 1 :=
  ⟨Program.empty.gate ⟨.add, Wire.input⟩, fun _ => .gate 0⟩

private theorem addCircuit_computes :
    addCircuit.Computes (arithInterpretation ℚ) (!![(1 : ℚ), 1] *ᵥ ·) := by
  intro x
  funext o
  fin_cases o
  change (Program.empty.gate _).eval (arithInterpretation ℚ) x (Fin.last 0) = _
  rw [Program.eval_gate_last]
  simp [Line.eval, arithInterpretation, mulVec, dotProduct, Fin.sum_univ_two]

example : (!![(1 : ℚ), 1]).rigidity (2 * 1 * 1 / 1) ≤ 1 * 2 ^ (2 ^ (1 - 1)) :=
  addCircuit_computes.rigidity_le_of_isPolynomial isPolynomial_arithInterpretation
    (Circuit.fanInAtMost_two_arith _) (by decide) le_rfl

/-! ### The hypotheses of the asymptotic criterion are satisfiable -/

private theorem log_sixteen : Nat.log 2 16 = 4 := by
  rw [show (16 : ℕ) = 2 ^ 4 by norm_num, Nat.log_pow one_lt_two]

private abbrev ones : Matrix (Fin 16) (Fin 16) ℚ := of fun _ _ => 1

-- With `n = 16`, `k = 2`, `e = 17`: `2 * k ≤ log₂ 16 = 4`, and the all-ones matrix needs
-- `256 > 16 * 2 ^ (4 / 2)` changes to reach rank `16 / 17 = 0`.
private theorem ones_hyp :
    2 * 2 ≤ Nat.log 2 16 ∧ 16 * 2 ^ (Nat.log 2 16 / 2) < ones.rigidity (16 / 17) := by
  rw [log_sixteen, show 16 / 17 = 0 by norm_num, rigidity_ones]
  norm_num

-- So every fan-in-`2` affine circuit computing it in depth at most `log₂ 16` has a gate.
example {c : Circuit (affineSignature ℚ) 16 16}
    (hc : c.Computes (affineInterpretation ℚ) (ones *ᵥ ·))
    (hfan : c.FanInAtMost 2) (hdepth : c.depth ≤ 1 * Nat.log 2 16) :
    16 * (Nat.log 2 (Nat.log 2 16) + 1) < 2 * 17 * (Nat.log 2 (2 * 1 * 2) + 1) * c.size :=
  hc.mul_log_log_lt_size one_pos two_pos (by norm_num) ones_hyp.1 ones_hyp.2 hfan hdepth

end ComplexityTests.MatrixRigidity
