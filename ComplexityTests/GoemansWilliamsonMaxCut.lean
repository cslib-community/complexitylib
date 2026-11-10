/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.MaxCut.GoemansWilliamsonCutWeight

/-! # Tests for Goemans–Williamson rounding

The constant's numerical bounds and its edge cases, and the triangle `K₃`: three unit vectors at
`120°` are optimal for its relaxation, with objective `9 / 4`; the rounded cut has expected weight
`2`, which is the maximum cut. This checks that the hypotheses of the headline guarantee are
satisfiable and that the guarantee holds with room to spare (`α · 2 < 2`). The bridge to
`Cslib.Complexity.MaxCut.cutWeight` is checked on a small weighted instance. -/

namespace ComplexityTests.GoemansWilliamsonMaxCut

open MeasureTheory ProbabilityTheory Real Cslib.Algorithms.Lean.MaxCut
open scoped RealInnerProductSpace

/-! ### The constant -/

example : (0.87856 : ℝ) < goemansWilliamsonConstant ∧ goemansWilliamsonConstant < 0.87857 :=
  ⟨lt_goemansWilliamsonConstant, goemansWilliamsonConstant_lt⟩

/-- The constant is strictly below `1`: random-hyperplane rounding is not exact. -/
example : goemansWilliamsonConstant < 1 := goemansWilliamsonConstant_lt.trans (by norm_num)

/-- At `y = -1` (antipodal vectors) the inequality of Lemma 3.4 reads `α ≤ 1`. -/
example : goemansWilliamsonConstant * ((1 - -1) / 2) ≤ arccos (-1) / π :=
  goemansWilliamsonConstant_mul_le_arccos le_rfl (by norm_num)

/-- At `y = 1` (equal vectors) both sides of Lemma 3.4 vanish. -/
example : goemansWilliamsonConstant * ((1 - 1) / 2) = 0 ∧ arccos 1 / π = 0 := by
  simp

/-! ### The triangle -/

/-- The plane. -/
local notation "P" => EuclideanSpace ℝ (Fin 2)

/-- Three unit vectors at `120°`. -/
noncomputable def tri : Fin 3 → P :=
  ![!₂[1, 0], !₂[-1 / 2, √3 / 2], !₂[-1 / 2, -(√3 / 2)]]

/-- The edges of the triangle. -/
def triEnds : Fin 3 → Fin 3 × Fin 3 := ![(0, 1), (1, 2), (2, 0)]

/-- Unit weights. -/
def triW : Fin 3 → ℝ := fun _ => 1

private theorem sqrt3_sq : √3 ^ 2 = 3 := sq_sqrt (by norm_num)

theorem norm_tri (i : Fin 3) : ‖tri i‖ = 1 := by
  rw [EuclideanSpace.norm_eq, sqrt_eq_one]
  fin_cases i <;> simp only [tri, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    norm_eq_abs, sq_abs, Fin.sum_univ_two, one_pow, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, add_zero, even_two, Even.neg_pow]
  all_goals nlinarith [sqrt3_sq]

theorem inner_tri (e : Fin 3) : ⟪tri (triEnds e).1, tri (triEnds e).2⟫ = -1 / 2 := by
  fin_cases e <;> simp only [tri, triEnds, Fin.reduceFinMk, Fin.zero_eta, Fin.mk_one, Fin.isValue,
    Matrix.cons_val, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one,
    PiLp.inner_apply, RCLike.inner_apply, conj_trivial, Fin.sum_univ_two, one_mul, mul_one,
    mul_zero, zero_mul, neg_mul, mul_neg, neg_zero, add_zero]
  all_goals nlinarith [sqrt3_sq]

theorem sdpValue_tri : sdpValue triEnds triW tri = 9 / 4 := by
  simp only [sdpValue, inner_tri, triW, Fin.sum_univ_three]
  norm_num

/-- `tri` is optimal: for unit vectors `a`, `b`, `c`, `0 ≤ ‖a + b + c‖²` gives
`⟪a, b⟫ + ⟪b, c⟫ + ⟪c, a⟫ ≥ -3 / 2`. -/
theorem isMaxOn_tri : IsMaxOn (sdpValue triEnds triW) {v' | ∀ i, ‖v' i‖ = 1} tri := by
  intro v (hv : ∀ i, ‖v i‖ = 1)
  simp only [Set.mem_ofPred_eq, sdpValue_tri]
  have h := real_inner_self_nonneg (x := v 0 + v 1 + v 2)
  simp only [inner_add_left, inner_add_right, real_inner_self_eq_norm_sq, hv,
    real_inner_comm (v 0) (v 1), real_inner_comm (v 0) (v 2), real_inner_comm (v 1) (v 2)] at h
  simp only [sdpValue, triW, Fin.sum_univ_three, triEnds, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons,
    real_inner_comm (v 0) (v 2)]
  linarith

private theorem arccos_neg_half : arccos (-1 / 2) = 2 * π / 3 := by
  rw [neg_div, arccos_neg, ← cos_pi_div_three,
    arccos_cos (by positivity) (by linarith [pi_pos])]
  ring

/-- The rounded cut of the triangle has expected weight `2` (Theorem 3.1). -/
theorem integral_tri :
    ∫ r, cutValue triEnds triW (hyperplaneSide tri r) ∂stdGaussian P = 2 := by
  rw [integral_cutValue_hyperplaneSide triEnds triW norm_tri]
  simp only [inner_tri, arccos_neg_half, triW, Fin.sum_univ_three]
  field_simp
  norm_num

/-- Every cut of the triangle has weight at most `2`. -/
theorem cutValue_tri_le (side : Fin 3 → Bool) : cutValue triEnds triW side ≤ 2 := by
  have key : ∀ a b c : Bool,
      ((if a ≠ b then (1 : ℝ) else 0) + if b ≠ c then 1 else 0) + (if c ≠ a then 1 else 0) ≤ 2 := by
    intro a b c
    cases a <;> cases b <;> cases c <;> norm_num
  simp only [cutValue, triW, Fin.sum_univ_three, triEnds, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons]
  exact key _ _ _

/-- The headline guarantee applies to the triangle: its hypotheses are satisfiable. -/
example (side : Fin 3 → Bool) :
    goemansWilliamsonConstant * cutValue triEnds triW side ≤
      ∫ r, cutValue triEnds triW (hyperplaneSide tri r) ∂stdGaussian P :=
  goemansWilliamsonConstant_mul_cutValue_le_integral triEnds (fun _ => zero_le_one) norm_tri
    isMaxOn_tri side

/-- The rounding of the triangle achieves the maximum cut exactly in expectation, so the
guarantee `α · 2 ≤ 2` holds strictly. -/
example : goemansWilliamsonConstant * cutValue triEnds triW ![true, false, false] <
    ∫ r, cutValue triEnds triW (hyperplaneSide tri r) ∂stdGaussian P := by
  rw [integral_tri]
  have h : cutValue triEnds triW ![true, false, false] = 2 := by
    simp only [cutValue, triW, Fin.sum_univ_three, triEnds]
    norm_num
  rw [h]
  nlinarith [goemansWilliamsonConstant_lt]

/-- Some hyperplane cut of the triangle has weight at least `α · 2`. -/
example : ∃ r : P, ∀ side : Fin 3 → Bool,
    goemansWilliamsonConstant * (cutValue triEnds triW side - 0) ≤
      cutValue triEnds triW (hyperplaneSide tri r) :=
  exists_forall_goemansWilliamsonConstant_mul_sub_le triEnds (fun _ => zero_le_one) norm_tri
    fun v' hv' => by rw [add_zero]; exact isMaxOn_iff.1 isMaxOn_tri v' hv'

/-- An optimal solution exists in the plane. -/
example : ∃ v : Fin 3 → P, (∀ i, ‖v i‖ = 1) ∧
    IsMaxOn (sdpValue triEnds triW) {v' | ∀ i, ‖v' i‖ = 1} v :=
  exists_isMaxOn_sdpValue triEnds triW

/-! ### The bridge to `MaxCut.cutWeight` -/

/-- A weighted path `0 - 1 - 2` with weights `3` and `5`, and a self-loop of weight `7`. -/
def pathL : List ((ℕ × ℕ) × ℕ) := [((0, 1), 3), ((1, 2), 5), ((2, 2), 7)]

/-- Cutting off vertex `1` cuts both path edges but never the self-loop. -/
example : cutValue (fun i : Fin pathL.length => pathL[i].1) (fun i => (pathL[i].2 : ℝ))
    (fun n => decide (n = 1)) = 8 := by
  rw [cutValue_eq_cutWeight,
    show Cslib.Complexity.MaxCut.cutWeight pathL (fun n => decide (n = 1)) = 8 by decide]
  norm_num

end ComplexityTests.GoemansWilliamsonMaxCut
