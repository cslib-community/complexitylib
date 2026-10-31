/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
import Complexity.Foundations.Probability.AtomCutoffs
import Complexity.Foundations.Probability.CorrectionAtom
import Complexity.Foundations.Probability.RootMetric
import Complexity.Foundations.Analysis.RootError
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-!
# Tests for smooth switches, root errors and root metrics

* The switch at its midpoint and the reflection of its complement.
* The correction atom identity and the incoming cap with the smooth cutoffs of (5.5) and (5.12),
  every hypothesis discharged.
* Ordinary versus root error, and the homogeneous loss, on concrete values.
* The row norm and the uniform bound on a concrete table.
-/

namespace ComplexityTests.RootMetric

open Finset Matrix Cslib Real
open scoped BigOperators

/-! ### Smooth switches -/

-- The switch `χ_{0,1}` is `1/2` at the midpoint.
example : smoothSwitch 0 1 (1 / 2) = 1 / 2 := by
  have hpos := expNegInvGlue.pos_of_pos (by norm_num : (0 : ℝ) < 1 / 2)
  rw [smoothSwitch, smoothTransition]
  norm_num
  field_simp
  ring

-- The complement of `χ_{0,1}` at `1/4` is its value at `3/4`.
example : 1 - smoothSwitch 0 1 (1 / 4) = smoothSwitch 0 1 (3 / 4) := by
  rw [smoothSwitch, smoothSwitch, smoothTransition.one_sub]
  norm_num

-- The fourth roots of the incoming cutoff are Lipschitz.
example : ∃ K, LipschitzWith K fun r => incomingCutoff r ^ (1 / 4 : ℝ) :=
  exists_lipschitzWith_incomingCutoff_rpow (by norm_num)

/-! ### The correction atom with the smooth cutoffs -/

/-- Correction cutoff: zero through `ϑ = 1/4`. -/
private noncomputable def Q : ℝ → ℝ := fun v => if v ≤ 1 / 4 then 0 else v

private theorem le_of_Q_ne_zero {v : ℝ} (hQ : Q v ≠ 0) : 1 / 4 < v := by
  unfold Q at hQ
  split_ifs at hQ with h
  · exact absurd rfl hQ
  · exact not_le.1 h

/-- The `½`-walk `0 → 1 → 2` on three vertices. -/
private noncomputable def W : Matrix (Fin 3) (Fin 3) ℝ := !![0, 1 / 2, 0; 0, 0, 1 / 2; 0, 0, 0]

private theorem filter_W : (univ.filter fun w : Fin 3 => (1 / 4 / 8 : ℝ) < W w 1 / 1) = {0} := by
  ext w; fin_cases w <;> norm_num [W]

-- With channels that retain everything, `ϑ = 1/4`, `K = 8004` and `K_c = 8`, the correction
-- atom at `(0, 1)` with multiplier `3` has conditional mean `Q (1/2) · 3 = 3/2`.
example : 𝔼 d ∈ (univ.filter fun _ : Unit => True) ×ˢ (univ.filter fun _ : Unit => True),
    correctionAtom (auxCutoff (1 / 4)) incomingCutoff 8004 8 1 W (fun _ _ => True)
      (fun _ _ => True) (fun _ _ => True) Q (prepCutoff (1 / 4)) (rowCutoff (1 / 4))
      (fun _ => 3) d 0 1 = 3 / 2 := by
  have h := expect_correctionAtom (I := auxCutoff (1 / 4)) (τ := incomingCutoff) (K := 8004)
    (Kc := 8) (f := 1) (G := W) (X := fun (_ : Unit) (_ : Fin 3) => True)
    (Y := fun (_ : Unit) (_ : Fin 3) => True) (Yt := fun _ _ => True) (Q := Q)
    (h := prepCutoff (1 / 4)) (ρ := rowCutoff (1 / 4)) (g₀ := fun _ => 3) (x := 0) (y := 1)
    ⟨(), by simp⟩ ⟨(), by simp⟩
    (fun v hv => prepCutoff_eq_one (by norm_num) (by linarith [le_of_Q_ne_zero hv]))
    (rowCutoff_nonneg _) (rowCutoff_le_one _) (by norm_num : (0 : ℝ) < 1 / 4 / 1000)
    (fun r hr => rowCutoff_eq_one (by norm_num) hr) incomingCutoff_nonneg incomingCutoff_le_one
    (by norm_num : (0 : ℝ) ≤ 1 / 4) (fun r hr => incomingCutoff_eq_one hr)
    (fun v r hv => auxCutoff_eq_zero (by norm_num) hv) one_pos
    (fun w => by fin_cases w <;> norm_num [W]) (M := 1 / 2) (by simp [W, Fin.sum_univ_three])
    (c := 1) zero_le_one (by norm_num) (fun w _ => by simp) (p := 1) zero_le_one
    (fun w _ => by simp) (B := 1) (fun _ => by rw [filter_W]; norm_num) (by norm_num)
  rw [h]
  norm_num [Q, W]

-- The incoming cap with the smooth cutoffs: on every draw of any channels, fewer than `K_c = 2`
-- retained sources have a nonzero correction atom in a column.
example {ι κ : Type*} [Fintype ι] [Fintype κ] (X : ι → Fin 3 → Prop) (Y Yt : κ → Fin 3 → Prop)
    [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)] [∀ t v, Decidable (Yt t v)]
    (G : Matrix (Fin 3) (Fin 3) ℝ) (g₀ : Fin 3 → ℝ) (d : ι × κ) (y : Fin 3) :
    #{x ∈ ({w | X d.1 w} : Finset (Fin 3)) |
        correctionAtom (auxCutoff (1 / 4)) incomingCutoff 3 2 1 G X Y Yt Q (prepCutoff (1 / 4))
          (rowCutoff (1 / 4)) g₀ d x y ≠ 0} < 2 := by
  refine card_filter_correctionAtom_col_ne_zero_lt (by norm_num) ?_ (g := 1 / 2) (by norm_num)
    (fun r hr => incomingCutoff_eq_zero hr) d y
  intro v r hQ hρ
  have hv := le_of_Q_ne_zero hQ
  exact auxCutoff_eq_one_of_rowCutoff_ne_zero (by norm_num) (by linarith) hρ

/-! ### Root error and the homogeneous loss -/

private theorem sixteen_rpow : (16 : ℝ) ^ ((4 : ℕ)⁻¹ : ℝ) = 2 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

-- `|16 - 1| ≤ 4 · 16^{3/4} · |16^{1/4} - 1^{1/4}| = 4 · 8 · 1`.
example : |(16 : ℝ) - 1| ≤ 32 := by
  have h := abs_sub_le_mul_abs_rpow_inv_sub (s := 4) (by norm_num) (z := 16) (w := 1) (C := 16)
    (by norm_num) (by norm_num) le_rfl (by norm_num)
  have h34 : (16 : ℝ) ^ ((((4 : ℕ) : ℝ) - 1) / ((4 : ℕ) : ℝ)) = 8 := by
    rw [show (((4 : ℕ) : ℝ) - 1) / ((4 : ℕ) : ℝ) = ((4 : ℕ) : ℝ)⁻¹ * (3 : ℕ) by norm_num,
      Real.rpow_mul (by norm_num), sixteen_rpow, Real.rpow_natCast]
    norm_num
  rw [h34, sixteen_rpow, Real.one_rpow] at h
  norm_num at h ⊢

example : homogeneousLoss 2 3 1 = 1 := by norm_num [homogeneousLoss]

-- The loss is not additive: `L(1, 1) = 0` lies below `L(1, 0) + L(0, 1) = 2`.
example : homogeneousLoss 2 (1 + 0) (0 + 1) ≤ homogeneousLoss 2 1 0 + homogeneousLoss 2 0 1 := by
  have h := homogeneousLoss_sum_le (s := 2) (univ : Finset (Fin 2)) (by norm_num)
    (w := fun _ => 1) (F := ![1, 0]) (F' := ![0, 1]) (fun _ _ => zero_le_one)
    (fun i _ => by fin_cases i <;> norm_num) (fun i _ => by fin_cases i <;> norm_num)
  simpa [Fin.sum_univ_two] using h

-- The clipped relative error (7.7) for `H = 1 ≤ 1 · G` with `G = 1`, `H' = 3` and `a = 1`.
example : 1 * min 1 (|(1 : ℝ) - 3| / (1 + 1)) ^ 2 ≤ 2 * (3 * 1 + 3) ^ 1 * 1 := by
  have h := mul_min_pow_le_homogeneousLoss (s := 2) (by norm_num) (C₀ := 1) (G := 1) (a := 1)
    (H := 1) (H' := 3) zero_le_one zero_le_one one_pos zero_le_one (by norm_num) (by norm_num)
  have hL : homogeneousLoss 2 1 3 = 1 := by norm_num [homogeneousLoss]
  rwa [hL] at h

/-! ### Row norms -/

/-- A table on `Fin 2` with a single nonzero entry `2` at `(0, 1)`. -/
private def Z : Unit → Fin 2 → Fin 2 → ℝ := fun _ x y => if x = 0 ∧ y = 1 then 2 else 0

-- Its fourth-power norm with full channels, `N = 2` and `u = 1` is `2^4 / 2 = 8`.
example : rowNormPow 4 2 1 (fun (_ : Unit) (_ : Fin 2) => True) (fun _ _ => True) Z = 8 := by
  simp [rowNormPow, Z, Fin.sum_univ_two]
  norm_num

-- The uniform bound: one nonzero entry of size `2` per row gives `‖Z‖^4 ≤ 1 · 2^4 · ‖1‖^4 = 16`.
example : rowNormPow 4 2 1 (fun (_ : Unit) (_ : Fin 2) => True) (fun _ _ => True) Z ≤ 16 := by
  have h := rowNormPow_le_of_card_le (s := 4) (N := 2) (u := 1) (K := 1) (B := 2)
    (X := fun (_ : Unit) (_ : Fin 2) => True) (Y := fun _ _ => True) (Z := Z) (by norm_num)
    (by norm_num) (by norm_num) (fun _ x y => by unfold Z; split_ifs <;> norm_num)
    (fun σ x _ => card_le_one.2 fun a ha b hb => by
      simp only [Z, mem_filter, mem_univ, true_and, ne_eq, ite_eq_right_iff, not_forall] at ha hb
      obtain ⟨⟨_, rfl⟩, _⟩ := ha
      obtain ⟨⟨_, rfl⟩, _⟩ := hb
      rfl)
  have hv : vertexNormPow 4 2 1 (fun (_ : Unit) (_ : Fin 2) => True) (fun _ _ => (1 : ℝ)) = 1 := by
    simp [vertexNormPow]
  rw [hv] at h
  norm_num at h
  exact h

end ComplexityTests.RootMetric
