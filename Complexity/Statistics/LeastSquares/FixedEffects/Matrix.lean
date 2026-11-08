/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Statistics.LeastSquares.Monotone
import Mathlib.Tactic

/-!
# The real fixed-effects design matrix

The matrix form of [XuGaoHu2027], equation (2), PDF p. 9. Columns consist of one
regressor and one dummy for each *nonempty retained* group. Empty groups must be
removed before forming this design; retaining their zero dummy columns makes the
Gram matrix singular. The observations and responses are arbitrary real numbers.
-/

public section

namespace Cslib.LeastSquares.FixedEffects.MatrixModel

open Matrix

variable {G : Type*} [Fintype G] [DecidableEq G]
variable {I : G → Type*} [∀ g, Fintype (I g)]

/-- The slope column is `none`, and `some g` is the dummy for group `g`. -/
@[expose] def row (x : (g : G) → I g → ℝ) (p : Sigma I) : Option G → ℝ
  | none => x p.1 p.2
  | some g => if p.1 = g then 1 else 0

/-- Actual observation Gram matrix, with one dummy per retained group. -/
@[expose] noncomputable def gram (x : (g : G) → I g → ℝ) :
    Matrix (Option G) (Option G) ℝ :=
  ∑ p, vecMulVec (row x p) (row x p)

/-- Actual design-transpose response vector. -/
@[expose] noncomputable def response (x y : (g : G) → I g → ℝ) : Option G → ℝ :=
  ∑ p : Sigma I, y p.1 p.2 • row x p

/-- Recomputed mean in a retained group. -/
@[expose] noncomputable def average (z : (g : G) → I g → ℝ) (g : G) : ℝ :=
  (∑ i, z g i) / Fintype.card (I g)

/-- Sum of within-group cross-scatters. -/
@[expose] noncomputable def cross (x y : (g : G) → I g → ℝ) : ℝ :=
  ∑ g, ((∑ i, x g i * y g i) -
    (∑ i, x g i) * (∑ i, y g i) / Fintype.card (I g))

/-- Sum of within-group regressor scatters. -/
@[expose] noncomputable def scatter (x : (g : G) → I g → ℝ) : ℝ := cross x x

/-- Coefficients obtained by refitting each group mean at a proposed slope. -/
@[expose] noncomputable def coefficients (x y : (g : G) → I g → ℝ) (b : ℝ) : Option G → ℝ
  | none => b
  | some g => average y g - b * average x g

omit [∀ g, Fintype (I g)] in
/-- Each row evaluates to its group intercept plus the common slope contribution. -/
theorem row_dot (x : (g : G) → I g → ℝ) (v : Option G → ℝ) (g : G) (i : I g) :
    row x ⟨g, i⟩ ⬝ᵥ v = x g i * v none + v (some g) := by
  simp [dotProduct, Fintype.sum_option, row]

/-- Dummy coordinates of the actual matrix equation. -/
theorem gram_dummy (x : (g : G) → I g → ℝ) (v : Option G → ℝ) (g : G) :
    (gram x *ᵥ v) (some g) =
      (∑ i, x g i) * v none + Fintype.card (I g) * v (some g) := by
  simp only [gram, sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sigma, row_dot]
  simp [row, Finset.sum_add_distrib, Finset.sum_mul]

/-- Regressor coordinate of the actual matrix equation. -/
theorem gram_slope (x : (g : G) → I g → ℝ) (v : Option G → ℝ) :
    (gram x *ᵥ v) none =
      ∑ g, ((∑ i, x g i * x g i) * v none + (∑ i, x g i) * v (some g)) := by
  simp only [gram, sum_mulVec, vecMulVec_mulVec, op_smul_eq_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Fintype.sum_sigma, row_dot, row]
  apply Finset.sum_congr rfl
  intro g _
  simp only [add_mul, Finset.sum_add_distrib, Finset.sum_mul]
  simp only [mul_comm, mul_assoc]

/-- The response's dummy coordinates are group response sums. -/
theorem response_dummy (x y : (g : G) → I g → ℝ) (g : G) :
    response x y (some g) = ∑ i, y g i := by
  simp [response, Fintype.sum_sigma, row]

/-- The response's slope coordinate is the pooled regressor-response sum. -/
theorem response_slope (x y : (g : G) → I g → ℝ) :
    response x y none = ∑ g, ∑ i, x g i * y g i := by
  simp [response, Fintype.sum_sigma, row, mul_comm]

/-- Leaving the dummy of a vanished group in the design makes the Gram matrix
singular. This explains why a fixed-column stability problem cannot in general
represent the paper's refitting convention. -/
theorem not_posDef_of_empty_group (x : (g : G) → I g → ℝ) (g : G) [IsEmpty (I g)] :
    ¬ (gram x).PosDef := by
  have hr (p : Sigma I) : row x p (some g) = 0 := by
    rcases p with ⟨h, i⟩
    dsimp only [row]
    split_ifs with he
    · subst h
      exact isEmptyElim i
    · rfl
  have hd : gram x (some g) (some g) = 0 := by
    simp [gram, vecMulVec, Matrix.sum_apply, hr]
  intro hp
  have hs : 0 < gram x (some g) (some g) := hp.diag_pos
  rw [hd] at hs
  exact lt_irrefl _ hs

variable [∀ g, Nonempty (I g)]

omit [Fintype G] [DecidableEq G] in
private theorem card_ne (g : G) : (Fintype.card (I g) : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (ne_of_gt Fintype.card_pos)

/-- Dummy normal equations force the refitted intercepts; this is derived from
the actual design and does not assume the within-estimator formula. -/
theorem normal_dummy_iff (x y : (g : G) → I g → ℝ) (v : Option G → ℝ) (g : G) :
    (gram x *ᵥ v) (some g) = response x y (some g) ↔
      v (some g) = average y g - v none * average x g := by
  rw [gram_dummy, response_dummy]
  dsimp only [average]
  constructor
  · intro h
    field_simp [card_ne g]
    nlinarith [h]
  · intro h
    rw [h]
    field_simp [card_ne g]
    ring

/-- Eliminating the dummy equations leaves precisely the pooled centered equation. -/
theorem normal_equations_iff (x y : (g : G) → I g → ℝ) (v : Option G → ℝ) :
    gram x *ᵥ v = response x y ↔
      v = coefficients x y (v none) ∧ scatter x * v none = cross x y := by
  have hreduce (b : ℝ) :
      (gram x *ᵥ coefficients x y b) none - response x y none =
        scatter x * b - cross x y := by
    rw [gram_slope, response_slope]
    change (∑ g, ((∑ i, x g i * x g i) * b +
      (∑ i, x g i) * (average y g - b * average x g))) -
      (∑ g, ∑ i, x g i * y g i) = _
    unfold scatter cross
    rw [Finset.sum_mul, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    dsimp only [average]
    intro g _
    ring
  constructor
  · intro h
    have hc : v = coefficients x y (v none) := by
      funext j
      cases j with
      | none => rfl
      | some g => exact (normal_dummy_iff x y v g).mp (congrFun h (some g))
    refine ⟨hc, ?_⟩
    have hs := congrFun h none
    rw [hc] at hs
    have hr := hreduce (v none)
    linarith
  · rintro ⟨hc, hs⟩
    funext j
    cases j with
    | none =>
      have hr := hreduce (v none)
      rw [← hc] at hr
      linarith
    | some g =>
      apply (normal_dummy_iff x y v g).mpr
      exact congrFun hc (some g)

/-- If the within-scatter is nonzero the normal equations have a unique solution,
whose slope is the within-group ratio. -/
theorem normal_equations_unique (x y : (g : G) → I g → ℝ)
    (hv : scatter x ≠ 0) (v : Option G → ℝ) :
    gram x *ᵥ v = response x y ↔ v = coefficients x y (cross x y / scatter x) := by
  rw [normal_equations_iff]
  constructor
  · rintro ⟨hc, hs⟩
    have hb : v none = cross x y / scatter x := (eq_div_iff hv).mpr (by linarith)
    rwa [hb] at hc
  · intro h
    subst v
    refine ⟨rfl, ?_⟩
    change scatter x * (cross x y / scatter x) = cross x y
    exact mul_div_cancel₀ _ hv

omit [DecidableEq G] in
/-- Within-scatter is a sum of real squares, not an assumed nonsingularity test. -/
theorem scatter_eq_sum_sq (x : (g : G) → I g → ℝ) :
    scatter x = ∑ g, ∑ i, (x g i - average x g) ^ 2 := by
  unfold scatter cross
  apply Finset.sum_congr rfl
  intro g _
  have he (i : I g) : (x g i - average x g) ^ 2 =
      x g i * x g i - 2 * average x g * x g i + average x g ^ 2 := by ring
  simp_rw [he]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, average]
  field_simp [card_ne g]
  ring

omit [DecidableEq G] in
/-- Nonnegativity of the derived within-scatter. -/
theorem scatter_nonneg (x : (g : G) → I g → ℝ) : 0 ≤ scatter x := by
  rw [scatter_eq_sum_sq]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- The actual Gram matrix is positive definite exactly when the pooled
within-group regressor scatter is positive. Every retained dummy is nonzero. -/
theorem gram_posDef_iff (x : (g : G) → I g → ℝ) :
    (gram x).PosDef ↔ 0 < scatter x := by
  have hps : (gram x).PosSemidef :=
    posSemidef_sum _ fun p _ => by simpa using posSemidef_vecMulVec_self_star (row x p)
  have hzero : cross x (fun _ _ => 0) = 0 := by simp [cross]
  have hc0 : coefficients x (fun _ _ => 0) 0 = 0 := by
    funext j
    cases j <;> simp [coefficients, average]
  have hr0 : response x (fun _ _ => 0) = 0 := by simp [response]
  constructor
  · intro hpos
    have hn : scatter x ≠ 0 := by
      intro hz
      have hnull : gram x *ᵥ coefficients x (fun _ _ => 0) 1 = 0 := by
        rw [← hr0, normal_equations_iff]
        exact ⟨rfl, by simp [coefficients, hz, hzero]⟩
      have he := hpos.mulVec_injective (hnull.trans (mulVec_zero _).symm)
      have := congrFun he none
      norm_num [coefficients] at this
    exact lt_of_le_of_ne (scatter_nonneg x) (Ne.symm hn)
  · intro hv
    apply hps.posDef_iff_mulVec_injective.mpr
    intro u v huv
    have hk : gram x *ᵥ (u - v) = response x (fun _ _ => 0) := by
      rw [mulVec_sub, huv, sub_self, hr0]
    have he := (normal_equations_unique x (fun _ _ => 0) (ne_of_gt hv) (u - v)).mp hk
    rw [hzero, zero_div, hc0] at he
    exact sub_eq_zero.mp he

/-- The inverse-matrix OLS estimator, including the refitted dummy coefficients,
is exactly the grouped scalar formula. -/
theorem inverse_estimate (x y : (g : G) → I g → ℝ) (hv : 0 < scatter x) :
    (gram x)⁻¹ *ᵥ response x y = coefficients x y (cross x y / scatter x) := by
  apply (normal_equations_unique x y (ne_of_gt hv) _).mp
  rw [mulVec_mulVec, mul_nonsing_inv _
    ((isUnit_iff_isUnit_det _).mp ((gram_posDef_iff x).mpr hv).isUnit), one_mulVec]

/-- The sign target on the actual inverse-matrix slope is the additive
within-group cross-scatter test, with nonsingularity derived separately. -/
theorem inverse_slope_nonpos_iff (x y : (g : G) → I g → ℝ)
    (hv : 0 < scatter x) :
    ((gram x)⁻¹ *ᵥ response x y) none ≤ 0 ↔ cross x y ≤ 0 := by
  rw [inverse_estimate x y hv]
  change cross x y / scatter x ≤ 0 ↔ cross x y ≤ 0
  exact (div_le_iff₀ hv).trans (by simp)

end Cslib.LeastSquares.FixedEffects.MatrixModel
