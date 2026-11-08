/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Geometry/Euclidean/Angle/Unoriented/`)

public import Complexity.Init
public import Complexity.Foundations.Geometry.Euclidean.Angle.Unoriented.Basic
public import Mathlib.Data.Finset.Prod
import Complexity.Foundations.Analysis.InnerProductSpace.Basic
import Complexity.Foundations.Analysis.SpecialFunctions.Arccos
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Angles within a spherical cap

Fix a unit vector `x` of a real inner product space and `κ ≥ 0`. The unit vectors `y` with
`κ ≤ ⟪y, x⟫` form the spherical cap of angular radius `arccos κ` around `x`. Vectors in such a
cap are close to each other:

* `InnerProductGeometry.two_mul_sq_sub_one_le_inner`: two of them have inner product at least
  `2 κ ^ 2 - 1 = cos (2 arccos κ)`, by the triangle inequality for angles.
* `InnerProductGeometry.le_sum_offDiag_inner`: `n` of them have inner products summing, over the
  ordered pairs of distinct indices, to at least `n ^ 2 κ ^ 2 - n`. Indeed their sum `S` has
  `‖S‖ ≥ ⟪S, x⟫ ≥ n κ`, and `‖S‖ ^ 2` is `n` plus that sum (`norm_sum_sq_real`).
* `InnerProductGeometry.sum_offDiag_angle_le`: if moreover `κ ≥ √2 / 2`, these inner products lie
  in `[0, 1]`, where `arccos` is concave, so by Jensen's inequality the angles over the
  `n (n - 1)` ordered pairs sum to at most `n (n - 1) arccos ((n κ ^ 2 - 1) / (n - 1))`.
* `InnerProductGeometry.card_mul_sq_sub_le_of_le_inner`: conversely, a cap holds few almost
  orthogonal vectors. If `n` vectors of norm at most `1` have pairwise inner products at most
  `γ ≤ 1` and inner products at least `κ ≥ 0` with a vector of norm at most `1`, then
  `n (κ ^ 2 - γ) ≤ 1 - γ`. The same holds when only the absolute values `|⟪y i, x⟫| ≥ κ` and
  `|⟪y i, y j⟫| ≤ γ` are bounded (`InnerProductGeometry.card_mul_sq_sub_le_of_le_abs_inner`), by
  flipping signs. This is the counting step of the statistical query lower bounds of Blum, Furst,
  Jackson, Kearns, Mansour and Rudich in the form of [Szörényi][Szorenyi2009].

The last bound beats the pairwise bound `2 arccos κ` on every angle: for `n = 3` the average
inner product is at least `(3 κ ^ 2 - 1) / 2`, which exceeds `2 κ ^ 2 - 1` by `(1 - κ ^ 2) / 2`.

## Main results

* `InnerProductGeometry.two_mul_sq_sub_one_le_inner`: the pairwise bound in a cap.
* `InnerProductGeometry.le_sum_offDiag_inner`: the bound on the sum of the pairwise inner
  products in a cap.
* `InnerProductGeometry.sum_offDiag_angle_le`: the bound on the sum of the pairwise angles in a
  cap.
* `InnerProductGeometry.card_mul_sq_sub_le_of_le_inner`,
  `InnerProductGeometry.card_mul_sq_sub_le_of_le_abs_inner`: the number of almost orthogonal
  vectors in a cap.

## References

* [B. Szörényi, *Characterizing statistical query learning: simplified notions and
  proofs*][Szorenyi2009]
-/

@[expose] public section

open Real Finset
open scoped RealInnerProductSpace

variable {V ι : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

namespace InnerProductGeometry

/-- **Two vectors in a cap.** Two unit vectors whose inner products with a unit vector `x` are at
least `κ ≥ 0` have inner product at least `2 κ ^ 2 - 1`: each makes an angle at most `arccos κ`
with `x`, so they make an angle at most `2 arccos κ ≤ π` with each other. -/
theorem two_mul_sq_sub_one_le_inner {x y z : V} (hx : ‖x‖ = 1) (hy : ‖y‖ = 1) (hz : ‖z‖ = 1)
    {κ : ℝ} (hκ : 0 ≤ κ) (hyx : κ ≤ ⟪y, x⟫) (hzx : κ ≤ ⟪z, x⟫) :
    2 * κ ^ 2 - 1 ≤ ⟪y, z⟫ := by
  have hκ1 : κ ≤ 1 := hyx.trans ((real_inner_le_norm y x).trans_eq (by rw [hy, hx, one_mul]))
  have hyx' : angle y x ≤ arccos κ := by
    rw [angle_eq_arccos_inner_of_norm_eq_one hy hx]
    exact arccos_le_arccos hyx
  have hxz' : angle x z ≤ arccos κ := by
    rw [angle_comm, angle_eq_arccos_inner_of_norm_eq_one hz hx]
    exact arccos_le_arccos hzx
  have hπ : 2 * arccos κ ≤ π := by linarith [arccos_le_pi_div_two.2 hκ]
  rw [inner_eq_cos_angle_of_norm_eq_one hy hz]
  calc 2 * κ ^ 2 - 1 = cos (2 * arccos κ) := by
        rw [cos_two_mul, cos_arccos (by linarith) hκ1]
    _ ≤ cos (angle y z) := cos_le_cos_of_nonneg_of_le_pi (angle_nonneg y z) hπ
        ((angle_le_angle_add_angle y x z).trans (by linarith))

/-- **Many short vectors in a cap.** If `n` vectors of norm at most `1` have inner products at
least `κ ≥ 0` with a vector of norm at most `1`, their inner products over the ordered pairs of
distinct indices sum to at least `n ^ 2 κ ^ 2 - n`. -/
theorem le_sum_offDiag_inner_of_norm_le {x : V} (hx : ‖x‖ ≤ 1) {s : Finset ι} {y : ι → V}
    (hy : ∀ i ∈ s, ‖y i‖ ≤ 1) {κ : ℝ} (hκ : 0 ≤ κ) (hyx : ∀ i ∈ s, κ ≤ ⟪y i, x⟫) :
    (#s : ℝ) ^ 2 * κ ^ 2 - #s ≤ ∑ p ∈ s.offDiag, ⟪y p.1, y p.2⟫ := by
  have hlin : #s * κ ≤ ‖∑ i ∈ s, y i‖ :=
    calc #s * κ ≤ ∑ i ∈ s, ⟪y i, x⟫ := by simpa using card_nsmul_le_sum s _ κ hyx
      _ = ⟪∑ i ∈ s, y i, x⟫ := (sum_inner s y x).symm
      _ ≤ ‖∑ i ∈ s, y i‖ * ‖x‖ := real_inner_le_norm _ x
      _ ≤ ‖∑ i ∈ s, y i‖ := mul_le_of_le_one_right (norm_nonneg _) hx
  have hn : ∑ i ∈ s, ‖y i‖ ^ 2 ≤ #s :=
    calc ∑ i ∈ s, ‖y i‖ ^ 2 ≤ ∑ _i ∈ s, (1 : ℝ) :=
          sum_le_sum fun i hi => pow_le_one₀ (norm_nonneg _) (hy i hi)
      _ = #s := by rw [sum_const, nsmul_one]
  have hsq := norm_sum_sq_real s y
  have h0 : 0 ≤ (#s : ℝ) * κ := by positivity
  nlinarith [mul_le_mul hlin hlin h0 (h0.trans hlin)]

/-- **Many vectors in a cap.** If `n` unit vectors have inner products at least `κ ≥ 0` with a
unit vector, their inner products over the ordered pairs of distinct indices sum to at least
`n ^ 2 κ ^ 2 - n`. -/
theorem le_sum_offDiag_inner {x : V} (hx : ‖x‖ = 1) {s : Finset ι} {y : ι → V}
    (hy : ∀ i ∈ s, ‖y i‖ = 1) {κ : ℝ} (hκ : 0 ≤ κ) (hyx : ∀ i ∈ s, κ ≤ ⟪y i, x⟫) :
    (#s : ℝ) ^ 2 * κ ^ 2 - #s ≤ ∑ p ∈ s.offDiag, ⟪y p.1, y p.2⟫ :=
  le_sum_offDiag_inner_of_norm_le hx.le (fun i hi => (hy i hi).le) hκ hyx

/-- **Few almost orthogonal vectors in a cap.** If `n` vectors of norm at most `1` have pairwise
inner products at most `γ ≤ 1` and inner products at least `κ ≥ 0` with a vector of norm at most
`1`, then `n (κ ^ 2 - γ) ≤ 1 - γ`: when `γ < κ ^ 2`, at most `(1 - γ) / (κ ^ 2 - γ)` of them fit
in the cap. -/
theorem card_mul_sq_sub_le_of_le_inner {x : V} (hx : ‖x‖ ≤ 1) {s : Finset ι} {y : ι → V}
    (hy : ∀ i ∈ s, ‖y i‖ ≤ 1) {κ γ : ℝ} (hκ : 0 ≤ κ) (hγ : γ ≤ 1)
    (hyx : ∀ i ∈ s, κ ≤ ⟪y i, x⟫) (hyy : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ⟪y i, y j⟫ ≤ γ) :
    (#s : ℝ) * (κ ^ 2 - γ) ≤ 1 - γ := by
  have hsum := le_sum_offDiag_inner_of_norm_le hx hy hκ hyx
  have hoff : ∑ p ∈ s.offDiag, ⟪y p.1, y p.2⟫ ≤ #s * (#s - 1) * γ :=
    calc ∑ p ∈ s.offDiag, ⟪y p.1, y p.2⟫ ≤ ∑ _p ∈ s.offDiag, γ :=
          sum_le_sum fun p hp => by
            obtain ⟨h1, h2, h3⟩ := mem_offDiag.1 hp
            exact hyy _ h1 _ h2 h3
      _ = #s * (#s - 1) * γ := by
          rw [sum_const, nsmul_eq_mul, offDiag_card, Nat.cast_sub (Nat.le_mul_self _),
            Nat.cast_mul]
          ring
  rcases Nat.eq_zero_or_pos #s with hs | hs
  · rw [hs, Nat.cast_zero, zero_mul]
    linarith
  · have hs' : (0 : ℝ) < #s := by exact_mod_cast hs
    refine le_of_mul_le_mul_left ?_ hs'
    nlinarith

/-- **Few almost orthogonal vectors in a double cap.** If `n` vectors of norm at most `1` have
pairwise inner products of absolute value at most `γ ≤ 1` and inner products of absolute value at
least `κ ≥ 0` with a vector of norm at most `1`, then `n (κ ^ 2 - γ) ≤ 1 - γ`. -/
theorem card_mul_sq_sub_le_of_le_abs_inner {x : V} (hx : ‖x‖ ≤ 1) {s : Finset ι} {y : ι → V}
    (hy : ∀ i ∈ s, ‖y i‖ ≤ 1) {κ γ : ℝ} (hκ : 0 ≤ κ) (hγ : γ ≤ 1)
    (hyx : ∀ i ∈ s, κ ≤ |⟪y i, x⟫|) (hyy : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → |⟪y i, y j⟫| ≤ γ) :
    (#s : ℝ) * (κ ^ 2 - γ) ≤ 1 - γ := by
  -- Flip each vector to the side of `x`.
  set σ : ι → ℝ := fun i => if 0 ≤ ⟪y i, x⟫ then 1 else -1 with hσ
  have hσabs : ∀ i, |σ i| = 1 := fun i => by
    simp only [hσ]
    split_ifs <;> simp
  refine card_mul_sq_sub_le_of_le_inner (y := fun i => σ i • y i) hx (fun i hi => ?_) hκ hγ
    (fun i hi => ?_) (fun i hi j hj hij => ?_)
  · rw [norm_smul, Real.norm_eq_abs, hσabs, one_mul]
    exact hy i hi
  · rw [real_inner_smul_left]
    simp only [hσ]
    split_ifs with h
    · rw [one_mul]
      exact (abs_of_nonneg h) ▸ hyx i hi
    · rw [neg_one_mul]
      exact (abs_of_neg (not_le.1 h)) ▸ hyx i hi
  · rw [real_inner_smul_left, real_inner_smul_right]
    calc σ i * (σ j * ⟪y i, y j⟫) ≤ |σ i * (σ j * ⟪y i, y j⟫)| := le_abs_self _
      _ = |⟪y i, y j⟫| := by rw [abs_mul, abs_mul, hσabs, hσabs, one_mul, one_mul]
      _ ≤ γ := hyy i hi j hj hij

/-- **Angles in a cap.** If `n` unit vectors have inner products at least `κ ≥ √2 / 2` with a
unit vector, the angles between them over the `n (n - 1)` ordered pairs of distinct indices sum
to at most `n (n - 1) arccos ((n κ ^ 2 - 1) / (n - 1))`. -/
theorem sum_offDiag_angle_le {x : V} (hx : ‖x‖ = 1) {s : Finset ι} {y : ι → V}
    (hy : ∀ i ∈ s, ‖y i‖ = 1) {κ : ℝ} (hκ : √2 / 2 ≤ κ) (hyx : ∀ i ∈ s, κ ≤ ⟪y i, x⟫) :
    ∑ p ∈ s.offDiag, angle (y p.1) (y p.2) ≤
      #s * (#s - 1) * arccos ((#s * κ ^ 2 - 1) / (#s - 1)) := by
  have hκ0 : 0 ≤ κ := (by positivity : (0 : ℝ) ≤ √2 / 2).trans hκ
  have hκ2 : 1 ≤ 2 * κ ^ 2 := by
    have h := mul_le_mul hκ hκ (by positivity) hκ0
    rw [div_mul_div_comm, mul_self_sqrt zero_le_two] at h
    nlinarith
  have hoff : ∀ p ∈ s.offDiag, ‖y p.1‖ = 1 ∧ ‖y p.2‖ = 1 ∧ κ ≤ ⟪y p.1, x⟫ ∧ κ ≤ ⟪y p.2, x⟫ :=
    fun p hp => by
      obtain ⟨h1, h2, -⟩ := mem_offDiag.1 hp
      exact ⟨hy _ h1, hy _ h2, hyx _ h1, hyx _ h2⟩
  rw [sum_congr rfl fun p hp => angle_eq_arccos_inner_of_norm_eq_one (hoff p hp).1
    (hoff p hp).2.1]
  rcases lt_or_ge #s 2 with hs | hs
  · -- At most one vector: there are no pairs.
    have : s.offDiag = ∅ := by
      rw [← card_eq_zero, offDiag_card]
      interval_cases #s <;> rfl
    have hs' : (#s : ℝ) * (#s - 1) = 0 := by
      interval_cases #s <;> simp
    rw [this, sum_empty, hs', zero_mul]
  have hs1 : (0 : ℝ) < #s - 1 := by
    have : (2 : ℝ) ≤ #s := by exact_mod_cast hs
    linarith
  have hcard : (#s.offDiag : ℝ) = #s * (#s - 1) := by
    rw [offDiag_card, Nat.cast_sub (Nat.le_mul_self _), Nat.cast_mul]
    ring
  rw [← hcard]
  refine sum_arccos_le_card_mul_arccos _ (fun p hp => ⟨?_, ?_⟩) ?_
  · obtain ⟨h1, h2, h3, h4⟩ := hoff p hp
    linarith [two_mul_sq_sub_one_le_inner hx h1 h2 hκ0 h3 h4]
  · obtain ⟨h1, h2, -⟩ := hoff p hp
    exact (real_inner_le_norm _ _).trans_eq (by rw [h1, h2, one_mul])
  · rw [hcard, mul_assoc, mul_div_cancel₀ _ hs1.ne']
    linarith [le_sum_offDiag_inner hx hy hκ0 hyx]

end InnerProductGeometry
