/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson
public import CslibFrontier.Foundations.Analysis.SpecialFunctions.GoemansWilliamsonDicut
import CslibFrontier.Foundations.Analysis.Normed.UnitSphere
import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Unoriented.Basic
import Mathlib.Geometry.Euclidean.Angle.Unoriented.TriangleInequality

/-!
# Goemans–Williamson random-hyperplane rounding for MAX-DICUT

This module formalizes the MAX-DICUT extension of Goemans–Williamson random-hyperplane rounding
[GoemansWilliamson1995, Section 7.3], reusing `hyperplaneSide`, `signVector`, and the Gaussian
expectation framework from `CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson`, together with
`Real.goemansWilliamsonDicutConstant` (`β > 0.79607`) and
`Real.goemansWilliamsonDicutConstant_mul_add_cos_le` from
`CslibFrontier.Foundations.Analysis.SpecialFunctions.GoemansWilliamsonDicut`.

Note on source typo: in display `(Q'')` of [GoemansWilliamson1995, Section 7.3, p. 1138], the
`d_{ijk}` term is misprinted as `1 - y_i y_j + y_i y_k + y_j y_k`; the surrounding prose on p. 1138,
relaxation `(P'')`, and Lemmas 7.3.1–7.3.2 on p. 1139 all use `1 + y_i y_j + y_i y_k + y_j y_k`,
which is the definition formalized here.

## Main definitions

* `Cslib.Algorithms.Lean.MaxDicut.tripleCutValue`,
  `Cslib.Algorithms.Lean.MaxDicut.tripleSdpValue`: the three-variable quadratic program `(Q'')` and
  its semidefinite relaxation `(P'')` (normalized by `1 / 4`).
* `Cslib.Algorithms.Lean.MaxDicut.dicutValue`,
  `Cslib.Algorithms.Lean.MaxDicut.dicutSdpValue`: the weighted directed-cut objective and its
  homogeneous `Option V` semidefinite relaxation.
* `Cslib.Algorithms.Lean.MaxDicut.dicutHyperplaneSet`,
  `Cslib.Algorithms.Lean.MaxDicut.liftDicutSet`: random-hyperplane rounding and `±u` vector lift
  for a directed cut `S : V → Bool`.
* `Cslib.Algorithms.Lean.MaxDicut.IsBalancedDigraph`: weighted outdegree equals weighted indegree at
  every vertex.

## Main results

* `integral_hyperplaneSide_all_eq`, `integral_hyperplaneSide_ne_and_eq`:
  [GoemansWilliamson1995, Lemma 7.3.1] triple agreement/disagreement probabilities under
  `stdGaussian`.
* `goemansWilliamsonDicutConstant_mul_add_inner_le`: vector form of
  [GoemansWilliamson1995, Lemma 7.3.2] via the spherical-triangle angle inequalities.
* `goemansWilliamsonDicutConstant_mul_tripleSdpValue_le_integral`: `(P'')` rounding guarantee.
* `goemansWilliamsonDicutConstant_mul_dicutSdpValue_le_integral`,
  `goemansWilliamsonDicutConstant_mul_sub_le_integral`,
  `goemansWilliamsonDicutConstant_mul_dicutValue_le_integral`: the `(β, ε)` and exact-optimum
  guarantees for weighted MAX-DICUT with `β > 0.79607`.
* `two_mul_dicutValue_eq_cutValue_of_isBalancedDigraph`,
  `two_mul_dicutSdpValue_eq_sdpValue_of_isBalancedDigraph`,
  `goemansWilliamsonConstant_mul_sub_le_integral_of_isBalancedDigraph`: the improved `(α, ε)`
  guarantee (`α > 0.87856`) on balanced (Eulerian) directed graphs.

## Limitations

As with `CslibFrontier.Algorithms.Lean.MaxCut.GoemansWilliamson`, this analyzes rounding of a given
vector solution under Mathlib's exact `stdGaussian`; polynomial-time SDP solving and
finite-precision sampling are not formalized.

## References

* [GoemansWilliamson1995]
-/

public section

open MeasureTheory ProbabilityTheory Real Set InnerProductGeometry
open scoped RealInnerProductSpace

namespace Cslib.Algorithms.Lean.MaxDicut

open Cslib.Algorithms.Lean.MaxCut

variable {ι V F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Lemma 7.3.1 & vector form of Lemma 7.3.2 -/

section TripleGaussian

omit [Fintype ι] in
/-- Triangle inequalities for three unit vectors place
`(arccos ⟪u, w⟫, arccos ⟪u, z⟫, arccos ⟪w, z⟫)` in `Real.DicutAngleSet`. -/
theorem dicutAngleSet_mem_of_unit {u w z : F} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    (arccos ⟪u, w⟫, arccos ⟪u, z⟫, arccos ⟪w, z⟫) ∈ Real.DicutAngleSet := by
  rw [← angle_eq_arccos_inner_of_norm_eq_one hu hw,
    ← angle_eq_arccos_inner_of_norm_eq_one hu hz,
    ← angle_eq_arccos_inner_of_norm_eq_one hw hz]
  have h1 := angle_le_angle_add_angle u z w
  have h2 := angle_le_angle_add_angle u w z
  have h3 := angle_le_angle_add_angle w u z
  have h4 := angle_le_angle_add_angle u (-z) w
  rw [angle_neg_right, angle_neg_left, angle_comm z w] at h4
  refine Real.mem_dicutAngleSet_iff.2 ⟨angle_nonneg _ _, angle_le_pi _ _,
    angle_nonneg _ _, angle_le_pi _ _, angle_nonneg _ _, angle_le_pi _ _, ?_, ?_, ?_, ?_⟩
  · linarith [angle_comm z w]
  · linarith [angle_comm w u, angle_comm w z]
  · linarith [angle_comm u w]
  · linarith

omit [Fintype ι] in
private theorem inner_bounds_of_unit {u w : F} (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) :
    -1 ≤ ⟪u, w⟫ ∧ ⟪u, w⟫ ≤ 1 := by
  have h := abs_real_inner_le_norm u w
  rwa [hu, hw, mul_one, abs_le] at h

/-- **Vector form of Lemma 7.3.2.** For any unit vectors `u`, `w`, `z`,
`(β / 4) · (1 + ⟪u, w⟫ + ⟪u, z⟫ + ⟪w, z⟫) ≤`
`1 - (arccos ⟪u, w⟫ + arccos ⟪u, z⟫ + arccos ⟪w, z⟫) / (2π)`. -/
theorem goemansWilliamsonDicutConstant_mul_add_inner_le {u w z : F}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    goemansWilliamsonDicutConstant / 4 * (1 + ⟪u, w⟫ + ⟪u, z⟫ + ⟪w, z⟫) ≤
      1 - (arccos ⟪u, w⟫ + arccos ⟪u, z⟫ + arccos ⟪w, z⟫) / (2 * π) := by
  have h := goemansWilliamsonDicutConstant_mul_add_cos_le (dicutAngleSet_mem_of_unit hu hw hz)
  obtain ⟨h1, h2⟩ := inner_bounds_of_unit hu hw
  obtain ⟨h3, h4⟩ := inner_bounds_of_unit hu hz
  obtain ⟨h5, h6⟩ := inner_bounds_of_unit hw hz
  rwa [cos_arccos h1 h2, cos_arccos h3 h4, cos_arccos h5 h6] at h

/-- Negated-first variant of Lemma 7.3.2:
`(β / 4) · (1 - ⟪u, w⟫ - ⟪u, z⟫ + ⟪w, z⟫) ≤`
`1 - (arccos ⟪-u, w⟫ + arccos ⟪-u, z⟫ + arccos ⟪w, z⟫) / (2π)`. -/
theorem goemansWilliamsonDicutConstant_mul_sub_add_inner_le {u w z : F}
    (hu : ‖u‖ = 1) (hw : ‖w‖ = 1) (hz : ‖z‖ = 1) :
    goemansWilliamsonDicutConstant / 4 * (1 - ⟪u, w⟫ - ⟪u, z⟫ + ⟪w, z⟫) ≤
      1 - (arccos ⟪-u, w⟫ + arccos ⟪-u, z⟫ + arccos ⟪w, z⟫) / (2 * π) := by
  have h := goemansWilliamsonDicutConstant_mul_add_inner_le (norm_neg u ▸ hu) hw hz
  simpa only [inner_neg_left, ← sub_eq_add_neg] using h

variable [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F]

omit [Fintype ι] [BorelSpace F] in
private theorem integral_bool_triple_identity (f g h : F → Bool)
    (hfg : MeasurableSet {r | f r = g r}) (hfh : MeasurableSet {r | f r = h r})
    (hgh : MeasurableSet {r | g r = h r}) :
    ∫ r : F, (if f r = g r ∧ g r = h r then (1 : ℝ) else 0) ∂stdGaussian F =
      ((∫ r : F, (if f r = g r then (1 : ℝ) else 0) ∂stdGaussian F) +
        (∫ r : F, (if f r = h r then (1 : ℝ) else 0) ∂stdGaussian F) +
        (∫ r : F, (if g r = h r then (1 : ℝ) else 0) ∂stdGaussian F) - 1) / 2 := by
  have hi₁ := integrable_ite_const (stdGaussian F) hfg 1
  have hi₂ := integrable_ite_const (stdGaussian F) hfh 1
  have hi₃ := integrable_ite_const (stdGaussian F) hgh 1
  have hi₁₂ : Integrable (fun r : F =>
      (if f r = g r then (1 : ℝ) else 0) + (if f r = h r then 1 else 0)) (stdGaussian F) :=
    hi₁.add hi₂
  have hi₁₂₃ : Integrable (fun r : F =>
      (if f r = g r then (1 : ℝ) else 0) + (if f r = h r then 1 else 0) +
        (if g r = h r then 1 else 0)) (stdGaussian F) := hi₁₂.add hi₃
  have hpoint : (fun r : F => if f r = g r ∧ g r = h r then (1 : ℝ) else 0) = fun r : F =>
      ((if f r = g r then (1 : ℝ) else 0) + (if f r = h r then (1 : ℝ) else 0) +
        (if g r = h r then (1 : ℝ) else 0) - 1) / 2 := by
    ext r
    cases f r <;> cases g r <;> cases h r <;> norm_num
  rw [hpoint, integral_div, integral_sub hi₁₂₃ (integrable_const 1), integral_add hi₁₂ hi₃,
    integral_add hi₁ hi₂, integral_const, probReal_univ, smul_eq_mul, mul_one]

omit [Fintype ι] in
/-- **Goemans–Williamson, Lemma 7.3.1.** Probability that a standard Gaussian hyperplane keeps
three unit vectors on the same side. -/
theorem integral_hyperplaneSide_all_eq {v : V → F} (hv : ∀ x, ‖v x‖ = 1) (i j k : V) :
    ∫ r : F, (if hyperplaneSide v r i = hyperplaneSide v r j ∧
        hyperplaneSide v r j = hyperplaneSide v r k then (1 : ℝ) else 0) ∂stdGaussian F =
      1 - (arccos ⟪v i, v j⟫ + arccos ⟪v i, v k⟫ + arccos ⟪v j, v k⟫) / (2 * π) := by
  rw [integral_bool_triple_identity (hyperplaneSide v · i) (hyperplaneSide v · j)
      (hyperplaneSide v · k) (measurableSet_hyperplaneSide_eq v i j)
      (measurableSet_hyperplaneSide_eq v i k) (measurableSet_hyperplaneSide_eq v j k),
    integral_hyperplaneSide_eq hv i j, integral_hyperplaneSide_eq hv i k,
    integral_hyperplaneSide_eq hv j k]
  ring

omit [Fintype ι] in
/-- **Goemans–Williamson, Lemma 7.3.1 (opposite-first variant).** Probability that a standard
Gaussian hyperplane puts `v i` on the opposite side from both `v j` and `v k`. -/
theorem integral_hyperplaneSide_ne_and_eq {v : V → F} (hv : ∀ x, ‖v x‖ = 1) (i j k : V) :
    ∫ r : F, (if hyperplaneSide v r i ≠ hyperplaneSide v r j ∧
        hyperplaneSide v r j = hyperplaneSide v r k then (1 : ℝ) else 0) ∂stdGaussian F =
      1 - (arccos ⟪-v i, v j⟫ + arccos ⟪-v i, v k⟫ + arccos ⟪v j, v k⟫) / (2 * π) := by
  have hne : ∀ a b : Bool, ((!a) = b) ↔ (a ≠ b) := fun a b => by cases a <;> cases b <;> decide
  have hm : ∀ a b : V, MeasurableSet {r : F | (!hyperplaneSide v r a) = hyperplaneSide v r b} :=
    fun a b => by simpa only [hne] using measurableSet_hyperplaneSide_ne v a b
  have hid := integral_bool_triple_identity (fun r => !hyperplaneSide v r i)
    (hyperplaneSide v · j) (hyperplaneSide v · k) (hm i j) (hm i k)
    (measurableSet_hyperplaneSide_eq v j k)
  simp only [hne] at hid
  rw [hid, integral_hyperplaneSide_ne hv i j, integral_hyperplaneSide_ne hv i k,
    integral_hyperplaneSide_eq hv j k, inner_neg_left, inner_neg_left, arccos_neg, arccos_neg]
  have hpi := pi_ne_zero
  field_simp
  ring

end TripleGaussian

/-! ### Three-variable quadratic program `(Q'')` and relaxation `(P'')` -/

/-- Objective of the quadratic program `(Q'')` [GoemansWilliamson1995, Section 7.3], normalized by
`1 / 4`: `c e` pays when `side i ≠ side j = side k`, and `d e` pays when `side i = side j = side k`.
-/
@[expose] noncomputable def tripleCutValue (triples : ι → V × V × V) (c d : ι → ℝ)
    (side : V → Bool) : ℝ :=
  ∑ e, match triples e with
    | (i, j, k) =>
      (if side i ≠ side j ∧ side j = side k then c e else 0) +
        (if side i = side j ∧ side j = side k then d e else 0)

/-- Objective of the semidefinite relaxation `(P'')` [GoemansWilliamson1995, Section 7.3],
normalized by `1 / 4`. -/
@[expose] noncomputable def tripleSdpValue (triples : ι → V × V × V) (c d : ι → ℝ)
    (v : V → F) : ℝ :=
  ∑ e, match triples e with
    | (i, j, k) =>
      c e * (1 - ⟪v i, v j⟫ - ⟪v i, v k⟫ + ⟪v j, v k⟫) / 4 +
        d e * (1 + ⟪v i, v j⟫ + ⟪v i, v k⟫ + ⟪v j, v k⟫) / 4

/-- At a cut's `±u` vector solution, `tripleSdpValue` equals `tripleCutValue`. -/
theorem tripleSdpValue_signVector (triples : ι → V × V × V) (c d : ι → ℝ) {u : F}
    (hu : ‖u‖ = 1) (side : V → Bool) :
    tripleSdpValue triples c d (signVector u side) = tripleCutValue triples c d side := by
  unfold tripleSdpValue tripleCutValue
  refine Finset.sum_congr rfl fun e _ => ?_
  rcases triples e with ⟨i, j, k⟩
  dsimp only
  unfold signVector
  cases side i <;> cases side j <;> cases side k <;>
    simp [inner_neg_left, inner_neg_right, hu] <;> ring

/-- If unit vectors `v` are within `ε` of optimal for `tripleSdpValue`, every Boolean cut has value
at most `tripleSdpValue triples c d v + ε`. -/
theorem tripleCutValue_le_tripleSdpValue_add {triples : ι → V × V × V} {c d : ι → ℝ} {v : V → F}
    {ε : ℝ} (hv : ∀ i, ‖v i‖ = 1)
    (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) →
      tripleSdpValue triples c d v' ≤ tripleSdpValue triples c d v + ε)
    (side : V → Bool) : tripleCutValue triples c d side ≤ tripleSdpValue triples c d v + ε := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    have := hopt v hv
    simp only [tripleCutValue, tripleSdpValue, Finset.univ_eq_empty, Finset.sum_empty] at this ⊢
    exact this
  | inr h =>
    obtain ⟨e⟩ := h
    rw [← tripleSdpValue_signVector triples c d (hv (triples e).1) side]
    exact hopt _ (norm_signVector (hv (triples e).1) side)

section TripleMeasurable

variable [MeasurableSpace F] [BorelSpace F]

private theorem measurableSet_triple_ne_eq (v : V → F) (i j k : V) :
    MeasurableSet {r : F | hyperplaneSide v r i ≠ hyperplaneSide v r j ∧
      hyperplaneSide v r j = hyperplaneSide v r k} :=
  (measurableSet_hyperplaneSide_ne v i j).inter (measurableSet_hyperplaneSide_eq v j k)

private theorem measurableSet_triple_all_eq (v : V → F) (i j k : V) :
    MeasurableSet {r : F | hyperplaneSide v r i = hyperplaneSide v r j ∧
      hyperplaneSide v r j = hyperplaneSide v r k} :=
  (measurableSet_hyperplaneSide_eq v i j).inter (measurableSet_hyperplaneSide_eq v j k)

/-- `tripleCutValue` along a random hyperplane is integrable under any finite measure. -/
theorem integrable_tripleCutValue_hyperplaneSide (triples : ι → V × V × V) (c d : ι → ℝ)
    (v : V → F) (μ : Measure F) [IsFiniteMeasure μ] :
    Integrable (fun r => tripleCutValue triples c d (hyperplaneSide v r)) μ := by
  unfold tripleCutValue
  exact integrable_finsetSum _ fun e _ =>
    (integrable_ite_const μ
      (measurableSet_triple_ne_eq v (triples e).1 (triples e).2.1 (triples e).2.2) (c e)).add
      (integrable_ite_const μ
        (measurableSet_triple_all_eq v (triples e).1 (triples e).2.1 (triples e).2.2) (d e))

variable [FiniteDimensional ℝ F]

/-- **Goemans–Williamson `(P'')` rounding bound.** For nonnegative weights `c` and `d` and unit
vectors `v`, the expected `tripleCutValue` under random-hyperplane rounding is at least
`β * tripleSdpValue triples c d v` [GoemansWilliamson1995, Section 7.3]. -/
theorem goemansWilliamsonDicutConstant_mul_tripleSdpValue_le_integral (triples : ι → V × V × V)
    {c d : ι → ℝ} (hc : ∀ e, 0 ≤ c e) (hd : ∀ e, 0 ≤ d e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1) :
    goemansWilliamsonDicutConstant * tripleSdpValue triples c d v ≤
      ∫ r, tripleCutValue triples c d (hyperplaneSide v r) ∂stdGaussian F := by
  unfold tripleCutValue
  have hint : ∀ e ∈ (Finset.univ : Finset ι), Integrable (fun r : F =>
      (if hyperplaneSide v r (triples e).1 ≠ hyperplaneSide v r (triples e).2.1 ∧
          hyperplaneSide v r (triples e).2.1 = hyperplaneSide v r (triples e).2.2 then c e else 0) +
        if hyperplaneSide v r (triples e).1 = hyperplaneSide v r (triples e).2.1 ∧
          hyperplaneSide v r (triples e).2.1 = hyperplaneSide v r (triples e).2.2 then d e else 0)
      (stdGaussian F) := fun e _ =>
    (integrable_ite_const (stdGaussian F) (measurableSet_triple_ne_eq v _ _ _) _).add
      (integrable_ite_const (stdGaussian F) (measurableSet_triple_all_eq v _ _ _) _)
  rw [integral_finsetSum _ hint, tripleSdpValue, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  rw [integral_add
    (integrable_ite_const (stdGaussian F) (measurableSet_triple_ne_eq v _ _ _) _)
    (integrable_ite_const (stdGaussian F) (measurableSet_triple_all_eq v _ _ _) _)]
  have hmul1 : (fun r : F => if hyperplaneSide v r (triples e).1 ≠
      hyperplaneSide v r (triples e).2.1 ∧
      hyperplaneSide v r (triples e).2.1 = hyperplaneSide v r (triples e).2.2 then c e else 0) =
      fun r : F => c e * (if hyperplaneSide v r (triples e).1 ≠
        hyperplaneSide v r (triples e).2.1 ∧
        hyperplaneSide v r (triples e).2.1 = hyperplaneSide v r (triples e).2.2
        then (1 : ℝ) else 0) := by
    ext r; split_ifs <;> ring
  have hmul2 : (fun r : F => if hyperplaneSide v r (triples e).1 =
      hyperplaneSide v r (triples e).2.1 ∧
      hyperplaneSide v r (triples e).2.1 = hyperplaneSide v r (triples e).2.2 then d e else 0) =
      fun r : F => d e * (if hyperplaneSide v r (triples e).1 =
        hyperplaneSide v r (triples e).2.1 ∧
        hyperplaneSide v r (triples e).2.1 = hyperplaneSide v r (triples e).2.2
        then (1 : ℝ) else 0) := by
    ext r; split_ifs <;> ring
  rw [hmul1, hmul2, integral_const_mul, integral_const_mul,
    integral_hyperplaneSide_ne_and_eq hv, integral_hyperplaneSide_all_eq hv]
  have h1 := mul_le_mul_of_nonneg_left
    (goemansWilliamsonDicutConstant_mul_sub_add_inner_le
      (hv (triples e).1) (hv (triples e).2.1) (hv (triples e).2.2)) (hc e)
  have h2 := mul_le_mul_of_nonneg_left
    (goemansWilliamsonDicutConstant_mul_add_inner_le
      (hv (triples e).1) (hv (triples e).2.1) (hv (triples e).2.2)) (hd e)
  calc goemansWilliamsonDicutConstant *
        (c e * (1 - ⟪v (triples e).1, v (triples e).2.1⟫ -
          ⟪v (triples e).1, v (triples e).2.2⟫ + ⟪v (triples e).2.1, v (triples e).2.2⟫) / 4 +
        d e * (1 + ⟪v (triples e).1, v (triples e).2.1⟫ +
          ⟪v (triples e).1, v (triples e).2.2⟫ + ⟪v (triples e).2.1, v (triples e).2.2⟫) / 4)
      = c e * (goemansWilliamsonDicutConstant / 4 * (1 - ⟪v (triples e).1, v (triples e).2.1⟫ -
          ⟪v (triples e).1, v (triples e).2.2⟫ + ⟪v (triples e).2.1, v (triples e).2.2⟫)) +
        d e * (goemansWilliamsonDicutConstant / 4 * (1 + ⟪v (triples e).1, v (triples e).2.1⟫ +
          ⟪v (triples e).1, v (triples e).2.2⟫ + ⟪v (triples e).2.1, v (triples e).2.2⟫)) := by
        ring
    _ ≤ c e * (1 - (arccos ⟪-v (triples e).1, v (triples e).2.1⟫ +
          arccos ⟪-v (triples e).1, v (triples e).2.2⟫ +
          arccos ⟪v (triples e).2.1, v (triples e).2.2⟫) / (2 * π)) +
        d e * (1 - (arccos ⟪v (triples e).1, v (triples e).2.1⟫ +
          arccos ⟪v (triples e).1, v (triples e).2.2⟫ +
          arccos ⟪v (triples e).2.1, v (triples e).2.2⟫) / (2 * π)) := add_le_add h1 h2

/-- The `(β, ε)` guarantee for `(Q'')`. -/
theorem goemansWilliamsonDicutConstant_mul_tripleCutValue_sub_le_integral
    (triples : ι → V × V × V) {c d : ι → ℝ} (hc : ∀ e, 0 ≤ c e) (hd : ∀ e, 0 ≤ d e)
    {v : V → F} (hv : ∀ i, ‖v i‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) →
      tripleSdpValue triples c d v' ≤ tripleSdpValue triples c d v + ε)
    (side : V → Bool) :
    goemansWilliamsonDicutConstant * (tripleCutValue triples c d side - ε) ≤
      ∫ r, tripleCutValue triples c d (hyperplaneSide v r) ∂stdGaussian F :=
  (mul_le_mul_of_nonneg_left (by linarith [tripleCutValue_le_tripleSdpValue_add hv hopt side])
    goemansWilliamsonDicutConstant_nonneg).trans
    (goemansWilliamsonDicutConstant_mul_tripleSdpValue_le_integral triples hc hd hv)

end TripleMeasurable

/-- Optimal unit vectors exist for `tripleSdpValue` in every nontrivial finite-dimensional `F`. -/
theorem exists_isMaxOn_tripleSdpValue [FiniteDimensional ℝ F] [Nontrivial F]
    (triples : ι → V × V × V) (c d : ι → ℝ) :
    ∃ v : V → F, (∀ i, ‖v i‖ = 1) ∧
      IsMaxOn (tripleSdpValue triples c d) {v' | ∀ i, ‖v' i‖ = 1} v :=
  NormedSpace.exists_isMaxOn_unitSphereFun (by unfold tripleSdpValue; fun_prop)

/-! ### Weighted MAX-DICUT -/

/-- The weight of the directed cut `S : V → Bool` (true on vertices in `S`) for directed arcs
`ends : ι → V × V` with weights `w`: sums `w e` over arcs with tail in `S` and head outside `S`. -/
@[expose] noncomputable def dicutValue (ends : ι → V × V) (w : ι → ℝ) (S : V → Bool) : ℝ :=
  ∑ e, if S (ends e).1 = true ∧ S (ends e).2 = false then w e else 0

/-- Semidefinite relaxation objective of weighted MAX-DICUT at unit vectors `v : Option V → F`
using truth-anchor `none : Option V` [GoemansWilliamson1995, Section 7.3]:
`∑ e, w e * (1 + ⟪v (some u), v none⟫ - ⟪v (some w), v none⟫ - ⟪v (some u), v (some w)⟫) / 4`. -/
@[expose] noncomputable def dicutSdpValue (ends : ι → V × V) (w : ι → ℝ) (v : Option V → F) :
    ℝ :=
  ∑ e, w e * (1 + ⟪v (some (ends e).1), v none⟫ - ⟪v (some (ends e).2), v none⟫ -
    ⟪v (some (ends e).1), v (some (ends e).2)⟫) / 4

/-- Directed cut produced by random-hyperplane rounding: vertex `x` lies in `S` iff
`hyperplaneSide v r (some x) = hyperplaneSide v r none` [GoemansWilliamson1995, Section 7.3]. -/
@[expose] noncomputable def dicutHyperplaneSet (v : Option V → F) (r : F) (x : V) : Bool :=
  hyperplaneSide v r (some x) == hyperplaneSide v r none

/-- Homogeneous `±u` vector lift of a directed cut `S : V → Bool`. -/
@[expose] def liftDicutSet (u : F) (S : V → Bool) : Option V → F :=
  signVector u fun o => o.elim true S

/-- Encoding of a directed arc `(u, w)` as the `(Q'')` triple `(some w, some u, none)`. -/
private def dicutTriple (ends : ι → V × V) (e : ι) :
    Option V × Option V × Option V :=
  (some (ends e).2, some (ends e).1, none)

private theorem dicutValue_eq_tripleCutValue (ends : ι → V × V) (w : ι → ℝ)
    (side : Option V → Bool) :
    dicutValue ends w (fun x => side (some x) == side none) =
      tripleCutValue (dicutTriple ends) w 0 side := by
  unfold dicutValue tripleCutValue dicutTriple
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [Pi.zero_apply, ite_self, add_zero]
  by_cases h1 : side (some (ends e).1) = true <;>
    by_cases h2 : side (some (ends e).2) = true <;>
    by_cases h3 : side none = true <;>
    simp [h1, h2, h3]

private theorem dicutSdpValue_eq_tripleSdpValue (ends : ι → V × V) (w : ι → ℝ)
    (v : Option V → F) :
    dicutSdpValue ends w v = tripleSdpValue (dicutTriple ends) w 0 v := by
  unfold dicutSdpValue tripleSdpValue dicutTriple
  refine Finset.sum_congr rfl fun e _ => ?_
  dsimp only
  rw [real_inner_comm (v (some (ends e).1)) (v (some (ends e).2))]
  simp only [Pi.zero_apply]
  ring

/-- At `liftDicutSet u S` (for `‖u‖ = 1`), `dicutSdpValue` equals `dicutValue`. -/
theorem dicutSdpValue_liftDicutSet (ends : ι → V × V) (w : ι → ℝ) {u : F} (hu : ‖u‖ = 1)
    (S : V → Bool) :
    dicutSdpValue ends w (liftDicutSet u S) = dicutValue ends w S := by
  rw [dicutSdpValue_eq_tripleSdpValue, liftDicutSet, tripleSdpValue_signVector _ _ _ hu,
    ← dicutValue_eq_tripleCutValue]
  congr 1

section DicutMeasurable

variable [MeasurableSpace F] [BorelSpace F]

/-- The directed-cut value under random-hyperplane rounding is integrable. -/
theorem integrable_dicutValue_dicutHyperplaneSet (ends : ι → V × V) (w : ι → ℝ)
    (v : Option V → F) (μ : Measure F) [IsFiniteMeasure μ] :
    Integrable (fun r => dicutValue ends w (dicutHyperplaneSet v r)) μ := by
  have heq : (fun r : F => dicutValue ends w (dicutHyperplaneSet v r)) =
      fun r => tripleCutValue (dicutTriple ends) w 0 (hyperplaneSide v r) := by
    ext r; exact dicutValue_eq_tripleCutValue ends w (hyperplaneSide v r)
  rw [heq]
  exact integrable_tripleCutValue_hyperplaneSide (dicutTriple ends) w 0 v μ

variable [FiniteDimensional ℝ F]

/-- **Goemans–Williamson MAX-DICUT relaxation bound.** For nonnegative arc weights `w` and unit
vectors `v : Option V → F`, the expected directed-cut weight under random-hyperplane rounding is at
least `β * dicutSdpValue ends w v` [GoemansWilliamson1995, Section 7.3], with `β > 0.79607`. -/
theorem goemansWilliamsonDicutConstant_mul_dicutSdpValue_le_integral (ends : ι → V × V)
    {w : ι → ℝ} (hw : ∀ e, 0 ≤ w e) {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) :
    goemansWilliamsonDicutConstant * dicutSdpValue ends w v ≤
      ∫ r, dicutValue ends w (dicutHyperplaneSet v r) ∂stdGaussian F := by
  rw [dicutSdpValue_eq_tripleSdpValue]
  have heq : (fun r : F => dicutValue ends w (dicutHyperplaneSet v r)) =
      fun r => tripleCutValue (dicutTriple ends) w 0 (hyperplaneSide v r) := by
    ext r; exact dicutValue_eq_tripleCutValue ends w (hyperplaneSide v r)
  rw [heq]
  exact goemansWilliamsonDicutConstant_mul_tripleSdpValue_le_integral (dicutTriple ends) hw
    (fun _ => le_rfl) hv

/-- **Goemans–Williamson MAX-DICUT `ε`-optimal guarantee.** If `v` are within `ε` of optimal for
`dicutSdpValue`, then for every directed cut `S`, the expected rounded weight is at least
`β * (dicutValue ends w S - ε)` [GoemansWilliamson1995, Section 7.3]. -/
theorem goemansWilliamsonDicutConstant_mul_sub_le_integral (ends : ι → V × V) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : Option V → F, (∀ o, ‖v' o‖ = 1) →
      dicutSdpValue ends w v' ≤ dicutSdpValue ends w v + ε)
    (S : V → Bool) :
    goemansWilliamsonDicutConstant * (dicutValue ends w S - ε) ≤
      ∫ r, dicutValue ends w (dicutHyperplaneSet v r) ∂stdGaussian F := by
  have h1 : dicutValue ends w S ≤ dicutSdpValue ends w v + ε := by
    rw [← dicutSdpValue_liftDicutSet ends w (hv none) S]
    exact hopt _ (norm_signVector (hv none) _)
  exact (mul_le_mul_of_nonneg_left (by linarith) goemansWilliamsonDicutConstant_nonneg).trans
    (goemansWilliamsonDicutConstant_mul_dicutSdpValue_le_integral ends hw hv)

/-- **Goemans–Williamson MAX-DICUT exact-optimum guarantee.** -/
theorem goemansWilliamsonDicutConstant_mul_dicutValue_le_integral (ends : ι → V × V) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1)
    (hopt : IsMaxOn (dicutSdpValue ends w) {v' | ∀ o, ‖v' o‖ = 1} v) (S : V → Bool) :
    goemansWilliamsonDicutConstant * dicutValue ends w S ≤
      ∫ r, dicutValue ends w (dicutHyperplaneSet v r) ∂stdGaussian F := by
  simpa only [sub_zero] using goemansWilliamsonDicutConstant_mul_sub_le_integral ends hw hv
    (ε := 0) (fun v' hv' => (add_zero (dicutSdpValue ends w v)).symm ▸ isMaxOn_iff.1 hopt v' hv') S

/-- Some hyperplane induces a directed cut achieving the `(β, ε)` MAX-DICUT guarantee against
every cut `S`. -/
theorem exists_forall_goemansWilliamsonDicutConstant_mul_sub_le (ends : ι → V × V) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : Option V → F, (∀ o, ‖v' o‖ = 1) →
      dicutSdpValue ends w v' ≤ dicutSdpValue ends w v + ε) :
    ∃ r : F, ∀ S : V → Bool,
      goemansWilliamsonDicutConstant * (dicutValue ends w S - ε) ≤
        dicutValue ends w (dicutHyperplaneSet v r) := by
  obtain ⟨r, hr⟩ := exists_integral_le
    (integrable_dicutValue_dicutHyperplaneSet ends w v (stdGaussian F))
  exact ⟨r, fun S =>
    (goemansWilliamsonDicutConstant_mul_sub_le_integral ends hw hv hopt S).trans hr⟩

end DicutMeasurable

/-- Optimal unit vectors exist for `dicutSdpValue` in every nontrivial finite-dimensional `F`. -/
theorem exists_isMaxOn_dicutSdpValue [FiniteDimensional ℝ F] [Nontrivial F]
    (ends : ι → V × V) (w : ι → ℝ) :
    ∃ v : Option V → F, (∀ o, ‖v o‖ = 1) ∧
      IsMaxOn (dicutSdpValue ends w) {v' | ∀ o, ‖v' o‖ = 1} v :=
  NormedSpace.exists_isMaxOn_unitSphereFun (by unfold dicutSdpValue; fun_prop)

/-! ### Balanced (Eulerian) directed graphs achieve `α > 0.87856` -/

/-- A weighted directed graph is balanced (Eulerian) when every vertex has equal weighted outdegree
and weighted indegree, equivalently `∑ e, w e * φ (ends e).1 = ∑ e, w e * φ (ends e).2` for every
potential `φ : V → ℝ` [GoemansWilliamson1995, Section 7.3, p. 1138]. -/
@[expose] def IsBalancedDigraph (ends : ι → V × V) (w : ι → ℝ) : Prop :=
  ∀ φ : V → ℝ, ∑ e, w e * φ (ends e).1 = ∑ e, w e * φ (ends e).2

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- Equal weighted outdegree and indegree at every vertex implies `IsBalancedDigraph`. -/
theorem isBalancedDigraph_of_outdeg_eq_indeg [DecidableEq V]
    {ends : ι → V × V} {w : ι → ℝ}
    (hdeg : ∀ x : V, (∑ e, if (ends e).1 = x then w e else 0) =
      ∑ e, if (ends e).2 = x then w e else 0) :
    IsBalancedDigraph ends w := by
  intro φ
  let V₀ : Finset V :=
    (Finset.univ.image fun e => (ends e).1) ∪ (Finset.univ.image fun e => (ends e).2)
  have h1 : ∀ e : ι, (ends e).1 ∈ V₀ := fun e =>
    Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
  have h2 : ∀ e : ι, (ends e).2 ∈ V₀ := fun e =>
    Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ e))
  have hL : ∑ e, w e * φ (ends e).1 =
      ∑ x ∈ V₀, φ x * ∑ e, if (ends e).1 = x then w e else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, h1 e, ↓reduceIte, mul_comm]
  have hR : ∑ e, w e * φ (ends e).2 =
      ∑ x ∈ V₀, φ x * ∑ e, if (ends e).2 = x then w e else 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [mul_ite, mul_zero, Finset.sum_ite_eq, h2 e, ↓reduceIte, mul_comm]
  rw [hL, hR]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [hdeg x]

omit [NormedAddCommGroup F] [InnerProductSpace ℝ F] in
/-- On a balanced digraph, `2 * dicutValue ends w S = cutValue ends w S`. -/
theorem two_mul_dicutValue_eq_cutValue_of_isBalancedDigraph {ends : ι → V × V} {w : ι → ℝ}
    (hbal : IsBalancedDigraph ends w) (S : V → Bool) :
    2 * dicutValue ends w S = cutValue ends w S := by
  have h0 : ∑ e, w e * (if S (ends e).1 then (1 : ℝ) else 0) =
      ∑ e, w e * (if S (ends e).2 then (1 : ℝ) else 0) :=
    hbal fun x => if S x then 1 else 0
  have hid : ∀ e : ι,
      2 * (if S (ends e).1 = true ∧ S (ends e).2 = false then w e else 0) -
        (if S (ends e).1 ≠ S (ends e).2 then w e else 0) =
        w e * (if S (ends e).1 then (1 : ℝ) else 0) -
          w e * (if S (ends e).2 then (1 : ℝ) else 0) := by
    intro e
    cases S (ends e).1 <;> cases S (ends e).2 <;> simp; all_goals ring
  have hsum : 2 * dicutValue ends w S - cutValue ends w S =
      (∑ e, w e * (if S (ends e).1 then (1 : ℝ) else 0)) -
        ∑ e, w e * (if S (ends e).2 then (1 : ℝ) else 0) := by
    unfold dicutValue cutValue
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun e _ => hid e
  linarith

/-- On a balanced digraph, `2 * dicutSdpValue ends w v` equals the MAX-CUT relaxation value of
`v ∘ some`. -/
theorem two_mul_dicutSdpValue_eq_sdpValue_of_isBalancedDigraph {ends : ι → V × V} {w : ι → ℝ}
    (hbal : IsBalancedDigraph ends w) (v : Option V → F) :
    2 * dicutSdpValue ends w v = sdpValue ends w (fun x => v (some x)) := by
  have h0 := hbal fun x => ⟪v (some x), v none⟫
  unfold dicutSdpValue sdpValue
  have hsub : 2 * ∑ e, w e * (1 + ⟪v (some (ends e).1), v none⟫ -
      ⟪v (some (ends e).2), v none⟫ - ⟪v (some (ends e).1), v (some (ends e).2)⟫) / 4 -
      ∑ e, w e * (1 - ⟪v (some (ends e).1), v (some (ends e).2)⟫) / 2 =
      (∑ e, w e * ⟪v (some (ends e).1), v none⟫ - ∑ e, w e * ⟪v (some (ends e).2), v none⟫) /
        2 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.sum_div]
    refine Finset.sum_congr rfl fun e _ => ?_
    ring
  linarith

variable [MeasurableSpace F] [BorelSpace F] [FiniteDimensional ℝ F] in
/-- **Goemans–Williamson balanced MAX-DICUT guarantee.** When `w` is balanced (equal weighted
outdegree and indegree at every vertex), random-hyperplane rounding achieves ratio `α > 0.87856`
[GoemansWilliamson1995, Section 7.3, p. 1138]. -/
theorem goemansWilliamsonConstant_mul_sub_le_integral_of_isBalancedDigraph (ends : ι → V × V)
    {w : ι → ℝ} (hw : ∀ e, 0 ≤ w e) (hbal : IsBalancedDigraph ends w)
    {v : Option V → F} (hv : ∀ o, ‖v o‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : Option V → F, (∀ o, ‖v' o‖ = 1) →
      dicutSdpValue ends w v' ≤ dicutSdpValue ends w v + ε)
    (S : V → Bool) :
    goemansWilliamsonConstant * (dicutValue ends w S - ε) ≤
      ∫ r, dicutValue ends w (dicutHyperplaneSet v r) ∂stdGaussian F := by
  have h1 : dicutValue ends w S ≤ dicutSdpValue ends w v + ε := by
    rw [← dicutSdpValue_liftDicutSet ends w (hv none) S]
    exact hopt _ (norm_signVector (hv none) _)
  have hcut : (fun r : F => dicutValue ends w (dicutHyperplaneSet v r)) =
      fun r => cutValue ends w (hyperplaneSide (fun x => v (some x)) r) / 2 := by
    ext r
    have heq : dicutValue ends w (dicutHyperplaneSet v r) =
        cutValue ends w (dicutHyperplaneSet v r) / 2 := by
      linarith [two_mul_dicutValue_eq_cutValue_of_isBalancedDigraph hbal (dicutHyperplaneSet v r)]
    have hinv : cutValue ends w (dicutHyperplaneSet v r) =
        cutValue ends w (hyperplaneSide (fun x => v (some x)) r) := by
      unfold cutValue dicutHyperplaneSet hyperplaneSide
      refine Finset.sum_congr rfl fun e _ => ?_
      cases decide (0 ≤ ⟪v (some (ends e).1), r⟫) <;>
        cases decide (0 ≤ ⟪v (some (ends e).2), r⟫) <;>
        cases decide (0 ≤ ⟪v none, r⟫) <;> simp
    rw [heq, hinv]
  rw [hcut, integral_div]
  have hsdp := goemansWilliamsonConstant_mul_sdpValue_le_integral ends hw
    (v := fun x => v (some x)) (fun x => hv (some x))
  rw [← two_mul_dicutSdpValue_eq_sdpValue_of_isBalancedDigraph hbal v] at hsdp
  have hbound : goemansWilliamsonConstant * dicutSdpValue ends w v ≤
      (∫ r, cutValue ends w (hyperplaneSide (fun x => v (some x)) r) ∂stdGaussian F) / 2 := by
    linarith
  exact (mul_le_mul_of_nonneg_left (by linarith) goemansWilliamsonConstant_nonneg).trans hbound

end Cslib.Algorithms.Lean.MaxDicut
