/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Foundations.Analysis.SpecialFunctions.GoemansWilliamson
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import Complexity.Foundations.MeasureTheory.Constructions.BorelSpace.Order
import Complexity.Foundations.Probability.Gaussian.Sheppard
import Mathlib.MeasureTheory.Integral.Average

/-!
# Goemans–Williamson random-hyperplane rounding for MAX-CUT

This module formalizes the analysis of the Goemans–Williamson algorithm for weighted maximum cut
[GoemansWilliamson1995, Sections 2 and 3]: given unit vectors that are optimal, or `ε`-optimal,
for the semidefinite relaxation of MAX-CUT, cutting along a random hyperplane through the origin
gives a cut whose expected weight is at least `α` times the weight of every cut, minus `α ε`,
where `α = Real.goemansWilliamsonConstant > 0.87856`.

## Model

A weighted multigraph is a finite type `ι` of edges, endpoints `ends : ι → V × V` and real weights
`w : ι → ℝ`. A cut is a side assignment `side : V → Bool`; its weight `cutValue ends w side` is the
total weight of the edges whose endpoints lie on different sides. Self-loops never cross and
parallel edges add their weights. The semidefinite relaxation assigns a vector `v i` of a real
inner product space `F` to each vertex; its objective is
`sdpValue ends w v = ∑ e, w e * (1 - ⟪v (ends e).1, v (ends e).2⟫) / 2`, maximized over
assignments of unit vectors. This is the relaxation (P) of [GoemansWilliamson1995, Section 2],
whose sum over pairs `i < j` is a sum over edges here. For a unit vector `u`, the assignment
`signVector u side` sends the two sides of a cut to `u` and `-u`; its objective is the weight of
the cut (`sdpValue_signVector`), so the relaxation's optimum is at least the maximum cut.

## Algorithm and source mapping

Random-hyperplane rounding draws a standard Gaussian vector `r` of `F` and puts vertex `i` on the
side `hyperplaneSide v r i = decide (0 ≤ ⟪v i, r⟫)`. The source draws `r` uniformly from the unit
sphere and uses `S = {i | v i · r ≥ 0}`; the side of each vertex depends only on the direction of
`r`, and the standard Gaussian is rotation invariant, so the two models agree. Here the rounding
is analyzed under Mathlib's exact `ProbabilityTheory.stdGaussian` on a finite-dimensional `F`, as
in the source, and the expected weight of the rounded cut is the integral
`∫ r, cutValue ends w (hyperplaneSide v r) ∂stdGaussian F`.

* Lemma 3.2 of the source, that a random hyperplane separates unit vectors `u` and `v` with
  probability `arccos ⟪u, v⟫ / π`, is Sheppard's formula
  `ProbabilityTheory.measureReal_stdGaussian_zero_mem_uIoc_eq_arccos`.
* Theorem 3.1 is `integral_cutValue_hyperplaneSide`.
* Theorem 3.3 is `goemansWilliamsonConstant_mul_sdpValue_le_integral`, from Lemma 3.4
  (`Real.goemansWilliamsonConstant_mul_le_arccos`).
* The approximation guarantee against the maximum cut, which the source draws from Theorem 3.3 and
  the fact that the relaxation's optimum is at least the maximum cut, is
  `goemansWilliamsonConstant_mul_sub_le_integral` for `ε`-optimal vectors and
  `goemansWilliamsonConstant_mul_cutValue_le_integral` for optimal ones. With
  `Real.lt_goemansWilliamsonConstant` (Lemma 3.5), the ratio exceeds `0.87856`.

An optimal assignment of unit vectors exists in every nontrivial `F`
(`exists_isMaxOn_sdpValue`): the objective depends on finitely many coordinates and the
assignments of unit vectors form a compact set. For the guarantee, `F` may have any dimension;
the source uses dimension `n`, the number of vertices, where an optimal solution of the
semidefinite program is a Gram matrix of vectors.

The bridge to the weighted `Cslib.Complexity.MaxCut` problem and its
`Cslib.Complexity.MaxCut.cutWeight` is in
`Complexity.Algorithms.Lean.MaxCut.GoemansWilliamsonCutWeight`, so that this module does not
depend on the machine-level complexity of `MaxCut`.

## Limitations

The theorem analyzes the rounding of a given vector solution under an exact Gaussian. Solving the
semidefinite program to precision `ε` in polynomial time, a finite-precision or `ProbComp`
realization of the Gaussian sample, the tightness of the analysis (the integrality gap of Feige and
Schechtman, Karloff's examples), the extensions to MAX-2SAT and MAX-DICUT, and derandomization are
not formalized.

## Main definitions

* `Cslib.Algorithms.Lean.MaxCut.cutValue`: the weight of a cut.
* `Cslib.Algorithms.Lean.MaxCut.sdpValue`: the objective of the semidefinite relaxation.
* `Cslib.Algorithms.Lean.MaxCut.hyperplaneSide`: the cut along the hyperplane orthogonal to `r`.
* `Cslib.Algorithms.Lean.MaxCut.signVector`: the vector solution of a cut.

## Main results

* `integral_cutValue_hyperplaneSide`: the expected weight of the rounded cut is
  `∑ e, w e * arccos ⟪v (ends e).1, v (ends e).2⟫ / π` [GoemansWilliamson1995, Theorem 3.1].
* `goemansWilliamsonConstant_mul_sdpValue_le_integral`: it is at least `α` times the relaxation's
  objective [GoemansWilliamson1995, Theorem 3.3].
* `sdpValue_signVector`, `cutValue_le_sdpValue_add`: the relaxation's objective at a cut's vector
  solution is the cut's weight, so `ε`-optimal vectors have objective at least every cut's weight
  minus `ε`.
* `goemansWilliamsonConstant_mul_sub_le_integral`,
  `goemansWilliamsonConstant_mul_cutValue_le_integral`: the Goemans–Williamson guarantee against
  every cut, hence against the maximum cut.
* `exists_forall_goemansWilliamsonConstant_mul_sub_le`: some hyperplane cut achieves the
  guarantee.
* `exists_isMaxOn_sdpValue`: the relaxation has an optimal solution.

## References

* [GoemansWilliamson1995]
-/

public section

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

namespace Cslib.Algorithms.Lean.MaxCut

variable {ι V F : Type*} [Fintype ι] [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-! ### Cuts, the relaxation and rounding -/

/-- The weight of the cut `side` of the weighted multigraph with endpoints `ends` and weights `w`:
the total weight of the edges whose endpoints lie on different sides. -/
@[expose] noncomputable def cutValue (ends : ι → V × V) (w : ι → ℝ) (side : V → Bool) : ℝ :=
  ∑ e, if side (ends e).1 ≠ side (ends e).2 then w e else 0

/-- The objective `∑ e, w e * (1 - ⟪v (ends e).1, v (ends e).2⟫) / 2` of the semidefinite
relaxation of MAX-CUT at the vector assignment `v` [GoemansWilliamson1995, Section 2]. -/
@[expose] noncomputable def sdpValue (ends : ι → V × V) (w : ι → ℝ) (v : V → F) : ℝ :=
  ∑ e, w e * (1 - ⟪v (ends e).1, v (ends e).2⟫) / 2

/-- Random-hyperplane rounding: vertex `i` goes on side `true` when `⟪v i, r⟫ ≥ 0`, so the cut is
`S = {i | v i · r ≥ 0}` of [GoemansWilliamson1995, Section 2]. -/
@[expose] noncomputable def hyperplaneSide (v : V → F) (r : F) (i : V) : Bool :=
  decide (0 ≤ ⟪v i, r⟫)

/-- The vector solution of the cut `side`: the vertices on side `true` get `u` and the others
`-u`. -/
@[expose] def signVector (u : F) (side : V → Bool) (i : V) : F :=
  if side i then u else -u

/-- Two vertices are separated by the hyperplane orthogonal to `r` exactly when `0` lies between
`⟪v i, r⟫` and `⟪v j, r⟫`, the event of Sheppard's formula. -/
theorem hyperplaneSide_ne_iff (v : V → F) (r : F) (i j : V) :
    hyperplaneSide v r i ≠ hyperplaneSide v r j ↔ (0 : ℝ) ∈ Ι ⟪v i, r⟫ ⟪v j, r⟫ := by
  simp only [hyperplaneSide, ne_eq, decide_eq_decide, mem_uIoc]
  constructor
  · intro h
    by_cases hi : 0 ≤ ⟪v i, r⟫
    · exact Or.inr ⟨lt_of_not_ge fun hj => h ⟨fun _ => hj, fun _ => hi⟩, hi⟩
    · exact Or.inl ⟨lt_of_not_ge hi, not_lt.1 fun hj => h ⟨fun h' => (hi h').elim,
        fun h' => (not_le.2 hj h').elim⟩⟩
  · rintro (⟨hi, hj⟩ | ⟨hj, hi⟩) h
    · exact (not_le.2 hi) (h.2 hj)
    · exact (not_le.2 hj) (h.1 hi)

omit [InnerProductSpace ℝ F] in
/-- Each vector of a cut's vector solution is a unit vector when `u` is. -/
theorem norm_signVector {u : F} (hu : ‖u‖ = 1) (side : V → Bool) (i : V) :
    ‖signVector u side i‖ = 1 := by
  unfold signVector
  split <;> simp [hu]

/-- **The relaxation's objective at a cut's vector solution is the cut's weight.** -/
theorem sdpValue_signVector (ends : ι → V × V) (w : ι → ℝ) {u : F} (hu : ‖u‖ = 1)
    (side : V → Bool) : sdpValue ends w (signVector u side) = cutValue ends w side := by
  unfold sdpValue cutValue
  refine Finset.sum_congr rfl fun e _ => ?_
  have huu : ⟪u, u⟫ = 1 := by rw [real_inner_self_eq_norm_sq, hu, one_pow]
  unfold signVector
  cases side (ends e).1 <;> cases side (ends e).2 <;>
    simp only [Bool.false_eq_true, Bool.true_eq_false, ↓reduceIte, ne_eq, not_true_eq_false,
      not_false_eq_true, inner_neg_left, inner_neg_right, neg_neg, huu] <;> ring

/-- **`ε`-optimal vectors beat every cut up to `ε`.** If the unit vectors `v` are within `ε` of
optimal for the relaxation, then their objective is at least the weight of every cut minus `ε`.
This needs no assumption on `F` beyond containing the unit vectors `v`. -/
theorem cutValue_le_sdpValue_add {ends : ι → V × V} {w : ι → ℝ} {v : V → F} {ε : ℝ}
    (hv : ∀ i, ‖v i‖ = 1)
    (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) → sdpValue ends w v' ≤ sdpValue ends w v + ε)
    (side : V → Bool) : cutValue ends w side ≤ sdpValue ends w v + ε := by
  cases isEmpty_or_nonempty ι with
  | inl _ =>
    have := hopt v hv
    simp only [cutValue, sdpValue, Finset.univ_eq_empty, Finset.sum_empty] at this ⊢
    exact this
  | inr h =>
    obtain ⟨e⟩ := h
    rw [← sdpValue_signVector ends w (hv (ends e).1) side]
    exact hopt _ (norm_signVector (hv (ends e).1) side)

/-! ### The expected weight of the rounded cut -/

/-- The weight of the rounded cut, as a sum of weighted indicators of separation events. -/
private theorem cutValue_hyperplaneSide_eq_sum_indicator (ends : ι → V × V) (w : ι → ℝ)
    (v : V → F) (r : F) :
    cutValue ends w (hyperplaneSide v r) = ∑ e,
      {r : F | hyperplaneSide v r (ends e).1 ≠ hyperplaneSide v r (ends e).2}.indicator
        (fun _ => w e) r := by
  unfold cutValue
  refine Finset.sum_congr rfl fun e _ => ?_
  simp only [indicator, mem_ofPred_eq]

variable [MeasurableSpace F] [BorelSpace F]

/-- The event that the hyperplane orthogonal to `r` separates two vertices is measurable. -/
theorem measurableSet_hyperplaneSide_ne (v : V → F) (i j : V) :
    MeasurableSet {r : F | hyperplaneSide v r i ≠ hyperplaneSide v r j} := by
  simp only [hyperplaneSide_ne_iff]
  exact measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) 0

/-- The weight of the rounded cut is integrable. -/
theorem integrable_cutValue_hyperplaneSide (ends : ι → V × V) (w : ι → ℝ) (v : V → F)
    (μ : Measure F) [IsFiniteMeasure μ] :
    Integrable (fun r => cutValue ends w (hyperplaneSide v r)) μ := by
  simp only [cutValue_hyperplaneSide_eq_sum_indicator]
  exact integrable_finsetSum _ fun e _ =>
    (integrable_const (w e)).indicator (measurableSet_hyperplaneSide_ne v _ _)

variable [FiniteDimensional ℝ F]

/-- **Goemans–Williamson, Theorem 3.1.** For unit vectors `v`, the expected weight of the cut
along the hyperplane orthogonal to a standard Gaussian vector is
`∑ e, w e * arccos ⟪v (ends e).1, v (ends e).2⟫ / π` [GoemansWilliamson1995, Theorem 3.1]. The
weights may have any sign. -/
theorem integral_cutValue_hyperplaneSide (ends : ι → V × V) (w : ι → ℝ) {v : V → F}
    (hv : ∀ i, ‖v i‖ = 1) :
    ∫ r, cutValue ends w (hyperplaneSide v r) ∂stdGaussian F =
      ∑ e, w e * (arccos ⟪v (ends e).1, v (ends e).2⟫ / π) := by
  simp only [cutValue_hyperplaneSide_eq_sum_indicator]
  rw [integral_finsetSum _ fun e _ =>
    (integrable_const (w e)).indicator (measurableSet_hyperplaneSide_ne v _ _)]
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [integral_indicator_const _ (measurableSet_hyperplaneSide_ne v _ _), smul_eq_mul, mul_comm]
  simp only [hyperplaneSide_ne_iff]
  rw [measureReal_stdGaussian_zero_mem_uIoc_eq_arccos (hv _) (hv _)]

/-- **Goemans–Williamson, Theorem 3.3.** For unit vectors `v` and nonnegative weights, the
expected weight of the rounded cut is at least `α` times the relaxation's objective at `v`
[GoemansWilliamson1995, Theorem 3.3]. -/
theorem goemansWilliamsonConstant_mul_sdpValue_le_integral (ends : ι → V × V) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1) :
    goemansWilliamsonConstant * sdpValue ends w v ≤
      ∫ r, cutValue ends w (hyperplaneSide v r) ∂stdGaussian F := by
  rw [integral_cutValue_hyperplaneSide ends w hv, sdpValue, Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  have h := abs_real_inner_le_norm (v (ends e).1) (v (ends e).2)
  rw [hv, hv, mul_one, abs_le] at h
  have := mul_le_mul_of_nonneg_left (goemansWilliamsonConstant_mul_le_arccos h.1 h.2) (hw e)
  calc goemansWilliamsonConstant * (w e * (1 - ⟪v (ends e).1, v (ends e).2⟫) / 2)
      = w e * (goemansWilliamsonConstant * ((1 - ⟪v (ends e).1, v (ends e).2⟫) / 2)) := by ring
    _ ≤ w e * (arccos ⟪v (ends e).1, v (ends e).2⟫ / π) := this

/-! ### The approximation guarantee -/

/-- **The Goemans–Williamson guarantee for `ε`-optimal vectors.** If the unit vectors `v` are
within `ε` of optimal for the relaxation and the weights are nonnegative, then the expected weight
of the rounded cut is at least `α` times the weight of every cut minus `ε`
[GoemansWilliamson1995, Section 3]. Taking `side` to be a maximum cut, the expected weight is at
least `α (OPT - ε)`, with `α > 0.87856` (`Real.lt_goemansWilliamsonConstant`). -/
theorem goemansWilliamsonConstant_mul_sub_le_integral (ends : ι → V × V) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) → sdpValue ends w v' ≤ sdpValue ends w v + ε)
    (side : V → Bool) :
    goemansWilliamsonConstant * (cutValue ends w side - ε) ≤
      ∫ r, cutValue ends w (hyperplaneSide v r) ∂stdGaussian F :=
  (mul_le_mul_of_nonneg_left (by linarith [cutValue_le_sdpValue_add hv hopt side])
    goemansWilliamsonConstant_nonneg).trans
    (goemansWilliamsonConstant_mul_sdpValue_le_integral ends hw hv)

/-- **The Goemans–Williamson guarantee.** If the unit vectors `v` maximize the relaxation and the
weights are nonnegative, then the expected weight of the rounded cut is at least `α` times the
weight of every cut, in particular of a maximum cut [GoemansWilliamson1995, Section 3]. -/
theorem goemansWilliamsonConstant_mul_cutValue_le_integral (ends : ι → V × V) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1)
    (hopt : IsMaxOn (sdpValue ends w) {v' | ∀ i, ‖v' i‖ = 1} v) (side : V → Bool) :
    goemansWilliamsonConstant * cutValue ends w side ≤
      ∫ r, cutValue ends w (hyperplaneSide v r) ∂stdGaussian F := by
  simpa only [sub_zero] using goemansWilliamsonConstant_mul_sub_le_integral ends hw hv
    (ε := 0) (fun v' hv' => (add_zero (sdpValue ends w v)).symm ▸ isMaxOn_iff.1 hopt v' hv') side

/-- **Some hyperplane achieves the guarantee.** Under the hypotheses of
`goemansWilliamsonConstant_mul_sub_le_integral`, some hyperplane cut has weight at least `α` times
the weight of every cut minus `ε`. -/
theorem exists_forall_goemansWilliamsonConstant_mul_sub_le (ends : ι → V × V) {w : ι → ℝ}
    (hw : ∀ e, 0 ≤ w e) {v : V → F} (hv : ∀ i, ‖v i‖ = 1) {ε : ℝ}
    (hopt : ∀ v' : V → F, (∀ i, ‖v' i‖ = 1) → sdpValue ends w v' ≤ sdpValue ends w v + ε) :
    ∃ r : F, ∀ side : V → Bool,
      goemansWilliamsonConstant * (cutValue ends w side - ε) ≤
        cutValue ends w (hyperplaneSide v r) := by
  obtain ⟨r, hr⟩ := exists_integral_le (integrable_cutValue_hyperplaneSide ends w v
    (stdGaussian F))
  exact ⟨r, fun side => (goemansWilliamsonConstant_mul_sub_le_integral ends hw hv hopt side).trans
    hr⟩

omit [MeasurableSpace F] [BorelSpace F] in
/-- **The relaxation has an optimal solution.** In a nontrivial finite-dimensional `F`, some
assignment of unit vectors maximizes the relaxation's objective. The vertex type may be infinite:
the objective depends only on the endpoints of the finitely many edges. -/
theorem exists_isMaxOn_sdpValue [Nontrivial F] (ends : ι → V × V)
    (w : ι → ℝ) : ∃ v : V → F, (∀ i, ‖v i‖ = 1) ∧
      IsMaxOn (sdpValue ends w) {v' | ∀ i, ‖v' i‖ = 1} v := by
  have hK : IsCompact {v' : V → F | ∀ i, ‖v' i‖ = 1} := by
    have := isCompact_univ_pi fun _ : V => isCompact_sphere (0 : F) 1
    simpa only [Set.pi, mem_univ, mem_sphere_iff_norm, sub_zero, true_imp_iff] using this
  obtain ⟨u, hu⟩ := (NormedSpace.sphere_nonempty_rclike ℝ (E := F) zero_le_one).some
  rw [mem_sphere_zero_iff_norm] at hu
  have hcont : Continuous (sdpValue ends w : (V → F) → ℝ) := by
    unfold sdpValue
    fun_prop
  obtain ⟨v, hv, hmax⟩ := hK.exists_isMaxOn ⟨fun _ => u, fun _ => hu⟩ hcont.continuousOn
  exact ⟨v, hv, hmax⟩

end Cslib.Algorithms.Lean.MaxCut
