/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityEven
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Affine

/-!
# Transport of ray parity along isolated segment interiors

The trace of ray parity on the interior of an isolated segment is constant when the
arrangement has even incidence. Removing the observed segment leaves its endpoint jumps
unchanged at every interior height. This gives transport without choosing a positive
distance from all the other endpoint heights. Local cancellation and its even-incidence
specialization are supplied by `RayParityEven`; this module applies that shared criterion
to the arrangement with the observed segment removed.
-/

public section

namespace Cslib.Polygonal

/-- A point on a nonhorizontal segment never counts that same segment as a crossing:
the horizontal ray excludes its base point. -/
theorem not_rayCrosses_lineMap {a b : ℂ} (hab : a.im ≠ b.im) (t : ℝ) :
    ¬RayCrosses a b (AffineMap.lineMap a b t) := by
  have hden : b.im - a.im ≠ 0 := sub_ne_zero.mpr hab.symm
  have him := lineMap_im a b t
  have hre : (AffineMap.lineMap a b t).re = horizontalIntercept a b
      (AffineMap.lineMap a b t).im := by
    rw [him]
    simp only [horizontalIntercept]
    rw [show a.im + t * (b.im - a.im) - a.im = t * (b.im - a.im) by ring,
      mul_div_cancel_right₀ t hden]
    simp only [AffineMap.lineMap_apply_module', Complex.add_re, Complex.real_smul,
      Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im, zero_mul, sub_zero]
    ring
  exact fun h => (ne_of_lt h.2.2) hre

/-- Ray parity on the open interior of one segment is constant if no other listed
segment meets that interior. The segment itself is omitted by the strict base-point
convention. Endpoint jumps from other segments cancel even when their heights occur
inside the observed segment's height range. -/
theorem rayParity_lineMap_eq_of_even {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (i : ι) (hisolated : ∀ j, j ≠ i → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      AffineMap.lineMap (a i) (b i) t ∉ segment ℝ (a j) (b j))
    {s t : ℝ} (hs : s ∈ Set.Ioo 0 1) (ht : t ∈ Set.Ioo 0 1) :
    rayParity a b x (AffineMap.lineMap (a i) (b i) s) =
      rayParity a b x (AffineMap.lineMap (a i) (b i) t) := by
  classical
  let X := {t : ℝ // t ∈ Set.Ioo (0 : ℝ) 1}
  let point (t : X) := AffineMap.lineMap (a i) (b i) t.val
  let color (t : X) := rayParity a b x (point t)
  let y (j : ι) : Bool := if j = i then 0 else x j
  have hremove (t : X) : color t = rayParity a b y (point t) := by
    apply Finset.sum_congr rfl
    intro j _
    by_cases hj : j = i
    · subst j
      simp only [point, not_rayCrosses_lineMap (hheight i), ↓reduceIte]
    · simp only [y, hj, ↓reduceIte]
  have hlocal : IsLocallyConstant color := by
    apply (IsLocallyConstant.iff_eventually_eq color).mpr
    intro t
    have him : (point t).im = (a i).im + t.val * ((b i).im - (a i).im) :=
      lineMap_im (a i) (b i) t.val
    have ha : (a i).im ≠ (point t).im := by
      rw [him]
      rcases lt_or_gt_of_ne (hheight i) with h | h <;> nlinarith [t.property.1]
    have hb : (b i).im ≠ (point t).im := by
      rw [him]
      rcases lt_or_gt_of_ne (hheight i) with h | h <;> nlinarith [t.property.2]
    have hjump : (∑ j, y j *
        (decide ((a j).im = (point t).im ∧ (point t).re < (a j).re) +
          decide ((b j).im = (point t).im ∧ (point t).re < (b j).re))) = 0 := by
      rw [← sum_rayParity_endpoint_jumps_eq_zero a b x heven (point t)]
      apply Finset.sum_congr rfl
      intro j _
      by_cases hj : j = i
      · subst j
        simp only [ha, hb, false_and, decide_false, ← Bool.zero_eq_false, add_zero, mul_zero]
      · simp only [y, hj, ↓reduceIte]
    have havoid (j : ι) (hy : y j = true) : point t ∉ segment ℝ (a j) (b j) := by
      have hj : j ≠ i := by
        intro h
        simp only [y, h, ↓reduceIte, Bool.zero_eq_false, Bool.false_eq_true] at hy
      exact hisolated j hj t.val t.property
    have h := eventually_rayParity_eq_of_endpoint_jumps_eq_zero a b y hheight
      (point t) havoid hjump
    have hline : Continuous (AffineMap.lineMap (a i) (b i) : ℝ → ℂ) :=
      AffineMap.lineMap_continuous
    have hcont : Continuous point := hline.comp continuous_subtype_val
    filter_upwards [hcont.continuousAt.eventually h] with u hu
    rw [hremove u, hremove t]
    exact hu
  let : PreconnectedSpace X := isPreconnected_iff_preconnectedSpace.mp
    (convex_Ioo (0 : ℝ) 1).isPreconnected
  exact hlocal.apply_eq_of_preconnectedSpace ⟨s, hs⟩ ⟨t, ht⟩

end Cslib.Polygonal
