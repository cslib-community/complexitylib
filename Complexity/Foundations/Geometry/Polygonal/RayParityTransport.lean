/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.RayParityEven
import Mathlib.Topology.LocallyConstant.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Algebra.Affine

/-!
# Transport of ray parity along isolated segment interiors

The trace of ray parity on the interior of an isolated segment is constant when the
arrangement has even incidence. Removing the observed segment leaves its endpoint jumps
unchanged at every interior height. This gives transport without choosing a positive
distance from all the other endpoint heights.
-/

public section

namespace Cslib.Polygonal

open Classical in
/-- The sum of the endpoint-height jumps vanishes for an even finite arrangement.
All actual occurrences are retained, including coincident endpoints. -/
theorem sum_rayParity_endpoint_jumps_eq_zero {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false) (z : ℂ) :
    (∑ i, x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
      decide ((b i).im = z.im ∧ z.re < (b i).re))) = 0 := by
  classical
  let endpoint (p : ι × Bool) : ℂ := if p.2 then b p.1 else a p.1
  let f (p : ℂ) : Bool := decide (p.im = z.im ∧ z.re < p.re)
  have hfiber (p : ℂ) :
      (∑ i : ι × Bool, if endpoint i = p then x i.1 else 0) = 0 := by
    simpa only [Fintype.sum_prod_type, Fintype.sum_bool, endpoint,
      Bool.false_eq_true, ↓reduceIte, add_comm, Bool.zero_eq_false] using heven p
  have hsum : (∑ i : ι × Bool, x i.1 * f (endpoint i)) = 0 := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ)
      (t := Finset.univ.image endpoint) (g := endpoint)
      (fun i _ => Finset.mem_image_of_mem _ (Finset.mem_univ i))]
    apply Finset.sum_eq_zero
    intro p _
    rw [Finset.sum_filter]
    have hterm (i : ι × Bool) :
        (if endpoint i = p then x i.1 * f (endpoint i) else 0) =
          (if endpoint i = p then x i.1 else 0) * f p := by
      split_ifs with h <;> simp [h]
    simp only [hterm, ← Finset.sum_mul, hfiber, zero_mul]
  simpa only [Fintype.sum_prod_type, Fintype.sum_bool, endpoint,
    Bool.false_eq_true, ↓reduceIte, ← mul_add, f, add_comm] using hsum

open Classical in
/-- Local cancellation requires only zero total endpoint jump on the observation ray.
Unlike global evenness, this condition is preserved when a segment whose endpoint heights
are different from the observation height is removed. -/
theorem eventually_rayParity_eq_of_endpoint_jumps_eq_zero {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (z : ℂ) (hz : ∀ i, x i = true → z ∉ segment ℝ (a i) (b i))
    (hjump : (∑ i, x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
      decide ((b i).im = z.im ∧ z.re < (b i).re))) = 0) :
    ∀ᶠ w in nhds z, rayParity a b x w = rayParity a b x z := by
  classical
  have hi (i : ι) : ∀ᶠ w in nhds z,
      x i * (decide (RayCrosses (a i) (b i) w) + decide (RayCrosses (a i) (b i) z)) =
        x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
          decide ((b i).im = z.im ∧ z.re < (b i).re)) * !decide (z.im ≤ w.im) := by
    by_cases hx : x i = true
    · filter_upwards [eventually_rayCrosses_jump (a i) (b i) z (hheight i) (hz i hx)] with w hw
      simpa only [← Bool.add_eq_xor, ← Bool.mul_eq_and, mul_assoc] using congrArg (x i * ·) hw
    · have hx' : x i = false := Bool.eq_false_iff.mpr hx
      exact Filter.Eventually.of_forall fun _ => by simp [hx', Bool.mul_eq_and]
  filter_upwards [Filter.eventually_all.mpr hi] with w hw
  apply (BooleanRing.add_eq_zero' _ _).mp
  calc
    rayParity a b x w + rayParity a b x z =
        ∑ i, x i * (decide (RayCrosses (a i) (b i) w) +
          decide (RayCrosses (a i) (b i) z)) := by
      simp only [rayParity, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hw : RayCrosses (a i) (b i) w <;>
        by_cases hz : RayCrosses (a i) (b i) z <;>
        simp [hw, hz, mul_add, Bool.mul_eq_and, Bool.zero_eq_false]
    _ = (∑ i, x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
        decide ((b i).im = z.im ∧ z.re < (b i).re))) * !decide (z.im ≤ w.im) := by
      simp only [hw, Finset.sum_mul]
    _ = 0 := by rw [hjump, zero_mul]

/-- A point on a nonhorizontal segment never counts that same segment as a crossing:
the horizontal ray excludes its base point. -/
theorem not_rayCrosses_lineMap {a b : ℂ} (hab : a.im ≠ b.im) (t : ℝ) :
    ¬RayCrosses a b (AffineMap.lineMap a b t) := by
  have hden : b.im - a.im ≠ 0 := sub_ne_zero.mpr hab.symm
  have him : (AffineMap.lineMap a b t).im = a.im + t * (b.im - a.im) := by
    simp only [AffineMap.lineMap_apply_module', Complex.add_im, Complex.real_smul,
      Complex.mul_im, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_mul, add_zero]
    ring
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
    have him : (point t).im = (a i).im + t.val * ((b i).im - (a i).im) := by
      simp only [point, AffineMap.lineMap_apply_module', Complex.add_im, Complex.real_smul,
        Complex.mul_im, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_mul, add_zero]
      ring
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
