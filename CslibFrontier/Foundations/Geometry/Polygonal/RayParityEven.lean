/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayParity

/-!
# Local constancy of ray parity for even segment arrangements

For a finite indexed arrangement of nonhorizontal segments, even incidence at every actual
endpoint cancels the endpoint-height jumps of horizontal-ray parity. Consequently parity
is constant on a neighborhood of every point off the selected support, including points
at endpoint heights. Repeated occurrences and both endpoints of each segment are counted.
The weaker criterion needs only zero total endpoint jump on the observation ray; global
even incidence supplies this premise. Segment-interior transport uses the same criterion
after removing its observed segment.

This is an original finite parity proof. It supplies no graph face colors or right-side
transport theorem.
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

/-- Even incidence at each actual endpoint cancels all endpoint-height jumps. The
nonhorizontal hypothesis is explicit, and the base point avoids every selected segment.
No simplicity, connectedness, degree bound or general-position condition on the endpoint
positions is required. In particular different endpoints may be the same point. -/
theorem eventually_rayParity_eq_of_even {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (z : ℂ) (hz : ∀ i, x i = true → z ∉ segment ℝ (a i) (b i)) :
    ∀ᶠ w in nhds z, rayParity a b x w = rayParity a b x z :=
  eventually_rayParity_eq_of_endpoint_jumps_eq_zero a b x hheight z hz
    (sum_rayParity_endpoint_jumps_eq_zero a b x heven z)

end Cslib.Polygonal
