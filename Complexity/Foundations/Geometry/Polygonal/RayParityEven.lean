/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.RayParity

/-!
# Local constancy of ray parity for even segment arrangements

For a finite indexed arrangement of nonhorizontal segments, even incidence at every actual
endpoint cancels the endpoint-height jumps of horizontal-ray parity. Consequently parity
is constant on a neighborhood of every point off the selected support, including points
at endpoint heights. Repeated occurrences and both endpoints of each segment are counted.

This is an original finite parity proof. It supplies no graph face colors or right-side
transport theorem.
-/

public section

namespace Cslib.Polygonal

/-- Even incidence at each actual endpoint cancels all endpoint-height jumps. The
nonhorizontal hypothesis is explicit, and the base point avoids every selected segment.
No simplicity, connectedness, degree bound or general-position condition on the endpoint
positions is required. In particular different endpoints may be the same point. -/
theorem eventually_rayParity_eq_of_even {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (z : ℂ) (hz : ∀ i, x i = true → z ∉ segment ℝ (a i) (b i)) :
    ∀ᶠ w in nhds z, rayParity a b x w = rayParity a b x z := by
  classical
  have hweighted (f : ℂ → Bool) :
      (∑ i, x i * (f (a i) + f (b i))) = 0 := by
    let s := Finset.univ.image a ∪ Finset.univ.image b
    have hgroup (g : ι → ℂ) (hg : ∀ i, g i ∈ s) :
        (∑ i, x i * f (g i)) =
          ∑ p ∈ s, (∑ i, if g i = p then x i else 0) * f p := by
      rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := s)
        (g := g) (fun i _ => hg i) (fun i => x i * f (g i))]
      apply Finset.sum_congr rfl
      intro p _
      rw [Finset.sum_mul, Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : g i = p <;> simp [hi]
    rw [Finset.sum_congr rfl (fun i _ => mul_add (x i) (f (a i)) (f (b i))),
      Finset.sum_add_distrib,
      hgroup a (fun i => Finset.mem_union_left _ (Finset.mem_image_of_mem a (Finset.mem_univ i))),
      hgroup b (fun i => Finset.mem_union_right _ (Finset.mem_image_of_mem b (Finset.mem_univ i))),
      ← Finset.sum_add_distrib]
    apply Finset.sum_eq_zero
    intro p _
    rw [← add_mul, ← Finset.sum_add_distrib, heven p, Bool.zero_eq_false]
    rfl
  have hjump (i : ι) : ∀ᶠ w in nhds z,
      x i * (decide (RayCrosses (a i) (b i) w) + decide (RayCrosses (a i) (b i) z)) =
        x i * (decide ((a i).im = z.im ∧ z.re < (a i).re) +
          decide ((b i).im = z.im ∧ z.re < (b i).re)) * !decide (z.im ≤ w.im) := by
    by_cases hi : x i = true
    · filter_upwards [eventually_rayCrosses_jump (a i) (b i) z (hheight i) (hz i hi)] with w hw
      simpa only [← Bool.add_eq_xor, ← Bool.mul_eq_and, mul_assoc] using congrArg (x i * ·) hw
    · have hif : x i = false := Bool.eq_false_iff.mpr hi
      exact Filter.Eventually.of_forall (fun _ => by simp [hif, Bool.mul_eq_and])
  filter_upwards [Filter.eventually_all.mpr hjump] with w hw
  have hdelta : rayParity a b x w + rayParity a b x z = 0 := by
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
      _ = 0 := by
        rw [hweighted (fun p => decide (p.im = z.im ∧ z.re < p.re))]
        rfl
  exact (BooleanRing.add_eq_zero' _ _).mp hdelta

end Cslib.Polygonal
