/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Analysis.Complex.Basic
public import Mathlib.Analysis.Convex.Segment
public import Mathlib.Algebra.Ring.BooleanRing
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Topology.Algebra.Order.Field

/-!
# Half-open horizontal ray crossings

A segment contributes to the ray from `z` towards positive real infinity when its
intersection with the horizontal line through `z` lies strictly to the right. The lower
endpoint height is included and the upper endpoint height is excluded, independently of
the orientation of the segment. Horizontal segments contribute nothing.

The crossing test is characterized by actual real affine parameters, including crossings
at the lower endpoint. These are original finite geometric calculations. They do not
assert local constancy of a closed chain's parity or construct colors on graph faces.
-/

public section

namespace Cslib.Polygonal

/-- The real coordinate where the supporting line of a nonhorizontal segment meets
height `h`. The formula is total; the horizontal case is excluded by `RayCrosses`. -/
@[expose] noncomputable def horizontalIntercept (a b : ℂ) (h : ℝ) : ℝ :=
  a.re + (h - a.im) / (b.im - a.im) * (b.re - a.re)

/-- Crossing of the positive horizontal ray with the lower endpoint height included and
the upper endpoint height excluded. The base point itself is excluded by a strict real
coordinate comparison. Horizontal and degenerate segments never contribute. -/
@[expose] def RayCrosses (a b z : ℂ) : Prop :=
  min a.im b.im ≤ z.im ∧ z.im < max a.im b.im ∧
    z.re < horizontalIntercept a b z.im

/-- A horizontal segment contributes no ray crossing, even at its own height. -/
theorem not_rayCrosses_of_im_eq {a b : ℂ} (hab : a.im = b.im) (z : ℂ) :
    ¬RayCrosses a b z := by
  simp only [RayCrosses, hab, min_self, max_self]
  intro h
  exact (not_lt_of_ge h.1) h.2.1

/-- A nonhorizontal supporting line has the same intercept after reversing its ends. -/
theorem horizontalIntercept_reverse {a b : ℂ} (hab : a.im ≠ b.im) (h : ℝ) :
    horizontalIntercept b a h = horizontalIntercept a b h := by
  unfold horizontalIntercept
  have hab' : b.im - a.im ≠ 0 := sub_ne_zero.mpr hab.symm
  have hba' : a.im - b.im ≠ 0 := sub_ne_zero.mpr hab
  field_simp
  ring

/-- The half-open convention depends on height, not on the order of the endpoints. -/
theorem rayCrosses_reverse (a b z : ℂ) : RayCrosses b a z ↔ RayCrosses a b z := by
  by_cases hab : a.im = b.im
  · exact iff_of_false (not_rayCrosses_of_im_eq hab.symm z)
      (not_rayCrosses_of_im_eq hab z)
  · simp only [RayCrosses, min_comm b.im a.im, max_comm b.im a.im,
      horizontalIntercept_reverse hab]

/-- At the first endpoint's height, the supporting-line intercept is that endpoint. -/
@[simp] theorem horizontalIntercept_left (a b : ℂ) :
    horizontalIntercept a b a.im = a.re := by
  simp [horizontalIntercept]

/-- At the second endpoint's height, the supporting-line intercept is that endpoint. -/
theorem horizontalIntercept_right {a b : ℂ} (hab : a.im ≠ b.im) :
    horizontalIntercept a b b.im = b.re := by
  rw [← horizontalIntercept_reverse hab, horizontalIntercept_left]

/-- The imaginary coordinate along a real affine segment is affine in its parameter. -/
theorem lineMap_im (a b : ℂ) (t : ℝ) :
    (AffineMap.lineMap a b t).im = a.im + t * (b.im - a.im) := by
  simp only [AffineMap.lineMap_apply_module', Complex.add_im, Complex.real_smul,
    Complex.mul_im, Complex.ofReal_re, Complex.sub_im, Complex.ofReal_im, zero_mul, add_zero]
  ring

private theorem lineMap_re (a b : ℂ) (t : ℝ) :
    (AffineMap.lineMap a b t).re = a.re + t * (b.re - a.re) := by
  simp only [AffineMap.lineMap_apply_module', Complex.add_re, Complex.real_smul,
    Complex.mul_re, Complex.ofReal_re, Complex.sub_re, Complex.ofReal_im, zero_mul, sub_zero]
  ring

/-- A crossing is an intersection at an actual real segment parameter. The final strict
height inequality is exactly the exclusion of the upper endpoint. No generic-position or
nonhorizontal assumption is hidden: horizontal segments make both sides false. -/
theorem rayCrosses_iff_exists (a b z : ℂ) :
    RayCrosses a b z ↔ ∃ t ∈ Set.Icc (0 : ℝ) 1,
      (AffineMap.lineMap a b t).im = z.im ∧
      z.re < (AffineMap.lineMap a b t).re ∧ z.im < max a.im b.im := by
  by_cases hab : a.im = b.im
  · constructor
    · exact fun h => (not_rayCrosses_of_im_eq hab z h).elim
    · rintro ⟨t, -, ht, -, hz⟩
      rw [lineMap_im, hab] at ht
      simp only [sub_self, mul_zero, add_zero] at ht
      simp only [hab, max_self, ← ht, lt_self_iff_false] at hz
  · have hden : b.im - a.im ≠ 0 := sub_ne_zero.mpr (Ne.symm hab)
    constructor
    · rintro ⟨hlo, hhi, hx⟩
      let t := (z.im - a.im) / (b.im - a.im)
      have ht : t ∈ Set.Icc (0 : ℝ) 1 := by
        rcases lt_or_gt_of_ne hab with hab | hab
        · rw [min_eq_left hab.le] at hlo
          rw [max_eq_right hab.le] at hhi
          exact ⟨div_nonneg (sub_nonneg.mpr hlo) (sub_nonneg.mpr hab.le),
            (div_le_one (sub_pos.mpr hab)).mpr (by linarith)⟩
        · rw [min_eq_right hab.le] at hlo
          rw [max_eq_left hab.le] at hhi
          exact ⟨div_nonneg_of_nonpos (by linarith) (by linarith),
            (div_le_one_of_neg (sub_neg.mpr hab)).mpr (by linarith)⟩
      refine ⟨t, ht, ?_, ?_, hhi⟩
      · rw [lineMap_im]
        dsimp only [t]
        rw [div_mul_cancel₀ _ hden]
        ring
      · exact (lineMap_re a b t).symm ▸ hx
    · rintro ⟨t, ht, him, hre, hhi⟩
      rw [lineMap_im] at him
      have ht' : t = (z.im - a.im) / (b.im - a.im) := by
        apply (eq_div_iff hden).mpr
        linarith
      refine ⟨?_, hhi, ?_⟩
      · rcases le_total a.im b.im with hab | hab
        · rw [min_eq_left hab]
          nlinarith [ht.1]
        · rw [min_eq_right hab]
          nlinarith [ht.2]
      · simpa only [lineMap_re, ht', horizontalIntercept] using hre

/-- Away from the endpoint heights and the supporting-line intercept, the ray-crossing
test is constant in a neighborhood. This is a statement about an actual open neighborhood
in the real plane, rather than finitely many test points. It does not handle cancellation
of jumps at the endpoint heights of a closed segment chain. -/
theorem eventually_rayCrosses_iff (a b z : ℂ) (ha : z.im ≠ a.im) (hb : z.im ≠ b.im)
    (hx : z.re ≠ horizontalIntercept a b z.im) :
    ∀ᶠ w in nhds z, RayCrosses a b w ↔ RayCrosses a b z := by
  have hcompare {f g : ℂ → ℝ} (hf : ContinuousAt f z) (hg : ContinuousAt g z)
      (hne : f z ≠ g z) : ∀ᶠ w in nhds z, f w < g w ↔ f z < g z := by
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · filter_upwards [hf.eventually_lt hg hlt] with w hw
      exact iff_of_true hw hlt
    · filter_upwards [hg.eventually_lt hf hgt] with w hw
      exact iff_of_false (not_lt_of_ge hw.le) (not_lt_of_ge hgt.le)
  have hmin : z.im ≠ min a.im b.im := by
    rcases le_total a.im b.im with h | h
    · simpa only [min_eq_left h] using ha
    · simpa only [min_eq_right h] using hb
  have hmax : z.im ≠ max a.im b.im := by
    rcases le_total a.im b.im with h | h
    · simpa only [max_eq_right h] using hb
    · simpa only [max_eq_left h] using ha
  have hcont : Continuous (fun w : ℂ => horizontalIntercept a b w.im) := by
    unfold horizontalIntercept
    fun_prop
  filter_upwards [hcompare Complex.continuous_im.continuousAt continuousAt_const hmin,
    hcompare Complex.continuous_im.continuousAt continuousAt_const hmax,
    hcompare Complex.continuous_re.continuousAt hcont.continuousAt hx] with w hlo hhi hre
  have hlo' : min a.im b.im ≤ w.im ↔ min a.im b.im ≤ z.im := by
    simpa only [not_lt] using not_congr hlo
  simp only [RayCrosses, hlo', hhi, hre]

/-- At a height in the half-open vertical range, a base point off the actual segment
cannot coincide with the segment's horizontal intercept. -/
theorem intercept_ne_of_not_mem_segment (a b z : ℂ)
    (hlo : min a.im b.im ≤ z.im) (hhi : z.im < max a.im b.im)
    (hz : z ∉ segment ℝ a b) : z.re ≠ horizontalIntercept a b z.im := by
  intro hx
  have hab : a.im ≠ b.im := by
    intro h
    simp only [h, min_self, max_self] at hlo hhi
    exact (not_lt_of_ge hlo) hhi
  let w : ℂ := ⟨z.re - 1, z.im⟩
  have hw : RayCrosses a b w := ⟨hlo, hhi, by
    change z.re - 1 < horizontalIntercept a b z.im
    rw [← hx]
    linarith⟩
  obtain ⟨t, ht, him, -, -⟩ := (rayCrosses_iff_exists a b w).mp hw
  have ht' : t = (z.im - a.im) / (b.im - a.im) := by
    apply (eq_div_iff (sub_ne_zero.mpr hab.symm)).mpr
    rw [lineMap_im] at him
    change a.im + t * (b.im - a.im) = z.im at him
    linarith
  have heq : AffineMap.lineMap a b t = z := by
    apply Complex.ext
    · rw [lineMap_re, ht']
      exact hx.symm
    · exact him
  exact hz (heq ▸ lineMap_mem_segment ℝ a b ht)

/-- Away from the endpoint heights, avoiding the actual segment is enough for local
constancy. Points on extensions of the supporting line are included. -/
theorem eventually_rayCrosses_iff_of_not_mem_segment (a b z : ℂ)
    (ha : z.im ≠ a.im) (hb : z.im ≠ b.im) (hz : z ∉ segment ℝ a b) :
    ∀ᶠ w in nhds z, RayCrosses a b w ↔ RayCrosses a b z := by
  by_cases hlo : z.im < min a.im b.im
  · filter_upwards [Complex.continuous_im.continuousAt.eventually_lt continuousAt_const hlo]
      with w hw
    exact iff_of_false (fun h => (not_lt_of_ge h.1) hw)
      (fun h => (not_lt_of_ge h.1) hlo)
  by_cases hhi : max a.im b.im < z.im
  · filter_upwards [continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hhi]
      with w hw
    exact iff_of_false (fun h => (not_lt_of_ge hw.le) h.2.1)
      (fun h => (not_lt_of_ge hhi.le) h.2.1)
  have hne : z.im ≠ max a.im b.im := by
    rcases le_total a.im b.im with h | h
    · simpa only [max_eq_right h] using hb
    · simpa only [max_eq_left h] using ha
  exact eventually_rayCrosses_iff a b z ha hb
    (intercept_ne_of_not_mem_segment a b z (le_of_not_gt hlo)
      (lt_of_le_of_ne (le_of_not_gt hhi) hne) hz)

open Classical in
/-- At an endpoint height of a nonhorizontal segment, its ray bit changes exactly when
that endpoint is to the right of the base point and the observation point moves below the
height. This includes either segment orientation and quantifies over a whole neighborhood.
The base point differs from the endpoint, as witnessed by `hx`. -/
theorem eventually_rayCrosses_endpoint_jump (a b z : ℂ) (hab : a.im ≠ b.im)
    (hz : z.im = a.im) (hx : z.re ≠ a.re) :
    ∀ᶠ w in nhds z,
      (decide (RayCrosses a b w) ^^ decide (RayCrosses a b z)) =
        (decide (z.re < a.re) && !decide (z.im ≤ w.im)) := by
  have hcont : Continuous (fun w : ℂ => horizontalIntercept a b w.im) := by
    unfold horizontalIntercept
    fun_prop
  have hx' : z.re ≠ horizontalIntercept a b z.im := by
    simpa only [hz, horizontalIntercept_left] using hx
  have hcompare : ∀ᶠ w in nhds z,
      w.re < horizontalIntercept a b w.im ↔ z.re < a.re := by
    rcases lt_or_gt_of_ne hx' with h | h
    · filter_upwards [Complex.continuous_re.continuousAt.eventually_lt hcont.continuousAt h]
        with w hw
      exact iff_of_true hw (by simpa only [hz, horizontalIntercept_left] using h)
    · filter_upwards [hcont.continuousAt.eventually_lt Complex.continuous_re.continuousAt h]
        with w hw
      exact iff_of_false (not_lt_of_ge hw.le)
        (by simpa only [hz, horizontalIntercept_left] using not_lt_of_ge h.le)
  rcases lt_or_gt_of_ne hab with hab | hab
  · have hz' : z.im < b.im := hz ▸ hab
    filter_upwards [hcompare,
      Complex.continuous_im.continuousAt.eventually_lt continuousAt_const hz'] with w hw hwb
    have hcw : RayCrosses a b w ↔ z.im ≤ w.im ∧ z.re < a.re := by
      unfold RayCrosses
      rw [min_eq_left hab.le, max_eq_right hab.le, ← hz]
      simp only [hw, hwb, true_and]
    have hcz : RayCrosses a b z ↔ z.re < a.re := by
      simp only [RayCrosses, min_eq_left hab.le, max_eq_right hab.le, hz,
        le_refl, hab, horizontalIntercept_left, true_and]
    by_cases hw' : z.im ≤ w.im <;> by_cases hx' : z.re < a.re <;> simp [hcw, hcz, hw', hx']
  · have hz' : b.im < z.im := hz ▸ hab
    filter_upwards [hcompare,
      continuousAt_const.eventually_lt Complex.continuous_im.continuousAt hz'] with w hw hbw
    have hcw : RayCrosses a b w ↔ w.im < z.im ∧ z.re < a.re := by
      unfold RayCrosses
      rw [min_eq_right hab.le, max_eq_left hab.le, ← hz]
      simp only [hw, hbw.le, true_and]
    have hcz : ¬RayCrosses a b z := by
      simp only [RayCrosses, max_eq_left hab.le, hz, lt_self_iff_false, false_and,
        and_false, not_false_eq_true]
    by_cases hw' : z.im ≤ w.im <;> by_cases hx' : z.re < a.re <;>
      simp [hcw, hcz, hw', hx', ← not_le]

open Classical in
/-- The complete local change formula for a nonhorizontal segment off its actual support.
Only endpoints on the positive horizontal ray can contribute jumps; each contributes once,
with its actual occurrence retained. This includes observation points at endpoint heights. -/
theorem eventually_rayCrosses_jump (a b z : ℂ) (hab : a.im ≠ b.im)
    (hz : z ∉ segment ℝ a b) :
    ∀ᶠ w in nhds z,
      (decide (RayCrosses a b w) ^^ decide (RayCrosses a b z)) =
        ((decide (a.im = z.im ∧ z.re < a.re) ^^
          decide (b.im = z.im ∧ z.re < b.re)) && !decide (z.im ≤ w.im)) := by
  have hne (p : ℂ) (hp : p ∈ segment ℝ a b) (him : z.im = p.im) : z.re ≠ p.re := by
    intro hre
    exact hz (Complex.ext hre him ▸ hp)
  by_cases ha : z.im = a.im
  · filter_upwards [eventually_rayCrosses_endpoint_jump a b z hab ha
      (hne a (left_mem_segment ℝ a b) ha)] with w hw
    simpa only [ha, Ne.symm hab, false_and, decide_false, Bool.xor_false, true_and] using hw
  by_cases hb : z.im = b.im
  · filter_upwards [eventually_rayCrosses_endpoint_jump b a z hab.symm hb
      (hne b (right_mem_segment ℝ a b) hb)] with w hw
    simpa only [rayCrosses_reverse, hb, hab, false_and, decide_false,
      Bool.false_xor, true_and] using hw
  · filter_upwards [eventually_rayCrosses_iff_of_not_mem_segment a b z ha hb hz] with w hw
    simp only [hw, Ne.symm ha, Ne.symm hb, false_and, decide_false,
      Bool.false_and, Bool.xor_self]

open Classical in
/-- Boolean parity of the selected indexed segments crossing the positive horizontal ray.
The finite index type retains repeated geometric segments as separate occurrences. -/
@[expose] noncomputable def rayParity {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (z : ℂ) : Bool :=
  ∑ i, if RayCrosses (a i) (b i) z then x i else 0

/-- Segment-ray parity is linear over the Boolean ring, retaining occurrence multiplicity. -/
theorem rayParity_add {ι : Type*} [Fintype ι] (a b : ι → ℂ)
    (x y : ι → Bool) (z : ℂ) :
    rayParity a b (x + y) z = (rayParity a b x z ^^ rayParity a b y z) := by
  classical
  rw [← Bool.add_eq_xor]
  simp only [rayParity, Pi.add_apply]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

/-- The parity of a finite arrangement is constant near any point avoiding all endpoint
heights and supporting lines. No geometry or topology provider is required. Endpoint-height
cancellation for even arrangements is a further statement, not a premise hidden here. -/
theorem eventually_rayParity_eq {ι : Type*} [Fintype ι] (a b : ι → ℂ)
    (x : ι → Bool) (z : ℂ) (ha : ∀ i, z.im ≠ (a i).im) (hb : ∀ i, z.im ≠ (b i).im)
    (hx : ∀ i, z.re ≠ horizontalIntercept (a i) (b i) z.im) :
    ∀ᶠ w in nhds z, rayParity a b x w = rayParity a b x z := by
  classical
  filter_upwards [Filter.eventually_all.mpr (fun i =>
    eventually_rayCrosses_iff (a i) (b i) z (ha i) (hb i) (hx i))] with w hw
  simp only [rayParity, hw]

end Cslib.Polygonal
