/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.RayParityGerms
import Mathlib.Topology.Order.LeftRight

/-!
# Angular prefix colors at the endpoints of a segment arrangement

An endpoint color adds the clockwise-side angular prefix to the horizontal-ray parity
at the center. Even incidence removes the dependence on the auxiliary horizontal cut.
The endpoints remain indexed separately throughout.
-/

public section

namespace Cslib.Polygonal

/-- An endpoint occurrence of a listed segment; `false` is its first endpoint. -/
@[expose] def rayEndpoint {ι : Type*} (a b : ι → ℂ) (e : ι × Bool) : ℂ :=
  if e.2 then b e.1 else a e.1

/-- The actual vector departing from one indexed endpoint of a segment. -/
@[expose] def rayEndVector {ι : Type*} (a b : ι → ℂ) (e : ι × Bool) : ℂ :=
  if e.2 then a e.1 - b e.1 else b e.1 - a e.1

open Classical in
/-- Angular prefix value used for the color immediately clockwise from `v` at `p`.
The sum ranges over every actual incident segment end; the theorems below identify it
with the geometric trace under their explicit arrangement hypotheses. -/
@[expose] noncomputable def rayGermColor {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (p v : ℂ) : Bool :=
  rayParity a b x p + ∑ e : ι × Bool, if rayEndpoint a b e = p then
    x e.1 * decide (turnArg (rayEndVector a b e) < turnArg v) else 0

/-- Nonhorizontal segments have nonhorizontal vectors at both separately indexed ends. -/
theorem rayEndVector_im_ne_zero {ι : Type*} (a b : ι → ℂ)
    (hheight : ∀ i, (a i).im ≠ (b i).im) (e : ι × Bool) :
    (rayEndVector a b e).im ≠ 0 := by
  rcases e with ⟨i, tag⟩
  cases tag <;>
    simp only [rayEndVector, Bool.false_eq_true, ↓reduceIte, Complex.sub_im, sub_ne_zero]
  · exact (hheight i).symm
  · exact hheight i

/-- The angular prefix color is the actual right-hand trace on the selected outgoing
segment. Distinct incident rays, separation of remote endpoints and segments, and even
incidence are geometric hypotheses on the finite arrangement. -/
theorem eventually_rayParity_rightGerm {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (k : ι × Bool)
    (hremote : ∀ i, a i ≠ rayEndpoint a b k → b i ≠ rayEndpoint a b k →
      (rayEndpoint a b k).im ≠ (a i).im ∧
      (rayEndpoint a b k).im ≠ (b i).im ∧
      rayEndpoint a b k ∉ segment ℝ (a i) (b i))
    (hdistinct : ∀ e : ι × Bool, rayEndpoint a b e = rayEndpoint a b k →
      turnArg (rayEndVector a b e) = turnArg (rayEndVector a b k) → e = k) :
    ∀ᶠ t : ℝ in nhds 0, 0 < t →
      rayParity a b x (rayEndpoint a b k + t • rayEndVector a b k) +
          (if (rayEndVector a b k).im < 0 then x k.1 else 0) =
        rayGermColor a b x (rayEndpoint a b k) (rayEndVector a b k) := by
  classical
  let p := rayEndpoint a b k
  let v := rayEndVector a b k
  let cross (e : ι × Bool) : Bool :=
    if rayEndpoint a b e = p then x e.1 * decide (GermCrosses (rayEndVector a b e) v) else 0
  let precolor (e : ι × Bool) : Bool :=
    if rayEndpoint a b e = p then x e.1 * decide (turnArg (rayEndVector a b e) < turnArg v)
    else 0
  let correction (e : ι × Bool) : Bool := if rayEndpoint a b e = p then
    x e.1 * decide (turnArg (rayEndVector a b e) = turnArg v ∧ v.im < 0) else 0
  have hcorrect : (∑ e, correction e) = if v.im < 0 then x k.1 else 0 := by
    rw [Finset.sum_eq_single k]
    · by_cases hv : v.im < 0 <;> simp [correction, p, v, hv, Bool.mul_eq_and, Bool.zero_eq_false]
    · intro e _ hne
      by_cases hep : rayEndpoint a b e = p
      · have harg : turnArg (rayEndVector a b e) ≠ turnArg v :=
          fun h => hne (hdistinct e hep h)
        simp [correction, harg, Bool.mul_eq_and, Bool.zero_eq_false]
      · simp [correction, hep]
    · simp
  have hsum : (∑ e, cross e) + (∑ e, correction e) = ∑ e, precolor e := by
    have heven' : (∑ e : ι × Bool, if rayEndpoint a b e = p then x e.1 else 0) = 0 := by
      simpa only [Fintype.sum_prod_type, Fintype.sum_bool, rayEndpoint,
        Bool.false_eq_true, ↓reduceIte, add_comm, Bool.zero_eq_false] using heven p
    have hi (e : ι × Bool) : cross e + correction e = precolor e +
        (if rayEndpoint a b e = p then x e.1 else 0) * decide (v.im < 0) := by
      by_cases hep : rayEndpoint a b e = p
      · simp only [cross, correction, precolor, hep, ↓reduceIte, ← mul_add]
        rw [germCrosses_prefix_identity (rayEndVector_im_ne_zero a b hheight e)
          (rayEndVector_im_ne_zero a b hheight k)]
      · simp [cross, correction, precolor, hep]
    rw [← Finset.sum_add_distrib]
    simp only [hi, Finset.sum_add_distrib, ← Finset.sum_mul, heven', zero_mul, add_zero]
  have hdelta : (∑ i, ((if a i = p then
        (if GermCrosses (b i - p) v then x i else 0) else 0) +
      (if b i = p then (if GermCrosses (a i - p) v then x i else 0) else 0))) =
        ∑ e, cross e := by
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.sum_bool]
    simp only [cross, rayEndpoint, rayEndVector, ↓reduceIte]
    have hbit (P : Prop) [Decidable P] :
        (if P then x i else 0) = x i * decide P := by
      by_cases h : P <;> simp [h, Bool.mul_eq_and, Bool.zero_eq_false]
    simp only [hbit, Bool.false_eq_true, ↓reduceIte]
    by_cases ha : a i = p <;> by_cases hb : b i = p <;>
      simp [ha, hb, add_comm]
  filter_upwards [eventually_rayParity_germ a b x hheight p v
    (rayEndVector_im_ne_zero a b hheight k) hremote] with t ht hpos
  rw [ht hpos, hdelta, ← hcorrect, add_assoc, hsum]
  rfl

/-- Endpoint prefix colors on the opposite sides of a segment differ by its label.
All parameters are real and the open segment is isolated from every other occurrence.
The local hypotheses concern the actual finite arrangement, without any face data. -/
theorem rayGermColor_ends {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (heven : ∀ p : ℂ, (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (i : ι)
    (hisolated : ∀ j, j ≠ i → ∀ t ∈ Set.Ioo (0 : ℝ) 1,
      AffineMap.lineMap (a i) (b i) t ∉ segment ℝ (a j) (b j))
    (hremote : ∀ k : ι × Bool, ∀ j,
      a j ≠ rayEndpoint a b k → b j ≠ rayEndpoint a b k →
      (rayEndpoint a b k).im ≠ (a j).im ∧
      (rayEndpoint a b k).im ≠ (b j).im ∧
      rayEndpoint a b k ∉ segment ℝ (a j) (b j))
    (hdistinct : ∀ k e : ι × Bool, rayEndpoint a b e = rayEndpoint a b k →
      turnArg (rayEndVector a b e) = turnArg (rayEndVector a b k) → e = k) :
    rayGermColor a b x (a i) (b i - a i) +
      rayGermColor a b x (b i) (a i - b i) = x i := by
  classical
  have h0 := eventually_rayParity_rightGerm a b x hheight heven (i, false)
    (hremote (i, false)) (hdistinct (i, false))
  have h1 := eventually_rayParity_rightGerm a b x hheight heven (i, true)
    (hremote (i, true)) (hdistinct (i, true))
  have hsmall : ∀ᶠ t : ℝ in nhds 0, t < 1 :=
    (isOpen_Iio.mem_nhds (by norm_num : (0 : ℝ) < 1))
  obtain ⟨t, htpos, ht0, ht1, htlt⟩ := (h0.and (h1.and hsmall)).exists_gt
  have hpoint0 : rayEndpoint a b (i, false) + t • rayEndVector a b (i, false) =
      AffineMap.lineMap (a i) (b i) t := by
    simp [rayEndpoint, rayEndVector, AffineMap.lineMap_apply_module', add_comm]
  have hpoint1 : rayEndpoint a b (i, true) + t • rayEndVector a b (i, true) =
      AffineMap.lineMap (a i) (b i) (1 - t) := by
    simp only [rayEndpoint, rayEndVector, ↓reduceIte, AffineMap.lineMap_apply_module']
    module
  have ht0' := ht0 htpos
  have ht1' := ht1 htpos
  rw [hpoint0] at ht0'
  rw [hpoint1] at ht1'
  simp only [rayEndpoint, rayEndVector, Bool.false_eq_true, ↓reduceIte] at ht0' ht1'
  have htrace := rayParity_lineMap_eq_of_even a b x hheight heven i hisolated
    ⟨htpos, htlt⟩ (show 1 - t ∈ Set.Ioo (0 : ℝ) 1 by constructor <;> linarith)
  have hsign : (if (b i - a i).im < 0 then x i else 0) +
      (if (a i - b i).im < 0 then x i else 0) = x i := by
    simp only [Complex.sub_im, sub_neg]
    rcases lt_or_gt_of_ne (hheight i) with h | h
    · simp [h, not_lt_of_ge h.le]
    · simp [h, not_lt_of_ge h.le]
  rw [← ht0', ← ht1', ← htrace]
  calc
    _ = (rayParity a b x (AffineMap.lineMap (a i) (b i) t) +
        rayParity a b x (AffineMap.lineMap (a i) (b i) t)) +
        ((if (b i - a i).im < 0 then x i else 0) +
          (if (a i - b i).im < 0 then x i else 0)) := by ac_rfl
    _ = x i := by rw [BooleanRing.add_self, zero_add, hsign]

/-- Angular prefix colors on the two sides of an empty counterclockwise sector differ
by the label of its first ray. Both endpoint occurrences and arbitrary degree are retained. -/
theorem rayGermColor_adjacent {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (p : ℂ) (heven : (∑ i, ((if a i = p then x i else 0) +
      (if b i = p then x i else 0))) = false)
    (k l : ι × Bool) (hk : rayEndpoint a b k = p) (hl : rayEndpoint a b l = p)
    (hkl : k ≠ l)
    (hinj : ∀ e f : ι × Bool, rayEndpoint a b e = p → rayEndpoint a b f = p →
      turnArg (rayEndVector a b e) = turnArg (rayEndVector a b f) → e = f)
    (hgap : ∀ e : ι × Bool, rayEndpoint a b e = p → e ≠ k → e ≠ l →
      ¬sbtw ((rayEndVector a b k).arg : Real.Angle)
        ((rayEndVector a b e).arg : Real.Angle) ((rayEndVector a b l).arg : Real.Angle)) :
    rayGermColor a b x p (rayEndVector a b k) +
      rayGermColor a b x p (rayEndVector a b l) = x k.1 := by
  classical
  let E := {e : ι × Bool // rayEndpoint a b e = p}
  have hrestrict (f : ι × Bool → Bool) :
      (∑ e, if rayEndpoint a b e = p then f e else 0) = ∑ e : E, f e.val := by
    rw [← Finset.sum_filter]
    exact Finset.sum_subtype _ (fun e => by simp) f
  have heven' : (∑ e : E, x e.val.1) = 0 := by
    rw [← hrestrict (fun e => x e.1)]
    simpa only [Fintype.sum_prod_type, Fintype.sum_bool, rayEndpoint,
      Bool.false_eq_true, ↓reduceIte, add_comm, Bool.zero_eq_false] using heven
  have hsum := sum_angularPrefix_adjacent
    (fun e : E => turnArg (rayEndVector a b e.val)) (fun e : E => x e.val.1)
    (fun e => turnArg_mem (rayEndVector_im_ne_zero a b hheight e.val))
    (fun e f h => Subtype.ext (hinj e.val f.val e.property f.property h))
    heven' (⟨k, hk⟩ : E) (⟨l, hl⟩ : E)
    (fun h => hkl (congrArg Subtype.val h))
    (fun e hek hel => by
      simpa only [turnArg_coe_angle] using hgap e.val e.property
        (fun h => hek (Subtype.ext h)) (fun h => hel (Subtype.ext h)))
  unfold rayGermColor
  calc
    _ = (rayParity a b x p + rayParity a b x p) +
        ((∑ e, if rayEndpoint a b e = p then
          x e.1 * decide (turnArg (rayEndVector a b e) < turnArg (rayEndVector a b k))
          else 0) +
        (∑ e, if rayEndpoint a b e = p then
          x e.1 * decide (turnArg (rayEndVector a b e) < turnArg (rayEndVector a b l))
          else 0)) := by ac_rfl
    _ = x k.1 := by
      rw [BooleanRing.add_self, zero_add, hrestrict, hrestrict]
      exact hsum

end Cslib.Polygonal
