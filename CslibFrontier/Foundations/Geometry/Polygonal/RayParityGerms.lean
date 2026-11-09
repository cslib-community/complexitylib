/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Polygonal.RayOrder
public import CslibFrontier.Foundations.Geometry.Polygonal.RayParityTransport

/-!
# Ray crossing at a segment germ

The local crossing contribution of a segment departing from an observation center is
determined by the two height signs and their determinant. The observations use every
sufficiently small positive real parameter; no discretization of the plane is used.
-/

public section

namespace Cslib.Polygonal

/-- Germ contribution for nonhorizontal outgoing and observation vectors `u` and `v`.
Equal rays contribute zero because the horizontal ray excludes its own base point. -/
@[expose] def GermCrosses (u v : ℂ) : Prop :=
  (0 < u.im ∧ 0 < v.im ∧ 0 < u.re * v.im - u.im * v.re) ∨
    (u.im < 0 ∧ v.im < 0 ∧ u.re * v.im - u.im * v.re < 0)

/-- The half-open ray test near a genuine endpoint is the germ determinant test.
The bound on the real observation parameter is constructed by continuity. -/
theorem eventually_rayCrosses_germ (p u v : ℂ) (hu : u.im ≠ 0) (hv : v.im ≠ 0) :
    ∀ᶠ t : ℝ in nhds 0, 0 < t →
      (RayCrosses p (p + u) (p + t • v) ↔ GermCrosses u v) := by
  have hcoord (t : ℝ) : (p + t • v).im = p.im + t * v.im := by
    simp [Complex.real_smul]
  have hdiff (t : ℝ) :
      horizontalIntercept p (p + u) (p + t • v).im - (p + t • v).re =
        t * (u.re * v.im - u.im * v.re) / u.im := by
    simp only [horizontalIntercept, Complex.add_re, Complex.add_im,
      Complex.real_smul, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, zero_mul, sub_zero, add_zero]
    ring_nf
    field_simp
  have hcont : ContinuousAt (fun t : ℝ => (p + t • v).im) 0 := by fun_prop
  rcases lt_or_gt_of_ne hu with hun | hup
  · have hevent : ∀ᶠ t : ℝ in nhds 0, p.im + u.im < (p + t • v).im :=
      continuousAt_const.eventually_lt hcont (by simp only [zero_smul, add_zero]; linarith)
    filter_upwards [hevent] with t ht htpos
    have hside : (p + t • v).re < horizontalIntercept p (p + u) (p + t • v).im ↔
        u.re * v.im - u.im * v.re < 0 := by
      rw [← sub_pos, hdiff, div_pos_iff]
      have hmul : t * (u.re * v.im - u.im * v.re) < 0 ↔
          u.re * v.im - u.im * v.re < 0 := by
        constructor <;> intro h <;> nlinarith
      simp [hun, not_lt_of_ge hun.le, hmul]
    have hlow : (p + t • v).im < p.im ↔ v.im < 0 := by
      rw [hcoord]
      constructor <;> intro h <;> nlinarith
    have hup' : p.im + u.im < p.im := by linarith
    unfold RayCrosses
    rw [Complex.add_im p u, min_eq_right hup'.le, max_eq_left hup'.le]
    simp only [ht.le, true_and, hlow, hside]
    simp [GermCrosses, hun, not_lt_of_ge hun.le]
  · have hevent : ∀ᶠ t : ℝ in nhds 0, (p + t • v).im < p.im + u.im :=
      hcont.eventually_lt continuousAt_const (by simp only [zero_smul, add_zero]; linarith)
    filter_upwards [hevent] with t ht htpos
    have hside : (p + t • v).re < horizontalIntercept p (p + u) (p + t • v).im ↔
        0 < u.re * v.im - u.im * v.re := by
      rw [← sub_pos, hdiff, div_pos_iff]
      have hmul : 0 < t * (u.re * v.im - u.im * v.re) ↔
          0 < u.re * v.im - u.im * v.re := mul_pos_iff_of_pos_left htpos
      simp [hup, not_lt_of_ge hup.le, hmul]
    have hlow : p.im ≤ (p + t • v).im ↔ 0 < v.im := by
      rw [hcoord]
      constructor
      · intro h
        rcases lt_or_gt_of_ne hv with hneg | hpos
        · nlinarith
        · exact hpos
      · intro h
        nlinarith
    have hup' : p.im < p.im + u.im := by linarith
    unfold RayCrosses
    rw [Complex.add_im p u, min_eq_left hup'.le, max_eq_right hup'.le]
    simp only [ht, hlow, hside]
    simp [GermCrosses, hup, not_lt_of_ge hup.le]

/-- In either open half-plane, the local crossing is the strict angular interval
from the cut to the observation ray, with the inequality reversed below the cut. -/
theorem germCrosses_iff_turnArg {u v : ℂ} (hu : u.im ≠ 0) (hv : v.im ≠ 0) :
    GermCrosses u v ↔
      (0 < u.im ∧ 0 < v.im ∧ turnArg u < turnArg v) ∨
        (u.im < 0 ∧ v.im < 0 ∧ turnArg v < turnArg u) := by
  rw [GermCrosses, turnArg_lt_iff hu hv, turnArg_lt_iff hv hu]
  by_cases hun : u.im < 0 <;> by_cases hvn : v.im < 0
  · have hu' : ¬0 < u.im := not_lt_of_ge hun.le
    have hv' : ¬0 < v.im := not_lt_of_ge hvn.le
    simp only [hun, hvn, hu', hv', true_and, false_and, false_or, iff_self]
    constructor <;> intro h <;> nlinarith
  · have hu' : ¬0 < u.im := not_lt_of_ge hun.le
    simp [hun, hvn, hu']
  · have hv' : ¬0 < v.im := not_lt_of_ge hvn.le
    simp [hun, hvn, hv']
  · have hu' : 0 < u.im := lt_of_le_of_ne (le_of_not_gt hun) hu.symm
    have hv' : 0 < v.im := lt_of_le_of_ne (le_of_not_gt hvn) hv.symm
    simp [hun, hvn, hu', hv']

open Classical in
/-- Correcting the descending observation ray itself turns the germ crossing bit into
the angular prefix bit, plus one common descending-half-plane bit. Even incidence cancels
that common bit when the contributions at a vertex are summed. -/
theorem germCrosses_prefix_identity {u v : ℂ} (hu : u.im ≠ 0) (hv : v.im ≠ 0) :
    decide (GermCrosses u v) +
        decide (turnArg u = turnArg v ∧ v.im < 0) =
      decide (turnArg u < turnArg v) + decide (v.im < 0) := by
  rw [germCrosses_iff_turnArg hu hv]
  by_cases hun : u.im < 0 <;> by_cases hvn : v.im < 0
  · have hu' : ¬0 < u.im := not_lt_of_ge hun.le
    have hv' : ¬0 < v.im := not_lt_of_ge hvn.le
    rcases lt_trichotomy (turnArg u) (turnArg v) with h | h | h
    · simp [hun, hvn, hu', hv', h, ne_of_lt h, not_lt.mpr h.le, Bool.add_eq_xor]
    · simp [hun, hvn, hu', hv', h, Bool.add_eq_xor]
    · simp [hun, hvn, hu', hv', h, ne_of_gt h, not_lt.mpr h.le, Bool.add_eq_xor]
  · have hu' : ¬0 < u.im := not_lt_of_ge hun.le
    have hv' : 0 < v.im := lt_of_le_of_ne (le_of_not_gt hvn) hv.symm
    have hgt : turnArg v < turnArg u := (turnArg_lt_iff hv hu).mpr
      (Or.inl ⟨hv', hun⟩)
    simp [hun, hvn, hu', hv', not_lt_of_ge hgt.le]
  · have hu' : 0 < u.im := lt_of_le_of_ne (le_of_not_gt hun) hu.symm
    have hv' : ¬0 < v.im := not_lt_of_ge hvn.le
    have hlt : turnArg u < turnArg v := (turnArg_lt_iff hu hv).mpr
      (Or.inl ⟨hu', hvn⟩)
    simp [hun, hvn, hu', hv', hlt, ne_of_lt hlt, Bool.add_eq_xor]
  · have hu' : 0 < u.im := lt_of_le_of_ne (le_of_not_gt hun) hu.symm
    have hv' : 0 < v.im := lt_of_le_of_ne (le_of_not_gt hvn) hv.symm
    simp [hun, hvn, hu', hv']

open Classical in
/-- The change of ray parity on leaving an arrangement endpoint along an actual ray
is the sum of its incident germ contributions. Remote segments are constant near the
center. Their endpoint heights and support are explicitly separated here. -/
theorem eventually_rayParity_germ {ι : Type*} [Fintype ι]
    (a b : ι → ℂ) (x : ι → Bool) (hheight : ∀ i, (a i).im ≠ (b i).im)
    (p v : ℂ) (hv : v.im ≠ 0)
    (hremote : ∀ i, a i ≠ p → b i ≠ p →
      p.im ≠ (a i).im ∧ p.im ≠ (b i).im ∧ p ∉ segment ℝ (a i) (b i)) :
    ∀ᶠ t : ℝ in nhds 0, 0 < t →
      rayParity a b x (p + t • v) = rayParity a b x p +
        ∑ i, ((if a i = p then (if GermCrosses (b i - p) v then x i else 0) else 0) +
          (if b i = p then (if GermCrosses (a i - p) v then x i else 0) else 0)) := by
  classical
  have hterm (i : ι) : ∀ᶠ t : ℝ in nhds 0, 0 < t →
      (if RayCrosses (a i) (b i) (p + t • v) then x i else 0) =
        (if RayCrosses (a i) (b i) p then x i else 0) +
          ((if a i = p then (if GermCrosses (b i - p) v then x i else 0) else 0) +
            (if b i = p then (if GermCrosses (a i - p) v then x i else 0) else 0)) := by
    by_cases ha : a i = p
    · have hb : b i ≠ p := fun hb => hheight i (by rw [ha, hb])
      have hu : (b i - p).im ≠ 0 := by
        rw [Complex.sub_im, sub_ne_zero]
        exact fun h => hheight i (by rw [ha, h])
      filter_upwards [eventually_rayCrosses_germ p (b i - p) v hu hv] with t ht hpos
      have hw : RayCrosses (a i) (b i) (p + t • v) ↔ GermCrosses (b i - p) v := by
        simpa only [ha, add_sub_cancel] using ht hpos
      have hp : ¬RayCrosses (a i) (b i) p := by
        simpa only [ha, AffineMap.lineMap_apply_zero] using
          not_rayCrosses_lineMap (hheight i) 0
      rw [hw, ite_eq_right hp]
      simp only [ha, hb, ↓reduceIte, add_zero, zero_add]
    · by_cases hb : b i = p
      · have hu : (a i - p).im ≠ 0 := by
          rw [Complex.sub_im, sub_ne_zero]
          exact fun h => hheight i (by rw [hb, h])
        filter_upwards [eventually_rayCrosses_germ p (a i - p) v hu hv] with t ht hpos
        have hw : RayCrosses (a i) (b i) (p + t • v) ↔ GermCrosses (a i - p) v := by
          simpa only [hb, add_sub_cancel, rayCrosses_reverse] using ht hpos
        have hp : ¬RayCrosses (a i) (b i) p := by
          rw [← rayCrosses_reverse, hb]
          simpa only [hb, AffineMap.lineMap_apply_zero] using
            not_rayCrosses_lineMap (hheight i).symm 0
        rw [hw, ite_eq_right hp]
        simp only [ha, hb, ↓reduceIte, zero_add]
      · obtain ⟨hpa, hpb, hp⟩ := hremote i ha hb
        have hcont : ContinuousAt (fun t : ℝ => p + t • v) 0 := by fun_prop
        have hconst := hcont.eventually
          (by simpa only [zero_smul, add_zero] using
            eventually_rayCrosses_iff_of_not_mem_segment (a i) (b i) p hpa hpb hp)
        filter_upwards [hconst] with t ht _
        simp only [ht, ha, hb, ↓reduceIte, add_zero]
  filter_upwards [Filter.eventually_all.mpr hterm] with t ht hpos
  simp only [rayParity, fun i => ht i hpos, Finset.sum_add_distrib]

end Cslib.Polygonal
