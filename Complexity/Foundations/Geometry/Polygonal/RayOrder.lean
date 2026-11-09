/-
Copyright (c) 2026 Erik Demaine, OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, OpenAI
-/

module
-- upstream: candidate

public import Complexity.Foundations.Geometry.Polygonal.LocalSplitOrder
public import Mathlib.Algebra.Ring.BooleanRing

/-!
# Ordering nonhorizontal rays from the positive horizontal cut

Nonhorizontal vectors have real angular representatives strictly inside one turn.
Within either open half-plane their order is the sign of the real planar determinant.
The cut is auxiliary; the resulting circular order is the existing order on `Real.Angle`.
-/

public section

namespace Cslib.Polygonal

/-- Argument measured counterclockwise from the positive real ray in `[0,2π)`.
For a nonhorizontal vector it lies strictly between the endpoints. -/
@[expose] noncomputable def turnArg (z : ℂ) : ℝ :=
  if z.im < 0 then z.arg + 2 * Real.pi else z.arg

/-- Nonhorizontal vectors avoid the argument cut and its half-turn. -/
theorem arg_mem_half_turn {z : ℂ} (hz : z.im ≠ 0) :
    if z.im < 0 then z.arg ∈ Set.Ioo (-Real.pi) 0
    else z.arg ∈ Set.Ioo 0 Real.pi := by
  split_ifs with h
  · exact ⟨Complex.neg_pi_lt_arg z, Complex.arg_neg_iff.mpr h⟩
  · refine ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.mpr (le_of_not_gt h)) ?_,
      Complex.arg_lt_pi_iff.mpr (Or.inr hz)⟩
    intro hzero
    exact hz (Complex.arg_eq_zero_iff.mp hzero.symm).2

/-- The real representative of a nonhorizontal ray lies inside one full turn. -/
theorem turnArg_mem {z : ℂ} (hz : z.im ≠ 0) :
    turnArg z ∈ Set.Ioo 0 (2 * Real.pi) := by
  have h := arg_mem_half_turn hz
  unfold turnArg
  split_ifs with hneg
  · rw [ite_eq_left hneg] at h
    constructor <;> linarith [h.1, h.2, Real.pi_pos]
  · rw [ite_eq_right hneg] at h
    exact ⟨h.1, h.2.trans (by linarith [Real.pi_pos])⟩

/-- Changing the cut does not change the actual direction as a circular angle. -/
@[simp] theorem turnArg_coe_angle (z : ℂ) :
    (turnArg z : Real.Angle) = z.arg := by
  unfold turnArg
  split_ifs <;> simp [Real.Angle.coe_add]

/-- In either open half-plane, argument comparison is the determinant sign. -/
theorem arg_lt_arg_iff_det_pos {u v : ℂ} (hu : u.im ≠ 0) (hv : v.im ≠ 0)
    (hsame : u.im < 0 ↔ v.im < 0) :
    u.arg < v.arg ↔ 0 < u.re * v.im - u.im * v.re := by
  have hu0 : u ≠ 0 := fun h => hu (congrArg Complex.im h)
  have hv0 : v ≠ 0 := fun h => hv (congrArg Complex.im h)
  have huarg := arg_mem_half_turn hu
  have hvarg := arg_mem_half_turn hv
  have hspan : u.arg - v.arg ∈ Set.Ioc (-Real.pi) Real.pi := by
    by_cases hneg : u.im < 0
    · rw [ite_eq_left hneg] at huarg
      rw [ite_eq_left (hsame.mp hneg)] at hvarg
      constructor <;> linarith [huarg.1, huarg.2, hvarg.1, hvarg.2]
    · rw [ite_eq_right hneg] at huarg
      rw [ite_eq_right (fun h => hneg (hsame.mpr h))] at hvarg
      constructor <;> linarith [huarg.1, huarg.2, hvarg.1, hvarg.2]
  have hdiv : (u / v).arg = u.arg - v.arg := by
    have h := congrArg Real.Angle.toReal (Complex.arg_div_coe_angle hu0 hv0)
    rw [Complex.arg_coe_angle_toReal_eq_arg, ← Real.Angle.coe_sub,
      Real.Angle.toReal_coe_eq_self_iff_mem_Ioc.mpr hspan] at h
    exact h
  have hnorm : 0 < Complex.normSq v := Complex.normSq_pos.mpr hv0
  calc
    u.arg < v.arg ↔ (u / v).arg < 0 := by rw [hdiv, sub_lt_zero]
    _ ↔ (u / v).im < 0 := Complex.arg_neg_iff
    _ ↔ 0 < u.re * v.im - u.im * v.re := by
      rw [Complex.div_im, ← sub_div, div_lt_iff₀ hnorm, zero_mul]
      constructor <;> intro h <;> linarith

/-- Comparison from the positive horizontal cut: upper rays precede lower rays,
and within either half-plane the determinant gives the order. -/
theorem turnArg_lt_iff {u v : ℂ} (hu : u.im ≠ 0) (hv : v.im ≠ 0) :
    turnArg u < turnArg v ↔
      (0 < u.im ∧ v.im < 0) ∨
        ((u.im < 0 ↔ v.im < 0) ∧ 0 < u.re * v.im - u.im * v.re) := by
  have hua := arg_mem_half_turn hu
  have hva := arg_mem_half_turn hv
  by_cases hun : u.im < 0 <;> by_cases hvn : v.im < 0
  · simpa [turnArg, hun, hvn, not_lt_of_ge hun.le] using
      arg_lt_arg_iff_det_pos hu hv (iff_of_true hun hvn)
  · rw [ite_eq_left hun] at hua
    rw [ite_eq_right hvn] at hva
    have hlt : ¬u.arg + 2 * Real.pi < v.arg := by
      linarith [hua.1, hva.2]
    simp [turnArg, hun, hvn, hlt, not_lt_of_ge hun.le]
  · rw [ite_eq_right hun] at hua
    rw [ite_eq_left hvn] at hva
    have hup : 0 < u.im := lt_of_le_of_ne (le_of_not_gt hun) hu.symm
    have hlt : u.arg < v.arg + 2 * Real.pi := by
      linarith [hua.2, hva.1]
    simp [turnArg, hun, hvn, hup, hlt]
  · simpa [turnArg, hun, hvn] using
      arg_lt_arg_iff_det_pos hu hv (iff_of_false hun hvn)

open Classical in
/-- Prefix sums of an even labeling differ by the intervening ray label across an
empty counterclockwise sector. The wrap around the horizontal cut cancels by evenness. -/
theorem sum_angularPrefix_adjacent {ι : Type*} [Fintype ι]
    (θ : ι → ℝ) (x : ι → Bool)
    (hθ : ∀ i, θ i ∈ Set.Ioo 0 (2 * Real.pi)) (hinj : Function.Injective θ)
    (heven : (∑ i, x i) = 0) (k l : ι) (hkl : k ≠ l)
    (hgap : ∀ e, e ≠ k → e ≠ l → ¬sbtw (θ k : Real.Angle) (θ e : Real.Angle)
      (θ l : Real.Angle)) :
    (∑ e, x e * decide (θ e < θ k)) + (∑ e, x e * decide (θ e < θ l)) = x k := by
  classical
  have hθkl : θ k ≠ θ l := fun h => hkl (hinj h)
  have hbit (e : ι) :
      decide (θ e < θ k) + decide (θ e < θ l) =
        (if e = k then 1 else 0) + decide (θ l < θ k) := by
    by_cases hek : e = k
    · subst e
      rcases lt_or_gt_of_ne hθkl with h | h <;>
        simp [h, not_lt.mpr h.le, Bool.add_eq_xor, Bool.one_eq_true]
    by_cases hel : e = l
    · subst e
      simp [hek, Bool.zero_eq_false, Bool.add_eq_xor]
    have hθek : θ e ≠ θ k := fun h => hek (hinj h)
    have hθel : θ e ≠ θ l := fun h => hel (hinj h)
    have hn := hgap e hek hel
    rw [sbtw_angle_iff_cyclic_lt (cut := 0) (by simpa only [zero_add] using hθ k)
      (by simpa only [zero_add] using hθ e) (by simpa only [zero_add] using hθ l)
      hθek.symm hθel hθkl] at hn
    by_cases h1 : θ e < θ k <;> by_cases h2 : θ e < θ l <;>
      by_cases h3 : θ l < θ k <;>
      simp only [hek, ↓reduceIte, h1, h2, h3, decide_true, decide_false,
        Bool.add_eq_xor, Bool.false_xor, Bool.xor_false, Bool.xor_self, Bool.zero_eq_false]
    all_goals grind
  rw [← Finset.sum_add_distrib]
  simp only [← mul_add]
  simp only [hbit, mul_add]
  rw [Finset.sum_add_distrib, ← Finset.sum_mul, heven, zero_mul, add_zero]
  simp [mul_ite]

/-- Circular angle order is unchanged by a common rotation. -/
theorem sbtw_angle_add_right_iff (a b c t : Real.Angle) :
    sbtw (a + t) (b + t) (c + t) ↔ sbtw a b c := by
  rw [sbtw_iff_not_btw, sbtw_iff_not_btw]
  change ¬((QuotientAddGroup.equivIcoMod Real.two_pi_pos 0 ((b + t) - (c + t)) : ℝ) ≤
    QuotientAddGroup.equivIocMod Real.two_pi_pos 0 ((a + t) - (c + t))) ↔
    ¬((QuotientAddGroup.equivIcoMod Real.two_pi_pos 0 (b - c) : ℝ) ≤
      QuotientAddGroup.equivIocMod Real.two_pi_pos 0 (a - c))
  simp only [add_sub_add_right_eq_sub]

/-- Multiplication by a nonzero complex number preserves literal circular ray order. -/
theorem sbtw_arg_mul_iff (u a b c : ℂ) (hu : u ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    sbtw ((u * a).arg : Real.Angle) ((u * b).arg : Real.Angle)
      ((u * c).arg : Real.Angle) ↔
    sbtw (a.arg : Real.Angle) (b.arg : Real.Angle) (c.arg : Real.Angle) := by
  rw [Complex.arg_mul_coe_angle hu ha, Complex.arg_mul_coe_angle hu hb,
    Complex.arg_mul_coe_angle hu hc]
  simpa only [add_comm] using sbtw_angle_add_right_iff
    (a.arg : Real.Angle) (b.arg : Real.Angle) (c.arg : Real.Angle) (u.arg : Real.Angle)

end Cslib.Polygonal
