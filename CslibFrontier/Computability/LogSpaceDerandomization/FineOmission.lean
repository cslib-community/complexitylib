/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.ScheduledFineProductMean

/-!
# True mass of omitted fine bins

The deterministic nonnegative contribution has entries bounded by `Cb * b` and row mass
bounded by `R`. Actual source and terminal hit densities are bounded by fixed multiples of
`u` and `a`. These hypotheses give the cubic fourth-moment omission cost of
[OpenAI2026LogSpace, Lemma 7.4], printed p. 37, revision `7ef5c0cc`.

The separate schedule tail estimate uses exact integer logarithmic offsets and the cutoff
`c * (1 + |h|)`. It is the wholly omitted-scale calculation in Lemma 7.6, pp. 40--41.
Fourth moments replace the source's eighth moments. No stochastic true-mean identity or
substochasticity of a hierarchy product is assumed to follow from these finite estimates.

## Main results

* `Cslib.rowNormPow_fine_omission_le`: the deterministic true-mass fourth moment.
* `Cslib.LogSpaceEstimation.sum_fine_omission_norm_le`: the total omitted-table norm bound.
* `Cslib.LogSpaceEstimation.omission_tail_le_parent`: activity pays the omission tail.
-/

public section

open Finset
open scoped BigOperators

namespace Cslib

/-- Fine omission from actual true mass. Source and terminal seeds are separate, while the
true contribution is deterministic. Empty source slices and zero true mass are allowed. -/
theorem rowNormPow_fine_omission_le {Γ Υ V : Type*}
    [Fintype Γ] [Fintype Υ] [Fintype V]
    (X : Γ → V → Prop) (Y : Υ → V → Prop)
    [∀ γ x, Decidable (X γ x)] [∀ τ y, Decidable (Y τ y)]
    {N u a b Cu Ca Cb R : ℝ} (hN : 0 < N) (hu : 0 < u) (ha : 0 < a)
    (hb : 0 ≤ b) (hCu : 0 ≤ Cu) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hR : 0 ≤ R)
    (hcard : (Fintype.card V : ℝ) ≤ N)
    (hX : ∀ x, (dens {γ | X γ x} : ℝ) ≤ Cu * u)
    (hY : ∀ y, (dens {τ | Y τ y} : ℝ) ≤ Ca * a)
    (H : V → V → ℝ) (hH : ∀ x y, 0 ≤ H x y)
    (hentry : ∀ x y, H x y ≤ Cb * b) (hrow : ∀ x, ∑ y, H x y ≤ R) :
    rowNormPow 4 N u (fun (σ : Γ × Υ) x => X σ.1 x) (fun σ y => Y σ.2 y)
      (fun _ x y => H x y / a) ≤ Cu * Ca * Cb ^ 3 * R * (b / a) ^ 3 := by
  classical
  have hpoint (x y : V) : |H x y / a| ^ 4 ≤ (Cb * b) ^ 3 * H x y / a ^ 4 := by
    rw [abs_of_nonneg (div_nonneg (hH x y) ha.le), div_pow]
    apply div_le_div_of_nonneg_right _ (by positivity)
    calc
      H x y ^ 4 = H x y ^ 3 * H x y := by ring
      _ ≤ (Cb * b) ^ 3 * H x y :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hH x y) (hentry x y) 3) (hH x y)
  have hdens (x y : V) :
      (dens {σ : Γ × Υ | X σ.1 x ∧ Y σ.2 y} : ℝ) ≤ (Cu * u) * (Ca * a) := by
    rw [dens_source_terminal]
    exact mul_le_mul (hX x) (hY y) (by positivity) (by positivity)
  rw [rowNormPow_const_eq_dens_sum]
  calc
    _ ≤ (N * u)⁻¹ * ∑ x, ∑ y, (Cu * u * (Ca * a)) *
        ((Cb * b) ^ 3 * H x y / a ^ 4) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact sum_le_sum fun x _ => sum_le_sum fun y _ =>
        mul_le_mul (hdens x y) (hpoint x y) (by positivity) (by positivity)
    _ = (N * u)⁻¹ * (Cu * u * (Ca * a) * (Cb * b) ^ 3 / a ^ 4) *
        ∑ x, ∑ y, H x y := by simp only [← mul_sum, ← sum_div]; ring
    _ ≤ (N * u)⁻¹ * (Cu * u * (Ca * a) * (Cb * b) ^ 3 / a ^ 4) *
        ((Fintype.card V : ℝ) * R) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa using sum_le_sum (fun x (_ : x ∈ (univ : Finset V)) => hrow x)
    _ ≤ (N * u)⁻¹ * (Cu * u * (Ca * a) * (Cb * b) ^ 3 / a ^ 4) * (N * R) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcard hR) (by positivity)
    _ = _ := by field_simp

end Cslib

namespace Cslib.LogSpaceEstimation

/-- A wholly omitted fine scale has an exponentially small norm cost. This uses the exact
integer cutoff, including equality at the boundary, without a rounding assumption. -/
theorem omitted_fine_cost_le (M c : ℕ) (hc : 0 < c) (h : ℤ) (hh : h < 0)
    (homit : M ≤ scaleCutoff c h) :
    binNormCost 4 (h : ℝ) ≤
      (2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) * scaleMajorant h := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hhR : (h : ℝ) < 0 := by exact_mod_cast hh
  have habs : (h.natAbs : ℝ) = -(h : ℝ) := by
    have heq : |(h : ℝ)| = (h.natAbs : ℝ) := by simp
    rw [abs_of_neg hhR] at heq
    exact heq.symm
  have hcut : (M : ℝ) ≤ c * (1 + (h.natAbs : ℝ)) := by
    exact_mod_cast homit
  have hbudget : (M : ℝ) / (2 * c) ≤ (1 + (h.natAbs : ℝ)) / 2 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * c)).2
    nlinarith
  rw [binNormCost, ite_eq_right (not_le.mpr hhR), scaleMajorant,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [habs] at hbudget ⊢
  linarith

/-- The sum of all actual omitted fine-bin norm costs is bounded independently of the number
of bins. The exponential budget tail multiplies the same convergent scale majorant as the
available-child estimates. -/
theorem sum_omitted_fine_cost_le (M c : ℕ) (hc : 0 < c) (S : Finset ℤ)
    (hfine : ∀ h ∈ S, h < 0) (homit : ∀ h ∈ S, M ≤ scaleCutoff c h) :
    ∑ h ∈ S, binNormCost 4 (h : ℝ) ≤
      (2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) *
        (2 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 8)) - 1) := by
  calc
    _ ≤ ∑ h ∈ S, (2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) * scaleMajorant h :=
      sum_le_sum fun h hh => omitted_fine_cost_le M c hc h (hfine h hh) (homit h hh)
    _ = (2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) * ∑ h ∈ S, scaleMajorant h :=
      (mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) * ∑' h, scaleMajorant h :=
      mul_le_mul_of_nonneg_left
        (summable_scaleMajorant.sum_le_tsum S (fun h _ => scaleMajorant_nonneg h)) (by positivity)
    _ = _ := by rw [tsum_scaleMajorant]

/-- Activity makes the entire omission tail smaller than parent accuracy with an additional
rank reserve `2^(-A)`. Thus its coefficient can be made small by increasing `A`, as in the
wholly omitted-scales part of Lemma 7.6. -/
theorem omission_tail_le_parent {A a u : ℝ} (M c i : ℕ) (hc : 0 < c)
    (hA : 1 ≤ A) (hi : 1 ≤ i) (ha : 0 < a) (ha1 : a ≤ 1)
    (hu : 0 < u) (hu1 : u ≤ 1)
    (hactive : 0 < precision (16 * c) A M i a u) :
    (2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) ≤
      (2 : ℝ) ^ (-precision (16 * c) A M i a u - A) := by
  have hcR : (0 : ℝ) < c := by exact_mod_cast hc
  have hiR : (1 : ℝ) ≤ i := by exact_mod_cast hi
  have hAi : A ≤ A * i := le_mul_of_one_le_right (by linarith) hiR
  have hla := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) ha.le ha1
  have hlu := Real.logb_nonpos (by norm_num : (1 : ℝ) < 2) hu.le hu1
  have hp : precision (16 * c) A M i a u ≤ (M : ℝ) / (16 * c) - A := by
    dsimp only [precision]
    linarith
  have hratio : (M : ℝ) / (2 * c) = 8 * ((M : ℝ) / (16 * c)) := by field_simp; ring
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
  rw [hratio]
  linarith

/-- Omitted deterministic tables have a uniformly summable total norm, derived from their
entry and row-mass bounds, rather than an assumed per-bin error certificate. This is the
omission contribution to Minkowski in the mean-prefix argument. -/
theorem sum_fine_omission_norm_le {Γ Υ V : Type*}
    [Fintype Γ] [Fintype Υ] [Fintype V]
    (X : Γ → V → Prop) (Y : Υ → V → Prop)
    [∀ γ x, Decidable (X γ x)] [∀ τ y, Decidable (Y τ y)]
    {N u a Cu Ca Cb R K : ℝ} (hN : 0 < N) (hu : 0 < u) (ha : 0 < a)
    (hCu : 0 ≤ Cu) (hCa : 0 ≤ Ca) (hCb : 0 ≤ Cb) (hR : 0 ≤ R) (hK : 0 ≤ K)
    (hconstant : Cu * Ca * Cb ^ 3 * R ≤ K ^ 4)
    (hcard : (Fintype.card V : ℝ) ≤ N)
    (hX : ∀ x, (dens {γ | X γ x} : ℝ) ≤ Cu * u)
    (hY : ∀ y, (dens {τ | Y τ y} : ℝ) ≤ Ca * a)
    (M c : ℕ) (hc : 0 < c) (S : Finset ℤ)
    (b : ℤ → ℝ) (H : ℤ → V → V → ℝ)
    (hb : ∀ h ∈ S, 0 < b h) (hfine : ∀ h ∈ S, h < 0)
    (homit : ∀ h ∈ S, M ≤ scaleCutoff c h)
    (hscale : ∀ h ∈ S, Real.logb 2 (b h / a) = (h : ℝ))
    (hH : ∀ h ∈ S, ∀ x y, 0 ≤ H h x y)
    (hentry : ∀ h ∈ S, ∀ x y, H h x y ≤ Cb * b h)
    (hrow : ∀ h ∈ S, ∀ x, ∑ y, H h x y ≤ R) :
    ∑ h ∈ S, (rowNormPow 4 N u (fun (σ : Γ × Υ) x => X σ.1 x)
      (fun σ y => Y σ.2 y) (fun _ x y => H h x y / a)) ^ (4⁻¹ : ℝ) ≤
      K * ((2 : ℝ) ^ (1 / 2 - (M : ℝ) / (2 * c)) *
        (2 / (1 - (2 : ℝ) ^ (-(1 : ℝ) / 8)) - 1)) := by
  have hpoint (h : ℤ) (hh : h ∈ S) :
      (rowNormPow 4 N u (fun (σ : Γ × Υ) x => X σ.1 x)
        (fun σ y => Y σ.2 y) (fun _ x y => H h x y / a)) ^ (4⁻¹ : ℝ) ≤
        K * binNormCost 4 (h : ℝ) := by
    have hmass := rowNormPow_fine_omission_le X Y hN hu ha (hb h hh).le
      hCu hCa hCb hR hcard hX hY (H h) (hH h hh) (hentry h hh) (hrow h hh)
    have hcost := fine_cost_pow_four ha (hb h hh) (by norm_num : (0 : ℝ) < 1)
      (by norm_num : (0 : ℝ) < 1) (hfine h hh) (hscale h hh)
    norm_num only [div_self one_ne_zero, Real.logb_one, zero_div, Real.rpow_zero, mul_one] at hcost
    have hpower : rowNormPow 4 N u (fun (σ : Γ × Υ) x => X σ.1 x)
        (fun σ y => Y σ.2 y) (fun _ x y => H h x y / a) ≤
        (K * binNormCost 4 (h : ℝ)) ^ 4 := by
      rw [mul_pow, hcost]
      exact hmass.trans (mul_le_mul_of_nonneg_right hconstant
        (pow_nonneg (div_nonneg (hb h hh).le ha.le) 3))
    exact (Real.rpow_le_rpow (rowNormPow_nonneg (s := 4) (N := N) (u := u) (by positivity) _) hpower
      (by positivity)).trans_eq (Real.pow_rpow_inv_natCast
        (mul_nonneg hK (binNormCost_pos 4 _).le) (by decide : 4 ≠ 0))
  calc
    _ ≤ ∑ h ∈ S, K * binNormCost 4 (h : ℝ) := sum_le_sum hpoint
    _ = K * ∑ h ∈ S, binNormCost 4 (h : ℝ) := (mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (sum_omitted_fine_cost_le M c hc S hfine homit) hK

end Cslib.LogSpaceEstimation
