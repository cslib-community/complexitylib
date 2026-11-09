/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.MatchingPencil
public import Complexity.Foundations.Combinatorics.Expander.PathInterpolation
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.Linarith

/-!
# Eigenvalue exclusion for paths attached along a matching

The finite certificate is stated directly in the generalized eigenvector equations. A core has
degree matrix `D = 3 I - P` and Laplacian `L`; a path of length `ℓ` joins each matched pair.
An eigenmode with eigenvalue `cos θ` has internal recurrence
`x j + x (j+2) = 2 cos θ x (j+1)` and core equation
`(D - L) f + P x₁ = 3 cos θ f`.

Path interpolation eliminates the internal coordinates. The matching-pencil theorem then rules
out a nonzero mode when the core gap exceeds `2 sin θ / sin (ℓ θ) + 3 (1 - cos θ)`.
The conclusion includes all internal coordinates, so modes supported only on the added paths
are also excluded whenever `sin (ℓ θ) ≠ 0`.

This interface allows the two orientations of each matching path to be indexed by their core
endpoints. It proves the finite system of eigenvector equations impossible; a separate graph
construction can supply those equations. No explicit family or asymptotic existence statement
is asserted here.

## Main results

* `Cslib.matchingPath_mode_eq_zero`: exclusion near the positive end of the spectrum.
* `Cslib.matchingPath_negative_mode_eq_zero`: exclusion near the negative end, with the
  path-length parity derived from alternating signs on the internal coordinates.
* `Cslib.matchingPath_mode_eq_zero_of_uniform_budget`: the two branches on an entire angle
  interval, using only one budget at its cutoff angle.
* `Cslib.matchingPath_neg_one_mode_eq_zero`: the endpoint `-1`, treated separately by affine
  interpolation so that no nonresonance assumption is used there.
-/

public section

namespace Cslib

open Matrix MatchingPencil
open scoped BigOperators

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- A matching-path eigenmode at `cos θ` vanishes if the Laplacian gap of the core exceeds the
explicit path-elimination budget. Both the core and all path interiors are included. -/
theorem matchingPath_mode_eq_zero {L : Matrix V V ℝ} (hL : L.IsSymm)
    (hLone : L *ᵥ (1 : V → ℝ) = 0) (w : V → ℝ) (σ : Equiv.Perm V)
    (hσ : Function.Involutive σ) (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1)
    (hwσ : ∀ v, w (σ v) = w v) (hwpos : 0 < ∑ v, w v)
    {μ θ : ℝ} {ℓ : ℕ}
    (hgap : ∀ z : V → ℝ, (1 : V → ℝ) ⬝ᵥ z = 0 → μ * (z ⬝ᵥ z) ≤ z ⬝ᵥ L *ᵥ z)
    (hSin : Real.sin ((ℓ : ℝ) * θ) ≠ 0)
    (hq : 0 < Real.sin θ / Real.sin ((ℓ : ℝ) * θ))
    (hc : Real.cos ((ℓ : ℝ) * θ) < 1)
    (hbudget : 2 * (Real.sin θ / Real.sin ((ℓ : ℝ) * θ)) + 3 * (1 - Real.cos θ) < μ)
    (f : V → ℝ) (x : V → ℕ → ℝ)
    (hrec : ∀ v, ExpanderPath.Recurrence ℓ (Real.cos θ) (x v))
    (hstart : ∀ v, x v 0 = f v) (hend : ∀ v, x v ℓ = f (σ v))
    (hcore : ∀ v, ((coreDegree w - L) *ᵥ f) v + w v * x v 1 =
      3 * Real.cos θ * f v) :
    f = 0 ∧ ∀ v j, j ≤ ℓ → x v j = 0 := by
  have hfirst (v : V) : x v 1 = Real.cos θ * f v +
      (Real.sin θ / Real.sin ((ℓ : ℝ) * θ)) *
        (f (σ v) - Real.cos ((ℓ : ℝ) * θ) * f v) := by
    simpa only [hstart, hend] using (hrec v).first_eq hSin
  have hker : pencil L w σ (Real.sin θ / Real.sin ((ℓ : ℝ) * θ))
      (Real.cos ((ℓ : ℝ) * θ)) (-1) (1 - Real.cos θ) *ᵥ f = 0 := by
    ext v
    have hv := hcore v
    rw [hfirst] at hv
    simp only [sub_mulVec, Pi.sub_apply, coreDegree, mulVec_diagonal] at hv
    simp only [pencil, sub_mulVec, add_mulVec, smul_mulVec, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, coreDegree, mulVec_diagonal, weightedMatching_mulVec,
      Pi.zero_apply]
    nlinarith [hv]
  have hf : f = 0 := by
    apply laplacianPencil_injective hL hLone w σ hσ hw0 hw1 hwσ hwpos hgap hq
      (Real.abs_cos_le_one _) hc (sub_nonneg.mpr (Real.cos_le_one _)) hbudget
    simpa only [mulVec_zero] using hker
  refine ⟨hf, fun v j hj => ?_⟩
  apply (hrec v).eq_zero_of_endpoints hSin _ _ hj
  · simp [hstart, hf]
  · simp [hend, hf]

/-- The corresponding certificate near `-1`. Alternating the signs of the path coordinates
changes their recurrence to `cos θ`, and yields the parity factor `(-1)^(ℓ+1)` in the core
pencil. The assumed gap belongs to the signless core matrix `2 D - L`. -/
theorem matchingPath_negative_mode_eq_zero (L : Matrix V V ℝ) (w : V → ℝ)
    (σ : Equiv.Perm V) (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1)
    (hwσ : ∀ v, w (σ v) = w v) {ν θ : ℝ} {ℓ : ℕ}
    (hgap : ∀ z : V → ℝ,
      ν * (z ⬝ᵥ z) ≤ z ⬝ᵥ ((2 : ℝ) • coreDegree w - L) *ᵥ z)
    (hSin : Real.sin ((ℓ : ℝ) * θ) ≠ 0)
    (hq : 0 ≤ Real.sin θ / Real.sin ((ℓ : ℝ) * θ))
    (hbudget : 2 * (Real.sin θ / Real.sin ((ℓ : ℝ) * θ)) + 3 * (1 - Real.cos θ) < ν)
    (f : V → ℝ) (x : V → ℕ → ℝ)
    (hrec : ∀ v, ExpanderPath.Recurrence ℓ (-Real.cos θ) (x v))
    (hstart : ∀ v, x v 0 = f v) (hend : ∀ v, x v ℓ = f (σ v))
    (hcore : ∀ v, ((coreDegree w - L) *ᵥ f) v + w v * x v 1 =
      -3 * Real.cos θ * f v) :
    f = 0 ∧ ∀ v j, j ≤ ℓ → x v j = 0 := by
  let y : V → ℕ → ℝ := fun v j => (-1) ^ j * x v j
  have hyrec (v : V) : ExpanderPath.Recurrence ℓ (Real.cos θ) (y v) := by
    intro j hj
    have heq := congrArg (fun a : ℝ => (-1) ^ j * a) (hrec v j hj)
    simp only [y, pow_add, pow_one, neg_one_sq, mul_one]
    nlinarith [heq]
  have hfirst (v : V) :
      -x v 1 = Real.cos θ * f v + (Real.sin θ / Real.sin ((ℓ : ℝ) * θ)) *
        ((-1) ^ ℓ * f (σ v) - Real.cos ((ℓ : ℝ) * θ) * f v) := by
    simpa only [y, pow_one, pow_zero, one_mul, neg_one_mul, hstart, hend] using
      (hyrec v).first_eq hSin
  have hker : pencil ((2 : ℝ) • coreDegree w - L) w σ
      (Real.sin θ / Real.sin ((ℓ : ℝ) * θ)) (Real.cos ((ℓ : ℝ) * θ))
        ((-1) ^ (ℓ + 1)) (1 - Real.cos θ) *ᵥ f = 0 := by
    ext v
    have hv := hcore v
    have hf := congrArg (fun a : ℝ => w v * a) (hfirst v)
    simp only [sub_mulVec, Pi.sub_apply, coreDegree, mulVec_diagonal] at hv
    simp only [pencil, sub_mulVec, add_mulVec, smul_mulVec, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, coreDegree, mulVec_diagonal, weightedMatching_mulVec,
      Pi.zero_apply, pow_succ]
    nlinarith [hv, hf]
  have hf : f = 0 := by
    apply signlessPencil_injective ((2 : ℝ) • coreDegree w - L) w σ hw0 hw1 hwσ hgap hq
      (c := Real.cos ((ℓ : ℝ) * θ)) (s := (-1) ^ (ℓ + 1))
      (Real.abs_cos_le_one _) (by simp) (sub_nonneg.mpr (Real.cos_le_one _)) hbudget
    simpa only [mulVec_zero] using hker
  refine ⟨hf, fun v j hj => ?_⟩
  have hy : y v j = 0 := (hyrec v).eq_zero_of_endpoints hSin
    (by simp [y, hstart, hf]) (by simp [y, hend, hf]) hj
  exact (mul_eq_zero.mp hy).resolve_left (pow_ne_zero _ (by norm_num))

/-- The endpoint eigenvalue `-1` is excluded by a signless core gap greater than `2 / ℓ`.
Alternating signs give an affine path recurrence, so this theorem remains applicable at angle
zero, where the sine denominator vanishes. -/
theorem matchingPath_neg_one_mode_eq_zero (L : Matrix V V ℝ) (w : V → ℝ)
    (σ : Equiv.Perm V) (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1)
    (hwσ : ∀ v, w (σ v) = w v) {ν : ℝ} {ℓ : ℕ} (hℓ : 0 < ℓ)
    (hgap : ∀ z : V → ℝ,
      ν * (z ⬝ᵥ z) ≤ z ⬝ᵥ ((2 : ℝ) • coreDegree w - L) *ᵥ z)
    (hbudget : 2 / (ℓ : ℝ) < ν) (f : V → ℝ) (x : V → ℕ → ℝ)
    (hrec : ∀ v, ExpanderPath.Recurrence ℓ (-1) (x v))
    (hstart : ∀ v, x v 0 = f v) (hend : ∀ v, x v ℓ = f (σ v))
    (hcore : ∀ v, ((coreDegree w - L) *ᵥ f) v + w v * x v 1 = -3 * f v) :
    f = 0 ∧ ∀ v j, j ≤ ℓ → x v j = 0 := by
  let y : V → ℕ → ℝ := fun v j => (-1) ^ j * x v j
  have hyrec (v : V) : ExpanderPath.Recurrence ℓ 1 (y v) := by
    intro j hj
    have heq := congrArg (fun a : ℝ => (-1) ^ j * a) (hrec v j hj)
    simp only [y, pow_add, pow_one, neg_one_sq, mul_one]
    nlinarith [heq]
  have hfirst (v : V) :
      -x v 1 = f v + ((-1) ^ ℓ * f (σ v) - f v) / (ℓ : ℝ) := by
    simpa only [y, pow_one, pow_zero, one_mul, neg_one_mul, hstart, hend] using
      (hyrec v).first_eq_of_one hℓ
  have hker : pencil ((2 : ℝ) • coreDegree w - L) w σ (1 / (ℓ : ℝ)) 1
      ((-1) ^ (ℓ + 1)) 0 *ᵥ f = 0 := by
    ext v
    have hv := hcore v
    have hf := congrArg (fun a : ℝ => w v * a) (hfirst v)
    simp only [sub_mulVec, Pi.sub_apply, coreDegree, mulVec_diagonal] at hv
    simp only [div_eq_mul_inv] at hf
    simp only [pencil, sub_mulVec, add_mulVec, smul_mulVec, Pi.sub_apply, Pi.add_apply,
      Pi.smul_apply, smul_eq_mul, coreDegree, mulVec_diagonal, weightedMatching_mulVec,
      Pi.zero_apply, pow_succ, div_eq_mul_inv, one_mul, zero_mul, sub_zero]
    nlinarith [hv, hf]
  have hbudget' : 2 * (1 / (ℓ : ℝ)) + 3 * 0 < ν := by
    convert hbudget using 1; ring
  have hf : f = 0 := by
    apply signlessPencil_injective ((2 : ℝ) • coreDegree w - L) w σ hw0 hw1 hwσ hgap
      (q := 1 / (ℓ : ℝ)) (c := 1) (s := (-1) ^ (ℓ + 1)) (δ := 0)
      (by positivity) (by norm_num) (by simp) (le_refl 0) hbudget'
    simpa only [mulVec_zero] using hker
  refine ⟨hf, fun v j hj => ?_⟩
  have hy : y v j = 0 := (hyrec v).eq_zero_of_endpoints_of_one hℓ
    (by simp [y, hstart, hf]) (by simp [y, hend, hf]) hj
  exact (mul_eq_zero.mp hy).resolve_left (pow_ne_zero _ (by norm_num))

/-- **Uniform finite matching-path certificate.** If
`2 τ / (ℓ sin τ) + 3 τ² / (2 ℓ²) < min μ ν` for `τ < π`, every path mode at `±cos θ`
with `0 < ℓ θ ≤ τ` vanishes. The two gap hypotheses concern the Laplacian and signless
Laplacian of the core respectively. -/
theorem matchingPath_mode_eq_zero_of_uniform_budget {L : Matrix V V ℝ} (hL : L.IsSymm)
    (hLone : L *ᵥ (1 : V → ℝ) = 0) (w : V → ℝ) (σ : Equiv.Perm V)
    (hσ : Function.Involutive σ) (hw0 : ∀ v, 0 ≤ w v) (hw1 : ∀ v, w v ≤ 1)
    (hwσ : ∀ v, w (σ v) = w v) (hwpos : 0 < ∑ v, w v)
    {μ ν θ τ r : ℝ} {ℓ : ℕ} (hℓ : 1 ≤ ℓ) (hθ : 0 < θ)
    (hθτ : (ℓ : ℝ) * θ ≤ τ) (hτπ : τ < Real.pi)
    (hgap : ∀ z : V → ℝ, (1 : V → ℝ) ⬝ᵥ z = 0 → μ * (z ⬝ᵥ z) ≤ z ⬝ᵥ L *ᵥ z)
    (hQgap : ∀ z : V → ℝ,
      ν * (z ⬝ᵥ z) ≤ z ⬝ᵥ ((2 : ℝ) • coreDegree w - L) *ᵥ z)
    (hbudget : 2 * τ / ((ℓ : ℝ) * Real.sin τ) + 3 * τ ^ 2 / (2 * (ℓ : ℝ) ^ 2) < min μ ν)
    (hr : r = Real.cos θ ∨ r = -Real.cos θ) (f : V → ℝ) (x : V → ℕ → ℝ)
    (hrec : ∀ v, ExpanderPath.Recurrence ℓ r (x v))
    (hstart : ∀ v, x v 0 = f v) (hend : ∀ v, x v ℓ = f (σ v))
    (hcore : ∀ v, ((coreDegree w - L) *ᵥ f) v + w v * x v 1 = 3 * r * f v) :
    f = 0 ∧ ∀ v j, j ≤ ℓ → x v j = 0 := by
  have hℓone : (1 : ℝ) ≤ ℓ := by exact_mod_cast hℓ
  have hℓpos : (0 : ℝ) < ℓ := lt_of_lt_of_le zero_lt_one hℓone
  have hangle : 0 < (ℓ : ℝ) * θ := mul_pos hℓpos hθ
  have hangleπ : (ℓ : ℝ) * θ < Real.pi := hθτ.trans_lt hτπ
  have hθangle : θ ≤ (ℓ : ℝ) * θ := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hℓone hθ.le
  have hsin : 0 < Real.sin ((ℓ : ℝ) * θ) :=
    Real.sin_pos_of_pos_of_lt_pi hangle hangleπ
  have hq : 0 < Real.sin θ / Real.sin ((ℓ : ℝ) * θ) :=
    div_pos (Real.sin_pos_of_pos_of_lt_pi hθ (hθangle.trans_lt hangleπ)) hsin
  have hc : Real.cos ((ℓ : ℝ) * θ) < 1 := by
    simpa only [Real.cos_zero] using
      Real.cos_lt_cos_of_nonneg_of_le_pi (le_refl 0) hangleπ.le hangle
  have hb := (ExpanderPath.perturbationBudget_le hℓpos hθ hθτ hτπ).trans_lt hbudget
  rcases hr with rfl | rfl
  · exact matchingPath_mode_eq_zero hL hLone w σ hσ hw0 hw1 hwσ hwpos hgap hsin.ne'
      hq hc (lt_min_iff.mp hb).1 f x hrec hstart hend hcore
  · apply matchingPath_negative_mode_eq_zero L w σ hw0 hw1 hwσ hQgap hsin.ne' hq.le
      (lt_min_iff.mp hb).2 f x hrec hstart hend
    intro v
    rw [hcore]
    ring

end Cslib
