/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
# Eliminating the interior of a path

At a degree-two vertex, the normalized adjacency equation with parameter `cos θ` is
`x j + x (j + 2) = 2 * cos θ * x (j + 1)`. When `sin (ℓ * θ) ≠ 0`, its values are
determined by the two endpoints through sine interpolation. A separate affine formula handles
parameter one, including the zero-angle endpoint. This module also proves the first-neighbor
identities used to eliminate added paths.

The recurrence is indexed by natural numbers; it is required only where the three vertices
belong to the path. The interpolation formula uses subtraction in the real numbers, so no
truncated natural subtraction occurs in its trigonometric arguments.

## Main definitions

* `Cslib.ExpanderPath.Recurrence`: the finite second-order path recurrence.
* `Cslib.ExpanderPath.sineInterpolation`: interpolation between the endpoint values.

## Main results

* `Cslib.ExpanderPath.Recurrence.eq_of_initial`: uniqueness from two consecutive values.
* `Cslib.ExpanderPath.Recurrence.first_eq_of_one`: the affine endpoint identity at parameter one.
* `Cslib.ExpanderPath.Recurrence.eq_affine`: endpoint interpolation at parameter one.
* `Cslib.ExpanderPath.Recurrence.first_eq`: the first-neighbor elimination identity.
* `Cslib.ExpanderPath.Recurrence.eq_sineInterpolation`: interpolation from two endpoints.
* `Cslib.ExpanderPath.Recurrence.eq_zero_of_endpoints`: the nonresonant Dirichlet problem.
* `Cslib.ExpanderPath.transferWeight_le`: a uniform bound on the path transfer coefficient.
* `Cslib.ExpanderPath.perturbationBudget_le`: the quantitative bound used by matching pencils.

These are scalar recurrence and trigonometric statements. They do not assert the existence of
a graph family or make a claim about optimal expander constants.
-/

public section

namespace Cslib.ExpanderPath

/-- The adjacency recurrence on a path of length `ℓ`, imposed at its interior vertices. -/
@[expose] def Recurrence (ℓ : ℕ) (c : ℝ) (x : ℕ → ℝ) : Prop :=
  ∀ j : ℕ, j + 2 ≤ ℓ → x j + x (j + 2) = 2 * c * x (j + 1)

/-- Two solutions of the same finite recurrence agree if their first two values agree. -/
theorem Recurrence.eq_of_initial {ℓ : ℕ} {c : ℝ} {x y : ℕ → ℝ}
    (hx : Recurrence ℓ c x) (hy : Recurrence ℓ c y)
    (hzero : x 0 = y 0) (hone : x 1 = y 1) :
    ∀ j : ℕ, j ≤ ℓ → x j = y j := by
  apply Nat.twoStepInduction
  · intro _
    exact hzero
  · intro _
    exact hone
  · intro j ih₀ ih₁ hj
    have h₀ := ih₀ (by omega)
    have h₁ := ih₁ (by omega)
    have hxr := hx j hj
    have hyr := hy j hj
    rw [h₀, h₁] at hxr
    linarith

/-- At parameter one, a path solution is affine in its vertex index. -/
theorem Recurrence.affine_identity {ℓ : ℕ} {x : ℕ → ℝ} (hx : Recurrence ℓ 1 x) :
    ∀ j : ℕ, j ≤ ℓ → x j = x 0 + (j : ℝ) * (x 1 - x 0) := by
  apply Nat.twoStepInduction
  · intro _
    simp
  · intro _
    simp only [Nat.cast_one, one_mul]
    ring
  · intro j ih₀ ih₁ hj
    have h₀ := ih₀ (by omega)
    have h₁ := ih₁ (by omega)
    have hxr := hx j hj
    simp only [Nat.cast_add, Nat.cast_ofNat, Nat.cast_one] at h₀ h₁ ⊢
    linear_combination hxr + 2 * h₁ - h₀

/-- The first-neighbor identity at parameter one, where sine interpolation has a zero
denominator. -/
theorem Recurrence.first_eq_of_one {ℓ : ℕ} {x : ℕ → ℝ}
    (hx : Recurrence ℓ 1 x) (hℓ : 0 < ℓ) :
    x 1 = x 0 + (x ℓ - x 0) / (ℓ : ℝ) := by
  have hℓne : (ℓ : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hℓ)
  have h := hx.affine_identity ℓ (le_refl ℓ)
  field_simp [hℓne]
  nlinarith

/-- Endpoint affine interpolation on a path of positive length at parameter one. -/
theorem Recurrence.eq_affine {ℓ : ℕ} {x : ℕ → ℝ}
    (hx : Recurrence ℓ 1 x) (hℓ : 0 < ℓ) (j : ℕ) (hj : j ≤ ℓ) :
    x j = x 0 + ((j : ℝ) / (ℓ : ℝ)) * (x ℓ - x 0) := by
  rw [hx.affine_identity j hj, hx.first_eq_of_one hℓ]
  ring

/-- The affine Dirichlet problem also has only the zero solution at parameter one. -/
theorem Recurrence.eq_zero_of_endpoints_of_one {ℓ j : ℕ} {x : ℕ → ℝ}
    (hx : Recurrence ℓ 1 x) (hℓ : 0 < ℓ) (hzero : x 0 = 0) (hlength : x ℓ = 0)
    (hj : j ≤ ℓ) : x j = 0 := by
  have h := hx.eq_affine hℓ j hj
  simpa only [hzero, hlength, sub_self, mul_zero, add_zero] using h

private theorem sin_centered (a θ : ℝ) :
    Real.sin (a - θ) + Real.sin (a + θ) = 2 * Real.cos θ * Real.sin a := by
  rw [Real.sin_sub, Real.sin_add]
  ring

private theorem sin_affine_step (a θ : ℝ) (j : ℕ) :
    Real.sin (a + (j : ℝ) * θ) + Real.sin (a + ((j + 2 : ℕ) : ℝ) * θ) =
      2 * Real.cos θ * Real.sin (a + ((j + 1 : ℕ) : ℝ) * θ) := by
  have h₀ : a + (j : ℝ) * θ = (a + ((j + 1 : ℕ) : ℝ) * θ) - θ := by
    push_cast
    ring
  have h₂ : a + ((j + 2 : ℕ) : ℝ) * θ =
      (a + ((j + 1 : ℕ) : ℝ) * θ) + θ := by
    push_cast
    ring
  rw [h₀, h₂, sin_centered]

/-- The sine solution identity with no division. It remains valid at resonant parameters. -/
theorem Recurrence.sin_identity {ℓ : ℕ} {θ : ℝ} {x : ℕ → ℝ}
    (hx : Recurrence ℓ (Real.cos θ) x) :
    ∀ j : ℕ, j ≤ ℓ →
      Real.sin θ * x j =
        Real.sin ((j : ℝ) * θ) * x 1 - Real.sin ((j : ℝ) * θ - θ) * x 0 := by
  apply Nat.twoStepInduction
  · intro _
    simp
  · intro _
    simp
  · intro j ih₀ ih₁ hj
    have h₀ := ih₀ (by omega)
    have h₁ := ih₁ (by omega)
    have hxr := hx j hj
    have hs := sin_affine_step 0 θ j
    have ht := sin_affine_step (-θ) θ j
    simp only [zero_add] at hs
    simp only [neg_add_eq_sub] at ht
    linear_combination Real.sin θ * hxr + (2 * Real.cos θ) * h₁ - h₀ -
      x 1 * hs + x 0 * ht

/-- The first internal value in terms of the two endpoints, away from Dirichlet resonance. -/
theorem Recurrence.first_eq {ℓ : ℕ} {θ : ℝ} {x : ℕ → ℝ}
    (hx : Recurrence ℓ (Real.cos θ) x) (hSin : Real.sin ((ℓ : ℝ) * θ) ≠ 0) :
    x 1 = Real.cos θ * x 0 +
      (Real.sin θ / Real.sin ((ℓ : ℝ) * θ)) *
        (x ℓ - Real.cos ((ℓ : ℝ) * θ) * x 0) := by
  have h := hx.sin_identity ℓ (le_refl ℓ)
  calc
    x 1 = (Real.sin θ * x ℓ + Real.sin ((ℓ : ℝ) * θ - θ) * x 0) /
        Real.sin ((ℓ : ℝ) * θ) := by
      apply (eq_div_iff hSin).2
      linarith
    _ = _ := by
      rw [Real.sin_sub]
      field_simp
      ring

/-- The sine interpolation of values `a` and `b` at positions zero and `ℓ`. -/
@[expose] noncomputable def sineInterpolation (ℓ : ℕ) (θ a b : ℝ) (j : ℕ) : ℝ :=
  (Real.sin ((ℓ : ℝ) * θ - (j : ℝ) * θ) * a +
    Real.sin ((j : ℝ) * θ) * b) / Real.sin ((ℓ : ℝ) * θ)

/-- The left endpoint of a nonresonant sine interpolant. -/
@[simp] theorem sineInterpolation_zero (ℓ : ℕ) (θ a b : ℝ)
    (hSin : Real.sin ((ℓ : ℝ) * θ) ≠ 0) :
    sineInterpolation ℓ θ a b 0 = a := by
  simp [sineInterpolation, hSin]

/-- The right endpoint of a nonresonant sine interpolant. -/
@[simp] theorem sineInterpolation_length (ℓ : ℕ) (θ a b : ℝ)
    (hSin : Real.sin ((ℓ : ℝ) * θ) ≠ 0) :
    sineInterpolation ℓ θ a b ℓ = b := by
  simp [sineInterpolation, hSin]

/-- Sine interpolation satisfies the interior adjacency equation. -/
theorem sineInterpolation_recurrence (ℓ : ℕ) (θ a b : ℝ) :
    Recurrence ℓ (Real.cos θ) (sineInterpolation ℓ θ a b) := by
  intro j _
  have hleft := sin_affine_step ((ℓ : ℝ) * θ) (-θ) j
  have hright := sin_affine_step 0 θ j
  simp only [Real.cos_neg, mul_neg, ← sub_eq_add_neg] at hleft
  simp only [zero_add] at hright
  dsimp only [sineInterpolation]
  linear_combination (a / Real.sin ((ℓ : ℝ) * θ)) * hleft +
    (b / Real.sin ((ℓ : ℝ) * θ)) * hright

/-- A solution of the nonresonant path equation is its endpoint sine interpolant. -/
theorem Recurrence.eq_sineInterpolation {ℓ : ℕ} {θ : ℝ} {x : ℕ → ℝ}
    (hx : Recurrence ℓ (Real.cos θ) x) (hSin : Real.sin ((ℓ : ℝ) * θ) ≠ 0) :
    ∀ j : ℕ, j ≤ ℓ → x j = sineInterpolation ℓ θ (x 0) (x ℓ) j := by
  have hy := sineInterpolation_recurrence ℓ θ (x 0) (x ℓ)
  apply hx.eq_of_initial hy
  · exact (sineInterpolation_zero ℓ θ (x 0) (x ℓ) hSin).symm
  · rw [hx.first_eq hSin, hy.first_eq hSin,
      sineInterpolation_zero ℓ θ (x 0) (x ℓ) hSin,
      sineInterpolation_length ℓ θ (x 0) (x ℓ) hSin]

/-- Zero boundary values force a nonresonant path solution to vanish everywhere on the path. -/
theorem Recurrence.eq_zero_of_endpoints {ℓ j : ℕ} {θ : ℝ} {x : ℕ → ℝ}
    (hx : Recurrence ℓ (Real.cos θ) x) (hSin : Real.sin ((ℓ : ℝ) * θ) ≠ 0)
    (hzero : x 0 = 0) (hlength : x ℓ = 0) (hj : j ≤ ℓ) : x j = 0 := by
  have h := hx.eq_sineInterpolation hSin j hj
  simpa only [sineInterpolation, hzero, hlength, mul_zero, add_zero, zero_div] using h

/-- The sine chord below an angle less than π. -/
theorem sin_chord_le {z τ : ℝ} (hz : 0 ≤ z) (hzτ : z ≤ τ)
    (hτ : 0 < τ) (hτπ : τ < Real.pi) :
    z * Real.sin τ ≤ τ * Real.sin z := by
  have hratio : 0 ≤ z / τ := div_nonneg hz hτ.le
  have hratio₁ : z / τ ≤ 1 := (div_le_one hτ).2 hzτ
  have hconc := strictConcaveOn_sin_Icc.concaveOn.2
    (show (0 : ℝ) ∈ Set.Icc 0 Real.pi from ⟨le_refl 0, Real.pi_pos.le⟩)
    (show τ ∈ Set.Icc 0 Real.pi from ⟨hτ.le, hτπ.le⟩)
    (sub_nonneg.2 hratio₁) hratio (show (1 - z / τ) + z / τ = 1 by ring)
  have hchord : (z / τ) * Real.sin τ ≤ Real.sin z := by
    simpa only [smul_eq_mul, Real.sin_zero, mul_zero, zero_add,
      div_mul_cancel₀ _ hτ.ne'] using hconc
  calc
    z * Real.sin τ = τ * ((z / τ) * Real.sin τ) := by field_simp
    _ ≤ τ * Real.sin z := mul_le_mul_of_nonneg_left hchord hτ.le

/-- A uniform bound on the transfer coefficient for lengths up to the angle τ < π. -/
theorem transferWeight_le {L θ τ : ℝ} (hL : 0 < L) (hθ : 0 < θ)
    (hLθ : L * θ ≤ τ) (hτπ : τ < Real.pi) :
    Real.sin θ / Real.sin (L * θ) ≤ τ / (L * Real.sin τ) := by
  have hz : 0 < L * θ := mul_pos hL hθ
  have hτ : 0 < τ := hz.trans_le hLθ
  have hsinz : 0 < Real.sin (L * θ) :=
    Real.sin_pos_of_pos_of_lt_pi hz (hLθ.trans_lt hτπ)
  have hsinτ : 0 < Real.sin τ := Real.sin_pos_of_pos_of_lt_pi hτ hτπ
  apply (div_le_div_iff₀ hsinz (mul_pos hL hsinτ)).2
  calc
    Real.sin θ * (L * Real.sin τ) ≤ θ * (L * Real.sin τ) :=
      mul_le_mul_of_nonneg_right (Real.sin_le hθ.le) (mul_pos hL hsinτ).le
    _ = (L * θ) * Real.sin τ := by ring
    _ ≤ τ * Real.sin (L * θ) := sin_chord_le hz.le hLθ hτ hτπ

/-- The finite matching-path perturbation budget in terms of a fixed cutoff angle τ < π. -/
theorem perturbationBudget_le {L θ τ : ℝ} (hL : 0 < L) (hθ : 0 < θ)
    (hLθ : L * θ ≤ τ) (hτπ : τ < Real.pi) :
    2 * (Real.sin θ / Real.sin (L * θ)) + 3 * (1 - Real.cos θ) ≤
      2 * τ / (L * Real.sin τ) + 3 * τ ^ 2 / (2 * L ^ 2) := by
  have htransfer := transferWeight_le hL hθ hLθ hτπ
  have hτ : 0 < τ := (mul_pos hL hθ).trans_le hLθ
  have hθτ : θ ≤ τ / L := (le_div_iff₀ hL).2 (by nlinarith)
  have hsquare : θ ^ 2 ≤ (τ / L) ^ 2 := sq_le_sq₀ hθ.le (div_pos hτ hL).le |>.2 hθτ
  have hcos : 1 - Real.cos θ ≤ θ ^ 2 / 2 := by
    linarith [Real.one_sub_sq_div_two_le_cos (x := θ)]
  have hdiv : (τ / L) ^ 2 / 2 = τ ^ 2 / (2 * L ^ 2) := by ring
  calc
    2 * (Real.sin θ / Real.sin (L * θ)) + 3 * (1 - Real.cos θ) ≤
        2 * (τ / (L * Real.sin τ)) + 3 * ((τ / L) ^ 2 / 2) := by nlinarith
    _ = _ := by rw [hdiv]; ring

end Cslib.ExpanderPath
