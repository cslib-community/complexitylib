/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.Hasse
import Mathlib.Tactic.NormNum.Prime

/-! Point counts and Hasse's bound for small elliptic curves over `ZMod p`, including the curve
`y² = x³ + 3x + 3` over `ZMod 7` from Example 9.69 of [KatzLindell2020]. -/

namespace CslibFrontierTests.EllipticCurveHasse

open WeierstrassCurve

instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-- The curve `y² = x³ + 3x + 3` over `ZMod 7`. -/
abbrev E7 : WeierstrassCurve (ZMod 7) := ofCubic 0 3 3

theorem Δ_E7 : E7.Δ ≠ 0 := by decide

instance : E7.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E7⟩

/-- The curve `y² + y = x³` over `ZMod 2`. -/
abbrev E2 : WeierstrassCurve (ZMod 2) := ⟨0, 0, 1, 0, 0⟩

theorem Δ_E2 : E2.Δ ≠ 0 := by decide

instance : E2.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E2⟩

theorem ringChar_zmod_seven : ringChar (ZMod 7) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

/-- `E7` has 6 points: the point at infinity, `(1, 0)`, `(3, ±2)` and `(4, ±3)`. -/
theorem natCard_E7 : Nat.card E7.toAffine.Point = 6 := by
  rw [Affine.natCard_point_eq_one_add_equation E7.toAffine Δ_E7,
    Nat.card_congr (Equiv.subtypeEquivRight fun xy : ZMod 7 × ZMod 7 ↦
      Affine.equation_iff (W := E7.toAffine) xy.1 xy.2),
    Nat.card_eq_fintype_card]
  decide

/-- `E2` has 3 points: the point at infinity, `(0, 0)` and `(0, 1)`. -/
theorem natCard_E2 : Nat.card E2.toAffine.Point = 3 := by
  rw [Affine.natCard_point_eq_one_add_equation E2.toAffine Δ_E2,
    Nat.card_congr (Equiv.subtypeEquivRight fun xy : ZMod 2 × ZMod 2 ↦
      Affine.equation_iff (W := E2.toAffine) xy.1 xy.2),
    Nat.card_eq_fintype_card]
  decide

-- The point count of `E7` forces the character sum of `x³ + 3x + 3` over `ZMod 7` to be `-2`.
example : cubicCharSum (E7.b₂ / 4) (E7.b₄ / 2) (E7.b₆ / 4) = -2 := by
  have h := natCard_point_eq ringChar_zmod_seven E7
  rw [natCard_E7, ZMod.card] at h
  omega

-- Manin's bound on that character sum, with the discriminant hypothesis checked by `decide`.
example : cubicCharSum (0 : ZMod 7) 3 3 ^ 2 ≤ 4 * 7 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using
    cubicCharSum_sq_le ringChar_zmod_seven (α := (0 : ZMod 7)) (β := 3) (γ := 3) (by decide)

-- Hasse's bound for `E7` in integer form: `(6 - 8)² ≤ 28`.
example : ((Nat.card E7.toAffine.Point : ℤ) - (7 + 1)) ^ 2 ≤ 4 * 7 := by
  simpa only [ZMod.card, Nat.cast_ofNat] using hasse_bound ringChar_zmod_seven E7

-- The real form for `E7`: `|6 - 8| ≤ 2 √7`.
example : |(6 : ℝ) - (7 + 1)| ≤ 2 * Real.sqrt 7 := by
  have h := abs_natCard_point_sub_le ringChar_zmod_seven E7
  rw [natCard_E7, ZMod.card] at h
  exact_mod_cast h

-- `hasse_bound_zmod` for `E7`, and for `E2` in characteristic two.
example : (7 : ℝ) + 1 - 2 * Real.sqrt 7 ≤ Nat.card E7.toAffine.Point ∧
    (Nat.card E7.toAffine.Point : ℝ) ≤ 7 + 1 + 2 * Real.sqrt 7 := by
  exact_mod_cast hasse_bound_zmod E7

example : (2 : ℝ) + 1 - 2 * Real.sqrt 2 ≤ Nat.card E2.toAffine.Point ∧
    (Nat.card E2.toAffine.Point : ℝ) ≤ 2 + 1 + 2 * Real.sqrt 2 := by
  exact_mod_cast hasse_bound_zmod E2

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

theorem ringChar_zmod_five : ringChar (ZMod 5) ≠ 2 := by
  rw [ZMod.ringChar_zmod_n]
  decide

/-- The curve `y² = x³ + 3x` over `ZMod 5`. -/
abbrev E5 : WeierstrassCurve (ZMod 5) := ofCubic 0 3 0

/-- The curve `y² = x³ + 2x` over `ZMod 5`. -/
abbrev E5' : WeierstrassCurve (ZMod 5) := ofCubic 0 2 0

theorem Δ_E5 : E5.Δ ≠ 0 := by decide

theorem Δ_E5' : E5'.Δ ≠ 0 := by decide

instance : E5.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E5⟩

instance : E5'.IsElliptic := ⟨isUnit_iff_ne_zero.2 Δ_E5'⟩

/-- `E5` has 10 points, the most that Hasse's bound allows over `ZMod 5`. -/
theorem natCard_E5 : Nat.card E5.toAffine.Point = 10 := by
  rw [Affine.natCard_point_eq_one_add_equation E5.toAffine Δ_E5,
    Nat.card_congr (Equiv.subtypeEquivRight fun xy : ZMod 5 × ZMod 5 ↦
      Affine.equation_iff (W := E5.toAffine) xy.1 xy.2),
    Nat.card_eq_fintype_card]
  decide

/-- `E5'` has 2 points, the fewest that Hasse's bound allows over `ZMod 5`. -/
theorem natCard_E5' : Nat.card E5'.toAffine.Point = 2 := by
  rw [Affine.natCard_point_eq_one_add_equation E5'.toAffine Δ_E5',
    Nat.card_congr (Equiv.subtypeEquivRight fun xy : ZMod 5 × ZMod 5 ↦
      Affine.equation_iff (W := E5'.toAffine) xy.1 xy.2),
    Nat.card_eq_fintype_card]
  decide

-- Over `ZMod 5`, Hasse's bound gives `2 ≤ #E ≤ 10` for every elliptic curve, and `E5'` and `E5`
-- show that both ends are attained.
example (W : WeierstrassCurve (ZMod 5)) [W.IsElliptic] :
    2 ≤ Nat.card W.toAffine.Point ∧ Nat.card W.toAffine.Point ≤ 10 := by
  have h := hasse_bound ringChar_zmod_five W
  simp only [ZMod.card, Nat.cast_ofNat] at h
  constructor
  · have : (2 : ℤ) ≤ Nat.card W.toAffine.Point := by nlinarith
    exact_mod_cast this
  · have : (Nat.card W.toAffine.Point : ℤ) ≤ 10 := by nlinarith
    exact_mod_cast this

example : (2 : ℤ) = Nat.card E5'.toAffine.Point ∧ (Nat.card E5.toAffine.Point : ℤ) = 10 := by
  rw [natCard_E5', natCard_E5]
  norm_num

end CslibFrontierTests.EllipticCurveHasse
