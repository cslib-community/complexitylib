/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
public import Mathlib.NumberTheory.LegendreSymbol.QuadraticChar.Basic

/-!
# Point counts of Weierstrass curves over finite fields

Over a finite field `F` of odd characteristic, completing the square turns the equation of a
Weierstrass curve `W` into `Y² = g(X)` with the monic cubic
`g = X³ + (b₂/4) X² + (b₄/2) X + b₆/4`. The fibre of the affine curve over `x` then has
`1 + χ(g(x))` points, where `χ` is the quadratic character of `F`, and summing over `x` gives
`#E(F) = q + 1 + ∑ₓ χ(g(x))` for `q = #F`.

## Main definitions

* `WeierstrassCurve.cubicPoly α β γ`: the monic cubic `X³ + α X² + β X + γ`.
* `WeierstrassCurve.ofCubic α β γ`: the Weierstrass curve `Y² = X³ + α X² + β X + γ`.
* `WeierstrassCurve.cubicCharSum α β γ`: the character sum `∑ₓ χ(x³ + α x² + β x + γ)`.

## Main results

* `WeierstrassCurve.Affine.natCard_point_eq_one_add_equation`: for `Δ ≠ 0`, the points are the
  point at infinity and the affine solutions of the Weierstrass equation.
* `WeierstrassCurve.Δ_ofCubic`: completing the square preserves the discriminant.
* `WeierstrassCurve.natCard_fiber`: the fibre over `x` has `1 + χ(g(x))` points.
* `WeierstrassCurve.natCard_point_eq`: `#E(F) = q + 1 + ∑ₓ χ(g(x))`.
* `WeierstrassCurve.natCard_point_zmod_two`: over `ZMod 2` there are between `1` and `5` points.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Section 9.3.4:
  Example 9.69 (p. 346) counts the points of `y² = f(x)` over `ℤ_p` through quadratic residues.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace WeierstrassCurve

/-! ### Finiteness and the point count -/

namespace Affine

variable {R : Type*} [CommRing R] [Finite R] (W : Affine R)

/-- The points of a Weierstrass curve over a finite ring form a finite type. -/
instance : Finite W.Point :=
  @Finite.of_equiv _ _ (inferInstanceAs (Finite (Option _))) W.nonsingularPointEquiv.symm

/-- The number of points is one (the point at infinity) plus the number of nonsingular affine
points. -/
theorem natCard_point_eq_one_add_nonsingular :
    Nat.card W.Point = 1 + Nat.card {xy : R × R // W.Nonsingular xy.1 xy.2} := by
  rw [Nat.card_congr W.nonsingularPointEquiv, add_comm]
  exact Finite.card_option

/-- For `Δ ≠ 0`, the number of points is one plus the number of affine solutions of the
Weierstrass equation. -/
theorem natCard_point_eq_one_add_equation (hΔ : W.Δ ≠ 0) :
    Nat.card W.Point = 1 + Nat.card {xy : R × R // W.Equation xy.1 xy.2} := by
  rw [natCard_point_eq_one_add_nonsingular]
  exact congrArg _ (Nat.card_congr (Equiv.subtypeEquivRight fun _ ↦
    (equation_iff_nonsingular_of_Δ_ne_zero hΔ).symm))

end Affine

/-! ### Curves `Y² = g(X)` for a monic cubic `g` -/

section Cubic

variable {R : Type*} [CommRing R]

/-- The monic cubic `X³ + α X² + β X + γ`. -/
def cubicPoly (α β γ : R) : R[X] := X ^ 3 + C α * X ^ 2 + C β * X + C γ

/-- The Weierstrass curve `Y² = X³ + α X² + β X + γ`. -/
def ofCubic (α β γ : R) : WeierstrassCurve R := ⟨0, α, 0, β, γ⟩

variable (α β γ : R)

@[simp] lemma ofCubic_a₁ : (ofCubic α β γ).a₁ = 0 := rfl
@[simp] lemma ofCubic_a₂ : (ofCubic α β γ).a₂ = α := rfl
@[simp] lemma ofCubic_a₃ : (ofCubic α β γ).a₃ = 0 := rfl
@[simp] lemma ofCubic_a₄ : (ofCubic α β γ).a₄ = β := rfl
@[simp] lemma ofCubic_a₆ : (ofCubic α β γ).a₆ = γ := rfl

lemma eval_cubicPoly (x : R) :
    (cubicPoly α β γ).eval x = x ^ 3 + α * x ^ 2 + β * x + γ := by
  simp [cubicPoly]

lemma monic_cubicPoly : (cubicPoly α β γ).Monic := by
  unfold cubicPoly
  monicity!

variable [Nontrivial R]

lemma natDegree_cubicPoly : (cubicPoly α β γ).natDegree = 3 := by
  unfold cubicPoly
  compute_degree!

lemma cubicPoly_ne_zero : cubicPoly α β γ ≠ 0 :=
  (monic_cubicPoly α β γ).ne_zero

end Cubic

/-- The character sum `∑ₓ χ(x³ + α x² + β x + γ)` of the quadratic character `χ` of `F`. -/
def cubicCharSum {F : Type*} [Field F] [Fintype F] [DecidableEq F] (α β γ : F) : ℤ :=
  ∑ x : F, quadraticChar F ((cubicPoly α β γ).eval x)

/-! ### Completing the square -/

section CompleteSquare

variable {F : Type*} [Field F] (W : WeierstrassCurve F)

private lemma four_ne_zero_of_two (h2 : (2 : F) ≠ 0) : (4 : F) ≠ 0 := by
  rw [show (4 : F) = 2 * 2 by norm_num]
  exact mul_ne_zero h2 h2

private lemma ofCubic_b₂ (h2 : (2 : F) ≠ 0) :
    (ofCubic (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).b₂ = W.b₂ := by
  have := four_ne_zero_of_two h2
  simp only [b₂, ofCubic_a₁, ofCubic_a₂]
  field_simp
  ring

private lemma ofCubic_b₄ (h2 : (2 : F) ≠ 0) :
    (ofCubic (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).b₄ = W.b₄ := by
  simp only [b₄, ofCubic_a₁, ofCubic_a₃, ofCubic_a₄]
  field_simp
  ring

private lemma ofCubic_b₆ (h2 : (2 : F) ≠ 0) :
    (ofCubic (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).b₆ = W.b₆ := by
  have := four_ne_zero_of_two h2
  simp only [b₆, ofCubic_a₃, ofCubic_a₆]
  field_simp
  ring

private lemma ofCubic_b₈ (h2 : (2 : F) ≠ 0) :
    (ofCubic (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).b₈ = W.b₈ := by
  have h4 := four_ne_zero_of_two h2
  have hb8 : W.b₈ = (W.b₂ * W.b₆ - W.b₄ ^ 2) / 4 := by
    rw [eq_div_iff h4, mul_comm]
    exact W.b_relation
  rw [hb8]
  simp only [b₈, ofCubic_a₁, ofCubic_a₂, ofCubic_a₃, ofCubic_a₄, ofCubic_a₆]
  field_simp
  ring

/-- Completing the square preserves the discriminant: when `2 ≠ 0`, the curve
`Y² = X³ + (b₂/4) X² + (b₄/2) X + b₆/4` has the discriminant of `W`. -/
theorem Δ_ofCubic (h2 : (2 : F) ≠ 0) : (ofCubic (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).Δ = W.Δ := by
  rw [Δ, Δ, ofCubic_b₂ W h2, ofCubic_b₄ W h2, ofCubic_b₆ W h2, ofCubic_b₈ W h2]

/-- Completing the square: `W.Equation x y ↔ (2y + a₁x + a₃)² = 4 g(x)` with
`g = X³ + (b₂/4) X² + (b₄/2) X + b₆/4`. -/
lemma equation_iff_sq_eq (h2 : (2 : F) ≠ 0) (x y : F) :
    W.toAffine.Equation x y ↔
      (2 * y + W.a₁ * x + W.a₃) ^ 2 = 4 * (cubicPoly (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).eval x := by
  have h4 := four_ne_zero_of_two h2
  have hg : 4 * (cubicPoly (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).eval x =
      4 * x ^ 3 + W.b₂ * x ^ 2 + 2 * W.b₄ * x + W.b₆ := by
    rw [eval_cubicPoly]
    field_simp
    ring
  rw [Affine.equation_iff, hg]
  simp only [b₂, b₄, b₆]
  constructor
  · intro h
    linear_combination 4 * h
  · intro h
    apply mul_left_cancel₀ h4
    linear_combination h

end CompleteSquare

/-! ### The point count -/

section Count

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F]

/-- The number of square roots of `a` is `1 + χ(a)`. -/
private lemma natCard_sqrts (hF : ringChar F ≠ 2) (a : F) :
    (Nat.card {z : F // z ^ 2 = a} : ℤ) = 1 + quadraticChar F a := by
  have h := quadraticChar_card_sqrts hF a
  rw [← Nat.card_eq_card_toFinset] at h
  rw [add_comm]
  exact h

/-- The fibre of the affine curve over `x` has `1 + χ(g(x))` points, where
`g = X³ + (b₂/4) X² + (b₄/2) X + b₆/4`. -/
theorem natCard_fiber (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) (x : F) :
    (Nat.card {y : F // W.toAffine.Equation x y} : ℤ) =
      1 + quadraticChar F ((cubicPoly (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).eval x) := by
  have h2 : (2 : F) ≠ 0 := Ring.two_ne_zero hF
  set g := (cubicPoly (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4)).eval x
  have e : {y : F // W.toAffine.Equation x y} ≃ {z : F // z ^ 2 = 4 * g} :=
    Equiv.subtypeEquiv ((Equiv.mulLeft₀ (2 : F) h2).trans (Equiv.addRight (W.a₁ * x + W.a₃)))
      fun y ↦ by
        rw [equation_iff_sq_eq W h2, add_assoc]
        exact Iff.rfl
  rw [Nat.card_congr e, natCard_sqrts hF, map_mul, show (4 : F) = 2 ^ 2 by norm_num,
    quadraticChar_sq_one' h2, one_mul]

/-- The number of affine solutions of the Weierstrass equation is `q + ∑ₓ χ(g(x))`. -/
theorem natCard_equation (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) :
    (Nat.card {xy : F × F // W.toAffine.Equation xy.1 xy.2} : ℤ) =
      Fintype.card F + cubicCharSum (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) := by
  rw [Nat.card_congr (Equiv.subtypeProdEquivSigmaSubtype fun x y ↦ W.toAffine.Equation x y),
    Nat.card_sigma, Nat.cast_sum]
  simp only [natCard_fiber hF, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, mul_one, cubicCharSum]

/-- **Point count.** An elliptic curve over a finite field `F` of odd characteristic has
`q + 1 + ∑ₓ χ(g(x))` points, where `g = X³ + (b₂/4) X² + (b₄/2) X + b₆/4`. -/
theorem natCard_point_eq (hF : ringChar F ≠ 2) (W : WeierstrassCurve F) [W.IsElliptic] :
    (Nat.card W.toAffine.Point : ℤ) =
      Fintype.card F + 1 + cubicCharSum (W.b₂ / 4) (W.b₄ / 2) (W.b₆ / 4) := by
  rw [W.toAffine.natCard_point_eq_one_add_equation W.isUnit_Δ.ne_zero, Nat.cast_add,
    natCard_equation hF]
  ring

end Count

/-- Over `ZMod 2` every Weierstrass curve has between `1` and `5` points. -/
theorem natCard_point_zmod_two (W : WeierstrassCurve (ZMod 2)) :
    1 ≤ Nat.card W.toAffine.Point ∧ Nat.card W.toAffine.Point ≤ 5 := by
  have hle : Nat.card {xy : ZMod 2 × ZMod 2 // W.toAffine.Nonsingular xy.1 xy.2} ≤ 4 := by
    have h := Finite.card_subtype_le fun xy : ZMod 2 × ZMod 2 ↦ W.toAffine.Nonsingular xy.1 xy.2
    rwa [Nat.card_prod, Nat.card_zmod] at h
  rw [W.toAffine.natCard_point_eq_one_add_nonsingular]
  omega

end WeierstrassCurve
