/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.ManinHeight
public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.PointCount

/-!
# The quadratic twist and Manin's parallelogram law

Let `g = X³ + α X² + β X + γ` over a field `k` and `D = g(T) ∈ k[T]`. The curve
`Y² = X³ + α D X² + β D² X + γ D³` over `k(T)` is the quadratic twist of `Y² = g(X)` by `D`:
`(x, y) ↦ (x / D, y / D²)` identifies it with `D Y² = g(X)`, which contains the generic point
`P₀ = (D T, D²)`. Manin's height of a point is `d P = max (deg r) (deg s)` where `x(P) / D = r / s`
in lowest terms (and `d 0 = 0`). It satisfies the exact parallelogram law
`d (P + Q) + d (P - Q) = 2 d P + 2 d Q`. The proof conjugates Stoll's identity
`WeierstrassCurve.Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x` on the twist by
`Λ = diag(1, D, D²)`, which turns it into the add-sub map of `Y² = g(X)` applied to primitive
triples over `k[T]`, and then compares heights.

## Main definitions

* `WeierstrassCurve.Manin.twistPoly`, `WeierstrassCurve.Manin.twist`: the twist over `k[T]` and
  over `k(T)`.
* `WeierstrassCurve.Manin.P₀`: the point `(D T, D²)` of the twist.
* `WeierstrassCurve.Manin.xPair`, `WeierstrassCurve.Manin.d`: the reduced pair of `x / D` and
  Manin's height.

## Main results

* `WeierstrassCurve.Manin.d_P₀`: `d P₀ = 1`.
* `WeierstrassCurve.Manin.parallelogram`: `d (P + Q) + d (P - Q) = 2 d P + 2 d Q`.

## References

* [Ju. I. Manin, *On cubic congruences to a prime modulus*][Manin1956], §2. The implementation
  notes of `ManinHeight` explain how this development follows it.
-/

public section

noncomputable section

open Polynomial

namespace WeierstrassCurve.Manin

variable {k : Type*} [Field k]

/-! ### The twist and the point `P₀` -/

/-- The twist `Y² = X³ + α D X² + β D² X + γ D³` over `k[T]`, where `D = g(T)` for
`g = X³ + α X² + β X + γ`. -/
@[expose] def twistPoly (α β γ : k) : WeierstrassCurve k[X] :=
  ⟨0, C α * cubicPoly α β γ, 0, C β * cubicPoly α β γ ^ 2, C γ * cubicPoly α β γ ^ 3⟩

/-- The twist over `k(T) = RatFunc k`. -/
@[expose] def twist (α β γ : k) : WeierstrassCurve (RatFunc k) :=
  (twistPoly α β γ).map (algebraMap k[X] (RatFunc k))

variable (α β γ : k)

@[simp] lemma twistPoly_a₁ : (twistPoly α β γ).a₁ = 0 := rfl
@[simp] lemma twistPoly_a₂ : (twistPoly α β γ).a₂ = C α * cubicPoly α β γ := rfl
@[simp] lemma twistPoly_a₃ : (twistPoly α β γ).a₃ = 0 := rfl
@[simp] lemma twistPoly_a₄ : (twistPoly α β γ).a₄ = C β * cubicPoly α β γ ^ 2 := rfl
@[simp] lemma twistPoly_a₆ : (twistPoly α β γ).a₆ = C γ * cubicPoly α β γ ^ 3 := rfl

/-- The discriminant of the twist is `D⁶` times that of `Y² = g(X)`. -/
lemma twistPoly_Δ : (twistPoly α β γ).Δ = cubicPoly α β γ ^ 6 * C (ofCubic α β γ).Δ := by
  simp only [Δ, b₂, b₄, b₆, b₈, twistPoly_a₁, twistPoly_a₂, twistPoly_a₃, twistPoly_a₄,
    twistPoly_a₆, ofCubic_a₁, ofCubic_a₂, ofCubic_a₃, ofCubic_a₄, ofCubic_a₆, map_add, map_sub,
    map_mul, map_neg, map_pow, map_ofNat, map_zero]
  ring

/-- `(D T, D²)` lies on the twist over `k[T]`. -/
lemma equation_P₀ :
    (twistPoly α β γ).toAffine.Equation (cubicPoly α β γ * X) (cubicPoly α β γ ^ 2) := by
  rw [Affine.equation_iff]
  simp only [twistPoly_a₁, twistPoly_a₂, twistPoly_a₃, twistPoly_a₄, twistPoly_a₆]
  unfold cubicPoly
  ring

variable {α β γ}

lemma twistPoly_Δ_ne_zero (hΔ : (ofCubic α β γ).Δ ≠ 0) : (twistPoly α β γ).Δ ≠ 0 := by
  rw [twistPoly_Δ]
  exact mul_ne_zero (pow_ne_zero _ (cubicPoly_ne_zero α β γ)) (C_ne_zero.2 hΔ)

/-- A solution over `k[T]` is a nonsingular point of the twist over `k(T)` when `Δ ≠ 0`. -/
lemma nonsingular_of_equation (hΔ : (ofCubic α β γ).Δ ≠ 0) {x y : k[X]}
    (h : (twistPoly α β γ).toAffine.Equation x y) :
    (twist α β γ).toAffine.Nonsingular (algebraMap k[X] (RatFunc k) x)
      (algebraMap k[X] (RatFunc k) y) :=
  ((twistPoly α β γ).toAffine.map_nonsingular (RatFunc.algebraMap_injective k) _ _).2
    ((Affine.equation_iff_nonsingular_of_Δ_ne_zero (twistPoly_Δ_ne_zero hΔ)).1 h)

variable (α β γ) in
open scoped Classical in
/-- The point `P₀ = (D T, D²)` of the twist (`0` if these coordinates are singular, which does
not happen when `Δ ≠ 0`, see `P₀_eq`). -/
def P₀ : (twist α β γ).toAffine.Point :=
  if h : (twist α β γ).toAffine.Nonsingular (algebraMap k[X] (RatFunc k) (cubicPoly α β γ * X))
      (algebraMap k[X] (RatFunc k) (cubicPoly α β γ ^ 2)) then .some _ _ h else .zero

lemma P₀_eq (hΔ : (ofCubic α β γ).Δ ≠ 0) :
    P₀ α β γ = .some _ _ (nonsingular_of_equation hΔ (equation_P₀ α β γ)) := by
  rw [P₀, dite_eq_left (nonsingular_of_equation hΔ (equation_P₀ α β γ))]

/-! ### Manin's height -/

/-- The reduced pair `(num, denom)` of `x / D` for an affine point `(x, y)` of the twist, and
`(1, 0)` for the point at infinity. -/
def xPair : (twist α β γ).toAffine.Point → k[X] × k[X]
  | .zero => (1, 0)
  | .some x _ _ => ((x / algebraMap k[X] (RatFunc k) (cubicPoly α β γ)).num,
      (x / algebraMap k[X] (RatFunc k) (cubicPoly α β γ)).denom)

/-- Manin's height of a point of the twist: `max (deg r) (deg s)` for `x / D = r / s` in lowest
terms, and `0` at infinity. -/
def d (P : (twist α β γ).toAffine.Point) : ℕ := max (xPair P).1.natDegree (xPair P).2.natDegree

lemma xPair_some {x y : RatFunc k} (h : (twist α β γ).toAffine.Nonsingular x y) :
    xPair (.some x y h) = ((x / algebraMap k[X] (RatFunc k) (cubicPoly α β γ)).num,
      (x / algebraMap k[X] (RatFunc k) (cubicPoly α β γ)).denom) := by
  simp only [xPair]

lemma isCoprime_xPair (P : (twist α β γ).toAffine.Point) :
    IsCoprime (xPair P).1 (xPair P).2 := by
  cases P with
  | zero => exact isCoprime_one_left
  | some x y h => exact RatFunc.isCoprime_num_denom _

lemma algebraMap_cubicPoly_ne_zero (α β γ : k) :
    algebraMap k[X] (RatFunc k) (cubicPoly α β γ) ≠ 0 :=
  (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).2 (cubicPoly_ne_zero α β γ)

/-- The height of an affine point of the twist depends only on `x / D`. -/
lemma d_some_eq_of_div {x y : RatFunc k} (h : (twist α β γ).toAffine.Nonsingular x y)
    {r : RatFunc k} (hx : x / algebraMap k[X] (RatFunc k) (cubicPoly α β γ) = r) :
    d (.some x y h) = max r.num.natDegree r.denom.natDegree := by
  rw [d, xPair_some, hx]

/-- A point with x-coordinate `D f` for a polynomial `f` has height `deg f`. -/
lemma d_some_of_x_eq {x y : RatFunc k} (h : (twist α β γ).toAffine.Nonsingular x y) (f : k[X])
    (hx : x = algebraMap k[X] (RatFunc k) (cubicPoly α β γ * f)) :
    d (.some x y h) = f.natDegree := by
  rw [d, xPair_some, hx, map_mul, mul_div_cancel_left₀ _ (algebraMap_cubicPoly_ne_zero α β γ),
    RatFunc.num_algebraMap, RatFunc.denom_algebraMap, natDegree_one]
  exact max_eq_left (Nat.zero_le _)

/-- `d P₀ = 1`. -/
theorem d_P₀ (hΔ : (ofCubic α β γ).Δ ≠ 0) : d (P₀ α β γ) = 1 := by
  rw [P₀_eq hΔ, d_some_of_x_eq _ X rfl, natDegree_X]

/-! ### The parallelogram law -/

/-- The components of `addSubMap` are homogeneous quadratics. -/
private lemma eval₂_smul_addSubMap {R S : Type*} [CommRing R] [CommRing S]
    (W : WeierstrassCurve R) (f : R →+* S) (c : S) (v : Fin 3 → S) (j : Fin 3) :
    MvPolynomial.eval₂ f (c • v) (W.addSubMap j) =
      c ^ 2 * MvPolynomial.eval₂ f v (W.addSubMap j) := by
  fin_cases j <;> simp [addSubMap] <;> ring

variable (α β γ) in
/-- The diagonal `![1, D, D²]` of the conjugation `Λ` between the twist and `Y² = g(X)`. -/
private def twistScale : Fin 3 → RatFunc k :=
  ![1, algebraMap k[X] (RatFunc k) (cubicPoly α β γ),
    algebraMap k[X] (RatFunc k) (cubicPoly α β γ) ^ 2]

variable (α β γ) in
/-- The add-sub map of `Y² = g(X)` at `Λ u` is `Λ` applied to the add-sub map of the twist at
`u`. -/
private lemma eval₂_addSubMap_twistScale (u : Fin 3 → RatFunc k) (j : Fin 3) :
    MvPolynomial.eval₂ ((algebraMap k[X] (RatFunc k)).comp C)
        (fun i ↦ twistScale α β γ i * u i) ((ofCubic α β γ).addSubMap j) =
      twistScale α β γ j * MvPolynomial.eval u ((twist α β γ).addSubMap j) := by
  rw [twist, addSubMap_map, MvPolynomial.eval_map]
  fin_cases j <;> simp [addSubMap, twistScale, b₂, b₄, b₆, b₈, map_ofNat] <;> ring

/-- `(xRep P 0, D · xRep P 1)` is a nonzero multiple of the reduced pair `xPair P`. -/
private lemma exists_xRep_eq (P : (twist α β γ).toAffine.Point) :
    ∃ l : RatFunc k, l ≠ 0 ∧ P.xRep 0 = l * algebraMap k[X] (RatFunc k) (xPair P).1 ∧
      algebraMap k[X] (RatFunc k) (cubicPoly α β γ) * P.xRep 1 =
        l * algebraMap k[X] (RatFunc k) (xPair P).2 := by
  cases P with
  | zero => exact ⟨1, one_ne_zero, by simp [← Affine.Point.zero_def, xPair],
      by simp [← Affine.Point.zero_def, xPair]⟩
  | some x y h =>
    simp only [Affine.Point.xRep_some, xPair_some, Matrix.cons_val_zero, Matrix.cons_val_one,
      mul_one]
    have hD := algebraMap_cubicPoly_ne_zero α β γ
    have hx : x = algebraMap k[X] (RatFunc k) (cubicPoly α β γ) *
        (x / algebraMap k[X] (RatFunc k) (cubicPoly α β γ)) := by field_simp
    generalize x / algebraMap k[X] (RatFunc k) (cubicPoly α β γ) = z at hx ⊢
    have hb : algebraMap k[X] (RatFunc k) z.denom ≠ 0 :=
      (map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).2 (RatFunc.denom_ne_zero _)
    refine ⟨algebraMap k[X] (RatFunc k) (cubicPoly α β γ) / algebraMap k[X] (RatFunc k) z.denom,
      div_ne_zero hD hb, ?_, ?_⟩
    · rw [hx]
      conv_lhs => rw [← RatFunc.num_div_denom z]
      field_simp
    · field_simp

/-- `Λ · sym2x P Q` is a nonzero multiple of the primitive triple
`sym2Pair (xPair P) (xPair Q)`. -/
private lemma exists_twistScale_sym2x (P Q : (twist α β γ).toAffine.Point) :
    ∃ c : RatFunc k, c ≠ 0 ∧ (fun i ↦ twistScale α β γ i * P.sym2x Q i) =
      c • fun i ↦ algebraMap k[X] (RatFunc k)
        (sym2Pair (xPair P).1 (xPair P).2 (xPair Q).1 (xPair Q).2 i) := by
  obtain ⟨l, hl, h0, h1⟩ := exists_xRep_eq P
  obtain ⟨l', hl', h0', h1'⟩ := exists_xRep_eq Q
  refine ⟨l * l', mul_ne_zero hl hl', ?_⟩
  funext i
  fin_cases i
  · simp [twistScale, Affine.Point.sym2x_eq, sym2Pair, h0, h0']
    ring
  · simp only [twistScale, Fin.mk_one, Fin.isValue, Matrix.cons_val_one, Matrix.cons_val_zero,
      Affine.Point.sym2x_eq, Nat.succ_eq_add_one, Nat.reduceAdd, sym2Pair, Pi.smul_apply, map_add,
      map_mul, smul_eq_mul]
    linear_combination Q.xRep 0 * h1 + P.xRep 0 * h1' +
      l' * algebraMap k[X] (RatFunc k) (xPair Q).2 * h0 +
      l * algebraMap k[X] (RatFunc k) (xPair P).2 * h0'
  · simp only [twistScale, Fin.reduceFinMk, Matrix.cons_val, Affine.Point.sym2x_eq,
      Nat.succ_eq_add_one, Nat.reduceAdd, Fin.isValue, sym2Pair, Pi.smul_apply, map_mul,
      smul_eq_mul]
    linear_combination (algebraMap k[X] (RatFunc k) (cubicPoly α β γ) * Q.xRep 1) * h1 +
      l * algebraMap k[X] (RatFunc k) (xPair P).2 * h1'

open scoped Classical in
/-- Stoll's identity conjugated by `Λ`: the add-sub map of `Y² = g(X)` over `k[T]`, applied to
the triple of `(P, Q)`, is proportional to the triple of `(P + Q, P - Q)`. -/
private lemma exists_smul_eq_addSubMap (P Q : (twist α β γ).toAffine.Point) :
    ∃ s : RatFunc k, s • (fun j ↦ algebraMap k[X] (RatFunc k)
        (sym2Pair (xPair (P + Q)).1 (xPair (P + Q)).2 (xPair (P - Q)).1 (xPair (P - Q)).2 j)) =
      fun j ↦ algebraMap k[X] (RatFunc k) (MvPolynomial.eval
        (sym2Pair (xPair P).1 (xPair P).2 (xPair Q).1 (xPair Q).2)
        (((ofCubic α β γ).map C).addSubMap j)) := by
  obtain ⟨t, -, hts⟩ := Affine.Point.sym2x_add_sub_eq_addSubMap_sym2x P Q
  obtain ⟨c, hc, hcS⟩ := exists_twistScale_sym2x P Q
  obtain ⟨c', -, hcS'⟩ := exists_twistScale_sym2x (P + Q) (P - Q)
  set w := sym2Pair (xPair P).1 (xPair P).2 (xPair Q).1 (xPair Q).2
  set v := sym2Pair (xPair (P + Q)).1 (xPair (P + Q)).2 (xPair (P - Q)).1 (xPair (P - Q)).2
  refine ⟨t * c' / c ^ 2, funext fun j ↦ ?_⟩
  have key : algebraMap k[X] (RatFunc k)
      (MvPolynomial.eval w (((ofCubic α β γ).map C).addSubMap j)) * c ^ 2 =
      t * c' * algebraMap k[X] (RatFunc k) (v j) := by
    rw [addSubMap_map, MvPolynomial.eval_map, MvPolynomial.eval₂_comp_left, mul_comm,
      ← eval₂_smul_addSubMap]
    have h1 : (algebraMap k[X] (RatFunc k)) ∘ w = fun i ↦ algebraMap k[X] (RatFunc k) (w i) :=
      rfl
    rw [h1, ← hcS, eval₂_addSubMap_twistScale, ← congrFun hts j]
    have h2 := congrFun hcS' j
    simp only [Pi.smul_apply, smul_eq_mul] at h2 ⊢
    rw [mul_assoc t, ← h2]
    ring
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [div_mul_eq_mul_div, div_eq_iff (pow_ne_zero 2 hc), key]

open scoped Classical in
/-- **Manin's parallelogram law.** On the twist, `d (P + Q) + d (P - Q) = 2 d P + 2 d Q` for all
points `P` and `Q`. -/
theorem parallelogram (hΔ : (ofCubic α β γ).Δ ≠ 0) (P Q : (twist α β γ).toAffine.Point) :
    d (P + Q) + d (P - Q) = 2 * d P + 2 * d Q := by
  obtain ⟨s, hs⟩ := exists_smul_eq_addSubMap P Q
  have hw := isPrim_sym2Pair (isCoprime_xPair P) (isCoprime_xPair Q)
  have h := hgt_eq_of_smul_eq
    (isPrim_sym2Pair (isCoprime_xPair (P + Q)) (isCoprime_xPair (P - Q)))
    (isPrim_addSubMap (ofCubic α β γ) hΔ hw) hs
  rw [hgt_addSubMap _ hΔ hw, hgt_sym2Pair (isCoprime_xPair _) (isCoprime_xPair _),
    hgt_sym2Pair (isCoprime_xPair _) (isCoprime_xPair _)] at h
  simp only [d]
  omega

end WeierstrassCurve.Manin
