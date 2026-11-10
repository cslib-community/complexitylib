/-
Copyright (c) 2026 Karn Seth. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.AlgebraicGeometry.EllipticCurve.ManinTwist
public import Mathlib.Analysis.Real.Sqrt

/-!
# Hasse's bound via Manin's proof

Let `F` be a finite field of odd characteristic with `q` elements, let
`g = X³ + α X² + β X + γ` over `F` with `Δ ≠ 0`, and let `S = ∑ₓ χ(g(x))`
(`WeierstrassCurve.cubicCharSum`). On the twist of `Y² = g(X)` over `F(T)`
(`WeierstrassCurve.Manin.twist`), the Frobenius point `P₁ = (D T^q, D^((q+3)/2))` has height `q`
and `P₁ - P₀` has height `q + 1 + S`, where `D = g(T)`. The parallelogram law and `d P₀ = 1` then
force `d (P₁ - n • P₀) = n² + S n + q` for every integer `n`. Heights are nonnegative and `q` is
odd, so `S² ≤ 4 q`. Together with the point count `#E(F) = q + 1 + S`
(`WeierstrassCurve.natCard_point_eq`) this is Hasse's bound. The argument is Manin's elementary
proof (1956).

The height of `P₁ - P₀` comes from the group law: `x(P₁ - P₀) / D = N / (T^q - T)²` with
`N = D (D^m + 1)² - (α + T^q + T) (T^q - T)²` and `m = q / 2`. Since `T^q - T = ∏_c (T - c)`,
the reduced denominator is `∏_c (T - c)^(1 + χ(g(c)))`; the exponent of each factor is read off
from Euler's criterion `g(c)^m = χ(g(c))` and from the simple roots of `g`.

## Main definitions

* `WeierstrassCurve.Manin.P₁`: the Frobenius point of the twist.

## Main results

* `WeierstrassCurve.Manin.d_P₁_sub_P₀`: `d (P₁ - P₀) = q + 1 + S`.
* `WeierstrassCurve.Manin.d_P₁_sub_zsmul_P₀`: `d (P₁ - n • P₀) = n² + S n + q`.
* `WeierstrassCurve.cubicCharSum_sq_le`: `S² ≤ 4 q`.
* `WeierstrassCurve.hasse_bound`: `(#E(F) - (q + 1))² ≤ 4 q` for every elliptic curve over a
  finite field of odd characteristic.
* `WeierstrassCurve.abs_natCard_point_sub_le`: `|#E(F) - (q + 1)| ≤ 2 √q`.
* `WeierstrassCurve.hasse_bound_zmod`: `p + 1 - 2 √p ≤ #E(ZMod p) ≤ p + 1 + 2 √p` for every
  prime `p`.

## References

* [J. Katz, Y. Lindell, *Introduction to Modern Cryptography*][KatzLindell2020], Theorem 9.72
  (p. 351), which states the bound over `ZMod p` without proof.
-/

@[expose] public section

noncomputable section

open Polynomial

namespace WeierstrassCurve.Manin

/-! ### Two facts about integer sequences -/

/-- Two functions `ℤ → ℤ` that satisfy `f (m + 1) + f (m - 1) = 2 f m + 2` and agree at `0` and
`1` agree everywhere. -/
private lemma eq_of_rec {f g : ℤ → ℤ} (h0 : f 0 = g 0) (h1 : f 1 = g 1)
    (hf : ∀ m, f (m + 1) + f (m - 1) = 2 * f m + 2)
    (hg : ∀ m, g (m + 1) + g (m - 1) = 2 * g m + 2) (n : ℤ) : f n = g n := by
  suffices h : f n = g n ∧ f (n + 1) = g (n + 1) from h.1
  induction n using Int.induction_on with
  | zero => exact ⟨h0, by rwa [zero_add]⟩
  | succ i ih =>
    refine ⟨ih.2, ?_⟩
    have a := hf ((i : ℤ) + 1)
    have b := hg ((i : ℤ) + 1)
    rw [add_sub_cancel_right] at a b
    omega
  | pred i ih =>
    rw [sub_add_cancel]
    refine ⟨?_, ih.1⟩
    have a := hf (-(i : ℤ))
    have b := hg (-(i : ℤ))
    omega

/-- An integer quadratic `n² + S n + q` with `q` odd that is nonnegative on `ℤ` has `S² ≤ 4 q`.
For `S = 2 k` evaluate at `-k`; for `S = 2 k + 1` evaluate at `-(k + 1)`, which gives
`k (k + 1) ≤ q`, and `k (k + 1)` is even while `q` is odd. -/
private lemma sq_le_of_forall_nonneg {q S : ℤ} (hq : Odd q)
    (h : ∀ n : ℤ, 0 ≤ n ^ 2 + S * n + q) : S ^ 2 ≤ 4 * q := by
  obtain ⟨k, rfl | rfl⟩ := Int.even_or_odd' S
  · have := h (-k)
    nlinarith
  · have h1 := h (-(k + 1))
    have hle : k * (k + 1) ≤ q := by nlinarith
    have hne : k * (k + 1) ≠ q := fun he ↦
      Int.not_even_iff_odd.2 hq (he ▸ Int.even_mul_succ_self k)
    have hlt : k * (k + 1) < q := lt_of_le_of_ne hle hne
    nlinarith

/-! ### Simple roots of the cubic and reduced fractions -/

section SimpleRoots

variable {k : Type*} [Field k] {α β γ : k}

/-- If `Δ ≠ 0`, the roots of `g` are simple: `g'(c) ≠ 0` at every root `c`. This is the
nonsingularity of `Y² = g(X)` at `(c, 0)`. -/
lemma derivative_cubicPoly_eval_ne_zero (hΔ : (ofCubic α β γ).Δ ≠ 0) {c : k}
    (hc : (cubicPoly α β γ).IsRoot c) : (derivative (cubicPoly α β γ)).eval c ≠ 0 := by
  have heq : (ofCubic α β γ).toAffine.Equation c 0 := by
    rw [Affine.equation_iff]
    have := hc.eq_zero
    rw [eval_cubicPoly] at this
    simp only [ofCubic_a₁, ofCubic_a₂, ofCubic_a₃, ofCubic_a₄, ofCubic_a₆]
    linear_combination -this
  have hns := (Affine.equation_iff_nonsingular_of_Δ_ne_zero hΔ).1 heq
  rw [Affine.nonsingular_iff] at hns
  have hd : (derivative (cubicPoly α β γ)).eval c = 3 * c ^ 2 + 2 * α * c + β := by
    simp [cubicPoly]
    ring
  rw [hd]
  simpa [eq_comm] using hns.2

/-- If `Δ ≠ 0`, every root of `g` has multiplicity at most one. -/
lemma rootMultiplicity_cubicPoly_le_one (hΔ : (ofCubic α β γ).Δ ≠ 0) (c : k) :
    (cubicPoly α β γ).rootMultiplicity c ≤ 1 := by
  by_contra h
  rw [not_le, one_lt_rootMultiplicity_iff_isRoot (cubicPoly_ne_zero α β γ)] at h
  exact derivative_cubicPoly_eval_ne_zero hΔ h.1 h.2

/-- If `x = M / H` with `M` and `H` nonzero and coprime, then the reduced numerator and
denominator of `x` have the degrees of `M` and `H`. -/
private lemma natDegree_num_denom_of_eq_div {x : RatFunc k} {M H : k[X]} (hM : M ≠ 0)
    (hH : H ≠ 0) (hMH : IsCoprime M H)
    (hx : x = algebraMap k[X] (RatFunc k) M / algebraMap k[X] (RatFunc k) H) :
    x.num.natDegree = M.natDegree ∧ x.denom.natDegree = H.natDegree := by
  have e : x.num * H = M * x.denom := (RatFunc.num_mul_eq_mul_denom_iff hH).2 hx
  have h1 : x.denom ∣ H :=
    (RatFunc.isCoprime_num_denom x).symm.dvd_of_dvd_mul_left ⟨M, by rw [e, mul_comm]⟩
  have h2 : H ∣ x.denom := hMH.symm.dvd_of_dvd_mul_left ⟨x.num, by rw [← e, mul_comm]⟩
  have hdeg : x.denom.natDegree = H.natDegree :=
    natDegree_eq_of_degree_eq (degree_eq_degree_of_associated (associated_of_dvd_dvd h1 h2))
  refine ⟨?_, hdeg⟩
  have hx0 : x ≠ 0 := by
    rw [hx]
    exact div_ne_zero ((map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).2 hM)
      ((map_ne_zero_iff _ (RatFunc.algebraMap_injective k)).2 hH)
  have := congrArg natDegree e
  rw [natDegree_mul (RatFunc.num_ne_zero hx0) hH, natDegree_mul hM (RatFunc.denom_ne_zero x),
    hdeg] at this
  omega

private lemma natDegree_sub_le_of_le' {f g : k[X]} {n : ℕ} (hf : f.natDegree ≤ n)
    (hg : g.natDegree ≤ n) : (f - g).natDegree ≤ n :=
  (natDegree_sub_le _ _).trans (max_le hf hg)

end SimpleRoots

/-! ### The Frobenius point `P₁` -/

section Frobenius

variable {F : Type*} [Field F] [Fintype F]

/-- `D^q = g(T^q)` over `F`, where `q = |F|`. -/
private lemma cubicPoly_pow_card (α β γ : F) :
    cubicPoly α β γ ^ Fintype.card F = (X ^ Fintype.card F) ^ 3 +
      C α * (X ^ Fintype.card F) ^ 2 + C β * X ^ Fintype.card F + C γ := by
  rw [← FiniteField.Polynomial.expand_card]
  simp [cubicPoly]

/-- `P₁ = (D T^q, D^((q+3)/2))` lies on the twist over `F[T]`, since `D^q = g(T^q)`. -/
lemma equation_P₁ (hF : ringChar F ≠ 2) (α β γ : F) :
    (twistPoly α β γ).toAffine.Equation (cubicPoly α β γ * X ^ Fintype.card F)
      (cubicPoly α β γ ^ ((Fintype.card F + 3) / 2)) := by
  have hodd : (Fintype.card F + 3) / 2 * 2 = Fintype.card F + 3 := by
    have := FiniteField.odd_card_of_char_ne_two hF
    omega
  rw [Affine.equation_iff]
  simp only [twistPoly_a₁, twistPoly_a₂, twistPoly_a₃, twistPoly_a₄, twistPoly_a₆]
  rw [← pow_mul, hodd]
  linear_combination cubicPoly α β γ ^ 3 * cubicPoly_pow_card α β γ

variable {α β γ : F}

variable (α β γ) in
open scoped Classical in
/-- The Frobenius point `P₁ = (D T^q, D^((q+3)/2))` of the twist (`0` if these coordinates are
singular, which does not happen in odd characteristic when `Δ ≠ 0`, see `P₁_eq`). -/
def P₁ : (twist α β γ).toAffine.Point :=
  if h : (twist α β γ).toAffine.Nonsingular
      (algebraMap F[X] (RatFunc F) (cubicPoly α β γ * X ^ Fintype.card F))
      (algebraMap F[X] (RatFunc F) (cubicPoly α β γ ^ ((Fintype.card F + 3) / 2))) then
    .some _ _ h
  else .zero

lemma P₁_eq (hF : ringChar F ≠ 2) (hΔ : (ofCubic α β γ).Δ ≠ 0) :
    P₁ α β γ = .some _ _ (nonsingular_of_equation hΔ (equation_P₁ hF α β γ)) := by
  rw [P₁, dite_eq_left (nonsingular_of_equation hΔ (equation_P₁ hF α β γ))]

/-- `d P₁ = q`. -/
theorem d_P₁ (hF : ringChar F ≠ 2) (hΔ : (ofCubic α β γ).Δ ≠ 0) :
    d (P₁ α β γ) = Fintype.card F := by
  rw [P₁_eq hF hΔ, d_some_of_x_eq _ (X ^ Fintype.card F) rfl, natDegree_X_pow]

/-! ### The height of `P₁ - P₀` -/

/-- `X ^ q - X = ∏ c, (X - C c)` over `F`. -/
private lemma X_pow_card_sub_X_eq_prod :
    (X ^ Fintype.card F - X : F[X]) = ∏ c : F, (X - C c) := by
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hroots := FiniteField.roots_X_pow_card_sub_X F
  have hmon : (X ^ Fintype.card F - X : F[X]).Monic :=
    monic_X_pow_sub (by rw [degree_X]; exact_mod_cast h1)
  have hcard : (X ^ Fintype.card F - X : F[X]).roots.card =
      (X ^ Fintype.card F - X : F[X]).natDegree := by
    rw [hroots, natDegree_X_pow_sub_X h1, Finset.card_val, Finset.card_univ]
  conv_lhs => rw [← prod_multiset_X_sub_C_of_monic_of_roots_card_eq hmon hcard, hroots]
  rfl

/-- Every `X - C c` divides `X ^ q - X`. -/
private lemma X_sub_C_dvd_X_pow_card_sub_X (c : F) :
    X - C c ∣ (X ^ Fintype.card F - X : F[X]) := by
  rw [dvd_iff_isRoot, IsRoot.def, eval_sub, eval_pow, eval_X, FiniteField.pow_card, sub_self]

variable (α β γ) in
/-- The numerator `N = D (D^m + 1)² - (α + T^q + T) (T^q - T)²` of `x(P₁ - P₀) / D`, where
`m = q / 2`. -/
private def d1Num : F[X] :=
  cubicPoly α β γ * (cubicPoly α β γ ^ (Fintype.card F / 2) + 1) ^ 2 -
    (C α + X ^ Fintype.card F + X) * (X ^ Fintype.card F - X) ^ 2

variable (α β γ) in
/-- `N = T^(2q+1) + (terms of degree at most 2q)`, using `D^q = g(T^q)`. -/
private lemma d1Num_eq (hF : ringChar F ≠ 2) :
    d1Num α β γ = X ^ (2 * Fintype.card F + 1) + (C β * X ^ Fintype.card F + C γ +
      2 * cubicPoly α β γ ^ (Fintype.card F / 2 + 1) + cubicPoly α β γ +
      X ^ (Fintype.card F + 2) + 2 * C α * X ^ (Fintype.card F + 1) - C α * X ^ 2 - X ^ 3) := by
  have hodd : 2 * (Fintype.card F / 2) + 1 = Fintype.card F := by
    have := FiniteField.odd_card_of_char_ne_two hF
    omega
  have he : cubicPoly α β γ ^ (2 * (Fintype.card F / 2) + 1) = (X ^ Fintype.card F) ^ 3 +
      C α * (X ^ Fintype.card F) ^ 2 + C β * X ^ Fintype.card F + C γ := by
    rw [hodd]
    exact cubicPoly_pow_card α β γ
  unfold d1Num
  linear_combination he

variable (α β γ) in
/-- `deg N = 2 q + 1`. -/
private lemma natDegree_d1Num (hF : ringChar F ≠ 2) :
    (d1Num α β γ).natDegree = 2 * Fintype.card F + 1 := by
  have hodd := FiniteField.odd_card_of_char_ne_two hF
  have h3 : 3 ≤ Fintype.card F := by
    have := Fintype.one_lt_card (α := F)
    omega
  rw [d1Num_eq α β γ hF, natDegree_add_eq_left_of_natDegree_lt] <;> rw [natDegree_X_pow]
  have hD : (cubicPoly α β γ ^ (Fintype.card F / 2 + 1)).natDegree ≤
      3 * (Fintype.card F / 2 + 1) := by
    refine natDegree_pow_le.trans ?_
    rw [natDegree_cubicPoly, mul_comm]
  have hc := natDegree_cubicPoly α β γ
  refine lt_of_le_of_lt (b := 2 * Fintype.card F) ?_ (by omega)
  repeat' first
    | with_reducible apply natDegree_sub_le_of_le'
    | with_reducible apply natDegree_add_le_of_degree_le
  · compute_degree
    omega
  · simp
  · refine natDegree_mul_le.trans ?_
    rw [natDegree_ofNat]
    omega
  · omega
  · rw [natDegree_X_pow]
    omega
  · compute_degree
    omega
  · compute_degree
    omega
  · rw [natDegree_X_pow]
    omega

/-- If `g(c) = 0`, then `(T - c)²` does not divide `D (D^m + 1)²`: `c` is a simple root of `D`
and `(D^m + 1)(c) = 1`. -/
private lemma not_sq_dvd_of_eval_eq_zero (hF : ringChar F ≠ 2) (hΔ : (ofCubic α β γ).Δ ≠ 0)
    {c : F} (h0 : (cubicPoly α β γ).eval c = 0) :
    ¬ (X - C c) ^ 2 ∣ cubicPoly α β γ * (cubicPoly α β γ ^ (Fintype.card F / 2) + 1) ^ 2 := by
  intro hDm
  have hm : 0 < Fintype.card F / 2 := by
    have := FiniteField.odd_card_of_char_ne_two hF
    have := Fintype.one_lt_card (α := F)
    omega
  have hcop : IsCoprime (X - C c) (cubicPoly α β γ ^ (Fintype.card F / 2) + 1) := by
    refine (irreducible_X_sub_C c).coprime_iff_not_dvd.2 fun h ↦ ?_
    rw [dvd_iff_isRoot, IsRoot.def, eval_add, eval_pow, h0, zero_pow hm.ne', eval_one,
      zero_add] at h
    exact one_ne_zero h
  have hD2 := (hcop.pow (m := 2) (n := 2)).dvd_of_dvd_mul_right hDm
  have := rootMultiplicity_cubicPoly_le_one hΔ c
  rw [← not_lt, ← Nat.succ_le_iff, le_rootMultiplicity_iff (cubicPoly_ne_zero α β γ)] at this
  exact this hD2

open scoped Classical in
/-- The group law on the twist: `x(P₁ - P₀) / D = N / (T^q - T)²`, so `d (P₁ - P₀)` is the
height of `N / (T^q - T)²`. -/
private lemma d_P₁_sub_P₀_eq (hF : ringChar F ≠ 2) (hΔ : (ofCubic α β γ).Δ ≠ 0) :
    d (P₁ α β γ - P₀ α β γ) = max
      (algebraMap F[X] (RatFunc F) (d1Num α β γ) /
        algebraMap F[X] (RatFunc F) ((X ^ Fintype.card F - X) ^ 2)).num.natDegree
      (algebraMap F[X] (RatFunc F) (d1Num α β γ) /
        algebraMap F[X] (RatFunc F) ((X ^ Fintype.card F - X) ^ 2)).denom.natDegree := by
  have hodd : (Fintype.card F + 3) / 2 = Fintype.card F / 2 + 2 := by
    have := FiniteField.odd_card_of_char_ne_two hF
    omega
  have hQ : (X ^ Fintype.card F - X : F[X]) ≠ 0 := X_pow_sub_X_ne_zero Fintype.one_lt_card
  have hQι : algebraMap F[X] (RatFunc F) (X ^ Fintype.card F - X) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).2 hQ
  have hDι := algebraMap_cubicPoly_ne_zero α β γ
  have hx : algebraMap F[X] (RatFunc F) (cubicPoly α β γ * X ^ Fintype.card F) ≠
      algebraMap F[X] (RatFunc F) (cubicPoly α β γ * X) := by
    intro h
    rw [map_mul, map_mul] at h
    exact hQ (sub_eq_zero.2 (RatFunc.algebraMap_injective _ (mul_left_cancel₀ hDι h)))
  rw [P₁_eq hF hΔ, P₀_eq hΔ, sub_eq_add_neg, Affine.Point.neg_some,
    Affine.Point.add_of_X_ne hx]
  refine d_some_eq_of_div _ ?_
  rw [Affine.slope_of_X_ne hx]
  simp only [Affine.addX, Affine.negY, twist, map_a₁, map_a₂, map_a₃,
    twistPoly_a₁, twistPoly_a₂, twistPoly_a₃, map_zero, zero_mul, sub_zero, add_zero,
    d1Num, hodd, map_mul, map_pow, map_sub, map_add, map_one] at hQι ⊢
  field_simp
  ring

variable [DecidableEq F]

variable (α β γ) in
/-- The exponent `1 + χ(g(c)) ∈ {0, 1, 2}` of `T - c` in the reduced denominator of
`N / (T^q - T)²`. -/
private def d1Exp (c : F) : ℕ := (1 + quadraticChar F ((cubicPoly α β γ).eval c)).toNat

variable (α β γ) in
/-- The reduced denominator `H = ∏_c (T - c)^(1 + χ(g(c)))` of `N / (T^q - T)²`. -/
private def d1Den : F[X] := ∏ c, (X - C c) ^ d1Exp α β γ c

variable (α β γ) in
/-- The common factor `G = ∏_c (T - c)^(1 - χ(g(c)))` of `N` and `(T^q - T)²`. -/
private def d1Gcd : F[X] := ∏ c, (X - C c) ^ (2 - d1Exp α β γ c)

private lemma d1Exp_le_two (c : F) : d1Exp α β γ c ≤ 2 := by
  rw [d1Exp]
  by_cases ha : (cubicPoly α β γ).eval c = 0
  · rw [ha, quadraticChar_zero]
    decide
  rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> decide

private lemma d1Gcd_mul_d1Den : d1Gcd α β γ * d1Den α β γ = (X ^ Fintype.card F - X) ^ 2 := by
  rw [X_pow_card_sub_X_eq_prod, ← Finset.prod_pow, d1Gcd, d1Den, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun c _ ↦ ?_
  rw [← pow_add, Nat.sub_add_cancel (d1Exp_le_two c)]

private lemma d1Gcd_ne_zero : d1Gcd α β γ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun c _ ↦ pow_ne_zero _ (X_sub_C_ne_zero c)

private lemma d1Den_ne_zero : d1Den α β γ ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun c _ ↦ pow_ne_zero _ (X_sub_C_ne_zero c)

private lemma natDegree_d1Den : (d1Den α β γ).natDegree = ∑ c, d1Exp α β γ c := by
  rw [d1Den, natDegree_prod_of_monic _ _ fun c _ ↦ (monic_X_sub_C c).pow _]
  simp

/-- `∑_c (1 + χ(g(c))) = q + S`. -/
private lemma sum_d1Exp :
    (∑ c, (d1Exp α β γ c : ℤ)) = Fintype.card F + cubicCharSum α β γ := by
  have h : ∀ c, (d1Exp α β γ c : ℤ) = 1 + quadraticChar F ((cubicPoly α β γ).eval c) := by
    intro c
    refine Int.toNat_of_nonneg ?_
    by_cases ha : (cubicPoly α β γ).eval c = 0
    · rw [ha, quadraticChar_zero]
      decide
    rcases quadraticChar_dichotomy ha with h | h <;> rw [h] <;> decide
  simp only [h, Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    mul_one, cubicCharSum]

/-- The three cases for `c ∈ F`: `g(c) = 0`; `g(c)` is a nonzero square; `g(c)` is not a square.
Euler's criterion gives `g(c)^(q/2) = χ(g(c))`. -/
private lemma d1Exp_cases (hF : ringChar F ≠ 2) (c : F) :
    ((cubicPoly α β γ).eval c = 0 ∧ d1Exp α β γ c = 1) ∨
    ((cubicPoly α β γ).eval c ≠ 0 ∧ (cubicPoly α β γ).eval c ^ (Fintype.card F / 2) = 1 ∧
      d1Exp α β γ c = 2) ∨
    ((cubicPoly α β γ).eval c ^ (Fintype.card F / 2) = -1 ∧ d1Exp α β γ c = 0) := by
  have hpow : (quadraticChar F ((cubicPoly α β γ).eval c) : F) =
      (cubicPoly α β γ).eval c ^ (Fintype.card F / 2) :=
    quadraticChar_eq_pow_of_char_ne_two' hF _
  by_cases ha : (cubicPoly α β γ).eval c = 0
  · refine Or.inl ⟨ha, ?_⟩
    rw [d1Exp, ha, quadraticChar_zero]
    rfl
  rcases quadraticChar_dichotomy ha with h | h
  · refine Or.inr (Or.inl ⟨ha, by rw [← hpow, h, Int.cast_one], ?_⟩)
    rw [d1Exp, h]
    rfl
  · refine Or.inr (Or.inr ⟨by rw [← hpow, h, Int.cast_neg, Int.cast_one], ?_⟩)
    rw [d1Exp, h]
    rfl

/-- `G` divides `N`: `T - c` divides both summands of `N` when `g(c) = 0`, and `(T - c)²` does
when `χ(g(c)) = -1`. -/
private lemma d1Gcd_dvd_d1Num (hF : ringChar F ≠ 2) : d1Gcd α β γ ∣ d1Num α β γ := by
  refine Finset.prod_dvd_of_coprime (fun a _ b _ hab ↦ ?_) fun c _ ↦ ?_
  · exact (pairwise_coprime_X_sub_C (K := F) (s := id) Function.injective_id hab).pow
  have hQ := X_sub_C_dvd_X_pow_card_sub_X c
  rcases d1Exp_cases (α := α) (β := β) (γ := γ) hF c with ⟨h0, he⟩ | ⟨_, _, he⟩ | ⟨hm, he⟩
  · rw [he, show 2 - 1 = 1 from rfl, pow_one]
    have hD : X - C c ∣ cubicPoly α β γ := dvd_iff_isRoot.2 h0
    exact dvd_sub (dvd_mul_of_dvd_left hD _) (dvd_mul_of_dvd_right (dvd_pow hQ two_ne_zero) _)
  · rw [he, pow_zero]
    exact one_dvd _
  · rw [he]
    have hD : X - C c ∣ cubicPoly α β γ ^ (Fintype.card F / 2) + 1 := by
      rw [dvd_iff_isRoot, IsRoot.def, eval_add, eval_pow, hm, eval_one, neg_add_cancel]
    exact dvd_sub (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hD 2) _)
      (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hQ 2) _)

/-- If `N = G M`, then `M` and `H` are coprime: no `T - c` with `1 + χ(g(c)) > 0` divides `M`.
For `χ(g(c)) = 1` this is `N(c) = 4 g(c) ≠ 0`; for `g(c) = 0` it is
`not_sq_dvd_of_eval_eq_zero`. -/
private lemma isCoprime_d1Den (hF : ringChar F ≠ 2) (hΔ : (ofCubic α β γ).Δ ≠ 0) {M : F[X]}
    (hM : d1Num α β γ = d1Gcd α β γ * M) : IsCoprime M (d1Den α β γ) := by
  refine IsCoprime.prod_right fun c _ ↦ ?_
  have hQ := X_sub_C_dvd_X_pow_card_sub_X c
  suffices hndvd : 0 < d1Exp α β γ c → ¬ X - C c ∣ M by
    rcases Nat.eq_zero_or_pos (d1Exp α β γ c) with h | h
    · rw [h, pow_zero]
      exact isCoprime_one_right
    · exact IsCoprime.pow_right ((irreducible_X_sub_C c).coprime_iff_not_dvd.2 (hndvd h)).symm
  intro hpos hdvd
  have hN : X - C c ∣ d1Num α β γ := hM ▸ dvd_mul_of_dvd_right hdvd _
  rcases d1Exp_cases (α := α) (β := β) (γ := γ) hF c with ⟨h0, he⟩ | ⟨h0, h1, _⟩ | ⟨_, he⟩
  · have hG : X - C c ∣ d1Gcd α β γ := by
      have := Finset.dvd_prod_of_mem (fun c ↦ (X - C c) ^ (2 - d1Exp α β γ c))
        (Finset.mem_univ c)
      rwa [he, show 2 - 1 = 1 from rfl, pow_one] at this
    have hN2 : (X - C c) ^ 2 ∣ d1Num α β γ := hM ▸ pow_two (X - C c) ▸ mul_dvd_mul hG hdvd
    refine not_sq_dvd_of_eval_eq_zero hF hΔ h0 ?_
    have := dvd_add hN2 (dvd_mul_of_dvd_right (pow_dvd_pow_of_dvd hQ 2)
      (C α + X ^ Fintype.card F + X))
    rwa [d1Num, sub_add_cancel] at this
  · rw [dvd_iff_isRoot, IsRoot.def, d1Num] at hN
    simp only [eval_sub, eval_mul, eval_pow, eval_add, eval_one, eval_X, eval_C,
      FiniteField.pow_card, sub_self, h1] at hN
    have h4 : (cubicPoly α β γ).eval c * 2 ^ 2 = 0 := by
      rw [← hN]
      ring
    exact mul_ne_zero h0 (pow_ne_zero 2 (Ring.two_ne_zero hF)) h4
  · omega

open scoped Classical in
/-- Manin's value `d (P₁ - P₀) = q + 1 + S`, where `S = ∑ₓ χ(g(x))`. -/
theorem d_P₁_sub_P₀ (hF : ringChar F ≠ 2) (hΔ : (ofCubic α β γ).Δ ≠ 0) :
    (d (P₁ α β γ - P₀ α β γ) : ℤ) = Fintype.card F + 1 + cubicCharSum α β γ := by
  obtain ⟨M, hM⟩ := d1Gcd_dvd_d1Num (α := α) (β := β) (γ := γ) hF
  have hN0 : d1Num α β γ ≠ 0 := by
    refine ne_zero_of_natDegree_gt (n := 0) ?_
    rw [natDegree_d1Num α β γ hF]
    omega
  have hM0 : M ≠ 0 := by
    rintro rfl
    rw [mul_zero] at hM
    exact hN0 hM
  have hGι : algebraMap F[X] (RatFunc F) (d1Gcd α β γ) ≠ 0 :=
    (map_ne_zero_iff _ (RatFunc.algebraMap_injective _)).2 d1Gcd_ne_zero
  have hx : algebraMap F[X] (RatFunc F) (d1Num α β γ) /
      algebraMap F[X] (RatFunc F) ((X ^ Fintype.card F - X) ^ 2) =
      algebraMap F[X] (RatFunc F) M / algebraMap F[X] (RatFunc F) (d1Den α β γ) := by
    rw [hM, ← d1Gcd_mul_d1Den, map_mul, map_mul, mul_div_mul_left _ _ hGι]
  obtain ⟨h1, h2⟩ := natDegree_num_denom_of_eq_div hM0 d1Den_ne_zero
    (isCoprime_d1Den hF hΔ hM) hx
  rw [d_P₁_sub_P₀_eq hF hΔ, h1, h2]
  have hdegN := natDegree_d1Num α β γ hF
  rw [hM, natDegree_mul d1Gcd_ne_zero hM0] at hdegN
  have hdegQ := congrArg natDegree (d1Gcd_mul_d1Den (α := α) (β := β) (γ := γ))
  rw [natDegree_mul d1Gcd_ne_zero d1Den_ne_zero, natDegree_pow,
    natDegree_X_pow_sub_X Fintype.one_lt_card] at hdegQ
  rw [max_eq_left (by omega), show M.natDegree = (d1Den α β γ).natDegree + 1 by omega,
    natDegree_d1Den, Nat.cast_add, Nat.cast_sum, sum_d1Exp, Nat.cast_one]
  ring

open scoped Classical in
/-- Manin's closed form: `d (P₁ - n • P₀) = n² + S n + q` for every `n : ℤ`. This is a two-sided
induction from the parallelogram law with `P = P₁ - n • P₀` and `Q = P₀`, starting from
`d P₁ = q` and `d (P₁ - P₀) = q + 1 + S`. -/
theorem d_P₁_sub_zsmul_P₀ (hF : ringChar F ≠ 2) (hΔ : (ofCubic α β γ).Δ ≠ 0) (n : ℤ) :
    (d (P₁ α β γ - n • P₀ α β γ) : ℤ) = n ^ 2 + cubicCharSum α β γ * n + Fintype.card F := by
  have hrec : ∀ m : ℤ, (d (P₁ α β γ - (m + 1) • P₀ α β γ) : ℤ) +
      d (P₁ α β γ - (m - 1) • P₀ α β γ) = 2 * d (P₁ α β γ - m • P₀ α β γ) + 2 := by
    intro m
    have h := parallelogram hΔ (P₁ α β γ - m • P₀ α β γ) (P₀ α β γ)
    rw [d_P₀ hΔ] at h
    have e1 : P₁ α β γ - m • P₀ α β γ + P₀ α β γ = P₁ α β γ - (m - 1) • P₀ α β γ := by
      rw [sub_zsmul, one_zsmul]
      abel
    have e2 : P₁ α β γ - m • P₀ α β γ - P₀ α β γ = P₁ α β γ - (m + 1) • P₀ α β γ := by
      rw [add_zsmul, one_zsmul]
      abel
    rw [e1, e2] at h
    omega
  refine eq_of_rec (f := fun n ↦ (d (P₁ α β γ - n • P₀ α β γ) : ℤ))
    (g := fun n ↦ n ^ 2 + cubicCharSum α β γ * n + Fintype.card F) ?_ ?_ hrec
    (fun m ↦ by ring) n
  · simp only [zero_zsmul, sub_zero, d_P₁ hF hΔ]
    ring
  · simp only [one_zsmul, d_P₁_sub_P₀ hF hΔ]
    ring

end Frobenius

end WeierstrassCurve.Manin

namespace WeierstrassCurve

/-- **Manin's bound** on the character sum: `S² ≤ 4 q` when `Y² = g(X)` is elliptic over a finite
field of odd characteristic with `q` elements. -/
theorem cubicCharSum_sq_le {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (hF : ringChar F ≠ 2) {α β γ : F} (hΔ : (ofCubic α β γ).Δ ≠ 0) :
    cubicCharSum α β γ ^ 2 ≤ 4 * (Fintype.card F : ℤ) := by
  have hodd : Odd (Fintype.card F : ℤ) := by
    have := FiniteField.odd_card_of_char_ne_two hF
    exact_mod_cast Nat.odd_iff.2 this
  exact Manin.sq_le_of_forall_nonneg hodd fun n ↦ by
    rw [← Manin.d_P₁_sub_zsmul_P₀ hF hΔ n]
    exact Nat.cast_nonneg _

/-- **Hasse's bound**: an elliptic curve `E` over a finite field `F` of odd characteristic with
`q` elements has `(#E(F) - (q + 1))² ≤ 4 q`. -/
theorem hasse_bound {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsElliptic] :
    ((Nat.card W.toAffine.Point : ℤ) - (Fintype.card F + 1)) ^ 2 ≤ 4 * Fintype.card F := by
  classical
  rw [natCard_point_eq hF W, add_sub_cancel_left]
  refine cubicCharSum_sq_le hF ?_
  rw [Δ_ofCubic W (Ring.two_ne_zero hF)]
  exact W.isUnit_Δ.ne_zero

/-- **Hasse's bound**, real form: `|#E(F) - (q + 1)| ≤ 2 √q`. -/
theorem abs_natCard_point_sub_le {F : Type*} [Field F] [Fintype F] (hF : ringChar F ≠ 2)
    (W : WeierstrassCurve F) [W.IsElliptic] :
    |(Nat.card W.toAffine.Point : ℝ) - (Fintype.card F + 1)| ≤
      2 * Real.sqrt (Fintype.card F) := by
  have h : ((Nat.card W.toAffine.Point : ℝ) - (Fintype.card F + 1)) ^ 2 ≤
      4 * Fintype.card F := by
    exact_mod_cast hasse_bound hF W
  calc |(Nat.card W.toAffine.Point : ℝ) - (Fintype.card F + 1)|
      ≤ Real.sqrt (4 * Fintype.card F) := Real.abs_le_sqrt h
    _ = 2 * Real.sqrt (Fintype.card F) := by
      rw [Real.sqrt_mul (by norm_num), show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num)]

/-- **Hasse's bound** over `ZMod p` for every prime `p` (Theorem 9.72 of [KatzLindell2020]):
`p + 1 - 2 √p ≤ #E(ZMod p) ≤ p + 1 + 2 √p`. -/
theorem hasse_bound_zmod {p : ℕ} [Fact p.Prime] (W : WeierstrassCurve (ZMod p))
    [W.IsElliptic] :
    (p : ℝ) + 1 - 2 * Real.sqrt p ≤ Nat.card W.toAffine.Point ∧
      (Nat.card W.toAffine.Point : ℝ) ≤ p + 1 + 2 * Real.sqrt p := by
  rcases eq_or_ne p 2 with rfl | hp
  · obtain ⟨h1, h5⟩ := natCard_point_zmod_two W
    have h1' : (1 : ℝ) ≤ Nat.card W.toAffine.Point := by exact_mod_cast h1
    have h5' : (Nat.card W.toAffine.Point : ℝ) ≤ 5 := by exact_mod_cast h5
    have hs : 1 ≤ Real.sqrt 2 := Real.one_le_sqrt.2 (by norm_num)
    simp only [Nat.cast_ofNat]
    exact ⟨by linarith, by linarith⟩
  · have hF : ringChar (ZMod p) ≠ 2 := by rwa [ZMod.ringChar_zmod_n]
    have h := abs_natCard_point_sub_le hF W
    rw [ZMod.card] at h
    obtain ⟨h1, h2⟩ := abs_le.1 h
    exact ⟨by linarith, by linarith⟩

end WeierstrassCurve
