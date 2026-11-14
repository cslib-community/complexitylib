/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareDoubleContactOnBox

/-!
# Cleared double contact and determinant-square descent

The rational graph root is used only after the two contact identities have
been converted to identities in the coefficient polynomial ring.  The latter
are then mapped to the fraction field, where the one-variable double-root
lemma applies; the compiled Gauss theorem descends the result.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareDeterminantGaussIntegration.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace SquarePolynomial

/-- The coefficient ring after separating the distinguished determinant entry. -/
abbrev PivotCoeffRing (m : ℕ) := MvPolynomial (DetCoeffVar m) ℝ

/-- The tau-homogenized polynomial expressed in the distinguished pivot coordinate. -/
def tauHomNested {m : ℕ} (hm : 0 < m) (P : Poly (m + 1)) :
    Polynomial (PivotCoeffRing m) :=
  toNested (R := ℝ) (pivotZero m)
    (tauHomogenize (R := ℝ)
      (simplexStar (by omega : 2 ≤ m + 1)) P)

/-- Degree in the pivot variable of the nested homogenized polynomial. -/
def tauHomNestedDegree {m : ℕ} (hm : 0 < m) (P : Poly (m + 1)) : ℕ :=
  (tauHomNested hm P).natDegree

/-- The pivot-root value with its denominator cleared. -/
def tauHomClearedValue {m : ℕ} (hm : 0 < m) (P : Poly (m + 1)) :
    PivotCoeffRing m :=
  clearLinearRoot (tauHomNestedDegree hm P) (tauHomNested hm P)
    (detPivotLeading ℝ m) (detPivotRemainder ℝ m)

/-- The pivot-root derivative with its denominator cleared. -/
def tauHomClearedDerivative {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) : PivotCoeffRing m :=
  clearLinearRoot (tauHomNestedDegree hm P)
    (Polynomial.derivative (tauHomNested hm P))
    (detPivotLeading ℝ m) (detPivotRemainder ℝ m)

lemma eval_tauHomNested {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (y : DetCoeffVar m → ℝ) :
    Polynomial.map (MvPolynomial.eval y) (tauHomNested hm P) =
      tauHomPivotPolynomial hm P y := by
  rfl

lemma eval_tauHomClearedValue {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (y : DetCoeffVar m → ℝ)
    (ha : graphLeadingValue m y ≠ 0) :
    MvPolynomial.eval y (tauHomClearedValue hm P) =
      graphLeadingValue m y ^ tauHomNestedDegree hm P *
        Polynomial.eval (graphRoot m y) (tauHomPivotPolynomial hm P y) := by
  have hmap := map_clearLinearRoot_eq_pow_mul_eval
    (MvPolynomial.eval y) (tauHomNestedDegree hm P) (tauHomNested hm P)
    (detPivotLeading ℝ m) (detPivotRemainder ℝ m) le_rfl ha
  simpa [tauHomClearedValue, graphLeadingValue, graphRemainderValue,
    graphRoot, eval_tauHomNested] using hmap

lemma eval_tauHomClearedDerivative {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (y : DetCoeffVar m → ℝ)
    (ha : graphLeadingValue m y ≠ 0) :
    MvPolynomial.eval y (tauHomClearedDerivative hm P) =
      graphLeadingValue m y ^ tauHomNestedDegree hm P *
        Polynomial.eval (graphRoot m y)
          (Polynomial.derivative (tauHomPivotPolynomial hm P y)) := by
  have hdeg : (Polynomial.derivative (tauHomNested hm P)).natDegree ≤
      tauHomNestedDegree hm P := by
    exact (Polynomial.natDegree_derivative_le _).trans (Nat.sub_le _ _)
  have hmap := map_clearLinearRoot_eq_pow_mul_eval
    (MvPolynomial.eval y) (tauHomNestedDegree hm P)
    (Polynomial.derivative (tauHomNested hm P))
    (detPivotLeading ℝ m) (detPivotRemainder ℝ m) hdeg ha
  rw [← Polynomial.derivative_map, eval_tauHomNested] at hmap
  simpa [tauHomClearedDerivative, graphLeadingValue, graphRemainderValue,
    graphRoot] using hmap

theorem tauHomClearedValue_eq_zero {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    tauHomClearedValue hm P = 0 := by
  obtain ⟨l, u, hlu, hcontact⟩ :=
    tauHomPivotPolynomial_double_contact_on_box hm P hDPI hRKO
  apply mvPolynomial_eq_zero_of_eval_eq_zero_on_open_box
    (tauHomClearedValue hm P) l u hlu
  intro y hy
  obtain ⟨ha, hvalue, hderiv⟩ := hcontact y hy
  rw [eval_tauHomClearedValue hm P y ha, hvalue, mul_zero]

theorem tauHomClearedDerivative_eq_zero {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    tauHomClearedDerivative hm P = 0 := by
  obtain ⟨l, u, hlu, hcontact⟩ :=
    tauHomPivotPolynomial_double_contact_on_box hm P hDPI hRKO
  apply mvPolynomial_eq_zero_of_eval_eq_zero_on_open_box
    (tauHomClearedDerivative hm P) l u hlu
  intro y hy
  obtain ⟨ha, hvalue, hderiv⟩ := hcontact y hy
  rw [eval_tauHomClearedDerivative hm P y ha, hderiv, mul_zero]

lemma detPivotLeading_real_ne_zero (m : ℕ) :
    detPivotLeading ℝ m ≠ 0 := by
  intro hzero
  have hbase := graphLeadingValue_base_ne m
  apply hbase
  simp [graphLeadingValue, hzero]

theorem det_sq_dvd_tauHom_succ {m : ℕ} (hm : 0 < m)
    (P : Poly (m + 1)) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    ∃ Q : Poly (m + 1),
      tauHomogenize (R := ℝ)
          (simplexStar (by omega : 2 ≤ m + 1)) P =
        detPoly (m + 1) ^ 2 * Q := by
  let A := PivotCoeffRing m
  let L := FractionRing A
  let f : A →+* L := algebraMap A L
  let p : Polynomial A := tauHomNested hm P
  let a : A := detPivotLeading ℝ m
  let b : A := detPivotRemainder ℝ m
  let N : ℕ := tauHomNestedDegree hm P
  have haA : a ≠ 0 := detPivotLeading_real_ne_zero m
  have haL : f a ≠ 0 := by
    intro h
    apply haA
    exact (IsFractionRing.injective A L) (by simpa [f] using h)
  have hvalueProduct :
      f a ^ N * Polynomial.eval (-f b / f a) (p.map f) = 0 := by
    rw [← map_clearLinearRoot_eq_pow_mul_eval f N p a b le_rfl haL]
    change f (tauHomClearedValue hm P) = 0
    rw [tauHomClearedValue_eq_zero hm P hDPI hRKO, map_zero]
  have hvalue : Polynomial.eval (-f b / f a) (p.map f) = 0 :=
    (mul_eq_zero.mp hvalueProduct).resolve_left (pow_ne_zero N haL)
  have hdegDerivative : p.derivative.natDegree ≤ N := by
    exact (Polynomial.natDegree_derivative_le p).trans (Nat.sub_le _ _)
  have hderivativeProduct :
      f a ^ N * Polynomial.eval (-f b / f a) (p.derivative.map f) = 0 := by
    rw [← map_clearLinearRoot_eq_pow_mul_eval f N p.derivative a b
      hdegDerivative haL]
    change f (tauHomClearedDerivative hm P) = 0
    rw [tauHomClearedDerivative_eq_zero hm P hDPI hRKO, map_zero]
  have hderivativeMapped :
      Polynomial.eval (-f b / f a) (p.derivative.map f) = 0 :=
    (mul_eq_zero.mp hderivativeProduct).resolve_left (pow_ne_zero N haL)
  have hderivative :
      Polynomial.eval (-f b / f a) (Polynomial.derivative (p.map f)) = 0 := by
    simpa using hderivativeMapped
  have hlinear :
      (Polynomial.C (f a) * Polynomial.X + Polynomial.C (f b)) ^ 2 ∣
        p.map f :=
    affine_linear_sq_dvd_of_eval_derivative_eq_zero
      (f a) (f b) haL (p.map f) hvalue hderivative
  let H : Poly (m + 1) :=
    tauHomogenize (R := ℝ)
      (simplexStar (by omega : 2 ≤ m + 1)) P
  have hfraction :
      ((toNested (R := ℝ) (pivotZero m)
          (genericDetPoly ℝ (m + 1)) ^ 2).map f) ∣
        (toNested (R := ℝ) (pivotZero m) H).map f := by
    rw [genericDetPoly_pivot_nested]
    simpa [p, a, b, H, tauHomNested] using hlinear
  have hgauss : genericDetPoly ℝ (m + 1) ^ 2 ∣ H :=
    genericDetPoly_sq_dvd_of_pivot_fraction_dvd hm H hfraction
  obtain ⟨Q, hQ⟩ := hgauss
  exact ⟨Q, hQ⟩

theorem det_sq_dvd_tauHom
    {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    ∃ Q : Poly n,
      tauHomogenize (R := ℝ) (simplexStar hn) P =
        detPoly n ^ 2 * Q := by
  cases n with
  | zero => omega
  | succ m =>
      have hm : 0 < m := by omega
      exact det_sq_dvd_tauHom_succ hm P hDPI hRKO

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
