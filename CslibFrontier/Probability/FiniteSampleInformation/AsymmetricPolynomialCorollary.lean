/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquarePolynomialCoordinates
public import CslibFrontier.Probability.FiniteSampleInformation.SquareOpenBoxIdentity

/-!
# Polynomial corollary in the asymmetric case

The C¹ vanishing theorem for `n > m` is combined with elimination of one
simplex coordinate.  Vanishing on a small positive open box makes the
dehomogenized polynomial zero, so the original polynomial is a multiple of
the total-mass equation.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`AsymmetricPolynomialCorollary.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators
open Set

namespace AsymmetricPolynomial

open GeneralAsymmetricC1

/-- Positions in a finite joint-distribution matrix. -/
abbrev Var (n m : ℕ) := Fin n × Fin m
/-- Real polynomials in the entries of a joint-distribution matrix. -/
abbrev Poly (n m : ℕ) := MvPolynomial (Var n m) ℝ

/-- Evaluate an entry polynomial at a real matrix. -/
@[expose] def peval {n m : ℕ} (P : Poly n m) (U : Mat n m) : ℝ :=
  MvPolynomial.eval (fun ia => U ia.1 ia.2) P

/-- One-sided fixed-alphabet DPI for the polynomial evaluation on the simplex. -/
@[expose] def PolynomialDPI {n m : ℕ} (P : Poly n m) : Prop := DPI (peval P)
/-- Vanishing on every independent joint law. -/
@[expose] def PolynomialRKO {n m : ℕ} (P : Poly n m) : Prop := RKO (peval P)

/-- The total-mass polynomial for a rectangular table. -/
@[expose] def tauPoly (n m : ℕ) : Poly n m :=
  ∑ ia : Var n m, MvPolynomial.X ia

lemma peval_contDiff {n m : ℕ} (P : Poly n m) :
    ContDiff ℝ 1 (peval P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have heq : peval (MvPolynomial.C c : Poly n m) = fun _ => c := by
        funext U
        simp [peval]
      rw [heq]
      fun_prop
  | add P Q hP hQ =>
      have heq : peval (P + Q) = fun U => peval P U + peval Q U := by
        funext U
        simp [peval]
      rw [heq]
      exact hP.add hQ
  | mul_X P ia hP =>
      have heq : peval (P * MvPolynomial.X ia) =
          fun U => peval P U * U ia.1 ia.2 := by
        funext U
        simp [peval]
      rw [heq]
      exact hP.mul (by fun_prop)

lemma sum_reconstruct
    {σ : Type*} [Fintype σ] [DecidableEq σ]
    (star : σ) (x : SquarePolynomial.Free star → ℝ) :
    ∑ i : σ, SquarePolynomial.reconstruct star x i = 1 := by
  calc
    ∑ i : σ, SquarePolynomial.reconstruct star x i =
        ∑ o : Option (SquarePolynomial.Free star),
          SquarePolynomial.reconstruct star x
            (SquarePolynomial.optionFreeEquiv star o) := by
      apply Fintype.sum_equiv (SquarePolynomial.optionFreeEquiv star).symm
      intro i
      simp
    _ = SquarePolynomial.reconstruct star x star +
        ∑ i : SquarePolynomial.Free star,
          SquarePolynomial.reconstruct star x i.1 := by
      rw [Fintype.sum_option]
      rfl
    _ = (1 - ∑ i, x i) + ∑ i, x i := by
      congr 1
      · simp [SquarePolynomial.reconstruct]
      · apply Finset.sum_congr rfl
        intro i hi
        simp [SquarePolynomial.reconstruct, i.2]
    _ = 1 := by ring

/-- If `n > m ≥ 2`, an admissible rectangular polynomial is a multiple of
the total-mass equation `tau - 1`. -/
theorem asymmetric_polynomial_mem_simplex_ideal
    {n m : ℕ} (hm : 2 ≤ m) (hnm : m < n)
    (P : Poly n m) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    ∃ Q : Poly n m, P = (tauPoly n m - 1) * Q := by
  let : NeZero m := ⟨by omega⟩
  let : NeZero n := ⟨by omega⟩
  have hvanish : ∀ U : Mat n m, Simplex U → peval P U = 0 :=
    general_asymmetric_simplex_C1 hm hnm (peval P) (peval_contDiff P)
      hDPI hRKO
  let star : Var n m := ((0 : Fin n), (0 : Fin m))
  let Free := SquarePolynomial.Free star
  let k : ℕ := Fintype.card Free
  let c : ℝ := 1 / (2 * ((k : ℝ) + 1))
  have hcpos : 0 < c := by
    dsimp [c]
    positivity
  have hfree : (Finset.univ : Finset Free).Nonempty := by
    let j : Fin m := ⟨1, by omega⟩
    let other : Var n m := ((0 : Fin n), j)
    have hother : other ≠ star := by
      intro h
      have hj := congrArg (fun ia : Var n m => ia.2.val) h
      simp [other, star, j] at hj
    exact ⟨⟨other, hother⟩, Finset.mem_univ _⟩
  have hkc_lt_one : (k : ℝ) * c < 1 := by
    have hden : 0 < 2 * ((k : ℝ) + 1) := by positivity
    have hklt : (k : ℝ) < 2 * ((k : ℝ) + 1) := by nlinarith
    have hdiv : (k : ℝ) / (2 * ((k : ℝ) + 1)) < 1 :=
      (div_lt_one hden).2 hklt
    simpa [c, div_eq_mul_inv] using hdiv
  have hdehom :
      SquarePolynomial.dehomSimplex (R := ℝ) star P = 0 := by
    apply SquarePolynomial.mvPolynomial_eq_zero_of_eval_eq_zero_on_open_box
      (SquarePolynomial.dehomSimplex (R := ℝ) star P)
      (fun _ => 0) (fun _ => c)
    · intro i
      simpa using hcpos
    · intro x hx
      have hsum_lt_const : (∑ i : Free, x i) < ∑ _i : Free, c := by
        apply Finset.sum_lt_sum_of_nonempty hfree
        intro i hi
        exact (hx i).2
      have hsum : (∑ i : Free, x i) < 1 := by
        calc
          (∑ i : Free, x i) < ∑ _i : Free, c := hsum_lt_const
          _ = (k : ℝ) * c := by simp [k]
          _ < 1 := hkc_lt_one
      let U : Mat n m := fun i a =>
        SquarePolynomial.reconstruct star x (i, a)
      have hU : Simplex U := by
        constructor
        · intro i a
          by_cases hia : (i, a) = star
          · change 0 ≤ SquarePolynomial.reconstruct star x (i, a)
            rw [show SquarePolynomial.reconstruct star x (i, a) =
              1 - ∑ j, x j by
                simp [SquarePolynomial.reconstruct, hia]]
            exact sub_nonneg.mpr hsum.le
          · have hxpos := (hx ⟨(i, a), hia⟩).1
            simpa [U, SquarePolynomial.reconstruct, hia] using hxpos.le
        · rw [mass]
          change (∑ i : Fin n, ∑ a : Fin m,
            SquarePolynomial.reconstruct star x (i, a)) = 1
          rw [← Fintype.sum_prod_type]
          exact sum_reconstruct star x
      rw [SquarePolynomial.dehomSimplex_eval]
      exact hvanish U hU
  obtain ⟨Q, hQ⟩ :=
    (SquarePolynomial.kernel_dehomSimplex (R := ℝ) star P).mp hdehom
  have htau : SquarePolynomial.tauPoly (R := ℝ) star = tauPoly n m := by
    apply (SquarePolynomial.toNested (R := ℝ) star).injective
    rw [SquarePolynomial.toNested_tauPoly]
    exact (SquarePolynomial.toNested_sum_X (R := ℝ) star).symm
  refine ⟨Q, ?_⟩
  rw [htau] at hQ
  exact hQ

end AsymmetricPolynomial


end

end Cslib.FiniteSampleInformation
