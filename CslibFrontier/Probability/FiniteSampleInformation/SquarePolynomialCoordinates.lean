/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareRowCone

/-!
# Polynomial evaluation and affine simplex coordinates

One variable is replaced by `1 -` the sum of all remaining variables.  The
`MvPolynomial.optionEquivLeft` equivalence turns the kernel calculation into
ordinary one-variable evaluation.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquarePolynomialCoordinates.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators
open Set

namespace SquarePolynomial

open GeneralAsymmetricC1

/-- Positions in a finite joint-distribution matrix. -/
abbrev Var (n : ℕ) := Fin n × Fin n
/-- Real polynomials in the entries of a joint-distribution matrix. -/
abbrev Poly (n : ℕ) := MvPolynomial (Var n) ℝ

/-- Evaluate an entry polynomial at a real matrix. -/
@[expose] def peval {n : ℕ} (P : Poly n) (U : Mat n n) : ℝ :=
  MvPolynomial.eval (fun ia => U ia.1 ia.2) P

/-- One-sided fixed-alphabet DPI for the polynomial evaluation on the simplex. -/
@[expose] def PolynomialDPI {n : ℕ} (P : Poly n) : Prop := DPI (peval P)
/-- Vanishing on every independent square joint law. -/
@[expose] def PolynomialRKO {n : ℕ} (P : Poly n) : Prop := RKO (peval P)

lemma peval_contDiff {n : ℕ} (P : Poly n) :
    ContDiff ℝ 1 (peval P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have heq : peval (MvPolynomial.C c : Poly n) = fun _ => c := by
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

/-- The determinant of the generic square matrix. -/
@[expose] def detPoly (n : ℕ) : Poly n :=
  Matrix.det (Matrix.mvPolynomialX (Fin n) (Fin n) ℝ)

lemma peval_detPoly {n : ℕ} (U : Mat n n) :
    peval (detPoly n) U = Matrix.det (Matrix.of U) := by
  exact Matrix.eval_det_mvPolynomialX (Fin n) ℝ (fun ia => U ia.1 ia.2)

section Dehomogenization

variable {σ R : Type*} [CommRing R] [Fintype σ] [DecidableEq σ]

/-- All variables except one distinguished coordinate. -/
abbrev Free (star : σ) := {i : σ // i ≠ star}

/-- `Option (Free star)` enumerates `star` followed by all other variables. -/
@[expose] def optionFreeEquiv (star : σ) : Option (Free star) ≃ σ where
  toFun
    | none => star
    | some i => i.1
  invFun i := if h : i = star then none else some ⟨i, h⟩
  left_inv o := by
    cases o with
    | none => simp
    | some i => simp [i.2]
  right_inv i := by
    by_cases h : i = star
    · subst i
      simp
    · simp [h]

/-- Curry the distinguished variable into an ordinary univariate polynomial. -/
@[expose] def toNested (star : σ) :
    MvPolynomial σ R ≃ₐ[R] Polynomial (MvPolynomial (Free star) R) :=
  (MvPolynomial.renameEquiv R (optionFreeEquiv star).symm).trans
    (MvPolynomial.optionEquivLeft R (Free star))

omit [Fintype σ] in
@[simp] lemma toNested_X_star (star : σ) :
    toNested (R := R) star (MvPolynomial.X star) = Polynomial.X := by
  simp [toNested, optionFreeEquiv]

omit [Fintype σ] in
@[simp] lemma toNested_X_ne (star : σ) (i : σ) (hi : i ≠ star) :
    toNested (R := R) star (MvPolynomial.X i) =
      Polynomial.C (MvPolynomial.X (⟨i, hi⟩ : Free star)) := by
  simp [toNested, optionFreeEquiv, hi]

/-- The sum of the undistinguished coordinate variables. -/
def freeSum (star : σ) : MvPolynomial (Free star) R :=
  ∑ i, MvPolynomial.X i

lemma toNested_sum_X (star : σ) :
    toNested (R := R) star (∑ i : σ, MvPolynomial.X i) =
      Polynomial.X + Polynomial.C (freeSum (R := R) star) := by
  rw [map_sum]
  calc
    ∑ i : σ, toNested (R := R) star (MvPolynomial.X i) =
        ∑ o : Option (Free star),
          toNested (R := R) star (MvPolynomial.X (optionFreeEquiv star o)) := by
      apply Fintype.sum_equiv (optionFreeEquiv star).symm
      intro i
      simp
    _ = Polynomial.X + Polynomial.C (freeSum (R := R) star) := by
      rw [Fintype.sum_option]
      simp only [optionFreeEquiv]
      congr 1
      · exact toNested_X_star (R := R) star
      · rw [freeSum, map_sum]
        apply Finset.sum_congr rfl
        intro i hi
        exact toNested_X_ne (R := R) star i.1 i.2

/-- The distinguished coordinate determined by the total-mass-one equation. -/
def simplexRoot (star : σ) : MvPolynomial (Free star) R :=
  1 - freeSum (R := R) star

/-- The total-coordinate polynomial, defined through the nested equivalence. -/
@[expose] def tauPoly (star : σ) : MvPolynomial σ R :=
  (toNested (R := R) star).symm
    (Polynomial.X + Polynomial.C (freeSum (R := R) star))

/-- Substitute the simplex equation into the distinguished variable. -/
@[expose] def dehomSimplex (star : σ) :
    MvPolynomial σ R →+* MvPolynomial (Free star) R :=
  (Polynomial.evalRingHom (simplexRoot (R := R) star)).comp
    (toNested (R := R) star).toRingHom

@[simp] lemma toNested_tauPoly (star : σ) :
    toNested (R := R) star (tauPoly (R := R) star) =
      Polynomial.X + Polynomial.C (freeSum (R := R) star) := by
  simp [tauPoly]

@[simp] lemma dehomSimplex_tau_sub_one (star : σ) :
    dehomSimplex (R := R) star (tauPoly (R := R) star - 1) = 0 := by
  simp [dehomSimplex, simplexRoot]

@[simp] lemma dehomSimplex_X_star (star : σ) :
    dehomSimplex (R := R) star (MvPolynomial.X star) =
      simplexRoot (R := R) star := by
  simp [dehomSimplex]

@[simp] lemma dehomSimplex_X_ne (star : σ) (i : σ) (hi : i ≠ star) :
    dehomSimplex (R := R) star (MvPolynomial.X i) =
      MvPolynomial.X (⟨i, hi⟩ : Free star) := by
  simp [dehomSimplex, hi]

/-- Recover all coordinates from the undistinguished coordinates on the mass-one hyperplane. -/
@[expose] def reconstruct (star : σ) (x : Free star → R) : σ → R :=
  fun i => if h : i = star then
    1 - ∑ j, x j
  else x ⟨i, h⟩

/-- Insert a value for the distinguished variable into an assignment of all
remaining variables. -/
@[expose] def insertDistinguished (star : σ) (r : R) (x : Free star → R) : σ → R :=
  fun i => if h : i = star then r else x ⟨i, h⟩

omit [Fintype σ] in
lemma toNested_map_eval (star : σ) (P : MvPolynomial σ R)
    (r : R) (x : Free star → R) :
    Polynomial.eval r
        (Polynomial.map (MvPolynomial.eval x) (toNested (R := R) star P)) =
      MvPolynomial.eval (insertDistinguished star r x) P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [toNested]
  | add P Q hP hQ => simp [hP, hQ]
  | mul_X P i hP =>
      rw [map_mul, Polynomial.map_mul, Polynomial.eval_mul,
        MvPolynomial.eval_mul, hP]
      by_cases hi : i = star
      · subst i
        simp [insertDistinguished]
      · simp [insertDistinguished, hi]

lemma dehomSimplex_eval (star : σ)
    (P : MvPolynomial σ R) (x : Free star → R) :
    MvPolynomial.eval x (dehomSimplex (R := R) star P) =
      MvPolynomial.eval (reconstruct star x) P := by
  let lhs : MvPolynomial σ R →+* R :=
    (MvPolynomial.eval x).comp (dehomSimplex (R := R) star)
  let rhs : MvPolynomial σ R →+* R :=
    MvPolynomial.eval (reconstruct star x)
  have hhom : lhs = rhs := by
    apply MvPolynomial.ringHom_ext
    · intro r
      simp [lhs, rhs, dehomSimplex, toNested]
    · intro i
      by_cases hi : i = star
      · subst i
        simp [lhs, rhs, reconstruct, simplexRoot, freeSum]
      · simp [lhs, rhs, reconstruct, hi]
  exact DFunLike.congr_fun hhom P

theorem kernel_dehomSimplex (star : σ) (P : MvPolynomial σ R) :
    dehomSimplex (R := R) star P = 0 ↔
      ∃ K : MvPolynomial σ R,
        P = (tauPoly (R := R) star - 1) * K := by
  constructor
  · intro hP
    let p : Polynomial (MvPolynomial (Free star) R) :=
      toNested (R := R) star P
    have heval : p.eval (simplexRoot (R := R) star) = 0 := hP
    have hdvd : Polynomial.X - Polynomial.C (simplexRoot (R := R) star) ∣ p := by
      have h := Polynomial.X_sub_C_dvd_sub_C_eval
        (p := p) (a := simplexRoot (R := R) star)
      simpa [heval] using h
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨(toNested (R := R) star).symm q, ?_⟩
    apply (toNested (R := R) star).injective
    rw [map_mul, AlgEquiv.apply_symm_apply]
    have htau : toNested (R := R) star (tauPoly (R := R) star - 1) =
        Polynomial.X - Polynomial.C (simplexRoot (R := R) star) := by
      simp [simplexRoot]
      ring
    rw [htau]
    exact hq
  · rintro ⟨K, rfl⟩
    simp

/-- A section of simplex dehomogenization, obtained by regarding a polynomial
in the free variables as a constant polynomial in the eliminated variable. -/
def rehomSimplex (star : σ) (Q : MvPolynomial (Free star) R) :
    MvPolynomial σ R :=
  (toNested (R := R) star).symm (Polynomial.C Q)

@[simp] lemma dehomSimplex_rehomSimplex (star : σ)
    (Q : MvPolynomial (Free star) R) :
    dehomSimplex (R := R) star (rehomSimplex (R := R) star Q) = Q := by
  simp [dehomSimplex, rehomSimplex]

/-- Lift a square factorization in simplex coordinates to an identity in the
original multivariate polynomial ring. -/
theorem lift_dehom_square_factor (star : σ)
    (P D : MvPolynomial σ R) (Qbar : MvPolynomial (Free star) R)
    (hfactor : dehomSimplex (R := R) star P =
      dehomSimplex (R := R) star D ^ 2 * Qbar) :
    ∃ Q K : MvPolynomial σ R,
      P = D ^ 2 * Q + (tauPoly (R := R) star - 1) * K := by
  let Q : MvPolynomial σ R := rehomSimplex (R := R) star Qbar
  have hzero : dehomSimplex (R := R) star (P - D ^ 2 * Q) = 0 := by
    simp [hfactor, Q]
  obtain ⟨K, hK⟩ := (kernel_dehomSimplex (R := R) star (P - D ^ 2 * Q)).mp hzero
  refine ⟨Q, K, ?_⟩
  calc
    P = D ^ 2 * Q + (P - D ^ 2 * Q) := by ring
    _ = D ^ 2 * Q + (tauPoly (R := R) star - 1) * K := by rw [hK]

end Dehomogenization

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
