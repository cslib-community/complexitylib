/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareSimplexTheorem

/-!
# Polynomial evaluation on wide rectangular matrices

This file contains only the probability-facing rectangular polynomial API.
It reuses `GeneralAsymmetricC1`'s rectangular matrix, simplex, DPI, and RKO
definitions and the compiled generic tau-homogenization.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`WidePolynomialSetup.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open scoped BigOperators

namespace WidePolynomial

open GeneralAsymmetricC1

/-- Positions in a rectangular joint-distribution matrix. -/
abbrev WideVar (n m : ℕ) := Fin n × Fin m
/-- Real polynomials in rectangular matrix entries. -/
abbrev WidePoly (n m : ℕ) := MvPolynomial (WideVar n m) ℝ

/-- Evaluate an entry polynomial at a real matrix. -/
@[expose] def peval {n m : ℕ} (P : WidePoly n m) (U : Mat n m) : ℝ :=
  MvPolynomial.eval (fun ia => U ia.1 ia.2) P

/-- One-sided fixed-alphabet DPI for the polynomial evaluation on the simplex. -/
@[expose] def PolynomialDPI {n m : ℕ} (P : WidePoly n m) : Prop :=
  DPI (peval P)

/-- Vanishing of the polynomial evaluation at independent joint laws. -/
@[expose] def PolynomialRKO {n m : ℕ} (P : WidePoly n m) : Prop :=
  RKO (peval P)

lemma peval_contDiff {n m : ℕ} (P : WidePoly n m) :
    ContDiff ℝ 1 (peval P) := by
  induction P using MvPolynomial.induction_on with
  | C c =>
      have heq : peval (MvPolynomial.C c : WidePoly n m) = fun _ => c := by
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

/-- A distinguished rectangular matrix entry for eliminating the simplex equation. -/
@[expose] def wideStar {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : WideVar n m :=
  (⟨0, hn⟩, ⟨0, hm⟩)

/-- The total-mass polynomial in rectangular matrix coordinates. -/
@[expose] def tauPolyWide {n m : ℕ} (hn : 0 < n) (hm : 0 < m) : WidePoly n m :=
  SquarePolynomial.tauPoly (R := ℝ) (wideStar hn hm)

/-- Homogenize using total mass, preserving evaluation on the simplex. -/
@[expose] def tauHomogenizeWide {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    (P : WidePoly n m) : WidePoly n m :=
  SquarePolynomial.tauHomogenize (R := ℝ) (wideStar hn hm) P

lemma tauPolyWide_eq_sum_X {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    tauPolyWide hn hm = ∑ ia : WideVar n m, MvPolynomial.X ia := by
  exact SquarePolynomial.tauPoly_eq_sum_X (R := ℝ) (wideStar hn hm)

lemma peval_tauPolyWide_eq_mass {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (U : Mat n m) :
    peval (tauPolyWide hn hm) U = mass U := by
  rw [tauPolyWide_eq_sum_X]
  simp only [peval, MvPolynomial.eval_sum, MvPolynomial.eval_X]
  rw [Fintype.sum_prod_type]
  rfl

lemma tauHomogenizeWide_isHomogeneous {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (P : WidePoly n m) :
    (tauHomogenizeWide hn hm P).IsHomogeneous P.totalDegree :=
  SquarePolynomial.tauHomogenize_isHomogeneous (wideStar hn hm) P

lemma tauHomogenizeWide_sub_original {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (P : WidePoly n m) :
    ∃ K : WidePoly n m,
      tauHomogenizeWide hn hm P - P =
        (tauPolyWide hn hm - 1) * K :=
  SquarePolynomial.tauHomogenize_sub_mem_simplex_kernel
    (R := ℝ) (wideStar hn hm) P

end WidePolynomial

end

end Cslib.FiniteSampleInformation
