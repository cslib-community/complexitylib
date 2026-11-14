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
# Degree lower bound in the square case

The tau-homogenization has the same total degree as the original polynomial.
If the simplex restriction is nonzero, the homogenization is nonzero; its
determinant-square factor therefore forces total degree at least `2 * n`.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareDegreeBound.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

namespace SquarePolynomial

open GeneralAsymmetricC1

lemma detPoly_isHomogeneous (n : ℕ) :
    (detPoly n).IsHomogeneous n := by
  rw [detPoly, Matrix.det_apply']
  apply MvPolynomial.IsHomogeneous.sum
  intro e he
  have hprod : MvPolynomial.IsHomogeneous
      (∏ i : Fin n,
        Matrix.mvPolynomialX (Fin n) (Fin n) ℝ (e i) i) n := by
    simpa using MvPolynomial.IsHomogeneous.prod Finset.univ
      (fun i : Fin n => Matrix.mvPolynomialX (Fin n) (Fin n) ℝ (e i) i)
      (fun _ => 1) (fun i hi => MvPolynomial.isHomogeneous_X ℝ (e i, i))
  simpa using hprod.C_mul (((Equiv.Perm.sign e : ℤ) : ℝ))

lemma totalDegree_detPoly_sq (n : ℕ) :
    (detPoly n ^ 2).totalDegree = 2 * n := by
  have hdet : detPoly n ≠ 0 :=
    Matrix.det_mvPolynomialX_ne_zero (Fin n) ℝ
  have hdegree : (detPoly n).totalDegree = n :=
    (detPoly_isHomogeneous n).totalDegree hdet
  rw [pow_two, MvPolynomial.totalDegree_mul_of_isDomain hdet hdet, hdegree]
  omega

/-- A square admissible polynomial which is nonzero somewhere on the simplex
has total degree at least `2 * n`. -/
theorem square_simplex_totalDegree_lower_bound
    {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P)
    (hnonzero : ∃ U : Mat n n, Simplex U ∧ peval P U ≠ 0) :
    2 * n ≤ P.totalDegree := by
  let H : Poly n :=
    tauHomogenize (R := ℝ) (simplexStar hn) P
  obtain ⟨Q, hfactor⟩ := det_sq_dvd_tauHom hn P hDPI hRKO
  obtain ⟨U, hU, hPU⟩ := hnonzero
  have hHU : peval H U = peval P U := by
    exact tauHom_eval_eq_on_simplex (simplexStar hn) P hU.2
  have hH : H ≠ 0 := by
    intro hzero
    apply hPU
    rw [hzero] at hHU
    simpa [peval] using hHU.symm
  have hHdegree : H.totalDegree = P.totalDegree := by
    exact (tauHomogenize_isHomogeneous (R := ℝ)
      (simplexStar hn) P).totalDegree hH
  have hdvd : detPoly n ^ 2 ∣ H := by
    refine ⟨Q, ?_⟩
    exact hfactor
  have hdegree :=
    MvPolynomial.totalDegree_le_of_dvd_of_isDomain hdvd hH
  rw [totalDegree_detPoly_sq, hHdegree] at hdegree
  exact hdegree

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
