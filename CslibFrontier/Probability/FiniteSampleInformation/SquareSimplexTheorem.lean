/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Probability.FiniteSampleInformation.SquareDeterminantGaussIntegration

/-!
# The determinant-square theorem on the square simplex

The homogeneous representative has a global determinant-square factor.  The
compiled simplex-kernel reconstruction then returns to the original
polynomial, adding exactly a multiple of the total-mass equation.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareSimplexTheorem.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

namespace SquarePolynomial

theorem square_simplex_det_sq
    {n : ℕ} (hn : 2 ≤ n)
    (P : Poly n) (hDPI : PolynomialDPI P)
    (hRKO : PolynomialRKO P) :
    ∃ Q K : Poly n,
      P = detPoly n ^ 2 * Q +
        (tauPoly (R := ℝ) (simplexStar hn) - 1) * K := by
  obtain ⟨Q, hfactor⟩ := det_sq_dvd_tauHom hn P hDPI hRKO
  obtain ⟨K, hidentity⟩ := square_identity_of_tauHomogenize_factor
    (simplexStar hn) P (detPoly n) Q hfactor
  exact ⟨Q, K, hidentity⟩

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
