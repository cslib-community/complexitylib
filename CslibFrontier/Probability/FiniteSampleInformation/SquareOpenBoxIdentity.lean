/-
Copyright (c) 2026 Yuqing Kong, Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuqing Kong, Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib

/-!
# Polynomial identity on a real open box

An ordinary real multivariate polynomial which vanishes on a product of
nonempty open intervals is the zero polynomial.  Mathlib's
`MvPolynomial.funext_set` packages the induction on the finitely many
variables; the only topological input is that each real open interval is
infinite.

Ported by Christian Reitwiessner from Yuqing Kong's Apache-2.0 formalization,
`SquareOpenBoxIdentity.lean` at commit
`4e27ef9d167be69902385307d40123ec665dc532` of
https://github.com/yuqkong-1844/finite-sample-information-monotones .
The mathematical source is [Kong2027].
-/

public section

namespace Cslib.FiniteSampleInformation

noncomputable section

open Set

namespace SquarePolynomial

theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open_box
    {σ : Type*}
    (P : MvPolynomial σ ℝ) (l u : σ → ℝ)
    (hlu : ∀ i, l i < u i)
    (hzero : ∀ x : σ → ℝ,
      (∀ i, x i ∈ Ioo (l i) (u i)) → MvPolynomial.eval x P = 0) :
    P = 0 := by
  apply MvPolynomial.funext_set (fun i => Ioo (l i) (u i))
    (fun i => Set.Ioo_infinite (hlu i))
  intro x hx
  rw [hzero x (fun i => hx i (Set.mem_univ i))]
  simp

theorem mvPolynomial_eq_zero_of_eval_eq_zero_on_open_box_fin
    {N : ℕ} (P : MvPolynomial (Fin N) ℝ)
    (l u : Fin N → ℝ) (hlu : ∀ i, l i < u i)
    (hzero : ∀ x : Fin N → ℝ,
      (∀ i, x i ∈ Ioo (l i) (u i)) → MvPolynomial.eval x P = 0) :
    P = 0 :=
  mvPolynomial_eq_zero_of_eval_eq_zero_on_open_box P l u hlu hzero

end SquarePolynomial


end

end Cslib.FiniteSampleInformation
