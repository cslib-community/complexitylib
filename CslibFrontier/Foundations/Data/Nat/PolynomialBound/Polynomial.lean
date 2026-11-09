/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import Cslib.Foundations.Data.Nat.PolynomialBound
public import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomials dominating polynomially bounded functions

A polynomially bounded function `f : ℕ → ℕ` is dominated pointwise by the evaluation of a
polynomial with natural-number coefficients, which may be taken to satisfy `n + 1 ≤ p.eval n`.
Such a polynomial is monotone by `Polynomial.monotone_eval`. Time bounds stated with an explicit
polynomial, as in time-bounded Kolmogorov complexity, are obtained this way from a polynomial-time
certificate.

## Main results

* `Cslib.PolynomiallyBounded.exists_polynomial_le`: a polynomial `p` with `n + 1 ≤ p.eval n` and
  `f n ≤ p.eval n` for all `n`.
-/

@[expose] public section

namespace Cslib

/-- A polynomially bounded function is dominated by a polynomial `p` over `ℕ` that is at least
`n + 1` at every `n`. -/
theorem PolynomiallyBounded.exists_polynomial_le {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    ∃ p : Polynomial ℕ, ∀ n, n + 1 ≤ p.eval n ∧ f n ≤ p.eval n := by
  obtain ⟨c, d, hle⟩ := polynomiallyBounded_iff_le.mp hf
  refine ⟨Polynomial.C c * (Polynomial.X + 1) ^ d + Polynomial.X + 1, fun n => ?_⟩
  have := hle n
  simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_C,
    Polynomial.eval_X, Polynomial.eval_one]
  omega

end Cslib
