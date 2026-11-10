/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (addition to `Cslib/Foundations/Data/Nat/PolynomialBound.lean`)

public import CslibFrontier.Foundations.Data.Nat.PolynomialBound.Closure
public import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Choose.Bounds

/-!
# Polynomial bounds for binomial coefficients

For fixed `k : ℕ`, `(f n).choose k ≤ f n ^ k`, so binomial coefficients preserve
`PolynomiallyBounded`. In particular, birthday-bound pair counts `(Q n).choose 2` of polynomially
bounded query budgets remain polynomially bounded.

## Main results

* `Cslib.PolynomiallyBounded.choose`: fixed-index binomial coefficients preserve polynomial bounds.
* `Cslib.PolynomiallyBounded.choose_two`: pair counts `(f n).choose 2` preserve polynomial bounds.
-/

@[expose] public section

namespace Cslib.PolynomiallyBounded

/-- Fixed-index binomial coefficients preserve polynomial bounds since `m.choose k ≤ m ^ k`. -/
@[fun_prop]
protected theorem choose {f : ℕ → ℕ} (hf : PolynomiallyBounded f) (k : ℕ) :
    PolynomiallyBounded (fun n => (f n).choose k) :=
  (hf.pow k).mono_of_le fun n => Nat.choose_le_pow (f n) k

/-- Birthday-bound pair counts `(f n).choose 2` preserve polynomial bounds. -/
protected theorem choose_two {f : ℕ → ℕ} (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => (f n).choose 2) :=
  hf.choose 2

end Cslib.PolynomiallyBounded
