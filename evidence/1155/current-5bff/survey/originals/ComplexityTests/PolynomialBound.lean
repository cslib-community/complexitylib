/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Foundations.Data.Nat.PolynomialBound.Closure

/-!
# `fun_prop` for polynomial bounds

Representative goals from time and size accounting, discharged by `fun_prop` from local bound
hypotheses.
-/

namespace ComplexityTests.PolynomialBound

open Cslib

variable {f g size growth : ℕ → ℕ}

example : PolynomiallyBounded (fun n => 3 * n ^ 2 + 7) := by fun_prop

example (hf : PolynomiallyBounded f) : PolynomiallyBounded (fun n => 2 * f n ^ 3 + n - 5) := by
  fun_prop

example (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => f (g n) + g (f n + 1)) := by
  fun_prop

/-- The shape of a composite clock: the second stage runs on the first stage's output length. -/
example (c₀ d₀ c₁ d₁ : ℕ) :
    PolynomiallyBounded (fun n =>
      c₀ * (n + 1) ^ d₀ + (c₀ * (n + 1) ^ d₀ + 4 + c₁ * (c₀ * (n + 1) ^ d₀ + 1) ^ d₁)) := by
  fun_prop

/-- The shape of a loop's size invariant. -/
example (hsize : PolynomiallyBounded size) (hgrowth : PolynomiallyBounded growth) :
    PolynomiallyBounded (fun n => 2 * n + size n * growth n + 1) := by
  fun_prop

example (hf : PolynomiallyBounded f) :
    PolynomiallyBounded (fun n => max (f n / 2) (Nat.log 2 (f n)) % (n + 1)) := by
  fun_prop

example (hf : PolynomiallyBounded f) (hg : PolynomiallyBounded g) :
    PolynomiallyBounded (fun n => if n % 2 = 0 then f n else g n) := by
  fun_prop

end ComplexityTests.PolynomialBound
