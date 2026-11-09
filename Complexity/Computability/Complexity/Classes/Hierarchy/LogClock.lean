/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible.Log
public import Complexity.Computability.Complexity.Classes.Hierarchy.Time

/-!
# A logarithmic clock for the native time hierarchy

The clock `f n * (Nat.size (f n) + 1)` eventually exceeds every constant multiple of an
at-least-linear `f`. Its constructibility follows from binary-polynomial postprocessing.
Using this clock replaces the earlier inflation `(n + 1) * f n` by `O(f n * log (f n))`,
which is smaller when `f` is polynomially bounded.

The resulting hierarchy still pays for the native universal interpreter: the upper bound is
`(n + 1) ^ 5 * (f n * (Nat.size (f n) + 1) + 1) ^ 3`. This is a quantitative improvement in the
clock for polynomially bounded `f`. `Hierarchy.TimePolylog` combines this clock with the
`O(t log t)` universal simulation, narrowing the gap to a polylogarithmic factor.

## Main results

* `Cslib.Complexity.eventually_mul_add_le_mul_size_succ`: the clock eventually exceeds every
  `c * f n + c`.
* `Cslib.Complexity.DTIME_ssubset_DTIME_of_log_clock`: the native hierarchy with a logarithmically
  inflated clock.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter

/-- The logarithmic clock of an at-least-linear `f` eventually exceeds every `c * f n + c`. -/
theorem eventually_mul_add_le_mul_size_succ {f : ℕ → ℕ} (hn : ∀ n, n ≤ f n) (c : ℕ) :
    ∀ᶠ n in atTop, c * f n + c ≤ f n * (Nat.size (f n) + 1) := by
  filter_upwards [eventually_ge_atTop (max c (2 ^ c))] with n hnc
  have hcf : c ≤ f n := (le_max_left _ _).trans (hnc.trans (hn n))
  have hsize : c < Nat.size (f n) :=
    Nat.lt_size.mpr ((le_max_right _ _).trans (hnc.trans (hn n)))
  have := Nat.mul_le_mul_left (f n) hsize.le
  nlinarith

/-- The native deterministic hierarchy using a logarithmically inflated clock. The upper bound
charges the existing universal interpreter explicitly. -/
theorem DTIME_ssubset_DTIME_of_log_clock {f g : ℕ → ℕ}
    (hf : TimeConstructible f) (hn : ∀ n, n ≤ f n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 5 * (f n * (Nat.size (f n) + 1) + 1) ^ 3 ≤ g n) :
    DTIME encBits f ⊂ DTIME encBits g :=
  DTIME_ssubset_DTIME_of_clock hf.mul_size_succ (eventually_mul_add_le_mul_size_succ hn) hg

end Cslib.Complexity
