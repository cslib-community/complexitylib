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
clock for polynomially bounded `f`; it does not prove the textbook logarithmic-overhead
universal simulation.

## Main results

* `Cslib.Complexity.DTIME_ssubset_DTIME_of_log_clock`: the native hierarchy with a logarithmically
  inflated clock.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter

/-- The native deterministic hierarchy using a logarithmically inflated clock. The upper bound
charges the existing universal interpreter explicitly. -/
theorem DTIME_ssubset_DTIME_of_log_clock {f g : ℕ → ℕ}
    (hf : TimeConstructible f) (hn : ∀ n, n ≤ f n)
    (hg : ∀ᶠ n in atTop, (n + 1) ^ 5 * (f n * (Nat.size (f n) + 1) + 1) ^ 3 ≤ g n) :
    DTIME encBits f ⊂ DTIME encBits g := by
  refine DTIME_ssubset_DTIME_of_clock hf.mul_size_succ (fun c => ?_) hg
  filter_upwards [eventually_ge_atTop (max c (2 ^ c))] with n hnc
  have hcf : c ≤ f n := (le_max_left _ _).trans (hnc.trans (hn n))
  have hsize : c < Nat.size (f n) :=
    Nat.lt_size.mpr ((le_max_right _ _).trans (hnc.trans (hn n)))
  have := Nat.mul_le_mul_left (f n) hsize.le
  nlinarith

end Cslib.Complexity
