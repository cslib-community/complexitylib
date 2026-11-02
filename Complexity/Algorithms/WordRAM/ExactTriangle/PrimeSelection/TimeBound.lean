/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.PrimeSelection.Flat
public import Complexity.Algorithms.WordRAM.ExactTriangle.CountPrime.TimeBound
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Complete charged prime-selection bound

The original matrix dimension has exponent 2.81, with an explicit cubic factor in
`sqrt(D)+1`. This includes every candidate's actual trial division, argument delivery, counter
execution and minimum comparison, plus the original header and halt. No source instruction
constant or counting-call time hypothesis is used.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection

/-- Separate the real counter calls from the charged enumeration, original header and halt. -/
theorem timeBound_le_calls (n D : ℕ) :
    timeBound n D + 16 ≤ (Nat.sqrt D + 1) * (CountPrime.cost n (Nat.sqrt D) + 10) +
      42 * (D + 1) := by
  have hs := Nat.sqrt_le D
  have hl := Nat.sqrt_le_self D
  unfold timeBound countTimeBound
  nlinarith only [hs, hl]

/-- Full initialized instruction charge, including halt. The dependence on the actual window
parameter remains explicit; the n exponent alone is strictly subcubic. -/
theorem timeBound_le_subcubic (n D : ℕ) :
    ((timeBound n D + 16 : ℕ) : ℝ) ≤
      3704 * (Nat.sqrt D + 1 : ℝ) ^ 3 * (n + 1 : ℝ) ^ (281 / 100 : ℝ) +
        42 * (D + 1 : ℝ) := by
  have hbase : ((timeBound n D + 16 : ℕ) : ℝ) ≤
      (Nat.sqrt D + 1 : ℝ) * ((CountPrime.cost n (Nat.sqrt D) + 10 : ℕ) : ℝ) +
        42 * (D + 1 : ℝ) := by exact_mod_cast timeBound_le_calls n D
  have hscale := mul_le_mul_of_nonneg_left (CountPrime.cost_le_subcubic n (Nat.sqrt D))
    (show 0 ≤ (Nat.sqrt D + 1 : ℝ) from by positivity)
  calc
    _ ≤ (Nat.sqrt D + 1 : ℝ) * ((CountPrime.cost n (Nat.sqrt D) + 10 : ℕ) : ℝ) +
        42 * (D + 1 : ℝ) := hbase
    _ ≤ (Nat.sqrt D + 1 : ℝ) *
        (3704 * (Nat.sqrt D + 1 : ℝ) ^ 2 * (n + 1 : ℝ) ^ (281 / 100 : ℝ)) +
          42 * (D + 1 : ℝ) :=
      add_le_add hscale le_rfl
    _ = _ := by ring

end Cslib.Algorithms.WordRAM.ExactTriangle.PrimeSelection
