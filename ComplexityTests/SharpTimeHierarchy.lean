/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import Complexity.Computability.Complexity.Classes.Hierarchy.LogClock
public import Complexity.Computability.Complexity.Classes.Hierarchy.Polynomial

/-! Concrete hierarchy instances and an irregular lower bound for which frequent clock
domination holds but eventual clock domination fails. -/

public section

namespace ComplexityTests.SharpTimeHierarchy

open Cslib.Complexity Turing.MultiTapeTM Filter

/-- Rounded padding reaches the linear lower boundary of the positive-integer hierarchy. -/
example : DTIME encBits (fun n => n) ⊂ DTIME encBits (fun n => n ^ 2) := by
  simpa only [pow_one] using DTIME_pow_ssubset_DTIME_pow (a := 1) (b := 2)
    (by omega) (by omega)

private def irregular (n : ℕ) : ℕ := if n % 2 = 0 then n else (n + 1) ^ 2

private theorem frequently_irregular (c : ℕ) :
    ∃ᶠ n in atTop, c * irregular n + c ≤ (n + 1) ^ 2 := by
  rw [frequently_atTop]
  intro N
  refine ⟨2 * (N + c + 1), by omega, ?_⟩
  have heven : 2 * (N + c + 1) % 2 = 0 := by omega
  simp only [irregular, heven, ↓reduceIte]
  nlinarith

/-- An unbounded set of even favorable lengths suffices for an actual native separation. -/
example : {x | timeDiagonal (fun n => (n + 1) ^ 2) x = true} ∉ DTIME encBits irregular :=
  setOf_timeDiagonal_notMem_DTIME_of_frequently_le frequently_irregular

/-- The previous eventual-domination hypothesis really fails for this same clock and bound. -/
example : ¬∀ᶠ n in atTop, 2 * irregular n + 2 ≤ (n + 1) ^ 2 := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp h
  have hbad := hN (2 * N + 1) (by omega)
  have hodd : (2 * N + 1) % 2 ≠ 0 := by omega
  simp only [irregular, hodd, ↓reduceIte] at hbad
  omega

/-- Ordinary and shifted input-length conventions can be mixed in hierarchy statements. -/
theorem shifted_quadratic_ssubset_cubic :
    DTIME encBits (fun n => (n + 1) ^ 2) ⊂ DTIME encBits (fun n => n ^ 3) := by
  rw [DTIME_succ_pow_eq]
  exact DTIME_pow_ssubset_DTIME_pow (by omega) (by omega)

end ComplexityTests.SharpTimeHierarchy
