/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.Hierarchy.TimePolylog
import Complexity.Foundations.Data.Nat.PolynomialBound.Exponential

/-! Linear-time shortness of descriptions, and the time hierarchy with a polylogarithmic gap on
concrete bounds. -/

namespace ComplexityTests.HierarchyPolylog

open Cslib Cslib.Complexity Turing Turing.MultiTapeTM Filter

/-- Shortness of the framed description is decided within linear time. -/
example : ComputableInO Diagonal.shortDesc encBits encBool (fun x => x.length) fun x => x.length :=
  Diagonal.computableInO_shortDesc

/-- The clock version with the exponential clock: linear time is strictly contained in the class
of the clocked diagonal for `2 ^ n`, which beats every linear function. -/
example : ∃ k, DTIME encBits (fun n => n) ⊂ DTIME encBits fun n =>
    n + (Nat.log 2 (n + 1) + 1) ^ k * ((2 ^ n + 1) * (Nat.log 2 (2 ^ n + 1) + 1)) := by
  obtain ⟨k, hk⟩ := exists_DTIME_ssubset_DTIME_of_clock_polylog
  exact ⟨k, hk timeConstructible_two_pow (fun c =>
    (PolynomiallyBounded.eventually_lt_two_pow (f := fun n => c * n + c) (by fun_prop)).mono
      fun _ h => h.le) (Eventually.of_forall fun _ => le_rfl)⟩

/-- **Quadratic time is strictly contained in quadratic time with a polylogarithmic factor**, for
an absolute exponent: far below the gap `(n + 1) ^ 8 * ((n + 1) ^ 2 + 1) ^ 3` of
`Cslib.Complexity.DTIME_ssubset_DTIME`. -/
example : ∃ k, DTIME encBits (fun n => (n + 1) ^ 2) ⊂
    DTIME encBits fun n => ((n + 1) ^ 2 + 1) * (Nat.log 2 ((n + 1) ^ 2 + 1) + 1) ^ k := by
  obtain ⟨k, hk⟩ := exists_DTIME_ssubset_DTIME_polylog
  exact ⟨k, hk timeConstructible_succ_sq (fun n => by nlinarith)
    (Eventually.of_forall fun _ => le_rfl)⟩

end ComplexityTests.HierarchyPolylog
