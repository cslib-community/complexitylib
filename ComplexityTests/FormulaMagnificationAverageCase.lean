/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.FormulaMagnification.AverageCase

/-!
# Clients of zero-error average-case formula magnification

The query schedules below are inhabited polynomial examples. The finite client uses an actual
agreeing NP language, with no unproved formula upper bound, and checks that the formula's false
output certifies NO and its true output is an unknown mask of the required density.
-/

namespace ComplexityTests.FormulaMagnificationAverageCase

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Filter

example : SubexponentiallyBounded (fun n => avgCaseMCSPQueryEncLength n (n ^ 2 + 1) n) :=
  subexponentiallyBounded_avgCaseMCSPQueryEncLength
    ((SubexponentiallyBounded.id.pow 2).add (.const 1)) SubexponentiallyBounded.id

-- Zero thresholds and zero loss also use the same query encoding and growth API.
example : SubexponentiallyBounded (fun n => avgCaseMCSPQueryEncLength n 0 0) :=
  subexponentiallyBounded_avgCaseMCSPQueryEncLength (.const 0) (.const 0)

open Classical in
example : ∃ F : Formula signature (2 ^ 8),
    (∀ T : BitString (2 ^ 8), F.eval interpretation T = false →
      List.ofFn T ∉ GapMCSP.yesSet (fun _ => 1)) ∧
    8 * (Finset.univ.filter fun T : BitString (2 ^ 8) =>
      F.eval interpretation T = true).card ≤ 2 ^ (2 ^ 8) := by
  obtain ⟨L, -, hag⟩ := SuccinctMCSP.exists_language_mem_NP
  obtain ⟨F, -, hyes, hcard⟩ := exists_formula_zero_error_average_case_of_agrees
    (s := fun _ => 1) (n := 8) (r := 8) hag (by decide)
  refine ⟨F, fun T hfalse hsmall => ?_, ?_⟩
  · have htrue := hyes T hsmall
    rw [hfalse] at htrue
    exact Bool.noConfusion htrue
  · calc
      8 * (Finset.univ.filter fun T : BitString (2 ^ 8) =>
          F.eval interpretation T = true).card
          ≤ 2 ^ 8 * 2 ^ (2 ^ 8 - 8) := Nat.mul_le_mul (by decide) hcard
      _ = 2 ^ (2 ^ 8) := by norm_num

-- The forward theorem instantiates directly with a fixed reciprocal exponent and loss r=n.
example {L : Language Bool} (hag : ∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L)
    (hL : L ∈ FormulaPoly) :
    ∀ᶠ n in atTop, ∃ F : Formula signature (2 ^ n),
      F.leafSize ≤ 2 ^ (n / 2) ∧
      (∀ T : BitString (2 ^ n), List.ofFn T ∈ GapMCSP.yesSet (fun n => n ^ 2 + 1) →
        F.eval interpretation T = true) ∧
      (Finset.univ.filter fun T : BitString (2 ^ n) =>
        F.eval interpretation T = true).card ≤ 2 ^ (2 ^ n - n) :=
  eventually_exists_formula_zero_error_average_case_of_mem_FormulaPoly
    ((SubexponentiallyBounded.id.pow 2).add (.const 1)) SubexponentiallyBounded.id
    hag hL 2 (by decide)

end ComplexityTests.FormulaMagnificationAverageCase
