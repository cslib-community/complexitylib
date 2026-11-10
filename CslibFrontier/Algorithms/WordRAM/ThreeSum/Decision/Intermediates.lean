/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.WordRAM.ThreeSum.Decision.Input
public import CslibFrontier.Foundations.Data.Nat.Log
import CslibFrontier.Foundations.Data.Nat.ClogPow

/-!
# Polynomial words and space for every ordinary-host prefix

The minimum derived physical width is logarithmic in the original input length. Since the
actual program never reads physical width, its completed minimum-width execution identifies
all prefixes at every wider admitted width, including all concrete callee scratch operations.

## Main results

* `two_pow_width_le`: explicit fixed polynomial word universe.
* `prefix_polynomial`: all prefix words and memory support share one polynomial envelope.

These native representation bounds are original and reuse the generic width-prefix theorem.
-/

public section

namespace Cslib.Algorithms.WordRAM.ThreeSum.Decision

open Cslib.WordRAM

/-- The fixed minimum-width word universe has polynomial magnitude in the original length. -/
theorem two_pow_width_le (κ d n : ℕ) :
    2 ^ width κ d n ≤ (n + 2) ^ (2 * widthCoefficient κ d) :=
  Nat.two_pow_mul_clog_le_pow (by omega) le_rfl

/-- Every prefix has polynomial words and zero memory above the same envelope, uniformly
at every admitted physical width. -/
theorem prefix_polynomial {κ w r : ℕ} (input : List ℤ) (c : Host.Callee r)
    (hw : width κ c.widthCoefficient input.length ≤ w)
    (hvalues : ∀ z ∈ input, |z| ≤ ((input.length + 2) ^ κ : ℕ))
    {s : State (registerCount r)} {steps : ℕ}
    (hr : Runs w (flatProgram κ c.code) (State.init (input.map Signed.encode)) s steps) :
    (∀ i, s.data.regs i < (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient)) ∧
      (∀ a, s.data.mem a < (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient)) ∧
      ∀ a, (input.length + 2) ^ (2 * widthCoefficient κ c.widthCoefficient) ≤ a →
        s.data.mem a = 0 := by
  obtain ⟨_, _, he, _⟩ := runs_input input c le_rfl hvalues
  have hi := ChanHe.Preprocessing.input_fits input
    (preprocessing_width_le κ c.widthCoefficient input.length) hvalues
  exact hr.prefix_bounds_init
    (Code.not_readsWidth_program (not_readsWidth κ c) (controllerRegisters r answer)) hw
    hi he (two_pow_width_le κ c.widthCoefficient input.length)

end Cslib.Algorithms.WordRAM.ThreeSum.Decision
