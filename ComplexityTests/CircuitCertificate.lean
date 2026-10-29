/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Boolean.Encoding.Certificate

/-! Certificate-length monotonicity needs only the certificate module. -/

open Cslib.Circuits.Boolean

-- Evaluate both lengths independently before comparing the input-width budgets.
example : certLength 2 5 = 97 ∧ certLength 4 5 = 119 ∧ certLength 2 5 ≤ certLength 4 5 := by
  decide

example (n : ℕ) : certLength 0 0 ≤ certLength n 0 :=
  certLength_mono_left (Nat.zero_le n) 0
