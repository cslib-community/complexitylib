/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (test driver)

import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.BigO.ListHead

/-! Ordinary-import clients compose the optional-head certificate and both public size bounds. -/

open Turing.MultiTapeTM

namespace ComplexityTests.ListHead

variable {α : Type} [Inhabited α] (enc : α ↪ List Bool)

-- Composition reads a head with a default without importing the zipFold implementation.
example : ComputableInO (fun l : List α => l.head?.getD default) (encList enc) enc
    (fun l => (2 * (enc default).length + 8) * ((encList enc l).length + 1))
    (fun l => (2 * (enc default).length + 8) * ((encList enc l).length + 1)) :=
  ComputableInO.optionGetD default (ComputableInO.head? (encB := enc))

-- Both pure bounds combine through an ordinary import on the same composed operation.
example (l : List α) :
    (enc (l.head?.getD default)).length ≤ (encList enc l).length + 1 + (enc default).length :=
  (length_enc_getD_le (encC := enc) l.head?).trans
    (Nat.add_le_add_right (length_encOption_head?_le (encB := enc) l) _)

end ComplexityTests.ListHead
