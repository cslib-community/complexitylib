/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! The canonical facade retains default captured binary multiplication automation. -/

open Turing.MultiTapeTM

example {α : Type} {input : α ↪ List Bool} {left right : α → ℕ}
    (hl : ComputableInPolyTime left input encNat)
    (hr : ComputableInPolyTime right input encNat) :
    ComputableInPolyTime (fun a => left a * right a) input encNat := by
  fail_if_success (clear hr; fun_prop)
  fail_if_success (clear hl; fun_prop)
  fun_prop

example : ComputableInPolyTime (fun p : ℕ × ℕ => p.1 * p.2)
    (encPair encNat encNat) encNat := by
  fun_prop
