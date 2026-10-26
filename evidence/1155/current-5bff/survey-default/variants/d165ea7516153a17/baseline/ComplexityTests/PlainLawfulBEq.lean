/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic
import Complexity.Tactic.PolyTime

/-! # Plain Boolean equality through a common encoding -/

open Turing.MultiTapeTM

example {α β : Type} {input : α ↪ List Bool} {output : β ↪ List Bool}
    [BEq β] [hlawful : LawfulBEq β] {left right : α → β}
    (hleft : ComputableInPolyTime left input output)
    (hright : ComputableInPolyTime right input output) :
    ComputableInPolyTime (fun a => left a == right a) input encBool := by
  fail_if_success (clear hright; fun_prop)
  fail_if_success (clear hlawful; fun_prop)
  exact hleft.beq hright

example {f : List Bool → List Bool} (hf : ComputableInPolyTime f encBits encBits) :
    ComputableInPolyTime (fun p : List Bool × List Bool => f p.1 == f p.2)
      (encPair encBits encBits) encBool := by
  fail_if_success (clear hf; fun_prop)
  fun_prop

-- Equality is uniform in both growing words, rather than a fixed finite-input shortcut.
example : ComputableInPolyTime (fun p : List Bool × List Bool => p.1 == p.2)
    (encPair encBits encBits) encBool := by
  fun_prop
