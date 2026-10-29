/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Basic

/-! Ordinary module clients retain the Boolean certificates from the original facade. -/

open Turing.MultiTapeTM

example :
    ComputableInPolyTime (fun p : Bool × Bool => p.1 && p.2) (encPair encBool encBool) encBool ∧
    ComputableInPolyTime Bool.not encBool encBool :=
  ⟨by fun_prop, by fun_prop⟩
