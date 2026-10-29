/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Universal.Input
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO

/-! Streaming lookup retains the distinction between a zero symbol and an absent symbol,
and emits the selected unary word once even when later input symbols are present. -/

open Turing.MultiTapeTM Turing.MultiTapeTM.Universal

example :
    [0, 1, 2, 3, 4, 4096].map (inputSymbol [0, 17, 0]) =
      [none, some 0, some 17, some 0, none, none] := by decide

example :
    encOption encUnary (inputSymbol [0, 17, 0] 2) = true :: List.replicate 17 true ∧
      encOption encUnary (inputSymbol [0, 17, 0] 3) = [true] ∧
      encOption encUnary (inputSymbol [0, 17, 0] 4) = [] := by decide

example : inputSymbol [] 0 = none ∧ inputSymbol [] 4096 = none := by decide

-- A real client fixes the simulated input while leaving an arbitrary binary head position.
-- Its machine and constants are uniform in that position, including positions beyond the end.
example : ComputableInO (fun p : ℕ => inputSymbol [0, 17, 0] p) encNat (encOption encUnary)
    (fun p => ((encNat p).length + 1) ^ 2) (fun p => (encNat p).length) := by
  have hid : ComputableInO (fun p : ℕ => p) encNat encNat
      (fun p => (encNat p).length) (fun p => (encNat p).length) :=
    .of_linear (.of_eq fun _ => rfl)
  refine (inputSymbol_stream_inO.comp
    ((ComputableInO.const (encMid := encList encUnary) [0, 17, 0]).prod hid)).mono 256
      (fun p => ?_) (fun p => ?_)
  · have hp : (encNat p).length + 1 ≤ ((encNat p).length + 1) ^ 2 :=
      Nat.le_self_pow two_ne_zero _
    change (encNat p).length + (encNat p).length + 38 * ((encNat p).length + 1) ^ 2 ≤
      256 * (((encNat p).length + 1) ^ 2 + 1)
    omega
  · simp only [length_encPair,
      show (encList encUnary [0, 17, 0]).length = 37 from rfl]
    omega
