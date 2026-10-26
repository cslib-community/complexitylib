/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: local-only (test driver)

import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-! Raw-word and binary bit-length reuse the existing zero-workspace decoder leaf. -/

open Turing.MultiTapeTM

example {α : Type} {input : α ↪ List Bool} {word : α → List Bool}
    (hw : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => (word a).length) input encUnary := by
  fail_if_success (clear hw; fun_prop)
  fun_prop

example {α : Type} {input : α ↪ List Bool} {n : α → ℕ}
    (hn : ComputableInPolyTime n input encNat) :
    ComputableInPolyTime (fun a => (n a).size) input encUnary := by
  fail_if_success (clear hn; fun_prop)
  fun_prop

-- The existing transducer counts every symbol, even false symbols in malformed unary words.
example : Internal.DecoderWords.unaryLengthT.run () [] = [] := rfl
example : Internal.DecoderWords.unaryLengthT.run () [false, true, false] = [true, true, true] :=
  rfl

-- Nonempty output is supported at zero workspace, rather than charged to that workspace.
example (w : List Bool) : Internal.DecoderWords.unaryLengthT.toTM.ComputesInTimeAndSpace
    w (List.replicate w.length true) (2 * w.length + 3) 0 := by
  simpa only [show Internal.DecoderWords.unaryLengthT.q₀ = () from rfl,
    Internal.DecoderWords.unaryLengthT_run] using
      Internal.DecoderWords.unaryLengthT.computesInTimeAndSpace_toTM w

example : Nat.size 0 = 0 := rfl
example : Nat.size (2 ^ 128) = 129 := by
  rw [Nat.size_pow]

example : (encUnary ((2 ^ 128).size)).length = 129 := by
  simp only [encUnary_apply, List.length_replicate, Nat.size_pow]
