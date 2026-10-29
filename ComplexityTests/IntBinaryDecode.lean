/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Encodings.IntBinary.Decode
import Complexity.Tactic.PolyTime

/-! Total signed decoding, noncanonical zero and a plain composed client. -/

open Turing.MultiTapeTM

example : decodeIntBin [] = 0 ∧ decodeIntBin [true] = 0 ∧
    decodeIntBin [true, false, false] = 0 := by decide +kernel

example : decodeIntBin [true, true, false, true] = -5 ∧
    decodeIntBin [false, true, false, true, false] = 5 ∧
    decodeIntBin (encIntBin (-(2 ^ 5 : ℤ))) = -(2 ^ 5 : ℤ) :=
  ⟨by decide +kernel, by decide +kernel, decodeIntBin_encIntBin _⟩

example : ComputableInPolyTime (fun p : List Bool × List Bool =>
    decodeIntBin p.1 - decodeIntBin p.2) (encPair encBits encBits) encIntBin := by
  fun_prop
