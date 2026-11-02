/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of the native block label codec)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.Encoding.NativeChecked

/-!
# Native block-label codec regressions

The explicit windows contain blank, written zero and written one. Successful and FAIL labels
share a charged buffer, malformed buffers are rejected, and parsing follows the exact existing
semantic codec rather than a second label format.
-/

@[expose] public section

namespace ComplexityTests.NativeBlockCodec

open Turing MultiTapeTM MultiTapePTM.BlockComputation
open MultiTapePTM.BlockComputation.QueryReplay

abbrev code : Fin 1 ≃ Fin 1 := Equiv.refl _

def raw : RawResult 1 (Fin 1) :=
  (some 0, fun _ => 0, .accept, fun _ => [0, 1, 2])

def good := Encoding.NativeEncode.serialize code (1, true, raw)
def fail := Encoding.NativeEncode.serialize code (1, false, raw)

example : good = [true, true, false, false, false, true, false,
    false, false, true, false, true, true] := by decide

example : good.length = Encoding.width 1 1 1 := by decide
example : fail = List.replicate (Encoding.width 1 1 1) false := by decide
example : Encoding.NativeEncode.serialize code
    (2, true, raw) = [] := by decide
example : Encoding.NativeDecode.cells [false, true, true, false, true, true, true] =
    [0, 1, 2] := rfl
example : Encoding.NativeDecode.readNat [true, false, true, true] 1 3 = 6 := by decide
example : Encoding.NativeDecode.parse (k := 1) code (1, fail) = none := by decide
example : Encoding.NativeDecode.parse (k := 1) code (0, good) = none := rfl
example : Encoding.NativeDecode.parse (k := 1) code (1, []) = none := by decide
example : Option.map (fun r : RawResult 1 (Fin 1) => let (_, _, _, cells) := r; cells 0)
    (Encoding.NativeDecode.parse code (1, good)) = some [0, 1, 2] := by decide

example : Encoding.NativeDecode.parse code (1, good) = some raw := by decide

def emptyRaw : RawResult 0 (Fin 1) := (none, fun _ => 123, .other, Fin.elim0)

-- With no work tapes the actual payload grows with the binary width, not the block width.
example : (Encoding.NativeEncode.serialize code (1000000000, true, emptyRaw)).length =
    Encoding.width 0 1 1000000000 := by decide

/-- The lenient decoder supplies defaults; the gate-facing canonical decoder must reject them. -/
def noncanonicalBlank := good.set 8 true

example : Encoding.NativeDecode.parse code (1, noncanonicalBlank) = some raw := by decide
example : Encoding.NativeChecked.parse (k := 1) code (1, noncanonicalBlank) = none := by decide
example : Encoding.NativeChecked.parse (k := 1) code (1, good) = some raw := by decide
example : Encoding.NativeChecked.parse (k := 1) code (1, good.set 2 true) = none := by decide
example : Encoding.NativeChecked.parse (k := 1) code (1, good.set 6 true) = none := by decide

end ComplexityTests.NativeBlockCodec
