/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Nat
import Lean.Elab.Command

/-! Original binary decoder examples and total plain-certificate controls. -/
open Turing.MultiTapeTM

-- These four examples retain the exact original Consolidation statements and proof bodies.
example : Decoder.nat.decode [true, false, true] = 5 := rfl
example : Decoder.nat.decode (encNat 6) = 6 := Decoder.nat.decode_enc 6
example : Decoder.nat.decode [true, false, false] = 1 := rfl
example : Decoder.nat.decode [] = 0 := rfl

example (n : ℕ) : Decoder.nat.decode (encNat n) = n := Decoder.nat.decode_enc n
example (w : List Bool) : encNat (Decoder.nat.decode w) = w.rdropWhile (!·) := bits_ofBits w
example : ComputableInPolyTime Decoder.nat.decode encBits encNat :=
  Decoder.nat.computableInPolyTime
example : ∃ d e, ComputableInDegree Decoder.nat.decode encBits encNat d e := Decoder.nat.computable

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
