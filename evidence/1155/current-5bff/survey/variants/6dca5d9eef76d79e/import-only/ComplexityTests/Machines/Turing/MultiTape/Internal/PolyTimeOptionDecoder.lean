/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Lean.Elab.Command


import Diag1155.Measure
/-! The concrete Decoder Option automation regression, with no high-raw fallback in scope. -/
open Turing.MultiTapeTM

example {α : Type} {a : α ↪ List Bool} (D : Decoder a) :
    ComputableInPolyTime (Decoder.option D).decode encBits (encOption a) := by fun_prop


example (w : List Bool) : (Decoder.option Decoder.bool).decode (true :: w) =
    some (Decoder.bool.decode w) := rfl
example : (Decoder.option Decoder.bool).decode [] = none := rfl
example : (Decoder.option Decoder.bool).decode [false] = some false := rfl

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

example :
    ComputableInPolyTime (Decoder.option Decoder.nat).decode encBits (encOption encNat) := by
  fun_prop
