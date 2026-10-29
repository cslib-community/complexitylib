/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeOptionPrimitives
import Lean.Elab.Command

/-! The concrete Decoder Option automation regression, with no high-raw fallback in scope. -/
open Turing.MultiTapeTM

example {α : Type} {a : α ↪ List Bool} (D : Decoder a) (w : List Bool) :
    ComputableInPolyTime (Decoder.option D).decode encBits (encOption a) ∧
    (Decoder.option Decoder.bool).decode (true :: w) = some (Decoder.bool.decode w) ∧
    (Decoder.option Decoder.bool).decode [] = none ∧
    (Decoder.option Decoder.bool).decode [false] = some false ∧
    ComputableInPolyTime (Decoder.option Decoder.nat).decode encBits (encOption encNat) :=
  ⟨by fun_prop, rfl, rfl, rfl, by fun_prop⟩

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
       `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
