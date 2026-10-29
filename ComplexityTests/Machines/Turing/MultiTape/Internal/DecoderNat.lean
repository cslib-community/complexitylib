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

-- Consolidates the original binary decoder examples and total plain-certificate controls.
example (n : ℕ) (w : List Bool) :
    Decoder.nat.decode [true, false, true] = 5 ∧
    Decoder.nat.decode (encNat 6) = 6 ∧
    Decoder.nat.decode [true, false, false] = 1 ∧
    Decoder.nat.decode [] = 0 ∧
    Decoder.nat.decode (encNat n) = n ∧
    encNat (Decoder.nat.decode w) = w.rdropWhile (!·) ∧
    ComputableInPolyTime Decoder.nat.decode encBits encNat ∧
    (∃ d e, ComputableInDegree Decoder.nat.decode encBits encNat d e) :=
  ⟨rfl, Decoder.nat.decode_enc 6, rfl, rfl, Decoder.nat.decode_enc n, bits_ofBits w,
    Decoder.nat.computableInPolyTime, Decoder.nat.computable⟩

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
