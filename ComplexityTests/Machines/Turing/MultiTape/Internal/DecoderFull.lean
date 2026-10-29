/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder
import Lean.Elab.Command

/-! Complete total decoder clients through the original public import. -/
open Turing.MultiTapeTM

-- Exact original consolidation statements and proof bodies.
example {α : Type} {a : α ↪ List Bool} (D : Decoder a) (l : List α)
    (lPair : List (ℕ × Option Bool)) :
    Decoder.nat.decode [true, false, true] = 5 ∧
    Decoder.nat.decode (encNat 6) = 6 ∧
    Decoder.nat.decode [true, false, false] = 1 ∧
    Decoder.nat.decode [] = 0 ∧
    Decoder.bool.decode (encBool true) = true ∧
    Decoder.bool.decode [] = false ∧
    (Decoder.list D).decode (encList a l) = l ∧
    (Decoder.list Decoder.bool).decode [] = [] ∧
    (Decoder.list Decoder.bool).decode [true] = [false] ∧
    (Decoder.list Decoder.nat).decode
      (encList encBits [[false, false], [true, false]]) = [0, 1] ∧
    ComputableInPolyTime (Decoder.list D).decode encBits (encList a) ∧
    (Decoder.list (Decoder.pair Decoder.nat (Decoder.option Decoder.bool))).decode
      (encList (encPair encNat (encOption encBool)) lPair) = lPair ∧
    (∃ d e, ComputableInDegree frames encBits (encList encBits) d e) := by
  refine ⟨rfl, Decoder.nat.decode_enc 6, rfl, rfl, Decoder.bool.decode_enc true, rfl,
    (Decoder.list D).decode_enc l, by simp [Decoder.list],
    by simp [Decoder.list, frames_of_ne_nil, unframe, dropFrame, Decoder.bool],
    ?_, (Decoder.list D).computableInPolyTime,
    (Decoder.list (Decoder.pair Decoder.nat (Decoder.option Decoder.bool))).decode_enc lPair,
    ⟨1, 1, computableInDegree_frames⟩⟩
  change (frames (encList encBits [[false, false], [true, false]])).map Decoder.nat.decode = [0, 1]
  rw [frames_encList]
  rfl

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
