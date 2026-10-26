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

-- Exact original Consolidation statements and proof bodies.
example : Decoder.nat.decode [true, false, true] = 5 := rfl
example : Decoder.nat.decode (encNat 6) = 6 := Decoder.nat.decode_enc 6
example : Decoder.nat.decode [true, false, false] = 1 := rfl
example : Decoder.nat.decode [] = 0 := rfl
example : Decoder.bool.decode (encBool true) = true := Decoder.bool.decode_enc true
example : Decoder.bool.decode [] = false := rfl

example {α : Type} {a : α ↪ List Bool} (D : Decoder a) (l : List α) :
    (Decoder.list D).decode (encList a l) = l := (Decoder.list D).decode_enc l
example : (Decoder.list Decoder.bool).decode [] = [] := by simp [Decoder.list]
example : (Decoder.list Decoder.bool).decode [true] = [false] := by
  simp [Decoder.list, frames_of_ne_nil, unframe, dropFrame, Decoder.bool]
example : (Decoder.list Decoder.nat).decode
    (encList encBits [[false, false], [true, false]]) = [0, 1] := by
  change (frames (encList encBits [[false, false], [true, false]])).map Decoder.nat.decode = [0, 1]
  rw [frames_encList]
  rfl
example {α : Type} {a : α ↪ List Bool} (D : Decoder a) :
    ComputableInPolyTime (Decoder.list D).decode encBits (encList a) :=
  (Decoder.list D).computableInPolyTime
example (l : List (ℕ × Option Bool)) :
    (Decoder.list (Decoder.pair Decoder.nat (Decoder.option Decoder.bool))).decode
      (encList (encPair encNat (encOption encBool)) l) = l :=
  (Decoder.list (Decoder.pair Decoder.nat (Decoder.option Decoder.bool))).decode_enc l
example : ∃ d e, ComputableInDegree frames encBits (encList encBits) d e :=
  ⟨1, 1, computableInDegree_frames⟩

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO, `Turing.MultiTapeTM.ComputableTidilyInSpace,
      `Turing.MultiTapeTM.ComputableTidilyInPolySpace] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"
