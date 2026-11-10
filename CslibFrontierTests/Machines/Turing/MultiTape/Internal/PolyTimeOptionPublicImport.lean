/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-! Ordinary public imports expose the shared plain rules without local certificates. -/
open Turing.MultiTapeTM

example {α β : Type} {a : α ↪ List Bool} {b : β ↪ List Bool} (D : Decoder a)
    {value : α → Option β} {fallback : α → β}
    (hvalue : ComputableInPolyTime value a (encOption b))
    (hfallback : ComputableInPolyTime fallback a b) :
    ComputableInPolyTime (Decoder.option D).decode encBits (encOption a) ∧
    ComputableInPolyTime (fun x => (value x).getD (fallback x)) a b ∧
    ComputableInPolyTime (Decoder.option Decoder.nat).decode encBits (encOption encNat) :=
  ⟨by fun_prop, by fun_prop, by fun_prop⟩

/-- Captured input is retained, including when mapping changes the underlying value encoding. -/
example {α : Type} {a : α ↪ List Bool} {value : α → Option (List Bool)}
    {captured : α → List Bool}
    (hv : ComputableInPolyTime value a (encOption encBits))
    (hp : ComputableInPolyTime captured a encBits) :
    ComputableInPolyTime (fun x => (value x).map (fun bits => (captured x, bits)))
      a (encOption (encPair encBits encBits)) := by
  apply hv.optionMapWithInput
  exact (hp.comp (ComputableInPolyTime.fst a encBits)).prod
    (ComputableInPolyTime.snd a encBits)
