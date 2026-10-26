/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import Lean.Elab.Command
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant


import Diag1155.Measure
/-! Plain-field total decoder clients, preserving malformed-word and independent-degree scope. -/
open Turing.MultiTapeTM
example : Decoder.bits.decode [] = [] := rfl
example (w : List Bool) : Decoder.bits.decode w = w := rfl
example : Decoder.bool.decode [] = false := rfl
example (w : List Bool) : Decoder.bool.decode (true :: w) = true := rfl
example : Decoder.unary.decode [false, true, false] = 3 := rfl
example (n : ℕ) : Decoder.unary.decode (encUnary n) = n := Decoder.unary.decode_enc n
example : ComputableInPolyTime Decoder.bool.decode encBits encBool :=
  Decoder.bool.computableInPolyTime
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) :
    ∃ d e, ComputableInDegree D.decode encBits a d e := D.computable
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) :
    ComputableInPolyTime D.decode encBits a := by fun_prop
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) :
    (Decoder.map D id id (fun _ => rfl) (fun _ => rfl)).decode = D.decode := rfl

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO,
      `Turing.MultiTapeTM.ComputableTidilyInBigO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

-- Both degrees may be zero; the field does not impose an output charge on workspace.
example {α : Type} (a : α ↪ List Bool) (decode : List Bool → α)
    (hround : ∀ x, decode (a x) = x) (h : ComputableInDegree decode encBits a 0 0) :
    Decoder a := ⟨decode, hround, 0, 0, h⟩

example : (Decoder.option Decoder.bool).decode [] = none := rfl
example : (Decoder.option Decoder.bool).decode [false] = some false := rfl
example : (Decoder.option Decoder.bool).decode [true] = some false := rfl
example (b : Bool) : (Decoder.option Decoder.bool).decode (encOption encBool (some b)) = some b :=
  (Decoder.option Decoder.bool).decode_enc (some b)
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) :
    ComputableInPolyTime (Decoder.option D).decode encBits (encOption a) :=
  (Decoder.option D).computableInPolyTime

example : (Decoder.pair Decoder.bool Decoder.bool).decode [] = (false, false) := rfl
example : (Decoder.pair Decoder.bool Decoder.bool).decode [true] = (false, false) := rfl
example {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (D₁ : Decoder a) (D₂ : Decoder b) (x : α × β) :
    (Decoder.pair D₁ D₂).decode (encPair a b x) = x := (Decoder.pair D₁ D₂).decode_enc x
example {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (D₁ : Decoder a) (D₂ : Decoder b) :
    ComputableInPolyTime (Decoder.pair D₁ D₂).decode encBits (encPair a b) :=
  (Decoder.pair D₁ D₂).computableInPolyTime

-- An inhabited total decoder with actual zero cost/output degrees, on unbounded runtime words.
example : ∃ (a : Unit ↪ List Bool) (D : Decoder a),
    ComputableInDegree D.decode encBits a 0 0 := by
  let a : Unit ↪ List Bool := ⟨fun _ => [], fun x y _ => Subsingleton.elim x y⟩
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := a) ()
  have hd : ComputableInDegree (fun _ : List Bool => ()) encBits a 0 0 :=
    ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, h⟩,
      DegreeBounded.const 0⟩
  exact ⟨a, ⟨fun _ => (), fun x => Subsingleton.elim _ x, 0, 0, hd⟩, hd⟩
