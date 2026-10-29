/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Decoder.Basic
import Lean.Elab.Command
import Cslib.Computability.Machines.Turing.MultiTape.Combinators.AlmostConstant

/-! Plain-field total decoder clients, preserving malformed-word and independent-degree scope. -/
open Turing.MultiTapeTM
example {α : Type} (a : α ↪ List Bool) (D : Decoder a) (w : List Bool) (n : ℕ) :
    Decoder.bits.decode [] = [] ∧
    Decoder.bits.decode w = w ∧
    Decoder.bool.decode [] = false ∧
    Decoder.bool.decode (true :: w) = true ∧
    Decoder.unary.decode [false, true, false] = 3 ∧
    Decoder.unary.decode (encUnary n) = n ∧
    ComputableInPolyTime Decoder.bool.decode encBits encBool ∧
    (∃ d e, ComputableInDegree D.decode encBits a d e) ∧
    ComputableInPolyTime D.decode encBits a ∧
    (Decoder.map D id id (fun _ => rfl) (fun _ => rfl)).decode = D.decode :=
  ⟨rfl, rfl, rfl, rfl, rfl, Decoder.unary.decode_enc n, Decoder.bool.computableInPolyTime,
    D.computable, by fun_prop, rfl⟩

open Lean Elab Command in
run_cmd do
  for name in #[`Turing.MultiTapeTM.ComputableTidilyInPolyTime,
      `Turing.MultiTapeTM.ComputableTidilyInDegree, `Turing.MultiTapeTM.ComputableTidilyInO] do
    if (← getEnv).contains name then
      throwError "A higher tidy calculus was imported: {name}"

-- Both degrees may be zero; the field does not impose an output charge on workspace.
example {α : Type} (a : α ↪ List Bool) (decode : List Bool → α)
    (hround : ∀ x, decode (a x) = x) (h : ComputableInDegree decode encBits a 0 0) :
    Decoder a := ⟨decode, hround, 0, 0, h⟩

example {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool)
    (D₁ : Decoder a) (D₂ : Decoder b) (bit : Bool) (x : α × β) :
    (Decoder.option Decoder.bool).decode [] = none ∧
    (Decoder.option Decoder.bool).decode [false] = some false ∧
    (Decoder.option Decoder.bool).decode [true] = some false ∧
    (Decoder.option Decoder.bool).decode (encOption encBool (some bit)) = some bit ∧
    ComputableInPolyTime (Decoder.option D₁).decode encBits (encOption a) ∧
    (Decoder.pair Decoder.bool Decoder.bool).decode [] = (false, false) ∧
    (Decoder.pair Decoder.bool Decoder.bool).decode [true] = (false, false) ∧
    (Decoder.pair D₁ D₂).decode (encPair a b x) = x ∧
    ComputableInPolyTime (Decoder.pair D₁ D₂).decode encBits (encPair a b) ∧
    (∃ (u : Unit ↪ List Bool) (Du : Decoder u), ComputableInDegree Du.decode encBits u 0 0) := by
  refine ⟨rfl, rfl, rfl, (Decoder.option Decoder.bool).decode_enc (some bit),
    (Decoder.option D₁).computableInPolyTime, rfl, rfl, (Decoder.pair D₁ D₂).decode_enc x,
    (Decoder.pair D₁ D₂).computableInPolyTime, ?_⟩
  let u : Unit ↪ List Bool := ⟨fun _ => [], fun x y _ => Subsingleton.elim x y⟩
  obtain ⟨c, h⟩ := computableInTimeAndSpace_of_const (encIn := encBits) (encOut := u) ()
  have hd : ComputableInDegree (fun _ : List Bool => ()) encBits u 0 0 :=
    ⟨⟨fun _ => c, fun _ => 0, DegreeBounded.const c, DegreeBounded.const 0, h⟩,
      DegreeBounded.const 0⟩
  exact ⟨u, ⟨fun _ => (), fun x => Subsingleton.elim _ x, 0, 0, hd⟩, hd⟩
