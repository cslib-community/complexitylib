/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DecoderPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimePrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeOptionPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeComposition

/-!
# Total decoders with plain degree certificates

A decoder is total on every word, inverts its encoding, and carries independent cost and encoded
output degrees. The basic constructors preserve totality and the round-trip law.

## Main definitions

* `Turing.MultiTapeTM.Decoder`: total decoding with independent cost and output degrees.
* `Turing.MultiTapeTM.Decoder.computableInPolyTime`: the ordinary polynomial-time certificate.
* `Turing.MultiTapeTM.Decoder.bits`, `.unary`, `.bool`, `.option`, `.pair`, `.map`: basic decoders.

## Main results

* `Turing.MultiTapeTM.Decoder.option_computableInDegree`: option decoding preserves the
  supplied output degree, including zero, with cost degree `max 1 (max d e)`.
-/

@[expose] public section
namespace Turing.MultiTapeTM

/-- A total decoder with polynomial cost and encoded-output growth on every input word. -/
structure Decoder {α : Type} (enc : α ↪ List Bool) where
  /-- The decoded value of any word. -/
  decode : List Bool → α
  /-- Decoding inverts the encoding. -/
  decode_enc (a : α) : decode (enc a) = a
  /-- Decoding has independent cost and encoded-output degrees, including zero. -/
  computable : ∃ d e, ComputableInDegree decode encBits enc d e

namespace Decoder
variable {α β : Type} {enc : α ↪ List Bool} {enc' : β ↪ List Bool}

/-- Every total decoder has a plain polynomial-time certificate. -/
@[fun_prop]
theorem computableInPolyTime (D : Decoder enc) : ComputableInPolyTime D.decode encBits enc := by
  obtain ⟨_, _, h⟩ := D.computable
  exact h.computableInPolyTime

/-- Bit strings are their own encoding. -/
def bits : Decoder encBits where
  decode := id
  decode_enc _ := rfl
  computable := ⟨1, 1, Internal.DecoderWords.bits_degree⟩

/-- Unary numbers are decoded by the length of the word. -/
def unary : Decoder encUnary where
  decode w := w.length
  decode_enc n := by simp
  computable := ⟨1, 1, Internal.DecoderWords.unary_degree⟩

/-- Booleans are decoded from the first symbol. -/
def bool : Decoder encBool where
  decode w := w.headD false
  decode_enc _ := rfl
  computable := ⟨1, 1, Internal.DecoderWords.bool_degree⟩

private theorem option_decode_degree {decode : List Bool → α} {d e : ℕ}
    (h : ComputableInDegree decode encBits enc d e) :
    ComputableInDegree (fun w => if w.isEmpty then none else some (decode w.tail))
      encBits (encOption enc) (max 1 (max d e)) e := by
  have hsome : ComputableInDegree (fun w => some (decode w.tail))
      encBits (encOption enc) (max 1 (max d e)) e :=
    ((ComputableInDegree.optionSome (enc₁ := enc) (enc := encOption enc)).comp
      (h.comp Internal.DecoderWords.tail_degree)).mono (by omega) (by omega)
  exact (ComputableInDegree.ite (f := fun _ => none)
    (g := fun w => some (decode w.tail)) Internal.DecoderWords.empty_degree
    (ComputableInDegree.const none)
    (ComputableInDegree.of_encIn_eq Subtype.val (fun _ => rfl) hsome)).mono
      (d' := max 1 (max d e)) (e' := e) (by omega) (by omega)

/-- Options are decoded as `none` from the empty word, and otherwise from the tail. -/
def option (D : Decoder enc) : Decoder (encOption enc) where
  decode w := if w.isEmpty then none else some (D.decode w.tail)
  decode_enc o := by cases o <;> simp [encOption, D.decode_enc]
  computable := by
    obtain ⟨d, e, hD⟩ := D.computable
    exact ⟨max 1 (max d e), e, option_decode_degree hD⟩

/-- Option decoding preserves any supplied encoded-output degree, including zero. Its cost
accounts for reading the input, running the decoder, and emitting the tagged decoded output. -/
theorem option_computableInDegree (D : Decoder enc) {d e : ℕ}
    (hD : ComputableInDegree D.decode encBits enc d e) :
    ComputableInDegree (option D).decode encBits (encOption enc) (max 1 (max d e)) e :=
  option_decode_degree hD

/-- Pairs are decoded from the framed first component and what follows it. -/
def pair {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool} (D₁ : Decoder enc₁)
    (D₂ : Decoder enc₂) : Decoder (encPair enc₁ enc₂) where
  decode w := (D₁.decode (unframe w), D₂.decode (dropFrame w))
  decode_enc p := by
    simp [unframe_frame_append, dropFrame_frame_append, D₁.decode_enc, D₂.decode_enc]
  computable := by
    obtain ⟨d₁, e₁, h₁⟩ := D₁.computable
    obtain ⟨d₂, e₂, h₂⟩ := D₂.computable
    exact ⟨_, _, (h₁.comp Internal.DecoderWords.unframe_degree).prod
      (h₂.comp Internal.DecoderWords.dropFrame_degree)⟩

/-- Transport a decoder along an encoding equality and a right inverse. -/
def map (D : Decoder enc) (f : α → β) (g : β → α) (hfg : ∀ b, f (g b) = b)
    (henc : ∀ a, enc' (f a) = enc a) : Decoder enc' where
  decode w := f (D.decode w)
  decode_enc b := by
    conv_lhs => rw [← hfg b, henc, D.decode_enc]
    exact hfg b
  computable :=
    let ⟨d, e, h⟩ := D.computable
    ⟨d, e, h.of_enc_eq fun w => henc _⟩

end Decoder
end Turing.MultiTapeTM
