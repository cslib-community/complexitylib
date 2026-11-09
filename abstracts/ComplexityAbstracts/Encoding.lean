/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

-- upstream: local-only (formal abstract foundations)

import ComplexityAbstracts.Check
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Nat

/-! # Binary input conventions

An encoding is an injective map to finite bitstrings; `↪` records injectivity. These fixed
conventions specify the inputs and outputs of the machines used in the abstracts. Framing makes
component boundaries recoverable with linear overhead. Natural numbers use binary digits unless
an abstract explicitly supplies a unary parameter. Changing binary to unary can change a
complexity claim. The delimiter convention below fixes the precise machine input.

The conventions are those of Christian Reitwiessner's native-machine encoding API. Their exact
definitions are collected here so each theorem can be read before its serialization details.
-/

namespace ComplexityTests.Abstracts.Encoding

/-- Make a word self-delimiting: tag each bit by `true` and finish with `false`. -/
def frame (w : List Bool) : List Bool := w.flatMap (fun b => [true, b]) ++ [false]

/-- Frame the first component, then append the second. -/
def encodePair {α β : Type} (a : α → List Bool) (b : β → List Bool) (p : α × β) :
    List Bool := frame (a p.1) ++ b p.2

/-- Concatenate the framed elements of a list. -/
def encodeList {α : Type} (enc : α → List Bool) (l : List α) : List Bool :=
  l.flatMap (frame ∘ enc)

theorem encodePair_injective {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) :
    Function.Injective (encodePair a b) := (Turing.MultiTapeTM.encPair a b).injective

theorem encodeList_injective {α : Type} (enc : α ↪ List Bool) :
    Function.Injective (encodeList enc) := (Turing.MultiTapeTM.encList enc).injective

theorem bits_injective : Function.Injective Nat.bits := Turing.MultiTapeTM.encNat.injective

/-- Injective encoding of a pair. Its length is `2 * |a x| + 1 + |b y|`. -/
def encPair {α β : Type} (a : α ↪ List Bool) (b : β ↪ List Bool) : α × β ↪ List Bool :=
  ⟨encodePair a b, encodePair_injective a b⟩

/-- Injective encoding of a list. -/
def encList {α : Type} (enc : α ↪ List Bool) : List α ↪ List Bool :=
  ⟨encodeList enc, encodeList_injective enc⟩

/-- Canonical binary digits, least significant first; zero has the empty encoding. -/
def encNat : ℕ ↪ List Bool := ⟨Nat.bits, bits_injective⟩

/-- A Boolean is a single bit. -/
def encBool : Bool ↪ List Bool := ⟨fun b => [b], by intro a b h; injection h⟩

/-- A bitstring is its own encoding. -/
def encBits : List Bool ↪ List Bool := Function.Embedding.refl _

/-- Unary size or security parameter: exactly `n` bits. -/
def encUnary : ℕ ↪ List Bool := ⟨fun n => List.replicate n true, by
  intro a b h
  simpa only [List.length_replicate] using congrArg List.length h⟩

end ComplexityTests.Abstracts.Encoding

/--
info: abstract audit passed for `ComplexityTests.Abstracts.Encoding`:
14 root declarations
-/
#guard_msgs (whitespace := lax) in
#check_abstract ComplexityTests.Abstracts.Encoding
