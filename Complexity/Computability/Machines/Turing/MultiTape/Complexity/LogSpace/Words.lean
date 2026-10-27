/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Append
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.TidyNormalForm

/-!
# Word operations and pairing in logarithmic space

The word operations underlying the encodings of pairs, options and lists — framing, reading and
dropping the first frame, prepending `true`, dropping or keeping the first symbol, and testing for
emptiness — are computed by finite-state transducers, without work tapes
(`Turing.MultiTapeTM.Transducer.computableInLogSpace`). They are therefore computable in
logarithmic space, as are the projections of pairs.

Pairing two logspace functions of the same input runs both machines one after the other, after
framing the first value; the work space is the sum of the two
(`Turing.MultiTapeTM.ComputableTidilyInTimeAndSpace.append`).

## Main results

* `Turing.MultiTapeTM.ComputableInLogSpace.of_frame`, `.of_unframe`, `.of_dropFrame`,
  `.of_cons_true`, `.of_tail`, `.of_take_one`, `.of_isEmpty`: word operations.
* `Turing.MultiTapeTM.ComputableInLogSpace.fst`, `Turing.MultiTapeTM.ComputableInLogSpace.snd`:
  projections of pairs.
* `Turing.MultiTapeTM.ComputableInLogSpace.pair`: pairing.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInLogSpace

open Encodings Internal.FrameMachines

variable {α β : Type} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}

/-- Framing an encoded value. -/
theorem of_frame (h : ∀ a, encOut (f a) = frame (encIn a)) :
    ComputableInLogSpace f encIn encOut :=
  frameT.computableInLogSpace fun a => by rw [h, frameT_run]

/-- Reading the word framed at the start of an encoded value. -/
theorem of_unframe (h : ∀ a, encOut (f a) = unframe (encIn a)) :
    ComputableInLogSpace f encIn encOut :=
  (readFrameT true).computableInLogSpace fun a => (h a).trans (readFrameT_run_true _).symm

/-- Dropping the frame at the start of an encoded value. -/
theorem of_dropFrame (h : ∀ a, encOut (f a) = dropFrame (encIn a)) :
    ComputableInLogSpace f encIn encOut :=
  (readFrameT false).computableInLogSpace fun a => (h a).trans (readFrameT_run_false _).symm

/-- Prepending `true` to an encoded value. -/
theorem of_cons_true (h : ∀ a, encOut (f a) = true :: encIn a) :
    ComputableInLogSpace f encIn encOut :=
  (headT none).computableInLogSpace fun a => by rw [h, headT_none_run]

/-- Dropping the first symbol of an encoded value. -/
theorem of_tail (h : ∀ a, encOut (f a) = (encIn a).tail) : ComputableInLogSpace f encIn encOut :=
  (headT (some false)).computableInLogSpace fun a => by rw [h, headT_some_false_run]

/-- Keeping just the first symbol of an encoded value. -/
theorem of_take_one (h : ∀ a, encOut (f a) = (encIn a).take 1) :
    ComputableInLogSpace f encIn encOut :=
  (headT (some true)).computableInLogSpace fun a => by rw [h, headT_some_true_run]

/-- Testing an encoded value for emptiness. -/
theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableInLogSpace f encIn encBool :=
  isEmptyT.computableInLogSpace fun a => by rw [h, isEmptyT_run]; rfl

variable {β₁ β₂ : Type} {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}

/-- The first component of a pair. -/
theorem fst (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInLogSpace Prod.fst (encPair enc₁ enc₂) enc₁ :=
  of_unframe fun p => by simp

/-- The second component of a pair. -/
theorem snd (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInLogSpace Prod.snd (encPair enc₁ enc₂) enc₂ :=
  of_dropFrame fun p => by simp

/-- **Pairing**: the values of two logspace functions of the same input, framed first value
followed by the second, are computed in logarithmic space. -/
theorem pair {f₁ : α → β₁} {f₂ : α → β₂} (h₁ : ComputableInLogSpace f₁ encIn enc₁)
    (h₂ : ComputableInLogSpace f₂ encIn enc₂) :
    ComputableInLogSpace (fun a => (f₁ a, f₂ a)) encIn (encPair enc₁ enc₂) := by
  have hF : ComputableInLogSpace f₁ encIn (encFramed enc₁) :=
    (of_frame (encIn := enc₁) (encOut := encFramed enc₁) (f := fun b => b) fun _ => rfl).comp h₁
  obtain ⟨t₁, c₁, hF⟩ := hF
  obtain ⟨t₂, c₂, h₂⟩ := h₂
  obtain ⟨d₁, hF⟩ := hF.exists_computableTidilyInTimeAndSpace
  obtain ⟨d₂, h₂⟩ := h₂.exists_computableTidilyInTimeAndSpace
  obtain ⟨k, h⟩ := hF.append h₂ (g := fun a => (f₁ a, f₂ a)) (encOut := encPair enc₁ enc₂)
    fun a => rfl
  refine ⟨_, d₁ * (c₁ + 1) + d₂ * (c₂ + 1) + k, h.computableInTimeAndSpace.mono
    (fun _ => le_rfl) fun a => ?_⟩
  generalize Nat.log2 (encIn a).length = l
  nlinarith [Nat.zero_le l, Nat.zero_le (d₁ * c₁ * l), Nat.zero_le (d₂ * c₂ * l)]

end Turing.MultiTapeTM.ComputableInLogSpace
