/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Fintype.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Words
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Encoding
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearCodecPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Frame.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.FrameMachines

/-!
# Word operations for encodings

The building blocks of concrete encodings of pairs, options and lists, and their plain computability
in linear time and space (`Turing.MultiTapeTM.ComputableInLinearTimeAndSpace`).

A word `w` is *framed* by writing each symbol `b` as `[true, b]` and appending `[false]`. A framed
word marks its own end, so it can be followed by any word and still be read back.

## Main definitions

* `Turing.MultiTapeTM.frame`: the framed word.
* `Turing.MultiTapeTM.unframe`, `Turing.MultiTapeTM.dropFrame`: the word framed at the start of a
  word, and what follows the frame.

## Main results

* `Turing.MultiTapeTM.frame_append_inj`: a framed word followed by another word determines both.
* Functions that act on encoded values by `frame`, `unframe`, `dropFrame`, `List.cons true`,
  `List.tail` or `List.take 1`, or that test the encoded value for emptiness, are computable
  in linear time and space.
-/

namespace Turing.MultiTapeTM

open Encodings Internal.FrameMachines

open Encodings Internal.FrameMachines

namespace ComputableTidilyInLinearTimeAndSpace

-- vendored: `of_cons_true`, `of_tail`, `of_take_one` and `of_isEmpty` below use the run equations
-- of `Internal/CodecWordMachines` instead of the inline case analysis of crei:crei/tidy-universal

variable {α β : Type*} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β}

/-- Framing an encoded value. -/
public theorem of_frame (h : ∀ a, encOut (f a) = frame (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  frameT.computableTidilyInLinearTimeAndSpace fun a => by rw [h, frameT_run]

/-- Reading the word framed at the start of an encoded value. -/
public theorem of_unframe (h : ∀ a, encOut (f a) = unframe (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (readFrameT true).computableTidilyInLinearTimeAndSpace fun a =>
    (h a).trans (readFrameT_run_true _).symm

/-- Dropping the frame at the start of an encoded value. -/
public theorem of_dropFrame (h : ∀ a, encOut (f a) = dropFrame (encIn a)) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (readFrameT false).computableTidilyInLinearTimeAndSpace fun a =>
    (h a).trans (readFrameT_run_false _).symm

/-- Prepending `true` to an encoded value. -/
public theorem of_cons_true (h : ∀ a, encOut (f a) = true :: encIn a) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (headT none).computableTidilyInLinearTimeAndSpace fun a => by rw [h, headT_none_run]

/-- Dropping the first symbol of an encoded value. -/
public theorem of_tail (h : ∀ a, encOut (f a) = (encIn a).tail) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (headT (some false)).computableTidilyInLinearTimeAndSpace fun a => by
    rw [h, headT_some_false_run]

/-- Keeping just the first symbol of an encoded value. -/
public theorem of_take_one (h : ∀ a, encOut (f a) = (encIn a).take 1) :
    ComputableTidilyInLinearTimeAndSpace f encIn encOut :=
  (headT (some true)).computableTidilyInLinearTimeAndSpace fun a => by
    rw [h, headT_some_true_run]

/-- Testing an encoded value for emptiness. -/
public theorem of_isEmpty {f : α → Bool} (h : ∀ a, f a = (encIn a).isEmpty) :
    ComputableTidilyInLinearTimeAndSpace f encIn encBool :=
  isEmptyT.computableTidilyInLinearTimeAndSpace fun a => by rw [h, isEmptyT_run]; rfl

end ComputableTidilyInLinearTimeAndSpace


end Turing.MultiTapeTM
