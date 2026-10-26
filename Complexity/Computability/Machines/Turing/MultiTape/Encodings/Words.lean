/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)

public import Mathlib.Data.Fintype.Basic
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Capabilities
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

-- upstream: vendored crei:crei/tidy-universal @9cce4cc7 (unsubmitted)
-- vendored: `encOfEquiv` below, from that revision's `Encodings/Basic`
/-- The encoding of `α` through an equivalence with `β`, such as that of a structure with the
tuple of its fields. -/
@[expose] public def encOfEquiv {α β : Type*} (e : α ≃ β) (enc : β ↪ List Bool) :
    α ↪ List Bool :=
  e.toEmbedding.trans enc

@[simp] public lemma encOfEquiv_apply {α β : Type*} (e : α ≃ β) (enc : β ↪ List Bool) (a : α) :
    encOfEquiv e enc a = enc (e a) := rfl



end Turing.MultiTapeTM
