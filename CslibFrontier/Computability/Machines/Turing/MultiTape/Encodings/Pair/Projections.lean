/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (additions to crei/tidy-universal `Encodings/Pair.lean`)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Projections of the framed pair encoding

`unframe` and `dropFrame` recover the two components of an `encPair` word. `simp` already
proves these through `encPair_apply`, `unframe_frame_append` and `dropFrame_frame_append`. The
named lemmas are for `rw` and for proofs that must not unfold `encPair`.

## Main results

* `Turing.MultiTapeTM.unframe_encPair`: `unframe` reads the first component of an `encPair` word.
* `Turing.MultiTapeTM.dropFrame_encPair`: `dropFrame` reads the second component.
* `Turing.MultiTapeTM.unframe_encPair_encBits`, `Turing.MultiTapeTM.dropFrame_encPair_encBits`:
  the same facts for a raw bit-string component, with `encBits` already removed.
-/

public section

namespace Turing.MultiTapeTM

universe u

variable {α β : Type u}

/-- `unframe` recovers the first component of an `encPair` word. -/
theorem unframe_encPair (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (a : α) (b : β) :
    unframe (encPair enc₁ enc₂ (a, b)) = enc₁ a :=
  unframe_frame_append (enc₁ a) (enc₂ b)

/-- `dropFrame` recovers the second component of an `encPair` word. -/
theorem dropFrame_encPair (enc₁ : α ↪ List Bool) (enc₂ : β ↪ List Bool) (a : α) (b : β) :
    dropFrame (encPair enc₁ enc₂ (a, b)) = enc₂ b :=
  dropFrame_frame_append (enc₁ a) (enc₂ b)

/-- `unframe_encPair` for a raw bit-string first component. -/
theorem unframe_encPair_encBits {γ : Type} (enc : γ ↪ List Bool) (a : List Bool) (b : γ) :
    unframe (encPair encBits enc (a, b)) = a :=
  unframe_encPair encBits enc a b

/-- `dropFrame_encPair` for a raw bit-string second component. -/
theorem dropFrame_encPair_encBits {γ : Type} (enc : γ ↪ List Bool) (a : γ) (b : List Bool) :
    dropFrame (encPair enc encBits (a, b)) = b :=
  dropFrame_encPair enc encBits a b

end Turing.MultiTapeTM
