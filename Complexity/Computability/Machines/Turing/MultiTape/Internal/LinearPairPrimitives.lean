/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.LinearPrimitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-! # Direct linear projections of the standard framed pair encoding

This separate consumer module keeps the word-machine core independent of pair codec providers.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInLinearTimeAndSpace

universe u

/-- The first component of a standard framed pair. -/
theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInLinearTimeAndSpace Prod.fst (encPair enc₁ enc₂) enc₁ :=
  of_unframe fun _ => by simp

/-- The second component of a standard framed pair. -/
theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInLinearTimeAndSpace Prod.snd (encPair enc₁ enc₂) enc₂ :=
  of_dropFrame fun _ => by simp

end Turing.MultiTapeTM.ComputableInLinearTimeAndSpace
