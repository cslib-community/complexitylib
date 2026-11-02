/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.DegreeClosure

/-! # Direct degree bounds from encoding capabilities

Pair projections reuse the degree certificates supplied by the encoding capability.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree
universe u

/-- The first component of a standard framed pair. -/
theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInDegree Prod.fst (encPair enc₁ enc₂) enc₁ 1 1 := PairEncoding.fst enc₂

/-- The second component of a standard framed pair. -/
theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInDegree Prod.snd (encPair enc₁ enc₂) enc₂ 1 1 := PairEncoding.snd enc₁

variable {d₁ e₁ d₂ e₂ : ℕ}

/-- Framed pairing retains the independent encoded-output degrees. -/
theorem prod {α β₁ β₂ : Type u} {encIn : α ↪ List Bool}
    {enc₁ : β₁ ↪ List Bool} {enc₂ : β₂ ↪ List Bool}
    {f : α → β₁} {g : α → β₂} (hf : ComputableInDegree f encIn enc₁ d₁ e₁)
    (hg : ComputableInDegree g encIn enc₂ d₂ e₂) :
    ComputableInDegree (fun x => (f x, g x)) encIn (encPair enc₁ enc₂) (max d₁ d₂)
      (max e₁ e₂) :=
  ⟨(hf.pair hg).1, (((hf.2.smul 2).add_const 1).add_max hg.2).mono fun x => by simp⟩

end Turing.MultiTapeTM.ComputableInDegree
