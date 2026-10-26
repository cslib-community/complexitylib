/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.Degree.Primitives
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair

/-!
# Direct degree bounds from encoding machines

Pair projections unpack the encoding capability's machine witness directly. The temporary
linear encoding fields are used only as machine constructors; no higher tidy degree or
polynomial-time calculus is used. Both cost and output retain degree one.
-/

@[expose] public section
namespace Turing.MultiTapeTM.ComputableInDegree
universe u

/-- The first framed component is computable with linear cost and output growth. -/
theorem fst {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInDegree Prod.fst (encPair enc₁ enc₂) enc₁ 1 1 := by
  obtain ⟨c, k, State, hfin, tm, htm⟩ :=
    PairEncoding.fst (enc₁ := enc₁) (enc₂ := enc₂) (enc := encPair enc₁ enc₂)
  refine ⟨⟨fun p => c * ((encPair enc₁ enc₂ p).length + 1),
    fun p => c * ((encPair enc₁ enc₂ p).length + 1),
    ⟨c, fun _ => by simp⟩, ⟨c, fun _ => by simp⟩,
    k, State, hfin, tm, fun p => htm p⟩,
    ⟨c, fun p => ?_⟩⟩
  simpa using (htm p).length_output_le

/-- The second framed component is computable with linear cost and output growth. -/
theorem snd {β₁ β₂ : Type u} (enc₁ : β₁ ↪ List Bool) (enc₂ : β₂ ↪ List Bool) :
    ComputableInDegree Prod.snd (encPair enc₁ enc₂) enc₂ 1 1 := by
  obtain ⟨c, k, State, hfin, tm, htm⟩ :=
    PairEncoding.snd (enc₁ := enc₁) (enc₂ := enc₂) (enc := encPair enc₁ enc₂)
  refine ⟨⟨fun p => c * ((encPair enc₁ enc₂ p).length + 1),
    fun p => c * ((encPair enc₁ enc₂ p).length + 1),
    ⟨c, fun _ => by simp⟩, ⟨c, fun _ => by simp⟩,
    k, State, hfin, tm, fun p => htm p⟩,
    ⟨c, fun p => ?_⟩⟩
  simpa using (htm p).length_output_le

end Turing.MultiTapeTM.ComputableInDegree
