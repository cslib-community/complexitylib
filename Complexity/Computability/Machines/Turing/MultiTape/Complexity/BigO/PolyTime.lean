/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO.Bounds
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Polynomial time as charged asymptotic bounds

A function computable in polynomial time is computable within charged bounds `O(T)` and `O(S)`
that are polynomial in the length of the encoded input. The time bound is the time of a realizing
machine; the space bound is the sum of its time and space, since the charged space also bounds the
length of the encoded output, which the machine's time bounds.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.exists_computableInO`: polynomial time gives
  polynomial charged bounds.
-/

namespace Turing.MultiTapeTM

variable {α β : Type*} {f : α → β} {encIn : α ↪ List Bool} {encOut : β ↪ List Bool}

/-- **Polynomial time gives polynomial charged bounds**: a function computable in polynomial time is
computable within time `O(T)` and space `O(S)` for bounds polynomial in the length of the encoded
input, namely the time of a realizing machine and the sum of its time and space. -/
public theorem ComputableInPolyTime.exists_computableInO (h : ComputableInPolyTime f encIn encOut) :
    ∃ T S, PolyBounded (fun a => (encIn a).length) T ∧ PolyBounded (fun a => (encIn a).length) S ∧
      ComputableInO f encIn encOut T S := by
  obtain ⟨t, s, ht, hs, h⟩ := h
  exact ⟨_, _, .of_polynomiallyBounded _ ht,
    (PolyBounded.of_polynomiallyBounded _ ht).add (.of_polynomiallyBounded _ hs),
    .of_bounds h 1 (fun _ => by omega) (fun _ => by omega) fun a => by
      have := h.length_le a
      omega⟩

end Turing.MultiTapeTM
