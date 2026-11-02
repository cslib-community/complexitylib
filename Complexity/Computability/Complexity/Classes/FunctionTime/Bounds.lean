/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.FunctionTime
import Complexity.Computability.Machines.Turing.MultiTape.Internal.ResourceFacts

/-!
# Charged bounds of function-time computations

A function in `Cslib.Complexity.FTIME enc encOut t` is computed within time `c₁ * t n + c₂`. As
a computation within time `O(t n)` (`Turing.MultiTapeTM.ComputableInO`), it carries the
workspace of its certificate, and its encoded output, written within the time bound, has length
`O(t n)`. Clients that compose function-time outputs with further computations, such as a
polynomial-time test of two counts, start from this form.

## Main results

* `Cslib.Complexity.FTIME.exists_computableInO`: a function in `FTIME[t]` is computable within
  time `O(t n)`, with encoded output length `O(t n)`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α β : Type} {enc : α ↪ List Bool} {encOut : β ↪ List Bool} {t : ℕ → ℕ} {f : α → β}

/-- **Function time as charged native bounds.** A function in `FTIME[t]` is computable within
time `O(t n)` and the workspace `t n + s n` of its certificate, and its encoded output has length
`O(t n)`, with the constant `c` fixed before the input. -/
theorem FTIME.exists_computableInO (hf : f ∈ FTIME enc encOut t) :
    ∃ (c : ℕ) (s : ℕ → ℕ), ComputableInO f enc encOut (fun a => t (enc a).length)
        (fun a => t (enc a).length + s (enc a).length) ∧
      ∀ a, (encOut (f a)).length ≤ c * (t (enc a).length + 1) := by
  obtain ⟨c₁, c₂, s, h⟩ := hf
  have hl (a : α) : (encOut (f a)).length ≤ (c₁ + c₂ + 1) * (t (enc a).length + 1) :=
    (h.length_le a).trans (by nlinarith)
  exact ⟨c₁ + c₂ + 1, s, ⟨c₁ + c₂ + 1, h.mono (fun _ => by dsimp only; nlinarith)
    (fun _ => by dsimp only; nlinarith), fun a => (hl a).trans (by nlinarith)⟩, hl⟩

end Cslib.Complexity
