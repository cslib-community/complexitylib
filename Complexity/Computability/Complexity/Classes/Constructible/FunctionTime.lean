/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Constructible
public import Complexity.Computability.Complexity.Classes.FunctionTime

/-!
# Constructible bounds in function time

A time-constructible bound `T` is computed in binary within time `O(T n)` from any word of length
`n`. Run on the encoding of an instance, the same machine computes `T |enc a|` in
`FTIME enc encNat T`, for every input encoding `enc`. Clocked simulations use this to compute
their clock from the input.

## Main results

* `Cslib.Complexity.TimeConstructible.mem_FTIME`: a time-constructible bound of the encoded
  length is in function time.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type} {enc : α ↪ List Bool}

/-- **A time-constructible bound is computed within its own time.** For every input encoding
`enc`, the bound `T |enc a|` of the encoded length is in `FTIME enc encNat T`. -/
theorem TimeConstructible.mem_FTIME {T : ℕ → ℕ} (hT : TimeConstructible T) :
    (fun a => T (enc a).length) ∈ FTIME enc encNat T := by
  obtain ⟨c, s, K, Q, hQ, tm, htm⟩ := hT
  exact ⟨c, c, s, K, Q, hQ, tm, fun a => htm (enc a)⟩

end Cslib.Complexity
