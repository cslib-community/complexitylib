/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.P
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Countable

/-!
# There are countably many problems in `P`

Problems in `P` are decidable (`Cslib.Complexity.isDecidable_of_mem_P`), and there are countably
many decidable problems (`Turing.MultiTapeTM.countable_setOf_isDecidable`), so `P` is countable
(`Cslib.Complexity.countable_P`). Diagonalization over `P` needs only this count: the existence of
complexity cores (`CslibFrontier.Computability.Complexity.Classes.Immune.Core`) is an example.

## Main results

* `Cslib.Complexity.isDecidable_of_mem_P`: problems in `P` are decidable.
* `Cslib.Complexity.countable_P`: there are countably many problems in `P`.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type*} {enc : α ↪ List Bool}

/-- **Problems in `P` are decidable.** -/
theorem isDecidable_of_mem_P {A : Set α} (hA : A ∈ P enc) : IsDecidable A enc :=
  let ⟨f, ⟨_, _, _, _, h⟩, hf⟩ := mem_P.mp hA
  isDecidable_iff.mpr ⟨f, ComputableInTimeAndSpace.isComputable h, hf⟩

/-- **There are countably many problems in `P`.** -/
theorem countable_P (enc : α ↪ List Bool) : (P enc).Countable :=
  (countable_setOf_isDecidable enc).mono fun _ => isDecidable_of_mem_P

end Cslib.Complexity
