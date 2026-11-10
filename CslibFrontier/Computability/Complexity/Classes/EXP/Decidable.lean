/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.EXP
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Computable

/-!
# Problems in exponential time are decidable

A problem decidable within a time bound is decidable (`Cslib.Complexity.isDecidable_of_mem_DTIME`):
the bounded decider is a total decider. Hence problems in `EXP` and in `E` are decidable
(`Cslib.Complexity.isDecidable_of_mem_EXP`, `Cslib.Complexity.isDecidable_of_mem_E`). The
polynomial-time case is `Cslib.Complexity.isDecidable_of_mem_P` in
`CslibFrontier.Computability.Complexity.Classes.P.Countable`; it agrees with the time-bounded case
through `Cslib.Complexity.mem_P_iff_exists_mem_DTIME`.

## Main results

* `Cslib.Complexity.isDecidable_of_mem_DTIME`, `Cslib.Complexity.isDecidable_of_mem_EXP`,
  `Cslib.Complexity.isDecidable_of_mem_E`: problems decidable within a time bound are decidable.
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

variable {α : Type*} {enc : α ↪ List Bool} {A : Set α}

/-- **Problems decidable within a time bound are decidable.** -/
theorem isDecidable_of_mem_DTIME {t : ℕ → ℕ} (hA : A ∈ DTIME enc t) : IsDecidable A enc :=
  let ⟨_, _, _, h⟩ := hA
  ⟨_, _, h⟩

/-- **Problems in `EXP` are decidable.** -/
theorem isDecidable_of_mem_EXP (hA : A ∈ EXP enc) : IsDecidable A enc :=
  let ⟨_, hk⟩ := mem_EXP_iff.mp hA
  isDecidable_of_mem_DTIME hk

/-- **Problems in `E` are decidable.** -/
theorem isDecidable_of_mem_E (hA : A ∈ E enc) : IsDecidable A enc :=
  isDecidable_of_mem_EXP (E_subset_EXP hA)

end Cslib.Complexity
