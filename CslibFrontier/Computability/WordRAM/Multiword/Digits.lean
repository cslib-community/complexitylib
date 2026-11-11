/-
Copyright (c) 2026 Erik Demaine, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.WordRAM.Multiword

/-!
# Little-endian register digits

The digit value and boundedness predicates do not depend on an arithmetic routine or a
workspace layout. They apply to any register count, including an empty register file.

## Main definitions

* `Cslib.WordRAM.Multiword.value`: reconstruct a natural number from little-endian digits.
* `Cslib.WordRAM.Multiword.Bounded`: every listed register holds a digit below the radix.

## Main results

* `Cslib.WordRAM.Multiword.value_congr`: the value depends only on the listed registers.
* `Cslib.WordRAM.Multiword.value_eq_zero_of_forall`: listed registers that are all zero have
  value zero.
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword

variable {r : ℕ}

/-- The value of a little-endian register list. -/
def value (β : ℕ) (x : Data r) (ds : List (Fin r)) : ℕ :=
  Nat.ofDigits β (ds.map x.regs)

/-- The value of a digit list depends only on the registers it lists. -/
theorem value_congr {β : ℕ} {x y : Data r} {ds : List (Fin r)}
    (h : ∀ i ∈ ds, x.regs i = y.regs i) : value β x ds = value β y ds :=
  congrArg (Nat.ofDigits β) (List.map_congr_left h)

/-- A digit list whose registers are all zero has value zero. -/
theorem value_eq_zero_of_forall {β : ℕ} {x : Data r} {ds : List (Fin r)}
    (h : ∀ i ∈ ds, x.regs i = 0) : value β x ds = 0 := by
  rw [value, List.map_congr_left (g := fun _ => 0) h, List.map_const',
    Nat.ofDigits_replicate_zero]

/-- Every register in a digit list contains a radix digit. -/
def Bounded (β : ℕ) (x : Data r) (ds : List (Fin r)) : Prop :=
  ∀ i ∈ ds, x.regs i < β

end Cslib.WordRAM.Multiword
