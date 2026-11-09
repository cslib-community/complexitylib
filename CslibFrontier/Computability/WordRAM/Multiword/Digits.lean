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
-/

@[expose] public section

namespace Cslib.WordRAM.Multiword

variable {r : ℕ}

/-- The value of a little-endian register list. -/
def value (β : ℕ) (x : Data r) (ds : List (Fin r)) : ℕ :=
  Nat.ofDigits β (ds.map x.regs)

/-- Every register in a digit list contains a radix digit. -/
def Bounded (β : ℕ) (x : Data r) (ds : List (Fin r)) : Prop :=
  ∀ i ∈ ds, x.regs i < β

end Cslib.WordRAM.Multiword
