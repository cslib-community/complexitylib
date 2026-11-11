/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating

/-!
# Alternating polynomial time `AP`

The class `Cslib.Complexity.AP` consists of the problems decided within polynomial time by
alternating machines (`Turing.MultiTapeATM`, in
`CslibFrontier.Computability.Machines.Turing.MultiTape.Alternating`) with a binary alphabet and
finitely many states [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Arora and Barak, Section 5.3][AroraBarak09] [Sipser, Section 10.3][Sipser2013]. Like
`Turing.MultiTapeNTM.DecidableInPolyTime`, it is relative to the encoding of instances. It is
`PSPACE` (`Cslib.Complexity.AP_eq_PSPACE`, in
`CslibFrontier.Computability.Complexity.Classes.Alternation.Savitch`).

## Main definitions

* `Cslib.Complexity.AP`: alternating polynomial time.

## References

* [A. K. Chandra, D. C. Kozen, L. J. Stockmeyer, *Alternation*][ChandraKozenStockmeyer1981]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
* [M. Sipser, *Introduction to the Theory of Computation*][Sipser2013]
-/

@[expose] public section

namespace Cslib.Complexity

open Turing

/-- **Alternating polynomial time** [Chandra, Kozen and Stockmeyer][ChandraKozenStockmeyer1981]
[Arora and Barak, Section 5.3][AroraBarak09]: the problems decided within polynomial time by an
alternating machine with a binary alphabet and finitely many states, with respect to the encoding
`enc` of instances. -/
def AP {α : Type} (enc : α ↪ List Bool) : Set (Set α) :=
  {A | MultiTapeATM.DecidableInPolyTime A enc}

end Cslib.Complexity
