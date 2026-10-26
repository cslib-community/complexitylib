/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Foundations.Data.Matrix.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Polynomial-time access to binary matrix words

Rows and columns are supplied at runtime in unary. Entries are decoded from arbitrary raw words,
padding missing bits with `false`. The result uses binary natural encoding, so no conversion to a
unary value is required.

## Main results

* `Turing.MultiTapeTM.ComputableTidilyInPolyTime.matrixBinaryEntry`: uniform entry access with
  computed dimensions, indices and input word.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableTidilyInPolyTime

/-- Read a fixed-width matrix entry from an arbitrary computed word. Dimensions and indices
are efficient unary values; the entry is returned in binary. -/
@[fun_prop]
theorem matrixBinaryEntry {α : Type} {input : α ↪ List Bool}
    {cols width row col : α → ℕ} {word : α → List Bool}
    (hcols : ComputableTidilyInPolyTime cols input encUnary)
    (hwidth : ComputableTidilyInPolyTime width input encUnary)
    (hword : ComputableTidilyInPolyTime word input encBits)
    (hrow : ComputableTidilyInPolyTime row input encUnary)
    (hcol : ComputableTidilyInPolyTime col input encUnary) :
    ComputableTidilyInPolyTime
      (fun a => Cslib.Matrix.binaryEntry (cols a) (width a) (word a) (row a) (col a))
      input encNat :=
  bitsToNat.comp (bitsRowWithInput hwidth (by fun_prop) hword)

end Turing.MultiTapeTM.ComputableTidilyInPolyTime
