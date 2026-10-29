/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
public import Complexity.Computability.Machines.Turing.MultiTape.PolyTime
public import Complexity.Foundations.Data.Matrix.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time access to binary matrix words

Rows and columns are supplied at runtime in unary. Entries are decoded from arbitrary raw words,
padding missing bits with `false`. The result uses binary natural encoding, so no conversion to a
unary value is required.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.matrixBinaryEntry`: uniform entry access with
  computed dimensions, indices and input word.
-/

@[expose] public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Read a fixed-width matrix entry from an arbitrary computed word. Dimensions and indices
are efficient unary values; the entry is returned in binary. -/
@[fun_prop]
theorem matrixBinaryEntry {α : Type} {input : α ↪ List Bool}
    {cols width row col : α → ℕ} {word : α → List Bool}
    (_hcols : ComputableInPolyTime cols input encUnary)
    (hwidth : ComputableInPolyTime width input encUnary)
    (hword : ComputableInPolyTime word input encBits)
    (_hrow : ComputableInPolyTime row input encUnary)
    (_hcol : ComputableInPolyTime col input encUnary) :
    ComputableInPolyTime
      (fun a => Cslib.Matrix.binaryEntry (cols a) (width a) (word a) (row a) (col a))
      input encNat :=
  bitsToNat.comp (bitsRowWithInput hwidth (by fun_prop) hword)

end Turing.MultiTapeTM.ComputableInPolyTime
