/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
public import CslibFrontier.Foundations.Data.BitString.List.Positions
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString

/-!
# Polynomial-time reading of bit positions

`Cslib.BitString.readPositions` reads a computed word at a computed list of binary positions.
Each lookup caps its index at the word length before converting it, so positions far beyond the
word cost only their encoded length and read `false`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.bitsReadPositions`: reading binary positions of a raw
  word, in order and with repetitions, is polynomial time.
-/

public section

namespace Turing.MultiTapeTM.ComputableInPolyTime

/-- Reading a computed word at computed binary positions is polynomial time, even for positions
beyond the word. -/
@[fun_prop]
theorem bitsReadPositions {α : Type} {input : α ↪ List Bool}
    {positions : α → List ℕ} {word : α → List Bool}
    (hpositions : ComputableInPolyTime positions input (encList encNat))
    (hword : ComputableInPolyTime word input encBits) :
    ComputableInPolyTime (fun a => Cslib.BitString.readPositions (positions a) (word a))
      input encBits := by
  apply listToBits.comp
  apply mapWithInput hpositions
  exact listGetD_binary false (by fun_prop) (by fun_prop)

end Turing.MultiTapeTM.ComputableInPolyTime
