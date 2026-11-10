/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (local addition beside the vendored `Turing.MultiTapeTM.Universal` files)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.List.Size
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Universal.Bit

/-!
# The length of a bit word as universal-machine symbols

A word of bits handed to the universal machine is the framed list of its symbols
`x.map Turing.MultiTapeTM.Universal.eBit`, each written in unary. Every symbol is `0` or `1`, so
this encoding is at most three times as long as the word. The diagonal arguments of the
hierarchy theorems and the time-space speedup bound the universal machine's input this way.

## Main results

* `Turing.MultiTapeTM.Universal.length_encList_map_eBit_le`: the symbol encoding of `x` is at
  most `3 * x.length` long.
-/

public section

namespace Turing.MultiTapeTM.Universal

/-- **A bit word as symbols is linear**: the unary symbols `0` and `1` of `x` take at most
`3 * x.length` bits as a framed list. -/
theorem length_encList_map_eBit_le (x : List Bool) :
    (encList encUnary (x.map eBit)).length ≤ 3 * x.length := by
  have h := length_encList_le encUnary (x.map eBit) (b := 1) fun s hs => by
    obtain ⟨(_ | _), -, rfl⟩ := List.mem_map.mp hs <;> decide
  rw [List.length_map] at h
  omega

end Turing.MultiTapeTM.Universal
