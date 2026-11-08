/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Kolmogorov.SelfDelimiting
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.BitString
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListLookup
import Complexity.Computability.Machines.Turing.MultiTape.Internal.PolyTimeListPrimitives

/-!
# Native polynomial-time self-delimiting decoding

The original total decoder is computed on every raw word by capping the decoded
length at the available payload length. Thus malformed huge length headers do not
require a huge unary counter. Capping changes neither `take` nor `drop`.

## Main results

* `Turing.MultiTapeTM.ComputableInPolyTime.decodeSelfDelimiting`: native decoding of the
  original self-delimiting format, including malformed words.
-/

public section
namespace Turing.MultiTapeTM
open Cslib

private def boundedSplit (word : List Bool) : List Bool × List Bool :=
  let width := word.idxOf false
  let suffix := word.drop (width + 1)
  let payload := suffix.drop width
  let count := BitString.boundedBinaryValue payload.length (suffix.take width).reverse
  (payload.take count, payload.drop count)

private theorem boundedSplit_eq (word : List Bool) :
    boundedSplit word = Kolmogorov.decodeSelfDelimiting word := by
  simp only [boundedSplit, Kolmogorov.decodeSelfDelimiting,
    BitString.boundedBinaryValue_eq, ← ofBits_reverse, List.reverse_reverse, ofBits]
  apply Prod.ext
  · rw [Nat.min_comm, ← List.take_eq_take_min]
  · rw [Nat.min_comm, ← List.drop_eq_drop_min]

namespace ComputableInPolyTime

/-- Decode the existing total self-delimiting format with a native polynomial
local clock. No numerical header bound or validity promise is required. -/
@[fun_prop] theorem decodeSelfDelimiting : ComputableInPolyTime
    Kolmogorov.decodeSelfDelimiting encBits (encPair encBits encBits) := by
  have hi : ComputableInPolyTime (fun w : List Bool => w.idxOf false) encBits encUnary :=
    idxOfWithInput bitsToList (const false)
  let suffix (w : List Bool) := w.drop (w.idxOf false + 1)
  have hs : ComputableInPolyTime suffix encBits encBits := by unfold suffix; fun_prop
  let payload (w : List Bool) := (suffix w).drop (w.idxOf false)
  have hp : ComputableInPolyTime payload encBits encBits := by unfold payload; fun_prop
  have hc : ComputableInPolyTime (fun w =>
      BitString.boundedBinaryValue (payload w).length ((suffix w).take (w.idxOf false)).reverse)
      encBits encUnary := by fun_prop
  have hb : ComputableInPolyTime boundedSplit encBits (encPair encBits encBits) := by
    change ComputableInPolyTime
      (fun w => ((payload w).take (BitString.boundedBinaryValue (payload w).length
          ((suffix w).take (w.idxOf false)).reverse),
        (payload w).drop (BitString.boundedBinaryValue (payload w).length
          ((suffix w).take (w.idxOf false)).reverse))) encBits _
    fun_prop
  have he : boundedSplit = Kolmogorov.decodeSelfDelimiting := funext boundedSplit_eq
  rwa [he] at hb

end ComputableInPolyTime
end Turing.MultiTapeTM
