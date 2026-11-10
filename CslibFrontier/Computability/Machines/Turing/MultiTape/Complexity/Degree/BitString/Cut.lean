/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.Degree.BitString
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Unary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Combinators.TakeDropUnary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Internal.DegreePrimitives

/-!
# Linear cuts of raw bit strings

Convert to framed Boolean elements, use the existing streaming unary list cutter, and remove
framing. The complete raw word and unary count are charged. Counts beyond the word length and
empty words need no additional hypotheses.

## Main results

* `Turing.MultiTapeTM.ComputableInDegree.bitsTake`: take a unary number of raw bits.
* `Turing.MultiTapeTM.ComputableInDegree.bitsDrop`: drop a unary number of raw bits.
-/

namespace Turing.MultiTapeTM.ComputableInDegree

/-- Take a unary number of bits with linear time, workspace and output length. -/
public theorem bitsTake : ComputableInDegree (fun p : List Bool × ℕ => p.1.take p.2)
    (encPair encBits encUnary) encBits 1 1 :=
  listToBits.comp ((takeUnary encBool).comp
    ((bitsToList.comp (fst encBits encUnary)).prod (snd encBits encUnary)))

/-- Drop a unary number of bits with linear time, workspace and output length. -/
public theorem bitsDrop : ComputableInDegree (fun p : List Bool × ℕ => p.1.drop p.2)
    (encPair encBits encUnary) encBits 1 1 :=
  listToBits.comp ((dropUnary encBool).comp
    ((bitsToList.comp (fst encBits encUnary)).prod (snd encBits encUnary)))

end Turing.MultiTapeTM.ComputableInDegree
