/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.BinaryDigitsPolyTime

/-!
# Exact binary-weight tensor recovery on finite examples
-/

public section

namespace Cslib.Circuits.Frontier.ExplicitTensorNetwork.BinaryDigitsTests

open Polynomial Turing.MultiTapeTM

/-- Two unary tensors sharing an edge, with contraction `3 * 7 + 5 * 11`. -/
@[expose] def weightedPair : ExplicitTensorNetwork ℕ :=
  ⟨1, [([0], [3, 5]), ([0], [7, 11])]⟩

example : binaryEntry [13] [] = [1, 0, 1, 1] ∧ binaryEntry [] [true] = [] := by decide

example : weightedPair.contraction = 76 := by decide

example : weightedPair.binaryDegreeBound 4 = 6 ∧ weightedPair.binaryPrecision 4 = 8 := by
  decide

example : (weightedPair.polyContraction binaryEntry).eval 2 = 76 := by
  rw [eval_two_polyContraction_binaryEntry]
  decide

example : evalCoeffList 2 (weightedPair.truncContraction binaryEntry 8 7) = 76 := by
  calc _ = weightedPair.contraction :=
      evalCoeffList_truncContraction_binaryEntry (B := 4) (by decide)
    _ = 76 := by decide

-- Automatic precision and truncation parameters need no separately supplied entry bound.
example (G : ExplicitTensorNetwork ℕ) :
    evalCoeffList 2 (G.truncContraction binaryEntry (G.binaryPrecision G.binaryTableBound)
      (G.binaryDegreeBound G.binaryTableBound + 1)) = G.contraction :=
  evalCoeffList_truncContraction_binaryTableBound G

example : ComputableInPolyTime (fun q : List ℕ × List Bool => binaryEntry q.1 q.2)
    (encPair (encList encNat) encBits) (encList encNat) := binaryEntry_polyTime

example : ComputableInPolyTime binaryTableBound (DescribedNetwork.encDescribed (encList encNat))
    encUnary := binaryTableBound_polyTime

end Cslib.Circuits.Frontier.ExplicitTensorNetwork.BinaryDigitsTests
