/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import all CslibFrontier.Cryptanalysis.AddXNORCounterSerialization
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.BinaryPairSums

/-!
# Serialized original-input DP layer clients

These clients test both directions, zero width, zero counters, branch collisions
and addition that is not self-inverse. The resource certificate is for the
interleaved counter-addition pass, not preparation of the pulled tables.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR

/-- One pair at zero width must still add both coinciding branches. -/
example : BinaryPairSums.run (WordTable.forwardPairs 0#0
    (WordTable.classCounters [0#0, 0#0, 0#0] 0#0)) = [16] := by decide

example : BinaryPairSums.run (WordTable.backwardPairs 0#0
    (WordTable.backwardCounters [0#0, 0#0, 0#0] 0#0)) = [16] := by decide

/-- Zero counters remain physical entries; a collision gives weight two, not one. -/
example : BinaryPairSums.run (WordTable.forwardPairs 0#2
    (WordTable.classCounters [0#2] 0#2)) = [2, 0, 0, 2] := by decide

/-- Addition by one and its inverse reach different full states. -/
example : BinaryPairSums.run (WordTable.forwardPairs 1#3
    (WordTable.classCounters [] 0#3)) = [0, 0, 0, 1, 1, 0, 0, 0] := by decide

example : BinaryPairSums.run (WordTable.backwardPairs 1#3
    (WordTable.backwardCounters [] 0#3)) = [0, 0, 0, 1, 0, 0, 0, 1] := by decide

example : BinaryPairSums.run (WordTable.forwardPairs 1#3
    (WordTable.classCounters [1#3, 2#3] 0#3)) =
      WordTable.entries (WordTable.classCounters [1#3, 2#3, 1#3] 0#3) := by decide

example : BinaryPairSums.run (WordTable.backwardPairs 1#3
    (WordTable.backwardCounters [1#3, 2#3] 0#3)) =
      WordTable.entries (WordTable.backwardCounters [1#3, 1#3, 2#3] 0#3) := by decide

/-- General original-input layers, not a supplied execution or count-table conclusion. -/
example {m : ℕ} (as : List (BitVec m)) (s a : BitVec m) :
    BinaryPairSums.run (WordTable.forwardPairs a (WordTable.classCounters as s)) =
      WordTable.entries (WordTable.classCounters (as ++ [a]) s) :=
  WordTable.forward_layer_append as s a

/-- The same uniform machine and polynomial handle every original projected width and count. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∃ c : Cslib.GenericRAM.NativeCertificate BinaryPairSums.run encNatPairList (encList encNat),
      c.time (WordTable.forwardPairs 0#0
        (WordTable.classCounters [0#0, 0#0, 0#0] 0#0)) ≤ P 4 ∧
      c.space (WordTable.backwardPairs 1#3
        (WordTable.backwardCounters [1#3, 2#3] 0#3)) ≤ 8 * P 3 := by
  obtain ⟨P, hp, hm, c, bound⟩ := WordTable.layer_certificate
  have forward := bound 0 3 (fun _ => 0#0) 0#0 0#0
  have backward := bound 3 2 ![1#3, 2#3] 0#3 1#3
  refine ⟨P, hp, hm, c, ?_, ?_⟩
  · simpa using forward.1
  · simpa [List.ofFn_succ] using backward.2.2.2
