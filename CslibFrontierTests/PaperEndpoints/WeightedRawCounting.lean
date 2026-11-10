/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (regression tests)

public import CslibFrontier.Computability.Complexity.FineGrained.WeightedRawCounting
public import CslibFrontierTests.WeightedRagged
-- This regression intentionally checks a noncanonical default, not just the decoder laws.
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Decoder

/-!
# Raw decoder aliases, canonical counts and a genuine finite-machine client

The empty noncanonical word denotes the decoder's default empty graph/system. The canonical
parser rejects it; the total-decoder counter must instead count its one empty assignment.
-/

public section
namespace WeightedRawCountingTests
open Cslib.Logic.PL.WeightedRow.BinaryRagged Turing.MultiTapeTM
open CslibFrontierTests.WeightedRagged

/-- Concrete default of the existing total decoder on the empty noncanonical word. -/
theorem decode_empty : decoder.decode [] = (0, []) := by
  simp [decoder, Decoder.pair, Decoder.list, dropFrame, unframe, Decoder.unary]
example : canonical [] = false := by decide
example : decoder.decode (encInput mixed) = mixed := decoder.decode_enc _

/-- One actual machine simultaneously handles decoded aliases and canonical original inputs.
The mixed system retains its unused variable and hence has count two, not one. -/
example : ∃ (count : List Bool → ℕ) (C e A k : ℕ) (State : Type) (_ : Finite State)
    (tm : Turing.MultiTapeTM k Bool State),
    (∀ w, tm.ComputesInTimeAndSpace (encBits w) (encNat (count w))
      (C * (w.length + 1) ^ e *
        2 ^ (A * Nat.logLogSqrtLogScale (decoder.decode w).1)) (C * (w.length + 1) ^ e)) ∧
    count [] = 1 ∧ count (encInput mixed) = 2 ∧ count (encInput contradiction) = 0 := by
  obtain ⟨count, C, e, A, k, State, hfinite, tm, ht, _, hc⟩ := exists_countDecoded_machine 0
  refine ⟨count, C, e, A, k, State, hfinite, tm, ht, ?_, ?_, ?_⟩
  · rw [hc [], decode_empty]
    decide
  · rw [hc (encInput mixed), decoder.decode_enc]
    decide
  · rw [hc (encInput contradiction), decoder.decode_enc]
    decide

end WeightedRawCountingTests
