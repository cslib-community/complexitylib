/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import all CslibFrontier.Cryptanalysis.AddXNORCounterPairing
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.AdjacentPairs
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.BinaryPairSums
import all CslibFrontier.Cryptanalysis.AddXNORCounterPull
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
# Executed pull/pair/add clients

Both original directions use the actual keyed counter tables and the generated
side tags. Zero counters remain physical records. The generic adjacent writer's
empty/odd behavior is tested separately from the source's derived even stream.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR
open CounterPairing
namespace CslibFrontierTests.AddXNORCounterPairing

example : AdjacentPairs.run [] = [] := rfl
example : AdjacentPairs.run [(0, 9)] = [] := rfl
example : AdjacentPairs.run [(0, 5), (1, 8), (2, 13)] = [(5, 8)] := rfl

/-- Original empty-chain counters, including seven zero records. -/
def seedRows : List (ℕ × ℕ) := CounterPull.graph (WordTable.classCounters [] 0#3).read

example : layer (((3, 1), false), seedRows) = [0, 1, 0, 0, 0, 0, 1, 0] := by decide
example : layer (((3, 1), true), seedRows) = [0, 0, 0, 0, 0, 0, 1, 1] := by decide
example : (pairs (((3, 1), false), seedRows)).length = 8 := by decide

/-- Width-zero branches coincide but both multiplicities are added. -/
example : layer (((0, 0), false), CounterPull.graph
    (WordTable.classCounters [0#0, 0#0, 0#0] 0#0).read) = [16] := by decide
example : layer (((0, 0), true), CounterPull.graph
    (WordTable.backwardCounters [0#0, 0#0, 0#0] 0#0).read) = [16] := by decide

example : pairs (((2, 0), false), CounterPull.graph
    (WordTable.classCounters [0#2, 0#2] 0#2).read) = [(2, 2), (0, 0), (0, 0), (2, 2)] := by decide

/-- General actual execution agrees with the recursive DP, without supplied pairing semantics. -/
example {m : ℕ} (table : WordTable ℕ m) (a : BitVec m) (inverse : Bool) :
    layer (((m, a.toNat), inverse), CounterPull.graph table.read) =
      (CounterPull.graph (if inverse then (WordTable.countBackAdvance (stateKey a) table).ret
        else (WordTable.countAdvance (stateKey a) table).ret).read).map Prod.snd :=
  layer_table table a inverse

/-- One uniform machine handles all counter widths; no runtime conclusion is an input. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∃ c : Cslib.GenericRAM.NativeCertificate layer encoding (encList encNat),
      c.time (((0, 0), false), CounterPull.graph
        (WordTable.classCounters [0#0, 0#0, 0#0] 0#0).read) ≤ P 4 ∧
      c.space (((3, 1), true), CounterPull.graph
        (WordTable.backwardCounters [1#3, 2#3] 0#3).read) ≤ 8*P 6 := by
  obtain ⟨P, hp, mp, c, bound⟩ := source_certificate
  have hf := bound 0 3 (fun _ => 0#0) 0#0 0#0 false
  have hb := bound 3 2 ![1#3, 2#3] 0#3 1#3 true
  refine ⟨P, hp, mp, c, ?_, ?_⟩
  · simpa using hf.1
  · simpa [List.ofFn_succ] using hb.2.2.2

end CslibFrontierTests.AddXNORCounterPairing
