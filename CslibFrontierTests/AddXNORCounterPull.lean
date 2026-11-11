/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import all CslibFrontier.Cryptanalysis.AddXNORCounterPull
import all CslibFrontier.Cryptanalysis.AddXNORCounterSerialization
import all CslibFrontier.Cryptanalysis.AddXNORClasses
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.BinaryPairSums
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixSort
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Algorithms.RadixPartition

/-!
# Actual counter pull and addition clients

The checks retain zero counters and exercise forward/inverse addition, XNOR,
zero width, concentrated counts and a general original-counter resource instance.
The symbolic composition checks the interleaving semantics using `List.zip`;
it does not claim a sharp machine implementation for that missing pairing step.
-/

public section
open Turing.MultiTapeTM Cslib.Cryptanalysis.AddXNOR
open CounterPull

namespace CslibFrontierTests.AddXNORCounterPull

/-- A zero-width pull preserves the one counter; it must not double it before addition. -/
example : run (((0, 0), (false, false)), [(0, 8)]) = [(0, 8)] := by decide

example : run (((0, 0), (true, true)), [(0, 8)]) = [(0, 8)] := by decide

/-- Native original-input counters, not a supplied semantic table fixture. -/
def initial : List (ℕ × ℕ) := graph (WordTable.classCounters [] 0#3).read

example : run (((3, 1), (false, false)), initial) =
    [(0, 0), (1, 1), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 0)] := by decide

example : run (((3, 1), (true, false)), initial) =
    [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 0), (7, 1)] := by decide

example : run (((3, 1), (false, true)), initial) =
    [(0, 0), (1, 0), (2, 0), (3, 0), (4, 0), (5, 0), (6, 1), (7, 0)] := by decide

/-- The two actual sorted pulls align by state before the approved binary addition pass.
The zip specifies pairing; the CounterPairing client checks its executable replacement. -/
example {m : ℕ} (table : WordTable ℕ m) (a : BitVec m) :
    BinaryPairSums.run
      (((run (((m, a.toNat), (false, false)), graph table.read)).map Prod.snd).zip
        ((run (((m, a.toNat), (false, true)), graph table.read)).map Prod.snd)) =
      (graph (WordTable.countAdvance (stateKey a) table).ret.read).map Prod.snd := by
  rw [run_table_eq, run_table_eq]
  apply List.ext_getElem
  · simp [BinaryPairSums.run, graph]
  · intro i hi hj
    simp only [BinaryPairSums.run, List.getElem_map, List.getElem_zip, graph,
      List.getElem_ofFn]
    rw [pulled_read, pulled_read, WordTable.countAdvance_read]
    rfl

/-- The inverse layer uses the same pairing semantics and the actual backward counter update. -/
example {m : ℕ} (table : WordTable ℕ m) (a : BitVec m) :
    BinaryPairSums.run
      (((run (((m, a.toNat), (true, false)), graph table.read)).map Prod.snd).zip
        ((run (((m, a.toNat), (true, true)), graph table.read)).map Prod.snd)) =
      (graph (WordTable.countBackAdvance (stateKey a) table).ret.read).map Prod.snd := by
  rw [run_table_eq, run_table_eq]
  apply List.ext_getElem
  · simp [BinaryPairSums.run, graph]
  · intro i hi hj
    simp only [BinaryPairSums.run, List.getElem_map, List.getElem_zip, graph,
      List.getElem_ofFn]
    rw [pulled_read, pulled_read, WordTable.countBackAdvance_read]
    rfl

/-- One source-derived machine/cost witness works for both original counter directions. -/
example : ∃ P : ℕ → ℕ, Cslib.PolynomiallyBounded P ∧ Monotone P ∧
    ∃ c : Cslib.GenericRAM.NativeCertificate run encoding encNatPairList,
      c.time (((0, 0), (false, true)),
        graph (WordTable.classCounters [0#0, 0#0, 0#0] 0#0).read) ≤ P 4 ∧
      c.space (((3, 1), (true, false)),
        graph (WordTable.backwardCounters [1#3, 2#3] 0#3).read) ≤ 8 * P 6 := by
  obtain ⟨P, hp, mp, c, bound⟩ := source_certificate
  have hf := bound 0 3 (fun _ => 0#0) 0#0 0#0 false true
  have hb := bound 3 2 ![1#3, 2#3] 0#3 1#3 true false
  refine ⟨P, hp, mp, c, ?_, ?_⟩
  · simpa using hf.1
  · simpa [List.ofFn_succ] using hb.2.2.2

end CslibFrontierTests.AddXNORCounterPull
