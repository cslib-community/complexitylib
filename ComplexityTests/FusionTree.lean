/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.DataStructure.FusionTree.Compression
import Complexity.DataStructure.FusionTree.Correction
import Complexity.DataStructure.FusionTree.Tree
import Complexity.DataStructure.FusionTree.WordRAM.Packed
import Complexity.Computability.WordRAM.PackedCount
import Complexity.Computability.WordRAM.Multiword

/-! Nonvacuity, arbitrary-query correction, sparse compression, and actual RAM fragments.
The complete fusion-node RAM implementation and predecessor-time endpoint are separate. -/

open Cslib.BitString
open Cslib.DataStructure.FusionTree
open Cslib.WordRAM

namespace FusionTreeTests

/-- Empty and singleton nodes require no selected bits, even at width zero. -/
example : relevantBits 0 (fun i : Fin 0 => i.elim0) = ∅ ∧
    relevantBits 0 (fun _ : Fin 1 => 0) = ∅ := by decide

/-- Four stored keys are distinguished by three bits. -/
example : relevantBits 6 ![16, 17, 19, 27] = {0, 1, 3} := by decide

/-- The original sketch gives the wrong query rank; correction returns the true rank. -/
example : sketchRank 4 ![0, 2, 12, 15] 5 = 1 ∧
    correctedRank 4 ![0, 2, 12, 15] 5 = 2 := by
  have hbits : relevantBits 4 ![0, 2, 12, 15] = {1, 3} := by decide
  have hsort : ({1, 3} : Finset ℕ).sort (· ≤ ·) = [1, 3] := by simp [Finset.sort_insert]
  constructor
  · simp only [sketchRank, hbits, sketch, hsort, upperRank, projectBits]
    decide
  · rw [correctedRank_eq_upperRank (by decide) (by decide) (by decide)]
    unfold upperRank
    decide

/-- Inclusive ranks cover exact hits, absent predecessors, and both extreme queries. -/
example : correctedRank 4 ![2, 12, 15] 0 = 0 ∧
    correctedRank 4 ![0, 2, 12, 15] 0 = 1 ∧
    correctedRank 4 ![0, 2, 12, 15] 12 = 3 ∧
    correctedRank 4 ![0, 2, 12, 15] 15 = 4 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    rw [correctedRank_eq_upperRank (by decide) (by decide) (by decide)] <;>
    unfold upperRank <;> decide

example : correctedRank 0 (fun i : Fin 0 => i.elim0) 0 = 0 := by decide

/-- Nontrivial collision-free positions and shifts exist without bundled correctness assumptions. -/
example : Function.Injective (fun p : Fin 2 × Fin 2 => (![0, 3] p.1) + (![4, 8] p.2)) :=
  by decide

/-- Both retained bits and all intervening zeros are checked by the exact numeric result. -/
example : approximateSketch 4 ![0, 3] ![4, 8] 9 = 129 ∧
    approximateSketch 4 ![0, 3] ![4, 8] 8 = 128 ∧
    approximateSketch 4 ![0, 3] ![4, 8] 1 = 1 := by decide

/-- Constructed trees handle empty input, incomplete right branches, and a query below all keys. -/
example : Tree.predecessor 5 (Tree.build 3 []) = none ∧
    Tree.predecessor 8 (Tree.build 3 [2, 4, 7, 9, 13]) = some 7 ∧
    Tree.predecessor 0 (Tree.build 2 [2, 4, 7, 9, 13]) = none ∧
    Tree.predecessor 13 (Tree.build 4 [2, 4, 7, 9, 13]) = some 13 := by
  simp [Tree.build, Tree.buildAux, Tree.join, Tree.chunks, Tree.predecessor,
    Tree.selectChild, Tree.minimum, Tree.keys, Tree.listPredecessor, Nat.clog, Nat.clog.go,
    List.splitLengths, List.take, List.drop, Option.or]

/-- Structural height and storage bounds have constants independent of the branching factor. -/
example (xs : List ℕ) :
    (Tree.build 3 xs).height ≤ Nat.log 3 xs.length + 1 ∧
      (Tree.build 3 xs).slots ≤ 14 * xs.length + 2 :=
  ⟨Tree.height_build_le_log_add_one (by decide) xs, Tree.slots_build_le (by decide) xs⟩

/-- Three packed flags, including a zero between two ones. -/
def flags (i : ℕ) : Bool := decide (i = 0 ∨ i = 2)

/-- Actual interpreter execution of the three-instruction counting fragment. -/
def countData : Data 5 :=
  ⟨![Cslib.BitString.packRadix 4 3 (fun i => (flags i).toNat),
      Cslib.BitString.packRadix 4 3 (fun _ => 1), 4 ^ 2, 4, 0], fun _ => 0⟩

example : (PackedCount.code.eval 12 0 countData).map
    (fun p => (p.1.regs 4, p.2)) = some (2, 3) := by decide

/-- The half-word update handles maximum digits and an odd physical word size. -/
example : (Multiword.LimbUpdate.program.eval 3 0
    ⟨![1, 1, 1, 1, 2, 0, 0], fun _ => 0⟩).map
    (fun p => (p.1.regs 6, p.1.regs 3, p.2)) = some (1, 1, 5) := by decide

end FusionTreeTests
