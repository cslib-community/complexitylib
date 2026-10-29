/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Width

/-! Kernel-checked initialized native runs with actual output witnesses and charged halt. -/

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

namespace ComplexityTests.SchonhagePrunedInput

-- A negative leaf is computed once and reported at both duplicate positions. The length
-- header, original operands and first outside cell belong to the same actual run witness.
example : ∃ y n, n ≤ timeBound (L := 0) ([0, 0] : List (Fin 1)) ∧
    Runs 10 (program.program output) (State.init (input 0 (fun _ => -3) (fun _ => 2) [0, 0]))
      ⟨program.size, y⟩ n ∧
    Executes 10 (program.program output) (State.init (input 0 (fun _ => -3) (fun _ => 2) [0, 0]))
      7 (n + 1) ∧ y.mem 7 = encode (-6) ∧ y.mem 8 = encode (-6) ∧
      y.mem 0 = 6 ∧ y.mem 3 = encode (-3) ∧ y.mem (memoryEnd 0 2) = 0 := by
  obtain ⟨_, y, n, hn, hr, he, _, hv, hf⟩ := runs (w := 8) (L := 0) (A := 3) (B := 2)
    (by decide) (fun _ => -3) (fun _ => 2) ([0, 0] : List (Fin 1))
    (by intro i; decide) (by intro i; decide) (by decide) (by decide)
  refine ⟨y, n, hn, hr, he, ?_, ?_, ?_, ?_, ?_⟩
  · simpa +decide [Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.result,
      Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.run, Finset.piecewise,
      requested, outputBase] using hv 0
  · simpa +decide [Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.result,
      Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.run, Finset.piecewise,
      requested, outputBase] using hv 1
  · exact (hf 0 (by decide)).trans rfl
  · exact (hf 3 (by decide)).trans rfl
  · rw [hf _ (by decide)]
    rfl

-- The conservative address admission is explicit and has a checked failing boundary.
example : Fits 10 (addressBound 0 2) ∧ ¬Fits 9 (addressBound 0 2) := by decide +kernel

-- The bilinear specialization has an admitted signed client: the supplied leaf arrays are
-- proved to be the actual encodingL/R of the original zero-depth arrays. Its same returned
-- memory witness is reached from State.init and holds -3 * 2 = -6 after the charged run.
example : InputFits 10 (input 0 (fun _ => -3) (fun _ => 2) [0]) ∧
    ∃ y n, n ≤ timeBound (L := 0) ([0] : List (Fin 1)) ∧
      Runs 10 (program.program output) (State.init (input 0 (fun _ => -3) (fun _ => 2) [0]))
        ⟨program.size, y⟩ n ∧
      Executes 10 (program.program output)
        (State.init (input 0 (fun _ => -3) (fun _ => 2) [0])) 6 (n + 1) ∧
      y.mem 6 = encode (-6) := by
  obtain ⟨hi, y, n, hn, hr, he, _, hv, _⟩ :=
    runs_bilinear (w := 8) (L := 0) (A := 3) (B := 2) (by decide)
      (fun _ => -3) (fun _ => 2) ([0] : List (Fin 1)) (fun _ => -3) (fun _ => 2)
      (by
        intro v
        simp [Cslib.Algorithms.MatrixMultiplication.Schonhage.encodingL,
          Cslib.Algorithms.MatrixMultiplication.Schonhage.encodeLeft])
      (by
        intro v
        simp [Cslib.Algorithms.MatrixMultiplication.Schonhage.encodingR,
          Cslib.Algorithms.MatrixMultiplication.Schonhage.encodeRight])
      (by intro i; decide) (by intro i; decide) (by decide) (by decide)
  refine ⟨hi, y, n, hn, hr, he, ?_⟩
  simpa +decide [outputBase, Cslib.Algorithms.MatrixMultiplication.Schonhage.bilinearProduct,
    Cslib.Algorithms.MatrixMultiplication.Schonhage.Leaf.Contributes,
    Cslib.Algorithms.MatrixMultiplication.Schonhage.encodeLeft,
    Cslib.Algorithms.MatrixMultiplication.Schonhage.encodeRight] using hv 0

-- The input-derived physical threshold is positive and guarantees actual runs at every larger
-- width. It is a conservative sufficient threshold, rather than a claim of necessity.
example : admissionWidth 0 2 3 2 = 13 := by decide +kernel

example (W : ℕ) (hW : 13 ≤ W) :
    InputFits W (input 0 (fun _ => -3) (fun _ => 2) [0, 0]) ∧
    ∃ n, Executes W (program.program output)
      (State.init (input 0 (fun _ => -3) (fun _ => 2) [0, 0])) 7 (n + 1) := by
  have hadmit : admissionWidth 0 2 3 2 ≤ W := by
    change 13 ≤ W
    exact hW
  obtain ⟨hi, _, n, _, _, he, _, _, _⟩ := runs_wide (W := W) (L := 0) (A := 3) (B := 2)
    (fun _ => -3) (fun _ => 2) ([0, 0] : List (Fin 1))
    (by intro i; decide) (by intro i; decide) hadmit
  exact ⟨hi, n, he⟩

-- An empty query list still executes setup, root deduplication and the real controller exit.
example : ∃ y n, n ≤ timeBound (L := 0) ([] : List (Fin 1)) ∧
    Runs 10 (program.program output) (State.init (input 0 (fun _ => -3) (fun _ => 2) []))
      ⟨program.size, y⟩ n ∧
    Executes 10 (program.program output) (State.init (input 0 (fun _ => -3) (fun _ => 2) []))
      5 (n + 1) ∧ y.mem 3 = encode (-3) := by
  obtain ⟨_, y, n, hn, hr, he, _, _, hf⟩ := runs (w := 8) (L := 0) (A := 3) (B := 2)
    (by decide) (fun _ => -3) (fun _ => 2) ([] : List (Fin 1))
    (by intro i; decide) (by intro i; decide) (by decide) (by decide)
  exact ⟨y, n, hn, hr, he, (hf 3 (by decide)).trans rfl⟩

private def left2 (i : Fin 100) : ℤ := i.val + 1
private def queries2 : List (Fin 100) := [99, 90, 9, 0, 99]

-- Both digit orders, shared wildcard leaves and duplicates are observed in a depth-two actual
-- flat run. Computing the small finite specification uses the kernel, not native_decide.
example : ∃ y n, n ≤ timeBound (L := 2) queries2 ∧
    Runs 17 (program.program output) (State.init (input 2 left2 (fun _ => 1) queries2))
      ⟨program.size, y⟩ n ∧
    Executes 17 (program.program output) (State.init (input 2 left2 (fun _ => 1) queries2))
      (outputBase 2 5) (n + 1) ∧
    ∀ i : Fin 5, y.mem (outputBase 2 5 + i.val) = encode (![5050, 460, 55, 1, 5050] i) := by
  obtain ⟨_, y, n, hn, hr, he, _, hv, _⟩ := runs (w := 15) (L := 2) (A := 100) (B := 1)
    (by decide) left2 (fun _ => 1) queries2
    (by
      intro i
      have := i.isLt
      dsimp only [left2]
      rw [abs_of_nonneg (by omega)]
      omega)
    (by intro i; decide) (by decide) (by decide)
  refine ⟨y, n, hn, hr, he, ?_⟩
  intro i
  have hvalue : Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.result 2
      (fun v => left2
        (Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.leafIndex v))
      (fun _ => 1) (requested (L := 2) queries2) (queryAt (queries2.get i)) =
        ![5050, 460, 55, 1, 5050] i := by
    fin_cases i <;> decide +kernel
  rw [← hvalue]
  exact hv i

end ComplexityTests.SchonhagePrunedInput
