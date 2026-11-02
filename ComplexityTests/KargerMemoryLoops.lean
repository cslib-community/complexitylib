/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Algorithms.Lean.Karger.Memory.Loops
import ComplexityTests.KargerMemory

/-! The canonical loop forms retain the actual memory queries and a concrete cut answer.
These are memory-client tests, not native initialization or instruction-time claims. -/

namespace ComplexityTests.KargerMemoryLoops

open Cslib Cslib.DataStructure Cslib.WordRAM Cslib.WordRAM.Realization
  Cslib.Algorithms.Lean.Karger.Memory Cslib.WeightedCut
open ComplexityTests.KargerMemory

/-- Scan the triangle's degree array at offset three in canonical early-exit form. -/
private def degreeScan : Memory.Prog (ℕ × ℕ) := do
  let (_, i, r) ← boundedWhile
    (fun (_ : Block) (s : ℕ × ℕ × ℕ) => let (left, _, _) := s; 0 < left)
    (fun (b, (left, i, r)) => do
      let x ← b.get i
      if r < x then pure (0, i, r) else pure (left - 1, i + 1, r - x))
    L.degree 3 (3, 0, 3)
  pure (i, r)

/-- The second degree contains the sampled offset. The early exit reads exactly two cells,
with no extra read from the third degree or from outside the block. -/
example : (Memory.spec 8).clientResult triangleMem degreeScan = (1, 1) ∧
    (Memory.spec 8).clientHistory triangleMem degreeScan = [.read 2, .read 3] := by
  have heq : degreeScan = scan L.degree 3 0 3 := (scan_eq_boundedWhile _ _ _ _).symm
  rw [heq]
  decide

/-- Zero fuel reads no cell, even when the supplied index lies outside the block. -/
example (b : Block) (i r : ℕ) : (do
    let (_, i, r) ← boundedWhile
      (fun (_ : Block) (s : ℕ × ℕ × ℕ) => let (left, _, _) := s; 0 < left)
      (fun (b, (left, i, r)) => do
        let x ← b.get i
        if r < x then pure (0, i, r) else pure (left - 1, i + 1, r - x))
      b 0 (0, i, r)
    pure (i, r)) = (pure (i, r) : Memory.Prog (ℕ × ℕ)) := by
  rw [← scan_eq_boundedWhile]
  rfl

/-- The normalized merge and compaction loops yield a genuine cut of the original triangle,
including the skipped contracted columns. The witness is stronger than a lower bound by minCut. -/
example : ∃ C : Finset (Fin 3), IsNonTrivialCut C ∧
    (Memory.spec 8).clientResult triangleMem (do
      contract L 0 1
      total L) / 2 = cutWeight triangle C := by
  refine ⟨{0}, by unfold IsNonTrivialCut; decide, ?_⟩
  simp only [contract, shrink, compact, mergeLoop_eq_iterate, compactLoop_eq_iterate]
  decide

end ComplexityTests.KargerMemoryLoops
