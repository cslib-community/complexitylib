/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ExactTriangle.ResidueClasses

/-! # Signed initialized residue/class preparation clients -/

namespace ComplexityTests.WordRAMExactTriangleResidues

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle.ResidueClasses

private def values : List ℤ := [-1, 0, 1, -3, -4, 5, 0, 2, 7, -8, 9, -10]

private def observe (w n p : ℕ) (xs : List ℤ) : Option (List ℕ × List ℕ × ℕ × ℕ) :=
  (program.eval w (xs.length + p + 1) (.init (input n p xs))).map fun yn =>
    ((List.range (3 * (n * n))).map fun q => yn.1.mem (3 + 3 * (n * n) + q),
      (List.range p).map fun j => yn.1.mem (3 + 6 * (n * n) + j),
      yn.1.mem 3, yn.1.mem (3 + 6 * (n * n) + p + 2 * (n * n) * p))

-- Unfolding twelve signed remainder iterations and the composed class loop exceeds the
-- default interpreter-expression recursion depth.
set_option maxRecDepth 4096 in
example : observe 8 2 3 values =
    some ([2, 0, 1, 0, 2, 2, 0, 2, 1, 1, 0, 2], [2, 1, 1], 3, 0) := by decide

example : observe 8 0 3 [] = some ([], [0, 0, 0], 0, 0) := by decide

example : observe 4 2 3 values = none := by decide

/-- The complete signed residue/class execution theorem has every premise discharged, and its
memory witnesses are connected to the actual initialized compiled run. -/
example : ∃ y t, t ≤ 517 ∧
    Runs 8 (program.program counts) (State.init (input 2 3 values)) ⟨program.size, y⟩ (t - 1) ∧
    Executes 8 (program.program counts) (State.init (input 2 3 values)) 27 t ∧
    y.mem 15 = 2 ∧ y.mem 26 = 2 ∧ y.mem 27 = 2 ∧
    y.mem 30 = 0 ∧ y.mem 31 = 1 ∧ y.mem 32 = 1 ∧ y.mem 33 = 1 ∧
    y.mem 3 = 3 ∧ y.mem 54 = 0 ∧ y.Bounded 8 := by
  obtain ⟨y, hy, -, hc, -, hr, hcounts, hpairs, hframe⟩ := exec_input (w := 6) 2 3 values
    (by decide) (by decide) (by decide)
    (by
      intro q hq
      have hq' : q < 12 := hq
      have hfit : ∀ i : Fin 12, Cslib.GenericRAM.Signed.Fits 6 (values.getD i.val 0) := by
        decide
      exact hfit ⟨q, hq'⟩)
    (by unfold addressBound; decide)
  have hr0 := hr 0 (by decide)
  have hr11 := hr 11 (by decide)
  have hc0 := hcounts 0 (by decide)
  have hp0 := hpairs 0 (by decide) 1 (by decide) (by decide)
  have hp3 := hpairs 0 (by decide) 3 (by decide) (by decide)
  have hcount0 : Nat.count (fun q => (values.getD q 0 % (3 : ℤ)).toNat = 0) 4 = 2 := by
    decide
  have hrank1 : Nat.count (fun q => (values.getD q 0 % (3 : ℤ)).toNat = 0) 1 = 0 := by
    decide
  have hrank3 : Nat.count (fun q => (values.getD q 0 % (3 : ℤ)).toNat = 0) 3 = 1 := by
    decide
  obtain ⟨t, ht, he⟩ := hy
  have hrun := he.runs (pc := 0) (p := program.program counts)
    (Program.Contains.self _).append_left
  refine ⟨y, t + 1, by omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [Nat.zero_add, State.init, Nat.add_sub_cancel] using hrun
  · simpa only [State.init, hc] using he.executes counts
  · simpa [values] using hr0
  · simpa [values] using hr11
  · simpa only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd, hcount0] using hc0
  · simpa only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, hrank1] using hp0.1
  · simpa only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, hrank1] using hp0.2
  · simpa only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, hrank3] using hp3.1
  · simpa only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd, Nat.reduceMod, hrank3] using hp3.2
  · exact hframe 3 (by decide)
  · exact hframe 54 (by decide)
  · exact hrun.bounded_init (by decide : InputFits 8 (input 2 3 values))

end ComplexityTests.WordRAMExactTriangleResidues
