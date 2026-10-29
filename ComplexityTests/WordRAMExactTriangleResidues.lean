/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.ExactTriangle.Catalogue
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

private def callerInput : List ℕ := [2, 1, 2, 3] ++ values.map Signed.encode

private def caller : Data 32 :=
  ((Data.init callerInput).set 7 23).write 0 199 |>.write 60 77

-- The same twelve signed iterations exceed the default interpreter-expression recursion depth.
set_option maxRecDepth 4096 in
example : ((programAt 3).eval 8 16 caller).map (fun (y, _) =>
    ((List.range 12).map fun q => y.mem (17 + q),
      (List.range 3).map fun j => y.mem (29 + j),
      [y.mem 0, y.mem 1, y.mem 2, y.mem 60])) =
    some ([2, 0, 1, 0, 2, 2, 0, 2, 1, 1, 0, 2], [2, 1, 1], [199, 2, 1, 77]) := by decide

/-- Caller header and signed payload are actual memory, with unrelated prefix words preserved. -/
example : ∃ y, ExecWithin 8 (programAt 3) caller y 516 ∧
    y.mem 0 = 199 ∧ y.mem 1 = 2 ∧ y.mem 2 = 1 ∧
    y.mem 17 = 2 ∧ y.mem 29 = 2 ∧ y.mem 60 = 77 := by
  have hwords : ∀ i : Fin 12,
      caller.mem (5 + i.val) = Signed.encode (values.getD i.val 0) := by decide
  have hvalues : ∀ i : Fin 12,
      Cslib.GenericRAM.Signed.Fits 6 (values.getD i.val 0) := by decide
  obtain ⟨y, hy, -, -, -, hr, hc, -, hf⟩ := exec_at (w := 6) 3 2 3
    (fun q => values.getD q 0) caller (by decide) (by decide)
    (by intro q hq; exact hwords ⟨q, hq⟩) (by decide) (by decide)
    (by intro q hq; exact hvalues ⟨q, hq⟩) (by unfold addressBoundAt; decide)
  have hr0 := hr 0 (by decide)
  have hc0 := hc 0 (by decide)
  have hcount : Nat.count (fun q => (values.getD q 0 % (3 : ℤ)).toNat = 0) 4 = 2 := by
    decide
  refine ⟨y, hy, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (hf 0 (Or.inl (by decide))).trans (by decide)
  · exact (hf 1 (Or.inl (by decide))).trans (by decide)
  · exact (hf 2 (Or.inl (by decide))).trans (by decide)
  · simpa [values] using hr0
  · simpa only [Nat.cast_ofNat, Nat.reduceMul, Nat.reduceAdd, hcount] using hc0
  · exact (hf 60 (Or.inr (by decide))).trans (by decide)

namespace CompleteCatalogue

open Cslib.Algorithms.WordRAM.ExactTriangle

private def raw : List ℕ := [1, 1, 2, 3] ++ values.map Signed.encode

private def tiny : List ℕ := [1, 1, 1, 2] ++ ([-1, 0, 1] : List ℤ).map Signed.encode

-- The composed controller includes signed residue loops, two square-root loops and nested
-- class/chunk loops in one interpreter expression.
set_option maxRecDepth 4096 in
example : (Catalogue.program.eval 10 4 (.init tiny)).map (fun (y, _) =>
    ([y.mem 17, y.mem 18, y.mem 19],
      [y.regs Catalogue.pieceLength, y.regs Catalogue.pieces,
        y.regs ChunkCatalogue.capacity, y.regs ChunkCatalogue.written,
        y.regs ChunkCatalogue.heap, y.mem 5, y.mem 8, y.mem 20])) =
    some ([1, 15, 1], [1, 1, 1, 1, 20, 3, 1, 0]) := by decide +kernel

/-- Every supplied value is an actual initialized word, and both parameter computations and
the descriptor count/readback come from the same charged compiled run. -/
example : ∃ y t, t ≤ 861 ∧
    Runs 10 (Catalogue.program.program ChunkCatalogue.written) (State.init raw)
      ⟨Catalogue.program.size, y⟩ (t - 1) ∧
    Executes 10 (Catalogue.program.program ChunkCatalogue.written) (State.init raw) 3 t ∧
    y.regs Catalogue.pieceLength = 1 ∧ y.regs Catalogue.pieces = 2 ∧
    y.mem 56 = 0 ∧ y.mem 57 = 32 ∧ y.mem 58 = 2 ∧
    y.mem 63 = 48 ∧ y.mem 64 = 1 ∧ y.mem 5 = 3 ∧ y.mem 65 = 0 := by
  have hwords : ∀ i : Fin 12,
      (Data.init raw : Data 32).mem (5 + i.val) = Signed.encode (values.getD i.val 0) := by
    decide
  have hvalues : ∀ i : Fin 12,
      Cslib.GenericRAM.Signed.Fits 8 (values.getD i.val 0) := by decide
  obtain ⟨y, hy, -, -, -, -, hd, hcap, hlen, hpieces, hcount, hheap, hr,
    hc, hq, hdesc, hf⟩ := Catalogue.exec_at (w := 8) 2 1 1 3
      (fun q => values.getD q 0) (.init raw)
      (by decide) (by decide) (by decide) (by decide)
      (by intro q hq; exact hwords ⟨q, hq⟩)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by intro q hq; exact hvalues ⟨q, hq⟩) (by unfold Catalogue.budget; decide)
  have hQ : Cslib.Algorithms.ExactTriangle.queryCap 2 1 = 4 := by
    have hlow : 4 ≤ Nat.sqrt 16 := Nat.le_sqrt.mpr (by decide)
    have hhigh : Nat.sqrt 16 < 5 := Nat.sqrt_lt.mpr (by decide)
    have heq : Nat.sqrt 16 = 4 := by omega
    simpa only [Cslib.Algorithms.ExactTriangle.queryCap, Nat.reducePow, Nat.div_one] using heq
  have hB : Cslib.Algorithms.ExactTriangle.pieceSize 1 1 = 1 := by decide
  have hH : Cslib.Algorithms.ExactTriangle.numPieces 2 1 1 = 2 := by decide
  let C := fun rho => Nat.count (fun q => (values.getD q 0 % (3 : ℤ)).toNat = rho) 4
  have hc0 : C 0 = 2 := by decide
  have hc1 : C 1 = 1 := by decide
  have hc2 : C 2 = 1 := by decide
  change y.regs ChunkCatalogue.written =
    ChunkCatalogue.before C (Cslib.Algorithms.ExactTriangle.queryCap 2 1) 3 at hcount
  have hbefore0 : ChunkCatalogue.before C 4 0 = 0 := by simp [ChunkCatalogue.before]
  have hbefore2 : ChunkCatalogue.before C 4 2 = 2 := by
    simp only [ChunkCatalogue.before, Finset.sum_range_succ, Finset.sum_range_zero,
      hc0, hc1, Nat.zero_add, Nat.ceilDiv_eq_add_pred_div]
  have hbefore3 : ChunkCatalogue.before C 4 3 = 3 := by
    simp only [ChunkCatalogue.before, Finset.sum_range_succ, Finset.sum_range_zero,
      hc0, hc1, hc2, Nat.zero_add, Nat.ceilDiv_eq_add_pred_div]
  have hcTotal : y.regs ChunkCatalogue.written = 3 := by
    simpa only [hQ, hbefore3] using hcount
  change (∀ rho < 3, ∀ k < C rho ⌈/⌉ Cslib.Algorithms.ExactTriangle.queryCap 2 1,
    y.mem (56 + 3 * (ChunkCatalogue.before C
      (Cslib.Algorithms.ExactTriangle.queryCap 2 1) rho + k)) = rho ∧
    y.mem (56 + 3 * (ChunkCatalogue.before C
      (Cslib.Algorithms.ExactTriangle.queryCap 2 1) rho + k) + 1) =
        32 + 2 * rho * 4 + 2 * (k * Cslib.Algorithms.ExactTriangle.queryCap 2 1) ∧
    y.mem (56 + 3 * (ChunkCatalogue.before C
      (Cslib.Algorithms.ExactTriangle.queryCap 2 1) rho + k) + 2) =
        min (Cslib.Algorithms.ExactTriangle.queryCap 2 1)
          (C rho - k * Cslib.Algorithms.ExactTriangle.queryCap 2 1)) at hdesc
  have first := hdesc 0 (by decide) 0 (by rw [hQ, hc0]; decide)
  have last := hdesc 2 (by decide) 0 (by rw [hQ, hc2]; decide)
  obtain ⟨t, ht, he⟩ := hy
  have hRun := he.runs (pc := 0) (p := Catalogue.program.program ChunkCatalogue.written)
    (Program.Contains.self _).append_left
  have hcost : Catalogue.cost 2 1 3 = 860 := by
    norm_num [Catalogue.cost, hQ, Cslib.Algorithms.ExactTriangle.sOf]
  refine ⟨y, t + 1, by rw [hcost] at ht; omega, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [State.init, Nat.zero_add, Nat.add_sub_cancel] using hRun
  · simpa only [State.init, hcTotal] using he.executes ChunkCatalogue.written
  · simpa only [hB] using hlen
  · simpa only [hH] using hpieces
  · simpa only [hQ, hbefore0, Nat.reduceAdd, Nat.reduceMul] using first.1
  · simpa only [hQ, hbefore0, Nat.reduceAdd, Nat.reduceMul] using first.2.1
  · simpa only [hQ, hbefore0, hc0, Nat.reduceAdd, Nat.reduceMul,
      Nat.sub_zero, min_eq_right (by decide : 2 ≤ 4)]
      using first.2.2
  · simpa only [hQ, hbefore2, Nat.reduceAdd, Nat.reduceMul] using last.2.1
  · simpa only [hQ, hbefore2, hc2, Nat.reduceAdd, Nat.reduceMul,
      Nat.sub_zero, min_eq_right (by decide : 1 ≤ 4)]
      using last.2.2
  · exact hf 5 (Or.inl (by decide))
  · exact hf 65 (Or.inr (by simpa only [hcTotal] using (by decide : 65 ≤ 65)))

end CompleteCatalogue

end ComplexityTests.WordRAMExactTriangleResidues
