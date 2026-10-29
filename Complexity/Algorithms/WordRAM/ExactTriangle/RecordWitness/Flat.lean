/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordWitness.Entry

/-!
# Actual initialized flat witness-recovery runs

One fixed standard unsigned program starts from the original input, computes the actual first
record's product and verifies its accepted pairs. The same actual state witnesses the prefix
run, final charged halt, original-coordinate result, false-positive accounting and caller frame.
This is a per-record endpoint; choosing parameters and the outer ET record loop remain separate.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness

open Cslib.WordRAM Cslib.Matrix Cslib.Algorithms.ExactTriangle
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- The complete initialized standard-native program uses 400 fixed registers, at most
133120 flat instruction slots including halt, and never inspects physical word width. -/
theorem entryProgram_fixed : (entryProgram.program Reg.found).length ≤ 133120 ∧
    ¬(entryProgram.program Reg.found).ReadsWidth := by
  constructor
  · simp only [Code.program, List.length_append, Code.length_assemble,
      List.length_singleton, entryProgram, Code.size, produce, RecordProduct.produce,
      program, Code.size_rename]
    have hc := RecordProduct.program_fixed.1
    have hp := Instances.program_fixed.1
    have hs := consume_fixed.1
    omega
  · apply Code.not_readsWidth_program
    simp only [entryProgram, Code.ReadsWidth, produce, RecordProduct.produce,
      Code.readsWidth_rename, Op.ReadsWidth, false_or, program]
    exact not_or.mpr ⟨Instances.program_fixed.2,
      not_or.mpr ⟨RecordProduct.program_fixed.2, consume_fixed.2⟩⟩

/-- Every sufficiently wide physical word size executes the actual original-input program.
Returned success is exactly an original zero in this actual selected chunk/piece, and every
returned coordinate belongs to that original witness. The instruction bound includes halt. -/
theorem runs_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : p ∈ Nat.sqrtPrimeWindow (D m)) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    let V := fun q => values.getD q 0
    let wAB := fun a b : Fin n => V (pairIndex (a, b))
    let wBC := fun b c : Fin n => V (n * n + pairIndex (b, c))
    let wAC := fun a c : Fin n => V (2 * (n * n) + pairIndex (a, c))
    InputFits W (PreparationInput.input n (D m) g p values) ∧
    ∃ a : Data 64, ∃ idx : InstanceIndex p,
      ExecWithin W Instances.program (.init (PreparationInput.input n (D m) g p values)) a
        (RecordProduct.preparationTime n (D m) g p values - 1) ∧
      Instances.Output n (D m) g p V (.init (PreparationInput.input n (D m) g p values)) a ∧
      idx ∈ instanceIndices wAB (D m) g p ∧
      RecordProduct.recordOrdinal n (D m) g p V idx = 0 ∧
      let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
        ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
      let Q := RecordProduct.recordQueryCount n (D m) p V idx
      let qs := RecordProduct.decodedQueries hn a.mem (RecordProduct.recordQueries n (D m) p idx) Q
      let length := min (pieceSize (D m) g) (n - idx.2.2 * pieceSize (D m) g)
      ∃ y t S, t + 1 ≤ RecordProduct.preparationTime n (D m) g p values +
          RecordProduct.timeBound (m := m) qs + 5 * Nat.sqrt (D m) + 8 * Q +
          (42 * length + 28) * S + 53 ∧
        Runs W (entryProgram.program Reg.found)
          (State.init (PreparationInput.input n (D m) g p values)) ⟨entryProgram.size, y⟩ t ∧
        Executes W (entryProgram.program Reg.found)
          (State.init (PreparationInput.input n (D m) g p values)) (y.regs Reg.found) (t + 1) ∧
        y.Bounded W ∧ y.regs Reg.scans = S ∧
        (y.regs Reg.found = 0 ∨ y.regs Reg.found = 1) ∧
        S ≤ falsePositiveCount wAB wBC wAC p + y.regs Reg.found ∧
        (y.regs Reg.found = 1 ↔
          ∃ q ∈ chunkOf wAB (D m) p idx.1 idx.2.1,
            ∃ c ∈ piece n (D m) g idx.2.2, weightSum wAB wBC wAC q.1 q.2 c = 0) ∧
        (y.regs Reg.found = 1 → ∃ u v c : Fin n,
          y.regs Reg.witnessA = u.val ∧ y.regs Reg.witnessB = v.val ∧
          y.regs Reg.witnessC = c.val ∧ (u, v) ∈ chunkOf wAB (D m) p idx.1 idx.2.1 ∧
          c ∈ piece n (D m) g idx.2.2 ∧ weightSum wAB wBC wAC u v c = 0) ∧
        (∀ u, u < a.regs Instances.heap ∨
          a.regs Instances.heap + CallableProduct.windowSize n Q ≤ u → y.mem u = a.mem u) ∧
        ∀ j : Fin 64, y.regs (productBank (RecordProduct.producerBank j)) = a.regs j := by
  have htwo : 2 ≤ W := by unfold admissionWidth at hW; omega
  have heq : W - 2 + 2 = W := Nat.sub_add_cancel htwo
  have h := exec_input (w := W - 2) values hlen hD hg hp hN hv
    (by simpa only [heq] using hW)
  rw [heq] at h
  obtain ⟨hi, a, idx, ha, hout, hidx, hord, y, S, he, yb, ys, yf, hS, yiff, yw, frame, regs⟩ := h
  obtain ⟨t, ht, hex⟩ := he
  refine ⟨hi, a, idx, ha, hout, hidx, hord, y, t, S, by omega,
    ?_, ?_, yb, ys, yf, hS, yiff, yw, frame, regs⟩
  · simpa only [Nat.zero_add, State.init] using hex.runs (pc := 0)
      (p := entryProgram.program Reg.found) (Program.Contains.self _).append_left
  · simpa only [State.init] using hex.executes Reg.found

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordWitness
