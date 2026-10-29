/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.Entry

/-!
# Initialized flat native producer and product runs

The original four scalar headers and three signed weight arrays initialize one fixed native
program. Prefix `Runs`, the charged final halt, exact answer words and the caller frame all
refer to the same actual final data. The initialized client selects the first actual record;
the caller interface `exec_of_output` supports every occupied ordinal.
-/

public section

namespace Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct

open Cslib.WordRAM Cslib.Algorithms.ExactTriangle Cslib.Matrix
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

/-- Fixed register count, instruction bound including halt, and physical-width independence. -/
theorem entryProgram_fixed : (entryProgram.program Reg.result).length ≤ 132352 ∧
    ¬(entryProgram.program Reg.result).ReadsWidth := by
  constructor
  · simp only [Code.program, List.length_append, Code.length_assemble,
      List.length_singleton, entryProgram, Code.size, produce, Code.size_rename]
    have hc := program_fixed.1
    have hp := Instances.program_fixed.1
    omega
  · apply Code.not_readsWidth_program
    simp only [entryProgram, Code.ReadsWidth, produce, Code.readsWidth_rename, Op.ReadsWidth,
      false_or]
    exact not_or.mpr ⟨Instances.program_fixed.2, program_fixed.2⟩

/-- Every sufficiently wide physical execution starts from the actual original input and
returns the first prepared record's exact requested product values. There is no supplied
layout, run, time, sparse-count or solver certificate. Source prime selection and the outer
instance loop are separate; this theorem alone is not an aggregate ExactTriangle bound. -/
theorem runs_input {W m n g p A : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W) :
    InputFits W (PreparationInput.input n (D m) g p values) ∧
    let hn : 0 < n := lt_of_lt_of_le (by omega : 0 < D m)
      ((Nat.le_self_pow (by decide : 18 ≠ 0) (D m)).trans hN)
    ∃ a : Data 64, ∃ idx : InstanceIndex p,
      ExecWithin W Instances.program (.init (PreparationInput.input n (D m) g p values)) a
        (preparationTime n (D m) g p values - 1) ∧
      idx ∈ instanceIndices (fun a b : Fin n => values.getD (pairIndex (a, b)) 0) (D m) g p ∧
      recordOrdinal n (D m) g p (fun q => values.getD q 0) idx = 0 ∧
      let qs := decodedQueries hn a.mem (recordQueries n (D m) p idx)
        (recordQueryCount n (D m) p (fun q => values.getD q 0) idx)
      ∃ y t, t + 1 ≤ preparationTime n (D m) g p values + timeBound (m := m) qs + 1 ∧
        Runs W (entryProgram.program Reg.result)
          (State.init (PreparationInput.input n (D m) g p values)) ⟨entryProgram.size, y⟩ t ∧
        Executes W (entryProgram.program Reg.result)
          (State.init (PreparationInput.input n (D m) g p values))
          (a.regs Instances.heap + QueriedProduct.outputBase (19 * m) m n qs.length) (t + 1) ∧
        y.Bounded W ∧
        y.regs Reg.result = a.regs Instances.heap +
          QueriedProduct.outputBase (19 * m) m n qs.length ∧
        (∀ j : Fin qs.length,
          y.mem (a.regs Instances.heap +
            (QueriedProduct.outputBase (19 * m) m n qs.length + j.val)) =
            Signed.encode ((leftMatrix m n g p (fun q => values.getD q 0) idx *
              rightMatrix m n g p (fun q => values.getD q 0) idx) (qs.get j).1 (qs.get j).2)) ∧
        (∀ u, u < a.regs Instances.heap ∨
          a.regs Instances.heap + CallableProduct.windowSize n qs.length ≤ u →
          y.mem u = a.mem u) ∧
        (∀ j : Fin 64, y.regs (producerBank j) = a.regs j) ∧ qs.length * 2 ^ m ≤ n ^ 2 := by
  obtain ⟨hi, a, idx, ha, hidx, hord, y, hy, yr, yv, yf, yg, hQ⟩ :=
    exec_input values hlen hD hg hp hN hv hW
  have ybound := hy.bounded (Data.Bounded.init hi)
  obtain ⟨t, ht, he⟩ := hy
  refine ⟨hi, a, idx, ha, hidx, hord, y, t, by omega, ?_, ?_, ybound, yr, yv, yf, yg, hQ⟩
  · simpa only [Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := entryProgram.program Reg.result) (Program.Contains.self _).append_left
  · simpa only [yr, State.init] using he.executes Reg.result

/-- Every native prefix is physically word-bounded from the actual admitted original input.
In particular this includes dirty loads before the callable compiler's remainder instruction. -/
theorem bounded_reachable {W m n g p A k : ℕ} (values : List ℤ)
    (hlen : values.length = 3 * (n * n)) (hD : 16 ≤ D m)
    (hg : 1 ≤ g) (hp : 0 < p) (hN : D m ^ 18 ≤ n)
    (hv : ∀ z ∈ values, z.natAbs ≤ A) (hW : admissionWidth n (D m) g p A ≤ W)
    {s : State 320} (hr : Runs W (entryProgram.program Reg.result)
      (State.init (PreparationInput.input n (D m) g p values)) s k) : s.data.Bounded W := by
  have hi := (exec_input values hlen hD hg hp hN hv hW).1
  exact hr.bounded_init hi

end Cslib.Algorithms.WordRAM.ExactTriangle.RecordProduct
