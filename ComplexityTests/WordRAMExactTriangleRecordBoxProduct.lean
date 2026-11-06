/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.RecordBoxProduct

/-!
# Actual threshold patch and positive-block producer-to-box execution

The VM fixture executes the real descriptor/log/header/threshold prefix with a
nonzero ordinal at valid `m=9`, `N=D^18` geometry, without allocating its matrices.
The separate kernel client runs the actual original-input producer and complete
new record consumer symbolically at that positive block. Its exact answer and
finite charged bound refer to the same pre-halt state and final halt.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleRecordBoxProduct

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.ExactTriangle Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

private def side : ℕ := (D 9) ^ 18
private def area : ℕ := side * D 9
private def stride : ℕ := 6 + 2 * area
private def record : ℕ := 100 + stride
private def heap : ℕ := 100 + 2 * stride

private def fixture : Data 320 :=
  { regs := fun i => if i.val = 39 then 100 else if i.val = 42 then heap
      else if i.val = 64 then 1 else 73
    mem := fun a => if a = 1 then D 9 else if a = 3 then side
      else if record ≤ a && a < record + 6 then
        [3, 1, 50, 2, record + 6, record + 6 + area].getD (a - record) 0
      else if a = 50 then side - 1 else if a = 51 then 7
      else if a = 52 then 8 else if a = 53 then side - 2 else 0 }

private def decodePrefix : Code .standard 320 :=
  .seq (.seq RecordProduct.readRecord
    (.seq RecordProduct.logarithm RecordProduct.writeHeader)) RecordBoxProduct.patchInput

private def observe : Option (List ℕ × List ℕ × Bool × ℕ) :=
  (decodePrefix.eval 32768 512 fixture).map fun (y, steps) =>
    ((List.range 5).map (fun i => y.mem (heap + i)) ++
        [y.mem (heap + 5 + 2 * area + 4)],
      (List.range 4).map (fun i => y.mem (50 + i)),
      decide (∀ i : Fin 64, y.regs (RecordProduct.producerBank i) =
        fixture.regs (RecordProduct.producerBank i)), steps)

-- Actual second record, recovered m=9, level189, new payload length and nonzero threshold1.
#guard observe == some ([5 + 2 * area + 4, 189, 9, side, 2, 1],
  [side - 1, 7, 8, side - 2], true, 136)

-- Geometry is fully admitted; the smaller tempting VM dimension would violate it.
#guard side ≥ (D 9) ^ 18
#guard ¬(D 9 ≥ (D 9) ^ 18)

private def zeroWeights (n : ℕ) : List ℤ := List.replicate (3 * (n * n)) 0
private def physicalWidth (k n : ℕ) : ℕ :=
  RecordProduct.admissionWidth n (D (9 * k)) 1 3 0

/-- A fully admitted, nonempty producer→adapter run at positive inner depth. The list is kept
symbolic: this kernel proof uses the general actual execution theorem, not VM enumeration of
the enormous matrix family. Its observed answer and charged halt use the same final memory. -/
private theorem initialized_zero (k N : ℕ) (hk : 1 ≤ k)
    (hgeo : D (9 * k) ^ 18 ≤ N) :
    ∃ a : Data 64, ∃ idx : InstanceIndex 3, ∃ y : Data 320, ∃ steps : ℕ,
    Runs (physicalWidth k N) (RecordBoxProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input N (D (9 * k)) 1 3 (zeroWeights N)))
      ⟨RecordBoxProduct.entryProgram.size, y⟩ steps ∧
    Executes (physicalWidth k N) (RecordBoxProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input N (D (9 * k)) 1 3 (zeroWeights N)))
      (y.regs RecordProduct.Reg.result) (steps + 1) ∧
    let qs := RecordProduct.decodedQueries
      ((Nat.pow_pos (Nat.pow_pos (by decide : 0 < (4 : ℕ))) (n := 18)).trans_le hgeo) a.mem
      (RecordProduct.recordQueries N (D (9 * k)) 3 idx)
      (RecordProduct.recordQueryCount N (D (9 * k)) 3 (fun q => (zeroWeights N).getD q 0) idx)
    ((steps + 1 : ℕ) : ℝ) ≤ RecordProduct.preparationTime N (D (9 * k)) 1 3 (zeroWeights N) +
      31457280 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
        (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (N : ℝ) ^ 2 ∧
    ∃ first : Fin qs.length,
      y.mem (y.regs RecordProduct.Reg.result) = Signed.encode
        ((RecordProduct.leftMatrix (9 * k) N 1 3 (fun q => (zeroWeights N).getD q 0) idx *
          RecordProduct.rightMatrix (9 * k) N 1 3 (fun q => (zeroWeights N).getD q 0) idx)
            (qs.get first).1 (qs.get first).2) := by
  have hposD : 0 < D (9 * k) := Nat.pow_pos (by decide : 0 < (4 : ℕ))
  have hlargeD : 16 ≤ D (9 * k) := by
    change 4 ^ 2 ≤ 4 ^ (9 * k)
    exact Nat.pow_le_pow_right (by decide) (by omega)
  have hv : ∀ z ∈ (zeroWeights N), z.natAbs ≤ 0 := by
    intro z hz
    have he : z = 0 := List.eq_of_mem_replicate hz
    subst z
    decide
  obtain ⟨hi, a, idx, ha, hidx, hord, y, steps, ht, hr, he, hb, yr, hvals, hf, hg, hQ⟩ :=
    RecordBoxProduct.runs_input (m := 9 * k) (n := N) (g := 1) (p := 3) (A := 0)
      (W := (physicalWidth k N)) (zeroWeights N) (by simp [zeroWeights])
      hlargeD (by decide) (by decide) hgeo hv le_rfl
  have hpos := RecordProduct.recordQueryCount_pos (n := N) (D := D (9 * k)) (g := 1) (p := 3)
    (fun q => (zeroWeights N).getD q 0)
    (by decide : (3 : ℕ) ≠ 0) hposD
    ((Nat.le_self_pow (by decide : 18 ≠ 0) (D (9 * k))).trans hgeo) idx hidx
  let qs := RecordProduct.decodedQueries
      ((Nat.pow_pos (Nat.pow_pos (by decide : 0 < (4 : ℕ))) (n := 18)).trans_le hgeo) a.mem
    (RecordProduct.recordQueries N (D (9 * k)) 3 idx)
    (RecordProduct.recordQueryCount N (D (9 * k)) 3 (fun q => (zeroWeights N).getD q 0) idx)
  have hlen : 0 < qs.length := by rw [RecordProduct.decodedQueries_length]; exact hpos
  let first : Fin qs.length := ⟨0, hlen⟩
  have hv0 := hvals first
  have hthin : ((RecordBoxProduct.timeBound (m := 9 * k) qs + 1 : ℕ) : ℝ) ≤
      31457280 * ((189 * k + 1 : ℕ) : ℝ) ^ 2 * ((9 * k + 1 : ℕ) : ℝ) *
        (D (9 * k) : ℝ) ^ (-(8 / 125 : ℝ)) * (N : ℝ) ^ 2 := by
    exact RecordBoxProduct.thin_timeBound (k := k) qs hgeo hQ
  have hsteps : ((steps + 1 : ℕ) : ℝ) ≤
      RecordProduct.preparationTime N (D (9 * k)) 1 3 (zeroWeights N) +
        ((RecordBoxProduct.timeBound (m := 9 * k) qs + 1 : ℕ) : ℝ) := by exact_mod_cast ht
  refine ⟨a, idx, y, steps, hr, ?_, hsteps.trans (add_le_add le_rfl hthin), first, ?_⟩
  · exact Eq.mpr (congrArg (fun ret =>
      Executes (physicalWidth k N)
        (RecordBoxProduct.entryProgram.program RecordProduct.Reg.result)
        (State.init (PreparationInput.input N (D (9 * k)) 1 3 (zeroWeights N)))
        ret (steps + 1)) yr) he
  · have hvalue : y.mem
        (a.regs Instances.heap +
          QueriedProduct.outputBase (21 * (9 * k)) (9 * k) N qs.length) =
        Signed.encode ((RecordProduct.leftMatrix (9 * k) N 1 3
          (fun q => (zeroWeights N).getD q 0) idx *
          RecordProduct.rightMatrix (9 * k) N 1 3 (fun q => (zeroWeights N).getD q 0) idx)
            (qs.get first).1 (qs.get first).2) := by
      simpa only [first, Fin.val_mk, Nat.add_zero] using hv0
    exact (congrArg y.mem yr).trans hvalue

example : ∃ a : Data 64, ∃ idx : InstanceIndex 3, ∃ y : Data 320, ∃ steps : ℕ,
    Runs (physicalWidth 1 side) (RecordBoxProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input side (D 9) 1 3 (zeroWeights side)))
      ⟨RecordBoxProduct.entryProgram.size, y⟩ steps ∧
    Executes (physicalWidth 1 side) (RecordBoxProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input side (D 9) 1 3 (zeroWeights side)))
      (y.regs RecordProduct.Reg.result) (steps + 1) ∧
    let qs := RecordProduct.decodedQueries
      (by change 0 < D 9 ^ 18; exact Nat.pow_pos (by norm_num [D] : 0 < D 9)) a.mem
      (RecordProduct.recordQueries side (D 9) 3 idx)
      (RecordProduct.recordQueryCount side (D 9) 3 (fun q => (zeroWeights side).getD q 0) idx)
    ((steps + 1 : ℕ) : ℝ) ≤
      RecordProduct.preparationTime side (D 9) 1 3 (zeroWeights side) +
        31457280 * (190 : ℝ) ^ 2 * 10 * (D 9 : ℝ) ^ (-(8 / 125 : ℝ)) * (side : ℝ) ^ 2 ∧
    ∃ first : Fin qs.length,
      y.mem (y.regs RecordProduct.Reg.result) = Signed.encode
        ((RecordProduct.leftMatrix 9 side 1 3 (fun q => (zeroWeights side).getD q 0) idx *
          RecordProduct.rightMatrix 9 side 1 3 (fun q => (zeroWeights side).getD q 0) idx)
            (qs.get first).1 (qs.get first).2) := initialized_zero 1 side le_rfl le_rfl

end ComplexityTests.WordRAMExactTriangleRecordBoxProduct
