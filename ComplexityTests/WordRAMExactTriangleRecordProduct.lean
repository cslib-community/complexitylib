/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.ExactTriangle.RecordProduct.SourceBounds

/-!
# Real record-decoder prefixes at admitted positive-depth geometry

Full positive-depth multiplication is too large for a concrete VM regression: its smallest
producer middle dimension is sixteen and the thin geometry requires `n≥16^18`. These tests
execute actual descriptor/log/header code at that valid geometry, without allocating matrices
or claiming a complete producer run for the fixture. General initialized composition is
checked separately by the library execution theorem.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMExactTriangleRecordProduct

open Cslib.WordRAM Cslib.Algorithms.WordRAM.ExactTriangle
open Cslib.Algorithms.ExactTriangle Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

private def side : ℕ := 16 ^ 18
private def area : ℕ := side * 16
private def stride : ℕ := 6 + 2 * area
private def record : ℕ := 100 + stride
private def heap : ℕ := 100 + 2 * stride

private def fixture : Data 320 :=
  { regs := fun i => if i.val = 39 then 100 else if i.val = 42 then heap
      else if i.val = 64 then 1 else 73
    mem := fun a => if a = 1 then 16 else if a = 3 then side
      else if record ≤ a && a < record + 6 then
        [3, 1, 50, 2, record + 6, record + 6 + area].getD (a - record) 0
      else if a = 50 then side - 1 else if a = 51 then 7
      else if a = 52 then 8 else if a = 53 then side - 2 else 0 }

private def decodePrefix : Code .standard 320 :=
  .seq RecordProduct.readRecord (.seq RecordProduct.logarithm RecordProduct.writeHeader)

private def observe : Option (List ℕ × List ℕ × Bool × ℕ) :=
  (decodePrefix.eval 32768 512 fixture).map fun (y, steps) =>
    ((List.range 5).map (fun i => y.mem (heap + i)),
      (List.range 4).map (fun i => y.mem (50 + i)),
      decide (∀ i : Fin 64, y.regs (RecordProduct.producerBank i) =
        fixture.regs (RecordProduct.producerBank i)), steps)

-- Actual nonzero ordinal selects the second six-word record, recovers m=2 and writes L=38.
#guard observe == some ([4 + 2 * area + 4, 38, 2, side, 2],
  [side - 1, 7, 8, side - 2], true, 64)

-- Geometry is fully admitted; the smaller tempting VM dimension would violate it.
#guard side ≥ 16 ^ 18
#guard ¬(16 ≥ 16 ^ 18)

-- Actual source words are not doubled by the adapter's copy routine.
private def copyFixture : Data 320 :=
  { regs := fun i => if i.val = 96 then 10 else if i.val = 97 then 30
      else if i.val = 98 then 2 else 91
    mem := fun a => if a = 10 then 1 else if a = 11 then 0 else 77 }

#guard (RecordProduct.copy.eval 16 8 copyFixture).map (fun (y, steps) =>
    (y.mem 30, y.mem 31, y.mem 29, y.mem 32, y.regs 39, steps)) ==
  some (1, 0, 77, 77, 91, 18)

private def zeroWeights (n : ℕ) : List ℤ := List.replicate (3 * (n * n)) 0
private def physicalWidth (n : ℕ) : ℕ := RecordProduct.admissionWidth n (D 2) 1 3 0

/-- A fully admitted, nonempty producer→adapter run at positive inner depth. The list is kept
symbolic: this kernel proof uses the general actual execution theorem, not VM enumeration of
the enormous matrix family. Its observed answer and charged halt use the same final memory. -/
private theorem initialized_zero (N : ℕ) (hgeo : D 2 ^ 18 ≤ N) :
    ∃ a : Data 64, ∃ idx : InstanceIndex 3, ∃ y : Data 320, ∃ steps : ℕ,
    Runs (physicalWidth N) (RecordProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input N (D 2) 1 3 (zeroWeights N)))
      ⟨RecordProduct.entryProgram.size, y⟩ steps ∧
    Executes (physicalWidth N) (RecordProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input N (D 2) 1 3 (zeroWeights N)))
      (y.regs RecordProduct.Reg.result) (steps + 1) ∧
    let qs := RecordProduct.decodedQueries
      ((Nat.pow_pos (by decide : 0 < D 2) (n := 18)).trans_le hgeo) a.mem
      (RecordProduct.recordQueries N (D 2) 3 idx)
      (RecordProduct.recordQueryCount N (D 2) 3 (fun q => (zeroWeights N).getD q 0) idx)
    ∃ first : Fin qs.length,
      y.mem (y.regs RecordProduct.Reg.result) = Signed.encode
        ((RecordProduct.leftMatrix 2 N 1 3 (fun q => (zeroWeights N).getD q 0) idx *
          RecordProduct.rightMatrix 2 N 1 3 (fun q => (zeroWeights N).getD q 0) idx)
            (qs.get first).1 (qs.get first).2) := by
  have hv : ∀ z ∈ (zeroWeights N), z.natAbs ≤ 0 := by
    intro z hz
    have he : z = 0 := List.eq_of_mem_replicate hz
    subst z
    decide
  obtain ⟨hi, a, idx, ha, hidx, hord, y, steps, ht, hr, he, hb, yr, hvals, hf, hg, hQ⟩ :=
    RecordProduct.runs_input (m := 2) (n := N) (g := 1) (p := 3) (A := 0)
      (W := (physicalWidth N)) (zeroWeights N) (by simp [zeroWeights])
      (by decide) (by decide) (by decide) hgeo hv le_rfl
  have hpos := RecordProduct.recordQueryCount_pos (n := N) (D := D 2) (g := 1) (p := 3)
    (fun q => (zeroWeights N).getD q 0)
    (by decide : (3 : ℕ) ≠ 0) (by decide : 1 ≤ D 2)
    ((Nat.le_self_pow (by decide : 18 ≠ 0) (D 2)).trans hgeo) idx hidx
  let qs := RecordProduct.decodedQueries
      ((Nat.pow_pos (by decide : 0 < D 2) (n := 18)).trans_le hgeo) a.mem
    (RecordProduct.recordQueries N (D 2) 3 idx)
    (RecordProduct.recordQueryCount N (D 2) 3 (fun q => (zeroWeights N).getD q 0) idx)
  have hlen : 0 < qs.length := by rw [RecordProduct.decodedQueries_length]; exact hpos
  let first : Fin qs.length := ⟨0, hlen⟩
  have hv0 := hvals first
  refine ⟨a, idx, y, steps, hr, ?_, first, ?_⟩
  · simpa only [yr] using he
  · simpa only [first, Fin.val_mk, Nat.add_zero, ← yr] using hv0

example : ∃ a : Data 64, ∃ idx : InstanceIndex 3, ∃ y : Data 320, ∃ steps : ℕ,
    Runs (physicalWidth side) (RecordProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input side (D 2) 1 3 (zeroWeights side)))
      ⟨RecordProduct.entryProgram.size, y⟩ steps ∧
    Executes (physicalWidth side) (RecordProduct.entryProgram.program RecordProduct.Reg.result)
      (State.init (PreparationInput.input side (D 2) 1 3 (zeroWeights side)))
      (y.regs RecordProduct.Reg.result) (steps + 1) ∧
    let qs := RecordProduct.decodedQueries (by dsimp [side]; positivity : 0 < side) a.mem
      (RecordProduct.recordQueries side (D 2) 3 idx)
      (RecordProduct.recordQueryCount side (D 2) 3 (fun q => (zeroWeights side).getD q 0) idx)
    ∃ first : Fin qs.length,
      y.mem (y.regs RecordProduct.Reg.result) = Signed.encode
        ((RecordProduct.leftMatrix 2 side 1 3 (fun q => (zeroWeights side).getD q 0) idx *
          RecordProduct.rightMatrix 2 side 1 3 (fun q => (zeroWeights side).getD q 0) idx)
            (qs.get first).1 (qs.get first).2) := initialized_zero side le_rfl

end ComplexityTests.WordRAMExactTriangleRecordProduct
