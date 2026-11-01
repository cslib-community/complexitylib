/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Input
public import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Lookup

/-!
# Initialized flat box-table construction and actual lookup

One fixed 64-register program computes the shared catalogue and a complete tile from
the original arrays. The exact pre-halt state is the same witness used for all table
readbacks and the charged final halt. Physical admission is an original-input logarithm.
The lookup theorem remains separately callable, so geometry is not rebuilt per query.
-/

public section

namespace Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

open Cslib.WordRAM Cslib.Algorithms.MatrixMultiplication.Schonhage

/-- The standard compiler gives a real initialized prefix and charged halt with the same data. -/
theorem runs_wide {W L m t A B : ℕ} (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hW : admissionWidth L m t A B ≤ W) :
    InputFits W (input L m t a b) ∧
    ∃ y n, n + 1 ≤ timeBound L m t ∧
      Runs W (program.program Reg.values) (State.init (input L m t a b))
        ⟨program.size, y⟩ n ∧
      Executes W (program.program Reg.values) (State.init (input L m t a b))
        (valueBase L m t) (n + 1) ∧ y.Bounded W ∧
      y.regs Reg.levels = L ∧ y.regs Reg.height = m - t ∧
      y.regs Reg.span = 10 ^ L ∧ y.regs Reg.directory = directoryBase L ∧
      y.regs Reg.values = valueBase L m t ∧
      y.regs Reg.count = (boxes L m t).card ∧
      (∀ s < (m - t + 1) * 10 ^ L,
        y.mem (directoryBase L + s) = directoryWord L (m - t) s) ∧
      (∀ s < (m - t + 1) * 10 ^ L, Eligible L (m - t) s →
        y.mem (valueBase L m t + Nat.count (Eligible L (m - t)) s) =
          Signed.encode (slotValue (fun τ => a (Encoding.leafIndex τ))
            (fun τ => b (Encoding.leafIndex τ)) s)) ∧
      (∀ q, ¬(directoryBase L ≤ q ∧ q < memoryEnd L m t) →
        y.mem q = (State.init (input L m t a b) : State registers).data.mem q) := by
  obtain ⟨hw, haddr, hmag⟩ := admission_bounds hW
  have hwidth : W - 2 + 2 = W := by unfold admissionWidth at hW; omega
  obtain ⟨hi, y, ⟨n, hn, he⟩, hy, hL, hH, hT, hD, hV, hK, hd, hv, hf⟩ :=
    exec_input a b ha hb (by simpa only [hwidth] using haddr) hmag
  refine ⟨by simpa only [hwidth] using hi, y, n, ?_, ?_, ?_,
    by simpa only [hwidth] using hy, hL, hH, hT, hD, hV, hK, hd, hv, hf⟩
  · have ht : 0 < timeBound L m t := by unfold timeBound; omega
    omega
  · simpa only [hwidth, Nat.zero_add, State.init] using he.runs (pc := 0)
      (p := program.program Reg.values) (Program.Contains.self _).append_left
  · simpa only [hwidth, hV, State.init] using he.executes Reg.values

/-- Every reachable initialized prefix has fitting native words under the same admission. -/
theorem bounded_reachable {W L m t A B n : ℕ} (a b : Fin (10 ^ L) → ℤ)
    (ha : ∀ i, (a i).natAbs ≤ A) (hb : ∀ i, (b i).natAbs ≤ B)
    (hW : admissionWidth L m t A B ≤ W) {y : State registers}
    (hy : Runs W (program.program Reg.values) (State.init (input L m t a b)) y n) :
    y.data.Bounded W := by
  have hi := (runs_wide a b ha hb hW).1
  exact hy.bounded_init hi

end Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable
