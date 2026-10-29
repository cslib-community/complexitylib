/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Memory
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Root
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Report
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.EmptyChild
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Finish
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Return
import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Pruned.Ready

-- Full controller regressions evaluate the actual native interpreter at elaboration time.
set_option linter.hashCommand false

/-! Actual native controller regressions, including shared and repeated query suffixes. -/

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.PrunedQuery

namespace ComplexityTests.SchonhagePruned

private def leafData : Data registers where
  regs i := match i.val with
    | 10 => 1 | 11 => 3 | 12 => 4 | 18 => 8 | 19 => 12 | 20 => 13 | 21 => 14
    | 24 => 1 | 25 => 1 | 26 => 10 | 27 => 9 | 28 => 4 | _ => 0
  mem a := if a = 3 then encode (-3) else if a = 4 then encode 2 else
    if a = 8 then 1 else if a = 10 then 1 else if a = 13 then 41 else 0

private theorem leafData_parameters : KernelRegs 0 8 3 4 leafData := by
  constructor <;> rfl

-- The general entry assertion is satisfied by concrete memory. Its timestamp directory has
-- one cell and its occupied list names the unique zero-depth query exactly once.
private theorem leafData_ready : NodeReady 0 8 3 4 0 0 0 0 {Fin.elim0} leafData := by
  refine ⟨leafData_parameters, rfl, by decide, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · intro i
    fin_cases i <;> rfl
  · change ScanMemory leafData.mem 12 14 0 1 {0}
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro q hq
      have he := Finset.mem_singleton.mp hq
      exact he ▸ (by decide : 0 < 1)
    · intro q hq
      have he : q = 0 := by omega
      subst q
      decide
    · intro q hq
      have he : q = 0 := by omega
      subst q
      decide
    · refine ⟨fun _ => 0, ?_, ?_, ?_⟩
      · change Function.Injective (fun _ : Fin 1 => (0 : ℕ))
        intro i j _
        exact Subsingleton.elim i j
      · ext q
        constructor
        · rintro ⟨i, rfl⟩
          exact Finset.mem_singleton_self _
        · intro hq
          exact ⟨⟨0, by simp⟩, (Finset.mem_singleton.mp hq).symm⟩
      · intro i
        change leafData.mem (12 + i.val) = 0
        have hi : i.val < 1 := i.isLt
        have he : i.val = 0 := by omega
        rw [he]
        rfl

-- The numerical magnitude/address hypotheses are derived from original input bounds, and the
-- value witness belongs to the same actual native execution (including the loop exit).
example : ∃ y, ExecWithin 9 controller leafData y 8194 ∧ y.mem 13 = encode (-6) := by
  let S : Finset (Cslib.Algorithms.MatrixMultiplication.Schonhage.OutStr 0) := {Fin.elim0}
  obtain ⟨y, hy, hrun⟩ := exec_ready_zero (w := 7) (A := 3) (B := 2) S
    (fun _ => -3) (fun _ => 2) leafData leafData_ready
    (by intro v; rfl) (by intro v; rfl) (by intro v; decide) (by intro v; decide)
    (by decide) (by decide) (by decide)
  have hexit : ExecWithin 9 controller y y 2 := ExecWithin.loop_exit
    (by simp only [Cond.holds_lt, hy.regs.nil_eq, hy.active_eq]; decide)
  refine ⟨y, ?_, ?_⟩
  · simpa only [traceWeight_zero, S, Finset.card_singleton] using hrun y 2 hexit
  · have hv := hy.values Fin.elim0 (Finset.mem_singleton_self _)
    simpa [Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.result,
      Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.run, Finset.piecewise, S] using hv

-- A concrete negative-product node discharges the general invariant, signed and address
-- premises. Its returned memory is attached to the same charged native loop execution.
example : ∃ y, ExecWithin 7 controller leafData y 8194 ∧ y.mem 13 = encode (-6) ∧
    y.mem 100 = 0 := by
  let S : Finset (Cslib.Algorithms.MatrixMultiplication.Schonhage.OutStr 0) := {Fin.elim0}
  obtain ⟨y, hregs, _, _, hactive, _, _, hvalue, hframe, _, hrun⟩ :=
    exec_node_zero (w := 5) (p := 0) (E := 0) (a := -3) (b := 2)
      (by decide) (by decide) (by decide) S leafData leafData_parameters
      rfl rfl rfl (by simp [leafData, S]) rfl rfl rfl rfl
      (by
        intro q hq
        have he : q = 0 := by omega
        subst q
        decide) (by decide)
  have hexit : ExecWithin 7 controller y y 2 :=
    ExecWithin.loop_exit (by simp only [Cond.holds_lt, hregs.nil_eq, hactive]; decide)
  refine ⟨y, ?_, ?_, ?_⟩
  · simpa only [traceWeight_zero, S, Finset.card_singleton] using hrun y 2 hexit
  · have hv := hvalue Fin.elim0 (Finset.mem_singleton_self _)
    simpa [Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.result,
      Cslib.Algorithms.MatrixMultiplication.Schonhage.Pruned.run,
      Finset.piecewise, S] using hv
  · exact (hframe 100 (by decide)).trans rfl

-- An empty leaf performs its real controller return without overwriting the old value cell.
example : ∃ y, ExecWithin 7 controller (leafData.write 8 0) y 47 ∧ y.mem 13 = 41 := by
  let x := leafData.write 8 0
  obtain ⟨y, hy, hmem, _, _, hactive, hreg⟩ := exec_leafStep (w := 5) (p := 0)
    (a := -3) (b := 2) (by decide) (by decide) (by decide) x
    rfl rfl rfl rfl rfl rfl rfl rfl (by decide)
  have hy0 : y.regs nil = 0 := (hreg nil (by decide)).trans rfl
  have he : ExecWithin 7 controller x y 47 := ExecWithin.loop_once
    (by decide) hy (by simp only [Cond.holds_lt, hy0, hactive]; decide)
  refine ⟨y, he, ?_⟩
  rw [hmem]
  rfl

-- Naming the reporting body and controller loop changes no native control-code tree.
example : report = ram[
    index ← #0; while index < queryCount do [
      address ← queries + index; query ← *address;
      address ← values + query; temporary ← *address;
      address ← output + index; *address ← temporary; index ← index + one ] ] := rfl

example : controller = ram[ while nil < active do [ ⟪step⟫ ] ] := rfl

-- Query codes use least-significant-first digits and retain the encoder's wildcard digit nine.
example : queryAt (L := 2) (90 : Fin 100) = ![.z 0 0, .z0] := by decide +kernel
example : (requested (L := 2) ([90, 9, 90] : List (Fin 100))).card = 2 := by decide +kernel

private def observe (w L fuel : ℕ) (a b : Fin (10 ^ L) → ℤ) (qs : List (Fin (10 ^ L))) :=
  (program.eval w fuel (State.init (input L a b qs) : State registers).data).map fun (y, time) =>
    ((List.range qs.length).map fun i => decode (y.mem (outputBase L qs.length + i)), time)

private def answers (w L fuel : ℕ) (a b : Fin (10 ^ L) → ℤ) (qs : List (Fin (10 ^ L))) :=
  (observe w L fuel a b qs).map Prod.fst

-- One leaf is multiplied once and reported twice, including its negative sign.
#guard answers 16 0 64 (fun _ => -3) (fun _ => 2) [0, 0] == some [-6, -6]
#guard answers 16 0 64 (fun _ => -3) (fun _ => 2) [] == some []

-- Digit nine is the inner wildcard; the outer query uses exactly its private leaf.
#guard answers 20 1 128 (fun i => i.val + 1) (fun _ => 1) [9, 0, 9] == some [55, 1, 55]
#guard answers 20 1 128 (fun i => -(i.val + 1 : ℤ)) (fun _ => 1) [9, 0, 9] ==
  some [-55, -1, -55]
#guard answers 20 1 128 (fun _ => 5) (fun _ => 0) [] == some []

-- The depth-two mixed-query and outside-sentinel cases now have kernel-checked actual native
-- run witnesses in SchonhagePrunedInput and SchonhagePrunedKernel, respectively. The shallow
-- interpreter checks above remain independent executable sanity checks of the code.

end ComplexityTests.SchonhagePruned
