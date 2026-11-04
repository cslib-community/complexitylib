/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable.Flat

/-!
Actual native constructor/lookup regressions. These execute code from State.init and
check observable words, including dirty scratch and invalid directory slots. They do
not replace the general execution, finite-meaning, frame or resource proofs.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMSchonhageBoxTable

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxTable

private def a (u : LeftStr 1) : ℤ :=
  match u 0 with
  | .x i => ![1, 2, -1] i
  | .p i j => !![-3, 2; 0, 5] i j

private def b (u : RightStr 1) : ℤ :=
  match u 0 with
  | .y j => ![3, -2, 1] j
  | .q i j => !![2, -1; 4, 0] i j

private def leftValues (i : Fin 10) : ℤ := encodeLeft (fun _ : Fin 1 =>
  Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.termDigits i) a

private def rightValues (i : Fin 10) : ℤ := encodeRight (fun _ : Fin 1 =>
  Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.termDigits i) b

-- The only depth-zero cube is a fully fixed empty leaf; both signed reads are real.
#guard match program.eval 12 100 ((State.init (input 0 0 0 (fun _ => 2) (fun _ => -3))).data) with
  | some (y, _) => y.regs Reg.count == 1 && y.mem (y.regs Reg.values) == encode (-6)
  | none => false

-- Complete memoized construction, with one shared starred box after ten fixed leaves.
private def signedState : Data registers :=
  let x := (State.init (input 1 1 0 leftValues rightValues) : State registers).data
  { x with mem := fun a => if 24 ≤ a ∧ a < 88 then 99 else if a = 88 then 777 else x.mem a }

#guard match program.eval 16 10000 signedState with
  | some (y, _) => y.regs Reg.count == 11 && y.regs Reg.values == 77 &&
      y.mem 86 == encode (-4) && y.mem 87 == encode (-8) && y.mem 88 == 777 &&
      (List.range 24).all (fun a => y.mem a == signedState.mem a) &&
      (List.range 9).all (fun i => y.mem (34 + i) == 0)
  | none => false

private def request : Code .standard registers :=
  .seq program (.seq (ram[ Reg.cube ← #100 ]) lookup)

private def queryState (digits : List ℕ) : Data registers :=
  { signedState with mem := fun a =>
      if 100 ≤ a then digits[a - 100]?.getD 0 else signedState.mem a }

-- Real lookup reads the computed compact table, including the digit-nine child of the sum.
#guard match request.eval 16 10000 (queryState [10]) with
  | some (y, _) => y.regs Reg.found == 1 && y.regs Reg.answer == encode (-8) && y.mem 88 == 777
  | none => false

-- Out-of-alphabet words are rejected by actual code before digit multiplication.
#guard match request.eval 16 10000 (queryState [999]) with
  | some (y, _) => y.regs Reg.found == 0 && y.regs Reg.answer == 0
  | none => false

-- At threshold m, only the nine non-P0 fixed leaves remain; a star is rejected.
#guard match program.eval 16 10000
    ((State.init (input 1 1 1 leftValues rightValues)).data) with
  | some (y, _) => y.regs Reg.count == 9 && y.regs Reg.values == 61 && y.mem 33 == 0
  | none => false

#guard match request.eval 16 10000 ((queryState [10]).write 3 1) with
  | some (y, _) => y.regs Reg.found == 0 && y.regs Reg.answer == 0
  | none => false

private def depthTwoState (digits : List ℕ) : Data registers :=
  let x := (State.init (input 2 2 0 (fun _ => 1) (fun _ => 1)) : State registers).data
  { x with mem := fun p => if 204 ≤ p ∧ p < 984 then 99 else
      if p = 1050 then 777 else if 1100 ≤ p then digits[p - 1100]?.getD 0 else x.mem p }

private def depthTwoRequest : Code .standard registers :=
  .seq program (.seq (ram[ Reg.cube ← #1100 ]) lookup)

-- Both star layers use real earlier ranks; the full two-star cube sums 100 leaf products.
#guard match depthTwoRequest.eval 20 10000 (depthTwoState [10, 10]) with
  | some (y, _) => y.regs Reg.count == 120 && y.regs Reg.values == 864 &&
      y.regs Reg.found == 1 && y.regs Reg.answer == encode 100 && y.mem 1050 == 777
  | none => false

#guard match depthTwoRequest.eval 20 10000 (depthTwoState [10, 9]) with
  | some (y, _) => y.regs Reg.found == 1 && y.regs Reg.answer == encode 10
  | none => false

-- Reversing those symbols puts a fixed P0 below a star and is not a canonical box.
#guard match depthTwoRequest.eval 20 10000 (depthTwoState [9, 10]) with
  | some (y, _) => y.regs Reg.found == 0 && y.regs Reg.answer == 0 && y.mem 1050 == 777
  | none => false

-- Fully admitted compilation client: the observed word belongs to the same native
-- pre-halt witness as the initialized prefix and charged halt.
example : ∃ y n,
    Runs 20 (program.program Reg.values) (State.init (input 0 0 0 (fun _ => 2) (fun _ => -3)))
      ⟨program.size, y⟩ n ∧
    Executes 20 (program.program Reg.values)
      (State.init (input 0 0 0 (fun _ => 2) (fun _ => -3))) (valueBase 0 0 0) (n + 1) ∧
    n + 1 ≤ timeBound 0 0 0 ∧ y.mem (y.regs Reg.values) = encode (-6) := by
  obtain ⟨_, y, n, hn, hr, he, _, _, _, _, _, hV, _, _, hvalues, _⟩ :=
    runs_wide (A := 2) (B := 3) (fun _ : Fin 1 => (2 : ℤ)) (fun _ => (-3 : ℤ))
      (by decide) (by decide) (by decide : admissionWidth 0 0 0 2 3 ≤ 20)
  refine ⟨y, n, hr, he, hn, ?_⟩
  have hv := hvalues 0 (by decide) (by decide)
  have hvalue : slotValue (fun _ : Leaf 0 => (2 : ℤ)) (fun _ => (-3 : ℤ)) 0 = -6 :=
    by decide
  rw [hV]
  simpa only [Nat.count_zero, Nat.add_zero, hvalue] using hv

private theorem left_magnitude : ∀ i, (leftValues i).natAbs ≤ 20 := by decide
private theorem right_magnitude : ∀ i, (rightValues i).natAbs ≤ 20 := by decide

-- Positive depth has a real ten-child sum. All hypotheses of the general native
-- constructor are discharged, including the original-array bounds and width.
example : ∃ y n,
    Runs 20 (program.program Reg.values) (State.init (input 1 1 0 leftValues rightValues))
      ⟨program.size, y⟩ n ∧
    Executes 20 (program.program Reg.values) (State.init (input 1 1 0 leftValues rightValues))
      77 (n + 1) ∧ n + 1 ≤ timeBound 1 1 0 ∧
    y.regs Reg.count = 11 ∧ y.regs Reg.values = 77 ∧ y.mem 87 = encode (-8) := by
  obtain ⟨_, y, n, hn, hr, he, _, _, _, _, _, hV, hK, _, hvalues, _⟩ :=
    runs_wide leftValues rightValues left_magnitude right_magnitude
      (by decide : admissionWidth 1 1 0 20 20 ≤ 20)
  have hbase : valueBase 1 1 0 = 77 := by decide
  have hcard : (boxes 1 1 0).card = 11 := by decide
  have hv := hvalues 19 (by decide) (by decide)
  have hindex : valueBase 1 1 0 + Nat.count (Eligible 1 1) 19 = 87 := by decide
  have hvalue : slotValue
      (fun τ : Leaf 1 => leftValues
        (Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.leafIndex τ))
      (fun τ : Leaf 1 => rightValues
        (Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.leafIndex τ)) 19 = -8 :=
    by decide
  refine ⟨y, n, hr, by simpa only [hbase] using he, hn,
    hK.trans hcard, hV.trans hbase, ?_⟩
  simpa only [hindex, hvalue] using hv

private def lookupCaller (y : Data registers) : Data registers :=
  (y.set Reg.cube 100).write 100 10

-- A genuine callable lookup consumes the table produced by the same initialized
-- constructor witness. Only the new query word and its pointer are supplied by the caller.
example : ∃ y n z,
    Runs 20 (program.program Reg.values) (State.init (input 1 1 0 leftValues rightValues))
      ⟨program.size, y⟩ n ∧
    Executes 20 (program.program Reg.values) (State.init (input 1 1 0 leftValues rightValues))
      77 (n + 1) ∧
    ExecWithin 20 lookup (lookupCaller y) z 50 ∧ z.regs Reg.found = 1 ∧
      z.regs Reg.answer = encode (-8) ∧ z.mem = (lookupCaller y).mem := by
  obtain ⟨_, y, n, _, hr, he, _, yL, yH, yT, yD, yV, _, hdir, hvalues, _⟩ :=
    runs_wide leftValues rightValues left_magnitude right_magnitude
      (by decide : admissionWidth 1 1 0 20 20 ≤ 20)
  let π : Cube 1 := fun _ => .star
  let encA (τ : Leaf 1) := leftValues
    (Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.leafIndex τ)
  let encB (τ : Leaf 1) := rightValues
    (Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Encoding.leafIndex τ)
  have hbase : valueBase 1 1 0 = 77 := by decide
  have hmem (q : ℕ) (hq : q ≠ 100) : (lookupCaller y).mem q = y.mem q := by
    simp only [lookupCaller, Data.write_mem, Data.set_mem, Function.update_of_ne hq]
  obtain ⟨z, hz, hzm, hfound, hanswer, _⟩ := exec_lookup (lookupCaller y) π encA encB
    (by decide : IsBox 1 0 π)
    (by simpa [lookupCaller, Reg.levels, Reg.cube] using yL)
    (by simpa [lookupCaller, Reg.height, Reg.cube] using yH)
    (by simpa [lookupCaller, Reg.span, Reg.cube] using yT)
    (by simp [lookupCaller])
    (by simpa [lookupCaller, Reg.directory, Reg.cube, directoryBase] using yD)
    (by simpa [lookupCaller, Reg.values, Reg.cube, hbase] using yV)
    (fun i hi => by
      have hi0 : i = 0 := by omega
      subst i
      simp [lookupCaller, rawCubeDigit, cubeDigit, π])
    (fun s hs => by
      rw [hmem _ (by omega)]
      simpa [directoryBase] using hdir s hs)
    (fun s hs hv => by
      have hc : Nat.count (Eligible 1 1) s ≤ s := Nat.count_le _
      rw [hmem _ (by
        change 77 + Nat.count (Eligible 1 1) s ≠ 100
        change s < 20 at hs
        omega)]
      simpa only [hbase, encA, encB] using hvalues s hs hv)
    (by decide : Fits 20 (100 + 24 + 77 + (1 - 0 + 1) * 10 ^ 1 + 10 ^ 1 + 1 + 30))
  have hvalue : boxValue encA encB π.starLevels.card π = -8 := by decide
  exact ⟨y, n, z, hr, by simpa only [hbase] using he, hz, hfound,
    by simpa only [hvalue] using hanswer, hzm⟩

end ComplexityTests.WordRAMSchonhageBoxTable
