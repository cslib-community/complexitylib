/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery.Flat

/-!
Actual native constructor/query regressions. The ordinary headers, both signed arrays,
computed geometry and real stack are executed, including the final query accumulator.
These VM examples complement the general execution and resource proofs.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMSchonhageBoxQuery

open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxQuery

#guard match program.eval 20 10000
    ((State.init (input 0 0 0 0 (fun _ => 2) (fun _ => -3))).data) with
  | some (y, _) => y.regs Reg.answer == encode (-6) && y.regs Reg.top == 0
  | none => false

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

-- At zero threshold the only visited leaf selects the single stored starred box.
#guard match program.eval 20 10000
    ((State.init (input 1 1 0 9 leftValues rightValues)).data) with
  | some (y, _) => y.regs Reg.answer == encode (-8) && y.regs Reg.top == 0
  | none => false

-- At threshold m the P0 product is low order and the nine indexed products use fixed boxes.
#guard match program.eval 20 10000
    ((State.init (input 1 1 1 9 leftValues rightValues)).data) with
  | some (y, _) => y.regs Reg.answer == encode (-8) && y.regs Reg.top == 0
  | none => false

-- Canonical depth-two table readback for a query-only threshold-zero client.
-- The full constructor remains covered above and by the general initialized theorem.
private def thresholdZeroQueryState : Data registers :=
  let x := (State.init (input 2 2 0 99 (fun _ => 1) (fun _ => 1)) : State registers).data
  let y := (((((((((x.set BoxTable.Reg.levels 2).set BoxTable.Reg.inner 2).set
    BoxTable.Reg.threshold 0).set BoxTable.Reg.span 100).set BoxTable.Reg.directory 205).set
    BoxTable.Reg.values 865).set BoxTable.Reg.arrayA 5).set BoxTable.Reg.arrayB 105).set
    BoxTable.Reg.count 120).set Reg.query 99
  { y with mem := fun p =>
      if 205 ≤ p ∧ p < 505 then BoxTable.directoryWord 2 2 (p - 205)
      else if 865 ≤ p ∧ p < 985 then encode (if p < 965 then 1 else if p < 984 then 10 else 100)
      else if 985 ≤ p ∧ p < 1500 then 99
      else if p = 2000 then 777 else x.mem p }

-- Only one complete threshold leaf is visited, without scanning all 100 leaves.
#guard match queryProgram.eval 20 1000 thresholdZeroQueryState with
  | some (y, n) => y.regs Reg.answer == encode 100 && y.regs Reg.top == 0 &&
      y.mem 985 != 99 && y.mem 2000 == 777 && n ≤ 1000
  | none => false

-- This query-only fixture supplies the canonical directory/value readback of the table
-- at threshold one. The constructor is not re-executed in this fixture. The first 99
-- records have no star; the final 18 have one star. All original leaf entries are one.
private def sparseQueryState : Data registers :=
  let x := (State.init (input 2 2 1 99 (fun _ => 1) (fun _ => 1)) : State registers).data
  let y := (((((((((x.set BoxTable.Reg.levels 2).set BoxTable.Reg.inner 2).set
    BoxTable.Reg.threshold 1).set BoxTable.Reg.span 100).set BoxTable.Reg.directory 205).set
    BoxTable.Reg.values 756).set BoxTable.Reg.arrayA 5).set BoxTable.Reg.arrayB 105).set
    BoxTable.Reg.count 117).set Reg.query 99
  { y with mem := fun p =>
      if 205 ≤ p ∧ p < 405 then BoxTable.directoryWord 2 1 (p - 205)
      else if 756 ≤ p ∧ p < 873 then encode (if p < 855 then 1 else 10)
      else if 873 ≤ p ∧ p < 1500 then 99
      else if p = 2000 then 777 else x.mem p }

-- Only 19 complete leaf tasks are visited: one low-order product and 18 box reads.
-- Both expansion levels and both leaf branches run, without another dense table build.
#guard match queryProgram.eval 20 1000 sparseQueryState with
  | some (y, n) => y.regs Reg.answer == encode 100 && y.regs Reg.top == 0 &&
      y.mem 873 != 99 && y.mem 2000 == 777 && n ≤ 10000 &&
      (List.range 205).all (fun p => y.mem p == sparseQueryState.mem p)
  | none => false


-- The actual pre-halt witness is the one consumed by Runs and the charged halt.
example : ∃ (y : Data registers) (n : ℕ),
    n + 1 ≤ timeBound 0 0 (PrunedQuery.queryAt (0 : Fin (10 ^ 0))) ∧
    Runs 24 (program.program Reg.answer)
      (State.init (input 0 0 0 0 (fun _ => 2) (fun _ => -3))) ⟨program.size, y⟩ n ∧
    Executes 24 (program.program Reg.answer)
      (State.init (input 0 0 0 0 (fun _ => 2) (fun _ => -3))) (encode (-6)) (n + 1) ∧
    y.regs Reg.answer = encode (-6) ∧ y.regs Reg.top = 0 := by
  obtain ⟨_, y, n, hn, hp, he, _, _, ht, hv, _⟩ :=
    runs_wide (W := 24) (m := 0) (t := 0) (A := 2) (B := 3) (0 : Fin (10 ^ 0))
      (by decide +kernel) (fun _ => 2) (fun _ => -3)
      (by intro i; decide +kernel) (by intro i; decide +kernel) (by decide +kernel)
  have hvalue : queryValue 0 0 (PrunedQuery.queryAt (0 : Fin (10 ^ 0)))
      (fun _ => 2) (fun _ => -3) = -6 := by decide +kernel
  exact ⟨y, n, hn, hp, by simpa only [hvalue] using he,
    by simpa only [hvalue] using hv, ht⟩

private def encodedLeft (i : Fin 10) : ℤ := encodingL a (BoxTable.leafAt i)
private def encodedRight (i : Fin 10) : ℤ := encodingR b (BoxTable.leafAt i)

-- Positive depth, nonzero signed encodings, and every specialization premise discharged.
example : ∃ (y : Data registers) (n : ℕ),
    Runs 32 (program.program Reg.answer)
      (State.init (input 1 1 1 9 encodedLeft encodedRight)) ⟨program.size, y⟩ n ∧
    Executes 32 (program.program Reg.answer)
      (State.init (input 1 1 1 9 encodedLeft encodedRight)) (encode (-8)) (n + 1) ∧
    y.regs Reg.answer = encode (-8) ∧
    y.mem 5 = encode (encodedLeft 0) := by
  have hl (τ : Leaf 1) : encodedLeft (Encoding.leafIndex τ) = encodingL a τ := by
    simp only [encodedLeft, BoxTable.leafAt_leafIndex]
  have hr (τ : Leaf 1) : encodedRight (Encoding.leafIndex τ) = encodingR b τ := by
    simp only [encodedRight, BoxTable.leafAt_leafIndex]
  obtain ⟨_, y, n, _, hp, he, _, hv, hf⟩ :=
    runs_bilinear (W := 32) (m := 1) (t := 1) (A := 16) (B := 16) (9 : Fin (10 ^ 1))
      (by decide +kernel) (by decide) a b encodedLeft encodedRight hl hr
      (by intro i; fin_cases i <;> decide +kernel)
      (by intro i; fin_cases i <;> decide +kernel) (by decide +kernel)
  have hvalue : bilinearProduct a b (PrunedQuery.queryAt (9 : Fin (10 ^ 1))) = -8 := by
    decide +kernel
  refine ⟨y, n, hp, by simpa only [hvalue] using he,
    by simpa only [hvalue] using hv, ?_⟩
  rw [hf 5 (by unfold directoryBase; omega)]
  exact (input_readback 1 1 1 (9 : Fin (10 ^ 1)) encodedLeft encodedRight).2.2.2.2.1 0


-- Zero operands also instantiate the exact minimum admitted physical width.
example : ∃ (y : Data registers) (n : ℕ),
    Runs (admissionWidth 0 0 0 0 0) (program.program Reg.answer)
      (State.init (input 0 0 0 0 (fun _ => 0) (fun _ => 0))) ⟨program.size, y⟩ n ∧
    Executes (admissionWidth 0 0 0 0 0) (program.program Reg.answer)
      (State.init (input 0 0 0 0 (fun _ => 0) (fun _ => 0))) 0 (n + 1) ∧
    y.regs Reg.answer = 0 := by
  obtain ⟨_, y, n, _, hp, he, _, _, _, hv, _⟩ :=
    runs_wide (m := 0) (t := 0) (A := 0) (B := 0) (0 : Fin (10 ^ 0))
      (by decide +kernel) (fun _ => 0) (fun _ => 0)
      (by intro i; decide +kernel) (by intro i; decide +kernel) le_rfl
  have hvalue : queryValue 0 0 (PrunedQuery.queryAt (0 : Fin (10 ^ 0)))
      (fun _ => 0) (fun _ => 0) = 0 := by decide +kernel
  have hz : encode (0 : ℤ) = 0 := rfl
  exact ⟨y, n, hp, by simpa only [hvalue, hz] using he,
    by simpa only [hvalue, hz] using hv⟩

example : (queryLeaves 2 0 (PrunedQuery.queryAt (99 : Fin (10 ^ 2)))).card = 1 := by
  decide +kernel

example : (queryLeaves 2 1 (PrunedQuery.queryAt (99 : Fin (10 ^ 2)))).card = 19 := by
  decide +kernel

example : (queryLeaves 2 2 (PrunedQuery.queryAt (99 : Fin (10 ^ 2)))).card = 100 := by
  decide +kernel

end ComplexityTests.WordRAMSchonhageBoxQuery
