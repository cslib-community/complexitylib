/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

/-!
Actual complete batch executions: empty and repeated wanted arrays, distinct output
codes, signed values, cancellation, dirty workspace and a nonvacuous initialized
execution theorem. Every VM fixture builds its own real geometry and retained values.
-/

set_option linter.hashCommand false

namespace CslibFrontierTests.WordRAMSchonhageBoxBatch

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxBatch

private def emptyCode : OutStr 0 := PrunedQuery.queryAt 0

-- A zero-length wanted array performs preparation and leaves the first result word untouched.
#guard match program.eval 24 1000
    (((State.init (input 0 0 ([] : List (OutStr 0)) (fun _ => 2) (fun _ => -3))).data).write
      (outputBase 0 0 0 0) 777) with
  | some (y, _) => y.regs Reg.next == queryBase 0 &&
      y.regs Reg.output == outputBase 0 0 0 0 && y.mem (outputBase 0 0 0 0) == 777
  | none => false

-- Repeated occurrences consume one constructed table and each receive their own answer word.
#guard match program.eval 24 1000
    (State.init (input 0 0 [emptyCode, emptyCode, emptyCode]
      (fun _ => 2) (fun _ => -3))).data with
  | some (y, _) => y.regs Reg.next == queryBase 0 + 3 &&
      y.regs Reg.output == memoryEnd 0 0 0 3 &&
      (List.range 3).all (fun i => y.mem (outputBase 0 0 0 3 + i) == encode (-6))
  | none => false

private def privateCodes : List (OutStr 1) :=
  [PrunedQuery.queryAt 0, PrunedQuery.queryAt 8, PrunedQuery.queryAt 0]

private def leftValues (i : Fin 10) : ℤ := if i.val = 0 then 2 else 5
private def rightValues (i : Fin 10) : ℤ := if i.val = 0 then -3 else 7

private def dirtyInput : Data registers :=
  let x := (State.init (input 0 0 privateCodes leftValues rightValues) : State registers).data
  { x with mem := fun p => if directoryBase 1 3 ≤ p then 777 else x.mem p }

-- Distinct private outputs and a repeated output retain their original order. Dirty
-- geometry, value, stack and result words are overwritten; the far sentinel is framed.
#guard match program.eval 24 1000 dirtyInput with
  | some (y, _) => y.mem (outputBase 1 0 0 3) == encode (-6) &&
      y.mem (outputBase 1 0 0 3 + 1) == encode 35 &&
      y.mem (outputBase 1 0 0 3 + 2) == encode (-6) &&
      y.mem 20000 == 777 &&
      (List.range (directoryBase 1 3)).all (fun p => y.mem p == dirtyInput.mem p)
  | none => false

private def innerCode : OutStr 1 := PrunedQuery.queryAt 9
private def cancellingRight (i : Fin 10) : ℤ :=
  if i.val = 0 then -3 else if i.val = 1 then 3 else 0

-- Both repeated inner queries sum signed nonzero terms to zero. Threshold zero uses
-- retained starred values; threshold one exercises low products and singleton table reads.
#guard match program.eval 24 1000
    (State.init (input 1 0 [innerCode, innerCode] (fun _ => 1) cancellingRight)).data with
  | some (y, _) => y.mem (outputBase 1 1 0 2) == encode 0 &&
      y.mem (outputBase 1 1 0 2 + 1) == encode 0
  | none => false

#guard match program.eval 24 1000
    (State.init (input 1 1 [innerCode, innerCode] (fun _ => 1) cancellingRight)).data with
  | some (y, _) => y.mem (outputBase 1 1 1 2) == encode 0 &&
      y.mem (outputBase 1 1 1 2 + 1) == encode 0
  | none => false

private def depthTwoCodes : List (OutStr 2) :=
  [PrunedQuery.queryAt 9, PrunedQuery.queryAt 90, PrunedQuery.queryAt 9]

private def depthTwoRight (i : Fin 100) : ℤ := if i.val = 0 then -3 else i.val

-- Different inner-coordinate positions exercise real least-significant-first code loads.
-- This fixture constructs the entire depth-two geometry/value table once for all three queries.
#guard match program.eval 24 1000
    (State.init (input 1 1 depthTwoCodes (fun _ => 1) depthTwoRight)).data with
  | some (y, _) => y.mem (outputBase 2 1 1 3) == encode 42 &&
      y.mem (outputBase 2 1 1 3 + 1) == encode 447 &&
      y.mem (outputBase 2 1 1 3 + 2) == encode 42
  | none => false

-- Every original-input fit and magnitude premise is discharged for a nonzero signed batch.
example : ∃ y : Data registers,
    ExecWithin 24 program
      (State.init (input 0 0 [emptyCode, emptyCode] (fun _ => 2) (fun _ => -3))).data y
      (preparationTime 0 0 0 + queryTime 0 0 [emptyCode, emptyCode]) ∧
    y.mem (outputBase 0 0 0 2) = encode (-6) ∧
    y.mem (outputBase 0 0 0 2 + 1) = encode (-6) ∧
    y.regs Reg.output = memoryEnd 0 0 0 2 := by
  obtain ⟨_, y, he, _, _, _, _, hy, hv, _⟩ :=
    exec_input (w := 22) (L := 0) (m := 0) (t := 0) (A := 2) (B := 3)
      (by decide) [emptyCode, emptyCode] (by
        intro η hη
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hη
        rcases hη with rfl | rfl <;> decide +kernel)
      (fun _ => 2) (fun _ => -3)
      (by intro i; decide +kernel) (by intro i; decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have hvalue : BoxQuery.queryValue 0 0 emptyCode (fun _ => 2) (fun _ => -3) = -6 := by
    decide +kernel
  have h0 := hv ⟨0, by decide⟩
  have h1 := hv ⟨1, by decide⟩
  change y.mem (outputBase 0 0 0 2 + 0) =
    encode (BoxQuery.queryValue 0 0 emptyCode (fun _ => 2) (fun _ => -3)) at h0
  change y.mem (outputBase 0 0 0 2 + 1) =
    encode (BoxQuery.queryValue 0 0 emptyCode (fun _ => 2) (fun _ => -3)) at h1
  exact ⟨y, he, by simpa only [Nat.add_zero, hvalue] using h0,
    by simpa only [hvalue] using h1, hy⟩

-- Even an empty batch has a fully admitted same-state prefix and charged halt at its
-- exact minimum width; the scalar return is the exclusive answer-array end.
example : ∃ (y : Data registers) (n : ℕ),
    Runs (admissionWidth 0 0 0 0 0 0) (program.program Reg.output)
      (State.init (input 0 0 ([] : List (OutStr 0)) (fun _ => 0) (fun _ => 0)))
      ⟨program.size, y⟩ n ∧
    Executes (admissionWidth 0 0 0 0 0 0) (program.program Reg.output)
      (State.init (input 0 0 ([] : List (OutStr 0)) (fun _ => 0) (fun _ => 0)))
      (memoryEnd 0 0 0 0) (n + 1) ∧
    y.regs Reg.output = memoryEnd 0 0 0 0 := by
  obtain ⟨_, y, n, _, hp, he, _, ho, _⟩ :=
    runs_wide (W := admissionWidth 0 0 0 0 0 0) (L := 0) (m := 0) (t := 0)
      (A := 0) (B := 0) (by decide) [] (by simp)
      (fun _ => 0) (fun _ => 0) (by intro i; decide +kernel)
      (by intro i; decide +kernel) le_rfl
  exact ⟨y, n, hp, he, ho⟩

-- Canonical depth-zero encodings connect repeated native answers to the original
-- bilinear product, with every encoding, magnitude and width premise discharged.
example : ∃ (y : Data registers) (n : ℕ),
    Runs 32 (program.program Reg.output)
      (State.init (input 0 0 [emptyCode, emptyCode] (fun _ => 2) (fun _ => -3)))
      ⟨program.size, y⟩ n ∧
    Executes 32 (program.program Reg.output)
      (State.init (input 0 0 [emptyCode, emptyCode] (fun _ => 2) (fun _ => -3)))
      (memoryEnd 0 0 0 2) (n + 1) ∧
    y.mem (outputBase 0 0 0 2) = encode (-6) ∧
    y.mem (outputBase 0 0 0 2 + 1) = encode (-6) := by
  obtain ⟨_, y, n, _, hp, he, _, hv, _⟩ :=
    runs_bilinear (W := 32) (L := 0) (m := 0) (t := 0) (A := 2) (B := 3)
      (by decide) (by decide) [emptyCode, emptyCode] (by
        intro η hη
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hη
        rcases hη with rfl | rfl <;> decide +kernel)
      (fun _ => 2) (fun _ => -3) (fun _ => 2) (fun _ => -3)
      (by intro τ; decide +kernel +revert) (by intro τ; decide +kernel +revert)
      (by intro i; decide +kernel) (by intro i; decide +kernel) (by decide +kernel)
  have hvalue : bilinearProduct (fun _ : LeftStr 0 => 2) (fun _ => -3) emptyCode = -6 := by
    decide +kernel
  have h0 := hv ⟨0, by decide⟩
  have h1 := hv ⟨1, by decide⟩
  change y.mem (outputBase 0 0 0 2 + 0) =
    encode (bilinearProduct (fun _ : LeftStr 0 => 2) (fun _ => -3) emptyCode) at h0
  change y.mem (outputBase 0 0 0 2 + 1) =
    encode (bilinearProduct (fun _ : LeftStr 0 => 2) (fun _ => -3) emptyCode) at h1
  exact ⟨y, n, hp, he, by simpa only [Nat.add_zero, hvalue] using h0,
    by simpa only [hvalue] using h1⟩

end CslibFrontierTests.WordRAMSchonhageBoxBatch
