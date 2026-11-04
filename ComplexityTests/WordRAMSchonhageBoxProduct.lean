/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

/-!
Complete native routed box-product regressions. Original matrices and coordinates are
routed and encoded by the real producers, one shared geometry is built, and every tile
runs the retained-value/sparse-query kernels. Input restoration includes the ordinary
appended threshold and native length header.
-/

set_option linter.hashCommand false

namespace ComplexityTests.WordRAMSchonhageBoxProduct

open Cslib.WordRAM Cslib.WordRAM.Signed
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage.BoxProduct

private def X : Matrix (Fin 2) (Fin (D 0)) ℤ := fun i _ => ![-3, 4] i
private def Y : Matrix (Fin (D 0)) (Fin 2) ℤ := fun _ j => ![2, -5] j
private def queries : List (Fin 2 × Fin 2) := [(1, 0), (0, 1), (1, 0), (0, 0)]

private def dirtyInput : Data 160 :=
  let x := (State.init (input false 0 0 X Y queries) : State 160).data
  { x with mem := fun p =>
      if QueriedProduct.inputEnd 0 2 queries.length < p then 777 else x.mem p }

-- Four different tiles reuse one real geometry; request order and repetitions survive.
-- Every original word is restored, and a far dirty sentinel lies outside the allocation.
#guard match (program false).eval 64 10000 dirtyInput with
  | some (y, _) =>
      y.mem (QueriedProduct.outputBase 0 0 2 4) == encode 8 &&
      y.mem (QueriedProduct.outputBase 0 0 2 4 + 1) == encode 15 &&
      y.mem (QueriedProduct.outputBase 0 0 2 4 + 2) == encode 8 &&
      y.mem (QueriedProduct.outputBase 0 0 2 4 + 3) == encode (-6) &&
      y.mem 100000 == 777 &&
      (List.range (QueriedProduct.inputEnd 0 2 4 + 1)).all
        (fun p => y.mem p == dirtyInput.mem p)
  | none => false

private def emptyX : Matrix (Fin 0) (Fin (D 0)) ℤ := fun i _ => Fin.elim0 i
private def emptyY : Matrix (Fin (D 0)) (Fin 0) ℤ := fun _ j => Fin.elim0 j

-- With no bands or wanted coordinates, the tile loop exits before any division by zero.
#guard match (program false).eval 64 10000
    (State.init (input false 0 0 emptyX emptyY [])).data with
  | some (y, _) => y.regs QueriedProduct.Reg.index == 0 &&
      y.mem (QueriedProduct.inputEnd 0 0 0) == 0
  | none => false

private def innerX : Matrix (Fin 1) (Fin (D 1)) ℤ := fun _ k => ![1, -2, 3, 0] k
private def innerY : Matrix (Fin (D 1)) (Fin 1) ℤ := fun k _ => ![4, 5, -1, 2] k

-- Positive depth and signed cancellation, using retained starred values at threshold zero.
#guard match (program false).eval 64 10000
    (State.init (input false 1 0 innerX innerY [(0, 0), (0, 0)])).data with
  | some (y, _) => y.mem (QueriedProduct.outputBase 1 1 1 2) == encode (-9) &&
      y.mem (QueriedProduct.outputBase 1 1 1 2 + 1) == encode (-9) &&
      y.mem (QueriedProduct.inputEnd 1 1 2) == 0
  | none => false

-- The same source product through low-order multiplication and singleton box lookups.
#guard match (program false).eval 64 10000
    (State.init (input false 1 1 innerX innerY [(0, 0)])).data with
  | some (y, _) => y.mem (QueriedProduct.outputBase 1 1 1 1) == encode (-9) &&
      y.mem (QueriedProduct.inputEnd 1 1 1) == 1
  | none => false

private def rawX : Matrix (Fin 2) (Fin (D 0)) ℤ := fun i _ => ![1, 0] i
private def rawY : Matrix (Fin (D 0)) (Fin 2) ℤ := fun _ j => ![0, 1] j

-- Actual raw-word conversion is part of the native program, as needed by the ET frontend.
#guard match (program true).eval 64 10000
    (State.init (input true 0 0 rawX rawY [(0, 1), (1, 0), (0, 1)])).data with
  | some (y, _) => y.mem (QueriedProduct.outputBase 0 0 2 3) == encode 1 &&
      y.mem (QueriedProduct.outputBase 0 0 2 3 + 1) == encode 0 &&
      y.mem (QueriedProduct.outputBase 0 0 2 3 + 2) == encode 1
  | none => false

-- Original signed matrices, four raw coordinate occurrences and every admission premise
-- instantiate the finite thin-product endpoint. Prefix, halt, charge and answers share y.
example : ∃ (y : Data 160) (n : ℕ),
    n + 1 ≤ 10485760 ∧
    Runs 64 ((program false).program QueriedProduct.Reg.output)
      (State.init (input false 0 0 X Y queries)) ⟨(program false).size, y⟩ n ∧
    Executes 64 ((program false).program QueriedProduct.Reg.output)
      (State.init (input false 0 0 X Y queries)) (QueriedProduct.outputBase 0 0 2 4) (n + 1) ∧
    y.mem (QueriedProduct.outputBase 0 0 2 4) = encode 8 ∧
    y.mem (QueriedProduct.outputBase 0 0 2 4 + 3) = encode (-6) ∧
    y.mem 0 = (input false 0 0 X Y queries).length := by
  obtain ⟨_, y, n, hn, hp, he, _, hv, hf⟩ :=
    runs_thin (W := 64) (k := 0) (N := 2) (A := 5) false X Y queries
      (by decide +kernel) (by decide +kernel) (by simp) (by decide +kernel)
      (by decide +kernel) (by decide +kernel)
  have hn' : n + 1 ≤ 10485760 := by
    norm_num [D] at hn
    exact_mod_cast hn
  have h0 := hv ⟨0, by decide⟩
  have h3 := hv ⟨3, by decide⟩
  have v0 : (X * Y) (queries.get ⟨0, by decide⟩).1 (queries.get ⟨0, by decide⟩).2 = 8 := by
    decide +kernel
  have v3 : (X * Y) (queries.get ⟨3, by decide⟩).1 (queries.get ⟨3, by decide⟩).2 = -6 := by
    decide +kernel
  refine ⟨y, n, hn', hp, he, ?_, ?_, ?_⟩
  · simpa only [v0, Fin.val_zero, Nat.add_zero, Nat.mul_zero,
      show queries.length = 4 from rfl] using h0
  · simpa only [v3, Nat.mul_zero, show queries.length = 4 from rfl] using h3
  · rw [hf 0 (by unfold QueriedProduct.inputEnd; omega)]
    rfl

-- Empty matrices and requests also instantiate the complete minimum-width initialized run.
example : ∃ (y : Data 160) (n : ℕ),
    Runs (admissionWidth 0 0 0 0 0 0) ((program false).program QueriedProduct.Reg.output)
      (State.init (input false 0 0 emptyX emptyY [])) ⟨(program false).size, y⟩ n ∧
    Executes (admissionWidth 0 0 0 0 0 0)
      ((program false).program QueriedProduct.Reg.output)
      (State.init (input false 0 0 emptyX emptyY [])) (QueriedProduct.outputBase 0 0 0 0) (n + 1) ∧
    y.mem (QueriedProduct.inputEnd 0 0 0) = 0 := by
  obtain ⟨_, y, n, _, hp, he, _, _, hf⟩ :=
    runs_wide (W := admissionWidth 0 0 0 0 0 0) (L := 0) (m := 0) (t := 0) (A := 0)
      (by decide) (by decide) false emptyX emptyY []
      (by intro i; exact Fin.elim0 i) (by intro _ j; exact Fin.elim0 j) (by simp) le_rfl
  refine ⟨y, n, hp, he, ?_⟩
  rw [hf _ (by simp only [List.length_nil]; omega)]
  exact input_threshold false emptyX emptyY []

end ComplexityTests.WordRAMSchonhageBoxProduct
