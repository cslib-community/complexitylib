/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

-- upstream: local-only (tests)

import Complexity.Algorithms.WordRAM.MatrixMultiplication.Schonhage.Callable.Width

-- VM checks exercise actual code alongside the separate kernel-checked general execution.
-- Complete interpreter clients use m=0,N=1: (4^m)^18 ≤ N makes larger depths impractical.
-- Positive-depth thin bounds are established by the general execution/resource theorems.
set_option linter.hashCommand false

namespace ComplexityTests.SchonhageCallable

open Cslib.WordRAM
open Cslib.Algorithms.MatrixMultiplication.Schonhage
open Cslib.Algorithms.WordRAM.MatrixMultiplication.Schonhage

private def observe {m N : ℕ} (caller : List ℕ)
    (X : Matrix (Fin N) (Fin (D m)) ℤ) (Y : Matrix (Fin (D m)) (Fin N) ℤ)
    (qs : List (Fin N × Fin N)) (dirtyWorkspace : Bool := false) : Option (List ℤ × Bool) :=
  let original := (State.init (CallableProduct.input caller X Y qs) : State 163).data
  let b := CallableProduct.inputBase caller
  let sentinel := b + CallableProduct.windowSize N qs.length + 7
  let dirty : Data 163 := ⟨original.regs, fun a =>
    if dirtyWorkspace && decide (b + QueriedProduct.inputEnd m N qs.length ≤ a ∧
        a < b + CallableProduct.windowSize N qs.length)
      then 2 * CallableProduct.windowSize N qs.length + 27 else original.mem a⟩
  let initial := dirty.write sentinel 91
  (CallableProduct.entryProgram.eval 512 1024 initial).map fun (y, _) =>
    ((List.range qs.length).map (fun i => Signed.decode (y.mem (y.regs 0 + i))),
      decide ((∀ a < b, y.mem a = original.mem a) ∧
        (∀ a < QueriedProduct.inputEnd m N qs.length, y.mem (b + a) = original.mem (b + a)) ∧
        y.mem sentinel = 91))

-- Actual raw-one multiplication and duplicate requests at a dynamic nonzero base.
#guard observe [17, 29] (m := 0) (N := 1) (fun _ _ => 1) (fun _ _ => 1)
    [(0, 0), (0, 0), (0, 0)] == some ([1, 1, 1], true)

-- Actual empty query and zero-product cases still restore the caller and local input.
#guard observe [23] (m := 0) (N := 1) (fun _ _ => 1) (fun _ _ => 0) [] == some ([], true)
#guard observe [] (m := 0) (N := 1) (fun _ _ => 1) (fun _ _ => 0) [(0, 0)] == some ([0], true)

-- A preexisting caller workspace can contain physical words larger than the source modulus.
-- This is a supplied dirty caller state; the callee performs no bulk fill or clearing.
#guard observe [17, 29] (m := 0) (N := 1) (fun _ _ => 1) (fun _ _ => 1)
    [(0, 0), (0, 0)] true == some ([1, 1], true)

private def X : Matrix (Fin 1) (Fin (D 0)) ℤ := fun _ _ => 1
private def Y : Matrix (Fin (D 0)) (Fin 1) ℤ := fun _ _ => 1
private def requests : List (Fin 1 × Fin 1) := [(0, 0)]

-- Kernel-checked complete initialized execution. The same y is reached by charged Runs,
-- supplies the exact physical signed answer 2, preserves the caller, and reaches halt.
example : ∃ y n,
    Runs 512 (CallableProduct.entryProgram.program CallableProduct.Reg.result)
      (State.init (CallableProduct.input [17, 29] X Y requests))
      ⟨CallableProduct.entryProgram.size, y⟩ n ∧
    Executes 512 (CallableProduct.entryProgram.program CallableProduct.Reg.result)
      (State.init (CallableProduct.input [17, 29] X Y requests))
      (4 + QueriedProduct.outputBase 0 0 1 1) (n + 1) ∧
    y.mem (4 + QueriedProduct.outputBase 0 0 1 1) = 2 ∧ y.mem 2 = 17 ∧ y.mem 3 = 29 := by
  obtain ⟨hi, y, n, hn, hr, he, hy, hv, hin, hf⟩ := CallableProduct.runs
    (W := 512) [17, 29] X Y requests (by decide +kernel)
    (by intro i k; constructor <;> norm_num [X])
    (by intro k j; constructor <;> norm_num [Y])
    (by
      intro v hv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl <;> decide +kernel)
    (by decide +kernel)
  refine ⟨y, n, hr, he, ?_, ?_, ?_⟩
  · have hone : (X * Y) 0 0 = 1 := by decide +kernel
    have h := hv (0 : Fin 1)
    change y.mem (4 + QueriedProduct.outputBase 0 0 1 1) = Signed.encode ((X * Y) 0 0) at h
    rw [hone] at h
    exact h
  · simpa [CallableProduct.input, CallableProduct.inputBase, State.init, Data.init] using
      hf 2 (Or.inl (by decide))
  · simpa [CallableProduct.input, CallableProduct.inputBase, State.init, Data.init] using
      hf 3 (Or.inl (by decide))

-- The numerical reservation/admission budget has a strict width boundary for this input.
example : Fits 387 (4 + 4 * CallableProduct.windowSize 1 1 + 1024) ∧
    ¬Fits 386 (4 + 4 * CallableProduct.windowSize 1 1 + 1024) := by decide +kernel

-- Empty query lists are admitted at positive geometry; zero N fails the explicit thin premise.
example : ¬D 0 ^ 18 ≤ 0 := by decide +kernel

end ComplexityTests.SchonhageCallable
