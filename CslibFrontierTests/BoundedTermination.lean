/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

import CslibFrontier.Computability.Complexity.Problems.BoundedTermination
import CslibFrontier.Computability.Machines.Turing.MultiTape.Halting.Partialize

/-! # Any-output bounded halting, exact clocks and the accepting-output distinction -/

set_option linter.privateModule false

namespace CslibFrontierTests.BoundedTermination

open Cslib Cslib.Complexity Cslib.BitString Turing Turing.MultiTapeTM
open Turing.MultiTapeTM.Universal BoundedComputation

private def haltAct (out : Option ℕ) : Act := ⟨0, [], out, none⟩
private def haltDesc (out : Option ℕ) : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, haltAct out), (⟨0, some 0, []⟩, haltAct out),
    (⟨0, some 1, []⟩, haltAct out)]⟩

-- Empty and false outputs both count as termination, but neither is accepting output [true].
example : mk (haltDesc none) [] [true] ∈ BoundedTermination := by
  rw [BoundedTermination.mk_mem_iff]
  decide
example : mk (haltDesc none) [] [true] ∉ BoundedHalting := by
  rw [BoundedHalting.mk_mem_iff]
  decide
example : mk (haltDesc (some 0)) [true] [true] ∈ BoundedTermination := by
  rw [BoundedTermination.mk_mem_iff]
  decide
example : mk (haltDesc (some 0)) [true] [true] ∉ BoundedHalting := by
  rw [BoundedHalting.mk_mem_iff]
  decide

-- The canonical-triple theorem also applies to a concrete native binary machine.
private def quietMachine : MultiTapeTM 0 Bool Unit :=
  ofTr () fun _ _ _ =>
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := none }

private def eUnit : Unit ↪ ℕ := ⟨fun _ => 0, fun _ _ _ => Subsingleton.elim _ _⟩

example (x : List Bool) : mk (desc eUnit eBit quietMachine) x [true] ∈ BoundedTermination := by
  rw [BoundedTermination.mk_desc_mem_iff]
  have hc : binaryValue [true] = 1 := by
    have h := binaryValue_replicate_true 1
    simp only [List.replicate_succ, List.replicate_zero, pow_one] at h
    omega
  rw [hc]
  change (quietMachine.step (quietMachine.initCfg x)).Halted
  rw [step_of_state (q := ()) rfl]
  simp only [quietMachine, tr_ofTr]
  rfl

-- Clock zero excludes even a one-step halter; halting exactly at the bound is included above.
example (d : Desc) (x : List Bool) : mk d x [] ∉ BoundedTermination := by
  rw [BoundedTermination.mk_mem_iff]
  exact Bool.false_ne_true

private def loopAct : Act := ⟨0, [], some 1, some 0⟩
private def loopDesc : Desc :=
  ⟨0, 0, [(⟨0, none, []⟩, loopAct), (⟨0, some 0, []⟩, loopAct),
    (⟨0, some 1, []⟩, loopAct)]⟩

-- Emitting true while continuing to run does not count as termination.
example : mk loopDesc [] [true, true] ∉ BoundedTermination := by
  rw [BoundedTermination.mk_mem_iff]
  decide

-- Partialization diverges at every clock after a true verdict; reuse the native halting API.
example {k : ℕ} {State : Type} [Fintype State] (tm : MultiTapeTM k Bool State)
    (eS : (Option State × Option Bool) ↪ ℕ) (x c : List Bool)
    (h : tm.Computes x [true]) : mk (desc eS eBit tm.partialize) x c ∉ BoundedTermination := by
  rw [BoundedTermination.mk_desc_mem_iff]
  intro ht
  have hc : tm.Computes x (encPartial none) := by simpa using h
  have hn : ¬tm.partialize.Halts x := by simpa using hc.halts_partialize
  exact hn ⟨binaryValue c, ht⟩

example (w : List Bool) : mk (descOf w) (inputOf w) (clockOf w) ∈ BoundedTermination ↔
    w ∈ BoundedTermination := BoundedTermination.mem_reencode_iff w

example : BoundedTermination ∈ E encBits ∧ BoundedTermination ∉ P encBits ∧
    PolyTimeComplete @EXP encBits BoundedTermination :=
  ⟨BoundedTermination.mem_E, BoundedTermination.notMem_P, BoundedTermination.polyTimeComplete_EXP⟩

example : PolyTimeReducible encBits encBits BoundedHalting BoundedTermination :=
  BoundedTermination.boundedHalting_polyTimeReducible

end CslibFrontierTests.BoundedTermination
