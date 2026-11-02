/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: local-only (tests of functional HPV block computation)

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation

/-!
# Functional HPV schedule validation

A native machine emits one bit and halts. Its actual schedule succeeds, a wrong input-head
movement fails, and failure persists through subsequent intervals. The empty schedule is also
inhabited. These test the deterministic bridge and the mandatory control dependency.
-/

@[expose] public section

namespace ComplexityTests.BlockComputation

open Turing MultiTapePTM.BlockComputation

/-- Emit one bit while keeping the input head fixed, then halt. -/
def emit : MultiTapeTM 0 Bool Unit := MultiTapeTM.ofTr () fun _ _ _ =>
  { inputTape := 0, workTapes := Fin.elim0, output := some true, state := none }

noncomputable def machine : MultiTapePTM 0 Bool Unit := MultiTapePTM.ofDeterministic emit
noncomputable def actual : MultiTapePTM.Schedule 0 2 := actualSchedule machine [] 1

def wrong : MultiTapePTM.Schedule 0 2 := fun i _ => if i = 0 then 1 else 0

example : value machine [] 1 actual 2 = some (trueView machine [] 1 actual 2) :=
  (value_final_eq_some_iff machine [] 1 actual _).mpr ⟨rfl, rfl⟩

private theorem initial_input_fixed :
    (emit.runFrom (Cfg.init () []) 1).headPos none = 0 := by
  rw [MultiTapeTM.runFrom_one, MultiTapeTM.step_of_state (q := ()) rfl]
  simp [emit, Action.apply, Cfg.headPos]

private theorem actual_first : (actual 0 none : ℤ) = 0 := by
  change ((machine.schedule 1 2 (List.replicate (2 * 1) false)
    (Cfg.init machine.initial [])) 0 none : ℤ) = 0
  rw [MultiTapePTM.coe_schedule machine (by decide)]
  change ((boundary machine [] 1 (q := 2) 1).headPos none / 1 -
    (boundary machine [] 1 (q := 2) 0).headPos none / 1) = 0
  rw [machine]
  rw [boundary_ofDeterministic [] 1 emit (by decide),
    boundary_ofDeterministic [] 1 emit (by decide)]
  change (emit.runFrom (Cfg.init () []) 1).headPos none / 1 -
    (Cfg.init () []).headPos none / 1 = 0
  rw [initial_input_fixed, Cfg.headPos_init]
  norm_num

private theorem wrong_schedule : actual ≠ wrong := by
  intro h
  have hi := congrArg (fun σ : MultiTapePTM.Schedule 0 2 => (σ 0 none : ℤ)) h
  rw [actual_first] at hi
  norm_num [wrong] at hi

example : value machine [] 1 wrong 2 = none :=
  (value_final_eq_none_iff machine [] 1 wrong).mpr wrong_schedule

example : value machine [] 1 wrong 3 = none :=
  value_succ_eq_none machine [] 1 wrong
    ((value_final_eq_none_iff machine [] 1 wrong).mpr wrong_schedule)

/-- Empty schedules validate at the initial source without making a replay step. -/
example (σ : MultiTapePTM.Schedule 0 0) :
    value machine [] 1 σ 0 = some (initialView machine 1) := by simp only [value]

example : boundary machine [] 1 (q := 2) 2 = emit.runFrom (Cfg.init () []) 2 :=
  boundary_ofDeterministic [] 1 emit le_rfl

end ComplexityTests.BlockComputation
