/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Execution

/-!
# Choosing between native counting machines

A single native instruction has two ordered occurrences, entering either component without
changing the input, tapes or output. Each component then retains its own occurrences and first
halt. The inner optional control state denotes the selector; the outer optional configuration
state denotes actual halting. They must not be identified.

## Main definitions

* `Turing.MultiTapeCTM.alternative`: a one-instruction choice between two machines.

## Main results

* `Turing.MultiTapeCTM.runList_alternative`: exact list concatenation after the selector.
* `Turing.MultiTapeCTM.branchCount_alternative`: native terminal counts add.
* `Turing.MultiTapeCTM.HaltsWithin.alternative`: the selector costs one additional instruction.

## References

The sum-of-path-counts construction is standard in counting complexity [Valiant1979]. The
native occurrence semantics and shared program interpreter are credited in `MultiTape.Counting`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

variable {k : ℕ} {Symbol State State' State₀ State₁ : Type} {input : List Symbol}

namespace Alternative

/-- Relabel control while preserving the native halting action. -/
def mapAction (f : State → State') (action : Turing.Action k Symbol State) :
    Turing.Action k Symbol State' := { action with state := action.state.map f }

/-- A control transfer that leaves every tape, head and output unchanged. -/
def jump (state : State) : Turing.Action k Symbol State :=
  { inputTape := 0, workTapes := fun _ => (none, 0), output := none, state := some state }

/-- A component configuration in the selector's state space. -/
def config (f : State → State') (cfg : Cfg k Symbol State input) :
    Cfg k Symbol State' input := cfg.mapState (Option.map f)

theorem apply_mapAction (f : State → State') (action : Turing.Action k Symbol State)
    (cfg : Cfg k Symbol State input) :
    (mapAction f action).apply (config f cfg) = config f (action.apply cfg) := rfl

private theorem runList_map (source : MultiTapeCTM k Symbol State)
    (target : MultiTapeCTM k Symbol State') (f : State → State')
    (hstep : ∀ cfg : Cfg k Symbol State input,
      target.actions (config f cfg) = (source.actions cfg).map (mapAction f))
    (fuel : ℕ) (cfg : Cfg k Symbol State input) :
    target.runList fuel (config f cfg) = (source.runList fuel cfg).map (config f) := by
  induction fuel generalizing cfg with
  | zero => simp
  | succ fuel ih =>
    cases hs : cfg.state with
    | none =>
      rw [source.runList_halted hs, target.runList_halted (by simp [config, Cfg.Halted, hs])]
      rfl
    | some state =>
      rw [target.runList_succ _ fuel (f state) (by simp [config, hs]), hstep,
        source.runList_succ cfg fuel state hs, List.flatMap_map, List.map_flatMap]
      simp only [apply_mapAction, ih]

end Alternative

open Turing.MultiTapeCTM.Alternative

/-- Choose one of two components in one instruction, preserving both transition occurrences. -/
def alternative (first : MultiTapeCTM k Symbol State₀)
    (second : MultiTapeCTM k Symbol State₁) :
    MultiTapeCTM k Symbol (Option (State₀ ⊕ State₁)) where
  initial := none
  tr state symbol work answer := match state with
    | none => [jump (some (.inl first.initial)), jump (some (.inr second.initial))].map
        MultiTapeMachine.Action.emptyOracleEquiv.symm
    | some (.inl state) => (first.tr state symbol work answer).map fun action =>
        MultiTapeMachine.Action.emptyOracleEquiv.symm
          (mapAction (some ∘ Sum.inl) (MultiTapeMachine.Action.emptyOracleEquiv action))
    | some (.inr state) => (second.tr state symbol work answer).map fun action =>
        MultiTapeMachine.Action.emptyOracleEquiv.symm
          (mapAction (some ∘ Sum.inr) (MultiTapeMachine.Action.emptyOracleEquiv action))

/-- The selector and both component phases have an occurrence at every running local view. -/
theorem Nonblocking.alternative {first : MultiTapeCTM k Symbol State₀}
    {second : MultiTapeCTM k Symbol State₁} (hfirst : first.Nonblocking)
    (hsecond : second.Nonblocking) : (alternative first second).Nonblocking := by
  rintro (_ | (state | state)) symbol work
  · simp [MultiTapeCTM.alternative]
  · simpa [MultiTapeCTM.alternative] using hfirst state symbol work
  · simpa [MultiTapeCTM.alternative] using hsecond state symbol work

/-- Entering the first component preserves its complete occurrence list. -/
theorem runList_alternative_left (first : MultiTapeCTM k Symbol State₀)
    (second : MultiTapeCTM k Symbol State₁) (fuel : ℕ) (cfg : Cfg k Symbol State₀ input) :
    (alternative first second).runList fuel (config (some ∘ Sum.inl) cfg) =
      (first.runList fuel cfg).map (config (some ∘ Sum.inl)) := by
  apply runList_map
  intro cfg
  cases hs : cfg.state <;>
    simp only [actions, config, Cfg.mapState, hs, alternative, List.map_map, Function.comp_def,
      Option.map_none, Option.map_some, List.map_nil, Equiv.apply_symm_apply]
  rfl

/-- Entering the second component preserves its complete occurrence list. -/
theorem runList_alternative_right (first : MultiTapeCTM k Symbol State₀)
    (second : MultiTapeCTM k Symbol State₁) (fuel : ℕ) (cfg : Cfg k Symbol State₁ input) :
    (alternative first second).runList fuel (config (some ∘ Sum.inr) cfg) =
      (second.runList fuel cfg).map (config (some ∘ Sum.inr)) := by
  apply runList_map
  intro cfg
  cases hs : cfg.state <;>
    simp only [actions, config, Cfg.mapState, hs, alternative, List.map_map, Function.comp_def,
      Option.map_none, Option.map_some, List.map_nil, Equiv.apply_symm_apply]
  rfl

/-- The selector contributes exactly one occurrence of each component, including equal outputs. -/
theorem runList_alternative (first : MultiTapeCTM k Symbol State₀)
    (second : MultiTapeCTM k Symbol State₁) (fuel : ℕ) (input : List Symbol) :
    (alternative first second).runList (fuel + 1)
        (Cfg.init (alternative first second).initial input) =
      (first.runList fuel (Cfg.init first.initial input)).map (config (some ∘ Sum.inl)) ++
      (second.runList fuel (Cfg.init second.initial input)).map (config (some ∘ Sum.inr)) := by
  have ha : (alternative first second).actions
      (Cfg.init (alternative first second).initial input) =
      [jump (some (.inl first.initial)), jump (some (.inr second.initial))] := by
    simp [actions, Cfg.init, alternative]
  rw [runList_succ _ _ fuel none rfl, ha]
  simp only [List.flatMap_cons, List.flatMap_nil, List.append_nil]
  have hjump (state : Option (State₀ ⊕ State₁)) : (jump (k := k) state).apply
      (Cfg.init (alternative first second).initial input) =
        Cfg.init state input := by
    simp [jump, Turing.Action.apply, Cfg.init, moveInputPos, alternative]
  rw [hjump, hjump]
  exact congrArg₂ List.append
    (runList_alternative_left first second fuel (Cfg.init first.initial input))
    (runList_alternative_right first second fuel (Cfg.init second.initial input))

/-- Native terminal counts add, even at clocks too short for some component branches. -/
theorem branchCount_alternative (first : MultiTapeCTM k Symbol State₀)
    (second : MultiTapeCTM k Symbol State₁) (verdict : List Symbol → Bool)
    (fuel : ℕ) (input : List Symbol) :
    (alternative first second).branchCount verdict (fuel + 1)
        (Cfg.init (alternative first second).initial input) =
      first.branchCount verdict fuel (Cfg.init first.initial input) +
        second.branchCount verdict fuel (Cfg.init second.initial input) := by
  rw [← countP_runList, runList_alternative, List.countP_append]
  simp only [List.countP_map, Function.comp_def, config, Cfg.mapState, Option.isNone_map,
    countP_runList]

/-- A common sufficient component clock gains exactly one selector instruction. -/
theorem HaltsWithin.alternative {first : MultiTapeCTM k Symbol State₀}
    {second : MultiTapeCTM k Symbol State₁} (hnonfirst : first.Nonblocking)
    (hnonsecond : second.Nonblocking) (fuel : ℕ) (input : List Symbol)
    (hfirst : first.HaltsWithin fuel (Cfg.init first.initial input))
    (hsecond : second.HaltsWithin fuel (Cfg.init second.initial input)) :
    (alternative first second).HaltsWithin (fuel + 1)
      (Cfg.init (alternative first second).initial input) := by
  apply haltsWithin_of_halted _ (hnonfirst.alternative hnonsecond).actions_ne_nil
  intro final hfinal
  rw [runList_alternative] at hfinal
  rcases List.mem_append.mp hfinal with hfinal | hfinal
  · obtain ⟨native, hnative, rfl⟩ := List.mem_map.mp hfinal
    simp [config, Cfg.Halted, hfirst.halted_of_mem_runList hnative]
  · obtain ⟨native, hnative, rfl⟩ := List.mem_map.mp hfinal
    simp [config, Cfg.Halted, hsecond.halted_of_mem_runList hnative]

end Turing.MultiTapeCTM
