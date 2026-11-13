/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Deterministic

/-!
# Relabeling emitted symbols

Output relabeling leaves the transition states, input, work tapes and clock unchanged. It lets a
Boolean evaluator emit whether its answer matches a claim without appending a comparison phase.
-/

public section

namespace Turing

variable {k : ℕ} {Symbol State : Type*} {input : List Symbol}

/-- Relabel only the output already emitted by a configuration. -/
@[expose, simps] def Cfg.mapOutput (cfg : Cfg k Symbol State input) (f : Symbol → Symbol) :
    Cfg k Symbol State input :=
  { cfg with output := cfg.output.map f }

namespace MultiTapeTM

/-- Relabel every emitted symbol, keeping all transitions and work tape operations. -/
@[expose] noncomputable def mapOutput (tm : MultiTapeTM k Symbol State) (f : Symbol → Symbol) :
    MultiTapeTM k Symbol State :=
  ofTr tm.q₀ fun q i w =>
    let action := tm.tr q i w
    { action with output := action.output.map f }

@[simp] theorem mapOutput_q₀ (tm : MultiTapeTM k Symbol State) (f : Symbol → Symbol) :
    (tm.mapOutput f).q₀ = tm.q₀ := rfl

/-- Output relabeling commutes with a physical machine step. -/
theorem step_mapOutput (tm : MultiTapeTM k Symbol State) (f : Symbol → Symbol)
    (cfg : Cfg k Symbol State input) :
    (tm.mapOutput f).step (cfg.mapOutput f) = (tm.step cfg).mapOutput f := by
  cases hq : cfg.state with
  | none => rw [step_of_halt hq, step_of_halt (by simpa using hq)]
  | some q =>
    rw [step_of_state hq, step_of_state (q := q) (by simpa using hq)]
    have hin : (cfg.mapOutput f).inputSymbol = cfg.inputSymbol := rfl
    have hw : (cfg.mapOutput f).workTapeSymbols = cfg.workTapeSymbols := rfl
    simp only [mapOutput, tr_ofTr, hin, hw]
    apply Cfg.ext <;> simp [Cfg.mapOutput, Action.apply, Option.toList_map]

/-- Relabeling output preserves every exact run length and all physical storage. -/
theorem runFrom_mapOutput (tm : MultiTapeTM k Symbol State) (f : Symbol → Symbol)
    (cfg : Cfg k Symbol State input) (time : ℕ) :
    (tm.mapOutput f).runFrom (cfg.mapOutput f) time =
      (tm.runFrom cfg time).mapOutput f :=
  (Function.Semiconj.iterate_right (f := fun cfg : Cfg k Symbol State input => cfg.mapOutput f)
    (ga := tm.step) (gb := (tm.mapOutput f).step)
    (fun cfg => (step_mapOutput tm f cfg).symm) time cfg).symm

end MultiTapeTM

end Turing
