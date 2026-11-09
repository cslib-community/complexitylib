/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.OutputPrefix
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.WordsCfg

/-!
# Retaining a charged prefix in counting computations

A tidy deterministic preparation restores the input head and blank work tapes after writing
a prefix. Its singleton lift then runs the counting machine without changing any occurrence.
Every preparation transition is included in the sum of the two native clocks.

## Main results

* `Turing.MultiTapeCTM.runList_prependOutput`: unreadable output preserves all occurrences.
* `Turing.MultiTapeCTM.runList_seq_prependOutput`: retain a natively prepared prefix.
* `Turing.MultiTapeCTM.haltsWithin_seq_prependOutput`: charge preparation and computation.

## References

The construction follows `MultiTape.Probabilistic.OutputPrefix`, adapted there from the cslib
`crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`. The singleton lift here
preserves exact multiplicity in addition to the output behavior.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State State₀ State₁ : Type} {input : List Symbol}

/-- Changing the unreadable output retains every subsequent configuration occurrence. -/
theorem runList_prependOutput (machine : MultiTapeCTM k Symbol State)
    (fuel : ℕ) (cfg : Cfg k Symbol State input) (pre : List Symbol) :
    machine.runList fuel (cfg.prependOutput pre) =
      (machine.runList fuel cfg).map (fun final => final.prependOutput pre) := by
  have h := congrArg
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n)))
    (MultiTapeMachine.runConfigFrom_prependOutput machine chooseOccurrence Empty.elim fuel
      (Config.emptyOracleEquiv.symm cfg) pre)
  have hm := congrArg (List.map Config.tapes) h
  simpa [interpret_runConfigFrom_eq_map_runList, OracleComp.interpret_map,
    List.map_map, Function.comp_def, Config.emptyOracleEquiv, Config.prependOutput] using hm

/-- A prefix changes no halting decision or clock, provided the transition table is nonblocking. -/
theorem HaltsWithin.prependOutput {machine : MultiTapeCTM k Symbol State}
    (hnon : machine.Nonblocking) {fuel : ℕ} {cfg : Cfg k Symbol State input}
    (h : machine.HaltsWithin fuel cfg) (pre : List Symbol) :
    machine.HaltsWithin fuel (cfg.prependOutput pre) := by
  apply haltsWithin_of_halted _ hnon.actions_ne_nil
  intro final hfinal
  rw [runList_prependOutput] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hfinal
  change original.state = none
  exact h.halted_of_mem_runList horiginal

variable (prepare : MultiTapeTM k Symbol State₀) (source : MultiTapeCTM k Symbol State₁)
  (hnon : source.Nonblocking) (input pre : List Symbol) (prepareTime runTime : ℕ)
  (hprepare : prepare.runFrom (prepare.initCfg input) prepareTime =
    wordsCfg input none (fun _ => []) pre)
  (hsource : source.HaltsWithin runTime (source.initialConfig input).tapes)

include hnon hprepare hsource

/-- Workspace-restoring singleton preparation retains the prefix and every source occurrence. -/
theorem runList_seq_prependOutput :
    runList ((ofDeterministic prepare).seq source) (prepareTime + runTime)
        (((ofDeterministic prepare).seq source).initialConfig input).tapes =
      (source.runList runTime (source.initialConfig input).tapes).map
        (fun final => (final.prependOutput pre).mapState (Option.map Sum.inr)) := by
  let cfg : Config k Symbol State₀ Empty input := (ofDeterministic prepare).initialConfig input
  have hfirst : (ofDeterministic prepare).runList prepareTime cfg.tapes =
      [wordsCfg input none (fun _ => []) pre] := by
    rw [runList_ofDeterministic]
    exact congrArg List.singleton hprepare
  have hhalt : (ofDeterministic prepare).HaltsWithin prepareTime cfg.tapes := by
    rw [haltsWithin_ofDeterministic_iff]
    change (prepare.runFrom (prepare.initCfg input) prepareTime).Halted
    rw [hprepare]
    rfl
  have hstart : (wordsCfg input (none : Option State₀) (fun _ => []) pre).withState
      (some source.initial) = (source.initialConfig input).tapes.prependOutput pre := by
    simp [initialConfig, Cfg.prependOutput, wordsCfg, Cfg.withState]
  have hsecond : ∀ result ∈ (ofDeterministic prepare).runList prepareTime cfg.tapes,
      source.HaltsWithin runTime (result.withState (some source.initial)) := by
    intro result hresult
    have hr : result = wordsCfg input none (fun _ => []) pre := by
      simpa [hfirst] using hresult
    rw [hr, hstart]
    exact hsource.prependOutput hnon pre
  change runList ((ofDeterministic prepare).seq source) _
    (Sequential.left source cfg).tapes = _
  rw [runList_seq _ _ _ prepareTime runTime hhalt hsecond, hfirst,
    List.flatMap_singleton, hstart, runList_prependOutput, List.map_map]
  rfl

/-- The actual prepared-prefix machine halts within the sum of the two charged clocks. -/
theorem haltsWithin_seq_prependOutput :
    MultiTapeCTM.HaltsWithin ((ofDeterministic prepare).seq source) (prepareTime + runTime)
      (((ofDeterministic prepare).seq source).initialConfig input).tapes := by
  apply haltsWithin_of_halted _ ((nonblocking_ofDeterministic prepare).seq hnon).actions_ne_nil
  intro final hfinal
  rw [runList_seq_prependOutput prepare source hnon input pre prepareTime runTime
    hprepare hsource] at hfinal
  obtain ⟨original, horiginal, rfl⟩ := List.mem_map.mp hfinal
  change original.state.map Sum.inr = none
  rw [hsource.halted_of_mem_runList horiginal]
  rfl

end Turing.MultiTapeCTM
