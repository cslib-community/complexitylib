/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.ExtendTapes
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Sequential
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Composition

/-!
# Count-preserving buffered machine composition

The shared compiler redirects each source output symbol to a work tape in the same transition.
The singleton deterministic lift rewinds that buffer and marks its boundary in the word length
plus four transitions. The consumer then reads the buffered word with separate blank work tapes.
Source scratch and the real input head are retained; preparation introduces exactly one path.

The complete compiler is closed, with no oracle channels. Its native occurrence counts compose
by List bind, and its all-branches clock is `T₀ + (T₀ + 4 + T₁)` from initialized tapes. The
initial output is empty here; the general output-growth lemma retains its initial length.

## Main definitions

* `Turing.MultiTapeCTM.comp`: feed one counting machine's output to another.

## Main results

* `Turing.MultiTapeCTM.runList_comp`: the exact complete-configuration composition law.
* `Turing.MultiTapeCTM.HaltsWithin.comp`: the charged native all-branches clock.
* `Turing.MultiTapeCTM.branchCount_comp`: exact native counts through buffered composition.

## References

The tape layout and native preparation are shared with `MultiTape.Machine.Composition`;
that module records the original deterministic and probabilistic compiler sources.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib MultiTapeMachine MultiTapeMachine.Composition

variable {k k' k₀ k₁ : ℕ} {Symbol State State₀ State₁ : Type} {input : List Symbol}

/-- Output redirection does not introduce empty transition lists. -/
theorem Nonblocking.outputToTape {machine : MultiTapeCTM k Symbol State}
    (h : machine.Nonblocking) : Nonblocking machine.outputToTape := by
  intro state symbol work
  simpa [MultiTapeMachine.outputToTape] using h state symbol (fun i => work i.castSucc)

/-- Virtual input redirection does not introduce empty transition lists. -/
theorem Nonblocking.inputFromTape {machine : MultiTapeCTM k Symbol State}
    (h : machine.Nonblocking) : Nonblocking machine.inputFromTape := by
  intro state symbol work
  simpa [MultiTapeMachine.inputFromTape] using
    h state (work (Fin.natAdd k 0)) (fun i => work (i.castAdd 2))

namespace Composition

/-- Rewind and mark the buffered word with exactly one path, then start the consumer. -/
noncomputable def continuation (machine : MultiTapeCTM k₁ Symbol State₁) (k₀ : ℕ)
    (mark : Symbol) : MultiTapeCTM (k₁ + k₀ + 2) Symbol
      ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁) :=
  (ofDeterministic (MultiTapeTM.prepareInput (k₁ + k₀) mark)).seq (consumer machine k₀)

/-- Source buffering preserves every configuration occurrence. -/
theorem runList_source (machine : MultiTapeCTM k₀ Symbol State₀) (k₁ fuel : ℕ)
    (input : List Symbol) :
    runList (source machine k₁) fuel ((source machine k₁).initialConfig input).tapes =
      (machine.runList fuel (machine.initialConfig input).tapes).map
        (fun cfg => (buffer k₁ (Config.emptyOracleEquiv.symm cfg)).tapes) := by
  have h := congrArg
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n)))
    (runConfigFrom_source chooseOccurrence chooseOccurrence_map machine k₁ fuel input)
  have hm := congrArg (List.map Config.tapes) h
  simpa [interpret_runConfigFrom_eq_map_runList, OracleComp.interpret_map,
    List.map_map, Function.comp_def, Config.emptyOracleEquiv] using hm

/-- The consumer keeps every source scratch cell and every continuation occurrence. -/
theorem runList_consumer (machine : MultiTapeCTM k₁ Symbol State₁) (mark : Symbol)
    (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) (fuel : ℕ) :
    runList (consumer machine k₀) fuel (consumerConfig mark cfg₀ cfg₁).tapes =
      (machine.runList fuel cfg₁.tapes).map
        (fun cfg => (consumerConfig mark cfg₀ (Config.emptyOracleEquiv.symm cfg)).tapes) := by
  have h := congrArg
    (OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n)))
    (runConfigFrom_consumer chooseOccurrence chooseOccurrence_map machine mark cfg₀ cfg₁ fuel)
  have hm := congrArg (List.map Config.tapes) h
  simpa [interpret_runConfigFrom_eq_map_runList, OracleComp.interpret_map,
    List.map_map, Function.comp_def, Config.emptyOracleEquiv] using hm

/-- Buffering the source preserves the explicit no-stuck table condition. -/
theorem nonblocking_source {machine : MultiTapeCTM k₀ Symbol State₀}
    (h : machine.Nonblocking) (k₁ : ℕ) : Nonblocking (source machine k₁) :=
  ((h.extendTapes _).outputToTape).extendTapes _

/-- The virtual-input consumer preserves the explicit no-stuck table condition. -/
theorem nonblocking_consumer {machine : MultiTapeCTM k₁ Symbol State₁}
    (h : machine.Nonblocking) (k₀ : ℕ) : Nonblocking (consumer machine k₀) :=
  (h.extendTapes _).inputFromTape

/-- Singleton preparation and a nonblocking consumer have no stuck local views. -/
theorem nonblocking_continuation {machine : MultiTapeCTM k₁ Symbol State₁}
    (h : machine.Nonblocking) (k₀ : ℕ) (mark : Symbol) :
    (continuation machine k₀ mark).Nonblocking :=
  (nonblocking_ofDeterministic _).seq (nonblocking_consumer h k₀)

/-- A native consumer clock survives the exact tape embedding. -/
theorem haltsWithin_consumer {machine : MultiTapeCTM k₁ Symbol State₁}
    (hnon : machine.Nonblocking) (mark : Symbol)
    (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) (fuel : ℕ)
    (h : machine.HaltsWithin fuel cfg₁.tapes) :
    MultiTapeCTM.HaltsWithin (consumer machine k₀) fuel
      (consumerConfig mark cfg₀ cfg₁).tapes := by
  apply haltsWithin_of_halted _ (nonblocking_consumer hnon k₀).actions_ne_nil
  intro final hfinal
  rw [runList_consumer] at hfinal
  obtain ⟨result, hresult, rfl⟩ := List.mem_map.mp hfinal
  exact h.halted_of_mem_runList hresult

/-- The charged handoff has one path and then preserves the consumer's complete configuration. -/
theorem runList_continuation (machine : MultiTapeCTM k₁ Symbol State₁)
    (hnon : machine.Nonblocking) (mark : Symbol)
    (cfg : Config k₀ Symbol State₀ Empty input) (prepareTime runTime : ℕ)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : machine.HaltsWithin runTime (machine.initialConfig cfg.tapes.output).tapes) :
    (continuation machine k₀ mark).runList (prepareTime + runTime)
        (Sequential.start (continuation machine k₀ mark) (buffer k₁ cfg)).tapes =
      (machine.runList runTime (machine.initialConfig cfg.tapes.output).tapes).map
        (fun final => (Sequential.right
          (consumerConfig mark cfg (Config.emptyOracleEquiv.symm final))).tapes) := by
  let prep := MultiTapeTM.prepareInput (k₁ + k₀) mark
  let initial := Sequential.start (ofDeterministic prep) (buffer k₁ cfg)
  have hdet := runFrom_prepare mark k₁ cfg
  change prep.runFrom initial.tapes (cfg.tapes.output.length + 4) = _ at hdet
  have hprep : prep.runFrom initial.tapes prepareTime = (ready mark k₁ cfg).tapes := by
    rw [prep.runFrom_eq_of_halt initial.tapes hprepare (by rw [hdet]; rfl), hdet]
  have hstate : (ofDeterministic prep).runList prepareTime initial.tapes =
      [(ready mark k₁ cfg).tapes] := by
    rw [runList_ofDeterministic, hprep]
  have hhalt : (ofDeterministic prep).HaltsWithin prepareTime initial.tapes := by
    rw [haltsWithin_ofDeterministic_iff, hprep]
    rfl
  have hstart := congrArg Config.tapes (start_ready machine mark cfg)
  change (ready mark k₁ cfg).tapes.withState (some (consumer machine k₀).initial) = _ at hstart
  have hconsumer : ∀ result ∈ (ofDeterministic prep).runList prepareTime initial.tapes,
      MultiTapeCTM.HaltsWithin (consumer machine k₀) runTime
        (result.withState (some (consumer machine k₀).initial)) := by
    intro result hresult
    have hr : result = (ready mark k₁ cfg).tapes := by simpa [hstate] using hresult
    rw [hr, hstart]
    exact haltsWithin_consumer hnon mark cfg _ runTime hrun
  change runList ((ofDeterministic prep).seq (consumer machine k₀)) _
    (Sequential.left (consumer machine k₀) initial).tapes = _
  rw [runList_seq _ _ _ prepareTime runTime hhalt hconsumer, hstate,
    List.flatMap_singleton, hstart, runList_consumer, List.map_map]
  rfl

/-- The singleton handoff and consumer halt natively within the charged combined bound. -/
theorem haltsWithin_continuation (machine : MultiTapeCTM k₁ Symbol State₁)
    (hnon : machine.Nonblocking) (mark : Symbol)
    (cfg : Config k₀ Symbol State₀ Empty input) (prepareTime runTime : ℕ)
    (hprepare : cfg.tapes.output.length + 4 ≤ prepareTime)
    (hrun : machine.HaltsWithin runTime (machine.initialConfig cfg.tapes.output).tapes) :
    (continuation machine k₀ mark).HaltsWithin (prepareTime + runTime)
      (Sequential.start (continuation machine k₀ mark) (buffer k₁ cfg)).tapes := by
  apply haltsWithin_of_halted _ (nonblocking_continuation hnon k₀ mark).actions_ne_nil
  intro final hfinal
  rw [runList_continuation machine hnon mark cfg prepareTime runTime hprepare hrun] at hfinal
  obtain ⟨result, hresult, rfl⟩ := List.mem_map.mp hfinal
  change result.state.map Sum.inr = none
  rw [hrun.halted_of_mem_runList hresult]
  rfl

end Composition

/-- Feed `first`'s output to `second`, with distinct work tapes and a singleton charged handoff. -/
noncomputable def comp (second : MultiTapeCTM k₁ Symbol State₁)
    (first : MultiTapeCTM k₀ Symbol State₀) (mark : Symbol) :
    MultiTapeCTM (k₁ + k₀ + 2) Symbol
      (State₀ ⊕ ((MultiTapeTM.MarkWorkState ⊕ MultiTapeTM.RewindWorkState) ⊕ State₁)) :=
  (source first k₁).seq (Composition.continuation second k₀ mark)

/-- Buffered composition has no stuck views when both component tables are nonblocking. -/
theorem Nonblocking.comp {first : MultiTapeCTM k₀ Symbol State₀}
    {second : MultiTapeCTM k₁ Symbol State₁} (hfirst : first.Nonblocking)
    (hsecond : second.Nonblocking) (mark : Symbol) : (second.comp first mark).Nonblocking :=
  (Composition.nonblocking_source hfirst k₁).seq
    (Composition.nonblocking_continuation hsecond k₀ mark)

section CompositionLaws

variable (first : MultiTapeCTM k₀ Symbol State₀) (second : MultiTapeCTM k₁ Symbol State₁)
  (hnonfirst : first.Nonblocking) (hnonsecond : second.Nonblocking)
  (mark : Symbol) (input : List Symbol) (firstTime secondTime : ℕ)
  (hfirst : first.HaltsWithin firstTime (first.initialConfig input).tapes)
  (hsecond : ∀ result ∈ first.runList firstTime (first.initialConfig input).tapes,
    second.HaltsWithin secondTime (second.initialConfig result.output).tapes)

include hnonfirst hnonsecond hfirst hsecond

/-- Exact full-configuration composition, including scratch and input-head preservation.
Both machines start with empty output. Each source instruction emits at most one symbol, so
preparation takes at most `firstTime + 4`; it is not a free conversion between machine models. -/
theorem runList_comp :
    (second.comp first mark).runList (firstTime + (firstTime + 4 + secondTime))
        ((second.comp first mark).initialConfig input).tapes =
      (first.runList firstTime (first.initialConfig input).tapes).flatMap (fun result =>
        (second.runList secondTime (second.initialConfig result.output).tapes).map
          (fun final => (finalConfig mark (Config.emptyOracleEquiv.symm result)
            (Config.emptyOracleEquiv.symm final)).tapes)) := by
  have hlength (result : Cfg k₀ Symbol State₀ input)
      (hresult : result ∈ first.runList firstTime (first.initialConfig input).tapes) :
      result.output.length ≤ firstTime := by
    simpa only [initialConfig, Cfg.init, List.length_nil, Nat.zero_add] using
      first.length_output_of_mem_runList firstTime _ result hresult
  have hsource : MultiTapeCTM.HaltsWithin (source first k₁) firstTime
      ((source first k₁).initialConfig input).tapes := by
    apply haltsWithin_of_halted _ (Composition.nonblocking_source hnonfirst k₁).actions_ne_nil
    intro final hfinal
    rw [Composition.runList_source] at hfinal
    obtain ⟨result, hresult, rfl⟩ := List.mem_map.mp hfinal
    exact hfirst.halted_of_mem_runList hresult
  have hcontinuation : ∀ result ∈ runList (source first k₁) firstTime
      ((source first k₁).initialConfig input).tapes,
      (Composition.continuation second k₀ mark).HaltsWithin (firstTime + 4 + secondTime)
        (result.withState (some (Composition.continuation second k₀ mark).initial)) := by
    intro final hfinal
    rw [Composition.runList_source] at hfinal
    obtain ⟨result, hresult, rfl⟩ := List.mem_map.mp hfinal
    exact Composition.haltsWithin_continuation second hnonsecond mark _
      (firstTime + 4) secondTime (by
        change result.output.length + 4 ≤ firstTime + 4
        exact Nat.add_le_add_right (hlength result hresult) 4)
      (hsecond result hresult)
  change runList ((source first k₁).seq (Composition.continuation second k₀ mark)) _
    (Sequential.left (Composition.continuation second k₀ mark)
      ((source first k₁).initialConfig input)).tapes = _
  rw [runList_seq _ _ _ firstTime (firstTime + 4 + secondTime) hsource hcontinuation,
    Composition.runList_source, List.flatMap_map]
  apply List.flatMap_congr
  intro result hresult
  change List.map _ ((Composition.continuation second k₀ mark).runList _
    (Sequential.start (Composition.continuation second k₀ mark)
      (buffer k₁ (Config.emptyOracleEquiv.symm result))).tapes) = _
  rw [Composition.runList_continuation second hnonsecond mark _ (firstTime + 4) secondTime
    (by
      change result.output.length + 4 ≤ firstTime + 4
      exact Nat.add_le_add_right (hlength result hresult) 4) (hsecond result hresult),
    List.map_map]
  rfl

/-- The compiled machine halts on every native branch within the charged combined clock. -/
theorem HaltsWithin.comp :
    (second.comp first mark).HaltsWithin (firstTime + (firstTime + 4 + secondTime))
      ((second.comp first mark).initialConfig input).tapes := by
  apply haltsWithin_of_halted _ (hnonfirst.comp hnonsecond mark).actions_ne_nil
  intro final hfinal
  rw [runList_comp first second hnonfirst hnonsecond mark input firstTime secondTime
    hfirst hsecond] at hfinal
  obtain ⟨source, hsource, hfinal⟩ := List.mem_flatMap.mp hfinal
  obtain ⟨target, htarget, rfl⟩ := List.mem_map.mp hfinal
  change (target.state.map Sum.inr).map Sum.inr = none
  rw [(hsecond source hsource).halted_of_mem_runList htarget]
  rfl

/-- Native terminal counts compose by summing the consumer count once per source occurrence.
The sum is over a List, so duplicate source configurations retain their exact multiplicity. -/
theorem branchCount_comp (verdict : List Symbol → Bool) :
    (second.comp first mark).branchCount verdict (firstTime + (firstTime + 4 + secondTime))
        ((second.comp first mark).initialConfig input).tapes =
      ((first.runList firstTime (first.initialConfig input).tapes).map
        (fun result => second.branchCount verdict secondTime
          (second.initialConfig result.output).tapes)).sum := by
  rw [← countP_runList, runList_comp first second hnonfirst hnonsecond mark input
    firstTime secondTime hfirst hsecond, List.countP_flatMap]
  simp only [List.countP_map, Function.comp_def, finalConfig, Sequential.right,
    consumerConfig, InputFromTape.config, Config.embed, MultiTapeTM.inCfg,
    MultiTapeTM.embed_castAdd, Config.emptyOracleEquiv, Cfg.mapState, Option.isNone_map]
  change ((first.runList firstTime (first.initialConfig input).tapes).map (fun result =>
    (second.runList secondTime (second.initialConfig result.output).tapes).countP
      (fun final => final.state.isNone && verdict final.output))).sum = _
  simp only [countP_runList]

end CompositionLaws

end Turing.MultiTapeCTM
