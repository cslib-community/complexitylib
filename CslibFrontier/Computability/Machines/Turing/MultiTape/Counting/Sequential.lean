/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Execution
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Sequential

/-!
# Count-preserving shared-tape sequencing

The existing sequential compiler preserves List occurrences, including duplicate endpoints.
With nonblocking transition tables, the two native all-branches halting clocks add. This is
sequencing on the same tapes; preparing encoded inputs, copying and clearing remain charged
obligations of the buffered composition compiler.

## Main results

* `Turing.MultiTapeCTM.Nonblocking.seq`: the compiler introduces no stuck local views.
* `Turing.MultiTapeCTM.runList_seq`: exact List bind for the existing sequential compiler.
* `Turing.MultiTapeCTM.HaltsWithin.seq`: native all-branches clocks add.

## References

The shared compiler and its source credit are in `MultiTape.Machine.Sequential`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol State₀ State₁ : Type} {input : List Symbol}
  {first : MultiTapeCTM k Symbol State₀} {second : MultiTapeCTM k Symbol State₁}

/-- Sequencing maps each transition occurrence once and introduces no empty live choice lists. -/
theorem Nonblocking.seq (hfirst : first.Nonblocking) (hsecond : second.Nonblocking) :
    Nonblocking (first.seq second) := by
  rintro (state | state) symbol work
  · simpa [MultiTapeMachine.seq] using hfirst state symbol work
  · simpa [MultiTapeMachine.seq] using hsecond state symbol work

/-- Exact native List execution of shared-tape sequencing. Each first-phase occurrence runs its
own continuation, even when several first-phase occurrences have the same final configuration. -/
theorem runList_seq (first : MultiTapeCTM k Symbol State₀) (second : MultiTapeCTM k Symbol State₁)
    (cfg : Config k Symbol State₀ Empty input) (firstTime secondTime : ℕ)
    (hfirst : first.HaltsWithin firstTime cfg.tapes)
    (hsecond : ∀ result ∈ first.runList firstTime cfg.tapes,
      second.HaltsWithin secondTime (result.withState (some second.initial))) :
    runList (first.seq second) (firstTime + secondTime) (Sequential.left second cfg).tapes =
      (first.runList firstTime cfg.tapes).flatMap (fun result =>
        (second.runList secondTime (result.withState (some second.initial))).map
          (fun final => final.mapState (Option.map Sum.inr))) := by
  have h := MultiTapeMachine.interpret_runConfigFrom_seq_list first second
    chooseOccurrence chooseOccurrence_map Empty.elim
    (fun n => List.ofFn (id : Fin n → Fin n)) cfg firstTime secondTime
    (by
      rw [interpret_runConfigFrom_eq_map_runList]
      intro result hresult
      obtain ⟨native, hnative, rfl⟩ := List.mem_map.mp hresult
      exact hfirst.halted_of_mem_runList hnative)
    (by
      rw [interpret_runConfigFrom_eq_map_runList]
      intro result hresult
      obtain ⟨native, hnative, rfl⟩ := List.mem_map.mp hresult
      rw [interpret_runConfigFrom_eq_map_runList]
      intro final hfinal
      obtain ⟨nativeFinal, hnativeFinal, rfl⟩ := List.mem_map.mp hfinal
      exact (hsecond native hnative).halted_of_mem_runList hnativeFinal)
  have hm := congrArg (List.map Config.tapes) h
  simpa [interpret_runConfigFrom_eq_map_runList, List.map_flatMap, List.flatMap_map,
    List.map_map, Function.comp_def, Config.emptyOracleEquiv, Sequential.start,
    Sequential.right] using hm

/-- Under the explicit no-stuck table hypotheses, every sequential branch halts within the sum.
The conclusion is the native occurrence-labelled bound, not just a support condition. -/
theorem HaltsWithin.seq (hnonfirst : first.Nonblocking) (hnonsecond : second.Nonblocking)
    (cfg : Config k Symbol State₀ Empty input) (firstTime secondTime : ℕ)
    (hfirst : first.HaltsWithin firstTime cfg.tapes)
    (hsecond : ∀ result ∈ first.runList firstTime cfg.tapes,
      second.HaltsWithin secondTime (result.withState (some second.initial))) :
    MultiTapeCTM.HaltsWithin (first.seq second) (firstTime + secondTime)
      (Sequential.left second cfg).tapes := by
  apply haltsWithin_of_halted _ (hnonfirst.seq hnonsecond).actions_ne_nil
  intro final hfinal
  rw [runList_seq first second cfg firstTime secondTime hfirst hsecond] at hfinal
  obtain ⟨result, hresult, hfinal⟩ := List.mem_flatMap.mp hfinal
  obtain ⟨native, hnative, rfl⟩ := List.mem_map.mp hfinal
  change native.state.map Sum.inr = none
  rw [(hsecond result hresult).halted_of_mem_runList hnative]
  rfl

end Turing.MultiTapeCTM
