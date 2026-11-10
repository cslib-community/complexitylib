/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Counting.Program
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact List interpretation of native counting runs

This module connects List interpretation of the existing shared FreeM program to the native
occurrence-labelled terminal-branch counts. Repeated final configurations retain their list
multiplicity. Running endpoints are filtered out; an empty running choice list remains stuck.
The interpreter is an auxiliary mathematical observation, not an uncharged machine instruction.

## Main definitions

* `Turing.MultiTapeCTM.runList`: List interpretation of the shared clocked run program.

## Main results

* `Turing.MultiTapeCTM.branchCount_succ`: terminal counts sum over transition occurrences.
* `Turing.MultiTapeCTM.countP_runList`: List interpretation equals the native terminal count.
* `Turing.MultiTapeCTM.haltsWithin_of_halted`: terminal endpoints imply a native halting bound
  when stuck local views are excluded.

## References

The common program and occurrence handler are developed in `MultiTape.Counting.Program`.
Native labelled branches and their source credit are in `MultiTape.Counting`.
-/

@[expose] public section

namespace Turing.MultiTapeCTM

open Cslib

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- Interpret the existing clocked FreeM program by enumerating each finite response once. -/
def runList (machine : MultiTapeCTM k Symbol State) (fuel : ℕ)
    (cfg : Cfg k Symbol State input) : List (Cfg k Symbol State input) :=
  OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n)) (machine.runProgram fuel cfg)

/-- The closed shared-configuration interpreter is the same List, with empty channels restored. -/
theorem interpret_runConfigFrom_eq_map_runList (machine : MultiTapeCTM k Symbol State)
    (fuel : ℕ) (cfg : MultiTapeMachine.Config k Symbol State Empty input) :
    OracleComp.interpret (fun n => List.ofFn (id : Fin n → Fin n))
        (machine.runConfigFrom chooseOccurrence Empty.elim fuel cfg) =
      (machine.runList fuel cfg.tapes).map MultiTapeMachine.Config.emptyOracleEquiv.symm := by
  simp only [runList, runProgram, OracleComp.interpret_map, List.map_eq_map, List.map_map]
  have hinv : MultiTapeMachine.Config.emptyOracleEquiv.symm ∘
      (MultiTapeMachine.Config.tapes (k := k) (Symbol := Symbol) (State := State)
        (Oracle := Empty) (input := input)) = id :=
    funext MultiTapeMachine.Config.emptyOracleEquiv.left_inv
  rw [hinv, List.map_id]
  congr 2
  exact (MultiTapeMachine.Config.emptyOracleEquiv.left_inv cfg).symm

@[simp]
theorem runList_zero (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) : machine.runList 0 cfg = [cfg] := by
  simp [runList]

/-- Halting returns one occurrence of the configuration, for every remaining clock. -/
theorem runList_halted (machine : MultiTapeCTM k Symbol State)
    {cfg : Cfg k Symbol State input} (h : cfg.Halted) (fuel : ℕ) :
    machine.runList fuel cfg = [cfg] := by
  simp [runList, machine.runProgram_halted h]

/-- A live step enumerates every action occurrence before interpreting its continuation. -/
theorem runList_succ (machine : MultiTapeCTM k Symbol State)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) (state : State) (h : cfg.state = some state) :
    machine.runList (fuel + 1) cfg =
      (machine.actions cfg).flatMap (fun action => machine.runList fuel (action.apply cfg)) :=
  machine.interpret_runProgram_succ cfg fuel state h

/-- Pausing and resuming the shared program preserves every endpoint occurrence. -/
theorem runList_add (machine : MultiTapeCTM k Symbol State) (first second : ℕ)
    (cfg : Cfg k Symbol State input) :
    machine.runList (first + second) cfg =
      (machine.runList first cfg).flatMap (machine.runList second) := by
  induction first generalizing cfg with
  | zero => simp
  | succ first ih =>
    cases hs : cfg.state with
    | none => simp [machine.runList_halted hs]
    | some state =>
      rw [Nat.succ_add, machine.runList_succ cfg _ state hs,
        machine.runList_succ cfg first state hs, List.flatMap_assoc]
      simp only [ih]

/-- Once every endpoint has halted, extra clock steps add no choices or multiplicities. -/
theorem runList_add_of_halted (machine : MultiTapeCTM k Symbol State) (first second : ℕ)
    (cfg : Cfg k Symbol State input)
    (h : ∀ final ∈ machine.runList first cfg, final.Halted) :
    machine.runList (first + second) cfg = machine.runList first cfg := by
  rw [runList_add]
  calc
    _ = (machine.runList first cfg).flatMap (fun final => [final]) := by
      apply List.flatMap_congr
      intro final hmem
      exact machine.runList_halted (h final hmem) second
    _ = _ := by simp

/-- An all-branches bound ensures every interpreted endpoint really has halted. -/
theorem HaltsWithin.halted_of_mem_runList {machine : MultiTapeCTM k Symbol State}
    {fuel : ℕ} {cfg final : Cfg k Symbol State input} (h : machine.HaltsWithin fuel cfg)
    (hfinal : final ∈ machine.runList fuel cfg) : final.Halted := by
  induction h with
  | @halt fuel cfg hh =>
    have hsame : final = cfg := by simpa [machine.runList_halted hh] using hfinal
    simpa only [hsame] using hh
  | @step fuel cfg hnonempty hnext ih =>
    cases hs : cfg.state with
    | none =>
      have hsame : final = cfg := by simpa [machine.runList_halted hs] using hfinal
      simpa only [hsame] using hs
    | some state =>
      rw [machine.runList_succ cfg fuel state hs] at hfinal
      obtain ⟨action, haction, hfinal⟩ := List.mem_flatMap.mp hfinal
      obtain ⟨index, hi, rfl⟩ := List.mem_iff_getElem.mp haction
      exact ih ⟨index, hi⟩ hfinal

/-- A non-stuck machine whose clocked endpoints all halt has the native all-branches bound.
The no-stuck hypothesis matters: an empty choice list would otherwise satisfy the endpoint
condition vacuously. -/
theorem haltsWithin_of_halted (machine : MultiTapeCTM k Symbol State)
    (hnonempty : ∀ cfg : Cfg k Symbol State input,
      cfg.state ≠ none → machine.actions cfg ≠ []) (fuel : ℕ)
    (cfg : Cfg k Symbol State input)
    (h : ∀ final ∈ machine.runList fuel cfg, final.Halted) : machine.HaltsWithin fuel cfg := by
  induction fuel generalizing cfg with
  | zero => exact .halt (h cfg (by simp))
  | succ fuel ih =>
    cases hs : cfg.state with
    | none => exact .halt hs
    | some state =>
      apply HaltsWithin.step (hnonempty cfg (by simp [hs]))
      intro index
      apply ih
      intro final hfinal
      apply h final
      rw [machine.runList_succ cfg fuel state hs]
      exact List.mem_flatMap.mpr ⟨_, List.getElem_mem index.isLt, hfinal⟩

/-- Each actual instruction emits at most one symbol, including on a still-running branch. -/
theorem length_output_of_mem_runList (machine : MultiTapeCTM k Symbol State) (fuel : ℕ)
    (cfg final : Cfg k Symbol State input) (hfinal : final ∈ machine.runList fuel cfg) :
    final.output.length ≤ cfg.output.length + fuel := by
  induction fuel generalizing cfg with
  | zero =>
    have hsame : final = cfg := by simpa using hfinal
    simp [hsame]
  | succ fuel ih =>
    cases hs : cfg.state with
    | none =>
      have hsame : final = cfg := by simpa [machine.runList_halted hs] using hfinal
      simp [hsame]
    | some state =>
      rw [machine.runList_succ cfg fuel state hs] at hfinal
      obtain ⟨action, _, hfinal⟩ := List.mem_flatMap.mp hfinal
      have hrest := ih (action.apply cfg) hfinal
      have hstep : (action.apply cfg).output.length ≤ cfg.output.length + 1 := by
        simp only [Action.apply_output, List.length_append]
        exact Nat.add_le_add_left action.output.length_toList_le _
      lia

/-- Terminal counts sum over positions in the transition list, even when actions coincide. -/
theorem branchCount_succ (machine : MultiTapeCTM k Symbol State) (verdict : List Symbol → Bool)
    (cfg : Cfg k Symbol State input) (fuel : ℕ) (state : State) (h : cfg.state = some state) :
    machine.branchCount verdict (fuel + 1) cfg =
      ∑ index : Fin (machine.actions cfg).length,
        machine.branchCount verdict fuel ((machine.actions cfg)[index].apply cfg) := by
  have hfilter (index : Fin (machine.actions cfg).length) :
      ((machine.branches fuel ((machine.actions cfg)[index].apply cfg)).image
        (List.cons index.val)).filter
          (fun choices => (machine.runBranch cfg choices).any (fun final => verdict final.output)) =
      ((machine.branches fuel ((machine.actions cfg)[index].apply cfg)).filter
        (fun choices => (machine.runBranch ((machine.actions cfg)[index].apply cfg) choices).any
          (fun final => verdict final.output))).image (List.cons index.val) := by
    rw [Finset.filter_image]
    congr 1
    apply Finset.filter_congr
    intro choices _
    simp [runBranch_cons, step?]
  unfold branchCount
  simp only [branches, h, Finset.filter_biUnion, hfilter]
  rw [Finset.card_biUnion]
  · apply Finset.sum_congr rfl
    intro index _
    exact Finset.card_image_of_injective _ List.cons_injective
  · intro left _ right _ hne
    apply Finset.disjoint_left.mpr
    intro choices hleft hright
    obtain ⟨leftRest, _, hleft⟩ := Finset.mem_image.mp hleft
    obtain ⟨rightRest, _, hright⟩ := Finset.mem_image.mp hright
    exact hne (Fin.ext (List.cons.inj (hleft.trans hright.symm)).1)

/-- The List interpretation counts exactly the native terminal branches. Filtering for actual
halting is essential when the clock is insufficient or a branch is stuck. -/
theorem countP_runList (machine : MultiTapeCTM k Symbol State) (verdict : List Symbol → Bool)
    (fuel : ℕ) (cfg : Cfg k Symbol State input) :
    (machine.runList fuel cfg).countP (fun final => final.state.isNone && verdict final.output) =
      machine.branchCount verdict fuel cfg := by
  induction fuel generalizing cfg with
  | zero =>
    cases hs : cfg.state <;> cases hv : verdict cfg.output <;>
      simp [runList_zero, branchCount, branches, hs, Finset.filter_singleton, hv]
  | succ fuel ih =>
    cases hs : cfg.state with
    | none =>
      cases hv : verdict cfg.output <;>
        simp [machine.runList_halted hs, branchCount, machine.branches_of_halted hs, hs,
          Finset.filter_singleton, hv]
    | some state =>
      rw [machine.runList_succ cfg fuel state hs,
        machine.branchCount_succ verdict cfg fuel state hs, List.countP_flatMap]
      simp only [Function.comp_def, ih]
      rw [← List.sum_ofFn]
      congr 1
      apply List.ext_getElem <;> simp

/-- When all branches halt, counting output occurrences is exactly the native terminal count. -/
theorem HaltsWithin.branchCount_eq_countP {machine : MultiTapeCTM k Symbol State}
    {fuel : ℕ} {cfg : Cfg k Symbol State input} (h : machine.HaltsWithin fuel cfg)
    (verdict : List Symbol → Bool) :
    machine.branchCount verdict fuel cfg = (machine.runList fuel cfg).countP
      (fun final => verdict final.output) := by
  rw [← countP_runList]
  apply List.countP_congr
  intro final hfinal
  simp [h.halted_of_mem_runList hfinal]

end Turing.MultiTapeCTM
