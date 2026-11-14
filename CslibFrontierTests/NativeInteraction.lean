/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Computability.Probabilistic.NativeInterface.Interaction
import Mathlib.Tactic

/-!
# Actual native query selection, resource observations and private output coins

The three-instruction program writes a true query bit, issues that actual buffer,
then flips a fresh private output coin. The source's hidden fair bit controls an
invoice and duration while its answer word stays empty. The complete history
therefore distinguishes source information absent from the answer word, and
separates a real zero-resource query from no-call padding.
-/

public section
noncomputable section
namespace CslibFrontierTests.NativeInteraction
open Cslib.Probability Turing Turing.MultiTapeMachine Turing.MultiTapeTM
open NativeOpenExecution NativeInterface
open scoped NNReal ENNReal

open NativeInterface.Interaction

/-- A genuine query-buffer write, external call, and post-response private coin. -/
def machine : MultiTapePTM 0 Bool (Fin 3) Unit where
  initial := 0
  tr c _ _ _ bit := if c = 1 then .query () 2 else .step
    { inputTape := 0, workTapes := Fin.elim0,
      output := if c = 2 then some bit else none,
      state := if c = 0 then some 1 else none }
    (fun _ => if c = 0 then some true else none) (fun _ => 0)

/-- A resource-bearing reply and a genuine zero-resource reply have the same empty word. -/
def reply (hidden : Bool) : Reply := if hidden then ⟨[], 2, 1⟩ else ⟨[], 0, 0⟩

/-- Positive charges arise only for the actual preformed word `[true]`. -/
def env : Environment Unit Bool := fun q memory =>
  PMF.pure ((if q.2 = [true] then reply memory.privateState else reply false), memory.privateState)

/-- The source samples its hidden bit independently of all subsequent native coins. -/
def initial : PMF (Memory Unit Bool) :=
  (PMF.uniformOfFintype Bool).map fun s => ⟨s, []⟩

/-- Concrete native configuration with its actual Unit query buffer. -/
def config (c : Option (Fin 3)) (query out : List Bool) : Config 0 Bool (Fin 3) Unit [] :=
  ⟨{ Cfg.init 0 [] with state := c, output := out }, fun _ => ⟨query, [], 0⟩⟩

/-- Actual initial source memory for one hidden bit. -/
def realMemory (s : Bool) : Memory Unit Bool := ⟨s, []⟩
/-- Real source memory after the actually encoded query. -/
def realAfter (s : Bool) : Memory Unit Bool :=
  (realMemory s).record ((), [true]) (reply s) s
private def dummyAfter (s : Bool) : Memory Unit Unit :=
  (⟨(), []⟩ : Memory Unit Unit).record ((), [true]) (reply s) ()

/-- Full newest-first history, including the real zero-resource query when `s=false`. -/
def history (s : Bool) : List (Option (Unit × List Bool) × Reply) :=
  [(none, reply false), (some ((), [true]), reply s), (none, reply false)]

private def state0 (s : Bool) : NativeInterface.Interaction.State 0 (Fin 3) Unit Bool [] :=
  ⟨[], .ready ⟨config (some 0) [] [], ⟨(), []⟩⟩, realMemory s⟩
private def state1 (s : Bool) : NativeInterface.Interaction.State 0 (Fin 3) Unit Bool [] :=
  ⟨[(none, reply false)], .ready ⟨config (some 1) [true] [], ⟨(), []⟩⟩, realMemory s⟩
private def state2 (s : Bool) : NativeInterface.Interaction.State 0 (Fin 3) Unit Bool [] :=
  ⟨[(some ((), [true]), reply s), (none, reply false)],
    .ready ⟨config (some 2) [] [], dummyAfter s⟩, realAfter s⟩
private def state3 (s bit : Bool) : NativeInterface.Interaction.State 0 (Fin 3) Unit Bool [] :=
  ⟨history s, .ready ⟨config none [] [bit], dummyAfter s⟩, realAfter s⟩

private def actualPolicy := policy machine (machine.initialConfig [])
private def actualSource := source env initial

private theorem initial_law : InteractionProcess.initialLaw actualPolicy actualSource =
    (PMF.uniformOfFintype Bool).map state0 := by
  simp only [InteractionProcess.initialLaw, actualPolicy, actualSource, policy, source,
    PMF.pure_bind, initial, PMF.map_comp, Function.comp_def]
  rfl

private theorem instruction_write (bit : Bool) :
    instruction machine (⟨config (some 0) [] [], ⟨(), []⟩⟩ : World 0 (Fin 3) Unit Unit []) bit =
      .local ⟨config (some 1) [true] [], ⟨(), []⟩⟩ := by
  simp only [instruction, config, machine, Fin.isValue]
  norm_num [Config.step, Action.apply, Cfg.init]
  constructor <;> funext i <;> exact Fin.elim0 i

private theorem instruction_output (s bit : Bool) :
    instruction machine (⟨config (some 2) [] [], dummyAfter s⟩ : World 0 (Fin 3) Unit Unit []) bit =
      .local ⟨config none [] [bit], dummyAfter s⟩ := by
  simp only [instruction, config, machine, Fin.isValue]
  norm_num [Config.step, Action.apply, Cfg.init]
  constructor <;> funext i <;> exact Fin.elim0 i

private theorem step0 (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state0 s) = PMF.pure (state1 s) := by
  simp [InteractionProcess.step, actualPolicy, actualSource, policy, source,
    state0, state1, worldOf, prepare, instruction_write, request, response,
    dispatch, reply, PMF.bind_map, PMF.map_comp, Function.comp_def]

private theorem step1 (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state1 s) = PMF.pure (state2 s) := by
  cases s <;> simp [InteractionProcess.step, actualPolicy, actualSource, policy, source,
    state1, state2, worldOf, prepare, instruction, machine, request, response,
    dispatch, env, realMemory, realAfter, dummyAfter, reply, config, Config.receive,
    Function.update_eq_const_of_subsingleton, PMF.bind_map,
    PMF.map_comp, Function.comp_def]
  all_goals rfl

private theorem step2 (s : Bool) :
    InteractionProcess.step actualPolicy actualSource (state2 s) =
      (PMF.uniformOfFintype Bool).map (state3 s) := by
  simp [InteractionProcess.step, actualPolicy, actualSource, policy, source,
    state2, state3, history, worldOf, prepare, instruction_output, request, response,
    dispatch, reply, PMF.map, Function.comp_def]

private theorem process_three : InteractionProcess.law actualPolicy actualSource 3 =
    (PMF.uniformOfFintype Bool).bind fun s =>
      (PMF.uniformOfFintype Bool).map (state3 s) := by
  rw [InteractionProcess.law_succ, InteractionProcess.law_succ, InteractionProcess.law_succ]
  simp only [InteractionProcess.law, ObservedProcess.stateLaw, PMF.bind_pure, initial_law,
    PMF.bind_map, step0, PMF.pure_bind, step1, step2, PMF.bind_bind, Function.comp_def]

/-- Exact actual three-tick history, native output configuration and source memory. -/
theorem execution_three : execution machine env initial (machine.initialConfig []) 3 =
    (PMF.uniformOfFintype Bool).bind fun s =>
      (PMF.uniformOfFintype Bool).map fun bit =>
        (history s, (⟨config none [] [bit], realAfter s⟩ : World 0 (Fin 3) Unit Bool [])) := by
  change (InteractionProcess.law actualPolicy actualSource 3).map
    (fun state => (state.history, world state)) = _
  rw [process_three]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]
  rfl

/-- The native interpreter itself has the same joint final world and private output coin. -/
theorem actual_world_law :
    (initial.bind fun memory => execute machine env 3 ⟨machine.initialConfig [], memory⟩) =
      (PMF.uniformOfFintype Bool).bind fun s =>
        (PMF.uniformOfFintype Bool).map fun bit =>
          (⟨config none [] [bit], realAfter s⟩ : World 0 (Fin 3) Unit Bool []) := by
  rw [← execution_native machine env initial (machine.initialConfig []) 3, execution_three]
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def]

/-- The complete invoice history is genuinely reached for each hidden source bit. -/
theorem reached (s : Bool) :
    history s ∈ ((execution machine env initial (machine.initialConfig []) 3).map
      Prod.fst).support := by
  rw [execution_three, PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  apply (PMF.mem_support_bind_iff _ _ _).mpr
  refine ⟨s, by simp, ?_⟩
  apply (PMF.mem_support_map_iff _ _ _).mpr
  exact ⟨false, by simp, rfl⟩

private theorem history_injective : Function.Injective history := by
  intro a b h
  cases a <;> cases b <;> first | rfl | norm_num [history, reply] at h

/-- The complete invoice-bearing history identifies actual source memory, despite an empty word. -/
theorem memory_posterior (s : Bool) :
    (PMF.conditionalSnd (execution machine env initial (machine.initialConfig []) 3)
      (history s)).map World.memory = PMF.pure (realAfter s) := by
  calc
    _ = (PMF.conditionalSnd (execution machine env initial (machine.initialConfig []) 3)
        (history s)).map (fun _ => realAfter s) := by
      apply PMF.map_congr_on_support
      intro w hw
      have hj := (PMF.mem_support_conditionalSnd_iff _ _ (reached s) w).mp hw
      rw [execution_three] at hj
      obtain ⟨t, _, ht⟩ := (PMF.mem_support_bind_iff _ _ _).mp hj
      obtain ⟨bit, _, he⟩ := (PMF.mem_support_map_iff _ _ _).mp ht
      have hs : t = s := history_injective (congrArg Prod.fst he)
      subst t
      exact congrArg World.memory (congrArg Prod.snd he).symm
    _ = _ := PMF.map_const _ _

/-- The same machine-independent source filter recovers that derived native posterior. -/
theorem common_source_filter (s : Bool) :
    (source env initial).filter (history s) = PMF.pure (realAfter s) := by
  rw [← source_posterior machine env initial (machine.initialConfig []) 3 (history s) (reached s)]
  exact memory_posterior s

/-- Private output changes the actual tape while preserving the complete resource receipt. -/
example (s bit : Bool) :
    (config none [] [bit]).tapes.output = [bit] ∧
      tokenBill (realAfter s).events = (reply s).tokens ∧
      elapsed (realAfter s).events = (reply s).duration := by
  simp [config, realAfter, realMemory, Memory.record, tokenBill, elapsed]

-- The real zero-resource query is still a selected query, not no-call padding.
example : (history false)[1]? = some (some ((), [true]), reply false) ∧
    (history false)[0]? = some (none, reply false) ∧
    (reply true).tokens = 2 ∧ (reply true).duration = 1 := by
  norm_num [history, reply]

end CslibFrontierTests.NativeInteraction
