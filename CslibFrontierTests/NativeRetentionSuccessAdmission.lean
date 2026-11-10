/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchOptimum
import Mathlib.Tactic

/-!
# Successful-output provenance strictly enlarges native admission

A native two-step program issues no query and writes the unsupported singleton
row zero. That row fails to cover a satisfiable two-element original instance
(row one covers both elements). The actual execution is admitted under the
counted-success criterion, but fails all-output provenance. No supplied execution
or admission contract is used. This checks the competitor-class improvement;
it is not a new upper selector or a source representation theorem.
-/

noncomputable section
open Cslib Cslib.Probability Turing NativeOpenExecution StochasticOracle NativeRetention
open ConcurrentBatch NativeBatch
open Turing.MultiTapeTM

private abbrev data : GuardedStartup.Input :=
  ⟨⟨⟨[[0], [0, 1]], [1, 2], [1, 1], 1, []⟩, 1, 1, []⟩, 1⟩
private theorem valid : Valid data.startup.system := by
  constructor
  · intro j; rcases j with _ | (_ | j) <;> norm_num
  · intro e; rcases e with _ | (_ | e) <;> norm_num
  · intro j; rcases j with _ | (_ | j) <;> norm_num [elements, ground, List.range_succ]

private def machine : MultiTapePTM 0 Bool (Fin 2) Unit where
  initial := 0
  tr c _ _ _ _ := .step
    { inputTape := 0, workTapes := Fin.elim0,
      output := some (decide (c = 0)), state := if c = 0 then some 1 else none }
    (fun _ => none) (fun _ => 0)

private def world (c : Option (Fin 2)) (out : List Bool) :
    World 0 (Fin 2) Unit (ServerState 1 Unit) (GuardedStartup.encoding data) :=
  ⟨⟨{ Cfg.init 0 (GuardedStartup.encoding data) with state := c, output := out },
    fun _ => ⟨[], [], 0⟩⟩, ⟨ConcurrentBatch.initial (), []⟩⟩

private def limits : Limits 1 := ⟨fun _ => 1, by intro _; norm_num, 1, 1⟩

example (sample : Sampler 1 Unit) :
    let start := (⟨machine.initialConfig (GuardedStartup.encoding data),
      ⟨ConcurrentBatch.initial (), []⟩⟩ :
        World 0 (Fin 2) Unit (ServerState 1 Unit) (GuardedStartup.encoding data))
    NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := 1) 2) (decodeFamily 2)
      (BatchOutput.accept data.startup.system valid) start ∧
    ¬NativeUnboundedExecution.SelectionOnly machine (environment limits sample)
      (candidateParser (n := 1) 2) (decodeFamily 2) (fun _ => true) start ∧
    (instanceOf data.startup.system valid).covered {1} =
      (instanceOf data.startup.system valid).ground := by
  classical
  let env := environment limits sample
  have h0 : NativeOpenExecution.step machine env (world (some 0) []) =
      PMF.pure (world (some 1) [true]) := by
    simp only [NativeOpenExecution.step, world, machine,
      MultiTapeMachine.Config.step, Action.apply, moveInputPos_zero,
      Option.toList_some, Option.toList_none, List.append_nil,
      SignType.coe_zero, add_zero, PMF.bind_const]
    norm_num
    congr 4 <;> funext i <;> exact Fin.elim0 i
  have h1 : NativeOpenExecution.step machine env (world (some 1) [true]) =
      PMF.pure (world none [true, false]) := by
    simp only [NativeOpenExecution.step, world, machine,
      MultiTapeMachine.Config.step, Action.apply, moveInputPos_zero,
      Option.toList_some, Option.toList_none, List.append_nil,
      SignType.coe_zero, add_zero, PMF.bind_const]
    norm_num
    congr 4 <;> funext i <;> exact Fin.elim0 i
  have hterminal : NativeUnboundedExecution.terminal machine env (world (some 0) []) =
      PMF.pure (some (world none [true, false])) := by
    unfold NativeUnboundedExecution.terminal
    rw [StoppedProcess.terminal_step, h0, PMF.pure_bind,
      StoppedProcess.terminal_step, h1, PMF.pure_bind]
    exact StoppedProcess.terminal_halted _ _ _ _ rfl
  have hdecode : NativeOpenSelection.result (decodeFamily 2) (world none [true, false]) =
      some ({0} : Finset (Fin 2)) := by
    change decodeFamily 2 [true, false] = some {0}
    simpa [encodeFamily, List.ofFn_succ] using (decodeFamily_encode ({0} : Finset (Fin 2)))
  have hfail : BatchOutput.accept data.startup.system valid ({0} : Finset (Fin 2)) = false := by
    norm_num [BatchOutput.accept, instanceOf, PartialCover.Instance.covered,
      PartialCover.Instance.cost, elements, ground, List.range_succ]
    decide
  change NativeUnboundedExecution.SelectionOnly machine env _ _ _ (world (some 0) []) ∧
    ¬NativeUnboundedExecution.SelectionOnly machine env _ _ _ (world (some 0) []) ∧ _
  refine ⟨?_, ?_, ?_⟩
  · intro fuel next hn C hC hA
    have hh : NativeUnboundedExecution.halted next := by
      cases hs : next.config.tapes.state with
      | none => exact hs
      | some c => simp [NativeOpenSelection.result, hs] at hC
    have ht := (NativeUnboundedExecution.terminal_support machine env _ next).mpr ⟨hh, fuel, hn⟩
    rw [hterminal, PMF.mem_support_pure_iff, Option.some.injEq] at ht
    subst next
    rw [hdecode, Option.some.injEq] at hC
    subst C
    simp [hfail] at hA
  · intro hall
    have hn : world none [true, false] ∈
        (execute machine env 2 (world (some 0) [])).support := by
      change world none [true, false] ∈ (execute machine env (1 + 1) (world (some 0) [])).support
      rw [execute_add, execute_one, h0, PMF.pure_bind, execute_one, h1]
      exact (PMF.mem_support_pure_iff _ _).mpr rfl
    have hbad := hall 2 (world none [true, false]) hn {0} hdecode rfl
    norm_num [NativeOpenSelection.proposals, world, ConcurrentBatch.initial] at hbad
  · norm_num [instanceOf, PartialCover.Instance.covered, elements, ground, List.range_succ]
