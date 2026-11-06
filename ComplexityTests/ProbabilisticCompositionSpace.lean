/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Composition.Space
import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.PairSampler
import Complexity.Computability.Machines.Turing.MultiTape.Combinators.Id
import Complexity.Computability.Machines.Turing.MultiTape.Run
import Complexity.Probability.PMF.Bind

/-! Actual sampler-to-native-consumer composition, including a consumer that never halts. -/

namespace ComplexityTests.ProbabilisticCompositionSpace

open Cslib Turing MultiTapeMachine MultiTapePTM MultiTapeTM

private theorem sampler_output_length (y r word : List Bool)
    (h : word ∈ (ProbComp.eval (pairSampler.runClosed
      ((frame y ++ r).length + 1) (frame y ++ r))).support) :
    word.length = (frame y).length + r.length := by
  rw [eval_pairSampler] at h
  obtain ⟨coins, hcoins, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  rw [List.length_append, BitString.length_of_mem_support_uniformList hcoins]

-- Both machines have zero work tapes, but their actual composition retains the sampled word.
-- The bound grows with the unary allocation and the framed captured input.
example (y : List Bool) (budget : ℕ) :
    ((ofDeterministic (MultiTapeTM.copyInput (Symbol := Bool))).comp
      pairSampler true).toNTM.RunsInSpace (frame y ++ List.replicate budget true)
        (2 * (2 * ((frame y).length + budget + 2) + 1)) := by
  have h := runsInSpace_toNTM_comp pairSampler
    (ofDeterministic (MultiTapeTM.copyInput (Symbol := Bool))) true
    (sourceSpace := 0) (consumerSpace := 0) (outputBound := (frame y).length + budget)
    (pairSampler_halted y (List.replicate budget true)) (by simp)
    (fun word hword => by simpa using (sampler_output_length y _ word hword).le)
    (fun _ _ => by simp)
  simpa using h

-- Omitting the two actual buffer tapes cannot give a valid zero-space certificate.
example (input : List Bool) :
    ¬ ((ofDeterministic (MultiTapeTM.copyInput (Symbol := Bool))).comp
      pairSampler true).toNTM.RunsInSpace input 0 := by
  intro h
  have := h.le
  omega

private theorem copy_halted (word : List Bool) : ∀ final ∈ (ProbComp.eval
    ((ofDeterministic (MultiTapeTM.copyInput (Symbol := Bool))).runClosedConfigFrom
      (word.length + 1) ((ofDeterministic MultiTapeTM.copyInput).initialConfig word))).support,
    final.tapes.state = none := by
  intro final hfinal
  rw [eval_runClosedConfigFrom_ofDeterministic, PMF.support_pure,
    Set.mem_singleton_iff] at hfinal
  subst final
  exact ((MultiTapeTM.CopyInput.computesInTimeAndSpace word).runFrom_of_le le_rfl).1

-- The same compiled machine really copies the sampled pair; its output law is not an assumed
-- consumer contract. The complete clock includes the native buffer handoff.
example (y r : List Bool) :
    ProbComp.eval (((ofDeterministic (MultiTapeTM.copyInput (Symbol := Bool))).comp
      pairSampler true).runClosed
        (((frame y ++ r).length + 1) + ((frame y ++ r).length + 1 + 4 +
          ((frame y ++ r).length + 1))) (frame y ++ r)) =
      (BitString.uniformList r.length).map (frame y ++ ·) := by
  have hcopy (word : List Bool) (hword : word ∈ (ProbComp.eval (pairSampler.runClosed
      ((frame y ++ r).length + 1) (frame y ++ r))).support) :
      word.length = (frame y ++ r).length := by
    simpa only [List.length_append] using sampler_output_length y r word hword
  rw [eval_comp pairSampler (ofDeterministic MultiTapeTM.copyInput) true (frame y ++ r)
    ((frame y ++ r).length + 1) ((frame y ++ r).length + 1) (pairSampler_halted y r)
    (fun word hword => by rw [← hcopy word hword]; exact copy_halted word)]
  rw [Probability.PMF.monad_bind_eq_bind]
  calc
    _ = (ProbComp.eval (pairSampler.runClosed ((frame y ++ r).length + 1)
        (frame y ++ r))).bind PMF.pure := by
      apply Probability.PMF.bind_congr_on_support
      intro word hword
      rw [eval_runClosed_ofDeterministic, ← hcopy word hword]
      rw [((MultiTapeTM.CopyInput.computesInTimeAndSpace word).runFrom_of_le le_rfl).2]
    _ = _ := by rw [PMF.bind_pure, eval_pairSampler]

-- A concrete consumer with no work tapes and an endless live control state.
private def spin : MultiTapePTM 0 Bool Unit where
  initial := ()
  tr _ _ _ _ _ := .step
    { inputTape := 0, workTapes := Fin.elim0, output := none, state := some () }
    Empty.elim Empty.elim

private theorem spin_replay (input : List Bool) (coins : List Bool) :
    spin.runClosedConfigFromCoins coins (spin.initialConfig input) = spin.initialConfig input := by
  have hstep (bit : Bool) : (spin.withCoin bit).step (spin.initialConfig input) =
      spin.initialConfig input := by
    rw [Config.eq_iff_tapes_eq]
    apply Cfg.ext_zero_tapes <;>
      simp [MultiTapeMachine.step, initialConfig, spin, MultiTapePTM.withCoin, Config.step,
      Turing.Action.apply, Cfg.init]
  induction coins with
  | nil => rfl
  | cons bit coins ih =>
    change spin.runClosedConfigFromCoins coins ((spin.withCoin bit).step
      (spin.initialConfig input)) = _
    rw [hstep, ih]

example (input : List Bool) (coins : List Bool) :
    (spin.runClosedConfigFromCoins coins (spin.initialConfig input)).tapes.state ≠ none := by
  rw [spin_replay]
  simp [initialConfig, Cfg.init]

-- No consumer halting premise: this all-prefix bound also covers the endless consumer.
example (y r : List Bool) :
    (spin.comp pairSampler false).toNTM.RunsInSpace (frame y ++ r)
      (2 * (2 * ((frame y).length + r.length + 2) + 1)) := by
  simpa using runsInSpace_toNTM_comp pairSampler spin false
    (sourceSpace := 0) (consumerSpace := 0) (outputBound := (frame y).length + r.length)
    (pairSampler_halted y r) (by simp)
    (fun word hword => (sampler_output_length y r word hword).le) (fun _ _ => by simp)

-- Empty intermediate output still incurs the two-tape compiler layout and boundary handling.
example : ((ofDeterministic (MultiTapeTM.copyInput (Symbol := Bool))).comp
    uniformListMachine false).toNTM.RunsInSpace [] 10 := by
  simpa using runsInSpace_toNTM_comp uniformListMachine
    (ofDeterministic (MultiTapeTM.copyInput (Symbol := Bool))) false
    (sourceSpace := 0) (consumerSpace := 0) (outputBound := 0)
    (uniformListMachine_halted []) (by simp) (fun word hword => by
      rw [eval_uniformListMachine] at hword
      exact (BitString.length_of_mem_support_uniformList hword).le) (fun _ _ => by simp)

end ComplexityTests.ProbabilisticCompositionSpace
