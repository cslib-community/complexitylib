/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Composition
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential.CoinTape
import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape.Space
import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.PrepareInput.Space

/-!
# Workspace of buffered probabilistic composition

The existing compiler retains the source scratch tapes and uses two additional tapes for the
consumer's virtual input and its boundary marker. Bounds concern every computation prefix of
the nondeterministic view, and charge the intermediate word separately from component workspace.

## Main results

* `Turing.MultiTapePTM.runsInSpace_toNTM_comp`: separate source and consumer workspace,
  with a supported intermediate-word bound and no consumer-halting premise.
-/

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

namespace Composition

open MultiTapeMachine.Composition

variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

private theorem replay_append (machine : MultiTapePTM k Symbol State)
    (before after : List Bool) (cfg : Config k Symbol State Empty input) :
    machine.runClosedConfigFromCoins (before ++ after) cfg =
      machine.runClosedConfigFromCoins after (machine.runClosedConfigFromCoins before cfg) :=
  List.foldl_append

private theorem replay_seq_cases {State₀ State₁ : Type}
    (first : MultiTapePTM k Symbol State₀) (second : MultiTapePTM k Symbol State₁)
    (initial : Config k Symbol State₀ Empty input) (coins : List Bool) :
    (∃ before, (first.seq second).runClosedConfigFromCoins coins (Sequential.left second initial) =
      Sequential.left second (first.runClosedConfigFromCoins before initial)) ∨
    ∃ before after,
      (first.runClosedConfigFromCoins before initial).tapes.state = none ∧
      (first.seq second).runClosedConfigFromCoins coins (Sequential.left second initial) =
        Sequential.right (second.runClosedConfigFromCoins after
          (Sequential.start second (first.runClosedConfigFromCoins before initial))) := by
  induction coins using List.reverseRecOn with
  | nil => exact Or.inl ⟨[], rfl⟩
  | append_singleton coins bit ih =>
    rw [replay_append]
    rcases ih with ⟨before, hp⟩ | ⟨before, after, hh, hs⟩
    · rw [hp]
      by_cases hh : (first.runClosedConfigFromCoins before initial).tapes.state = none
      · right
        refine ⟨before, [bit], hh, ?_⟩
        rw [Sequential.left_halted second _ hh]
        simpa only [runClosedConfigFromCoins, List.foldl_cons, List.foldl_nil] using
          step_withCoin_seq_right first second bit
            (Sequential.start second (first.runClosedConfigFromCoins before initial))
      · left
        refine ⟨before ++ [bit], ?_⟩
        rw [replay_append]
        exact step_withCoin_seq_left first second bit _ hh
    · right
      refine ⟨before, after ++ [bit], hh, ?_⟩
      rw [hs, replay_append]
      exact step_withCoin_seq_right first second bit _

private theorem output_length_le_replay (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input) :
    cfg.tapes.output.length ≤
      (machine.runClosedConfigFromCoins coins cfg).tapes.output.length := by
  obtain ⟨p, hhead, _, hlast⟩ := (machine.exists_runPath_toNTM_iff
    (c := cfg.tapes)).mpr ⟨coins, rfl, rfl⟩
  have h := p.length_output_mono (Fin.zero_le (Fin.last p.length))
  change p.head.output.length ≤ p.last.output.length at h
  rw [hhead, hlast] at h
  simpa only [tapes_runClosedConfigFromCoins] using h

private theorem replay_halted (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input)
    (h : cfg.tapes.state = none) : machine.runClosedConfigFromCoins coins cfg = cfg := by
  induction coins with
  | nil => rfl
  | cons bit coins ih =>
    change machine.runClosedConfigFromCoins coins ((machine.withCoin bit).step cfg) = cfg
    rw [show (machine.withCoin bit).step cfg = cfg by simp [MultiTapeMachine.step, h], ih]

private theorem completed_replay_mem_support (machine : MultiTapePTM k Symbol State)
    (initial : Config k Symbol State Empty input) (time : ℕ)
    (hhalt : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom time initial)).support,
      final.tapes.state = none)
    (coins : List Bool)
    (hcoins : (machine.runClosedConfigFromCoins coins
      initial).tapes.state = none) :
    machine.runClosedConfigFromCoins coins initial ∈
      (ProbComp.eval (machine.runClosedConfigFrom time initial)).support := by
  by_cases hle : time ≤ coins.length
  · have h := machine.runClosedConfigFromCoins_mem_support coins initial
    rwa [eval_runClosedConfigFrom_eq_of_halted machine _ hle hhalt] at h
  · have h := machine.runClosedConfigFromCoins_mem_support
      (coins ++ List.replicate (time - coins.length) false) initial
    have hlen : (coins ++ List.replicate (time - coins.length) false).length = time := by
      simp only [List.length_append, List.length_replicate]
      omega
    rw [hlen] at h
    simp only [runClosedConfigFromCoins, List.foldl_append] at h
    change machine.runClosedConfigFromCoins (List.replicate (time - coins.length) false)
      (machine.runClosedConfigFromCoins coins initial) ∈ _ at h
    rwa [replay_halted machine _ _ hcoins] at h

private theorem replay_output_length_le (machine : MultiTapePTM k Symbol State)
    (time bound : ℕ)
    (hhalt : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom time (machine.initialConfig input))).support,
      final.tapes.state = none)
    (hbound : ∀ word ∈ (ProbComp.eval (machine.runClosed time input)).support,
      word.length ≤ bound) (coins : List Bool) :
    (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.output.length ≤
      bound := by
  let extra := List.replicate (time - coins.length) false
  have hle : time ≤ (coins ++ extra).length := by
    simp only [List.length_append, extra, List.length_replicate]
    omega
  have hfull := machine.runClosedConfigFromCoins_mem_support (coins ++ extra)
    (machine.initialConfig input)
  rw [eval_runClosedConfigFrom_eq_of_halted machine _ hle hhalt] at hfull
  have hout : (machine.runClosedConfigFromCoins (coins ++ extra)
      (machine.initialConfig input)).tapes.output ∈
      (ProbComp.eval (machine.runClosed time input)).support := by
    rw [runClosed_eq_map, ProbComp.eval_map]
    exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, hfull, rfl⟩
  have hlen := hbound _ hout
  have hmono := output_length_le_replay machine extra
    (machine.runClosedConfigFromCoins coins (machine.initialConfig input))
  simp only [runClosedConfigFromCoins, List.foldl_append] at hmono hlen ⊢
  exact hmono.trans hlen

private theorem replay_seq_window {State₀ State₁ : Type}
    (first : MultiTapePTM k Symbol State₀) (second : MultiTapePTM k Symbol State₁)
    (initial : Config k Symbol State₀ Empty input) (bound : ℕ)
    (hfirst : ∀ coins i,
      (first.runClosedConfigFromCoins coins initial).tapes.workTapePos i ∈ window bound)
    (hsecond : ∀ before,
      (first.runClosedConfigFromCoins before initial).tapes.state = none →
      ∀ after i, (second.runClosedConfigFromCoins after
        (Sequential.start second (first.runClosedConfigFromCoins before initial))).tapes.workTapePos
          i ∈ window bound) (coins : List Bool) (i : Fin k) :
    ((first.seq second).runClosedConfigFromCoins coins
      (Sequential.left second initial)).tapes.workTapePos i ∈ window bound := by
  rcases replay_seq_cases first second initial coins with ⟨before, h⟩ | ⟨before, after, hh, h⟩
  · rw [h]; exact hfirst before i
  · rw [h]; exact hsecond before hh after i

private theorem source_replay_exists {k₀ k₁ : ℕ} {State₀ : Type}
    (first : MultiTapePTM k₀ Symbol State₀) (coins : List Bool) :
    ∃ sourceCoins, (source first k₁).runClosedConfigFromCoins coins
        ((source first k₁).initialConfig input) =
      buffer k₁ (first.runClosedConfigFromCoins sourceCoins (first.initialConfig input)) := by
  have h := (source first k₁).runClosedConfigFromCoins_mem_support coins
    ((source first k₁).initialConfig input)
  rw [runClosedConfigFrom_source, ProbComp.eval_map] at h
  obtain ⟨cfg, hcfg, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  rw [eval_runClosedConfigFrom_eq_map_coins] at hcfg
  obtain ⟨sourceCoins, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hcfg
  exact ⟨sourceCoins, heq.symm⟩

private theorem buffer_window {k₀ : ℕ} {State₀ : Type}
    (k₁ bound : ℕ) (cfg : Config k₀ Symbol State₀ Empty input)
    (hheads : ∀ i, cfg.tapes.workTapePos i ∈ window bound)
    (hword : cfg.tapes.output.length ≤ bound) (i : Fin (k₁ + k₀ + 2)) :
    (buffer k₁ cfg).tapes.workTapePos i ∈ window bound := by
  rw [buffer_tapes]
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i => simp [reserve, Config.embed, MultiTapeTM.embed_natAdd, mem_window]
    | right i => simpa [reserve, Config.embed, MultiTapeTM.embed_natAdd] using hheads i
  | right i =>
    fin_cases i <;> simp [mem_window, hword]

private theorem consumer_replay_exists {k₀ k₁ : ℕ} {State₀ State₁ : Type}
    (second : MultiTapePTM k₁ Symbol State₁) (mark : Symbol)
    (cfg : Config k₀ Symbol State₀ Empty input) (coins : List Bool) :
    ∃ consumerCoins, (consumer second k₀).runClosedConfigFromCoins coins
        (consumerConfig mark cfg (second.initialConfig cfg.tapes.output)) =
      consumerConfig mark cfg
        (second.runClosedConfigFromCoins consumerCoins
          (second.initialConfig cfg.tapes.output)) := by
  have h := (consumer second k₀).runClosedConfigFromCoins_mem_support coins
    (consumerConfig mark cfg (second.initialConfig cfg.tapes.output))
  rw [runClosedConfigFrom_consumer, ProbComp.eval_map] at h
  obtain ⟨final, hfinal, heq⟩ := (PMF.mem_support_map_iff _ _ _).mp h
  rw [eval_runClosedConfigFrom_eq_map_coins] at hfinal
  obtain ⟨consumerCoins, _, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hfinal
  exact ⟨consumerCoins, heq.symm⟩

private theorem consumerConfig_window {k₀ k₁ : ℕ} {State₀ State₁ : Type}
    (mark : Symbol) (cfg₀ : Config k₀ Symbol State₀ Empty input)
    (cfg₁ : Config k₁ Symbol State₁ Empty cfg₀.tapes.output) (bound : ℕ)
    (hfirst : ∀ i, cfg₀.tapes.workTapePos i ∈ window bound)
    (hsecond : ∀ i, cfg₁.tapes.workTapePos i ∈ window bound)
    (hword : cfg₀.tapes.output.length ≤ bound) (hone : 1 ≤ bound)
    (i : Fin (k₁ + k₀ + 2)) :
    (consumerConfig mark cfg₀ cfg₁).tapes.workTapePos i ∈ window bound := by
  simp only [consumerConfig, InputFromTape.config, MultiTapeTM.inCfg]
  induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i => simpa [Config.embed, MultiTapeTM.embed_castAdd] using hsecond i
    | right i =>
      simpa [Config.embed, MultiTapeTM.embed_castAdd, reserve, MultiTapeTM.embed_natAdd]
        using hfirst i
  | right i =>
    simp only [Fin.append_right]
    rw [window, Finset.mem_Icc]
    have hpos := cfg₁.tapes.inputPos.isLt
    constructor <;> omega

private theorem continuation_replay_window {k₀ k₁ : ℕ} {State₀ State₁ : Type}
    (second : MultiTapePTM k₁ Symbol State₁) (mark : Symbol)
    (cfg : Config k₀ Symbol State₀ Empty input) (bound : ℕ)
    (hfirst : ∀ i, cfg.tapes.workTapePos i ∈ window bound)
    (hsecond : ∀ coins i, (second.runClosedConfigFromCoins coins
      (second.initialConfig cfg.tapes.output)).tapes.workTapePos i ∈ window bound)
    (hword : cfg.tapes.output.length ≤ bound) (hone : 1 ≤ bound)
    (coins : List Bool) (i : Fin (k₁ + k₀ + 2)) :
    ((continuation second k₀ mark).runClosedConfigFromCoins coins
      (Sequential.start (continuation second k₀ mark) (buffer k₁ cfg))).tapes.workTapePos i ∈
        window bound := by
  let prep := MultiTapeTM.prepareInput (k₁ + k₀) mark
  let initial := Sequential.start (ofDeterministic prep) (buffer k₁ cfg)
  have hprepare : ProbComp.eval ((ofDeterministic prep).runClosedConfigFrom
      (cfg.tapes.output.length + 4) initial) = PMF.pure (ready mark k₁ cfg) := by
    rw [eval_runClosedConfigFrom_ofDeterministic]
    congr 1
    apply Config.ext
    · exact runFrom_prepare mark k₁ cfg
    · exact Subsingleton.elim _ _
  have hhalt : ∀ final ∈ (ProbComp.eval ((ofDeterministic prep).runClosedConfigFrom
      (cfg.tapes.output.length + 4) initial)).support, final.tapes.state = none := by
    intro final hfinal
    rw [hprepare, PMF.support_pure, Set.mem_singleton_iff] at hfinal
    subst final
    rfl
  change (((ofDeterministic prep).seq (consumer second k₀)).runClosedConfigFromCoins coins
    (Sequential.left (consumer second k₀) initial)).tapes.workTapePos i ∈ window bound
  apply replay_seq_window
  · intro before j
    rw [replay_ofDeterministic]
    apply MultiTapeTM.workTapePos_runFrom_prepareInput_mem_window mark
      (buffer k₁ cfg).tapes cfg.tapes.output bound
      (by rw [buffer_tapes]; simp) (by rw [buffer_tapes]; simp)
      (by rw [buffer_tapes]; simp) hword hone (buffer_window k₁ bound cfg hfirst hword)
  · intro before hh after j
    have hfinal := completed_replay_mem_support (ofDeterministic prep) initial
      (cfg.tapes.output.length + 4) hhalt before hh
    rw [hprepare, PMF.support_pure, Set.mem_singleton_iff] at hfinal
    rw [hfinal, start_ready]
    obtain ⟨consumerCoins, heq⟩ := consumer_replay_exists second mark cfg after
    rw [heq]
    exact consumerConfig_window mark cfg _ bound hfirst (hsecond consumerCoins) hword hone j

end Composition

/-- Workspace of the existing buffered probabilistic compiler, measured on every prefix of every
branch. The source must halt within its clock and its supported completed outputs must fit the
buffer bound. The consumer needs only an all-prefix workspace bound on those supported words;
it need not halt. The two extra tapes and retained source scratch are charged explicitly.
This bound is independent of the source clock and of any consumer runtime. -/
public theorem runsInSpace_toNTM_comp {k₀ k₁ : ℕ} {Symbol State₀ State₁ : Type}
    (first : MultiTapePTM k₀ Symbol State₀) (second : MultiTapePTM k₁ Symbol State₁)
    (mark : Symbol) {input : List Symbol} {time sourceSpace consumerSpace outputBound : ℕ}
    (hhalt : ∀ final ∈ (ProbComp.eval
      (first.runClosedConfigFrom time (first.initialConfig input))).support,
      final.tapes.state = none)
    (hfirst : first.toNTM.RunsInSpace input sourceSpace)
    (houtput : ∀ word ∈ (ProbComp.eval (first.runClosed time input)).support,
      word.length ≤ outputBound)
    (hsecond : ∀ word ∈ (ProbComp.eval (first.runClosed time input)).support,
      second.toNTM.RunsInSpace word consumerSpace) :
    (second.comp first mark).toNTM.RunsInSpace input
      ((k₁ + k₀ + 2) * (2 * max (max sourceSpace consumerSpace) (outputBound + 2) + 1)) := by
  let bound := max (max sourceSpace consumerSpace) (outputBound + 2)
  have hmono {s : ℕ} {z : ℤ} (h : z ∈ window s) (hle : s ≤ bound) :
      z ∈ window bound := mem_window.mpr ((mem_window.mp h).trans hle)
  have hsource (coins : List Bool) (i : Fin k₀) :
      (first.runClosedConfigFromCoins coins (first.initialConfig input)).tapes.workTapePos i ∈
        window bound :=
    hmono (workTapePos_runClosedCoins_mem_window first hfirst coins i)
      ((le_max_left _ _).trans (le_max_left _ _))
  have hword (coins : List Bool) :
      (first.runClosedConfigFromCoins coins (first.initialConfig input)).tapes.output.length ≤
        bound :=
    (Composition.replay_output_length_le first time outputBound hhalt houtput coins).trans
      (by dsimp only [bound]; omega)
  have hreach (coins : List Bool) (i : Fin (k₁ + k₀ + 2)) :
      ((second.comp first mark).runClosedConfigFromCoins coins
        ((second.comp first mark).initialConfig input)).tapes.workTapePos i ∈ window bound := by
    change ((Composition.source first k₁).seq (Composition.continuation second k₀ mark)
      |>.runClosedConfigFromCoins coins
        (Sequential.left (Composition.continuation second k₀ mark)
          ((Composition.source first k₁).initialConfig input))).tapes.workTapePos i ∈ window bound
    apply Composition.replay_seq_window
    · intro before j
      obtain ⟨sourceCoins, heq⟩ := Composition.source_replay_exists first before
      rw [heq]
      exact Composition.buffer_window k₁ bound _ (hsource sourceCoins) (hword sourceCoins) j
    · intro before hh after j
      obtain ⟨sourceCoins, heq⟩ := Composition.source_replay_exists first before
      rw [heq] at hh ⊢
      have hfinal := Composition.completed_replay_mem_support first (first.initialConfig input)
        time hhalt sourceCoins hh
      have hout : (first.runClosedConfigFromCoins sourceCoins
          (first.initialConfig input)).tapes.output ∈
          (ProbComp.eval (first.runClosed time input)).support := by
        rw [runClosed_eq_map, ProbComp.eval_map]
        exact (PMF.mem_support_map_iff _ _ _).mpr ⟨_, hfinal, rfl⟩
      apply Composition.continuation_replay_window second mark _ bound (hsource sourceCoins)
        (fun consumerCoins i => hmono
          (workTapePos_runClosedCoins_mem_window second (hsecond _ hout) consumerCoins i)
          ((le_max_right _ _).trans (le_max_left _ _)))
        (hword sourceCoins) (by dsimp only [bound]; omega)
  intro path
  apply MultiTapeNTM.RunPath.InWindow.space_le
  rintro _ ⟨j, rfl⟩ i
  obtain ⟨coins, _, hcoins⟩ := ((second.comp first mark).exists_runPath_toNTM_iff).mp
    ⟨path.toRunPath.take j, RelSeries.head_take _ _, rfl, RelSeries.last_take _ _⟩
  rw [← hcoins, path.head_eq, initCfg_toNTM, ← tapes_runClosedConfigFromCoins]
  exact hreach coins i

end Turing.MultiTapePTM
