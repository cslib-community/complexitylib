/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential
import CslibFrontier.Computability.Machines.Turing.MultiTape.Machine.Nondeterministic

/-!
# Fixed-coin steps of sequential probabilistic machines

## Main results

* `Turing.MultiTapePTM.step_withCoin_seq_left`: a running first phase follows its own step.
* `Turing.MultiTapePTM.step_withCoin_seq_right`: the second phase follows its own step.
* `Turing.MultiTapePTM.replay_append`, `Turing.MultiTapePTM.replay_seq_cases`: concatenate coin
  replays and identify the active phase of a sequential machine.
* `Turing.MultiTapePTM.output_length_le_replay`, `Turing.MultiTapePTM.replay_halted`: output length
  is monotone along a replay, and halted configurations remain fixed.
* `Turing.MultiTapePTM.completed_replay_mem_support`,
  `Turing.MultiTapePTM.replay_output_length_le`: connect completed replays to run support and
  transfer support-wise output bounds to arbitrary replay prefixes.
-/

public section

namespace Turing.MultiTapePTM

open Cslib MultiTapeMachine

variable {k : ℕ} {Symbol : Type} {input : List Symbol}

/-- With a fixed coin, a running first phase of a sequential machine steps as the first machine. -/
theorem step_withCoin_seq_left {S₀ S₁ : Type} (first : MultiTapePTM k Symbol S₀)
    (second : MultiTapePTM k Symbol S₁) (bit : Bool) (c : Config k Symbol S₀ Empty input)
    (hc : c.tapes.state ≠ none) :
    ((first.seq second).withCoin bit).step (Sequential.left second c) =
      Sequential.left second ((first.withCoin bit).step c) := by
  obtain ⟨q, hq⟩ := Option.ne_none_iff_exists'.mp hc
  rw [Config.eq_iff_tapes_eq]
  have hstate : (Sequential.left second c).tapes.state = some (.inl q) := by
    simp [Sequential.left, Cfg.mapState, hq]
  have hinput : (Sequential.left second c).tapes.inputSymbol = c.tapes.inputSymbol := rfl
  have hwork : (Sequential.left second c).tapes.workTapeSymbols = c.tapes.workTapeSymbols := rfl
  have hans : (Sequential.left second c).answerSymbols = c.answerSymbols := Subsingleton.elim _ _
  have hmap (f : ReaderT Bool Id (MultiTapeMachine.Action k Symbol S₀ Empty)) :
      (Sequential.leftAction second.initial <$> f) bit =
        Sequential.leftAction second.initial (f bit) := rfl
  simp only [MultiTapeMachine.step, hstate, hq, withCoin, seq, MultiTapeMachine.seq, hinput,
    hwork, hans, hmap]
  cases first.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
  | step a s m =>
    simp [Sequential.leftAction, Sequential.left, Config.step, Turing.Action.apply, Cfg.mapState]
  | query op _ => exact op.elim

/-- With a fixed coin, the second phase of a sequential machine steps as the second machine. -/
theorem step_withCoin_seq_right {S₀ S₁ : Type} (first : MultiTapePTM k Symbol S₀)
    (second : MultiTapePTM k Symbol S₁) (bit : Bool) (c : Config k Symbol S₁ Empty input) :
    ((first.seq second).withCoin bit).step (Sequential.right (State₀ := S₀) c) =
      Sequential.right ((second.withCoin bit).step c) := by
  rw [Config.eq_iff_tapes_eq]
  cases hq : c.tapes.state with
  | none => simp [MultiTapeMachine.step, Sequential.right, Cfg.mapState, hq]
  | some q =>
    have hstate : (Sequential.right (State₀ := S₀) c).tapes.state = some (.inr q) := by
      simp [Sequential.right, Cfg.mapState, hq]
    have hinput : (Sequential.right (State₀ := S₀) c).tapes.inputSymbol =
        c.tapes.inputSymbol := rfl
    have hwork : (Sequential.right (State₀ := S₀) c).tapes.workTapeSymbols =
        c.tapes.workTapeSymbols := rfl
    have hans : (Sequential.right (State₀ := S₀) c).answerSymbols = c.answerSymbols :=
      Subsingleton.elim _ _
    have hmap (f : ReaderT Bool Id (MultiTapeMachine.Action k Symbol S₁ Empty)) :
        (Sequential.rightAction (State₀ := S₀) <$> f) bit = Sequential.rightAction (f bit) := rfl
    simp only [MultiTapeMachine.step, hstate, hq, withCoin, seq, MultiTapeMachine.seq, hinput,
      hwork, hans, hmap]
    cases second.tr q c.tapes.inputSymbol c.tapes.workTapeSymbols c.answerSymbols bit with
    | step a s m =>
      simp [Sequential.rightAction, Sequential.right, Config.step, Turing.Action.apply,
        Cfg.mapState]
    | query op _ => exact op.elim


variable {k : ℕ} {Symbol State : Type} {input : List Symbol}

/-- Running a sequential concatenation of coin sequences is equivalent to
running them consecutively. -/
theorem replay_append (machine : MultiTapePTM k Symbol State)
    (before after : List Bool) (cfg : Config k Symbol State Empty input) :
    machine.runClosedConfigFromCoins (before ++ after) cfg =
      machine.runClosedConfigFromCoins after (machine.runClosedConfigFromCoins before cfg) :=
  List.foldl_append

/-- Replaying a sequence of coins on a sequentially composed machine either stays in the
first phase or transitions to the second. -/
theorem replay_seq_cases {State₀ State₁ : Type}
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

/-- The output tape length is monotonically non-decreasing during a run. -/
theorem output_length_le_replay (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input) :
    cfg.tapes.output.length ≤
      (machine.runClosedConfigFromCoins coins cfg).tapes.output.length := by
  obtain ⟨p, hhead, _, hlast⟩ := (machine.exists_runPath_toNTM_iff
    (c := cfg.tapes)).mpr ⟨coins, rfl, rfl⟩
  have h := p.length_output_mono (Fin.zero_le (Fin.last p.length))
  change p.head.output.length ≤ p.last.output.length at h
  rw [hhead, hlast] at h
  simpa only [tapes_runClosedConfigFromCoins] using h

/-- A halted configuration does not change when further coins are replayed. -/
theorem replay_halted (machine : MultiTapePTM k Symbol State)
    (coins : List Bool) (cfg : Config k Symbol State Empty input)
    (h : cfg.tapes.state = none) : machine.runClosedConfigFromCoins coins cfg = cfg := by
  induction coins with
  | nil => rfl
  | cons bit coins ih =>
    change machine.runClosedConfigFromCoins coins ((machine.withCoin bit).step cfg) = cfg
    rw [show (machine.withCoin bit).step cfg = cfg by simp only [MultiTapeMachine.step, h], ih]

/-- A replay that halts belongs to the support of the closed run evaluation. -/
theorem completed_replay_mem_support (machine : MultiTapePTM k Symbol State)
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
    have hlen : (coins ++ List.replicate (time - coins.length) false).length = time := by grind
    rw [hlen] at h
    simp only [runClosedConfigFromCoins, List.foldl_append] at h
    change machine.runClosedConfigFromCoins (List.replicate (time - coins.length) false)
      (machine.runClosedConfigFromCoins coins initial) ∈ _ at h
    rwa [replay_halted machine _ _ hcoins] at h

/-- Bounds the output length of any replay given a bound on the support of the closed run. -/
theorem replay_output_length_le (machine : MultiTapePTM k Symbol State)
    (time bound : ℕ)
    (hhalt : ∀ final ∈ (ProbComp.eval
      (machine.runClosedConfigFrom time (machine.initialConfig input))).support,
      final.tapes.state = none)
    (hbound : ∀ word ∈ (ProbComp.eval (machine.runClosed time input)).support,
      word.length ≤ bound) (coins : List Bool) :
    (machine.runClosedConfigFromCoins coins (machine.initialConfig input)).tapes.output.length ≤
      bound := by
  let extra := List.replicate (time - coins.length) false
  have hle : time ≤ (coins ++ extra).length := by grind
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
  rw [← replay_append] at hmono
  exact hmono.trans hlen

end Turing.MultiTapePTM
