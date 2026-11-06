/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.CoinTape
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.Sequential

/-!
# Fixed-coin steps of sequential probabilistic machines

## Main results

* `Turing.MultiTapePTM.step_withCoin_seq_left`: a running first phase follows its own step.
* `Turing.MultiTapePTM.step_withCoin_seq_right`: the second phase follows its own step.
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


end Turing.MultiTapePTM
