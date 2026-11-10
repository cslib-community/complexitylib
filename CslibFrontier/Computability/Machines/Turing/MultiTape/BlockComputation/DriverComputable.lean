/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.DriverCorrect

/-!
# Compiling the native simulation driver

The existing query-machine compiler turns the complete driver into an ordinary multitape
computation. Its space is bounded by the maximum physical storage of its candidate searches.
The supplied source halting clock is a semantic witness only: the compiled machine obtains its
input length and time guesses itself. Any correct evaluator and any guess parameters may be
used; reducing the allowance to a closed-form expression is a separate quantitative step for
each instance.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.Driver

open MultiTapeTM

variable {k : ℕ} {Q : Type}

/-- A total deterministic source's Boolean decision is computed by an ordinary multitape
machine with the complete driver's physical-space allowance, for any correct evaluator and any
guess parameters. No computability assumption on its source halting-clock witness is needed. -/
theorem computableInSpace_decision {E : ScheduleSearch.Evaluator} {M : MultiTapeTM k Bool Q}
    {A : ℕ → ℕ → ℕ → ℕ} (hE : E.Correct M A) (P : OuterSearch.Parameters)
    {α : Type} (enc : α ↪ List Bool) (τ : α → ℕ)
    (hτ : ∀ a, (M.runFrom (Cfg.init M.q₀ (enc a)) (τ a)).Halted) :
    ∃ time c, ComputableInTimeAndSpace
      (fun a => decide ((M.runFrom (Cfg.init M.q₀ (enc a)) (τ a)).output = [true]))
      enc encBool time (fun a => c * space k A P (enc a).length (τ a)) := by
  classical
  choose clock hpre hhalt hout hsize using fun a =>
    exists_first_decision P hE (enc a) (τ a) (hτ a)
  refine QueryMachine.computableInSpace (encS := encState E) (machine E k P)
    (machine_query_inSpace E k P) (machine_next_inSpace E k P) (machine_emit_inSpace E k P)
    (machine_halted_inSpace E k P) (machine_finish_inSpace E k P) clock hhalt hpre ?_
    (fun a => space k A P (enc a).length (τ a)) ?_ ⟨1, ?_⟩
  · intro w
    exact (hout w).symm
  · intro w
    dsimp only [space]
    omega
  · intro w t ht
    simpa only [Nat.one_mul] using hsize w t ht

end Turing.MultiTapePTM.BlockComputation.Driver
