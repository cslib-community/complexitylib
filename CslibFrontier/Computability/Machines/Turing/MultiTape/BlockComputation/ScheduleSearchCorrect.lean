/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootDecisionCorrect
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt

/-!
# Exact finite schedule search on the original input

Each counter invokes the complete evaluator. When the evaluator is correct, wrong schedules have
no outcome and the actual schedule gives precisely the simulated boundary's halted decision.
Exhausting the native range guard therefore returns no decision exactly when that boundary is
still live.

## Main definitions

* `ScheduleSearch.Evaluator.Correct`: the per-schedule correctness and storage contract.

## Main results

* `ScheduleSearch.exists_runFrom_boundaryDecision`: a correct evaluator's search returns the
  source machine's boundary decision within `space k A N b q`.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

/-- An evaluator is correct for the source machine `M` within allowance `A` when every in-range
schedule number reaches a halted state whose outcome is the source's boundary decision for the
actual schedule and absent for every other schedule, and every clock through that halt stores
at most `A N b q` bits. The allowance depends only on the input length, block width and
horizon. -/
@[expose] def Evaluator.Correct {k : ℕ} {Q : Type} (E : Evaluator) (M : MultiTapeTM k Bool Q)
    (A : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (w : List Bool) (b : ℕ) [NeZero b] (q σ : ℕ), σ < 3 ^ ((k + 1) * q) → ∃ T,
    E.machine.halted (E.machine.runFrom w (E.start (w.length, b, σ, q)) T) = true ∧
    E.outcome ((w.length, b, q), E.machine.runFrom w (E.start (w.length, b, σ, q)) T) =
      (if actualSchedule (MultiTapePTM.ofDeterministic M) w b (q := q) = scheduleOfNat k q σ
        then RootDecision.boundaryDecision M w (q * b) else none) ∧
    ∀ t ≤ T, (E.encState (E.machine.runFrom w (E.start (w.length, b, σ, q)) t)).length ≤
      A w.length b q

variable {k : ℕ}

/-- Entry and return add exactly two clocks to the first-halt evaluator run. -/
theorem runFrom_one (E : Evaluator) (args : Args)
    (w : List Bool) (σ T : ℕ) (hvalid : ScheduleCounter.valid k (σ, (horizon args)) = true)
    (hpre : ∀ t < T, E.machine.halted (E.machine.runFrom w
      (E.start (inputLength args, blockWidth args, σ, horizon args)) t) = false)
    (hhalt : E.machine.halted (E.machine.runFrom w
      (E.start (inputLength args, blockWidth args, σ, horizon args)) T) = true) :
    (machine E k).runFrom w (.inl (args, σ, none)) (T + 2) =
      .inl (resume E (args, σ, none) (E.machine.runFrom w
        (E.start (inputLength args, blockWidth args, σ, horizon args)) T)) := by
  apply QueryMachine.withCalls_runFrom_call
  · change (!pending k (args, σ, none)) = false
    rcases args with ⟨N, b, q⟩
    dsimp only [horizon] at hvalid
    simp only [pending, Option.isSome_none, Bool.not_false, Bool.true_and, hvalid, Bool.not_true]
  · rcases args with ⟨N, b, q⟩
    dsimp only [horizon] at hvalid
    simp only [inputLength, blockWidth, horizon, request, pending, Option.isSome_none,
      Bool.not_false, Bool.true_and,
      hvalid, ↓reduceIte]
  · exact hpre
  · exact hhalt

/-- Finite search is complete whenever every candidate either has no outcome or the specified
outcome, and a nonempty specified outcome occurs among the remaining candidates. -/
theorem exists_runFrom_candidates (E : Evaluator)
    (args : Args) (w : List Bool) (values : ℕ → Option Bool) (result : Option Bool) (B : ℕ)
    (hcaller : ∀ σ ≤ 3 ^ ((k + 1) * (horizon args)), ∀ result : Option Bool,
      (encState E (.inl (args, σ, result))).length ≤ B)
    (hstep : ∀ σ < 3 ^ ((k + 1) * (horizon args)), ∃ T,
      (machine E k).runFrom w (.inl (args, σ, none)) T =
        .inl (match values σ with
          | none => (args, σ + 1, none)
          | some answer => (args, σ, some answer)) ∧
      ∀ t ≤ T, (encState E ((machine E k).runFrom w (.inl (args, σ, none)) t)).length ≤ B)
    (hsafe : ∀ σ < 3 ^ ((k + 1) * (horizon args)), values σ = none ∨ values σ = result)
    (hcomplete : result ≠ none → ∃ σ < 3 ^ ((k + 1) * (horizon args)), values σ = result) :
    ∃ T σ, (machine E k).runFrom w (initial E args) T = .inl (args, σ, result) ∧
      (machine E k).halted (.inl (args, σ, result)) = true ∧
      ∀ t ≤ T, (encState E ((machine E k).runFrom w (initial E args) t)).length ≤ B := by
  obtain ⟨T, ⟨hrun, hnone⟩ | ⟨σ, answer, -, hσ, hv, hrun⟩, hB⟩ :=
    QueryMachine.exists_runFrom_search_encoding_le (M := machine E k) (w := w) (encState E)
      (fun σ => .inl (args, σ, none)) values (fun σ answer => .inl (args, σ, some answer))
      (hi := 3 ^ ((k + 1) * (horizon args))) (Nat.zero_le _) (hcaller 0 (Nat.zero_le _) none)
      (fun σ _ hσ hv => by simpa only [hv] using hstep σ hσ)
      (fun σ answer _ hσ hv => by simpa only [hv] using hstep σ hσ)
  · have hresult : result = none := by
      by_contra h
      obtain ⟨σ, hσ, hv⟩ := hcomplete h
      exact h (hv.symm.trans (hnone σ (Nat.zero_le _) hσ))
    subst result
    refine ⟨T, 3 ^ ((k + 1) * (horizon args)), hrun, ?_, hB⟩
    rcases args with ⟨N, b, q⟩
    change !ScheduleCounter.valid k (3 ^ ((k + 1) * q), q) = true
    rw [ScheduleCounter.valid_bound]
    rfl
  · have hresult : some answer = result := by
      simpa only [hv, reduceCtorEq, false_or] using hsafe σ hσ
    subst result
    rcases args with ⟨N, b, q⟩
    exact ⟨T, σ, hrun, rfl, hB⟩

/-- Sequential native schedule search with a correct evaluator returns exactly the original
machine's bounded halted decision. Every candidate is evaluated on the original input; no
lookup or supplier oracle is assumed, and a live boundary exhausts the schedule range with no
decision. -/
theorem exists_runFrom_boundaryDecision {Q : Type} {E : Evaluator} {M : MultiTapeTM k Bool Q}
    {A : ℕ → ℕ → ℕ → ℕ} (hE : E.Correct M A) (w : List Bool) (b : ℕ) [NeZero b] (q : ℕ) :
    ∃ T, (machine E k).halted
        ((machine E k).runFrom w (initial E (w.length, b, q)) T) = true ∧
      answer ((machine E k).runFrom w (initial E (w.length, b, q)) T) =
        RootDecision.boundaryDecision M w (q * b) ∧
      ∀ t ≤ T, (encState E ((machine E k).runFrom w (initial E (w.length, b, q)) t)).length ≤
        space k A w.length b q := by
  classical
  let result := RootDecision.boundaryDecision M w (q * b)
  let values : ℕ → Option Bool := fun σ =>
    if actualSchedule (MultiTapePTM.ofDeterministic M) w b (q := q) = scheduleOfNat k q σ
    then result else none
  have hstep : ∀ σ < 3 ^ ((k + 1) * q), ∃ T,
      (machine E k).runFrom w (.inl ((w.length, b, q), σ, none)) T =
        .inl (match values σ with
          | none => ((w.length, b, q), σ + 1, none)
          | some answer => ((w.length, b, q), σ, some answer)) ∧
      ∀ t ≤ T, (encState E ((machine E k).runFrom w
        (.inl ((w.length, b, q), σ, none)) t)).length ≤ space k A w.length b q := by
    intro σ hσ
    obtain ⟨U, hhaltU, houtU, hsizeU⟩ := hE w b q σ hσ
    obtain ⟨T, hle, hhalt, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
      E.machine w _ U hhaltU
    have hvalid : ScheduleCounter.valid k (σ, q) = true :=
      (ScheduleCounter.valid_eq_true_iff k σ q).mpr hσ
    have hrun := runFrom_one E (w.length, b, q) w σ T hvalid hpre hhalt
    have houtcome : E.outcome ((w.length, b, q),
        E.machine.runFrom w (E.start (w.length, b, σ, q)) T) = values σ := by
      rw [hstate]
      exact houtU
    refine ⟨T + 2, ?_, ?_⟩
    · cases hv : values σ <;>
        simpa only [resume, inputLength, blockWidth, horizon, houtcome, hv] using hrun
    · have hpending : pending k ((w.length, b, q), σ, none) = true := by
        simpa only [pending, Option.isSome_none, Bool.not_false, Bool.true_and] using hvalid
      exact runFrom_one_encoding_le E A w.length b q σ none w T hpending hpre hhalt
        (fun u hu => hsizeU u (hu.trans hle))
  have hsafe : ∀ σ < 3 ^ ((k + 1) * q), values σ = none ∨ values σ = result := by
    intro σ _
    dsimp only [values]
    split <;> simp
  have hcomplete : result ≠ none → ∃ σ < 3 ^ ((k + 1) * q), values σ = result := by
    intro _
    obtain ⟨σ, hvalid, hschedule⟩ := ScheduleCounter.exists_valid_schedule
      (actualSchedule (MultiTapePTM.ofDeterministic M) w b (q := q))
    refine ⟨σ, (ScheduleCounter.valid_eq_true_iff k σ q).mp hvalid, ?_⟩
    dsimp only [values]
    simp only [hschedule, ↓reduceIte]
  have hcaller : ∀ σ ≤ 3 ^ ((k + 1) * q), ∀ result : Option Bool,
      (encState E (.inl ((w.length, b, q), σ, result))).length ≤
        space k A w.length b q := by
    intro σ hσ result
    have hc := caller_encoding_le k w.length b q σ result hσ
    change (encCaller ((w.length, b, q), σ, result)).length + 1 ≤ _
    dsimp only [space]
    omega
  obtain ⟨T, σ, hrun, hhalt, hspace⟩ := exists_runFrom_candidates E (w.length, b, q) w
    values result (space k A w.length b q) hcaller hstep hsafe hcomplete
  refine ⟨T, ?_, ?_, hspace⟩
  · rw [hrun]
    exact hhalt
  · rw [hrun]
    rfl

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch
