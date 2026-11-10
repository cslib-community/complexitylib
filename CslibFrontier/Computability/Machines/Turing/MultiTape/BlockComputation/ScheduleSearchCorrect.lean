/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.InitializedEvaluatorCorrect
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.RootDecisionCorrect
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt

/-!
# Exact finite schedule search on the original input

Each counter invokes the complete initialized evaluator. Wrong schedules have no outcome;
the actual schedule gives precisely the simulated boundary's halted decision. Exhausting the
native range guard therefore returns no decision exactly when that boundary is still live.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleSearch

open Cslib.TreeEval.Ary Cslib.TreeEval.Ary.Packed

variable {k s : ℕ} {Q : Type}

/-- One actual initialized evaluation returns the classification of the existing tree root at
its first halt, retaining its physical-clock storage bound. -/
theorem exists_first_outcome [Finite Q] (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (b : ℕ) [NeZero b] (σ q : ℕ) :
    ∃ T,
      (∀ t < T, (InitializedEvaluator.machine M e).halted
        ((InitializedEvaluator.machine M e).runFrom w
          (InitializedEvaluator.start k s (w.length, b, σ, q)) t) = false) ∧
      (InitializedEvaluator.machine M e).halted ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (w.length, b, σ, q)) T) = true ∧
      outcome e ((w.length, b, q), (InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (w.length, b, σ, q)) T) =
        RootDecision.classify k e (b, List.ofFn
          (encodedTree (MultiTapePTM.ofDeterministic M) w b
            (scheduleOfNat k q σ) e).eval) ∧
      ∀ t ≤ T, (InitializedEvaluator.encState ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (w.length, b, σ, q)) t)).length ≤
        InitializedEvaluator.allowance k s Q w.length b σ q := by
  obtain ⟨U, bank, hrun, hdecode, hhalt, hsize⟩ :=
    InitializedEvaluator.exists_runFrom_decode_root M e w b σ q
  obtain ⟨T, hle, hT, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
    (InitializedEvaluator.machine M e) w _ U hhalt
  refine ⟨T, hpre, hT, ?_, ?_⟩
  · rw [hstate, hrun]
    change RootDecision.classify k e (b, _) = _
    rw [hdecode]
  · intro t ht
    exact hsize t (ht.trans hle)

/-- Entry and return add exactly two clocks to the first-halt evaluator run. -/
theorem runFrom_one (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (args : Args)
    (w : List Bool) (σ T : ℕ) (hvalid : ScheduleCounter.valid k (σ, (horizon args)) = true)
    (hpre : ∀ t < T, (InitializedEvaluator.machine M e).halted
      ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (inputLength args, blockWidth args, σ, horizon args))
          t) = false)
    (hhalt : (InitializedEvaluator.machine M e).halted
      ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (inputLength args, blockWidth args, σ, horizon args))
          T) = true) :
    (machine M e).runFrom w (.inl (args, σ, none)) (T + 2) =
      .inl (resume e (args, σ, none) ((InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (inputLength args, blockWidth args, σ, horizon args))
          T)) := by
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
theorem exists_runFrom_candidates [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (args : Args) (w : List Bool) (values : ℕ → Option Bool) (result : Option Bool) (B : ℕ)
    (hcaller : ∀ σ ≤ 3 ^ ((k + 1) * (horizon args)), ∀ result : Option Bool,
      (encState (.inl (args, σ, result) : State k Q)).length ≤ B)
    (hstep : ∀ σ < 3 ^ ((k + 1) * (horizon args)), ∃ T,
      (machine M e).runFrom w (.inl (args, σ, none)) T =
        .inl (match values σ with
          | none => (args, σ + 1, none)
          | some answer => (args, σ, some answer)) ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (.inl (args, σ, none)) t)).length ≤ B)
    (hsafe : ∀ σ < 3 ^ ((k + 1) * (horizon args)), values σ = none ∨ values σ = result)
    (hcomplete : result ≠ none → ∃ σ < 3 ^ ((k + 1) * (horizon args)), values σ = result) :
    ∃ T σ, (machine M e).runFrom w (initial args) T = .inl (args, σ, result) ∧
      (machine M e).halted (.inl (args, σ, result)) = true ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial args) t)).length ≤ B := by
  obtain ⟨T, ⟨hrun, hnone⟩ | ⟨σ, answer, -, hσ, hv, hrun⟩, hB⟩ :=
    QueryMachine.exists_runFrom_search_encoding_le (M := machine M e) (w := w) encState
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

/-- Sequential native schedule search returns exactly the original machine's bounded halted
decision. Every candidate is evaluated on the original input; no lookup or supplier oracle is
assumed, and a live boundary exhausts the schedule range with no decision. -/
theorem exists_runFrom_boundaryDecision [Finite Q]
    (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s) (w : List Bool)
    (b : ℕ) [NeZero b] (q : ℕ) :
    ∃ T, (machine M e).halted
        ((machine M e).runFrom w (initial (w.length, b, q)) T) = true ∧
      answer ((machine M e).runFrom w (initial (w.length, b, q)) T) =
        RootDecision.boundaryDecision M w (q * b) ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial (w.length, b, q)) t)).length ≤
        space k s Q w.length b q := by
  classical
  let values : ℕ → Option Bool := fun σ => RootDecision.classify k e
    (b, List.ofFn (encodedTree (MultiTapePTM.ofDeterministic M) w b
      (scheduleOfNat k q σ) e).eval)
  let result := RootDecision.boundaryDecision M w (q * b)
  have hsemantic (σ : ℕ) : values σ =
      if actualSchedule (MultiTapePTM.ofDeterministic M) w b (q := q) = scheduleOfNat k q σ
      then result else none := by
    change RootDecision.classify k e (b, List.ofFn
      (encodedTree (MultiTapePTM.ofDeterministic M) w b (scheduleOfNat k q σ) e).eval) = _
    rw [RootDecision.classify_ofFn_eq_decision_decode]
    exact RootDecision.decision_eval_eq_boundary M e w b σ
  have hstep : ∀ σ < 3 ^ ((k + 1) * q), ∃ T,
      (machine M e).runFrom w (.inl ((w.length, b, q), σ, none)) T =
        .inl (match values σ with
          | none => ((w.length, b, q), σ + 1, none)
          | some answer => ((w.length, b, q), σ, some answer)) ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w
        (.inl ((w.length, b, q), σ, none)) t)).length ≤ space k s Q w.length b q := by
    intro σ hσ
    obtain ⟨T, hpre, hhalt, houtcome, hsize⟩ := exists_first_outcome M e w b σ q
    have hvalid : ScheduleCounter.valid k (σ, q) = true :=
      (ScheduleCounter.valid_eq_true_iff k σ q).mpr hσ
    have hrun := runFrom_one M e (w.length, b, q) w σ T hvalid hpre hhalt
    have houtcome' : outcome e ((w.length, b, q), (InitializedEvaluator.machine M e).runFrom w
        (InitializedEvaluator.start k s (w.length, b, σ, q)) T) = values σ := houtcome
    refine ⟨T + 2, ?_, ?_⟩
    · cases hv : values σ <;>
        simpa only [resume, inputLength, blockWidth, horizon, houtcome', hv] using hrun
    · have hpending : pending k ((w.length, b, q), σ, none) = true := by
        simpa only [pending, Option.isSome_none, Bool.not_false, Bool.true_and] using hvalid
      have hsize' : ∀ u ≤ T, (InitializedEvaluator.encState
          ((InitializedEvaluator.machine M e).runFrom w
            (InitializedEvaluator.start k s (w.length, b, σ, q)) u)).length ≤
          candidateSpace k s Q w.length b q := by
        intro u hu
        exact (hsize u hu).trans (candidate_allowance_le k s Q w.length b q σ hσ.le)
      exact runFrom_one_encoding_le M e w.length b q σ none w T
        hpending hpre hhalt hsize'
  have hsafe : ∀ σ < 3 ^ ((k + 1) * q), values σ = none ∨ values σ = result := by
    intro σ _
    rw [hsemantic]
    split <;> simp
  have hcomplete : result ≠ none → ∃ σ < 3 ^ ((k + 1) * q), values σ = result := by
    intro _
    obtain ⟨σ, hvalid, hschedule⟩ := ScheduleCounter.exists_valid_schedule
      (actualSchedule (MultiTapePTM.ofDeterministic M) w b (q := q))
    refine ⟨σ, (ScheduleCounter.valid_eq_true_iff k σ q).mp hvalid, ?_⟩
    rw [hsemantic]
    simp only [hschedule, ↓reduceIte]
  have hcaller : ∀ σ ≤ 3 ^ ((k + 1) * q), ∀ result : Option Bool,
      (encState (.inl ((w.length, b, q), σ, result) : State k Q)).length ≤
        space k s Q w.length b q := by
    intro σ hσ result
    have hc := caller_encoding_le k w.length b q σ result hσ
    change (encCaller ((w.length, b, q), σ, result)).length + 1 ≤ _
    dsimp only [space]
    omega
  obtain ⟨T, σ, hrun, hhalt, hspace⟩ := exists_runFrom_candidates M e (w.length, b, q) w
    values result (space k s Q w.length b q) hcaller hstep hsafe hcomplete
  refine ⟨T, ?_, ?_, hspace⟩
  · rw [hrun]
    exact hhalt
  · rw [hrun]
    rfl

end Turing.MultiTapePTM.BlockComputation.ScheduleSearch
