/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearchSpace
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchCorrect
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.CallBounds
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt

/-!
# Increasing time guesses recover the source machine's decision

Each guess invokes the complete native schedule search with a correct evaluator. Source
configurations are stationary after halting, so every returned decision agrees with the
original halted computation. A guess at least the source halting time is covered by its
parameters and returns a decision. The final guess is bounded by the larger of that time and the
positive initial input-length guess.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.OuterSearch

variable {k : ℕ} {Q : Type}

private theorem boundaryDecision_of_halted (M : MultiTapeTM k Bool Q) (w : List Bool)
    (τ clock : ℕ) (hhalt : (M.runFrom (Cfg.init M.q₀ w) τ).Halted) (hle : τ ≤ clock) :
    RootDecision.boundaryDecision M w clock =
      some (decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])) := by
  classical
  unfold RootDecision.boundaryDecision
  rw [MultiTapeTM.runFrom_eq_of_halt M _ hle hhalt]
  have hstate : (M.runFrom (Cfg.init M.q₀ w) τ).state = none := hhalt
  simp only [hstate, Option.isNone_none, ↓reduceIte]

private theorem boundaryDecision_safe (M : MultiTapeTM k Bool Q) (w : List Bool)
    (τ clock : ℕ) (hhalt : (M.runFrom (Cfg.init M.q₀ w) τ).Halted) :
    RootDecision.boundaryDecision M w clock = none ∨
      RootDecision.boundaryDecision M w clock =
        some (decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])) := by
  classical
  by_cases hle : τ ≤ clock
  · exact Or.inr (boundaryDecision_of_halted M w τ clock hhalt hle)
  · cases hv : RootDecision.boundaryDecision M w clock with
    | none => exact Or.inl rfl
    | some result =>
      have hclock : (M.runFrom (Cfg.init M.q₀ w) clock).Halted := by
        dsimp only [RootDecision.boundaryDecision] at hv
        split at hv
        · rename_i hstate
          exact Option.isNone_iff_eq_none.mp hstate
        · cases hv
      have hs := boundaryDecision_of_halted M w clock τ hclock (by omega)
      have hc := boundaryDecision_of_halted M w clock clock hclock le_rfl
      have ht := boundaryDecision_of_halted M w τ τ hhalt le_rfl
      rw [hv] at hc
      exact Or.inr (hc.trans (hs.symm.trans ht))

/-- Every candidate's schedule search reaches a first halt with its exact bounded decision. -/
theorem exists_first_candidate {E : ScheduleSearch.Evaluator} {M : MultiTapeTM k Bool Q}
    {A : ℕ → ℕ → ℕ → ℕ} (hE : E.Correct M A) (P : Parameters) (w : List Bool) (guess : ℕ) :
    ∃ T,
      (∀ t < T, (ScheduleSearch.machine E k).halted
        ((ScheduleSearch.machine E k).runFrom w
          (ScheduleSearch.initial E (w.length, P.blockWidth guess, P.horizon guess)) t) =
            false) ∧
      (ScheduleSearch.machine E k).halted ((ScheduleSearch.machine E k).runFrom w
        (ScheduleSearch.initial E (w.length, P.blockWidth guess, P.horizon guess)) T) = true ∧
      ScheduleSearch.answer ((ScheduleSearch.machine E k).runFrom w
        (ScheduleSearch.initial E (w.length, P.blockWidth guess, P.horizon guess)) T) =
          RootDecision.boundaryDecision M w (P.horizon guess * P.blockWidth guess) ∧
      ∀ t ≤ T, (ScheduleSearch.encState E ((ScheduleSearch.machine E k).runFrom w
        (ScheduleSearch.initial E (w.length, P.blockWidth guess, P.horizon guess)) t)).length ≤
          ScheduleSearch.space k A w.length (P.blockWidth guess) (P.horizon guess) := by
  have : NeZero (P.blockWidth guess) := ⟨(P.blockWidth_pos guess).ne'⟩
  obtain ⟨U, hhalt, hans, hspace⟩ := ScheduleSearch.exists_runFrom_boundaryDecision hE w
    (P.blockWidth guess) (P.horizon guess)
  obtain ⟨T, hle, hT, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
    (ScheduleSearch.machine E k) w _ U hhalt
  exact ⟨T, hpre, hT, by rw [hstate]; exact hans,
    fun t ht => hspace t (ht.trans hle)⟩

/-- A candidate call consumes its first-halt search clocks plus one entry and one return. -/
theorem runFrom_one (E : ScheduleSearch.Evaluator) (P : Parameters)
    (w : List Bool) (guess T : ℕ)
    (hpre : ∀ t < T, (ScheduleSearch.machine E k).halted
      ((ScheduleSearch.machine E k).runFrom w
        (ScheduleSearch.initial E (w.length, P.blockWidth guess, P.horizon guess)) t) = false)
    (hhalt : (ScheduleSearch.machine E k).halted ((ScheduleSearch.machine E k).runFrom w
      (ScheduleSearch.initial E (w.length, P.blockWidth guess, P.horizon guess)) T) = true) :
    (machine E k P).runFrom w (.inl (w.length, guess, none)) (T + 2) =
      .inl (resume E (w.length, guess, none) ((ScheduleSearch.machine E k).runFrom w
        (ScheduleSearch.initial E (w.length, P.blockWidth guess, P.horizon guess)) T)) := by
  apply QueryMachine.withCalls_runFrom_call
  · rfl
  · rfl
  · exact hpre
  · exact hhalt

/-- If the source machine halts, increasing native time guesses reaches exactly its Boolean
output decision at a first halt. The completed guess never exceeds `max (input.length+1) τ`. -/
theorem exists_first_decision {E : ScheduleSearch.Evaluator} {M : MultiTapeTM k Bool Q}
    {A : ℕ → ℕ → ℕ → ℕ} (hE : E.Correct M A) (P : Parameters)
    (w : List Bool) (τ : ℕ) (hhalt : (M.runFrom (Cfg.init M.q₀ w) τ).Halted) :
    ∃ T guess, guess ≤ max (w.length + 1) τ ∧
      (∀ t < T, (machine E k P).halted ((machine E k P).runFrom w (initial E w.length) t) =
        false) ∧
      (machine E k P).runFrom w (initial E w.length) T =
        .inl (w.length, guess, some (decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true]))) ∧
      (machine E k P).halted ((machine E k P).runFrom w (initial E w.length) T) = true ∧
      ∀ t ≤ T, (encState E ((machine E k P).runFrom w (initial E w.length) t)).length ≤
        space k A P w.length (max (w.length + 1) τ) := by
  classical
  let result := decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])
  let bound := max (w.length + 1) τ
  let value := fun guess => RootDecision.boundaryDecision M w
    (P.horizon guess * P.blockWidth guess)
  have hsafe (guess : ℕ) : value guess = none ∨ value guess = some result :=
    boundaryDecision_safe M w τ _ hhalt
  have hbound : value bound = some result := boundaryDecision_of_halted M w τ _ hhalt
    ((Nat.le_max_right _ _).trans (P.coverage bound))
  have hstep (guess : ℕ) (hguess : guess ≤ bound) : ∃ T,
      (machine E k P).runFrom w (.inl (w.length, guess, none)) T =
        .inl (match value guess with
          | none => (w.length, guess + 1, none)
          | some answer => (w.length, guess, some answer)) ∧
      ∀ t ≤ T, (encState E ((machine E k P).runFrom w (.inl (w.length, guess, none)) t)).length ≤
        space k A P w.length bound := by
    obtain ⟨T, hpre, hT, hans, hsize⟩ := exists_first_candidate hE P w guess
    have hrun := runFrom_one E P w guess T hpre hT
    have hnext : (encCaller (resume E (w.length, guess, none)
        ((ScheduleSearch.machine E k).runFrom w (ScheduleSearch.initial E
          (w.length, P.blockWidth guess, P.horizon guess)) T))).length ≤
        callerSpace w.length bound := by
      change (encCaller (match ScheduleSearch.answer _ with
        | none => (w.length, guess + 1, none)
        | some answer => (w.length, guess, some answer))).length ≤ _
      rw [hans]
      change (encCaller (match value guess with
        | none => (w.length, guess + 1, none)
        | some answer => (w.length, guess, some answer))).length ≤ callerSpace w.length bound
      cases hv : value guess with
      | none =>
        have hlt : guess < bound := by grind
        exact caller_encoding_le w.length bound (guess + 1) none (by omega)
      | some answer => exact caller_encoding_le w.length bound guess (some answer) hguess
    refine ⟨T + 2, ?_, ?_⟩
    · have hresume : resume E (w.length, guess, none)
          ((ScheduleSearch.machine E k).runFrom w (ScheduleSearch.initial E
            (w.length, P.blockWidth guess, P.horizon guess)) T) =
          (match value guess with
            | none => (w.length, guess + 1, none)
            | some answer => (w.length, guess, some answer)) := by
        change (match ScheduleSearch.answer _ with
          | none => (w.length, guess + 1, none)
          | some answer => (w.length, guess, some answer)) = _
        rw [hans]
      exact hrun.trans (congrArg Sum.inl hresume)
    · exact runFrom_one_encoding_le E A P w.length guess bound none w T rfl hguess hpre hT
        (fun t ht => (hsize t ht).trans
          (candidate_space_le k A P w.length bound guess hguess)) hnext
  have hlo : (encState E (.inl (w.length, w.length + 1, none))).length ≤
      space k A P w.length bound := by
    have := caller_encoding_le w.length bound (w.length + 1) none (Nat.le_max_left _ _)
    change (encCaller _).length + 1 ≤ _
    dsimp only [space]
    omega
  obtain ⟨U, ⟨-, hnone⟩ | ⟨guess, answer, -, hguess, hv, hrun⟩, hspace⟩ :=
    QueryMachine.exists_runFrom_search_encoding_le (M := machine E k P) (w := w) (encState E)
      (fun guess => .inl (w.length, guess, none)) value
      (fun guess answer => .inl (w.length, guess, some answer)) (hi := bound + 1) (by omega) hlo
      (fun guess _ hguess hv => by simpa only [hv] using hstep guess (by omega))
      (fun guess answer _ hguess hv => by simpa only [hv] using hstep guess (by omega))
  · simp only [hnone bound (Nat.le_max_left _ _) (by omega), reduceCtorEq] at hbound
  rw [Option.some.inj (hv.symm.trans ((hsafe guess).resolve_left (by simp [hv])))] at hrun
  have hU : (machine E k P).halted ((machine E k P).runFrom w (initial E w.length) U) = true := by
    change (machine E k P).halted ((machine E k P).runFrom w
      (.inl (w.length, w.length + 1, none)) U) = true
    rw [hrun]
    rfl
  obtain ⟨T, hle, hT, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
    (machine E k P) w (initial E w.length) U hU
  exact ⟨T, guess, Nat.le_of_lt_succ hguess, hpre, hstate.trans hrun, hT,
    fun t ht => hspace t (ht.trans hle)⟩

end Turing.MultiTapePTM.BlockComputation.OuterSearch
