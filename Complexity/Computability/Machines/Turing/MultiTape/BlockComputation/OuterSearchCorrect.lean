/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearch
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.OuterSearchSpace
public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleSearchCorrect
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.LogSpace.QueryMachine.FirstHalt

/-!
# Increasing time guesses recover the source machine's decision

Each guess invokes the complete native schedule search. Source configurations are stationary
after halting, so every returned decision agrees with the original halted computation. A guess
at least the source halting time covers that time and returns a decision. The final guess is
bounded by the larger of that time and the positive initial input-length guess.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.OuterSearch

variable {k s : ℕ} {Q : Type}

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
theorem exists_first_candidate [Finite Q] (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (guess : ℕ) :
    ∃ T,
      (∀ t < T, (ScheduleSearch.machine M e).halted
        ((ScheduleSearch.machine M e).runFrom w
          (ScheduleSearch.initial (w.length, BalancedParameters.blockWidth guess,
            BalancedParameters.horizon guess)) t) = false) ∧
      (ScheduleSearch.machine M e).halted ((ScheduleSearch.machine M e).runFrom w
        (ScheduleSearch.initial (w.length, BalancedParameters.blockWidth guess,
          BalancedParameters.horizon guess)) T) = true ∧
      ScheduleSearch.answer ((ScheduleSearch.machine M e).runFrom w
        (ScheduleSearch.initial (w.length, BalancedParameters.blockWidth guess,
          BalancedParameters.horizon guess)) T) = RootDecision.boundaryDecision M w
            (BalancedParameters.horizon guess * BalancedParameters.blockWidth guess) ∧
      ∀ t ≤ T, (ScheduleSearch.encState ((ScheduleSearch.machine M e).runFrom w
        (ScheduleSearch.initial (w.length, BalancedParameters.blockWidth guess,
          BalancedParameters.horizon guess)) t)).length ≤ ScheduleSearch.space k s Q w.length
            (BalancedParameters.blockWidth guess) (BalancedParameters.horizon guess) := by
  have : NeZero (BalancedParameters.blockWidth guess) :=
    ⟨(BalancedParameters.blockWidth_pos guess).ne'⟩
  obtain ⟨U, hhalt, hans, hspace⟩ := ScheduleSearch.exists_runFrom_boundaryDecision M e w
    (BalancedParameters.blockWidth guess) (BalancedParameters.horizon guess)
  obtain ⟨T, hle, hT, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
    (ScheduleSearch.machine M e) w _ U hhalt
  exact ⟨T, hpre, hT, by rw [hstate]; exact hans,
    fun t ht => hspace t (ht.trans hle)⟩

/-- A candidate call consumes its first-halt search clocks plus one entry and one return. -/
theorem runFrom_one (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (guess T : ℕ)
    (hpre : ∀ t < T, (ScheduleSearch.machine M e).halted
      ((ScheduleSearch.machine M e).runFrom w
        (ScheduleSearch.initial (w.length, BalancedParameters.blockWidth guess,
          BalancedParameters.horizon guess)) t) = false)
    (hhalt : (ScheduleSearch.machine M e).halted ((ScheduleSearch.machine M e).runFrom w
      (ScheduleSearch.initial (w.length, BalancedParameters.blockWidth guess,
        BalancedParameters.horizon guess)) T) = true) :
    (machine M e).runFrom w (.inl (w.length, guess, none)) (T + 2) =
      .inl (resume (w.length, guess, none) ((ScheduleSearch.machine M e).runFrom w
        (ScheduleSearch.initial (w.length, BalancedParameters.blockWidth guess,
          BalancedParameters.horizon guess)) T)) := by
  apply QueryMachine.withCalls_runFrom_call
  · rfl
  · rfl
  · exact hpre
  · exact hhalt

/-- If the source machine halts, increasing native time guesses reaches exactly its Boolean
output decision at a first halt. The completed guess never exceeds `max (input.length+1) τ`. -/
theorem exists_first_decision [Finite Q] (M : MultiTapeTM k Bool Q) (e : Q ≃ Fin s)
    (w : List Bool) (τ : ℕ) (hhalt : (M.runFrom (Cfg.init M.q₀ w) τ).Halted) :
    ∃ T guess, guess ≤ max (w.length + 1) τ ∧
      (∀ t < T, (machine M e).halted ((machine M e).runFrom w (initial w.length) t) = false) ∧
      (machine M e).runFrom w (initial w.length) T =
        .inl (w.length, guess, some (decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true]))) ∧
      (machine M e).halted ((machine M e).runFrom w (initial w.length) T) = true ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (initial w.length) t)).length ≤
        space k s Q w.length (max (w.length + 1) τ) := by
  classical
  let result := decide ((M.runFrom (Cfg.init M.q₀ w) τ).output = [true])
  let bound := max (w.length + 1) τ
  let value := fun guess => RootDecision.boundaryDecision M w
    (BalancedParameters.horizon guess * BalancedParameters.blockWidth guess)
  have hsafe (guess : ℕ) : value guess = none ∨ value guess = some result :=
    boundaryDecision_safe M w τ _ hhalt
  have hbound : value bound = some result := boundaryDecision_of_halted M w τ _ hhalt
    ((Nat.le_max_right _ _).trans (BalancedParameters.coverage bound))
  have hstep (guess : ℕ) (hguess : guess ≤ bound) : ∃ T,
      (machine M e).runFrom w (.inl (w.length, guess, none)) T =
        .inl (match value guess with
          | none => (w.length, guess + 1, none)
          | some answer => (w.length, guess, some answer)) ∧
      ∀ t ≤ T, (encState ((machine M e).runFrom w (.inl (w.length, guess, none)) t)).length ≤
        space k s Q w.length bound := by
    obtain ⟨T, hpre, hT, hans, hsize⟩ := exists_first_candidate M e w guess
    have hrun := runFrom_one M e w guess T hpre hT
    have hnext : (encCaller (resume (w.length, guess, none)
        ((ScheduleSearch.machine M e).runFrom w (ScheduleSearch.initial
          (w.length, BalancedParameters.blockWidth guess,
            BalancedParameters.horizon guess)) T))).length ≤
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
        have hlt : guess < bound := by
          by_contra h
          have heq : guess = bound := by omega
          rw [heq, hbound] at hv
          cases hv
        exact caller_encoding_le w.length bound (guess + 1) none (by omega)
      | some answer => exact caller_encoding_le w.length bound guess (some answer) hguess
    refine ⟨T + 2, ?_, ?_⟩
    · have hresume : resume (w.length, guess, none)
          ((ScheduleSearch.machine M e).runFrom w (ScheduleSearch.initial
            (w.length, BalancedParameters.blockWidth guess, BalancedParameters.horizon guess)) T) =
          (match value guess with
            | none => (w.length, guess + 1, none)
            | some answer => (w.length, guess, some answer)) := by
        change (match ScheduleSearch.answer _ with
          | none => (w.length, guess + 1, none)
          | some answer => (w.length, guess, some answer)) = _
        rw [hans]
      exact hrun.trans (congrArg Sum.inl hresume)
    · exact runFrom_one_encoding_le M e w.length guess bound none w T rfl hguess hpre hT
        (fun t ht => (hsize t ht).trans
          (candidate_space_le k s Q w.length bound guess hguess)) hnext
  have haux (n : ℕ) : ∀ guess, guess + n = bound →
      ∃ T final, final ≤ bound ∧ (machine M e).runFrom w (.inl (w.length, guess, none)) T =
        .inl (w.length, final, some result) ∧
        ∀ t ≤ T, (encState ((machine M e).runFrom w (.inl (w.length, guess, none)) t)).length ≤
          space k s Q w.length bound := by
    induction n with
    | zero =>
      intro guess heq
      have heq' : guess = bound := by omega
      obtain ⟨T, hT, hspace⟩ := hstep guess (by omega)
      refine ⟨T, guess, by omega, ?_, hspace⟩
      simpa only [heq', hbound] using hT
    | succ n ih =>
      intro guess heq
      obtain ⟨T, hT, hspace⟩ := hstep guess (by omega)
      cases hv : value guess with
      | none =>
        obtain ⟨U, final, hfinal, hU, hUspace⟩ := ih (guess + 1) (by omega)
        refine ⟨T + U, final, hfinal, ?_, ?_⟩
        · rw [QueryMachine.runFrom_add, hT, hv, hU]
        · intro t ht
          by_cases hbefore : t ≤ T
          · exact hspace t hbefore
          · obtain ⟨u, rfl⟩ := Nat.exists_eq_add_of_le (show T ≤ t by omega)
            rw [QueryMachine.runFrom_add, hT, hv]
            exact hUspace u (by omega)
      | some answer =>
        have hans : some answer = some result := by
          rcases hsafe guess with hnone | hans
          · rw [hv] at hnone
            cases hnone
          · exact hv.symm.trans hans
        refine ⟨T, guess, by omega, ?_, hspace⟩
        rw [hv] at hT
        rw [← hans]
        exact hT
  obtain ⟨U, guess, hguess, hrun, hspace⟩ := haux (bound - (w.length + 1)) (w.length + 1)
    (Nat.add_sub_of_le (Nat.le_max_left _ _))
  have hU : (machine M e).halted ((machine M e).runFrom w (initial w.length) U) = true := by
    change (machine M e).halted ((machine M e).runFrom w
      (.inl (w.length, w.length + 1, none)) U) = true
    rw [hrun]
    rfl
  obtain ⟨T, hle, hT, hpre, hstate⟩ := QueryMachine.exists_first_halt_le
    (machine M e) w (initial w.length) U hU
  exact ⟨T, guess, hguess, hpre, hstate.trans hrun, hT,
    fun t ht => hspace t (ht.trans hle)⟩

end Turing.MultiTapePTM.BlockComputation.OuterSearch
