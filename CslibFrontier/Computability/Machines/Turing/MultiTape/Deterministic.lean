/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- `ComputableInTimeAndSpace.exists_no_work_tapes` is from cslib PR #1138 @b1635b2e.

public import Cslib.Computability.Machines.Turing.MultiTape.Deterministic
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Space

/-!
# Runs one step at a time, the halting step, and machines computing in zero space

The additions of Christian Reitwiessner's branch `crei/tidy-universal` to
`Cslib.Computability.Machines.Turing.MultiTape.Deterministic`, together with the addition of cslib
PR #1138: runs one step or one phase at a time, the time bound of a deterministic machine as a
halted run, the step at which a run halts, the output emitted in `t` steps, and machines computing
in zero space.

## Main definitions

* `Turing.MultiTapeTM.HaltsAt`: the run from a configuration halts at exactly a given step.

## Main results

* `Turing.MultiTapeTM.runFrom_succ`, `Turing.MultiTapeTM.runFrom_add`: a run, one step or one phase
  at a time.
* `Turing.MultiTapeTM.runsInTime_iff_halted`: a deterministic machine runs in time `t` exactly when
  it has halted after `t` steps.
* `Turing.MultiTapeTM.exists_haltsAt`: a halted run halts at some step.
* `Turing.MultiTapeTM.length_output_runFrom_le`: in `t` steps a machine emits at most `t` symbols.
* `Turing.MultiTapeTM.ComputableInTimeAndSpace.exists_no_work_tapes`: a function computable in zero
  space is computable by a machine without work tapes.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {State Symbol : Type*} {input : List Symbol}
variable {tm : MultiTapeTM k Symbol State}

/-- One more step of a run. -/
lemma runFrom_succ (cfg : Cfg k Symbol State input) (t : ℕ) :
    tm.runFrom cfg (t + 1) = tm.step (tm.runFrom cfg t) :=
  Function.iterate_succ_apply' _ _ _

/-- A run of one step. -/
lemma runFrom_one (cfg : Cfg k Symbol State input) : tm.runFrom cfg 1 = tm.step cfg := rfl

/-- A run splits at any intermediate step. -/
lemma runFrom_add (cfg : Cfg k Symbol State input) (m n : ℕ) :
    tm.runFrom cfg (m + n) = tm.runFrom (tm.runFrom cfg m) n := by
  rw [runFrom, Nat.add_comm, Function.iterate_add_apply]
  rfl

/-- A deterministic machine runs in time `t` exactly when it has halted after `t` steps. -/
lemma runsInTime_iff_halted {input : List Symbol} {t : ℕ} :
    tm.RunsInTime input t ↔ (tm.runFrom (tm.initCfg input) t).Halted := by
  refine ⟨fun h => ?_, fun h p hp => ?_⟩
  · -- apply the time bound to the computation path of length `t`
    -- vendored: the path is `ComputationPath.ofDeterministic`, upstream since cslib #1117
    exact computationPath_last_eq_runFrom (.ofDeterministic tm input t) ▸
      h (.ofDeterministic tm input t) le_rfl
  · rw [computationPath_last_eq_runFrom p, runFrom_eq_of_halt _ _ hp h]
    exact h

/-- The machine `tm` started in `cfg` halts at step `t`: it is halted after `t` steps and not
halted after any smaller number of steps. -/
def HaltsAt (tm : MultiTapeTM k Symbol State) {input : List Symbol}
    (cfg : Cfg k Symbol State input) (t : ℕ) : Prop :=
  (tm.runFrom cfg t).Halted ∧ ∀ s < t, ¬(tm.runFrom cfg s).Halted

namespace HaltsAt

variable {input : List Symbol} {cfg : Cfg k Symbol State input} {s t : ℕ}

lemma halted (h : tm.HaltsAt cfg t) : (tm.runFrom cfg t).Halted := h.1

lemma not_halted (h : tm.HaltsAt cfg t) (hs : s < t) : ¬(tm.runFrom cfg s).Halted := h.2 s hs

/-- The halting step is the first step at which the machine is halted. -/
lemma le_of_halted (h : tm.HaltsAt cfg t) (hs : (tm.runFrom cfg s).Halted) : t ≤ s :=
  Nat.le_of_not_lt fun hlt => h.not_halted hlt hs

/-- The halting step is unique. -/
lemma unique (h₁ : tm.HaltsAt cfg s) (h₂ : tm.HaltsAt cfg t) : s = t :=
  Nat.le_antisymm (h₁.le_of_halted h₂.halted) (h₂.le_of_halted h₁.halted)

/-- From the halting step on, the configuration does not change. -/
lemma runFrom_eq (h : tm.HaltsAt cfg t) (hts : t ≤ s) : tm.runFrom cfg s = tm.runFrom cfg t :=
  runFrom_eq_of_halt tm cfg hts h.halted

end HaltsAt

/-- A run that is halted after `t` steps halts at some step `u ≤ t`. -/
lemma exists_haltsAt {input : List Symbol} {cfg : Cfg k Symbol State input} {t : ℕ}
    (hhalt : (tm.runFrom cfg t).Halted) : ∃ u ≤ t, tm.HaltsAt cfg u := by
  classical
  have hex : ∃ n, (tm.runFrom cfg n).Halted := ⟨t, hhalt⟩
  exact ⟨Nat.find hex, Nat.find_min' hex hhalt, Nat.find_spec hex,
    fun s hs => Nat.find_min hex hs⟩

/-- A run that is halted after some number of steps halts at exactly one step. -/
lemma existsUnique_haltsAt {input : List Symbol} {cfg : Cfg k Symbol State input} {t : ℕ}
    (hhalt : (tm.runFrom cfg t).Halted) : ∃! u, tm.HaltsAt cfg u :=
  let ⟨u, _, hu⟩ := exists_haltsAt hhalt
  ⟨u, hu, fun _ h => h.unique hu⟩

/-- In `t` steps the machine emits at most `t` symbols. -/
lemma length_output_runFrom_le (tm : MultiTapeTM k Symbol State)
    (cfg : Cfg k Symbol State input) (t : ℕ) :
    (tm.runFrom cfg t).output.length ≤ cfg.output.length + t := by
  induction t with
  | zero => simp [runFrom]
  | succ t ih =>
    rw [runFrom_succ]
    cases hq : (tm.runFrom cfg t).state with
    | none => rw [step_of_halt hq]; omega
    | some q =>
      rw [step_of_state hq, Action.apply_output, List.length_append]
      grind [Option.length_toList_le]

/-- A function computable in zero space is computable by a machine without work tapes, within the
same bounds, since every work tape costs at least one cell (`MultiTapeNTM.RunsInSpace.le`). The
domain must be nonempty: otherwise the machine is never run and its number of tapes is arbitrary.
-/
theorem ComputableInTimeAndSpace.exists_no_work_tapes {α β : Type*} [Nonempty α]
    {encIn : α ↪ List Bool} {encOut : β ↪ List Bool} {f : α → β} {t : α → ℕ}
    (h : ComputableInTimeAndSpace f encIn encOut t (fun _ => 0)) :
    ∃ (State : Type) (_ : Finite State) (tm : MultiTapeTM 0 Bool State),
      ComputesFunInTimeAndSpace tm encIn encOut f t (fun _ => 0) := by
  obtain ⟨k, State, hfin, tm, htm⟩ := h
  obtain rfl : k = 0 := Nat.le_zero.mp (htm (Classical.arbitrary α)).2.2.le
  exact ⟨State, hfin, tm, htm⟩

end Turing.MultiTapeTM
