/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Sam
-/

module
-- upstream: vendored crei:crei/tidy-universal @7f7c0696 (unsubmitted)
-- vendored: `spaceUsed` is `space` since cslib #1133

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.TransformsTapes

/-!
# Branching on a work tape

`branchOn test i tm₁ tm₂` selects a continuation by applying `test` to the inspected cell.
`branch i tm₁ tm₂` is its blank/nonblank specialization: it reads the cell under the head of
work tape `i` and then runs `tm₁` if that cell is not blank and `tm₂` if it is.
On a `Turing.wordsCfg` configuration the head of tape
`i` is on the first cell of its word, so the machine runs `tm₂` exactly when the word on tape `i`
is empty.

## Main definitions

* `Turing.MultiTapeTM.branchOn`: branching on a Boolean test of the inspected cell.
* `Turing.MultiTapeTM.branch`: the blank/nonblank specialization.

## Main results

* `Turing.MultiTapeTM.transformsTapes_branch`: a specification of `branch i tm₁ tm₂` from
  specifications of `tm₁` for a non-empty word on tape `i` and of `tm₂` for an empty one.
-/

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol S₁ S₂ : Type*} {input : List Symbol}

/-- Reads the cell under the head of work tape `i`, moving no head and writing nothing, then runs
`tm₁` if `test` returns true and `tm₂` otherwise. -/
public noncomputable def branchOn (test : Option Symbol → Bool) (i : Fin k)
    (tm₁ : MultiTapeTM k Symbol S₁) (tm₂ : MultiTapeTM k Symbol S₂) :
    MultiTapeTM k Symbol (Option (S₁ ⊕ S₂)) :=
  ofTr none fun q inp work =>
    match q with
    | none =>
      { inputTape := 0, workTapes := fun _ => (none, 0), output := none,
        state := some (some (if test (work i) then .inl tm₁.q₀ else .inr tm₂.q₀)) }
    | some (.inl q) =>
      let a := tm₁.tr q inp work
      { a with state := a.state.map (some ∘ .inl) }
    | some (.inr q) =>
      let a := tm₂.tr q inp work
      { a with state := a.state.map (some ∘ .inr) }

/-- Branch on whether the inspected work-tape cell is nonblank. -/
public noncomputable def branch (i : Fin k) (tm₁ : MultiTapeTM k Symbol S₁)
    (tm₂ : MultiTapeTM k Symbol S₂) : MultiTapeTM k Symbol (Option (S₁ ⊕ S₂)) :=
  branchOn Option.isSome i tm₁ tm₂

namespace Branch

variable {i : Fin k} {tm₁ : MultiTapeTM k Symbol S₁} {tm₂ : MultiTapeTM k Symbol S₂}

/-- If `branchOn test i tm₁ tm₂` acts in the state `f q` as `tm` acts in `q`, its runs
from such states follow the runs of `tm`. -/
lemma runFrom_mapState {S : Type*} {tm : MultiTapeTM k Symbol S} {f : S → Option (S₁ ⊕ S₂)}
    {test : Option Symbol → Bool}
    (htr : ∀ q inp work, (branchOn test i tm₁ tm₂).tr (f q) inp work =
      { tm.tr q inp work with state := (tm.tr q inp work).state.map f })
    (cfg : Cfg k Symbol S input) (n : ℕ) :
    (branchOn test i tm₁ tm₂).runFrom (cfg.mapState (Option.map f)) n =
      (tm.runFrom cfg n).mapState (Option.map f) := by
  refine (Function.Semiconj.iterate_right (fun c => ?_) n cfg).symm
  cases hq : c.state with
  | none => rw [step_of_halt hq, step_of_halt (by simp [hq])]
  | some q => rw [step_of_state hq, step_of_state (q := f q) (by simp [hq]), htr]; rfl

/-- The first step reads tape `i` and starts `tm₁` or `tm₂`. -/
lemma step_check (ws : Fin k → List Symbol) (out : List Symbol) :
    (branch i tm₁ tm₂).step (wordsCfg input (some none) ws out) =
      if ws i = [] then (wordsCfg input (some tm₂.q₀) ws out).mapState (Option.map (some ∘ .inr))
      else (wordsCfg input (some tm₁.q₀) ws out).mapState (Option.map (some ∘ .inl)) := by
  have hsym : (wordsCfg input (some (none : Option (S₁ ⊕ S₂))) ws out).workTapeSymbols i =
      (ws i).head? := by
    simp [Cfg.workTapeSymbols, wordsCfg, tapeOfList_zero]
  rw [step_of_state rfl]
  simp only [branch, branchOn, tr_ofTr, hsym]
  by_cases h : ws i = []
  · rw [ite_eq_left h, h]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply, Cfg.mapState, wordsCfg]
  · rw [ite_eq_right h]
    obtain ⟨a, l, hl⟩ := List.exists_cons_of_ne_nil h
    rw [hl]
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;> simp [Action.apply, Cfg.mapState, wordsCfg]

/-- If the first step starts `tm`, with its states mapped by `f`, then a specification of `tm`
gives one of `branchOn test i tm₁ tm₂`, with one more step and at most `k` more cells. -/
lemma transformsTapes_of_step {S : Type*} {tm : MultiTapeTM k Symbol S}
    {f : S → Option (S₁ ⊕ S₂)} {test : Option Symbol → Bool}
    (htr : ∀ q inp work, (branchOn test i tm₁ tm₂).tr (f q) inp work =
      { tm.tr q inp work with state := (tm.tr q inp work).state.map f })
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t s : ℕ}
    (hstep : ∀ input ws out, P input ws →
      (branchOn test i tm₁ tm₂).step (wordsCfg input (some none) ws out) =
        (wordsCfg input (some tm.q₀) ws out).mapState (Option.map f))
    (h : TransformsTapes tm P Q t s) :
    TransformsTapes (branchOn test i tm₁ tm₂) P Q (1 + t) (k + s) := by
  -- vendored: `TransformsTapes` is stated with run paths since cslib #1117
  refine transformsTapes_iff_runFrom.mpr fun input ws out hP => ?_
  obtain ⟨ws', e, hrun', hQ, hsp⟩ := transformsTapes_iff_runFrom.mp h input ws out hP
  rw [show (branchOn test i tm₁ tm₂).q₀ = none from rfl]
  refine ⟨ws', e, ?_, hQ, (space_add_le _ _ _).trans (Nat.add_le_add ?_ ?_)⟩
  · rw [runFrom_add, runFrom_one, hstep _ _ _ hP, runFrom_mapState htr, hrun']; rfl
  · -- the first step does not move any head
    refine space_le_of_workTapePos_const _ _ fun m hm => ?_
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hm with rfl | rfl
    · rfl
    · rw [runFrom_one, hstep _ _ _ hP]; rfl
  · rw [runFrom_one, hstep _ _ _ hP, space_eq_of_workTapePos (tm' := tm) _
      (wordsCfg input (some tm.q₀) ws out) t fun m _ => by rw [runFrom_mapState htr]; rfl]
    exact hsp

end Branch

open Branch in
/-- If `tm₁` performs the transformation `Q` within `t₁` steps and `s₁` cells whenever the word on
tape `i` is non-empty, and `tm₂` within `t₂` steps and `s₂` cells whenever it is empty, then
`branch i tm₁ tm₂` performs `Q` with one more step and at most `k` more cells. -/
public theorem transformsTapes_branch (i : Fin k)
    -- vendored: `tm₁` and `tm₂` are bound here, as `autoImplicit` is off
    {tm₁ : MultiTapeTM k Symbol S₁} {tm₂ : MultiTapeTM k Symbol S₂}
    {P : (input : List Symbol) → (Fin k → List Symbol) → Prop}
    {Q : (input : List Symbol) → (Fin k → List Symbol) → (Fin k → List Symbol) →
      List Symbol → Prop} {t₁ s₁ t₂ s₂ : ℕ}
    (h₁ : TransformsTapes tm₁ (fun inp ws => P inp ws ∧ ws i ≠ []) Q t₁ s₁)
    (h₂ : TransformsTapes tm₂ (fun inp ws => P inp ws ∧ ws i = []) Q t₂ s₂) :
    TransformsTapes (branch i tm₁ tm₂) P Q (max t₁ t₂ + 1) (max s₁ s₂ + k) := by
  intro input ws out hP
  by_cases hi : ws i = []
  · exact ((transformsTapes_of_step (test := Option.isSome) (f := some ∘ .inr)
      (fun _ _ _ => by simp [branchOn])
      (fun _ _ _ h => by
        change (branch i tm₁ tm₂).step _ = _
        rw [step_check, ite_eq_left h.2]) h₂).mono (by omega) (by omega))
      input ws out ⟨hP, hi⟩
  · exact ((transformsTapes_of_step (test := Option.isSome) (f := some ∘ .inl)
      (fun _ _ _ => by simp [branchOn])
      (fun _ _ _ h => by
        change (branch i tm₁ tm₂).step _ = _
        rw [step_check, ite_eq_right h.2]) h₁).mono (by omega) (by omega))
      input ws out ⟨hP, hi⟩

end Turing.MultiTapeTM
