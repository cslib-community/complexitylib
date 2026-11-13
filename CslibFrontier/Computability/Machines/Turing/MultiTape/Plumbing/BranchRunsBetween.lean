/-
Copyright (c) 2026 Sam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sam
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Branch
-- Reuse Branch.runFrom_mapState and the branch transition body in this companion specification.
import all CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.Branch
public import CslibFrontier.Computability.Machines.Turing.MultiTape.Plumbing.RunsBetween

/-!
# Branching from arbitrary work-tape cursors

The work-tape branch combinator can inspect a cell at a shifted cursor, not only the first cell
of an origin-aligned word. These run specifications charge one selection transition, followed
by the selected machine's clock. They use the general per-transition work-space bound.
-/

public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol S₁ S₂ : Type*} {input : List Symbol}
  {i : Fin k} {tm₁ : MultiTapeTM k Symbol S₁} {tm₂ : MultiTapeTM k Symbol S₂}

private theorem branch_step_config (c : Cfg k Symbol Unit input) :
    (branch i tm₁ tm₂).step (c.withState (some none)) =
      if c.workTapeSymbols i = none then
        (c.withState (some tm₂.q₀)).mapState (Option.map (some ∘ .inr))
      else (c.withState (some tm₁.q₀)).mapState (Option.map (some ∘ .inl)) := by
  rw [step_of_state rfl]
  have hw : (c.withState (some (none : Option (S₁ ⊕ S₂)))).workTapeSymbols =
      c.workTapeSymbols := rfl
  rw [hw]
  cases hs : c.workTapeSymbols i <;>
    refine Cfg.ext ?_ ?_ ?_ ?_ ?_ <;>
    simp [branch, hs, Action.apply, Cfg.withState, Cfg.mapState]

/-- A nonblank inspected cell selects the first run, with one extra transition. The source
configuration may have arbitrary tape contents and cursor positions. -/
theorem RunsBetween.branch_of_ne_none {c c' : Cfg k Symbol Unit input} {t s : ℕ}
    (h : RunsBetween tm₁ c c' t s) (hc : c.workTapeSymbols i ≠ none) :
    RunsBetween (branch i tm₁ tm₂) c c' (t + 1) (k * (t + 2)) := by
  apply RunsBetween.of_runFrom
  change (branch i tm₁ tm₂).runFrom (c.withState (some none)) (t + 1) = _
  rw [Nat.add_comm t 1, runFrom_add, runFrom_one, branch_step_config, ite_eq_right hc,
    Branch.runFrom_mapState (tm := tm₁) (fun _ _ _ => by simp [branch]), h.1]
  rfl

/-- A blank inspected cell selects the second run, with one extra transition. The source
configuration may have arbitrary tape contents and cursor positions. -/
theorem RunsBetween.branch_of_none {c c' : Cfg k Symbol Unit input} {t s : ℕ}
    (h : RunsBetween tm₂ c c' t s) (hc : c.workTapeSymbols i = none) :
    RunsBetween (branch i tm₁ tm₂) c c' (t + 1) (k * (t + 2)) := by
  apply RunsBetween.of_runFrom
  change (branch i tm₁ tm₂).runFrom (c.withState (some none)) (t + 1) = _
  rw [Nat.add_comm t 1, runFrom_add, runFrom_one, branch_step_config, ite_eq_left hc,
    Branch.runFrom_mapState (tm := tm₂) (fun _ _ _ => by simp [branch]), h.1]
  rfl

end Turing.MultiTapeTM
