/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: submitted #1111 @3441fa81
-- `ComputableTidilyInTimeAndSpace.length_le` is from crei:crei/tidy-universal @7f7c0696
-- (unsubmitted).

public import Complexity.Computability.Machines.Turing.MultiTape.Plumbing.ExtendTapes
public import Cslib.Computability.Machines.Turing.MultiTape.Plumbing.Tidy.Defs

/-! # Basic semantic facts for tidy machine runs

Machine declarations are moved from their original module without changing programs or resource
formulas. Higher computability-calculus theorems remain in the original facade.
-/

@[expose] public section

namespace Turing.MultiTapeTM

variable {k : ℕ} {Symbol State : Type*} {tm : MultiTapeTM k Symbol State} {t s : ℕ}

namespace ComputesTidilyInTimeAndSpace

variable {input output : List Symbol}

/-- A tidy computation is a computation in the sense of
`Turing.MultiTapeTM.ComputesInTimeAndSpace`. -/
theorem computesInTimeAndSpace (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    tm.ComputesInTimeAndSpace input output t s := by
  obtain ⟨p, hh, hl, ht, hs⟩ := computesTidily_iff.mp h
  have hhead : p.head = tm.initCfg input := hh.trans (Cfg.init_eq_wordsCfg tm.q₀ input).symm
  have hrun : tm.runFrom (tm.initCfg input) p.time = wordsCfg input none (fun _ => []) output :=
    hhead ▸ (runPath_apply_eq_runFrom p (.last _)).symm.trans hl
  have hhalt : (tm.runFrom (tm.initCfg input) p.time).Halted := by rw [hrun]; rfl
  exact ⟨⟨p.time, hhalt, by rw [hrun]; rfl⟩,
    runsInTime_of_halted (runFrom_eq_of_halt tm _ ht hhalt ▸ hhalt),
    runsInSpace_of_runPath hhead (by rw [hl]; rfl) hs⟩

/-- A tidy computation within `t` steps emits at most `t` symbols. -/
theorem length_output_le (h : tm.ComputesTidilyInTimeAndSpace input output t s) :
    output.length ≤ t := by
  obtain ⟨p, hh, hl, ht, -⟩ := computesTidily_iff.mp h
  simpa [hh, hl, wordsCfg] using p.length_output_last_le.trans (Nat.add_le_add_left ht _)

/-- A tidy computation stays tidy with more work tapes, at one cell per added tape. -/
theorem extendTapes {k' : ℕ} (h : tm.ComputesTidilyInTimeAndSpace input output t s)
    (e : Fin k ↪ Fin k') :
    (tm.extendTapes e).ComputesTidilyInTimeAndSpace input output t (s + (k' - k)) := by
  refine (TransformsTapes.extendTapes h e).imp (fun _ _ ⟨hin, hws⟩ => ⟨hin, by subst hws; rfl⟩)
    (fun _ _ _ _ ⟨_, hws⟩ ⟨⟨hv, hout⟩, hx⟩ => ⟨funext fun l => ?_, hout⟩) le_rfl le_rfl
  by_cases hl : l ∈ Set.range e
  · obtain ⟨j, rfl⟩ := hl
    exact congrFun hv j
  · rw [hx l hl, hws]

end ComputesTidilyInTimeAndSpace

end Turing.MultiTapeTM
