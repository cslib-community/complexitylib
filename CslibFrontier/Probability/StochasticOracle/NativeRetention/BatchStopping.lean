/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.NativeRetention.BatchAdmission
public import CslibFrontier.Probability.StochasticOracle.AdaptiveSelection
import Mathlib.Tactic

/-!
# Computed native guards and actual retained progress

[Wang2027], Theorem 5(1), PDF p. 12, Appendix A.5 p. 16: the upper policy
stops at retained completion or its configured horizon. This module identifies
its actual parsed runtime retention with `AdaptiveSelection.selected`, without a
retention-law premise. It derives the guard from that history and the remaining
budgets, and derives completion from a productive-count threshold.

The decoder processes complete raw replies in their actual chronological order;
no finite response alphabet or independent responses are required. Source admission
and history authentication are supplied by `BatchAdmission.run_aligned` for the
constructed native program. This is the pathwise guard/progress connection.
`BatchReceipts` and `BatchUpper` build its selected-epoch and numerical receipt-cost
transfer. Complete certified-output success/deadline transfer and the common-oracle
optimum comparison remain open.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.NativeRetention.BatchStopping
open Turing Turing.MultiTapeMachine NativeOpenExecution ConcurrentBatch
open PartialCover AdaptiveSelection

/-- The actual packet parser followed by the executable candidate normalization.
It reads no future response; the instance and interface are fixed runtime data. -/
@[expose] def proposal (w : Packets.Work) (_ : List Word) (word : Word) : List (Finset ℕ) :=
  (Packets.families w.opportunities w.system.rows.length word).map
    (fun P => (normalize w.system P).toFinset)

/-- The native rational computation and abstract real-valued local-test retention
agree on the entire actual raw history, without a supplied output/retention contract. -/
theorem retained_eq (w : Packets.Work) (hx : Valid w.system) :
    (retain (Packets.assemble w)).toFinset =
      selected (instanceOf w.system hx) w.system.rho (proposal w) w.history := by
  have hv : Valid (Packets.assemble w) := ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  change _ = selected _ _ (fun _ word =>
    (Packets.families w.opportunities w.system.rows.length word).map
      (fun P => (normalize w.system P).toFinset)) w.history
  rw [selected_eq_retain]
  have hi : instanceOf (Packets.assemble w) hv = instanceOf w.system hx := by
    unfold instanceOf
    congr 1
  have hr := retain_eq (Packets.assemble w) hv
  rw [hi] at hr
  simpa only [Packets.assemble, normalize, population, List.map_flatMap,
    List.flatMap_map, Function.comp_def] using hr

/-- Completion is computed from retained original sets, not all revealed sets. -/
theorem completion_iff (w : Packets.Work) (hx : Valid w.system) :
    (Packets.decision w).1 = true ↔
      (instanceOf w.system hx).covered
        (selected (instanceOf w.system hx) w.system.rho (proposal w) w.history) =
          (instanceOf w.system hx).ground := by
  have hv : Valid (Packets.assemble w) := ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  have hc := complete_eq (Packets.assemble w) hv
  change complete (Packets.assemble w) = true ↔ _
  rw [← retained_eq w hx]
  exact hc

/-- The native guard is live exactly when all three allowances remain and the
actually retained original sets are incomplete. A latency reservation is not an
observation of physical elapsed time. -/
theorem live_iff (state : RuntimeControl.State) (hx : Valid state.work.system) :
    RuntimeControl.stopped state = false ↔
      0 < state.turns ∧ 0 < state.opportunities ∧ 0 < state.allotments ∧
      (instanceOf state.work.system hx).covered
        (selected (instanceOf state.work.system hx) state.work.system.rho
          (proposal state.work) state.work.history) ≠ (instanceOf state.work.system hx).ground := by
  have hc := completion_iff state.work hx
  simp only [ne_eq, ← hc]
  cases hd : (Packets.decision state.work).1 <;>
    simp [RuntimeControl.stopped, hd, Nat.pos_iff_ne_zero, and_assoc]

/-- Productive-count progress forces the actual native stop and certified output.
The returned cover and dual bound are conclusions of the executed local test. -/
theorem count_completed (state : RuntimeControl.State) (hx : Valid state.work.system)
    (a : ℕ)
    (hc : (instanceOf state.work.system hx).ground.card ≤ a *
      count (productive (instanceOf state.work.system hx) state.work.system.rho
        (proposal state.work) a) state.work.history) :
    RuntimeControl.stopped state = true ∧
      RuntimeControl.result state = output (Packets.assemble state.work) ∧
      (instanceOf state.work.system hx).covered
        ((outputFamily (Packets.assemble state.work)).image Fin.val) =
          (instanceOf state.work.system hx).ground ∧
      (instanceOf state.work.system hx).cost
        ((outputFamily (Packets.assemble state.work)).image Fin.val) ≤
          (state.work.system.rho : ℝ) * ∑ e ∈ (instanceOf state.work.system hx).ground,
            (instanceOf state.work.system hx).dual e := by
  have hdone := (completion_iff state.work hx).mpr
    (count_completes _ _ _ a _ hc)
  have hv : Valid (Packets.assemble state.work) :=
    ⟨hx.weight_nonneg, hx.dual_nonneg, hx.feasible⟩
  refine ⟨?_, ?_, completed_output (Packets.assemble state.work) hv hdone⟩
  · simp [RuntimeControl.stopped, hdone]
  · exact ite_eq_left hdone

/-- Before the configured horizon the executed loop cannot stop merely because of
an allowance counter, provided the original opportunity/reservation budgets cover
that horizon. The remaining reason is precisely actual retained completion. -/
theorem run_live_before_horizon {P : Type} (env : Environment Unit P) (fuel : ℕ)
    (state : RuntimeControl.State) (channels : Unit → Channel Bool) (memory : Memory Unit P)
    (request : RuntimeControl.State → Word) (outcome : Feedback.Outcome P)
    (ho : outcome ∈ (Feedback.run env fuel state channels memory request).support)
    (hopps : state.turns ≤ state.opportunities) (hallot : state.turns ≤ state.allotments)
    (hbefore : outcome.memory.events.length < state.turns + memory.events.length)
    (hx : Valid outcome.state.work.system) :
    RuntimeControl.stopped outcome.state = false ↔
      (instanceOf outcome.state.work.system hx).covered
        (selected (instanceOf outcome.state.work.system hx) outcome.state.work.system.rho
          (proposal outcome.state.work) outcome.state.work.history) ≠
            (instanceOf outcome.state.work.system hx).ground := by
  have hb := Feedback.run_allowances env fuel state channels memory request outcome ho
  have ht : 0 < outcome.state.turns := by omega
  have hp : 0 < outcome.state.opportunities := by omega
  have ha : 0 < outcome.state.allotments := by omega
  simp only [live_iff outcome.state hx, ht, hp, ha, true_and]

end Cslib.Probability.StochasticOracle.NativeRetention.BatchStopping
