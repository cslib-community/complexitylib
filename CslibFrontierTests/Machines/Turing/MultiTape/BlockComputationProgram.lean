/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of the HPV block computation as a program)

public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputationProgram
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputation.ImplicitPathCorrect

/-!
# Pebbling the HPV block computation

Every interval reads its predecessor's control record, a concrete schedule has a window edge
besides the control edges, every vertex has in-degree at most `3 * k + 1`, and a black pebbling
of the root is an evaluation that validates the guessed schedule whenever its root register holds
a view. With one pebble per vertex the root can always be
evaluated.
-/

public section

namespace CslibFrontierTests.BlockComputationProgram

open Turing MultiTapePTM.BlockComputation Cslib.Circuits Cslib.Pebbling

-- The mandatory control edge from each interval to the next.
example {k q : ℕ} (σ : MultiTapePTM.Schedule k q) {n : ℕ} (hn : n < q) :
    (program σ).dag.Adj (Descending.node q n) (Descending.node q (n + 1)) :=
  (Descending.dag_adj_node (child σ) (child_lt σ) hn).2 ⟨0, by simp [child, hn]⟩

/- A window edge. Under the one-tape schedule `380` with three intervals (rows `(2,0)`, `(0,2)`,
`(1,1)`), the third window entry of interval `3` was last provided by interval `1`, so the DAG has
the edge `1 → 3` besides the control edge `2 → 3`. -/
example :
    (program (MultiTapePTM.scheduleOfNat 1 3 380)).dag.Adj (Descending.node 3 1)
      (Descending.node 3 3) :=
  (Descending.dag_adj_node _ (child_lt _) (by decide)).2
    ⟨3, congrArg (Descending.node 3) (by rw [← ImplicitPath.child_eq]; decide)⟩

-- On one work tape, every vertex reads at most four earlier vertices.
example (σ : MultiTapePTM.Schedule 1 2) (v : Wire 1 2) :
    {u | (program σ).dag.Adj u v}.ncard ≤ 4 :=
  ncard_dag_adj_program_le σ v

/-- A pebbling evaluation whose root register holds a view validates the guessed schedule, and the
view is the true final view. -/
example {k q b s : ℕ} {State : Type} [NeZero b] (machine : MultiTapePTM k Bool State)
    (input : List Bool) (σ : MultiTapePTM.Schedule k q)
    (h : BlackPebblable (program σ).dag s (Descending.node q q))
    (r₀ : Wire 1 q → Option (View k State b)) :
    ∃ ms c, ((program σ).registerLTS (interpretation machine input b σ)
        (fun _ => some (initialView machine b)) s).MTr (∅, r₀) ms c ∧
      Descending.node q q ∈ c.1 ∧ ∀ v, c.2 (Descending.node q q) = some v →
        actualSchedule machine input b (q := q) = σ ∧ v = trueView machine input b σ q := by
  obtain ⟨ms, c, hc, hmem, hval⟩ := exists_registerLTS_value machine input b σ le_rfl h r₀
  exact ⟨ms, c, hc, hmem, fun v hv =>
    (value_final_eq_some_iff machine input b σ v).1 (hval ▸ hv)⟩

-- One pebble per vertex always suffices.
example {k q : ℕ} (σ : MultiTapePTM.Schedule k q) :
    BlackPebblable (program σ).dag (1 + q) (Descending.node q q) := by
  simpa using blackPebblable_fintypeCard (program σ).wellFounded_dag (Descending.node q q)

end CslibFrontierTests.BlockComputationProgram
