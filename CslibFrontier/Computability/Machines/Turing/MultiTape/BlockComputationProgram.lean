/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Descending
public import CslibFrontier.Computability.Machines.Turing.MultiTape.BlockComputationTree

/-!
# HPV block computation as a straight-line program

For a guessed movement schedule `σ` with `q` intervals, the block computation of
`Turing.MultiTapePTM.BlockComputation` is a descending computation: interval `n + 1` reads the
control record of interval `n` and the last providers of its `3 * k` window blocks
(`Turing.MultiTapePTM.BlockComputation.child`). Keeping the shared dependencies, rather than
unfolding them into a tree as `BlockComputationTree` does, gives a straight-line program with one
input (the initial view) and `q` gates of fan-in `3 * k + 1`. Its computation DAG has `q + 1`
vertices and depends only on `σ`.

This is the graph of the Hopcroft–Paul–Valiant simulation, with the aligned three-block windows of
the library in place of a block-respecting normal form: a black pebbling of the DAG with `s`
pebbles is an evaluation of the block computation holding at most `s` interval views at a time
(`Turing.MultiTapePTM.BlockComputation.exists_registerLTS_value`). The pebbling bound, the
native search over schedules and the space accounting are separate obligations.

## Main definitions

* `Turing.MultiTapePTM.BlockComputation.program`: the block computation of `σ`.
* `Turing.MultiTapePTM.BlockComputation.interpretation`: its interval gates.

## Main results

* `Turing.MultiTapePTM.BlockComputation.trace_program`: the trace at interval `n` is
  `Turing.MultiTapePTM.BlockComputation.value`.
* `Turing.MultiTapePTM.BlockComputation.ncard_dag_adj_program_le`: every vertex has in-degree at
  most `3 * k + 1`.
* `Turing.MultiTapePTM.BlockComputation.exists_registerLTS_value`: a black pebbling of interval
  `n` is a register evaluation whose register for `n` holds its value.

## References

* [J. Hopcroft, W. Paul, L. Valiant, *On time versus space*][HopcroftPaulValiant1977]: the
  computation graph of a block-respecting machine and its pebbling (journal text not inspected).
* [R. Williams, *Simulating Time With Square-Root Space*][Williams2025], arXiv v1, §3.3: the
  computation graph of the block computation, and its pebbling following Hopcroft, Paul and
  Valiant.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation

open Cslib Cslib.Circuits Cslib.Pebbling

variable {k q b : ℕ} {State : Type}

/-- The block computation of the schedule `σ` as a straight-line program: the input is the initial
view, and gate `n` computes interval `n + 1` from its `3 * k + 1` dependencies. -/
@[expose] def program (σ : Schedule k q) : Program (Descending.signature (k * 3 + 1)) 1 q :=
  Descending.program (child σ) q

variable (machine : MultiTapePTM k Bool State) (input : List Bool) (b : ℕ) (σ : Schedule k q)

/-- The interval gates of the block computation, with failure. -/
@[expose] noncomputable def interpretation :
    Interpretation (Descending.signature (k * 3 + 1)) (Option (View k State b)) :=
  Descending.interpretation (intervalGate machine input b σ)

/-- The trace of the program at interval `n` is the functional block value. -/
theorem trace_program {n : ℕ} (hn : n ≤ q) :
    (program σ).trace (interpretation machine input b σ) (fun _ => some (initialView machine b))
      (Descending.node q n) = value machine input b σ n := by
  refine Descending.trace_node_eq (child σ) (intervalGate machine input b σ) _ (child_lt σ)
    (by rw [value]) (fun i => ?_) hn
  by_cases hi : i < q
  · exact (intervalGate_value machine input b σ hi).symm
  · rw [value, dite_eq_right hi, intervalGate, dite_eq_right hi]

/-- Every vertex of the computation DAG reads at most `3 * k + 1` earlier vertices. -/
theorem ncard_dag_adj_program_le (v : Wire 1 q) :
    {u | (program σ).dag.Adj u v}.ncard ≤ k * 3 + 1 :=
  Program.ncard_dag_adj_le (Descending.fanInAtMost_program _ _) v

/-- **Pebbles are interval views.** A black pebbling of interval `n` with `s` pebbles is an
evaluation of the block computation holding at most `s` interval views at once, from any initial
register contents; at its end, the register of interval `n` holds the value of `n`. -/
theorem exists_registerLTS_value {s n : ℕ} (hn : n ≤ q)
    (h : BlackPebblable (program σ).dag s (Descending.node q n))
    (r₀ : Wire 1 q → Option (View k State b)) :
    ∃ ms c, ((program σ).registerLTS (interpretation machine input b σ)
        (fun _ => some (initialView machine b)) s).MTr (∅, r₀) ms c ∧
      Descending.node q n ∈ c.1 ∧ c.2 (Descending.node q n) = value machine input b σ n := by
  obtain ⟨ms, c, hc, hmem, hval⟩ :=
    ((Program.evaluatesInRegisters_iff_blackPebblable (r₀ := r₀)).2 h).exists_eq_trace
  exact ⟨ms, c, hc, hmem, hval.trans (trace_program machine input b σ hn)⟩

end Turing.MultiTapePTM.BlockComputation
