/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: local-only (tests of descending straight-line programs)

public import CslibFrontier.Computability.Circuit.Descending
public import Mathlib.Data.Nat.Fib.Basic

/-!
# The Fibonacci recurrence as a descending program

Index `i + 2` reads indices `i + 1` and `i`, and index `1` is the constant `1`. The program on
indices `0, …, g` shares every intermediate value, so it has `g` gates of fan-in two, and its
trace is `Nat.fib`. A register evaluation of the program computes `Nat.fib 5`.
-/

@[expose] public section

namespace CslibFrontierTests.CircuitDescending

open Cslib.Circuits

/-- Index `i` reads indices `i - 1` and `i - 2`. -/
def fibChild (i : ℕ) (a : Fin 2) : ℕ := if a = 0 then i - 1 else i - 2

/-- Index `1` is the constant `1`; every later index adds its two children. -/
def fibGate (i : ℕ) (x : Fin 2 → ℕ) : ℕ := if i = 1 then 1 else x 0 + x 1

theorem fibChild_lt : ∀ i, 0 < i → ∀ a, fibChild i a < i := by
  intro i hi a
  unfold fibChild
  split <;> omega

theorem trace_fib {g i : ℕ} (hi : i ≤ g) :
    (Descending.program fibChild g).trace (Descending.interpretation fibGate) (fun _ => 0)
      (Descending.node g i) = Nat.fib i :=
  Descending.trace_node_eq fibChild fibGate 0 fibChild_lt Nat.fib_zero (fun i _ => by
    cases i with
    | zero => simp [fibGate]
    | succ i =>
      rw [Nat.fib_add_two, Nat.add_comm]
      simp [fibGate, fibChild]) hi

-- Index `3` reads indices `2` and `1`.
example : (Descending.program fibChild 3).dag.Adj (Descending.node 3 2) (Descending.node 3 3) ∧
    (Descending.program fibChild 3).dag.Adj (Descending.node 3 1) (Descending.node 3 3) :=
  ⟨(Descending.dag_adj_node fibChild fibChild_lt (by decide)).2 ⟨0, rfl⟩,
    (Descending.dag_adj_node fibChild fibChild_lt (by decide)).2 ⟨1, rfl⟩⟩

-- Every vertex has in-degree at most two.
example (g : ℕ) (v : Wire 1 g) : {u | (Descending.program fibChild g).dag.Adj u v}.ncard ≤ 2 :=
  Program.ncard_dag_adj_le (Descending.fanInAtMost_program fibChild g) v

-- A register evaluation with one register per index ends holding `fib 5 = 5`.
example (r₀ : Wire 1 5 → ℕ) :
    ∃ ms c, ((Descending.program fibChild 5).registerLTS (Descending.interpretation fibGate)
        (fun _ => 0) 6).MTr (∅, r₀) ms c ∧
      Descending.node 5 5 ∈ c.1 ∧ c.2 (Descending.node 5 5) = 5 := by
  obtain ⟨ms, c, hc, hmem, hval⟩ :=
    (Program.evaluatesInRegisters_card (p := Descending.program fibChild 5)
      (I := Descending.interpretation fibGate) (x := fun _ => 0) r₀
      (Descending.node 5 5)).exists_eq_trace
  refine ⟨ms, c, hc, hmem, ?_⟩
  rw [hval, trace_fib le_rfl]
  decide

end CslibFrontierTests.CircuitDescending
