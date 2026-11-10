/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Pebbling
import CslibFrontier.Computability.Circuit.Program

/-!
# Computations with decreasing indices as straight-line programs

A descending computation has a source at index `0` and, at each positive index `i`, a gate
`gates i` reading the values at the `d` strictly smaller indices `child i 0, …, child i (d - 1)`.
`Cslib.TreeEval.Ary.Descending` unfolds such a computation into a tree. This file keeps the
sharing instead: indices `0, …, g` become the single input and the `g` gates of a straight-line
program, so the computation DAG of the program is the dependency graph of the computation. The
register and pebbling results for straight-line programs (`Cslib.Circuits.Program.dag`,
`Cslib.Circuits.Program.EvaluatesInRegisters`) then apply to the computation directly.

## Main definitions

* `Cslib.Circuits.Descending.signature`: one operation per positive index, each of arity `d`.
* `Cslib.Circuits.Descending.node`: the wire of an index; index `0` is the input.
* `Cslib.Circuits.Descending.program`: the computation on indices `0, …, g`.

## Main results

* `Cslib.Circuits.Descending.trace_node_zero`, `Cslib.Circuits.Descending.trace_node_succ`: the
  trace satisfies the source and gate equations of the computation.
* `Cslib.Circuits.Descending.trace_node_eq`: every solution of those equations is the trace.
* `Cslib.Circuits.Descending.dag_adj_node`: the computation DAG has the dependency edges.
* `Cslib.Circuits.Descending.fanInAtMost_program`: every gate reads `d` wires.
-/

public section

namespace Cslib.Circuits.Descending

variable {d : ℕ}

/-- One operation for each positive index `i + 1`, named by `i`; each reads `d` arguments. -/
@[expose] def signature (d : ℕ) : Signature where
  Op := ℕ
  Arity _ := d

/-- The wire carrying index `i` among indices `0, …, g`: index `0` is the input, index `i + 1`
the gate `i`. Indices beyond `g` are sent to the input; `program` only uses indices `≤ g`. -/
@[expose] def node (g i : ℕ) : Wire 1 g :=
  match i with
  | 0 => .input 0
  | i + 1 => if h : i < g then .gate ⟨i, h⟩ else .input 0

/-- The gate at index `j + 1`, reading the wires of its children. -/
@[expose] def line (child : ℕ → Fin d → ℕ) (g j : ℕ) : Line (signature d) 1 g :=
  ⟨j, fun a => node g (child (j + 1) a)⟩

/-- The descending computation on indices `0, …, g` as a straight-line program with one input
and `g` gates. Gate `j` computes index `j + 1`. -/
@[expose] def program (child : ℕ → Fin d → ℕ) : (g : ℕ) → Program (signature d) 1 g
  | 0 => .empty
  | g + 1 => (program child g).gate (line child g g)

@[simp] theorem node_zero (g : ℕ) : node g 0 = .input 0 := rfl

theorem node_succ {g i : ℕ} (h : i < g) : node g (i + 1) = .gate ⟨i, h⟩ := by
  simp [node, h]

/-- Widening the wire of an index `≤ g` to `g + 1` gates gives the wire of the same index. -/
theorem node_castSucc {g i : ℕ} (h : i ≤ g) : (node g i).castSucc = node (g + 1) i := by
  cases i with
  | zero => rfl
  | succ i => rw [node_succ (by omega), node_succ (by omega)]; rfl

variable (child : ℕ → Fin d → ℕ)

/-- The widened lines of `program` are its gates. -/
theorem lines_program (hchild : ∀ i, 0 < i → ∀ a, child i a < i) {g : ℕ} (j : Fin g) :
    (program child g).lines j = line child g j := by
  induction g with
  | zero => exact j.elim0
  | succ g ih =>
    have hwiden (j : ℕ) (hj : j < g + 1) :
        (line child g j).mapWires Wire.Renaming.castSucc = line child (g + 1) j := by
      simp only [line, Line.mapWires, Function.comp_def, Wire.Renaming.castSucc_apply]
      congr 1
      funext a
      exact node_castSucc (by have := hchild (j + 1) (by omega) a; omega)
    refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [program, Program.lines_gate_last]
      exact hwiden g (by omega)
    · rw [program, Program.lines_gate_castSucc, ih]
      exact hwiden j (by omega)

variable {U : Type*} (gates : ℕ → (Fin d → U) → U) (source : U)

/-- The interpretation of `signature d` running gate `gates (i + 1)` at operation `i`. -/
@[expose] def interpretation : Interpretation (signature d) U := fun (i : ℕ) => gates (i + 1)

/-- The trace at index `0` is the source. -/
theorem trace_node_zero (g : ℕ) :
    (program child g).trace (interpretation gates) (fun _ => source) (node g 0) = source := rfl

/-- The trace at a positive index applies its gate to the trace at its children. -/
theorem trace_node_succ (hchild : ∀ i, 0 < i → ∀ a, child i a < i) {g i : ℕ} (hi : i < g) :
    (program child g).trace (interpretation gates) (fun _ => source) (node g (i + 1)) =
      gates (i + 1) fun a =>
        (program child g).trace (interpretation gates) (fun _ => source)
          (node g (child (i + 1) a)) := by
  rw [node_succ hi, Program.trace_gate, lines_program child hchild]
  rfl

/-- **Uniqueness.** A function on indices that takes the source at `0` and satisfies every gate
equation agrees with the trace on indices `0, …, g`. -/
theorem trace_node_eq (hchild : ∀ i, 0 < i → ∀ a, child i a < i) {v : ℕ → U}
    (hzero : v 0 = source) (hsucc : ∀ i, v (i + 1) = gates (i + 1) fun a => v (child (i + 1) a))
    {g i : ℕ} (hi : i ≤ g) :
    (program child g).trace (interpretation gates) (fun _ => source) (node g i) = v i := by
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    cases i with
    | zero => exact hzero.symm
    | succ i =>
      rw [trace_node_succ child gates source hchild (by omega), hsucc]
      congr 1
      funext a
      have ha := hchild (i + 1) (by omega) a
      exact ih _ ha (by omega)

/-- In the computation DAG, the predecessors of a positive index are its children. -/
theorem dag_adj_node (hchild : ∀ i, 0 < i → ∀ a, child i a < i) {g i : ℕ} (hi : i < g)
    {u : Wire 1 g} : (program child g).dag.Adj u (node g (i + 1)) ↔
      ∃ a, node g (child (i + 1) a) = u := by
  rw [node_succ hi, Program.dag_adj_gate, lines_program child hchild]
  rfl

/-- Every gate of a descending computation reads `d` wires. -/
theorem fanInAtMost_program (g : ℕ) : (program child g).FanInAtMost d :=
  (Program.fanInAtMost_iff).2 fun _ => le_rfl

end Cslib.Circuits.Descending
