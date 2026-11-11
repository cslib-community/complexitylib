/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Parameterized.WHierarchy.IndependentSet

/-!
# Tests: the W-hierarchy, and Independent Set and Clique in `W[1]`

Weft and depth of small circuits, evaluated by `decide`: a conjunction of three inputs is a large
gate and has weft `1`, a disjunction of two has weft `0`; two such conjunctions have weft `1` in
parallel and `2` in series. Weighted satisfiability of the
conjunction of three inputs holds for weight `3` and fails for weight `2`. The circuit of the
triangle has a satisfying input of weight `1` and none of weight `2`, so the triangle has no
independent set of two vertices; edges with an undeclared end and self-loops are ignored by the
circuit. Finally the class-level consequences: `Clique` is in `W[2]`, and a `W[1]`-hard problem in
`FPT` would put `Clique` in `FPT`.
-/

namespace ComplexityTests.WHierarchy

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Turing.MultiTapeTM

/-! ### Weft and depth -/

/-- The conjunction of three inputs. -/
def and3 : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨3, ⟨Program.empty.gate ⟨.and 3, fun i => .input i⟩, fun _ => .gate 0⟩⟩

/-- The disjunction of two inputs. -/
def or2 : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨2, ⟨Program.empty.gate ⟨.or 2, fun i => .input i⟩, fun _ => .gate 0⟩⟩

-- A gate of three arguments is large; one of two is not.
example : and3.2.weft = 1 ∧ and3.2.depth = 1 := by decide

example : or2.2.weft = 0 ∧ or2.2.depth = 1 := by decide

example : WCS.trueCircuit.2.weft = 0 ∧ WCS.trueCircuit.2.depth = 1 := by decide

/-- Two conjunctions of three inputs in parallel, under a disjunction of two. -/
def parallelAnd3 : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨3, ⟨(((Program.empty : Program Unbounded.signature 3 0).gate
    ⟨.and 3, fun i => .input i⟩).gate ⟨.and 3, fun i => .input i⟩).gate
    ⟨.or 2, ![.gate 0, .gate 1]⟩, fun _ => .gate 2⟩⟩

/-- Two conjunctions of three arguments in series: the second reads the first. -/
def seriesAnd3 : Σ n, Circuit Unbounded.signature n 1 :=
  ⟨3, ⟨((Program.empty : Program Unbounded.signature 3 0).gate
    ⟨.and 3, fun i => .input i⟩).gate ⟨.and 3, ![.gate 0, .input 1, .input 2]⟩, fun _ => .gate 1⟩⟩

-- The weft is the largest number of large gates on a path, not their number: two large gates in
-- parallel give weft `1`, in series weft `2`.
example : parallelAnd3.2.weft = 1 ∧ parallelAnd3.2.depth = 2 := by decide

example : seriesAnd3.2.weft = 2 ∧ seriesAnd3.2.depth = 2 := by decide

/-! ### Weighted circuit satisfiability -/

-- The conjunction of three inputs is satisfied only by the input with three ones.
example : (and3, 3) ∈ WeightedCircuitSAT := ⟨fun _ => true, by decide, by decide⟩

example : (and3, 2) ∉ WeightedCircuitSAT := by
  rintro ⟨x, hk, hx⟩
  revert hk hx
  revert x
  unfold BitString.weight
  decide

example : WCS.yesInstance 1 ∈ WCS 1 1 ∧ WCS.noInstance 1 ∉ WCS 1 1 :=
  ⟨WCS.yesInstance_mem 1, WCS.noInstance_not_mem 1⟩

/-! ### The circuit of a graph -/

/-- The triangle on `0, 1, 2`. -/
def K3 : Graph := ([0, 1, 2], [(0, 1), (1, 2), (0, 2)])

example : IndependentSet.edgeIndices K3 = [(0, 1), (1, 2), (0, 2)] := by decide

-- One vertex of the triangle is a satisfying input of weight `1`.
example : IndependentSet.toWCS (K3, 1) ∈ WCS 1 3 :=
  ⟨fun i => decide (i.val = 0), by decide, by rw [IndependentSet.eval_toCircuit]; decide⟩

-- No input of weight `2` satisfies the circuit of the triangle, so the triangle has no
-- independent set of two vertices.
example : (K3, 2) ∉ IndependentSet := by
  rw [← IndependentSet.toWCS_mem_WCS_iff]
  rintro ⟨x, hk, hx⟩
  rw [IndependentSet.eval_toCircuit] at hx
  revert x
  decide

-- An edge with an undeclared end is not an edge of the circuit.
example : IndependentSet.edgeIndices ([0, 1], [(0, 5)]) = [] := by decide

example : ((([0, 1], [(0, 5)]), 2) : Graph × ℕ) ∈ IndependentSet := by
  rw [← IndependentSet.toWCS_mem_WCS_iff]
  exact ⟨fun _ => true, by decide, by rw [IndependentSet.eval_toCircuit]; decide⟩

-- A self-loop is not an edge of the circuit.
example : ((([0], [(0, 0)]), 1) : Graph × ℕ) ∈ IndependentSet := by
  rw [← IndependentSet.toWCS_mem_WCS_iff]
  exact ⟨fun _ => true, by decide, by rw [IndependentSet.eval_toCircuit]; decide⟩

/-! ### Classes -/

example : Clique ∈ W 2 (encPair encGraph encNat) Prod.snd :=
  W_mono (by norm_num) Clique_mem_W

-- A `W[1]`-hard problem in `FPT` would put `Clique` in `FPT`.
example {β : Type} {enc : β ↪ List Bool} {κ : β → ℕ} {B : Set β} (hB : WHard 1 enc κ B)
    (hFPT : B ∈ FPT enc κ) : Clique ∈ FPT (encPair encGraph encNat) Prod.snd :=
  hB.subset_FPT hFPT Clique_mem_W

end ComplexityTests.WHierarchy
