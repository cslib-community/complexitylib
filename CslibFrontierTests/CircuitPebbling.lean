/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Pebbling
import CslibFrontier.Computability.Pebbling.Map
import CslibFrontier.Computability.Pebbling.Pyramid
import Cslib.Computability.Circuit.Boolean.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.IntervalCases

/-!
# Register evaluation of a pyramid-shaped program

The De Morgan program `pyr` computes `(x₀ ∧ x₁) ∧ (x₁ ∧ x₂)` with three inputs and three gates.
Its computation DAG is the pyramid `Π_2`, so by Cook's theorem it needs exactly four registers
when every gate value goes into a fresh register (three under Savage's sliding rule).
An explicit four-register evaluation computes the right value, and three registers do not
suffice for any interpretation.
-/

namespace ComplexityTests.CircuitPebbling

open Cslib Cslib.Circuits Cslib.Pebbling

/-- A conjunction gate reading two wires. -/
def andLine {g : ℕ} (a b : Wire 3 g) : Line Boolean.signature 3 g :=
  ⟨.and, ![a, b]⟩

/-- `(x₀ ∧ x₁) ∧ (x₁ ∧ x₂)` as a three-gate straight-line program. -/
def pyr : Program Boolean.signature 3 3 :=
  ((Program.empty.gate (andLine (.input 0) (.input 1))).gate
    (andLine (.input 1) (.input 2))).gate (andLine (.gate 0) (.gate 1))

end ComplexityTests.CircuitPebbling

namespace ComplexityTests.CircuitPebbling

open Cslib Cslib.Circuits Cslib.Pebbling

/-- The adjacency of the computation DAG of `pyr`, decided by evaluation. -/
example : pyr.dag.Adj (.gate 0) (.gate 2) ∧ pyr.dag.Adj (.input 1) (.gate 0) ∧
    ¬ pyr.dag.Adj (.input 0) (.gate 1) := by
  simp only [Program.dag_adj_gate]
  decide

/-- The wires of `pyr` as vertices of `Π_2`. -/
def toPyramid : Wire 3 3 → PyramidVertex 2
  | .input i => ⟨0, i.val, by have := i.isLt; omega⟩
  | .gate j => if h : j.val < 2 then ⟨1, j.val, by omega⟩ else ⟨2, 0, by omega⟩

/-- The vertices of `Π_2` as wires of `pyr`. -/
def ofPyramid (v : PyramidVertex 2) : Wire 3 3 :=
  if v.level = 0 then .input ⟨v.pos, by have := v.le; omega⟩
  else if v.level = 1 then .gate ⟨v.pos, by have := v.le; omega⟩
  else .gate 2

/-- The wires of `pyr` are the vertices of `Π_2`. -/
def wireEquiv : Wire 3 3 ≃ PyramidVertex 2 where
  toFun := toPyramid
  invFun := ofPyramid
  left_inv := by decide
  right_inv := by
    rintro ⟨l, q, h⟩
    have hl : l ≤ 2 := by omega
    have hq : q ≤ 2 := by omega
    interval_cases l <;> interval_cases q <;> first | rfl | omega

/-- `wireEquiv` is an isomorphism from the computation DAG of `pyr` onto `Π_2`. -/
theorem wireEquiv_adj (u v : Wire 3 3) :
    (pyramid 2).Adj (wireEquiv u) (wireEquiv v) ↔ pyr.dag.Adj u v := by
  revert u v
  simp only [pyramid_adj, Program.dag_adj]
  decide

/-- `wireEquiv` as a relation isomorphism between the computation DAG of `pyr` and `Π_2`. -/
def wireIso : pyr.dag.Adj ≃r (pyramid 2).Adj := ⟨wireEquiv, wireEquiv_adj _ _⟩

/-- Three registers do not suffice to evaluate the output of `pyr`, for any interpretation,
input and initial register contents. -/
example {U : Type} (I : Interpretation Boolean.signature U) (x : Fin 3 → U)
    (r₀ : Wire 3 3 → U) : ¬ pyr.EvaluatesInRegisters I x r₀ 3 (.gate 2) := by
  rw [Program.evaluatesInRegisters_iff_blackPebblable,
    ← blackPebblable_relIso_iff wireIso]
  intro h
  exact absurd (PyramidVertex.le_of_blackPebblable (by decide) h) (by decide)

/-- The least number of registers evaluating the output of `pyr` is four. -/
example {U : Type} (I : Interpretation Boolean.signature U) (x : Fin 3 → U)
    (r₀ : Wire 3 3 → U) : sInf {s | pyr.EvaluatesInRegisters I x r₀ s (.gate 2)} = 4 := by
  rw [Program.sInf_evaluatesInRegisters, ← blackPebblingPrice_relIso wireIso]
  exact blackPebblingPrice_pyramid_top (by decide)

/-- A four-register evaluation over the Booleans holds the true output value. -/
example : ∃ ms d, (pyr.registerLTS Boolean.interpretation ![true, false, true] 4).MTr
    (∅, fun _ => false) ms d ∧ .gate 2 ∈ d.1 ∧ d.2 (.gate 2) = false := by
  have h : pyr.EvaluatesInRegisters Boolean.interpretation ![true, false, true] (fun _ => false) 4
      (.gate 2) := by
    rw [Program.evaluatesInRegisters_iff_blackPebblable,
      ← blackPebblable_relIso_iff wireIso]
    exact blackPebblable_pyramid (PyramidVertex.top 2)
  obtain ⟨ms, d, hd, hw, hv⟩ := h.exists_eq_trace
  exact ⟨ms, d, hd, hw, hv.trans (by decide)⟩

end ComplexityTests.CircuitPebbling
