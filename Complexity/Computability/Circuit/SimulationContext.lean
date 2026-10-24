/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.MapLines
public import Complexity.Computability.Circuit.Simulation
import Cslib.Foundations.Data.Fin.Tuple

/-!
# Circuit simulation with shared context

An operation gadget can read a shared block of ambient inputs as well as its ordinary
arguments. This permits a nullary dictionary term to depend on ambient variables, as in
Waring decompositions. All gadgets read the same input block; no context gates are added.

Compilation first adds context arguments to each line, then uses `Program.simulate` through
`Circuit.simulate`. Thus the existing wire-renaming and gate-replacement machinery handles
sharing and output wiring. Costs count every gadget gate, including gates unused by outputs.

## Main definitions

* `Cslib.Circuits.Signature.withContext`: prepend ambient inputs to every operation's arguments.
* `Cslib.Circuits.Line.withContext`, `Cslib.Circuits.Circuit.withContext`: pass the same ambient
  inputs to a gate line or to every gate in a circuit.
* `Cslib.Circuits.Circuit.simulateWithContext`: replace each operation by a contextual gadget.

## Main results

* `Cslib.Circuits.Circuit.eval_simulateWithContext`: exact semantics for every output.
* `Cslib.Circuits.Circuit.cost_program_simulateWithContext`: exact arbitrary weighted cost.

## References

* Ported from Translation/Contextual.lean in [S. Schlesinger, *Algebraic circuit
  formalizations in Complexitylib*][Schlesinger2026Algebraic], using native circuit simulation.
-/

@[expose] public section

namespace Cslib.Circuits

universe v w u

variable {σ : Signature.{v}} {τ : Signature.{w}} {U : Type u} {n m g : ℕ}

/-- Add a `q`-input context before each operation's ordinary arguments. -/
abbrev Signature.withContext (σ : Signature.{v}) (q : ℕ) : Signature.{v} where
  Op := σ.Op
  Arity op := q + σ.Arity op

/-- Prepend references to the ambient input block to a line's arguments. -/
def Line.withContext (q : ℕ) (line : Line σ (q + n) g) :
    Line (σ.withContext q) (q + n) g :=
  ⟨line.op, Fin.append (Wire.input ∘ Fin.castAdd n) line.wires⟩

/-- Every gate receives the shared context, followed by its original arguments. -/
def Circuit.withContext (c : Circuit σ n m) (q : ℕ) : Circuit (σ.withContext q) (q + n) m :=
  (c.comp (wiring σ (Fin.natAdd q))).mapLines (Line.withContext q)

/-- Adding context does not add gates or change their costs. -/
private theorem Circuit.cost_program_withContext (c : Circuit σ n m) (q : ℕ) (cost : σ.Op → ℕ) :
    (c.withContext q).program.cost cost = c.program.cost cost := by
  change ((c.comp (wiring σ (Fin.natAdd q))).program.mapLines
    (Line.withContext q)).cost cost = _
  rw [Program.cost_mapLines (f := Line.withContext q) (cost := cost) (fun _ => rfl),
    cost_program_comp, cost_program_wiring, Nat.zero_add]

/-- Adding context keeps the number of gates. -/
@[simp] theorem Circuit.size_withContext (c : Circuit σ n m) (q : ℕ) :
    (c.withContext q).size = c.size := by
  simp [withContext]

/-- Evaluating a context-bearing circuit fixes the same context in every operation. -/
theorem Circuit.eval_withContext (c : Circuit σ n m) (q : ℕ)
    (J : Interpretation (σ.withContext q) U) (context : Fin q → U) (x : Fin n → U) :
    (c.withContext q).eval J (Fin.append context x) =
      c.eval (fun op args => J op (Fin.append context args)) x := by
  unfold withContext
  rw [Circuit.eval_mapLines_at (σ := σ) (τ := σ.withContext q)
    (f := Line.withContext q) (I := fun op args => J op (Fin.append context args))
    (hf := ?_), eval_comp, eval_wiring, Fin.append_comp_natAdd]
  intro g line gates
  change J line.op (Wire.elim (Fin.append context x) gates ∘
    Fin.append (Wire.input ∘ Fin.castAdd n) line.wires) =
      J line.op (Fin.append context (Wire.elim (Fin.append context x) gates ∘ line.wires))
  rw [Fin.comp_append]
  simp [Function.comp_def]

/-- Replace every gate by a gadget receiving shared ambient inputs and its local arguments. -/
def Circuit.simulateWithContext (c : Circuit σ n m) (q : ℕ)
    (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1) : Circuit τ (q + n) m :=
  (c.withContext q).simulate impl

/-- Contextual simulation computes every output with the supplied gadget semantics. -/
theorem Circuit.eval_simulateWithContext (c : Circuit σ n m) (q : ℕ)
    (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1)
    (J : Interpretation τ U) (context : Fin q → U) (x : Fin n → U) :
    (c.simulateWithContext q impl).eval J (Fin.append context x) =
      c.eval (fun op args => (impl op).eval J (Fin.append context args) 0) x := by
  let I : Interpretation (σ.withContext q) U := fun op args => (impl op).eval J args 0
  have h : ∀ op, (impl op).Computes J (single (I op)) :=
    fun _ _ => funext fun j => congrArg _ (Subsingleton.elim j 0)
  rw [simulateWithContext, eval_simulate _ _ h, eval_withContext]

/-- Contextual simulation charges exactly the weighted cost of each operation gadget. -/
theorem Circuit.cost_program_simulateWithContext (c : Circuit σ n m) (q : ℕ)
    (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1) (cost : τ.Op → ℕ) :
    (c.simulateWithContext q impl).program.cost cost =
      c.program.cost fun op => (impl op).program.cost cost := by
  rw [simulateWithContext, cost_program_simulate, cost_program_withContext]

/-- The compiled gate count is exactly the sum of the gadget sizes. -/
@[simp] theorem Circuit.size_simulateWithContext (c : Circuit σ n m) (q : ℕ)
    (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1) :
    (c.simulateWithContext q impl).size = c.program.cost fun op => (impl op).size := by
  rw [simulateWithContext, size_simulate, cost_program_withContext]

/-- A uniform gadget-size bound gives a uniform factor on circuit size. -/
theorem Circuit.size_simulateWithContext_le (c : Circuit σ n m) (q : ℕ)
    (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1) {b : ℕ}
    (h : ∀ op, (impl op).size ≤ b) : (c.simulateWithContext q impl).size ≤ b * c.size := by
  rw [size_simulateWithContext]
  exact c.program.cost_le_mul h

end Cslib.Circuits
