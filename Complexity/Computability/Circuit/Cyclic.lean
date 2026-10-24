/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.SourceComplexity
public import Mathlib.Order.FixedPoints
import Complexity.Computability.Circuit.Simulation

/-!
# Cyclic circuits and least-fixed-point semantics

A cyclic circuit reuses native `Line` and `Wire`, allowing each equation to refer to any gate.
Unlike a topologically ordered `Program`, the equations may contain feedback. Designated outputs
can read inputs or gates; zero gates, zero outputs, sharing and unused components are allowed.
Every equation is charged once by its operation weight.

For a monotone interpretation on a complete lattice, Mathlib's `OrderHom.lfp` gives a canonical
least solution, without a separate construction certificate. This is mathematical semantics,
not an execution algorithm or a finite-iteration bound. In particular, monotonicity alone does
not imply that iteration through the natural numbers reaches or approaches the least solution.
Native acyclic circuits embed with exactly the same gate values, outputs and weighted costs.

## Main definitions

* `Cslib.Circuits.CyclicCircuit`, `Cslib.Circuits.CyclicCircuit.cost`: finite equations with
  designated output wires and weighted gate cost.
* `Cslib.Circuits.Circuit.toCyclic`: embed an acyclic circuit into a cyclic circuit.
* `Cslib.Circuits.CyclicCircuit.step`, `Cslib.Circuits.CyclicCircuit.evalGates`,
  `Cslib.Circuits.CyclicCircuit.eval`: monotone step operator and least-solution gate values
  and outputs.
* `Cslib.Circuits.CyclicCircuit.ComputesFrom`,
  `Cslib.Circuits.CyclicCircuit.ecomplexityFrom`: computation and minimum cost from supplied
  source functions.

## Main results

* `Cslib.Circuits.Circuit.eval_toCyclic`, `Cslib.Circuits.Circuit.cost_toCyclic`: the native
  acyclic embedding preserves semantics and costs.
* `Cslib.Circuits.CyclicCircuit.evalGates_le`: leastness among pre-fixed states.
* `Cslib.Circuits.CyclicCircuit.ecomplexityFrom_le_acyclic`: allowing feedback cannot increase
  source complexity.

## References

* Adapted from LowerBound/Fusion/Cyclic.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
  The least-solution semantics uses Mathlib's Knaster–Tarski fixed-point API.
-/

@[expose] public section

namespace Cslib.Circuits

universe u v

/-- A finite system of gate equations with designated input or gate outputs. -/
structure CyclicCircuit (σ : Signature.{u}) (inputCount outputCount : ℕ) where
  /-- Number of equations; inputs and designated outputs cost nothing. -/
  {size : ℕ}
  /-- Every gate may read any input or gate, including itself. -/
  lines : Fin size → Line σ inputCount size
  /-- Each output reads an input or a solved gate. Sharing is allowed. -/
  outputs : Fin outputCount → Wire inputCount size

variable {σ : Signature.{u}} {U : Type v} {n m : ℕ}

/-- Sum all operation weights, including unused and repeated equations. -/
def CyclicCircuit.cost (c : CyclicCircuit σ n m) (weight : σ.Op → ℕ) : ℕ :=
  ∑ i, weight (c.lines i).op

/-- Regard the native acyclic program as a system of simultaneous equations. -/
def Circuit.toCyclic (c : Circuit σ n m) : CyclicCircuit σ n m :=
  ⟨c.program.lines, c.outputs⟩

/-- The embedding retains exactly the weighted cost of every gate. -/
@[simp] theorem Circuit.cost_toCyclic (c : Circuit σ n m) (weight : σ.Op → ℕ) :
    c.toCyclic.cost weight = c.program.cost weight := (c.program.cost_eq_sum weight).symm

/-- Update every gate simultaneously using the supplied input and proposed gate values. -/
def CyclicCircuit.step [Preorder U] (c : CyclicCircuit σ n m)
    (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U) :
    (Fin c.size → U) →o (Fin c.size → U) where
  toFun state i := (c.lines i).eval I input state
  monotone' lower upper h i := hI _ fun a => by
    change Wire.elim input lower ((c.lines i).wires a) ≤
      Wire.elim input upper ((c.lines i).wires a)
    cases (c.lines i).wires a with
    | input j => exact (le_rfl : input j ≤ input j)
    | gate j => exact h j

/-- The least solution of the gate equations in a complete lattice. -/
def CyclicCircuit.evalGates [CompleteLattice U] (c : CyclicCircuit σ n m)
    (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U) :
    Fin c.size → U := (c.step I hI input).lfp

/-- Read all designated outputs at the least solution. -/
def CyclicCircuit.eval [CompleteLattice U] (c : CyclicCircuit σ n m)
    (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U) :
    Fin m → U := Wire.elim input (c.evalGates I hI input) ∘ c.outputs

/-- The least solution satisfies every gate equation. This is not a recursive simp rule. -/
theorem CyclicCircuit.evalGates_fixed [CompleteLattice U] (c : CyclicCircuit σ n m)
    (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U) (i : Fin c.size) :
    (c.lines i).eval I input (c.evalGates I hI input) = c.evalGates I hI input i :=
  congrFun (c.step I hI input).map_lfp i

/-- The solution lies below every state whose equation results lie below its gate values. -/
theorem CyclicCircuit.evalGates_le [CompleteLattice U] (c : CyclicCircuit σ n m)
    (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U)
    {state : Fin c.size → U} (h : ∀ i, (c.lines i).eval I input state ≤ state i) :
    c.evalGates I hI input ≤ state := (c.step I hI input).lfp_le h

/-- The unique solution of an acyclic program is its ordinary gate evaluation. -/
@[simp] theorem Circuit.evalGates_toCyclic [CompleteLattice U] (c : Circuit σ n m)
    (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U) :
    c.toCyclic.evalGates I hI input = c.program.eval I input :=
  c.program.eq_eval_of_forall_lines_eval I input _ (c.toCyclic.evalGates_fixed I hI input)

/-- Embedding a native circuit preserves all outputs, including direct inputs and sharing. -/
@[simp] theorem Circuit.eval_toCyclic [CompleteLattice U] (c : Circuit σ n m)
    (I : Interpretation σ U) (hI : ∀ op, Monotone (I op)) (input : Fin n → U) :
    c.toCyclic.eval I hI input = c.eval I input := by
  simp only [CyclicCircuit.eval, evalGates_toCyclic]
  rfl

namespace CyclicCircuit

variable [CompleteLattice U] {X : Type*}

/-- Compute the target from exactly the supplied sources using least-fixed-point semantics. -/
def ComputesFrom (c : CyclicCircuit σ n m) (I : Interpretation σ U)
    (hI : ∀ op, Monotone (I op)) (target : X → Fin m → U) (sources : X → Fin n → U) : Prop :=
  ∀ x, c.eval I hI (sources x) = target x

/-- Minimum weighted cyclic cost, or infinity if no implementing circuit exists. -/
noncomputable def ecomplexityFrom (I : Interpretation σ U) (hI : ∀ op, Monotone (I op))
    (weight : σ.Op → ℕ) (target : X → Fin m → U) (sources : X → Fin n → U) : ℕ∞ :=
  ⨅ c : {c : CyclicCircuit σ n m // c.ComputesFrom I hI target sources}, (c.val.cost weight : ℕ∞)

variable {I : Interpretation σ U} {hI : ∀ op, Monotone (I op)} {weight : σ.Op → ℕ}
  {target : X → Fin m → U} {sources : X → Fin n → U}

/-- Every implementing cyclic circuit bounds the minimum cost. -/
theorem ecomplexityFrom_le_of_computesFrom (c : CyclicCircuit σ n m)
    (hc : c.ComputesFrom I hI target sources) :
    ecomplexityFrom I hI weight target sources ≤ c.cost weight :=
  iInf_le (fun c : {c // c.ComputesFrom I hI target sources} => (c.val.cost weight : ℕ∞)) ⟨c, hc⟩

/-- Finite cyclic complexity is equivalent to the existence of an implementation. -/
theorem ecomplexityFrom_ne_top_iff :
    ecomplexityFrom I hI weight target sources ≠ ⊤ ↔
      ∃ c : CyclicCircuit σ n m, c.ComputesFrom I hI target sources := by
  rw [ecomplexityFrom, ENat.iInf_natCast_ne_top, nonempty_subtype]

/-- A lower bound on cyclic complexity holds exactly when it bounds every implementation. -/
theorem le_ecomplexityFrom_iff {k : ℕ∞} :
    k ≤ ecomplexityFrom I hI weight target sources ↔
      ∀ c : CyclicCircuit σ n m, c.ComputesFrom I hI target sources → k ≤ c.cost weight := by
  simp only [ecomplexityFrom, le_iInf_iff, Subtype.forall]

/-- Allowing feedback cannot increase minimum cost: native circuits embed without any cost. -/
theorem ecomplexityFrom_le_acyclic : ecomplexityFrom I hI weight target sources ≤
    Cslib.Circuits.ecomplexityFrom I weight target sources :=
  Cslib.Circuits.le_ecomplexityFrom_iff.mpr fun c hc => by
    simpa only [Circuit.cost_toCyclic] using
      ecomplexityFrom_le_of_computesFrom c.toCyclic
        (fun x => (c.eval_toCyclic I hI (sources x)).trans (hc x))

end CyclicCircuit

end Cslib.Circuits
