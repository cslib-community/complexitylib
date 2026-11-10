/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Basic
public import CslibFrontier.Computability.Circuit.SimulationContext
import CslibFrontier.Computability.Circuit.Fusion.Simulation
import Cslib.Foundations.Data.Fin.Tuple

/-!
# Local Fusion properties with shared context

Every gate of `Circuit.withContext` receives the same supplied context. Therefore a local
property of contextual gadgets transfers to every atom of the compiled circuit, with gadget
assumptions needed only at this fixed context. The rest of each gadget's arguments may be
arbitrary. Compilation and cost accounting remain those of native contextual simulation.

## Main results

* `Cslib.Circuits.Fusion.forall_programAtoms_withContext`: all source atoms receive the context.
* `Cslib.Circuits.Fusion.forall_programAtoms_simulateWithContext`: transfer gadget properties
  to the compiled circuit at a fixed context.

## References

* Adapted from LowerBound/Fusion/Contextual.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

public section

namespace Cslib.Circuits.Fusion

universe u v w

variable {σ : Signature.{u}} {τ : Signature.{v}} {U : Type w} {n m : ℕ}

/-- Every atom of a context-bearing circuit receives the same context prefix. -/
theorem forall_programAtoms_withContext (c : Circuit σ n m) (q : ℕ)
    (I : Interpretation (σ.withContext q) U) (context : Fin q → U) (input : Fin n → U)
    (P : Atom (σ.withContext q) U → Prop)
    (h : ∀ op args, P ⟨op, Fin.append context args⟩) :
    ∀ k, P (programAtoms (c.withContext q).program I (Fin.append context input) k) := by
  suffices ∀ g (p : Program σ (q + n) g) k,
      P (programAtoms (p.mapLines (Line.withContext q)) I (Fin.append context input) k) from
    this _ _
  intro g p
  induction p with
  | empty => exact fun k => k.elim0
  | gate p line ih =>
    rw [Program.mapLines_gate, programAtoms_gate]
    intro k
    induction k using Fin.lastCases with
    | cast k => simpa only [Fin.snoc_castSucc] using ih k
    | last =>
      rw [Fin.snoc_last]
      change P ⟨line.op, _ ∘ Fin.append (Wire.input ∘ Fin.castAdd n) line.wires⟩
      rw [Fin.comp_append]
      simpa only [Function.comp_def, Program.trace_input, Fin.append_left] using
        h line.op ((p.mapLines (Line.withContext q)).trace I
          (Fin.append context input) ∘ line.wires)

/-- A property of every gadget atom at the supplied context holds throughout compilation.
No assumption is made about the same gadget at a different context. -/
theorem forall_programAtoms_simulateWithContext (c : Circuit σ n m) (q : ℕ)
    (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1)
    (J : Interpretation τ U) (context : Fin q → U) (input : Fin n → U)
    (P : Atom τ U → Prop)
    (hlocal : ∀ op args j, P (programAtoms (impl op).program J (Fin.append context args) j)) :
    ∀ j, P (programAtoms (c.simulateWithContext q impl).program J
      (Fin.append context input) j) := by
  let I : Interpretation (σ.withContext q) U := fun op args => (impl op).eval J args 0
  have himpl : ∀ op, (impl op).Computes J (single (I op)) :=
    fun _ _ => funext fun j => congrArg _ (Subsingleton.elim j 0)
  exact forall_programAtoms_simulate (c.withContext q) impl himpl (Fin.append context input) P
    (forall_programAtoms_withContext c q I context input
      (fun a => ∀ j, P (programAtoms (impl a.op).program J a.arguments j)) hlocal)

end Cslib.Circuits.Fusion
