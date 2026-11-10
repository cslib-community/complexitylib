/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Fusion.Basic
public import CslibFrontier.Computability.Circuit.Simulation
import CslibFrontier.Computability.Circuit.Fusion.Composition

/-!
# Local Fusion properties under circuit simulation

A property holds at every compiled atom exactly when it holds at every atom of each operation
gadget, evaluated at the source gate's actual arguments. This includes unused source gates and
all gates of each gadget, whether or not its output uses them. Zero-gate implementations add no
atoms. The simulation is CSLib's native gate replacement.

## Main results

* `Cslib.Circuits.Fusion.forall_programAtoms_simulate_iff`: reduce a property of all compiled
  atoms to the actual operation gadgets.
* `Cslib.Circuits.Fusion.forall_programAtoms_simulate`: circuit-level local property transfer.

## References

* Generalizes the transport argument in LowerBound/Fusion/Contextual.lean in
  [S. Schlesinger, *Algebraic circuit formalizations in Complexitylib*][Schlesinger2026Algebraic].
-/

public section

namespace Cslib.Circuits.Fusion

universe u v w

variable {σ : Signature.{u}} {τ : Signature.{v}} {U : Type w} {n m g : ℕ}

/-- Every compiled atom has a property exactly when all actual gadget atoms do.
The gadget assumptions are needed only at the arguments of source gates. -/
theorem forall_programAtoms_simulate_iff (p : Program σ n g)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    {I : Interpretation σ U} {J : Interpretation τ U}
    (himpl : ∀ op, (impl op).Computes J (single (I op))) (input : Fin n → U)
    (P : Atom τ U → Prop) :
    (∀ j, P (programAtoms (p.simulateProgram impl) J input j)) ↔
      ∀ k, let a := programAtoms p I input k
        ∀ j, P (programAtoms (impl a.op).program J a.arguments j) := by
  induction p with
  | empty => simp [Program.simulateProgram, Program.simulate]
  | gate p line ih =>
    change (∀ j, P (programAtoms ((p.simulateProgram impl).append
      (p.simulateRenaming impl ∘ line.wires) (impl line.op).program) J input j)) ↔ _
    rw [programAtoms_append, ← Function.comp_assoc, p.trace_simulate impl himpl,
      programAtoms_gate]
    simp only [Fin.forall_fin_add, Fin.append_left, Fin.append_right, ih,
      Fin.forall_fin_succ']
    refine and_congr (forall_congr' fun k => ?_) ?_
    · rw [Fin.snoc_castSucc]
    · rw [Fin.snoc_last]

/-- Local gadget properties transfer to every atom of the simulated circuit. -/
theorem forall_programAtoms_simulate (c : Circuit σ n m)
    (impl : ∀ op : σ.Op, Circuit τ (σ.Arity op) 1)
    {I : Interpretation σ U} {J : Interpretation τ U}
    (himpl : ∀ op, (impl op).Computes J (single (I op))) (input : Fin n → U)
    (P : Atom τ U → Prop)
    (hlocal : ∀ k, let a := programAtoms c.program I input k
      ∀ j, P (programAtoms (impl a.op).program J a.arguments j)) :
    ∀ j, P (programAtoms (c.simulate impl).program J input j) :=
  (forall_programAtoms_simulate_iff c.program impl himpl input P).mpr hlocal

end Cslib.Circuits.Fusion
