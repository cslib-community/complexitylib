/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Computability.Circuit.Fusion.Composition
import CslibFrontier.Computability.Circuit.Fusion.Simulation
import CslibFrontier.Computability.Circuit.Fusion.SimulationContext
import CslibFrontier.Computability.Circuit.SumOfTerms.Basic
import Mathlib.Tactic.FinCases

/-!
# Fusion transport clients

Composition preserves atom order and evaluated arguments through repeated outputs and supplied
inputs. Native simulation retains unused gadget gates. Its local criterion needs bounds only
on actual gadget inputs, and its reverse implication detects a bad unused atom.
-/

namespace CslibFrontierTests.FusionTransport

open Cslib.Circuits SumOfTerms

private def inner : Circuit (signature ℕ) 2 3 :=
  ⟨((Program.empty : Program (signature ℕ) 2 0).gate ⟨.add, ![.input 0, .input 1]⟩).gate
    ⟨.term 9, Fin.elim0⟩, ![.gate 0, .input 0, .gate 0]⟩

private def outer : Circuit (signature ℕ) 3 3 :=
  ⟨((Program.empty : Program (signature ℕ) 3 0).gate ⟨.add, ![.input 0, .input 2]⟩).gate
    ⟨.add, ![.gate 0, .input 1]⟩, ![.gate 0, .gate 1, .gate 0]⟩

private def atomView (a : Fusion.Atom (signature ℕ) ℕ) : Option ℕ × List ℕ :=
  (match a.op with | .add => none | .term t => some t, List.ofFn a.arguments)

-- The unused term remains between the inner and outer additions, while repeated outputs are free.
/-- info: [(none, [2, 3]), (some 9, []), (none, [5, 5]), (none, [10, 2])] -/
#guard_msgs in
#eval List.ofFn (fun k => atomView
  (Fusion.programAtoms (outer.comp inner).program (interpretation id) ![2, 3] k))

example : (outer.comp inner).eval (interpretation id) ![2, 3] = ![10, 12, 10] := by decide

example : Fusion.programAtoms (outer.comp inner).program (interpretation id) ![2, 3] =
    Fin.append (Fusion.programAtoms inner.program (interpretation id) ![2, 3])
      (Fusion.programAtoms outer.program (interpretation id) ![5, 2, 5]) := by
  rw [Fusion.programAtoms_comp,
    show inner.eval (interpretation id) ![2, 3] = ![5, 2, 5] from by decide]

-- Direct continuation can read an ambient gate not designated as an output.
private def duplicate : Program (signature ℕ) 1 1 :=
  Program.empty.gate ⟨.add, fun _ => .input 0⟩

example : Fusion.programAtoms (inner.program.append (fun _ => .gate (1 : Fin 2)) duplicate)
    (interpretation id) ![2, 3] =
      Fin.append (Fusion.programAtoms inner.program (interpretation id) ![2, 3])
        (Fusion.programAtoms duplicate (interpretation id) (fun _ => 9)) :=
  Fusion.programAtoms_append inner.program (fun _ => .gate (1 : Fin 2)) duplicate
    (interpretation id) ![2, 3]

-- Every implementation computes its operation, then emits an unused term.
private def implementation (op : Op ℕ) : Circuit (signature ℕ) op.arity 1 :=
  ⟨((Program.empty : Program (signature ℕ) op.arity 0).gate ⟨op, Wire.input⟩).gate
    ⟨.term 99, Fin.elim0⟩, fun _ => .gate 0⟩

private theorem implementation_computes (op : Op ℕ) :
    (implementation op).Computes (interpretation id) (single (interpretation id op)) := by
  intro x
  funext o
  fin_cases o
  rfl

private def smallInputs (a : Fusion.Atom (signature ℕ) ℕ) : Prop :=
  ∀ i, a.arguments i ≤ 10

private instance (a : Fusion.Atom (signature ℕ) ℕ) : Decidable (smallInputs a) :=
  inferInstanceAs (Decidable (∀ i, a.arguments i ≤ 10))

-- Actual gadget arguments satisfy the bound even though arbitrary arguments need not.
example : ∀ j, smallInputs (Fusion.programAtoms
    ((outer.comp inner).simulate implementation).program (interpretation id) ![2, 3] j) := by
  apply Fusion.forall_programAtoms_simulate (outer.comp inner) implementation
    implementation_computes ![2, 3] smallInputs
  decide

example : ¬ smallInputs (Fusion.programAtoms (implementation .add).program
    (interpretation id) ![99, 99] (0 : Fin 2)) := by decide

private def wrongModel : Circuit (signature ℕ) 0 1 :=
  ⟨((Program.empty : Program (signature ℕ) 0 0).gate ⟨.term 20, Fin.elim0⟩).gate
    ⟨.add, fun _ => .gate 0⟩, fun _ => .gate 1⟩

-- If source semantics disagree with gadget semantics, its local bound need not transfer.
example :
    (∀ k,
      let a := Fusion.programAtoms wrongModel.program (interpretation (fun _ => (0 : ℕ)))
        Fin.elim0 k
      ∀ j, smallInputs (Fusion.programAtoms (implementation a.op).program
        (interpretation id) a.arguments j)) ∧
    ¬ ∀ j, smallInputs (Fusion.programAtoms (wrongModel.simulate implementation).program
      (interpretation id) Fin.elim0 j) := by decide

-- Both the unused source term and each unused gadget term are charged.
example : ((outer.comp inner).simulate implementation).size = 8 ∧
    ((outer.comp inner).simulate implementation).program.cost termCost = 5 := by decide

example : ((outer.comp inner).simulate implementation).eval (interpretation id) ![2, 3] =
    ![10, 12, 10] := by
  rw [Circuit.eval_simulate _ _ implementation_computes]
  decide

-- The reverse implication detects an unused bad gadget atom, even for a one-gate source.
example : ¬ ∀ j, (Fusion.programAtoms
    ((Circuit.oneGate (σ := signature ℕ) .add id).simulate implementation).program
      (interpretation id) ![2, 3] j).op ≠ .term 99 := by
  intro h
  have hg := (Fusion.forall_programAtoms_simulate_iff
    (Circuit.oneGate (σ := signature ℕ) .add id).program implementation
    implementation_computes ![2, 3] (fun a => a.op ≠ .term 99)).mp h
  exact hg (0 : Fin 1) (1 : Fin 2) rfl

-- A zero-gate source has no atom obligations.
example : ∀ _ : Fin 0, False :=
  (Fusion.forall_programAtoms_simulate_iff (Program.empty : Program (signature ℕ) 0 0)
    implementation implementation_computes Fin.elim0 (fun _ => False)).mpr
      (fun k => k.elim0)

-- The transport API preserves independence of the source, target and carrier universes.
universe u v w
example {σ : Signature.{u}} {τ : Signature.{v}} {U : Type w} {n m q : ℕ}
    (c : Circuit σ n m) (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1)
    (J : Interpretation τ U) (ctx : Fin q → U) (x : Fin n → U)
    (P : Fusion.Atom τ U → Prop)
    (h : ∀ op args j, P (Fusion.programAtoms (impl op).program J (Fin.append ctx args) j)) :
    ∀ j, P (Fusion.programAtoms (c.simulateWithContext q impl).program J (Fin.append ctx x) j) :=
  Fusion.forall_programAtoms_simulateWithContext c q impl J ctx x P h

end CslibFrontierTests.FusionTransport
