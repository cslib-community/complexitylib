/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.SimulationContext
import Complexity.Computability.Circuit.Fusion.SimulationContext
import Complexity.Computability.Circuit.Arithmetic.Power
import Complexity.Computability.Circuit.SumOfTerms
import Mathlib.Data.Fin.VecNotation

/-!
# Shared-context compilation and binary powering

The source circuit emits a power term, doubles it using the same wire twice, then emits an
unused copy of the term. Three outputs select the original term, its double and the original
term again. Compilation must preserve all outputs and charge both term gadgets exactly once.
-/

namespace ComplexityTests.ContextualPower

open Cslib.Circuits

universe u v w

private def source : Circuit (SumOfTerms.signature Unit) 0 3 :=
  ⟨(((Program.empty : Program (SumOfTerms.signature Unit) 0 0).gate
      ⟨.term (), Fin.elim0⟩).gate ⟨.add, fun _ => .gate 0⟩).gate ⟨.term (), Fin.elim0⟩,
    ![.gate 0, .gate 1, .gate 0]⟩

private def gadget (op : SumOfTerms.Op Unit) :
    Circuit (arithSignature Unit) (1 + op.arity) 1 :=
  match op with
  | .add => Circuit.oneGate (σ := arithSignature Unit) .add (Fin.natAdd 1)
  | .term _ => binaryPowerCircuit () 13

-- This executable circuit has ten multiplication gates and one addition gate.
example :
    (source.simulateWithContext 1 gadget).size = 11 ∧
    (source.simulateWithContext 1 gadget).program.cost ArithOp.mulCost = 10 := by
  decide

/-- info: [8192, 16384, 8192] -/
#guard_msgs in
#eval List.ofFn ((source.simulateWithContext 1 gadget).eval
  (arithInterpretationWith Unit (fun _ => (1 : ℕ))) (fun _ => 2))

-- The same computation is verified symbolically, over any semiring.
example {R : Type*} [Semiring R] (x : R) :
    (source.simulateWithContext 1 gadget).eval
      (arithInterpretationWith Unit (fun _ => (1 : R))) (fun _ => x) =
        ![x ^ 13, x ^ 13 + x ^ 13, x ^ 13] := by
  have hx : (fun _ : Fin 1 => x) = Fin.append (fun _ : Fin 1 => x) Fin.elim0 := by
    ext i
    fin_cases i
    rfl
  rw [hx, Circuit.eval_simulateWithContext]
  have hg : (fun op args => (gadget op).eval
      (arithInterpretationWith Unit (fun _ => (1 : R)))
      (Fin.append (fun _ : Fin 1 => x) args) 0) =
        SumOfTerms.interpretation (fun _ : Unit => x ^ 13) := by
    funext op args
    cases op with
    | add => simp [gadget, Circuit.eval_oneGate, arithInterpretationWith,
        SumOfTerms.interpretation, Fin.append, Fin.addCases]
    | term t =>
      rw [show gadget (.term t) = binaryPowerCircuit () 13 from rfl,
        eval_binaryPowerCircuit () (fun _ => (1 : R)) rfl]
      rfl
  rw [hg]
  ext j
  fin_cases j <;> rfl

-- A nullary source gate may compile to a free context wire.
private def contextWire (op : SumOfTerms.Op Unit) :
    Circuit (arithSignature Unit) (1 + op.arity) 1 :=
  match op with
  | .add => Circuit.oneGate (σ := arithSignature Unit) .add (Fin.natAdd 1)
  | .term _ => Circuit.wiring (arithSignature Unit) (fun _ => 0)

example :
    (source.simulateWithContext 1 contextWire).size = 1 ∧
    (source.simulateWithContext 1 contextWire).eval
      (arithInterpretationWith Unit (fun _ => (0 : ℕ))) (fun _ => 7) = ![7, 14, 7] := by
  decide

-- At context two, every multiplication reads positive values, for any source circuit.
-- Addition gadgets may read arbitrary arguments; they have no multiplication atoms.
private def positiveMulInputs : Fusion.Atom (arithSignature Unit) ℕ → Prop
  | ⟨.mul, args⟩ => ∀ i : Fin 2, 0 < args i
  | _ => True

private instance (a : Fusion.Atom (arithSignature Unit) ℕ) : Decidable (positiveMulInputs a) :=
  match a with
  | ⟨.mul, args⟩ => inferInstanceAs (Decidable (∀ i : Fin 2, 0 < args i))
  | ⟨.add, _⟩ | ⟨.const _, _⟩ => isTrue trivial

example {n m : ℕ} (c : Circuit (SumOfTerms.signature Unit) n m) (input : Fin n → ℕ) :
    ∀ k, positiveMulInputs (Fusion.programAtoms (c.simulateWithContext 1 gadget).program
      (arithInterpretationWith Unit (fun _ => (1 : ℕ)))
      (Fin.append (fun _ : Fin 1 => 2) input) k) := by
  apply Fusion.forall_programAtoms_simulateWithContext
  intro op args
  cases op with
  | add =>
    intro j
    change Fin 1 at j
    fin_cases j
    trivial
  | term t =>
    have hargs : Fin.append (fun _ : Fin 1 => 2) args = fun _ : Fin 1 => 2 := by
      ext i
      fin_cases i
      rfl
    rw [hargs]
    change ∀ j : Fin 5, positiveMulInputs (Fusion.programAtoms
      (binaryPowerCircuit () 13).program _ (fun _ => 2) j)
    intro j
    fin_cases j <;> decide

-- The fixed-context premise is substantive: the same first gadget atom fails at context zero.
example : ¬ positiveMulInputs (Fusion.programAtoms (gadget (.term ())).program
    (arithInterpretationWith Unit (fun _ => (1 : ℕ))) (fun _ => 0) (0 : Fin 5)) := by
  decide

-- A zero-gate term gadget contributes no atoms, including the unused source term.
example : ∀ k, (Fusion.programAtoms (source.simulateWithContext 1 contextWire).program
    (arithInterpretationWith Unit (fun _ => (0 : ℕ))) (fun _ => 7) k).op = .add := by
  have h := Fusion.forall_programAtoms_simulateWithContext source 1 contextWire
    (arithInterpretationWith Unit (fun _ => (0 : ℕ))) (fun _ => 7) Fin.elim0
    (fun a => a.op = .add) (by
      intro op args j
      cases op with
      | add => fin_cases j; rfl
      | term t => exact j.elim0)
  simpa only [Fin.append_elim0, Function.comp_def] using h

-- Both entries of a larger context remain available to every gadget.
private def productGadget (op : SumOfTerms.Op Unit) :
    Circuit (arithSignature Unit) (2 + op.arity) 1 :=
  match op with
  | .add => Circuit.oneGate (σ := arithSignature Unit) .add (Fin.natAdd 2)
  | .term _ => Circuit.oneGate (σ := arithSignature Unit) .mul id

-- Context-2 product gadget, raw source input identity, zero-context wiring, and
-- `binaryPowerCircuit` size, cost, and evaluation checks.
example (ctx : Fin 2 → ℕ) (x : Fin 1 → ℕ) (e : ℕ) :
    (source.simulateWithContext 2 productGadget).eval
      (arithInterpretationWith Unit (fun _ => (0 : ℕ))) ![3, 7] = ![21, 42, 21] ∧
    ((Circuit.id (SumOfTerms.signature Unit) 1).simulateWithContext 2
      (fun op => Circuit.oneGate (σ := SumOfTerms.signature Unit) op (Fin.natAdd 2))).eval
        (SumOfTerms.interpretation (fun _ : Unit => 0)) (Fin.append ctx x) = x ∧
    ((Circuit.wiring (arithSignature Unit) (Fin.elim0 : Fin 0 → Fin 0)).simulateWithContext
      0 (fun op => Circuit.oneGate op (Fin.natAdd 0))).size = 0 ∧
    ((binaryPowerCircuit () 0).program.cost (fun _ => 17) = 17 ∧
      (binaryPowerCircuit () 0).size = 1 ∧
      (binaryPowerCircuit () 1).size = 0 ∧
      (binaryPowerCircuit () 0).program.cost ArithOp.mulCost = 0 ∧
      (binaryPowerCircuit () 0).eval
        (arithInterpretationWith Unit (fun _ => (0 : ℕ))) (fun _ => 7) 0 = 0 ∧
      binaryMultiplicationCount 15 = 6 ∧
      (binaryPowerCircuit () 1024).size = 10 ∧
      (binaryPowerCircuit () 13).program.cost
        (fun op => match op with | .mul => 7 | .add => 11 | .const _ => 19) = 35) ∧
    (binaryPowerCircuit () e).program.cost
      (fun op => match op with | .add => 1 | _ => 0) = 0 := by
  refine ⟨by decide, by rw [Circuit.eval_simulateWithContext]; rfl, by decide, by decide, ?_⟩
  rw [cost_program_binaryPowerCircuit]
  split_ifs <;> simp

-- No commutativity or distributivity is needed for the power circuit's semantics.
example {R : Type*} [Add R] [Monoid R] (x : R) (e : ℕ) :
    (binaryPowerCircuit () e).eval (arithInterpretationWith Unit (fun _ => (1 : R)))
      (fun _ => x) 0 = x ^ e :=
  eval_binaryPowerCircuit () (fun _ => (1 : R)) rfl e _

-- The two signatures and carrier have independent universe levels.
example {σ : Signature.{u}} {τ : Signature.{v}} {R : Type w} {n m q : ℕ}
    (c : Circuit σ n m) (impl : ∀ op : σ.Op, Circuit τ (q + σ.Arity op) 1)
    (J : Interpretation τ R) (ctx : Fin q → R) (x : Fin n → R) :
    (c.simulateWithContext q impl).eval J (Fin.append ctx x) =
      c.eval (fun op args => (impl op).eval J (Fin.append ctx args) 0) x :=
  c.eval_simulateWithContext q impl J ctx x

end ComplexityTests.ContextualPower
