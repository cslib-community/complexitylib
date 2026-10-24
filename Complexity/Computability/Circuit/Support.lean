/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate
public import Cslib.Computability.Circuit.Basic
public import Complexity.Computability.Circuit.Program
public import Mathlib.Data.Fin.SuccPred
public import Mathlib.Data.Finset.Union
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Logic.Function.DependsOn

/-!
# Circuit input support

This file computes the original inputs that can affect each wire and proves
that circuit evaluation depends only on those inputs. An input on which a function depends
essentially (`EssentialAt`) therefore reaches an output of every circuit computing it.

## Main definitions

* `Cslib.Circuits.EssentialAt`: coordinates whose change can change a function.
* `Cslib.Circuits.supportInterpretation`, `Cslib.Circuits.Line.inputSupport`,
  `Cslib.Circuits.Program.gateSupport`, `Cslib.Circuits.Program.wireSupport`,
  `Cslib.Circuits.Circuit.outputSupport`, `Cslib.Circuits.Circuit.inputSupport`: the support
  interpretation and the structural input supports of lines, gates, wires, outputs, and circuits.

## Main results

* `Cslib.Circuits.Circuit.dependsOn_eval`: a circuit depends only on its input support.
-/

@[expose] public section

namespace Cslib.Circuits

variable {σ : Signature} {U V : Type*} {n m g : ℕ}

/-- Changing only coordinate `i` can change the value of `f`. -/
def EssentialAt (f : (Fin n → U) → V) (i : Fin n) : Prop :=
  ∃ x y, (∀ k, k ≠ i → x k = y k) ∧ f x ≠ f y

/-- Every essential coordinate belongs to any support of the function. -/
theorem EssentialAt.mem_support {f : (Fin n → U) → V} {support : Finset (Fin n)} {i : Fin n}
    (h : EssentialAt f i) (hf : DependsOn f (support : Set (Fin n))) : i ∈ support := by
  obtain ⟨x, y, hxy, hne⟩ := h
  by_contra hi
  exact hne (hf fun k hk => hxy k fun e => hi (e ▸ hk))

/-- A coordinate is essential exactly when the function does not depend only on the others. -/
theorem essentialAt_iff_not_dependsOn {f : (Fin n → U) → V} {i : Fin n} :
    EssentialAt f i ↔ ¬DependsOn f {i}ᶜ := by
  simp only [EssentialAt, DependsOn, Set.mem_compl_iff, Set.mem_singleton_iff, not_forall,
    exists_prop]


/-- The support interpretation unions the supports of a gate's argument wires. -/
def supportInterpretation (σ : Signature) (n : ℕ) : Interpretation σ (Finset (Fin n)) :=
  fun _ supports => Finset.univ.biUnion supports


/-- The original inputs supporting a line, given the support of each wire. -/
def Line.inputSupport
    (line : Line σ n g)
    (wireSupport : Wire n g → Finset (Fin n)) : Finset (Fin n) :=
  Finset.univ.biUnion fun k => wireSupport (line.wires k)


/-- Membership in a line's input support comes from one of its arguments. -/
@[simp] theorem Line.mem_inputSupport
    {line : Line σ n g}
    {wireSupport : Wire n g → Finset (Fin n)}
    {input : Fin n} :
    input ∈ line.inputSupport wireSupport ↔
      ∃ argument, input ∈ wireSupport (line.wires argument) := by
  simp [Line.inputSupport]


/-- The input support of every gate in a program. -/
def Program.gateSupport (program : Program σ n g) : Fin g → Finset (Fin n) :=
  program.eval (supportInterpretation σ n) (fun i => {i})


/-- The input support of every input or gate wire in a program. -/
def Program.wireSupport
    (program : Program σ n g) : Wire n g → Finset (Fin n) :=
  program.trace (supportInterpretation σ n) (fun i => {i})


/-- An input wire is supported only by that input. -/
@[simp] theorem Program.wireSupport_input
    (program : Program σ n g)
    (input : Fin n) :
    program.wireSupport (Wire.input input) = {input} := rfl


/-- A gate-output wire has the support of that gate. -/
@[simp] theorem Program.wireSupport_gate
    (program : Program σ n g)
    (gate : Fin g) :
    program.wireSupport (Wire.gate gate) =
      program.gateSupport gate := rfl


/-- Adding a gate preserves the support of every earlier wire. -/
@[simp] theorem Program.wireSupport_gate_castSucc
    (program : Program σ n g)
    (line : Line σ n g)
    (wire : Wire n g) :
    (program.gate line).wireSupport wire.castSucc = program.wireSupport wire :=
  program.trace_gate_castSucc line (supportInterpretation σ n) (fun i => {i}) wire


/-- The new gate is supported by precisely the inputs supporting the new line. -/
@[simp] theorem Program.gateSupport_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).gateSupport (Fin.last g) =
      line.inputSupport program.wireSupport :=
  program.eval_gate_last line (supportInterpretation σ n) (fun i => {i})


/-- The new wire is supported by precisely the inputs supporting the new line. -/
theorem Program.wireSupport_gate_last
    (program : Program σ n g)
    (line : Line σ n g) :
    (program.gate line).wireSupport (Wire.gate (Fin.last g)) =
      line.inputSupport program.wireSupport :=
  program.gateSupport_gate_last line


/-- The input support of every designated output wire in a circuit. -/
def Circuit.outputSupport
    (c : Circuit σ n m) : Fin m → Finset (Fin n) :=
  c.program.wireSupport ∘ c.outputs


/-- The union of the input supports of a circuit's outputs. -/
def Circuit.inputSupport (c : Circuit σ n m) : Finset (Fin n) :=
  Finset.univ.biUnion c.outputSupport


/-- An input supports a circuit exactly when it supports a designated output wire. -/
@[simp] theorem Circuit.mem_inputSupport
    {c : Circuit σ n m}
    {input : Fin n} :
    input ∈ c.inputSupport ↔
      ∃ output, input ∈ c.program.wireSupport (c.outputs output) := by
  simp [Circuit.inputSupport, Circuit.outputSupport]


/-- Program traces agree on any wire whose supporting inputs agree. -/
theorem Program.trace_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (wire : Wire n g)
    (agree : ∀ i ∈ program.wireSupport wire, left i = right i) :
    program.trace interpretation left wire =
      program.trace interpretation right wire := by
  revert agree
  refine program.wire_induction (P := fun wire =>
    (∀ i ∈ program.wireSupport wire, left i = right i) →
      program.trace interpretation left wire = program.trace interpretation right wire)
    (fun i agree => agree i (Finset.mem_singleton_self i)) (fun k ih agree => ?_) wire
  rw [program.trace_gate, program.trace_gate]
  congr 1
  funext a
  apply ih a
  intro i hi
  apply agree i
  change i ∈ program.trace (supportInterpretation σ n) (fun i => {i}) (.gate k)
  rw [program.trace_gate]
  exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_univ a, hi⟩


/-- Program gates agree whenever their supporting inputs agree. -/
theorem Program.eval_congr
    (program : Program σ n g)
    (interpretation : Interpretation σ U)
    (left right : Fin n → U)
    (k : Fin g)
    (agree : ∀ i ∈ program.gateSupport k, left i = right i) :
    program.eval interpretation left k = program.eval interpretation right k :=
  program.trace_congr interpretation left right (.gate k) agree


/-- Circuit evaluation depends only on the circuit's structural input support. -/
theorem Circuit.dependsOn_eval
    (c : Circuit σ n m)
    (interpretation : Interpretation σ U) :
    DependsOn (c.eval interpretation) (c.inputSupport : Set (Fin n)) := by
  intro left right agree
  funext output
  apply c.program.trace_congr interpretation left right (c.outputs output)
  intro input present
  exact agree input (Circuit.mem_inputSupport.mpr ⟨output, present⟩)


/-- A computed function depends only on the circuit's structural input support. -/
theorem Circuit.Computes.dependsOn
    {c : Circuit σ n m}
    {interpretation : Interpretation σ U}
    {target : (Fin n → U) → Fin m → U}
    (computes : c.Computes interpretation target) :
    DependsOn target (c.inputSupport : Set (Fin n)) := by
  intro left right agree
  rw [← computes left, ← computes right]
  exact c.dependsOn_eval interpretation agree


end Cslib.Circuits
