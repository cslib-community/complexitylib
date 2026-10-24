/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.CircuitValue.Completeness

/-! The circuit value problem is `P`-complete under logarithmic-space
reductions. Clients: the tableau of any machine is a well-formed circuit with its output wire
among its wires; its hypothesis `n < 2 T` is met by the time bound of the reduction; the reduction
applies to the circuit value problem itself and to its complement; completeness transfers to
polynomial-time reductions; and axiom guards for the headline results. -/

namespace ComplexityTests.CircuitValueCompleteness

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)

/-! The canonical space APIs retain the full input-dependent budget telescope. -/

section PlainTableauBudgets
variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ} {n T g : α → ℕ}

-- Same arbitrary input encoding, bound, time function and finite state family.
example (hT : ComputableInSpace T encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun x => Tableau.gfStart k State (T x)) encIn encNat Bs :=
  Tableau.gfStart_inSpace hT hin

example (hT : ComputableInSpace T encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs) :
    ComputableInSpace (fun x => Tableau.blockSize k State (T x)) encIn encNat Bs :=
  Tableau.blockSize_inSpace hT hin

example (tm : MultiTapeTM k Bool State)
    (hn : ComputableInSpace n encIn encNat Bs)
    (hT : ComputableInSpace T encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs)
    (hg : ComputableInSpace g encIn encNat Bs) :
    ComputableInSpace (fun x => Tableau.gateCode tm (n x) (T x) (g x)) encIn encGate Bs :=
  Tableau.gateCode_inSpace tm hn hT hin hg
end PlainTableauBudgets

/-- The tableau is the code of a program, for every machine, input length and time bound. -/
example (n T : ℕ) : Program.IsCodeFrom signature n 0 (Tableau.gates tm n T) :=
  Tableau.isCodeFrom_gates tm n T

/-- The output wire of the tableau is a wire of the circuit. -/
example (n T : ℕ) : Tableau.outWire k State n T < n + (Tableau.gates tm n T).length := by
  simpa [Tableau.gates] using Tableau.outWire_lt (k := k) (State := State) n T

/-- The time bound of the reduction leaves room for the input head: `n < 2 T`. -/
example (C d n : ℕ) : n < 2 * CircuitValue.timeBound C d n := by
  simp only [CircuitValue.timeBound]
  omega

/-- The tableau circuit on the input `w` outputs whether the machine has written `[true]`. -/
example (C d : ℕ) (w : List Bool) :
    (CircuitValue.tableauInstance tm C d w).2.1.eval interpretation
        (CircuitValue.tableauInstance tm C d w).2.2 0 =
      decide (OutView.ofList
        (tm.runFrom (tm.initCfg w) (CircuitValue.timeBound C d w.length)).output = .one true) := by
  have hw : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  simp only [CircuitValue.tableauInstance]
  rw [Tableau.eval_circuit tm (by simp only [CircuitValue.timeBound]; omega), hw]

/-- The circuit value problem reduces to itself through the tableau of its decider. -/
example : LogSpaceReducible encCircuitValue encCircuitValue CircuitValue CircuitValue :=
  CircuitValue.logSpaceReducible_of_mem_P CircuitValue.mem_P

/-- Its complement is in `P`, so it reduces to the circuit value problem too. -/
example : LogSpaceReducible encCircuitValue encCircuitValue CircuitValueᶜ CircuitValue :=
  CircuitValue.logSpaceHard _ _ (compl_mem_P CircuitValue.mem_P)

/-- Completeness under logspace reductions gives completeness under polynomial-time ones. -/
example : PolyTimeComplete @P encCircuitValue CircuitValue :=
  CircuitValue.logSpaceComplete.polyTimeComplete

/-- If the circuit value problem were in `L`, every problem in `P` would be, for every encoding. -/
example (h : CircuitValue ∈ L encCircuitValue) : P encBits = L encBits :=
  CircuitValue.mem_L_iff_forall_P_eq_L.1 h encBits

/-- Hardness transfers through the identity reduction. -/
example : LogSpaceHard @P encCircuitValue CircuitValue :=
  CircuitValue.logSpaceHard.trans (LogSpaceReducible.refl _ _)

/-- A logspace-hard problem in `L` contains the whole source class in `L`. -/
example (h : CircuitValue ∈ L encCircuitValue) : P encBits ⊆ L encBits :=
  CircuitValue.logSpaceHard.subset_L h encBits

/-! ### Axiom guards -/

/-- A single certified constructor provides circuits for every encoded input length. -/
example {α : Type} {enc : α ↪ List Bool} {f : α → Bool}
    (hf : ComputableInPolyTime f enc encBool) :
    ∃ circuits : (n : ℕ) → Circuit signature n 1,
      ComputableInPolyTime (fun n => (circuits n).code) encUnary encCode ∧
      ∀ a, (circuits (enc a).length).eval interpretation (fun i => (enc a)[i]) 0 = f a :=
  CircuitValue.exists_uniformCircuits hf

/-- info: 'Cslib.Complexity.CircuitValue.exists_uniformCircuits' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.exists_uniformCircuits

/-- info: 'Cslib.Complexity.CircuitValue.computableInPolyTime_tableauCode' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.computableInPolyTime_tableauCode

/-- info: 'Cslib.Complexity.CircuitValue.logSpaceComplete' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.logSpaceComplete

/-- info: 'Cslib.Complexity.CircuitValue.logSpaceHard' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.logSpaceHard

/-- info: 'Cslib.Complexity.CircuitValue.mem_L_iff_forall_P_eq_L' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.mem_L_iff_forall_P_eq_L

/-- info: 'Cslib.Complexity.CircuitValue.computableInLogSpace_tableauInstance' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.computableInLogSpace_tableauInstance

/-- info: 'Cslib.Circuits.Boolean.Tableau.eval_circuit' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Tableau.eval_circuit

/-- info: 'Cslib.Circuits.Boolean.Tableau.gateCode_inSpace' depends on axioms: [propext,
Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms Tableau.gateCode_inSpace

/-- info: 'Cslib.Complexity.CircuitValue.logSpaceReducible_of_mem_P' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.logSpaceReducible_of_mem_P

/-- info: 'Cslib.Complexity.CircuitValue.run_writer' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms CircuitValue.run_writer

end ComplexityTests.CircuitValueCompleteness
