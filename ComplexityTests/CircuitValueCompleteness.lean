/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Problems.CircuitValue.Completeness

/-! The circuit value problem is `P`-complete under logarithmic-space
reductions. Clients: the tableau of any machine is a well-formed circuit with its output wire
among its wires; its hypothesis `n < 2 T` is met by the time bound of the reduction; the reduction
applies to the circuit value problem itself and to its complement; and completeness transfers to
polynomial-time reductions. -/

namespace ComplexityTests.CircuitValueCompleteness

open Cslib Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean Turing Turing.MultiTapeTM

variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  (tm : MultiTapeTM k Bool State)

/-! The canonical space APIs retain the full input-dependent budget telescope. -/

section PlainTableauBudgets
variable {k : ℕ} {State : Type} [Fintype State] [DecidableEq State]
  {α : Type} {encIn : α ↪ List Bool} {Bs : α → ℕ} {n g : α → ℕ}

-- Composing `timeBound_inSpace` with `gfStart_inSpace`, `blockSize_inSpace`, `numGates_inSpace`,
-- and `gateCode_inSpace`.
example (tm : MultiTapeTM k Bool State) (C d : ℕ)
    (hn : ComputableInSpace n encIn encNat Bs)
    (hin : (fun x => (encIn x).length) ≼ Bs)
    (hg : ComputableInSpace g encIn encNat Bs) :
    ComputableInSpace (fun x => Tableau.gfStart k State (CircuitValue.timeBound C d (n x)))
      encIn encNat Bs ∧
    ComputableInSpace (fun x => Tableau.blockSize k State (CircuitValue.timeBound C d (n x)))
      encIn encNat Bs ∧
    ComputableInSpace (fun x => Tableau.numGates k State (CircuitValue.timeBound C d (n x)))
      encIn encNat Bs ∧
    ComputableInSpace (fun x => Tableau.gateCode tm (n x) (CircuitValue.timeBound C d (n x)) (g x))
      encIn encGate Bs :=
  let hT := CircuitValue.timeBound_inSpace C d hin hn
  ⟨Tableau.gfStart_inSpace hT hin,
    Tableau.blockSize_inSpace hT hin,
    CircuitValue.numGates_inSpace hin hT,
    Tableau.gateCode_inSpace tm hn hT hin hg⟩
end PlainTableauBudgets

/-- The tableau's output wire lies within its wires, and the time bound of the reduction leaves
room for the input head (`n < 2 T`). -/
example (C d n T : ℕ) :
    Tableau.outWire k State n T < n + (Tableau.gates tm n T).length ∧
    n < 2 * CircuitValue.timeBound C d n :=
  ⟨by simpa [Tableau.gates] using Tableau.outWire_lt (k := k) (State := State) n T,
    by simp only [CircuitValue.timeBound]; omega⟩

/-- The tableau circuit on the input `w` outputs whether the machine has written `[true]`. -/
example (C d : ℕ) (w : List Bool) :
    (CircuitValue.tableauInstance tm C d w).2.1.eval interpretation
        (CircuitValue.tableauInstance tm C d w).2.2 0 =
      decide (OutView.ofList
        (tm.runFrom (tm.initCfg w) (CircuitValue.timeBound C d w.length)).output = .one true) := by
  have hw : List.ofFn (fun i : Fin w.length => w[i]) = w := List.ofFn_getElem
  simp only [CircuitValue.tableauInstance]
  rw [Tableau.eval_circuit tm (by simp only [CircuitValue.timeBound]; omega), hw]

/-- `CircuitValue` and its complement reduce to `CircuitValue` in logarithmic space and polynomial
time. -/
example :
    LogSpaceReducible encCircuitValue encCircuitValue CircuitValue CircuitValue ∧
    LogSpaceReducible encCircuitValue encCircuitValue CircuitValueᶜ CircuitValue ∧
    PolyTimeReducible encCircuitValue encCircuitValue CircuitValueᶜ CircuitValue :=
  ⟨CircuitValue.logSpaceReducible_of_mem_P CircuitValue.mem_P,
    CircuitValue.logSpaceHard _ _ (compl_mem_P CircuitValue.mem_P),
    CircuitValue.logSpaceComplete.polyTimeComplete.2 _ _ (compl_mem_P CircuitValue.mem_P)⟩

/-- If `CircuitValue` lies in `L`, then `CircuitValueᶜ ∈ L`. -/
example (h : CircuitValue ∈ L encCircuitValue) :
    CircuitValueᶜ ∈ L encCircuitValue :=
  CircuitValue.logSpaceHard.subset_L h encCircuitValue (compl_mem_P CircuitValue.mem_P)

/-- Uniform circuit generation applied to the polynomial-time head-bit extractor `headD false`. -/
example :
    ∃ circuits : (n : ℕ) → Circuit signature n 1,
      ComputableInPolyTime (fun n => (circuits n).code) encUnary encCode ∧
      ∀ w : List Bool,
        (circuits (encBits w).length).eval interpretation (fun i => (encBits w)[i]) 0 =
          w.headD false :=
  CircuitValue.exists_uniformCircuits (enc := encBits)
    (ComputableInPolyTime.headD (encA := encBool) false)

end ComplexityTests.CircuitValueCompleteness
