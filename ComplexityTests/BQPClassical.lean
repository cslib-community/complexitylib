/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.BQP.Classical
import Complexity.Computability.Complexity.Problems.CircuitValue

/-! `P ⊆ BQP`: the reversible compilation of a concrete De Morgan gate list, its exact acceptance
probability, and the circuit value problem in `BQP`. -/

namespace ComplexityTests.BQPClassical

open Cslib Cslib.Quantum Cslib.Complexity Cslib.Circuits Cslib.Circuits.Boolean

/-- Exclusive or of the inputs `0, 1` as a De Morgan gate list: wire `2` is `x₀ ∨ x₁`, wire `3` is
`x₀ ∧ x₁`, wire `4` is `¬ x₀ ∧ x₁`, and wire `5` is their conjunction. -/
def xorGates : List (Op × List ℕ) := [(.or, [0, 1]), (.and, [0, 1]), (.not, [3]), (.and, [2, 4])]

-- Compiled onto `2 + 4 + 1` qubits, qubit `5` holds `x₀ ⊕ x₁`.
example : readBit (GateCode.classicalRun (Reversible.codes 2 6 xorGates)
    (fun i : Fin 7 => decide (i = 0))) 5 = true := by decide
example : readBit (GateCode.classicalRun (Reversible.codes 2 6 xorGates)
    (fun i : Fin 7 => decide (i.val < 2))) 5 = false := by decide

-- A repeated argument compiles to a CNOT, and an argument naming a later wire reads `false`.
example : readBit (GateCode.classicalRun (Reversible.codes 1 3 [(.or, [0, 0]), (.and, [0, 7])])
    (fun i : Fin 4 => decide (i = 0))) 1 = true := by decide
example : readBit (GateCode.classicalRun (Reversible.codes 1 3 [(.or, [0, 0]), (.and, [0, 7])])
    (fun i : Fin 4 => decide (i = 0))) 2 = false := by decide

-- The compiled exclusive or accepts `10` with certainty and rejects `11` with certainty.
example : acceptProb (2 + xorGates.length + 1) (Reversible.circuitCodes 2 (xorGates, [5]))
    [true, false] = 1 := by
  have h : evalOutput [true, false] xorGates 5 = true := by decide
  exact (Reversible.acceptProb_circuitCodes (n := 2) (xorGates, [5]) rfl).trans (ite_eq_left h)
example : acceptProb (2 + xorGates.length + 1) (Reversible.circuitCodes 2 (xorGates, [5]))
    [true, true] = 0 := by
  have h : ¬evalOutput [true, true] xorGates 5 = true := by decide
  exact (Reversible.acceptProb_circuitCodes (n := 2) (xorGates, [5]) rfl).trans (ite_eq_right h)

/-- The circuit value problem is in `BQP`. -/
example : CircuitValue ∈ BQP encCircuitValue := P_subset_BQP CircuitValue.mem_P

end ComplexityTests.BQPClassical
