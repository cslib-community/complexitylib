/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

public import CslibFrontier.Computability.Circuit.Quantum.Reversible.Resources
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary

/-!
# Ordinary-module clients of reversible compiler costs

A natively generated circuit negates the first input bit. The empty input reads the existing
false default. The tests also check output relocation, an invalid output index, and the zero-gate
edge. This module imports the compiler without importing the complexity class `BQP`.
-/

public section

namespace CslibFrontierTests.ReversibleCompilerResources

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Cslib.Quantum Turing.MultiTapeTM

/-- A uniform nonconstant family, built with the actual reversible Boolean compiler. -/
def negation : UniformCircuitFamily where
  width n := n + 2
  gates n := Reversible.circuitCodes n ([⟨.not, [0]⟩], [n])
  computableInPolyTime_width := by fun_prop
  computableInPolyTime_gates := Reversible.computableInPolyTime_circuitCodes
    (by fun_prop) (by fun_prop)
  le_width n := by omega
  width_pos n := by omega
  wellFormed n g hg := by
    simpa using (Reversible.isClassical_circuitCodes n ([⟨.not, [0]⟩], [n]) g hg).2

example (n : ℕ) : (negation.gates n).length = 2 + if n = 0 then 0 else 3 := by
  simp [negation, Reversible.length_circuitCodes, Reversible.codes,
    Reversible.gateCodes, Reversible.outQubit]

example (n : ℕ) : (encList encGateCode (negation.gates n)).length ≤
    6 * (12 * (n + 2) + 1) := by
  simpa [negation] using Reversible.length_encoding_circuitCodes_le n ([⟨.not, [0]⟩], [n])

example (n : ℕ) : OracleCircuit.Within
    ((negation.gates n).map fun g => OracleGateCode.gate (false, g))
    (n + 2) ⟨n + 2, 6, 0⟩ := by
  simpa [negation] using Reversible.within_circuitCodes n ([⟨.not, [0]⟩], [n])

-- Embedding into the oracle instruction language preserves execution for every supplied oracle.
example {a b : ℕ} (H : (Fin a → Bool) → Fin b → Bool) (n : ℕ) :
    OracleCircuit.toCircuit (n + 2) H
      ((negation.gates n).map fun g => OracleGateCode.gate (false, g)) =
      Quantum.Circuit.ofCodes (n + 2) (negation.gates n) := by
  simpa only [List.map_map, Function.comp_def] using
    (OracleCircuit.toCircuit_map_gate (m := n + 2) H
      ((negation.gates n).map fun g => (false, g))).trans
        (Quantum.Circuit.ofPhaseCodes_map (negation.gates n))

example : negation.acceptProb [false] = 1 := by
  change acceptProb (1 + 1 + 1) (Reversible.circuitCodes 1 ([⟨.not, [0]⟩], [1])) [false] = 1
  exact Reversible.acceptProb_circuitCodes (n := 1) ([⟨.not, [0]⟩], [1]) rfl

example : negation.acceptProb [true] = 0 := by
  change acceptProb (1 + 1 + 1) (Reversible.circuitCodes 1 ([⟨.not, [0]⟩], [1])) [true] = 0
  exact Reversible.acceptProb_circuitCodes (n := 1) ([⟨.not, [0]⟩], [1]) rfl

example : negation.acceptProb [] = 1 := by
  change acceptProb (0 + 1 + 1) (Reversible.circuitCodes 0 ([⟨.not, [0]⟩], [0])) [] = 1
  exact Reversible.acceptProb_circuitCodes (n := 0) ([⟨.not, [0]⟩], [0]) rfl

-- Exact encoding cost, including target/control and instruction framing.
example : (encList encGateCode (negation.gates 1)).length = 73 := by decide

example : Reversible.circuitCodes 0 ([], []) = [] := by decide
example : (encList encGateCode (Reversible.circuitCodes 0 ([], []))).length = 0 := by decide
example : acceptProb 1 (Reversible.circuitCodes 0 ([], [])) [] = 0 := by
  exact Reversible.acceptProb_circuitCodes (n := 0) ([], []) rfl

-- An invalid output is read from the zero wire; the relocation gates still cost three.
example : (Reversible.circuitCodes 1 ([⟨.not, [100]⟩], [99])).length = 5 := by decide
example : acceptProb 3 (Reversible.circuitCodes 1 ([⟨.not, [100]⟩], [99])) [true] = 0 := by
  exact Reversible.acceptProb_circuitCodes (n := 1) ([⟨.not, [100]⟩], [99]) rfl

end CslibFrontierTests.ReversibleCompilerResources
