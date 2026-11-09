/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.FineGrained.ContractionCircuitCounting

/-! # Counting satisfying inputs of circuits by tensor contraction: checked instances

A De Morgan circuit with fan-out, an unreachable gate and an unread input: its count, the
density of its compiled formula, and instances of the counters. -/

namespace ComplexityTests.ContractionCircuitCounting

open Cslib.Circuits Cslib.Circuits.Frontier Cslib.Complexity Cslib.Complexity.ContractionCounting
  Cslib.Logic.PL Turing.MultiTapeTM

/-- `(x₀ ∧ x₁) ∨ ¬x₂` on four inputs: gate `0` is `x₀ ∧ x₁`, gate `1` is `¬x₂`, gate `2` (the
output) is their disjunction, and gate `3`, `x₀ ∧ x₂`, is unreachable. Input `3` is unread. -/
def sample : Circuit Boolean.signature 4 1 :=
  ⟨(((Program.empty.gate ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 1]⟩).gate
      ⟨Boolean.Op.not, ![Wire.input 2]⟩).gate
      ⟨Boolean.Op.or, ![Wire.gate 0, Wire.gate 1]⟩).gate
      ⟨Boolean.Op.and, ![Wire.input 0, Wire.input 2]⟩,
    fun _ => Wire.gate 2⟩

-- Five of the eight assignments to `x₀, x₁, x₂` satisfy it, and input `3` is free.
example : sample.size = 4 ∧ sample.satCount Boolean.interpretation = 10 := by decide

-- The compiled formula keeps the three reachable gates: `4 + 2 + 4` gate clauses and one output
-- clause on the six reachable wires, within the density bound `2 ^ 3 * (6 + 1)`.
example : (Compiler.toSatCNF sample Boolean.interpretation).length = 11 ∧
    (Compiler.toSatCNF sample Boolean.interpretation).numVars = 6 ∧
    Compiler.reachGateCountCode 4 sample.code = 3 ∧
    Compiler.satFreeShift sample Boolean.interpretation = 1 := by decide

example : (Compiler.toSatCNF sample Boolean.interpretation).length ≤
    2 ^ (2 + 1) * ((Compiler.toSatCNF sample Boolean.interpretation).numVars + 1) :=
  Compiler.length_toCNF_le_numVars _ _ sample.fanInAtMost_two

-- The counter, on `sample`.
example : ∃ (count : (Σ n, Circuit Boolean.signature n 1) → ℕ) (A e b : ℕ),
    count ⟨4, sample⟩ = 10 ∧
    ComputableInO count (Boolean.encCircuit 1) encNat
      (fun c => 2 ^ (A * (c.2.size + 1) / Nat.sqrt (Nat.log 2 (c.2.size + 2))) *
        ((Boolean.encCircuit 1 c).length + 1) ^ e)
      (fun c => ((Boolean.encCircuit 1 c).length + 1) ^ b) := by
  obtain ⟨count, A, e, b, hspec, hinO⟩ := exists_booleanCircuitSatCounter
  exact ⟨count, A, e, b, by rw [hspec]; decide, hinO⟩

-- The linear-size form applies to `sample`, which has `4 ≤ 1 * 4 + 1` gates.
example : ∃ (count T : (Σ n, Circuit Boolean.signature n 1) → ℕ) (e A : ℕ),
    count ⟨4, sample⟩ = 10 ∧
    T ⟨4, sample⟩ ≤ 2 ^ (A * (4 + 1) / Nat.sqrt (Nat.log 2 (4 + 2))) *
      ((Boolean.encCircuit 1 ⟨4, sample⟩).length + 1) ^ e := by
  obtain ⟨count, T, S, e, b, hspec, -, -, hT⟩ := exists_linearSizeBooleanCircuitSatCounter
  obtain ⟨A, hA⟩ := hT 1
  exact ⟨count, T, e, A, by rw [hspec]; decide, hA ⟨4, sample⟩ (by decide)⟩

end ComplexityTests.ContractionCircuitCounting
