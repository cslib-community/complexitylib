/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

-- upstream: local-only (formal abstract tests)

import ComplexityAbstracts.PartialMCSPAbstract

/-! # Concrete clients and non-vacuity checks for the Partial MCSP formal abstract

Verifies that `ThreeSAT`, `numVars`, and `ETH` in `PartialMCSPAbstract` match the library's native
definitions, tests `Instance`, `AgreesWith`, `PartialMCSP`, and `PartialMCSPBinaryGate` on concrete
small circuits and partial truth tables, and exhibits a concrete `1`-variable negation instance
that separates `PartialMCSP` (all-gates size `0`) from `PartialMCSPBinaryGate` (binary-gate count
`0`).
-/

namespace ComplexityTests.Abstracts.PartialMCSPTests

open ComplexityAbstracts.PartialMCSPAbstract

-- The public 3SAT, variable-count, and ETH definitions match the library's native definitions.
example : ThreeSAT = Cslib.Complexity.ThreeSAT :=
  ComplexityAbstracts.PartialMCSPBridge.threeSAT_eq

example : numVars = Cslib.Logic.PL.CNF.numVars (V := ℕ) :=
  rfl

example : ETH ↔ Cslib.Complexity.ETH :=
  ComplexityAbstracts.PartialMCSPBridge.eth_iff

-- Concrete checks of `numVars` and `ThreeSAT` on a 2-clause 3-CNF formula `(x₀ ∨ ¬x₁) ∧ (x₁ ∨ x₂)`.
def sampleFormula : Formula :=
  [[(0, true), (1, false)], [(1, true), (2, true)]]

example : numVars sampleFormula = 3 := by decide

example : sampleFormula ∈ ThreeSAT := by
  refine ⟨by decide, fun _ => true, ?_⟩
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact ⟨(0, true), List.Mem.head _, rfl⟩
  · rcases List.mem_singleton.mp hc with rfl
    exact ⟨(1, true), List.Mem.head _, rfl⟩

-- An all-`none` (`*`) partial truth table of arity 1 is satisfied by a 0-gate wire circuit.
abbrev allStarInstance : Instance where
  arity := 1
  table := fun _ => none
  threshold := 0

example : tableSize allStarInstance = 2 := rfl

example : allStarInstance ∈ PartialMCSP := by
  refine ⟨Cslib.Circuits.Circuit.wiring Cslib.Circuits.Boolean.signature (fun _ => 0), le_rfl, ?_⟩
  intro _ _ h
  cases h

-- A 1-gate NOT circuit has all-gates size 1 and binary-gate count 0.
def notCircuit : DeMorganCircuit 1 where
  size := 1
  program := .gate .empty ⟨.not, fun _ => .input 0⟩
  outputs _ := .gate 0

example : notCircuit.size = 1 := rfl

example : binaryGateCount notCircuit = 0 := rfl

-- The 1-variable negation table `0 ↦ 1, 1 ↦ 0` at threshold 0 belongs to `PartialMCSPBinaryGate`
-- (since NOT gates are free in `binaryGateCount`) and to `PartialMCSP` at threshold 1.
abbrev negationInstance (s : ℕ) : Instance where
  arity := 1
  table := ![some true, some false]
  threshold := s

theorem agreesWith_negationInstance (s : ℕ) :
    AgreesWith (negationInstance s) notCircuit := by
  intro y b hy
  have hy_cases : y = (fun _ => false) ∨ y = (fun _ => true) := by
    cases h0 : y 0
    · left; ext i; rw [Subsingleton.elim i 0, h0]
    · right; ext i; rw [Subsingleton.elim i 0, h0]
  rcases hy_cases with rfl | rfl
  · have hb : some true = some b := hy
    cases hb
    rfl
  · have hb : some false = some b := hy
    cases hb
    rfl

example : negationInstance 0 ∈ PartialMCSPBinaryGate :=
  ⟨notCircuit, le_rfl, agreesWith_negationInstance 0⟩

example : negationInstance 1 ∈ PartialMCSP :=
  ⟨notCircuit, le_rfl, agreesWith_negationInstance 1⟩

end ComplexityTests.Abstracts.PartialMCSPTests
