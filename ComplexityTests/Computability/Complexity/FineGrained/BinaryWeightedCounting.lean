/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.BinaryWeightedCounting

/-!
# Native exact counting with input-supplied weight tables

The relation symbol is itself a list of binary naturals. The checked unary example has weights
five and thirteen, accepts its adequate bit budget, and rejects an inadequate budget. The native
machine certificate uses ordinary polynomial-time table lookup for its local evaluator.
-/

public section

namespace Cslib.Complexity.BinaryWeightedCountingTests

open Cslib.Logic.PL Cslib.Circuits.Frontier Cslib.Circuits.Frontier.ClauseNetwork
  Turing.MultiTapeTM Cslib.GenericRAM BinaryWeightedCounting

/-- One unary relation whose two table entries are part of the input. -/
@[expose] def weightedVariable : CSP (List ℕ) ℕ := [([5, 13], [0])]

private theorem tableWeight_polyTime (w : List Bool) :
    ComputableInPolyTime (fun table : List ℕ => ExplicitTensorNetwork.entry table w)
      (encList encNat) encNat :=
  ComputableInPolyTime.listGetDWithInput ComputableInPolyTime.id'
    (ComputableInPolyTime.const (BitString.lsbValue w)) 0

example : weightedVariable.partitionFunction ExplicitTensorNetwork.entry = 18 := by decide

example : guard 1 16 1 ExplicitTensorNetwork.entry weightedVariable = true := by decide

example : count 1 16 1 ExplicitTensorNetwork.entry weightedVariable = 18 := by
  rw [count_eq (by decide) (by decide)]
  decide

example : count 1 0 1 ExplicitTensorNetwork.entry weightedVariable = 0 := by decide

example : count 1 16 1 ExplicitTensorNetwork.entry ([] : CSP (List ℕ) ℕ) = 1 := count_nil ..

example : count 1 16 1 ExplicitTensorNetwork.entry [([5, 13], [])] = 0 := by decide

-- The supplied local weight certificate produces an ordinary native machine for the input tables.
example : ComputableInO (count 1 16 1 ExplicitTensorNetwork.entry)
    (encCSP (encList encNat) encNat) encNat
    (certificate (encList encNat) 1 16 1 ExplicitTensorNetwork.entry
      (fun w _ => tableWeight_polyTime w)).time
    (certificate (encList encNat) 1 16 1 ExplicitTensorNetwork.entry
      (fun w _ => tableWeight_polyTime w)).space :=
  (certificate (encList encNat) 1 16 1 ExplicitTensorNetwork.entry
    (fun w _ => tableWeight_polyTime w)).computes

-- Per-entry four-bit bounds imply the network's total table-bit budget, with explicit constants.
example : (cspNetwork 1 ExplicitTensorNetwork.entry weightedVariable).2.binaryTableBound ≤
    49 * ((cspNetwork 1 ExplicitTensorNetwork.entry weightedVariable).2.numEdges + 1) ^ 3 := by
  apply binaryTableBound_cspNetwork_le 2 (by decide)
  intro c hc w hw
  have hc' : c = ([5, 13], [0]) := by simpa [weightedVariable] using hc
  subst c
  apply ExplicitTensorNetwork.size_entry_le
  decide

end Cslib.Complexity.BinaryWeightedCountingTests
