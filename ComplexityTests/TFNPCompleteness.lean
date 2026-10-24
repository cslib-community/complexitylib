/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Complexity.Classes.TFNP.Subclasses.Completeness
import Complexity.Tactic.PolyTime

/-! Uniform circuit compilation and total-search completeness, including zero vertex width and
local-search costs whose bit-length exceeds the vertex width. -/

namespace ComplexityTests.TFNPCompleteness

open Cslib.Complexity Cslib.BitString Cslib.Circuits.Boolean
open Turing.MultiTapeTM ComputableTidilyInPolyTime

-- One uniform constructor handles every identity cube, including the zero-dimensional cube.
example : ∃ code : ℕ → CircuitCode,
    ComputableInPolyTime code encUnary encCode ∧
      ∀ n u, u.length = n → evalCircuitOutputs (code n) u = u :=
  exists_uniformCircuitCodes (.of_tidy id') (.of_tidy id') (.of_tidy (snd encUnary encBits))
    (fun _ _ h => h)

-- Each canonical search problem has the advertised class and reduction quantifiers.
example : SearchComplete @PPP encPigeon Pigeon := Pigeon_searchComplete
example : SearchComplete @PPAD encEndOfLine EndOfLine := EndOfLine_searchComplete
example : SearchComplete @PPA encLeaf Leaf := Leaf_searchComplete
example : SearchComplete @PLS encLocalOpt LocalOpt := LocalOpt_searchComplete

private def neighbor (_ : Bool × List Bool) : List Bool := [false]

private def cost (p : Bool × List Bool) : ℕ := if p.2.headD false then 17 else 3

private theorem neighbor_polytime :
    ComputableTidilyInPolyTime neighbor (encPair encBool encBits) encBits := const _

private theorem cost_polytime :
    ComputableTidilyInPolyTime cost (encPair encBool encBits) encNat := by
  unfold cost
  polytime

/-- A one-bit local-search family can have costs requiring five bits. -/
theorem wideCostFamily_mem_PLS : localOptRel (fun _ : Bool => 1) neighbor cost ∈ PLS encBool :=
  localOptRel_mem_PLS (.of_tidy (const 1)) (.of_tidy neighbor_polytime) (.of_tidy cost_polytime)
    (by simp [neighbor])

/-- The reduction preserves this family without restricting costs to the vertex width. -/
theorem wideCostFamily_reduces :
    SearchReducible encBool encLocalOpt (localOptRel (fun _ : Bool => 1) neighbor cost) LocalOpt :=
  localOptRel_searchReducible_LocalOpt (.of_tidy (const 1)) (.of_tidy neighbor_polytime)
    (.of_tidy cost_polytime)
    (by simp [neighbor])

example : localOptRel (fun _ : Bool => 1) neighbor cost false [false] := by
  simp [localOptRel, neighbor, cost]
example : ¬localOptRel (fun _ : Bool => 1) neighbor cost false [true] := by
  simp [localOptRel, neighbor, cost]
example : binaryWord 5 17 = [true, false, false, false, true] := by decide
example : binaryValue (binaryWord 5 17) = 17 := binaryValue_binaryWord _ _

-- The finite principles and compiled reductions include empty vertex strings.
example : pigeonRel (fun _ : Bool => 0) (fun p => p.2) false [] := by
  simp [pigeonRel, zeroVertex]
example : endOfLineRel (fun _ : Bool => 0) (fun p => p.2) (fun p => p.2) false [] := by
  simp [endOfLineRel, hasIn, hasOut, zeroVertex]
example : leafRel (fun _ : Bool => 0) (fun p => p.2) (fun p => p.2) false [] := by
  simp [leafRel, hasOddDegree, undirectedEdge, zeroVertex]

/-- info: 'Cslib.Complexity.Pigeon_searchComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.Pigeon_searchComplete

/-- info: 'Cslib.Complexity.EndOfLine_searchComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.EndOfLine_searchComplete

/-- info: 'Cslib.Complexity.Leaf_searchComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.Leaf_searchComplete

/-- info: 'Cslib.Complexity.LocalOpt_searchComplete' depends on axioms:
[propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms Cslib.Complexity.LocalOpt_searchComplete

end ComplexityTests.TFNPCompleteness
