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
open Turing.MultiTapeTM

-- One uniform constructor handles every identity cube, including the zero-dimensional cube.
example : ∃ code : ℕ → CircuitCode,
    ComputableInPolyTime code encUnary encCode ∧
      ∀ n u, u.length = n → evalCircuitOutputs (code n) u = u :=
  exists_uniformCircuitCodes .id' .id' (.snd encUnary encBits) (fun _ _ h => h)

private def neighbor (_ : Bool × List Bool) : List Bool := [false]

private def cost (p : Bool × List Bool) : ℕ := if p.2.headD false then 17 else 3

private theorem neighbor_polytime :
    ComputableInPolyTime neighbor (encPair encBool encBits) encBits := .const _

private theorem cost_polytime :
    ComputableInPolyTime cost (encPair encBool encBits) encNat := by
  unfold cost
  fun_prop

/-- A one-bit local-search family can have costs requiring five bits. -/
theorem wideCostFamily_mem_PLS : localOptRel (fun _ : Bool => 1) neighbor cost ∈ PLS encBool :=
  localOptRel_mem_PLS (.const 1) neighbor_polytime cost_polytime (by simp [neighbor])

/-- The reduction preserves this family without restricting costs to the vertex width. -/
theorem wideCostFamily_reduces :
    SearchReducible encBool encLocalOpt (localOptRel (fun _ : Bool => 1) neighbor cost) LocalOpt :=
  localOptRel_searchReducible_LocalOpt (.const 1) neighbor_polytime cost_polytime
    (by simp [neighbor])

-- Each canonical search problem reduces concrete 1-bit instances of its defining principle.
example : SearchReducible encBool encLocalOpt
    (localOptRel (fun _ : Bool => 1) neighbor (fun _ => 0)) LocalOpt :=
  LocalOpt_searchComplete.2 encBool _
    (localOptRel_mem_PLS (.const 1) neighbor_polytime (.const 0) (by simp [neighbor]))

example : SearchReducible encBool encPigeon
    (pigeonRel (fun _ : Bool => 1) neighbor) Pigeon :=
  Pigeon_searchComplete.2 encBool _
    (pigeonRel_mem_PPP (.const 1) neighbor_polytime (by simp [neighbor]))

example : SearchReducible encBool encEndOfLine
    (endOfLineRel (fun _ : Bool => 1) neighbor neighbor) EndOfLine :=
  EndOfLine_searchComplete.2 encBool _
    (endOfLineRel_mem_PPAD (.const 1) neighbor_polytime neighbor_polytime
      (by simp [neighbor]) (by simp [neighbor]))

example : SearchReducible encBool encLeaf
    (leafRel (fun _ : Bool => 1) neighbor neighbor) Leaf :=
  Leaf_searchComplete.2 encBool _
    (leafRel_mem_PPA (.const 1) neighbor_polytime neighbor_polytime
      (by simp [neighbor]) (by simp [neighbor]))

example : localOptRel (fun _ : Bool => 1) neighbor cost false [false] := by
  simp [localOptRel, neighbor, cost]
example : ¬localOptRel (fun _ : Bool => 1) neighbor cost false [true] := by
  simp [localOptRel, neighbor, cost]
example : binaryWord 5 17 = [true, false, false, false, true] := by decide
example : binaryValue [true, false, false, false, true] = 17 := by decide

-- The finite principles and compiled reductions include empty vertex strings.
example : pigeonRel (fun _ : Bool => 0) (fun p => p.2) false [] := by
  simp [pigeonRel, zeroVertex]
example : endOfLineRel (fun _ : Bool => 0) (fun p => p.2) (fun p => p.2) false [] := by
  simp [endOfLineRel, hasIn, hasOut, zeroVertex]
example : leafRel (fun _ : Bool => 0) (fun p => p.2) (fun p => p.2) false [] := by
  simp [leafRel, hasOddDegree, undirectedEdge, zeroVertex]

end ComplexityTests.TFNPCompleteness
