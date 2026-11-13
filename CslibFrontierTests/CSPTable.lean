/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import CslibFrontier.Computability.PolyTime.CSP.Table

/-!
Behavioral tests for explicit table semantics, local contraction and actual binary encodings.
The instances deliberately include empty/nullary relations, duplicates and malformed inputs.
-/

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Logic.PL.CSP.Table
open Cslib.Complexity Cslib.Complexity.CSP Turing.MultiTapeTM

private def sample : Table :=
  ⟨3, [[false, false, false], [false, false, false], [true, false, true],
    [false, true, true], [true, true, false]]⟩

-- Empty/nullary relations differ, and malformed rows reject even stored assignments.
example : (Table.mk 0 []).wellFormed = true := by decide
example : (Table.mk 0 []).sem [] = false := by decide
example : (Table.mk 0 [[]]).sem [] = true := by decide
example : (Table.mk 0 [[]]).sem [false] = false := by decide
example : (Table.mk 2 [[true]]).sem [true] = false := by decide
example : (Table.mk 2 []).wellFormed = true := by decide

-- A real CSP with explicit tables, repeated variables and ordinary Boolean assignments.
example : CSP.eval Table.sem (fun _ : ℕ => false)
    [⟨Table.mk 2 [[false, false]], [37, 37]⟩] = true := by decide
example : CSP.eval Table.sem (fun _ : ℕ => true)
    [⟨Table.mk 2 [[false, false]], [37, 37]⟩] = false := by decide

-- Zero, one and more than one deviation; duplicates remain duplicated and order is stable.
example : (sample.contract [false, false, false] [0, 1]).rows =
    [[false, false], [false, false], [true, true], [true, true]] := by decide
example : deviations [false, false, false] [false, false, false] [0, 1] = 0 := by decide
example : deviations [false, false, false] [true, false, true] [0, 1] = 1 := by decide
example : deviations [false, false, false] [true, true, false] [0, 1] = 2 := by decide
example : (sample.contract [false, false, false] [0, 1]).sem [false, true] = false := by decide
example : (sample.contract [false, false, false] [0, 1]).arity = 2 := by decide

-- Selection order does not reorder the outside coordinates; malformed selections reject.
example : outsidePositions 4 [2, 0] = [1, 3] := by decide
example : validPositions 3 [0, 0] = false := by decide
example : validPositions 3 [3] = false := by decide
example : (sample.contract [false, false, false] [0, 0]).rows = [] := by decide
example : (sample.contract [false, false, false] [1000000]).rows = [] := by decide
example : (sample.contract [true] [0]).rows = [] := by decide
example : ((Table.mk 2 [[false]]).contract [false] []).rows = [] := by decide
example : (sample.contract [true, true, true] []).rows = [] := by decide

-- All-outside, all-internal and nullary boundaries. Empty selection adds a zero connector.
example : (sample.contract [false, false, false] []).arity = 4 := by decide
example : (sample.contract [false, false, false] [0, 1, 2]).rows =
    [[false], [false]] := by decide
example : ((Table.mk 0 [[]]).contract [] []).rows = [[false]] := by decide
example : ((Table.mk 0 []).contract [] []).rows = [] := by decide

-- Exactly-one at 0/1/3 connectors, with positive and negative assignments.
example : (exactlyOne ([] : List ℕ)).rows = [] := by decide
example : (exactlyOne [1000000]).rows = [[true]] := by decide
example : (exactlyOne [5, 8, 13]).rows =
    [[true, false, false], [false, true, false], [false, false, true]] := by decide
example : (exactlyOne [5, 8, 13]).sem [false, true, false] = true := by decide
example : (exactlyOne [5, 8, 13]).sem [true, true, false] = false := by decide
example : (exactlyOne [5, 8, 13]).sem [false, false, false] = false := by decide
example : (exactlyOne [5, 8, 13]).sem [true] = false := by decide

-- Binary arity and names, with every framing layer charged (not unary name lengths).
example : (encTable (exactlyOne [5, 8, 13])).length = 62 := by decide
example : (encConstraint encTable encNat ⟨exactlyOne [5, 8, 13], [5, 8, 13]⟩).length =
    150 := by
  rw [length_encConstraint_exactlyOne]
  decide
example : (encTable (Table.mk 1024 [])).length = 23 := by decide
example : (encTable sample).length = 100 := by decide
example : (encTable (sample.contract [false, false, false] [0, 1])).length = 57 := by decide

-- Client use of the native certificates does not require a finite relation alphabet.
example : ComputableInPolyTime
    (fun p : Table × List Bool => p.1.sem p.2)
    (encPair encTable (encList encBool)) encBool := computableInPolyTime_tableSem
example : ComputableInPolyTime (exactlyOne (V := ℕ)) (encList encNat) encTable :=
  computableInPolyTime_tableExactlyOne
