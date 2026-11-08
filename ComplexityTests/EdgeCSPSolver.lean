/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

import Complexity.Computability.PolyTime.CSP.Edge.Solver.Endpoint
import Complexity.Computability.PolyTime.CSP.Edge.Solver.GuardPolyTime

/-! Execute the actual whole-instance solver, including nonempty blossom preparation,
contraction without variable decrease, repeated original constraints, sparse binary names,
multiple outer improvements and every raw model guard. -/

namespace ComplexityTests.EdgeCSPSolver

open Cslib.Logic.PL Cslib.Logic.PL.CSP Cslib.Complexity.CSP
open EdgeSolver
open Cslib.Complexity (encCSP)

private def equality : Table := ⟨2, [[false, false], [true, true]]⟩
private def equalityTrueFirst : Table := ⟨2, [[true, true], [false, false]]⟩
private def inequality : Table := ⟨2, [[false, true], [true, false]]⟩
private def unit (b : Bool) : Table := ⟨1, [[b]]⟩
private def starTable : Table :=
  ⟨3, [[false, false, false], [true, true, false], [true, false, true]]⟩

-- Every model test is an ordinary native machine certificate on the complete raw encoding.
example : Turing.MultiTapeTM.ComputableInPolyTime checkModel
    (encCSP encTable Turing.MultiTapeTM.encNat) Turing.MultiTapeTM.encBool := by fun_prop

example : Program.decideSAT [] = true := by decide
example : Program.optimize [] = some [] := by decide
example : Program.decideSAT [(⟨0, [[]]⟩, [])] = true := by decide
example : Program.decideSAT [(⟨0, [[], []]⟩, [])] = true := by decide
example : Program.decideSAT [(⟨0, []⟩, [])] = false := by decide
example : Program.decideSAT [(⟨0, [[true]]⟩, [])] = false := by decide
example : Program.decideSAT [(⟨2 ^ 250, [[]]⟩, [])] = false := by decide +kernel

-- Two odd singleton relations disagree on their common edge: an unavoidable odd defect.
example : Program.decideSAT [(unit false, [0]), (unit true, [0])] = false := by decide
example : Program.decideSAT [(unit true, [0]), (unit true, [0])] = true := by decide

-- Duplicate constraints and duplicate rows retain their positional semantics.
example : Program.decideSAT [(⟨2, [[false, false], [false, false], [true, true]]⟩, [0, 1]),
    (equality, [0, 1])] = true := by decide
example : Program.decideSAT [(equality, [0, 0])] = false := by decide
example : Program.decideSAT [(unit false, [0])] = false := by decide
example : Program.decideSAT [(⟨1, [[false], [true]]⟩, [0]),
    (unit false, [0])] = false := by decide
example : checkConstraint (⟨4, [[false, false, false, false], [true, true, true, true]]⟩,
    [0, 1, 2, 3]) = false := by decide

private def multiple : CSP Table ℕ :=
  [(equality, [0, 1]), (equalityTrueFirst, [0, 1]),
    (equality, [2, 3]), (equalityTrueFirst, [2, 3])]

-- The first improvement leaves two defects; the second removes them. Both are run by
-- the original optimization loop, without recursively optimizing any contracted child.
example : Program.improve ⟨multiple,
    [false, false, true, true, false, false, true, true]⟩ =
    some [true, true, true, true, false, false, true, true] := by decide +kernel
example : Program.optimize multiple =
    some [true, true, true, true, true, true, true, true] := by decide +kernel
example : Program.decideSAT multiple = true := by decide +kernel

private abbrev a : ℕ := 2 ^ 100
private abbrev b : ℕ := 2 ^ 200
private abbrev c : ℕ := 2 ^ 250
private def star : CSP Table ℕ :=
  [(starTable, [a, b, c]), (equality, [b, c]), (unit true, [a])]

private def descend (input : EdgeForest.Input) : Option (Program.Frame × EdgeForest.Input) := do
  let .inr (.inr event) ← EdgeForest.run input | none
  Program.push input event

-- Verify that the real first search pushes a blossom, changes the prepared buffer and
-- retains the number of variables while appending exactly one original constraint.
example : ((descend ⟨star, [false, false, false, false, false, true]⟩).map fun (frame, child) =>
    (frame.parent.labels != [false, false, false, false, false, true]) &&
      (child.body.vars.eraseDups.length == star.vars.eraseDups.length) &&
      (child.body.length == star.length + 1)) = some true := by decide +kernel

-- Actual copied-constraint LCA, with a nonempty preparatory flip and r=b contraction.
example : Program.improve ⟨star, [false, false, false, false, false, true]⟩ = none := by
  decide +kernel
example : Program.decideSAT star = false := by decide +kernel

private def outside : CSP Table ℕ :=
  [(starTable, [a, b, c]), (equality, [b, c]),
    (equality, [a, 2 ^ 120]), (unit false, [2 ^ 120])]

-- A child comparison changes the surviving outside equality row. The lift executes the
-- native comparison-to-augmentation run and then the actual nonempty-prefix blossom lift.
example : Program.lift
    ⟨⟨outside, [true, true, false, false, false, true, true, false]⟩,
      ⟨b, [(3, 4), (2, 1)]⟩⟩
    [false, true, false, false, false, false, true, false] =
      some (List.replicate 8 false) := by decide +kernel

example : (descend
    ⟨outside, [true, true, false, false, false, true, true, false]⟩).isSome = true := by
  decide +kernel

-- The full one-improvement call really descends through that blossom and returns the lift.
example : Program.improve
    ⟨outside, [true, true, false, false, false, true, true, false]⟩ =
      some (List.replicate 8 false) := by decide +kernel

example : Program.improve ⟨multiple, [false]⟩ = none := by decide

private def triangle : CSP Table ℕ :=
  [(inequality, [0, 1]), (equality, [1, 2]), (equality, [2, 0])]
example : Program.decideSAT triangle = false := by decide +kernel

private def repeated : CSP Table ℕ :=
  [(⟨4, [[false, false, false, false], [true, true, false, false],
      [false, false, true, true], [true, true, true, true]]⟩, [0, 1, 2, 3]),
    (equality, [1, 2]), (inequality, [3, 0])]

example : ((descend
    ⟨repeated, [false, false, false, false, false, false, false, true]⟩).map fun (frame, _) =>
      decide (((frame.cycle.steps.map fun step =>
        (EdgeAugmenting.recordAt repeated step.1).1).count 0) ≥ 2)) = some true := by
  decide +kernel

-- The real cycle touches original constraint zero at two distinct copied times.
example : Program.improve ⟨repeated, [false, false, false, false, false, false, false, true]⟩ =
    none := by decide +kernel
example : Program.decideSAT repeated = false := by decide +kernel

-- The mathematical optimizer is fully proved for every accepted model, independently of
-- these executable regressions. This is the existing CSP semantics and original encoding.
example (F : CSP Table ℕ) (h : checkModel F = true) :
    ∃ bits, EdgeSolver.optimize F = some bits ∧
      IsOptimalLabeling Table.sem (EdgeAugmenting.labeling F bits) := optimize_spec F h

-- Ordinary imports expose the existing original lookup/endpoint facts, not duplicate bridges.
example {F : CSP Table ℕ} (o : Occurrence F) :
    EdgeAugmenting.recordAt F (EdgeAugmenting.occurrenceIndex o) = o.record :=
  EdgeAugmenting.recordAt_index o
example {F : CSP Table ℕ} (w : Walk F) :
    EdgeAugmenting.finish ⟨F, [], [], 0⟩ (EdgeAugmenting.code w) = w.finish :=
  EdgeAugmenting.finish_eq (⟨F, [], [], 0⟩ : EdgeAugmenting.Input) w
example : EdgeAugmenting.recordAt [] (2 ^ 250) = (0, 0, 0) := by decide +kernel
example : EdgeAugmenting.finish ⟨[], [], [], 0⟩ ⟨123, []⟩ = 123 := by decide

example : Program.safeImprove ⟨multiple, [false]⟩ = none := by decide
example : Program.safeImprove
    ⟨multiple, [false, true, false, false, false, false, false, false]⟩ = none := by decide
example : Program.safeImprove ⟨multiple, List.replicate 8 false⟩ = none := by decide +kernel
example : Program.safeImprove ⟨[(⟨2 ^ 250, [[]]⟩, [])], []⟩ = none := by decide +kernel
example : Program.safeImprove ⟨[], []⟩ = none := by decide

-- Complete ordinary native certificates have no input-validity runtime premise.
example : evenEdgeSAT ∈ Cslib.Complexity.P (encCSP encTable Turing.MultiTapeTM.encNat) :=
  evenEdgeSAT_mem_P
example : Turing.MultiTapeTM.ComputableInPolyTime EdgeSolver.optimize
    (encCSP encTable Turing.MultiTapeTM.encNat)
    (Turing.MultiTapeTM.encOption (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBool)) :=
  EdgeSolver.computableInPolyTime_optimize
example : Turing.MultiTapeTM.ComputableInPolyTime EdgeSolver.solve
    (encCSP encTable Turing.MultiTapeTM.encNat)
    (Turing.MultiTapeTM.encOption (Turing.MultiTapeTM.encList Turing.MultiTapeTM.encBool)) :=
  EdgeSolver.computableInPolyTime_solve
example (F : CSP Table ℕ) : decideSAT F = true ↔ F ∈ evenEdgeSAT := decideSAT_eq_true_full F

end ComplexityTests.EdgeCSPSolver
