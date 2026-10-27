/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceSemantics

/-! Regression tests for `BoundedIncidenceSemantics`. -/

namespace ComplexityTests.BoundedIncidenceSemantics

open Cslib Cslib.Complexity Cslib.GenericRAM Cslib.LinearAlgebra
open Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

private def validEmpty : BranchEvalInput := ((16, 0), (1, 1, 16, 1), (2, 2, 1, 1), [])
private def validSingleVar : BranchEvalInput := ((16, 1), (2, 1, 17, 1), (2, 2, 1, 1), [[[0]]])
private def invalidSmallN : BranchEvalInput := ((15, 1), (2, 1, 16, 1), (2, 2, 1, 1), [[[0]]])
private def invalidVars : BranchEvalInput := ((16, 1), (2, 1, 17, 1), (2, 2, 1, 1), [[[16]]])
private def invalidNonCanon : BranchEvalInput := ((16, 2), (2, 2, 18, 1), (2, 2, 1, 1), [[[1, 0]]])
private def invalidDeg : BranchEvalInput := ((16, 1), (2, 2, 18, 1), (2, 2, 1, 1), [[[0, 1]]])

example : validBranchEvalParams validEmpty = true ∧ validBranchEvalParams validSingleVar = true ∧
    validBranchEvalParams invalidSmallN = false ∧ validBranchEvalParams invalidVars = false ∧
    validBranchEvalParams invalidNonCanon = false ∧ validBranchEvalParams invalidDeg = false := by
  decide +kernel

private def sampleDesignOk : ReplacementDesignData :=
  { varGroups := [[[0, 2], [1, 3]]], factorGroups := [[0]], incidences := [(0, 0)],
    copyCount := 1, placements := [(0, 0)], measurementMatrix := [[1, 0, -1, 0]],
    groupMeasurementMatrices := [[[[1, -1]], [[0, 0]]]], denom := 2,
    replacementRows := [[[2], [0], [0], [0]]] }

example : validDesignShape 2 2 0 sampleDesignOk = true ∧
    validDesignShape 2 2 0 { sampleDesignOk with varGroups := [[[0, 1, 2, 3, 4], []]] } = false ∧
    validDesignShape 1 2 0
      { sampleDesignOk with measurementMatrix := List.replicate 21 [1, 0] } = false := by
  decide +kernel

example : applyGroupBits 4 [1, 3] [true, false] [false, false, true, true] =
      [false, true, true, false] ∧
    buildBaseAssignment 4 2 [[0, 2], [1, 3]] [[true, false], [false, true]] =
      [true, false, false, true] ∧
    checkRestrictedGroup 4 [true, false, true, false] [0, 2] [true, true] = true ∧
    checkRestrictedGroup 4 [true, false, true, false] [0, 2] [true, false] = false ∧
    buildEqRowTables 2 [[[0]]] sampleDesignOk = [[[[2], [0], [0], [0]], []]] ∧
    groupEquationsAt [[[0]], [[1]], [[0, 1]]] [[0], [1], [0]] [[[[1]]], [[[2]]], [[[3]]]] 0 0 =
      [([[0]], [[[1]]]), ([[0, 1]], [[[3]]])] := by decide +kernel

private def sampleMeasCtx : MeasStepCtx :=
  ((2, 2, 1), (1, 2, 1), (1, 1), ([[0], [1]], [[[1]], [[1]]]),
    ([false, false], [false, false]), [[], []])

example : (measurementStepBody (((0, 0), [1, 0]), (sampleMeasCtx, [[0, 0]]))).2 = [[1, 0]] ∧
    (measurementStepBody (((0, 0), [2, 0]), (sampleMeasCtx, [[0, 0]]))).2 = [[0, 0]] := by
  decide +kernel

private def runTinyPipeline (n' : ℕ) (eqs : List (List (List ℕ))) : ℕ :=
  let k' := 1; let Q := 1; let r := 1; let A₀ := 0; let R := 1
  let ℓ := n' + 1; let q := n'; let J := q + 1
  let aug := withNeutralScopesList (eqs.map equationVars) n'
  let sc := BalancedSchedules.constructBalancedSchedules n' aug.length Q r 3
    (scopeIncidencesList n' aug)
  let d := buildReplacementDesignData n' 1 Q r A₀ R aug sc.1 sc.2
  let tbls := buildEqRowTables n' eqs d; let m := d.measurementMatrix.length
  let nodeJets := (List.range Q).map fun (t : ℕ) =>
    let grpEqs := (List.range r).map fun g => groupEquationsAt eqs d.factorGroups tbls t g
    let subCtx : SubsetStepCtx := ((n', r, m), (r * m, 1), (J, ℓ, k'), ((t : ℤ) + 1, d.denom),
      (d.varGroups.getD t [], d.groupMeasurementMatrices.getD t []), grpEqs)
    (SubsetPairFold.run subsetPairStepBody n' q (subCtx, zeroJet J ℓ)).2
  (CommonCountingAccum.recoverOuterJetSumModPowTwo [1] J ℓ
    (((d.denom ^ k') ^ (2 * ℓ - 1)) ^ eqs.length) nodeJets).toNat

example : runTinyPipeline 1 [] = 2 ∧ runTinyPipeline 1 [[[]]] = 0 ∧
    runTinyPipeline 1 [[[0]]] = 1 := by decide +kernel

example : runTinyPipeline 2 [[[0], [1]], [[0], []]] = 1 ∧
    evalBoundedIncidenceBranch invalidSmallN = 0 ∧
    evalBoundedIncidenceBranch invalidVars = 0 ∧ evalBoundedIncidenceBranch invalidNonCanon = 0 ∧
    evalBoundedIncidenceBranch invalidDeg = 0 := by decide +kernel

example : evalBoundedIncidenceBranch validSingleVar ≤ 65536 ∧
    evalBoundedIncidenceBranch invalidSmallN ≤ 32768 :=
  ⟨(evalBoundedIncidenceBranch_le_two_pow validSingleVar).trans_eq (by decide +kernel),
   (evalBoundedIncidenceBranch_le_two_pow invalidSmallN).trans_eq (by decide +kernel)⟩

end ComplexityTests.BoundedIncidenceSemantics
