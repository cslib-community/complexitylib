/-
Copyright (c) 2026 Anton Kovsharov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anton Kovsharov
-/

import Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert

/-! Regression tests for
`Complexity.Computability.PolyTime.BooleanAnalysis.BoundedIncidenceStepCert`. -/

namespace ComplexityTests.BoundedIncidenceStepCert

open Cslib Cslib.BitString Cslib.LinearAlgebra Turing.MultiTapeTM
open Cslib.Complexity.SubexponentialSAT.SparsePolyCounter

private def sampleDesign : ReplacementDesignData :=
  buildReplacementDesignData 2 1 1 2 1 1 [[0], [1]] [[0], [1]] [[0], [1]]

private def sampleGrpCtx (indE : List Bool) : GroupEvalCtx :=
  ((2, 1, 2, 1), (0, 1), ([0, 1], [[1, 1]], [1]), (indE, [false, false], [false, false]),
    [([[0]], [[[1], [0]], [[0], [1]]])])

private def sampleMeasCtx : MeasStepCtx :=
  ((2, 1, 1), (1, 2, 1), (0, 1), ([[0, 1]], [[[1, 1]]]), ([false, false], [false, false]),
    [[([[0]], [[[1], [0]], [[0], [1]]])]])

private def sampleSubCtx : SubsetStepCtx :=
  ((2, 1, 1), (1, 1), (1, 2, 1), (0, 1), ([[0, 1]], [[[1, 1]]]),
    [[([[0]], [[[1], [0]], [[0], [1]]])]])

example : validBranchEvalParams ((16, 2), (1, 2, 2, 1), (2, 2, 1, 2), [[[0, 1]]]) = true ∧
    validBranchEvalParams ((15, 2), (1, 2, 2, 1), (2, 2, 1, 2), [[[0, 1]]]) = false ∧
    validDesignShape 2 2 1 sampleDesign = true ∧
    validDesignShape 2 2 1 { sampleDesign with varGroups := [[[0, 1, 2, 3, 4]]] } = false ∧
    maxGroupDim 2 2 [[0, 1, 2], [3]] = 3 ∧
    maxGroupDim 1 2 [[0, 1, 2], [3]] = 2 ∧
    maxAllGroupDim 2 2 2 [[[0]], [[0, 1, 2], [3]]] = 3 := by decide +kernel

example : evalGroupFactorJet (sampleGrpCtx [false, false], (2, [false, true])) = [[1, 0]] ∧
    evalGroupFactorJet (sampleGrpCtx [false, false], (2, [true, false])) = [[0, 0]] ∧
    evalGroupFactorJet (sampleGrpCtx [false, true], (2, [true, false])) = [[0, 0]] ∧
    evalGroupFactorJet (sampleGrpCtx [false, false], (2, [false, false])) = [[0, 0]] ∧
    evalMeasPayload ([1], sampleMeasCtx) = some [[1, 0]] ∧
    evalMeasPayload ([3], sampleMeasCtx) = none ∧
    (measurementStepBody (((0, 0), [1]), (sampleMeasCtx, [[5, 7]]))).2 = [[6, 7]] ∧
    (measurementStepBody (((0, 0), [3]), (sampleMeasCtx, [[5, 7]]))).2 = [[5, 7]] ∧
    encGroupEvalCtx (sampleGrpCtx [false, false]) ≠ [] ∧
    encMeasStepCtx sampleMeasCtx ≠ [] ∧
    encSubsetStepCtx sampleSubCtx ≠ [] := by decide +kernel

example (inp : ((ℕ × ℕ) × List ℤ) × (MeasStepCtx × JetRows)) :
    measurementStepBody inp =
      (evalMeasPayload (inp.1.2, inp.2.1)).elim inp.2
        (fun pj => (inp.2.1, addJet inp.2.1.2.1.1 inp.2.1.2.1.2.1 inp.2.2 pj)) :=
  measurementStepBody_eq inp

example : ComputableInPolyTime validBranchEvalParams encBranchEvalInput encBool ∧
    ComputableInPolyTime (fun d : ReplacementDesignData => validDesignShape 2 2 1 d)
      encReplacementDesignData encBool ∧
    ComputableInPolyTime evalGroupFactorJet
      (encPair encGroupEvalCtx (encPair encUnary encBits)) (encList (encList encIntBin)) :=
  ⟨computableInPolyTime_validBranchEvalParams,
   computableInPolyTime_validDesignShape (by fun_prop) (by fun_prop) (by fun_prop) (by fun_prop),
   computableInPolyTime_evalGroupFactorJet⟩

example : ∃ P : List ℤ × MeasStepCtx → ℕ,
    PolyBounded (fun wc => (encPair (encList encIntBin) encMeasStepCtx wc).length) P ∧
    ComputableInO evalMeasPayload (encPair (encList encIntBin) encMeasStepCtx)
      (encOption (encList (encList encIntBin)))
      (fun wc =>
        (wc.2.1.2.1 * (2 ^ maxGroupDim wc.2.1.1 wc.2.1.2.1 wc.2.2.2.2.1.1 + 1) + 1) * P wc) P :=
  exists_computableInO_measPayload

end ComplexityTests.BoundedIncidenceStepCert
