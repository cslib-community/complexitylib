/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Protocols.PolynomialCommitment.Basic
import Mathlib.Algebra.Field.ZMod
import Mathlib.Tactic.NormNum.Prime

/-!
# Tests for polynomial commitment schemes, evaluation batching, and the Ligero matrix-code IOP core

Exercises `PolyCommitScheme`, random-linear-combination evaluation batching (`batchEvalReduction`,
`toOuterMeasure_batchEval_eq`), and the Ligero matrix-code IOP core (`ligeroRowComb`,
`ligeroColumnCheck`, `ligeroEvalCheck`, `LigeroMatrixIOP`) over `ZMod 5` and `ZMod 7`.
-/

namespace CslibFrontierTests.Crypto.PolynomialCommitment

open Cslib Cslib.Crypto.Protocols Cslib.Interactive Cslib.Probability
open scoped BigOperators ENNReal Matrix

instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩
instance : Fact (Nat.Prime 7) := ⟨by norm_num⟩

/-! ### Interface and theorem signature checks -/

example := @PolyCommitScheme
example := @PolyCommitScheme.EvalComplete
example := @PolyCommitScheme.CommitmentBinding
example := @PolyCommitScheme.EvaluationBinding
example := @PolyCommitScheme.EvaluationBinding.eq_eval_of_verifyEval
example := @PolyCommitScheme.EvaluationBinding.commitmentBinding_of_eval_inj
example := @uniformOfFintype_map_linearComb
example := @toOuterMeasure_batchEval_sub_eq_zero
example := @toOuterMeasure_batchEval_eq
noncomputable example := @batchEvalReduction
noncomputable example := @batchEvalReduction_complete
noncomputable example := @batchEvalReduction_rbrSound
noncomputable example := @batchEvalReduction_sound
example := @ligeroRowComb
example := @ligeroRowComb_mul
example := @ligeroEval
example := @ligeroColumnCheck
example := @ligeroEvalCheck
example := @toOuterMeasure_ligeroRowComb_eq
example := @LigeroMatrixIOP.columnReduction_complete
example := @LigeroMatrixIOP.columnReduction_sound

/-! ### Concrete `PolyCommitScheme` tests over `ZMod 5` and `ZMod 7` -/

example : (PolyCommitScheme.direct (ZMod 5) 2).EvalComplete :=
  PolyCommitScheme.direct_evalComplete (ZMod 5) 2

example : (PolyCommitScheme.direct (ZMod 7) 3).CommitmentBinding :=
  PolyCommitScheme.direct_commitmentBinding (ZMod 7) 3

example : (PolyCommitScheme.direct (ZMod 7) 3).EvaluationBinding :=
  PolyCommitScheme.direct_evaluationBinding (ZMod 7) 3

/-- A concrete linear polynomial `2 * X + 1` over `ZMod 5` opens and verifies at `z = 3` (giving
`2 * 3 + 1 = 7 = 2 : ZMod 5`), while a wrong value `y = 4` is rejected. -/
example :
    let S := PolyCommitScheme.direct (ZMod 5) 2
    let p : Polynomial (ZMod 5) := Polynomial.C 2 * Polynomial.X + Polynomial.C 1
    S.verifyEval (S.commit p ()) 3 (S.eval p 3) (S.openEval p () 3).2 = true ∧
      S.verifyEval (S.commit p ()) 3 4 () = false := by
  refine ⟨?_, ?_⟩
  · apply PolyCommitScheme.direct_evalComplete (ZMod 5) 2
    refine (Polynomial.natDegree_add_le _ _).trans (max_le ?_ (by simp))
    exact (Polynomial.natDegree_C_mul_le _ _).trans (by simp)
  · simp only [PolyCommitScheme.direct, decide_eq_false_iff_not, not_and, Polynomial.eval_add,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_X]
    intro _
    decide

/-! ### Concrete evaluation-batching tests over `ZMod 5` and `ZMod 7` -/

/-- Two evaluation functions `Fin 2 → ZMod 5 → ZMod 5` where the first claimed evaluation at `z = 2`
is wrong (`(2 : ZMod 5) ≠ 3`): a uniform linear combination `r : Fin 2 → ZMod 5` agrees with the
false claim with probability *exactly* `1 / 5`. -/
example :
    let eval : (ZMod 5 → ZMod 5) → ZMod 5 → ZMod 5 := fun f z => f z
    let p : Fin 2 → (ZMod 5 → ZMod 5) := ![fun z => z, fun z => z + 1]
    let y : Fin 2 → ZMod 5 := ![3, 3]
    (PMF.uniformOfFintype (Fin 2 → ZMod 5)).toOuterMeasure
        {r | ∑ i : Fin 2, r i * eval (p i) 2 = ∑ i : Fin 2, r i * y i} =
      1 / 5 := by
  intro eval p y
  have hne : eval (p 0) 2 ≠ y 0 := by decide
  have h := toOuterMeasure_batchEval_eq eval p 2 y hne
  simpa [ZMod.card] using h

/-- Over `ZMod 7`, batching 3 evaluation claims is perfectly complete and `1 / 7`-sound. -/
example (eval : (ZMod 7 → ZMod 7) → ZMod 7 → ZMod 7) (p : Fin 3 → (ZMod 7 → ZMod 7))
    (z : ZMod 7) :
    (batchEvalReduction eval p z).Complete World.plain
        (batchEvalRelIn eval p z) (batchEvalRelOut eval p z) 0 ∧
      (batchEvalReduction eval p z).verifier.Sound (oP := OracleSpec.empty) World.plain
        (language (batchEvalRelIn eval p z)) (language (batchEvalRelOut eval p z)) (1 / 7) := by
  refine ⟨batchEvalReduction_complete eval p z, ?_⟩
  have h := batchEvalReduction_sound eval p z
  simpa [ZMod.card] using h

/-! ### Concrete Ligero matrix-code IOP tests over `ZMod 5` and `ZMod 7` -/

/-- A `2 × 2` witness matrix over `ZMod 5`. -/
def testU : Matrix (Fin 2) (Fin 2) (ZMod 5) := !![1, 2; 3, 4]

/-- A `2 × 3` systematic generator matrix over `ZMod 5`. -/
def testG : Matrix (Fin 2) (Fin 3) (ZMod 5) := !![1, 0, 1; 0, 1, 1]

/-- A challenge vector `r = ![2, 1]` over `ZMod 5`. -/
def testR : Fin 2 → ZMod 5 := ![2, 1]

/-- A column vector `c = ![1, 3]` over `ZMod 5`. -/
def testC : Fin 2 → ZMod 5 := ![1, 3]

-- Concrete verification of `ligeroColumnCheck` and `ligeroEvalCheck` on the honestly encoded matrix
example : ∀ j : Fin 3,
    ligeroColumnCheck testG (testU * testG) testR (ligeroRowComb testR testU) j = true := by
  decide

example : ∀ j : Fin 3,
    ligeroEvalCheck testG (testU * testG) testR testC (ligeroEval testU testR testC)
      (ligeroRowComb testR testU) j = true := by
  decide

/-- Corrupting entry `(0, 0)` of `testU * testG` over `ZMod 5` is caught at column `0` by a uniform
challenge `r : Fin 2 → ZMod 5` except with probability *exactly* `1 / 5`. -/
def badM : Matrix (Fin 2) (Fin 3) (ZMod 5) :=
  Matrix.of fun i j => if i = 0 ∧ j = 0 then (testU * testG) 0 0 + 1 else (testU * testG) i j

example :
    (PMF.uniformOfFintype (Fin 2 → ZMod 5)).toOuterMeasure
        {r | (r ᵥ* badM) 0 = (ligeroRowComb r testU ᵥ* testG) 0} =
      1 / 5 := by
  have hne : badM 0 0 ≠ ((testU 0) ᵥ* testG) 0 := by decide
  have h := toOuterMeasure_ligeroRowComb_eq testG badM testU hne
  simpa [ZMod.card] using h

/-- For any Ligero matrix instance over `ZMod 7`, the public-coin column reduction is perfectly
complete and `1 / 7`-sound. -/
example (L : LigeroMatrixIOP (ZMod 7) 2 2 4) :
    L.columnReduction.Complete World.plain L.relIn L.relOut 0 ∧
      L.columnReduction.verifier.Sound (oP := OracleSpec.empty) World.plain
        (language L.relIn) (language L.relOut) (1 / 7) := by
  refine ⟨L.columnReduction_complete, ?_⟩
  have h := L.columnReduction_sound
  simpa [ZMod.card] using h

end CslibFrontierTests.Crypto.PolynomialCommitment
