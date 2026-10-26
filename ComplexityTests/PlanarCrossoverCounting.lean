/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Logics.Propositional.CNF.Planar.CrossoverCounting
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! Full satisfying assignments correspond bijectively to the two incoming bits, including
after splitting. The model counts below use these structural equivalences, not enumeration. -/

open Cslib.Logic.PL Cslib.Logic.PL.CNF.Crossover

private def modelsEquivInputs :
    {σ : Variable → Bool // formula.eval σ = true} ≃ Bool × Bool where
  toFun σ := (σ.val .aLeft, σ.val .bTop)
  invFun ab := ⟨canonicalExtension ab.1 ab.2, eval_canonicalExtension ab.1 ab.2⟩
  left_inv σ := Subtype.ext (eq_canonicalExtension_of_holds σ.property).symm
  right_inv _ := rfl

private def splitModelsEquivInputs :
    {σ : SplitVariable → Bool // splitFormula.eval σ = true} ≃ Bool × Bool where
  toFun σ := (σ.val .aLeft, σ.val .bTop)
  invFun ab := ⟨canonicalSplitExtension ab.1 ab.2, eval_canonicalSplitExtension ab.1 ab.2⟩
  left_inv σ := Subtype.ext (eq_canonicalSplitExtension_of_holds σ.property).symm
  right_inv _ := rfl

example : Fintype.card {σ : Variable → Bool // formula.eval σ = true} = 4 := by
  rw [Fintype.card_congr modelsEquivInputs]
  decide

example : Fintype.card {σ : SplitVariable → Bool // splitFormula.eval σ = true} = 4 := by
  rw [Fintype.card_congr splitModelsEquivInputs]
  decide

-- The mixed input has a concrete internal value, common to all six copies.
example (i : Fin 6) : canonicalSplitExtension false true (.copy .upperLeft i) = true := rfl

-- Changing a free-looking internal value cannot produce another satisfying full assignment.
example : splitFormula.eval (Function.update (canonicalSplitExtension false true) .center true) =
    false := by
  cases h : splitFormula.eval
      (Function.update (canonicalSplitExtension false true) .center true) with
  | false => rfl
  | true =>
    have heq := eq_canonicalSplitExtension_of_holds h
    have hcenter := congrFun heq .center
    simp [canonicalSplitExtension, canonicalExtension, assignment, SplitVariable.origin] at hcenter
