/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

import Complexity.Logics.Propositional.CNF.Planar.PairedCrossover
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! The paired template has exactly four full models, including every internal copy and all
eight ports. Counting uses the canonical-extension bijection instead of enumerating 57 bits. -/

open Cslib.Logic.PL Cslib.Logic.PL.CNF.PairedCrossover

private def modelsEquivInputs :
    {σ : Variable → Bool // formula.eval σ = true} ≃ Bool × Bool where
  toFun σ := (σ.val (terminal 0 0), σ.val (terminal 2 0))
  invFun ab := ⟨canonicalExtension ab.1 ab.2, eval_canonicalExtension ab.1 ab.2⟩
  left_inv σ := Subtype.ext (eq_canonicalExtension_of_holds σ.property).symm
  right_inv _ := rfl

example : Fintype.card {σ : Variable → Bool // formula.eval σ = true} = 4 := by
  rw [Fintype.card_congr modelsEquivInputs]
  decide

-- Incoming and outgoing values on distinct lanes still agree across the same wire.
example {σ : Variable → Bool} (h : formula.eval σ = true) :
    σ (terminal 0 1) = σ (terminal 1 0) ∧
      σ (terminal 2 1) = σ (terminal 3 0) := by
  constructor
  · exact (terminal_value_of_holds h 0 1).trans (terminal_value_of_holds h 1 0).symm
  · exact (terminal_value_of_holds h 2 1).trans (terminal_value_of_holds h 3 0).symm

-- The two signals are independent, with all ports populated in this concrete model.
example : formula.eval (canonicalExtension true false) = true ∧
    canonicalExtension true false (terminal 1 1) = true ∧
      canonicalExtension true false (terminal 3 1) = false :=
  ⟨eval_canonicalExtension true false, rfl, rfl⟩
