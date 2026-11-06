/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Logics.Propositional.CNF.WeightedAffine

/-! # Actual signed weighted affine conversion clients -/

public section
namespace Cslib.Logic.PL.WeightedRow.Tests

/-- The capped mixed-polarity equation `2x + 3(1-y) = 2`, with an unused variable. -/
@[expose] def mixed : Row (Fin 3) 2 where
  support := {0, 1}
  sign := ![true, false, true]
  weight := ![2, 3, 9]
  demand := 2
  positive := by decide
  bounded := by decide
  capped := by decide

example : mixed.coefficients = [2, -3, 0] ∧ mixed.rhs = -1 := by decide
example : mixed.value ![true, true, false] = 2 := by decide
example : mixed.value ![false, false, true] ≠ 2 := by decide
example (σ : Fin 3 → Bool) : mixed.value σ = 2 ↔
    (∑ i, mixed.coefficient i * (if σ i then (1 : ℤ) else 0)) = -1 :=
  mixed.affine_iff σ

example (σ : Fin 3 → Bool) :
    (∀ N ∈ ([.trivial, .row mixed] : List (Normalized 3 2)), N.Holds σ) ↔
      mixed.value σ = 2 := by simp [Normalized.Holds, mixed]

example (σ : Fin 3 → Bool) :
    ¬ ∀ N ∈ ([.row mixed, .reject] : List (Normalized 3 2)), N.Holds σ := by
  simp [Normalized.Holds]

/-- Empty support and zero demand really give the zero affine equation. -/
@[expose] def zero : Row (Fin 0) 0 where
  support := ∅
  sign := fun _ => false
  weight := fun _ => 0
  demand := 0
  positive := by simp
  bounded := by decide
  capped := by simp

example : zero.coefficients = [] ∧ zero.rhs = 0 := by decide
example (σ : Fin 0 → Bool) : zero.value σ = zero.demand := by
  simp [zero, Row.value, Row.active]

-- All Boolean solutions survive actual computed row selection under computed consistency.
example (ns : List (Normalized 3 2))
    (hc : Cslib.LinearSystem.rectangularConsistent 3 (cappedMatrix ns) (cappedRhs ns) = true)
    (σ : Fin 3 → Bool) :
    (∀ i, (selectedCappedRow ns i).value σ = (selectedCappedRow ns i).demand) ↔
      ∀ R ∈ cappedRows ns, R.value σ = R.demand := selectedCappedRow_iff ns hc σ

/-- Duplicate mixed rows and a deleted true row exercise actual selection and pullback. -/
@[expose] def mixedSystem : List (Normalized 3 2) := [.row mixed, .trivial, .row mixed]

example : cappedMatrix mixedSystem = [[2, -3, 0], [2, -3, 0]] ∧
    cappedRhs mixedSystem = [-1, -1] := by decide
example : cappedBasis mixedSystem = [0] := by decide
example : LinearSystem.rectangularConsistent 3
    (cappedMatrix mixedSystem) (cappedRhs mixedSystem) = true := by decide
example (σ : Fin 3 → Bool) :
    (∀ i, (selectedCappedRow mixedSystem i).value σ =
      (selectedCappedRow mixedSystem i).demand) ↔
    ∀ R ∈ cappedRows mixedSystem, R.value σ = R.demand :=
  selectedCappedRow_iff mixedSystem (by decide) σ

example : cappedBasis ([.row zero] : List (Normalized 0 0)) = [] := by decide
example : LinearSystem.rectangularConsistent 0
    (cappedMatrix ([.row zero] : List (Normalized 0 0)))
    (cappedRhs ([.row zero] : List (Normalized 0 0))) = true := by decide

/-- A nonzero demand on empty support is an actual inconsistent affine system. -/
@[expose] def impossible : Row (Fin 0) 1 where
  support := ∅
  sign := fun _ => false
  weight := fun _ => 0
  demand := 1
  positive := by simp
  bounded := by decide
  capped := by simp

example : LinearSystem.rectangularConsistent 0
    (cappedMatrix ([.row impossible] : List (Normalized 0 1)))
    (cappedRhs ([.row impossible] : List (Normalized 0 1))) = false := by decide
example (σ : Fin 0 → Bool) :
    ¬ ∀ R ∈ cappedRows ([.row impossible] : List (Normalized 0 1)),
      R.value σ = R.demand := capped_inconsistent _ (by decide) σ

end Cslib.Logic.PL.WeightedRow.Tests
