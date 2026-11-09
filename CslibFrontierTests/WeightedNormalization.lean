/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.WeightedNormalization

/-! # Repeated weighted occurrence normalization regressions -/

public section

namespace Cslib.Logic.PL.WeightedRow.Tests

/-- Positive repetitions and both polarities: `3x + 2x + 2¬x + y = 5`. -/
@[expose] def repeated (t : ℤ) : Occurrences 2 4 where
  var := ![0, 0, 0, 1]
  sign := ![true, true, false, true]
  weight := ![3, 2, 2, 1]
  positive := by decide
  target := t

example : (repeated 5).constant = 2 ∧ (repeated 5).total = 4 ∧
    (repeated 5).flip = true ∧ (repeated 5).demand = 1 := by decide

-- The coefficient 3 becomes 2 after complementation and capping.
example : ((repeated 5).toRow 1 (by decide)).weight 0 = 2 := by decide

example : (repeated 5).value ![true, false] = 5 := by decide
example : (repeated 5).value ![false, true] ≠ 5 := by decide

example : ∀ σ, ((repeated 5).normalize 1 (by decide)).Holds σ ↔
    ((repeated 5).value σ : ℤ) = 5 :=
  (repeated 5).normalize_iff 1 (by decide)

example : (repeated (-1)).normalize 0 (by decide) = .reject := by rfl
example : (repeated 7).normalize 0 (by decide) = .reject := by rfl

-- At demand zero, every active positive coefficient must disappear from the assignment.
example : (repeated 2).demand = 0 ∧
    ((repeated 2).toRow 0 (by decide)).weight 0 = 1 := by decide

/-- Equal opposite coefficients yield a constant-true row. -/
@[expose] def constantRow : Occurrences 1 2 where
  var := fun _ => 0
  sign := ![true, false]
  weight := fun _ => 4
  positive := fun _ => by decide
  target := 4

example : constantRow.normalize 0 (by decide) = .trivial := by rfl

example : ∀ σ, (((repeated 5).toRow 1 (by decide)).upper.eval σ = true ∧
    ((repeated 5).toRow 1 (by decide)).attainment.eval σ = true) ↔
      ((repeated 5).value σ : ℤ) = 5 :=
  (repeated 5).formula_iff 1 (by decide) (by decide)

example : Fintype.card {σ : Fin 2 → Bool // ((repeated 5).value σ : ℤ) = 5} = 1 := by decide

example : Fintype.card {σ : Fin 2 → Bool // ((repeated 5).value σ : ℤ) = 5} =
    Fintype.card {σ : Fin 2 ⊕ Fin 0 → Bool //
      (query (fun _ : Fin 1 => (repeated 5).toRow 1 (by decide)) false).eval σ = true} -
    Fintype.card {σ : Fin 2 ⊕ Fin 0 → Bool //
      (query (fun _ : Fin 1 => (repeated 5).toRow 1 (by decide)) true).eval σ = true} :=
  original_counting_identity (fun _ : Fin 1 => repeated 5) (fun _ => by decide)
    (fun _ => by decide)

end Cslib.Logic.PL.WeightedRow.Tests
