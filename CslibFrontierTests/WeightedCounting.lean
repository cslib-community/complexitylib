/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Logics.Propositional.CNF.WeightedCounting
public import CslibFrontierTests.WeightedAffine
public import CslibFrontierTests.WeightedNormalization

/-! # Complete original-input and all-cases counting-plan clients -/

public noncomputable section
namespace Cslib.Logic.PL.WeightedRow.Tests

-- The complete entry point consumes repeated signed occurrences, not a supplied basis.
example : (originalCountingPlan (fun _ : Fin 2 => repeated 5) (d := 1)
    (fun _ => by decide)).val.count =
    Fintype.card {σ : Fin 2 → Bool // ∀ _j : Fin 2,
      ((repeated 5).value σ : ℤ) = (repeated 5).target} :=
  (originalCountingPlan (fun _ : Fin 2 => repeated 5) (d := 1) (fun _ => by decide)).property

-- Every concrete client uses the assembler with its own computed branches.
example : (countingPlan mixedSystem).val.count = normalizedCount mixedSystem :=
  (countingPlan mixedSystem).property
example : (countingPlan ([.reject] : List (Normalized 3 2))).val.count =
    normalizedCount (n := 3) (d := 2) [.reject] := (countingPlan _).property
example : (countingPlan ([] : List (Normalized 4 2))).val.count =
    normalizedCount (n := 4) (d := 2) [] := (countingPlan _).property
example : (countingPlan ([.row zero] : List (Normalized 0 0))).val.count =
    normalizedCount [.row zero] := (countingPlan _).property

/-- Single-coordinate full-rank constraint with either a Boolean or fractional candidate. -/
@[expose] def single (w b : ℕ) (hw : 0 < w) (hb : b ≤ 2) (hc : w ≤ b + 1) :
    Row (Fin 1) 2 where
  support := {0}
  sign := fun _ => true
  weight := fun _ => w
  demand := b
  positive := by simpa using hw
  bounded := hb
  capped := by simpa using hc

-- The actual unique-candidate test distinguishes 1*x=1 from 2*x=1.
example : normalizedCount [.row (single 1 1 (by decide) (by decide) (by decide))] = 1 := by
  rw [normalized_full_count _ (by simp) (by decide)]
  decide
example : normalizedCount [.row (single 2 1 (by decide) (by decide) (by decide))] = 0 := by
  rw [normalized_full_count _ (by simp) (by decide)]
  decide

-- Ordinary query clients can inspect all three budgets directly.
example {n d : ℕ} (k : ℕ) (q : Bool → CNF (Fin n ⊕ Fin k))
    (hv : n + k ≤ 2 * n - 2) (hw : ∀ β c, c ∈ q β → c.length ≤ d + 2)
    (hc : ∀ β, (q β).length ≤ countingBudget n d) :
    (CountingPlan.queries k q hv hw hc).count =
      Fintype.card {σ // (q false).eval σ = true} -
        Fintype.card {σ // (q true).eval σ = true} := rfl

end Cslib.Logic.PL.WeightedRow.Tests
