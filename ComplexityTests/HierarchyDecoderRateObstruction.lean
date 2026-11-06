/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: local-only (tests of the algebraic decoder rate obstruction)
import Complexity.Foundations.Probability.HierarchyDecoderRateObstruction
import all ComplexityTests.HierarchyPreparationRateSalary

/-!
Concrete half-mean and zero-entry checks use the production polynomial, gates, masks and
walks. The growing-prime client retains horizon admissibility, independent sparse tables,
true canonical input, positive actual density and the exact rooted/ordinary error ratio.
Imported RAW33/PREP34 execution and exhaustive-bin algebra remain distinct. These new
one-entry tables are algebraic decoder inputs; recursive successful execution is not asserted.
-/
set_option linter.privateModule false
noncomputable section
open Finset Cslib Matrix Matrix.HierarchyParams
open Matrix.HierarchyParams.H4RankEnvironment
open Matrix.DecoderRateObstruction
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

-- The hierarchy hypotheses have an existing witness; the obstruction is nonvacuous.
example : ∃ HP : FourthRootHierarchyParams 16 1 16 32 8, 0 < coefficient HP := by
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty
    (q := 16) (cπ := 1) (Cπ := 16) (Cpair := 32) (Cvar := 8) (by norm_num) (by norm_num)
  exact ⟨HP, coefficient_pos HP⟩

section Five
local instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- Research's mean is half only at (0,0), not across the entire row or matrix.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (σ : Environment 5 3) :
    (data HP 1).incomingPreparation (request HP 1)
        (fun _ => single 0 0 (5 * HP.θ * rate 1 / 8)) σ 0 0 = 1 / 2 ∧
    (data HP 1).incomingPreparation (request HP 1)
        (fun _ => single 0 0 (5 * HP.θ * rate 1 / 8)) σ 1 0 = 0 := by
  rw [incoming_half]
  norm_num

-- The literal decoder after a real conditional walk outputs 2q or q on its actual mask.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (M : ℕ) (σ : Environment 5 3) :
    output HP 1 (walkedPreparation HP 1 M (5 * HP.θ * rate 1 / 8)) σ 0 0 =
      (if (request (P := 5) HP 1).usage.retains (channels 1) σ 0 then 2 * HP.Q 1 else 0) ∧
    output HP 1 (walkedPreparation HP 1 M (rate 1)) σ 0 0 =
      (if (request (P := 5) HP 1).usage.retains (channels 1) σ 0 then HP.Q 1 else 0) := by
  rw [output_walked, output_walked]
  have ha : (data (P := 5) HP 1).incomingPreparation (request HP 1)
      (fun _ => single 0 0 (5 * HP.θ * rate 1 / 8)) = fun _ => single 0 0 (1 / 2) :=
    funext (incoming_half HP 1)
  have hg : (data (P := 5) HP 1).incomingPreparation (request HP 1)
      (fun _ => single 0 0 (rate 1)) = fun _ => single 0 0 1 := funext (incoming_one HP 1)
  rw [ha, hg, output_entry, output_entry]
  norm_num [single_apply, div_eq_mul_inv, mul_comm]

-- Actual density differs from nominal f at P=5, exponent 1: side=3, not 5/2.
example : densityFactor (P := 5) 1 = 81 / 3125 ∧
    densityFactor (P := 5) 1 ≠ rate 1 / 5 := by
  norm_num [densityFactor, show side 5 1 = 3 by decide, rate]

end Five

-- A fresh, growing field can satisfy the grid horizon and exceed both caps. The
-- algebraic completion identity holds for all budgets, separately from evaluator success.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) (C : ℝ) :
    ∃ ka P : ℕ, P.Prime ∧ 2 ^ ka ≤ P ∧ HP.K < P ∧
      ⌈4 * (1 + 32 * HP.R)⌉₊ < P ∧
      C < coefficient HP * (rate ka)⁻¹ ^ 4 ∧
      ∀ (_hP : Fact P.Prime) (M N : ℕ),
        let X := fun σ x => (request (P := P) HP ka).source.retains (channels 1) σ x
        let U := fun σ y => (request (P := P) HP ka).usage.retains (channels 1) σ y
        rootDistPow 4 P (request (P := P) HP ka).source.rate X U
            (output HP ka (walkedPreparation HP ka M (5 * HP.θ * rate ka / 8)))
            (output HP ka (walkedPreparation HP ka N (rate ka))) /
          rowNormPow 4 P (request (P := P) HP ka).source.rate X U
            (fun _ x y => single 0 0 (5 * HP.θ * rate ka / 8) x y -
              single 0 0 (rate ka) x y) = coefficient HP * (rate ka)⁻¹ ^ 4 := by
  obtain ⟨ka, hk⟩ := pow_unbounded_of_one_lt (C / coefficient HP)
    (by norm_num : (1 : ℝ) < 65536)
  obtain ⟨P, hp, hprime⟩ := Nat.exists_infinite_primes
    (max (2 ^ ka) (max HP.K ⌈4 * (1 + 32 * HP.R)⌉₊) + 1)
  refine ⟨ka, P, hprime, by omega, by omega, by omega, ?_, ?_⟩
  · rw [inverse_rate_fourth]
    simpa only [mul_comm] using (div_lt_iff₀ (coefficient_pos HP)).mp hk
  · intro hP M N
    exact walked_ratio HP ka M N
