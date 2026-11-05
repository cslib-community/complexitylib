/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.GameTheory.FairDivision.EFXApproximation
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega

/-!
# Clients for the parameterized approximate-EFX counterexample

An actual EFX allocation and actual strict improvement show that the incompatibility is
not a claim that EFX alone fails. Explicit parameters test factors below the former `6/7`
gap, including a factor only `1/3000` above `2/3`.
-/

public section

namespace ComplexityTests.FairDivision.Approximation

open Cslib.FairDivision Cslib.FairDivision.ApproximateCounterexample

/-- Complete allocation `(x,y,abcpq,de)` in the nine-good order. -/
@[expose] def initial : Fin 9 → Fin 4 := ![0, 1, 2, 2, 2, 3, 3, 2, 2]

/-- The paper's trade `(x,bce,yp,adq)`. -/
@[expose] def improvement : Fin 9 → Fin 4 := ![0, 2, 3, 1, 1, 3, 1, 2, 3]

/-- The whole parameterized family admits this complete EFX allocation. -/
theorem initial_is_efx_family {K : ℕ} (hK : 6 ≤ K) : EFX (values K) initial := by
  intro i j g hij hg
  fin_cases i <;> fin_cases j <;> fin_cases g <;> norm_num at hij <;>
    norm_num [initial] at hg <;>
    norm_num [initial, bundleValue, values, Fin.sum_univ_succ] <;> omega

/-- The factor-one condition is satisfiable, even with every item value positive. -/
theorem initial_is_approximateEFX : ApproximateEFX 1 (values 6) initial := by
  apply (approximateEFX_one_iff _ _).mpr
  exact initial_is_efx_family (by decide)

example : ApproximateEFX (1 / 2) (values 6) initial :=
  initial_is_approximateEFX.mono (by norm_num)

example : (fun i : Fin 4 => bundleValue (values 6) initial i i) = ![18, 18, 11, 12] := by
  decide

example : (fun i : Fin 4 => bundleValue (values 6) improvement i i) = ![18, 18, 16, 14] := by
  decide

/-- This is an actual strict Pareto improvement of the checked EFX allocation. -/
theorem improvement_dominates : ParetoDominates (values 6) improvement initial := by
  decide

example : ¬ ParetoOptimal (values 6) initial := by
  intro h
  exact h ⟨improvement, improvement_dominates⟩

/-- Giving everything to one agent fails the ordinary factor-one removal test. -/
theorem crowded_not_approximateEFX : ¬ ApproximateEFX 1 (values 6) (fun _ => 0) := by
  intro h
  have hc := h 1 0 0 (by decide) rfl
  norm_num [bundleValue, values, Fin.sum_univ_succ] at hc

example : ∀ i g, 0 < values 13 i g := values_pos (by decide)

example (a : Fin 9 → Fin 4) :
    ¬ (ApproximateEFX (3 / 4) (values 13) a ∧ ParetoOptimal (values 13) a) :=
  not_approximateEFX_and_paretoOptimal (by decide) (by norm_num) a

example (a : Fin 9 → Fin 4) :
    ¬ (ApproximateEFX (667 / 1000) (values 3001) a ∧ ParetoOptimal (values 3001) a) :=
  not_approximateEFX_and_paretoOptimal (by decide) (by norm_num) a

/-- A client can obtain a concrete family parameter for a real factor without choosing a
rational approximation or proving a new finite certificate. -/
theorem exclusion_for_real_factor (α : ℝ) (hα : 2 / 3 < α) :
    ∃ K : ℕ, 6 ≤ K ∧ ∀ a : Fin 9 → Fin 4,
      ApproximateEFX α (values K) a → ∃ b, ParetoDominates (values K) b a := by
  obtain ⟨K, hK, hαK⟩ := exists_parameter hα
  exact ⟨K, hK, fun a ha => approximateEFX_has_pareto_improvement hK hαK a ha⟩

end ComplexityTests.FairDivision.Approximation
