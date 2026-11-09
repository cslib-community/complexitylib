/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.GameTheory.FairDivision.MMSExistence
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

/-! # Clients for uniform MMS hardness and exact-MMS semantics -/

open Cslib.FairDivision
open Cslib.FairDivision.MMSAsymptotic

-- The first admissible population uses the actual logarithmic code length.
example : populationLength 65536 = 1088 ∧ populationDummies 65536 = 63358 := by decide

-- The agent and item types are the actual source construction, not placeholders.
example : Fintype.card (HighGood (populationLength 65536) (populationDummies 65536)) = 65536 :=
  card_population _ (by decide)

-- Exact MMS cannot be promised even with an explicitly quantified item budget.
example : ¬ GoodsExistenceBudget 65536 75776 ∧ ¬ ChoresExistenceBudget 65536 75776 :=
  ⟨not_goodsExistenceBudget _ (by decide), not_choresExistenceBudget _ (by decide)⟩

-- One agent receives everything, for every competing complete partition.
example (v : Fin 1 → Fin 3 → ℝ) : GoodsMMSAllocation v (fun _ => 0) ∧
    ChoresMMSAllocation v (fun _ => 0) := by
  have hp (p : Fin 3 → Fin 1) : p = fun _ => 0 := by funext g; exact Fin.eq_zero _
  constructor <;> intro i p <;> fin_cases i <;> rw [hp p] <;> exact ⟨0, le_rfl⟩

-- Two identical agents, two unit items: giving everything to the first agent
-- fails both exact-MMS notions. The identity partition witnesses each failure.
example : ¬ GoodsMMSAllocation (fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) (fun _ => 0) := by
  intro h
  obtain ⟨j, hj⟩ := h 1 id
  fin_cases j <;>
    norm_num [bundleValue, Finset.sum_filter, Fin.sum_univ_two, Finset.filter_eq'] at hj

example : ¬ ChoresMMSAllocation (fun (_ : Fin 2) (_ : Fin 2) => (1 : ℝ)) (fun _ => 0) := by
  intro h
  obtain ⟨j, hj⟩ := h 0 id
  fin_cases j <;>
    norm_num [bundleValue, Finset.sum_filter, Fin.sum_univ_two, Finset.filter_eq'] at hj

-- The real-exponent corollary applies to 17n^(-1/3), not just integer powers.
example : ∃ N : ℕ, ∀ n ≥ N, (17 : ℝ) * (n : ℝ) ^ (-(1 / 3 : ℝ)) < populationGap n :=
  inverse_polynomial_lt_gap _ _ (by norm_num) (by norm_num)
