/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Cryptanalysis.AddXNORIdealVerificationCovering
import CslibFrontier.Languages.Probabilistic.Oracle.Norm
import Mathlib.Tactic.NormNum

/-!
# Actual verification birth counts and literal Theorem 8

The finite native walk client derives counts from supported execution, including the reverse
view. The numerical clients instantiate literal Theorem 8 at even and odd chain lengths,
including the smallest odd case with a bound below one.
-/

public section

open Cslib Cslib.Probability Cslib.OracleComp Cslib.RandomPermutation
open Cslib.Cryptanalysis.AddXNOR.IdealChain

namespace IdealVerificationCoveringClient

/-- A five-step actual independent-family walk has at most one fresh birth at its middle
layer, and no reverse-view forward births. No table or path-validity conclusion is supplied. -/
example : ∃ endpoint : Fin 7, ∃ records : List (Forest.Record (Label 5) (Fin 7)),
    (endpoint, records) ∈ (OracleComp.runWith Ledger.answer
      (walk (List.ofFn fun i : Fin 5 => (i, false)) 0) []).support ∧
      (records.filter (Forest.selected (fun label => decide (label.1 = (2 : Fin 5))))).length ≤ 1 ∧
      ((records.map Forest.Record.reverse).filter
        (Forest.selected (fun _ => true))).length = 0 := by
  obtain ⟨⟨endpoint, records⟩, hout⟩ := (OracleComp.runWith Ledger.answer
    (walk (List.ofFn fun i : Fin 5 => (i, false)) (0 : Fin 7)) []).support_nonempty
  have hforward := (VerificationCovering.walk_counts
    (fun label : Label 5 => decide (label.1 = (2 : Fin 5))) _ _ _ _ _ hout).1
  have hreverse := (VerificationCovering.walk_counts
    (fun _ : Label 5 => true) _ _ _ _ _ hout).2
  have hl := VerificationCovering.verification_layer_count (fun _ : Fin 5 => false) 2
  refine ⟨endpoint, records, hout, ?_, ?_⟩
  · simpa using hforward.trans (by
      simpa only [List.filter_nil, List.length_nil, zero_add] using hl)
  · simpa using hreverse

/-- Literal Theorem 8 at an even chain length, with the query budget equal to the length. -/
example (adversary : Fin (2 ^ 40) → Fin (2 ^ 40) →
    ProbOracleComp (Spec 20 (Fin (2 ^ 40))) (Operators 20))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) 20) :
    ((plantedSearch adversary) true).toReal ≤
      3 * (20 : ℝ) / 2 ^ 10 + 10 * (20 : ℝ) ^ 2 / 2 ^ 40 + 1 / 2 ^ 20 :=
  VerificationCovering.source_theorem_eight (by norm_num : 3 ≤ 20) 40 20 adversary hbudget
    (by norm_num) (by norm_num)

/-- Literal Theorem 8 at an odd chain length, where the backward side is one level shorter. -/
example (adversary : Fin (2 ^ 40) → Fin (2 ^ 40) →
    ProbOracleComp (Spec 21 (Fin (2 ^ 40))) (Operators 21))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) 100) :
    ((plantedSearch adversary) true).toReal ≤
      3 * (100 : ℝ) / 2 ^ 11 + 10 * (100 : ℝ) ^ 2 / 2 ^ 40 + 1 / 2 ^ 21 :=
  VerificationCovering.source_theorem_eight (by norm_num : 3 ≤ 21) 40 100 adversary hbudget
    (by norm_num) (by norm_num)

/-- The smallest odd case `q = T = 9` where the bound is below one, at the smallest such
alphabet; below `T = 12` the factor-ten collision term alone does not absorb the rate. -/
example (adversary : Fin (2 ^ 13) → Fin (2 ^ 13) →
    ProbOracleComp (Spec 9 (Fin (2 ^ 13))) (Operators 9))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) 9) :
    ((plantedSearch adversary) true).toReal ≤
      3 * (9 : ℝ) / 2 ^ 5 + 10 * (9 : ℝ) ^ 2 / 2 ^ 13 :=
  VerificationCovering.source_search_sharp (by norm_num : 3 ≤ 9) 13 9 adversary hbudget
    (by norm_num) (by norm_num)

/-- The unrounded whole-game rate at the odd example is far below the literal bound. -/
example (adversary : Fin (2 ^ 40) → Fin (2 ^ 40) →
    ProbOracleComp (Spec 21 (Fin (2 ^ 40))) (Operators 21))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) 100) :
    ((plantedSearch adversary) true).toReal < 99 / 1000 := by
  have h := VerificationCovering.source_search_rate (by norm_num : 3 ≤ 21) 40 100
    adversary hbudget (by norm_num) (by norm_num)
  exact h.trans_lt (by norm_num [Collisions.rate])

end IdealVerificationCoveringClient
