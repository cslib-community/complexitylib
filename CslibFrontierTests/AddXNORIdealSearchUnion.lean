/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module

public import CslibFrontier.Cryptanalysis.AddXNORIdealSearchUnion
public import CslibFrontierTests.AddXNORIdealSecurity
import Mathlib.Tactic.NormNum

/-!
# Shared-collision search bounds and the remaining sharp-constant gap

The source's displayed inequality follows from the old unrounded endpoint at the review's
even-length example, and from the strengthened endpoint too. At the adjacent odd length,
even the strengthened numerical upper bound is larger than the source expression. This is
an obstruction to that comparison of bounds, not a counterexample to Theorem 8.
-/

public section

open Cslib Cslib.Probability Cslib.OracleComp Cslib.RandomPermutation
open Cslib.Cryptanalysis.AddXNOR.IdealChain

namespace IdealSearchUnionClient

/-- Reply-dependent acceptance of the guessed hidden endpoint from the earlier client. -/
@[expose] def guessedAccept : ProbOracleComp (Spec 3 (Fin 5)) Bool := do
  let reply ← IdealSecurityClient.guess
  return decide (reply = 2)

/-- Acceptance and disagreement actually overlap in the non-self-inverse guessed-endpoint
family: counting their probabilities separately pays for the same outcome twice. -/
example :
    (ProbOracleComp.runWith
      (Visible.handler true IdealSecurityClient.perms
        (IdealSecurityClient.cut.splice IdealSecurityClient.perms 0 4))
      guessedAccept (((), []), false)).map (fun (out, _, flag) => (out, flag)) =
    PMF.pure (true, true) := by
  have he : RandomPermutation.Family.eval IdealSecurityClient.perms ((1, false), .forward 1) =
      (2 : Fin 5) := by decide
  have hc : RandomPermutation.Family.eval
      (IdealSecurityClient.cut.splice IdealSecurityClient.perms 0 4)
      ((1, false), .forward 1) = (3 : Fin 5) := by decide
  simp [guessedAccept, IdealSecurityClient.guess,
    ProbOracleComp.runWith_query, Visible.handler,
    withBadFlag, Visible.step, he, hc]

/-- At the reviewer's example the previously approved unrounded theorem already implies the
literal source constants, for every budgeted adversary rather than just one fixed output. -/
example (adversary : Fin (2 ^ 40) → Fin (2 ^ 40) →
    ProbOracleComp (Spec 20 (Fin (2 ^ 40))) (Operators 20))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) 100) :
    ((plantedSearch adversary) true).toReal ≤
      3 * (100 : ℝ) / 2 ^ 10 + 10 * (100 : ℝ) ^ 2 / 2 ^ 40 + 1 / 2 ^ 20 := by
  have h := Security.source_search_rate (by norm_num : 3 ≤ 20) 40 100 adversary hbudget
    (by norm_num) (by norm_num)
  exact h.trans (by norm_num [Collisions.rate])

/-- The new actual-game endpoint also implies the source inequality there, after removing
rather than ignoring the repeated verification-collision charge. -/
example (adversary : Fin (2 ^ 40) → Fin (2 ^ 40) →
    ProbOracleComp (Spec 20 (Fin (2 ^ 40))) (Operators 20))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) 100) :
    ((plantedSearch adversary) true).toReal ≤
      3 * (100 : ℝ) / 2 ^ 10 + 10 * (100 : ℝ) ^ 2 / 2 ^ 40 + 1 / 2 ^ 20 := by
  have h := SearchUnion.source_search_rate (by norm_num : 3 ≤ 20) 40 100 adversary hbudget
    (by norm_num) (by norm_num)
  exact h.trans (by norm_num [Collisions.rate])

/-- A nontrivial odd-length whole-game bound from the same endpoint. -/
example (adversary : Fin (2 ^ 40) → Fin (2 ^ 40) →
    ProbOracleComp (Spec 21 (Fin (2 ^ 40))) (Operators 21))
    (hbudget : ∀ seed target, ProbOracleComp.IsQueryBounded (adversary seed target) 100) :
    ((plantedSearch adversary) true).toReal < 1 / 5 := by
  have h := SearchUnion.source_search_rate (by norm_num : 3 ≤ 21) 40 100 adversary hbudget
    (by norm_num) (by norm_num)
  exact h.trans_lt (by norm_num [Collisions.rate])

/-- The remaining loss is real at the level of this proved upper bound. No claim is made
that any adversary attains the bound or violates the source inequality. -/
example :
    3 * (100 : ℝ) / 2 ^ 11 + 10 * (100 : ℝ) ^ 2 / 2 ^ 40 + 1 / 2 ^ 21 <
      Collisions.rate (2 ^ 40) (100 + 21 + 21) +
        (100 + 21 : ℕ) / (2 : ℝ) ^ 11 + (100 + 21 : ℕ) / (2 : ℝ) ^ 10 := by
  norm_num [Collisions.rate]

end IdealSearchUnionClient
