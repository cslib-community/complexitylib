/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.StochasticOracle.SelectionPolicy.Discrete
public import CslibFrontier.Probability.StochasticOracle.SelectionOptimum
import Mathlib.Tactic

/-!
# Finite-table specialization of the discrete retaining policy

The existing finite-table upper policy and the arbitrary-PMF policy construct
the same next-record law after interpreting the tables as PMFs. Equality holds
at all histories, including unreachable histories with a prior halt before
coverage. The two interfaces preserve the same selected-before-response order.
-/

public section
noncomputable section
namespace Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
open Cslib.Optimization.OneConstraint AdaptiveSelection PartialCover
variable {B R J E : Type} [Fintype B] [Fintype R] [Fintype J]
  [DecidableEq E] [DecidableEq J]

omit [DecidableEq J] in
/-- Every finite-table competing policy has the shared actual PMF execution
law after interpreting its choice and response tables. -/
theorem policyLaw_toPMF (O : Oracle B R J) (π : Policy B R J) (h : List (Record B R)) :
    (law O π h).toPMF =
      policyLaw (fun h => (π.choose h).toPMF) (fun h b => (O.respond h b).toPMF) h := by
  classical
  by_cases hn : none ∈ h
  · simp [law, policyLaw, hn, Distribution.toPMF_pure]
  · rw [law, ite_eq_right hn, policyLaw, ite_eq_right hn, Distribution.toPMF_bind]
    congr 1
    funext b
    cases b <;> simp [Distribution.toPMF_pure, Distribution.toPMF_map]

/-- The finite retaining policy's actual record law is exactly the discrete
construction, even on unreachable prior-halt/incomplete histories. -/
theorem retainingLaw_toPMF (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (h : List (Record B R)) :
    (law O (retainingPolicy O I ρ select) h).toPMF =
      retainingLaw I ρ O.proposed (fun h => (select h).toPMF)
        (fun h b => (O.respond h b).toPMF) h := by
  classical
  rw [policyLaw_toPMF, retainingLaw]
  congr 1
  funext g
  have hpropose : proposals O = recordProposals O.proposed := rfl
  by_cases hc : I.covered (selected I ρ (recordProposals O.proposed) g) = I.ground <;>
    simp [retainingPolicy, retainingChoose, hpropose, hc,
      Distribution.toPMF_pure, Distribution.toPMF_map]

end Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
