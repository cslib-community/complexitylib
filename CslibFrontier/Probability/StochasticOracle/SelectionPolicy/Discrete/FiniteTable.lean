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

/-- The finite retaining policy's actual record law is exactly the discrete
construction, even on unreachable prior-halt/incomplete histories. -/
theorem retainingLaw_toPMF (O : Oracle B R J) (I : Instance E J) (ρ : ℝ)
    (select : List (Record B R) → Distribution B ℝ) (h : List (Record B R)) :
    (law O (retainingPolicy O I ρ select) h).toPMF =
      retainingLaw I ρ O.proposed (fun h => (select h).toPMF)
        (fun h b => (O.respond h b).toPMF) h := by
  classical
  have hpropose : proposals O = recordProposals O.proposed := rfl
  by_cases hn : none ∈ h
  · simp [law, retainingLaw, hn, Distribution.toPMF_pure]
  · by_cases hc : I.covered (selected I ρ (recordProposals O.proposed) h) = I.ground
    · simp [law, retainingPolicy, hpropose, retainingLaw, hn, hc,
        Distribution.toPMF_bind, Distribution.toPMF_pure]
    · simp [law, retainingPolicy, hpropose, retainingLaw, hn, hc, Distribution.toPMF_bind,
        Distribution.toPMF_map, PMF.bind_map, Function.comp_def]

end Cslib.Probability.StochasticOracle.SelectionPolicy.Discrete
