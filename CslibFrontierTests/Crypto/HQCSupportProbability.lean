/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module

import CslibFrontier.Crypto.Primitives.HQC.SupportProbability

/-! Ordinary-module clients for the shared finite sampler discrepancy and growing-width law. -/

namespace CslibFrontierTests.HQCSupportProbability

open Cslib Cslib.Crypto Cslib.Crypto.HQC Cslib.Probability Finset
open scoped ENNReal

-- A non-dyadic support space: two-element subsets of a five-element universe.
example : CloseTo ((ProbComp.eval (sampleSupport2 3 5 2)).map (fun S => decide (4 ∈ S)))
    ((PMF.uniformOfFinset ((range 5).powersetCard 2) (by decide)).map
      (fun S => decide (4 ∈ S))) (3 / 8) := by
  have h := (sampleSupport2_closeTo (width := 3) (by decide : 2 ≤ 5)).map
    (fun S => decide (4 ∈ S))
  rw [supportLowerDensity_toReal] at h
  norm_num [Fin.prod_univ_succ] at h
  rw [ENNReal.ofReal_div_of_pos (by norm_num)] at h
  norm_num at h
  exact h

-- Valid zero width has no abort: at full weight there is only one possible support.
example {S : Finset ℕ} (hS : S ∈ (ProbComp.eval (sampleSupport2 0 5 5)).support) :
    S = range 5 := by
  obtain ⟨hsub, hcard⟩ := mem_powersetCard.mp
    (sampleSupport2_mem_powersetCard (by decide : 5 ≤ 5) hS)
  exact eq_of_subset_of_card_le hsub (by simp [hcard])

example : CloseTo (ProbComp.eval (sampleSupport2 0 0 0))
    (PMF.uniformOfFinset ((range 0).powersetCard 0) (by decide)) 0 := by
  simpa [supportLowerDensity] using sampleSupport2_closeTo (width := 0) (by decide : 0 ≤ 0)

-- Increasing the word width, rather than treating fixed32 as an asymptotic sampler.
example : Negligible (fun s => Real.toNNReal
    (1 - (supportLowerDensity s 5 0 2).toReal)) :=
  negligible_one_sub_supportLowerDensity (fun _ => by decide) (.const 5) (.const 2)
    (fun _ => le_rfl)

end CslibFrontierTests.HQCSupportProbability
