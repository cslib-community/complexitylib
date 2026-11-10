/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Spread.Duality
public import CslibFrontier.Probability.Spread.SmallnessDuality
import CslibFrontier.Probability.Minimax

/-!
# The exceptional-class consequence of thinning domination

The finite fractional-cover duality constructs a spread law supported by any proposed
non-weakly-small exceptional class. Increasing the retention rate then contradicts domination.
The source loss of a factor two in alpha is explicit.

## Main results

* `conjecture73At_of_conjecture78At`: source reduction with alpha/2.
* `conjecture73_of_conjecture78`, `conjecture73_of_conjecture711`: dimension-uniform implications.

## References

[Talagrand2010Small], Conjecture 7.3 (author PDF p.9), and the proof that Conjecture 7.8
implies Conjecture 7.3 (p.10), using Proposition 6.7(a) (p.7).
-/

public section
namespace Cslib.Probability.Spread
open Finset
open scoped BigOperators

/-- Thinning domination yields weak smallness of the exceptional family at half the constant. -/
theorem conjecture73At_of_conjecture78At {α : ℝ} (hα : 0 < α) (hα' : α < 1)
    (h : Conjecture78At α) : Conjecture73At (α / 2) := by
  classical
  intro n p hp hp' A hA
  by_contra hn
  obtain ⟨ν, hν, hsupp⟩ := exists_spread_of_not_isWeaklySmall
    (mul_pos (div_pos hα (by norm_num)) hp) hn
  have hspread : IsSpreadLaw (α * p) ν := by
    convert hν using 1; ring
  have hdom := h n p hp hp' ν hspread A hA
  let f := theta α A
  obtain ⟨J, hJ, hmean⟩ :=
    (PMF.toStdSimplex ν).exists_mem_support_le_sum_mul f
  have hsupport : J ∈ ν.support := by
    apply (PMF.mem_support_iff _ _).mpr
    intro hz
    have hh := Finsupp.mem_support_iff.mp hJ
    apply hh
    simp only [PMF.weights_toStdSimplex, hz, ENNReal.toReal_zero]
  have hex : productProb p A < f J :=
    (hsupp J hsupport).trans_le (theta_mono (by positivity) (by linarith) hα'.le hA J)
  have hmean' : f J ≤ ∑ K, (ν K).toReal * f K := by
    rw [Finsupp.sum_fintype _ _ (by simp)] at hmean
    simpa only [PMF.weights_toStdSimplex] using hmean
  exact (not_lt_of_ge hdom) (hex.trans_le hmean')

/-- The source universal-constant assertion 7.3 follows from 7.8 without a supplied spread law. -/
theorem conjecture73_of_conjecture78 (h : Conjecture78) : Conjecture73 := by
  obtain ⟨α, hα, hα', h⟩ := h
  exact ⟨α / 2, by positivity, by linarith, conjecture73At_of_conjecture78At hα hα' h⟩

/-- Combined source reductions from the majorizing-witness formulation to exceptional smallness. -/
theorem conjecture73_of_conjecture711 (h : Conjecture711) : Conjecture73 :=
  conjecture73_of_conjecture78 (conjecture78_of_conjecture711 h)

end Cslib.Probability.Spread
