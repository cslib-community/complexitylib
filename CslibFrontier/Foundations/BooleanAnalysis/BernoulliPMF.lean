/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.BooleanAnalysis.Bernoulli
public import CslibFrontier.Probability.PMF

/-!
# The Bernoulli product law on bit strings

`bernoulliPMF` packages the nonnegative normalized product weights of `bernoulliWeight` as
an actual probability mass function for every parameter in `[0, 1]`. Its expectations agree
with `bernoulliAverage`, including empty coordinate types and endpoint densities.

## Main definitions

* `bernoulliPMF`: the actual independent Bernoulli mask law.

## Main results

* `bernoulliPMF_apply_toReal`: its atom weights are `bernoulliWeight`.
* `sum_bernoulliPMF_mul`: its expectations are `bernoulliAverage`.
-/

public section

namespace Cslib.BitString

open Finset

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- Product mask weights are nonnegative for every density in the unit interval. -/
theorem bernoulliWeight_nonneg {t : ℝ} (ht : 0 ≤ t) (ht' : t ≤ 1) (x : ι → Bool) :
    0 ≤ bernoulliWeight t x :=
  prod_nonneg fun i _ => by
    split_ifs
    · exact ht
    · exact sub_nonneg.mpr ht'

/-- The law of a Boolean retention mask, with independent coordinates of density `t`.
This is a semantic distribution, not a resource-bounded sampler. -/
@[expose] noncomputable def bernoulliPMF (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1) :
    PMF (ι → Bool) :=
  PMF.ofFintype (fun x => ENNReal.ofReal (bernoulliWeight t x)) (by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun x _ => bernoulliWeight_nonneg ht ht' x)]
    have hs : (∑ x : ι → Bool, bernoulliWeight t x) = 1 := by
      simpa only [bernoulliAverage, mul_one] using
        bernoulliAverage_const (ι := ι) t 1
    rw [hs, ENNReal.ofReal_one])

/-- The actual mask law assigns exactly the real-valued product weight to each mask. -/
@[simp] theorem bernoulliPMF_apply_toReal (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (x : ι → Bool) : (bernoulliPMF t ht ht' x).toReal = bernoulliWeight t x :=
  ENNReal.toReal_ofReal (bernoulliWeight_nonneg ht ht' x)

/-- Averaging under the actual mask law recovers the real-valued Bernoulli average. -/
theorem sum_bernoulliPMF_mul (t : ℝ) (ht : 0 ≤ t) (ht' : t ≤ 1)
    (f : (ι → Bool) → ℝ) :
    (∑ x, (bernoulliPMF (ι := ι) t ht ht' x).toReal * f x) =
      bernoulliAverage t f := by
  simp only [bernoulliAverage, bernoulliPMF_apply_toReal]

end Cslib.BitString
