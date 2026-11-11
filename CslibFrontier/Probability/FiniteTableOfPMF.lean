/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteTable

/-!
# Finite tables from actual probability mass functions

An arbitrary PMF on a finite observable type determines its normalized real table.
Conversion is inverse to `Distribution.toPMF`; it does not require finite hidden
storage or a supplied distributional representation certificate.

## Main results

* `toPMF_ofPMF`, `ofPMF_toPMF`: inverse conversions.
* `toPMF_injective`: transfer equality of laws to equality of finite tables.
-/

public section
noncomputable section
namespace Cslib.Optimization.OneConstraint.Distribution
variable {A : Type} [Fintype A]

/-- The real probability table of a finite observation of any discrete experiment. -/
@[expose] def ofPMF (p : PMF A) : Distribution A ℝ where
  weight a := (p a).toReal
  nonneg _ := ENNReal.toReal_nonneg
  total := by
    rw [← ENNReal.toReal_sum (fun a _ => p.apply_ne_top a)]
    have h : ∑ a, p a = 1 := by simpa only [tsum_fintype] using p.tsum_coe
    rw [h, ENNReal.toReal_one]

/-- The constructed table has exactly the original law. -/
theorem toPMF_ofPMF (p : PMF A) : (ofPMF p).toPMF = p := by
  ext a
  exact ENNReal.ofReal_toReal (p.apply_ne_top a)

/-- No information is lost when an existing finite table is round-tripped. -/
theorem ofPMF_toPMF (w : Distribution A ℝ) : ofPMF w.toPMF = w := by
  ext a
  exact w.toPMF_real a

/-- Interpreting finite tables is injective. -/
theorem toPMF_injective : Function.Injective (toPMF : Distribution A ℝ → PMF A) := by
  intro w v h
  simpa only [ofPMF_toPMF] using congrArg ofPMF h

/-- Decoding a deterministic PMF gives its deterministic table. -/
theorem ofPMF_pure (a : A) : ofPMF (PMF.pure a) = (Distribution.pure a : Distribution A ℝ) := by
  apply toPMF_injective
  simp only [toPMF_ofPMF, toPMF_pure]

end Cslib.Optimization.OneConstraint.Distribution
