/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.Entropy
public import CslibFrontier.Probability.Product

/-!
# Entropy of independent products

The entropy of an independent product `Cslib.Probability.PMF.pi p` of finite distributions is the
sum of the entropies of its coordinates (`Cslib.Probability.PMF.entropy_pi`)
[Cover and Thomas, Section 2.6][CoverThomas2006]. For two factors this is
`Cslib.Probability.PMF.entropy_prod`.

## Main results

* `Cslib.Probability.PMF.entropy_pi`: entropy is additive over independent coordinates.

## References

* [T. M. Cover, J. A. Thomas, *Elements of Information Theory*][CoverThomas2006], 2nd ed.
-/

public section

namespace Cslib.Probability.PMF

/-- Independent coordinates add their entropies: `H(X₁, …, Xₙ) = ∑ᵢ H(Xᵢ)`. -/
theorem entropy_pi {ι : Type*} [Fintype ι] {α : ι → Type*} [∀ i, Finite (α i)]
    (p : ∀ i, PMF (α i)) : entropy (pi p) = ∑ i, entropy (p i) := by
  classical
  let (i : ι) := Fintype.ofFinite (α i)
  rw [entropy_eq_sum]
  simp only [entropy_eq_sum, ← Finset.sum_div]
  congr 1
  have hterm : ∀ x : ∀ i, α i, Real.negMulLog (pi p x).toReal =
      (pi p x).toReal * ∑ i, -Real.log (p i (x i)).toReal := by
    intro x
    rw [pi_apply, ENNReal.toReal_prod]
    by_cases h0 : ∀ i, (p i (x i)).toReal ≠ 0
    · rw [Real.negMulLog, Real.log_prod (fun i _ => h0 i), Finset.sum_neg_distrib]
      ring
    · push Not at h0
      obtain ⟨i, hi⟩ := h0
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hi, Real.negMulLog_zero, zero_mul]
  simp only [hterm]
  rw [sum_pi_mul_sum p (fun i a => -Real.log (p i a).toReal)]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => ?_
  rw [Real.negMulLog]
  ring

end Cslib.Probability.PMF
