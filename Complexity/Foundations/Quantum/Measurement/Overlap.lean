/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Quantum.Measurement
import Mathlib.Analysis.Real.Sqrt

/-!
# Overlap bounds distinguishability

Two unit states with a large overlap give nearly the same probability to every set of outcomes:
`|⟨ψ, φ⟩|² + (P_ψ(S) - P_φ(S))² ≤ 1` (`Cslib.Quantum.norm_inner_sq_add_sq_measureProb_sub_le_one`).
This is how an adversary argument turns a bound on overlaps into a bound on the success
probability of a measurement.

## Main results

* `Cslib.Quantum.norm_inner_sq_add_sq_measureProb_sub_le_one`: `|⟨ψ, φ⟩|² + (p - q)² ≤ 1`.
-/

public section

namespace Cslib.Quantum

open Finset

/-- **Overlap and distinguishability**: for unit states `ψ` and `φ` and a set `S` of outcomes,
`|⟨ψ, φ⟩|² + (P_ψ(S) - P_φ(S))² ≤ 1`. Splitting the overlap along `S` and its complement and
applying Cauchy–Schwarz to each part bounds it by `√(pq) + √((1-p)(1-q))`, where `p` and `q` are
the probabilities of `S`. -/
theorem norm_inner_sq_add_sq_measureProb_sub_le_one {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (S : Finset ι) :
    ‖inner ℂ ψ φ‖ ^ 2 + (measureProb ψ S - measureProb φ S) ^ 2 ≤ 1 := by
  classical
  set p := measureProb ψ S
  set q := measureProb φ S
  have hp1 : measureProb ψ Sᶜ = 1 - p := by
    have := measureProb_univ ψ
    rw [← union_compl S, measureProb, sum_union disjoint_compl_right, hψ] at this
    change p + measureProb ψ Sᶜ = 1 ^ 2 at this
    linarith
  have hq1 : measureProb φ Sᶜ = 1 - q := by
    have := measureProb_univ φ
    rw [← union_compl S, measureProb, sum_union disjoint_compl_right, hφ] at this
    change q + measureProb φ Sᶜ = 1 ^ 2 at this
    linarith
  -- Cauchy–Schwarz on `S` and on its complement
  have hcs (T : Finset ι) : ‖∑ k ∈ T, (starRingEnd ℂ) (ψ.ofLp k) * φ.ofLp k‖ ≤
      √(measureProb ψ T) * √(measureProb φ T) := by
    refine (norm_sum_le _ _).trans ?_
    simp only [norm_mul, RCLike.norm_conj]
    exact Real.sum_mul_le_sqrt_mul_sqrt _ _ _
  have hsplit : inner ℂ ψ φ = ∑ k ∈ S, (starRingEnd ℂ) (ψ.ofLp k) * φ.ofLp k +
      ∑ k ∈ Sᶜ, (starRingEnd ℂ) (ψ.ofLp k) * φ.ofLp k := by
    rw [sum_add_sum_compl, PiLp.inner_apply]
    simp only [RCLike.inner_apply']
  have hinner : ‖inner ℂ ψ φ‖ ≤ √p * √q + √(1 - p) * √(1 - q) := by
    rw [hsplit, ← hp1, ← hq1]
    exact (norm_add_le _ _).trans (add_le_add (hcs S) (hcs Sᶜ))
  -- the algebra of two unit vectors in the plane
  have hp0 : 0 ≤ p := measureProb_nonneg _ _
  have hq0 : 0 ≤ q := measureProb_nonneg _ _
  have hp1' : 0 ≤ 1 - p := hp1 ▸ measureProb_nonneg _ _
  have hq1' : 0 ≤ 1 - q := hq1 ▸ measureProb_nonneg _ _
  set a := √p
  set a' := √(1 - p)
  set b := √q
  set b' := √(1 - q)
  have ha : a ^ 2 = p := Real.sq_sqrt hp0
  have ha' : a' ^ 2 = 1 - p := Real.sq_sqrt hp1'
  have hb : b ^ 2 = q := Real.sq_sqrt hq0
  have hb' : b' ^ 2 = 1 - q := Real.sq_sqrt hq1'
  have hsum : (a * b + a' * b') ^ 2 + (a * b' - a' * b) ^ 2 = 1 := by
    nlinarith
  have hcross : (a * b' + a' * b) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (a * b - a' * b')]
  have hdiff : p - q = (a * b' - a' * b) * (a * b' + a' * b) := by
    nlinarith
  have h₁ : ‖inner ℂ ψ φ‖ ^ 2 ≤ (a * b + a' * b') ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) hinner 2
  have h₂ : (p - q) ^ 2 ≤ (a * b' - a' * b) ^ 2 := by
    rw [hdiff, mul_pow]
    nlinarith [sq_nonneg (a * b' - a' * b)]
  linarith

end Cslib.Quantum
