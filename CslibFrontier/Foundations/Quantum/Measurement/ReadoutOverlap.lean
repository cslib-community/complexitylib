/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Quantum.Measurement.Readout
import CslibFrontier.Foundations.Quantum.Measurement.Overlap

/-!
# Multi-outcome readout distinguishability and state overlap

When a computational-basis measurement distinguishes two unit states through disjoint outcome sets
(or distinct values under a classical readout `out : ι → β`), their inner product is bounded by
`2√(ε(1-ε))` ([Ambainis2002], Lemma 1). This lifts the two-outcome overlap bound in
`CslibFrontier/Foundations/Quantum/Measurement/Overlap.lean` to multi-outcome functions and search
problems such as permutation inversion.

## Main results

* `Cslib.Quantum.norm_inner_le_two_mul_sqrt_of_disjoint`: overlap bound for disjoint accepting
  outcome sets `S₁` and `S₂`.
* `Cslib.Quantum.le_measureProb_of_le_measureOut_apply`: converts a lower bound on
  `measureOut ψ hψ out b` to `measureProb`.
* `Cslib.Quantum.norm_inner_le_two_mul_sqrt_of_readout_ne` and
  `Cslib.Quantum.norm_inner_le_two_mul_sqrt_of_measureOut_ne`: multi-outcome Lemma 1 of
  [Ambainis2002] for `measureProb` and `measureOut`.
* `Cslib.Quantum.one_eighteenth_le_one_sub_two_mul_sqrt`: numerical bound
  `1 / 18 ≤ 1 - 2 * √((1 / 3) * (1 - 1 / 3))` at bounded error `ε = 1 / 3`.

## References

* [A. Ambainis, *Quantum lower bounds by quantum arguments*][Ambainis2002]
-/

public section

namespace Cslib.Quantum

open Finset

/-- **Multi-outcome overlap bound for disjoint events** ([Ambainis2002], Lemma 1): if `S₁` and `S₂`
are disjoint sets of basis outcomes such that `ψ` lands in `S₁` with probability at least `1 - ε`
and `φ` lands in `S₂` with probability at least `1 - ε` (`2 * ε ≤ 1`), then
`‖inner ℂ ψ φ‖ ≤ 2 * √(ε * (1 - ε))`. -/
theorem norm_inner_le_two_mul_sqrt_of_disjoint {ι : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) {S₁ S₂ : Finset ι}
    (hdisj : Disjoint S₁ S₂) {ε : ℝ}
    (h₁ : 1 - ε ≤ measureProb ψ S₁) (h₂ : 1 - ε ≤ measureProb φ S₂) (hε : 2 * ε ≤ 1) :
    ‖inner ℂ ψ φ‖ ≤ 2 * √(ε * (1 - ε)) := by
  classical
  have hsub : S₁ ⊆ S₂ᶜ := fun a ha => mem_compl.2 (Finset.disjoint_left.1 hdisj ha)
  have hφ₁ : measureProb φ S₁ ≤ ε := by
    have hm := measureProb_mono φ hsub
    rw [measureProb_compl, hφ, one_pow] at hm
    linarith
  exact norm_inner_le_two_mul_sqrt_of_measureProb hψ hφ h₁ hφ₁ hε

/-- Converts an `ENNReal.ofReal` lower bound on `measureOut ψ hψ out b` into a `measureProb` lower
bound on the fiber `{a | out a = b}`. -/
theorem le_measureProb_of_le_measureOut_apply {ι β : Type*} [Fintype ι] [DecidableEq β]
    (ψ : EuclideanSpace ℂ ι) (hψ : ‖ψ‖ = 1) (out : ι → β) (b : β) {p : ℝ}
    (hp : ENNReal.ofReal p ≤ measureOut ψ hψ out b) :
    p ≤ measureProb ψ {a | out a = b} := by
  rw [measureOut_eq_ofReal_measureProb] at hp
  exact (ENNReal.ofReal_le_ofReal_iff (measureProb_nonneg _ _)).1 hp

/-- **Distinguishable multi-outcome readouts have small overlap** ([Ambainis2002], Lemma 1): if a
classical readout `out : ι → β` outputs `b₁` on `ψ` with probability at least `1 - ε` and `b₂ ≠ b₁`
on `φ` with probability at least `1 - ε` (`2 * ε ≤ 1`), then
`‖inner ℂ ψ φ‖ ≤ 2 * √(ε * (1 - ε))`. -/
theorem norm_inner_le_two_mul_sqrt_of_readout_ne {ι β : Type*} [Fintype ι] [DecidableEq β]
    {ψ φ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (out : ι → β) {b₁ b₂ : β}
    (hne : b₁ ≠ b₂) {ε : ℝ}
    (h₁ : 1 - ε ≤ measureProb ψ {a | out a = b₁})
    (h₂ : 1 - ε ≤ measureProb φ {a | out a = b₂}) (hε : 2 * ε ≤ 1) :
    ‖inner ℂ ψ φ‖ ≤ 2 * √(ε * (1 - ε)) := by
  refine norm_inner_le_two_mul_sqrt_of_disjoint hψ hφ ?_ h₁ h₂ hε
  rw [Finset.disjoint_filter]
  intro a _ ha₁ ha₂
  exact hne (ha₁.symm.trans ha₂)

/-- `PMF` form of `norm_inner_le_two_mul_sqrt_of_readout_ne` stated directly in terms of
`measureOut`. -/
theorem norm_inner_le_two_mul_sqrt_of_measureOut_ne {ι β : Type*} [Fintype ι]
    {ψ φ : EuclideanSpace ℂ ι} (hψ : ‖ψ‖ = 1) (hφ : ‖φ‖ = 1) (out : ι → β) {b₁ b₂ : β}
    (hne : b₁ ≠ b₂) {ε : ℝ}
    (h₁ : ENNReal.ofReal (1 - ε) ≤ measureOut ψ hψ out b₁)
    (h₂ : ENNReal.ofReal (1 - ε) ≤ measureOut φ hφ out b₂) (hε : 2 * ε ≤ 1) :
    ‖inner ℂ ψ φ‖ ≤ 2 * √(ε * (1 - ε)) := by
  classical
  exact norm_inner_le_two_mul_sqrt_of_readout_ne hψ hφ out hne
    (le_measureProb_of_le_measureOut_apply ψ hψ out b₁ h₁)
    (le_measureProb_of_le_measureOut_apply φ hφ out b₂ h₂) hε

/-- Numerical lower bound at bounded error `ε = 1 / 3`:
`1 / 18 ≤ 1 - 2 * √((1 / 3) * (1 - 1 / 3))`. -/
theorem one_eighteenth_le_one_sub_two_mul_sqrt :
    (1 / 18 : ℝ) ≤ 1 - 2 * √((1 / 3 : ℝ) * (1 - 1 / 3)) := by
  have hsqrt : √((1 / 3 : ℝ) * (1 - 1 / 3)) ≤ 17 / 36 :=
    (Real.sqrt_le_left (by norm_num)).2 (by norm_num)
  linarith

end Cslib.Quantum
