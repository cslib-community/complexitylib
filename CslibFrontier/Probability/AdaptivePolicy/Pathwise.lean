/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Basic.Real.Basic
public import Mathlib.Topology.Algebra.Ring.Real
public import Mathlib.Topology.Constructions
public import Mathlib.Analysis.Convex.Combination
public import Mathlib.Topology.Order.Compact
import Mathlib.Tactic

/-!
# Pathwise linear regret is covariance plus static allocation

[Aldridge2027], Theorem 3.1 and Corollary 3.2 (PDF p. 3). A nonempty finite
sample path has arbitrary real cost vectors and feasible actions in a compact
convex subset of a finite-dimensional real vector space. No randomness or
online-algorithm hypothesis is needed: the identities hold for every path.
The comparator is an attained minimum over the entire feasible set.

## Main results

* `pathwise_decomposition`: an attained comparator and the exact decomposition.
* `pathwise_covariance_le_regret`: the covariance inequality and equality criterion.
-/

public section
noncomputable section
open Finset
namespace Cslib.Probability.AdaptivePolicy.Pathwise
variable {ι τ : Type*} [Fintype ι] [Fintype τ] [Nonempty τ]

/-- Empirical mean of a vector-valued finite path. -/
@[expose] def mean (v : τ → ι → ℝ) : ι → ℝ :=
  fun i => (∑ t, v t i) / Fintype.card τ

/-- Sum of coordinatewise empirical centered products; no normalization by path length. -/
@[expose] def covariance (c z : τ → ι → ℝ) : ℝ :=
  ∑ t, ∑ i, (c t i - mean c i) * (z t i - mean z i)

/-- Regret against a particular fixed comparator. -/
@[expose] def regret (c z : τ → ι → ℝ) (u : ι → ℝ) : ℝ :=
  (∑ t, ∑ i, c t i * z t i) - ∑ t, ∑ i, c t i * u i

private theorem card_ne_zero : (Fintype.card τ : ℝ) ≠ 0 :=
  Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)

omit [Fintype ι] in
private theorem sum_eq_card_mean (v : τ → ι → ℝ) (i : ι) :
    (∑ t, v t i) = (Fintype.card τ : ℝ) * mean v i := by
  unfold mean
  field_simp

private theorem decomposition (c z : τ → ι → ℝ) (u : ι → ℝ) :
    regret c z u = covariance c z +
      (Fintype.card τ : ℝ) * ∑ i, mean c i * (mean z i - u i) := by
  unfold regret covariance
  simp only [sub_mul, mul_sub, sum_sub_distrib]
  rw [sum_comm (f := fun t i => c t i * mean z i),
    sum_comm (f := fun t i => mean c i * z t i),
    sum_comm (f := fun t i => mean c i * mean z i),
    sum_comm (f := fun t i => c t i * u i)]
  simp only [← sum_mul, ← mul_sum, sum_eq_card_mean, sum_const, card_univ, nsmul_eq_mul]
  simp only [mul_sum]
  ring_nf

omit [Fintype ι] in
private theorem mean_mem {Z : Set (ι → ℝ)} (hZ : Convex ℝ Z)
    (z : τ → ι → ℝ) (hz : ∀ t, z t ∈ Z) : mean z ∈ Z := by
  have h := hZ.sum_mem (t := (univ : Finset τ)) (w := fun _ => (Fintype.card τ : ℝ)⁻¹)
    (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))
    (by simp) (fun t _ => hz t)
  convert! h using 1
  ext i
  simp [mean, div_eq_mul_inv, ← sum_mul, mul_comm]

/-- Theorem 3.1, including existence and global optimality of the fixed comparator.
The source assumes a positive number of rounds; `Nonempty τ` expresses that condition. -/
theorem pathwise_decomposition (Z : Set (ι → ℝ)) (hcompact : IsCompact Z)
    (hconvex : Convex ℝ Z) (c z : τ → ι → ℝ) (hz : ∀ t, z t ∈ Z) :
    ∃ u ∈ Z,
      (∀ v ∈ Z, (∑ t, ∑ i, c t i * u i) ≤ ∑ t, ∑ i, c t i * v i) ∧
      regret c z u = covariance c z +
        (Fintype.card τ : ℝ) * ∑ i, mean c i * (mean z i - u i) ∧
      0 ≤ (Fintype.card τ : ℝ) * ∑ i, mean c i * (mean z i - u i) := by
  have hcont : Continuous (fun u : ι → ℝ => ∑ t, ∑ i, c t i * u i) := by fun_prop
  obtain ⟨u, hu, hmin⟩ := hcompact.exists_isMinOn
    ⟨z (Classical.arbitrary τ), hz _⟩ hcont.continuousOn
  refine ⟨u, hu, hmin, decomposition c z u, ?_⟩
  have h : (∑ t, ∑ i, c t i * u i) ≤ ∑ t, ∑ i, c t i * mean z i :=
    hmin (mean_mem hconvex z hz)
  simp only [sum_comm (f := fun t i => c t i * _), ← sum_mul, sum_eq_card_mean] at h
  simp only [mul_sub, sum_sub_distrib, mul_sum, ← mul_assoc]
  exact sub_nonneg.mpr h

/-- Corollary 3.2 for any globally minimizing comparator: covariance never
exceeds regret, with equality exactly when the mean action also minimizes cost. -/
theorem pathwise_covariance_le_regret (Z : Set (ι → ℝ)) (hconvex : Convex ℝ Z)
    (c z : τ → ι → ℝ) (hz : ∀ t, z t ∈ Z) (u : ι → ℝ) (huZ : u ∈ Z)
    (hu : ∀ v ∈ Z, (∑ t, ∑ i, c t i * u i) ≤ ∑ t, ∑ i, c t i * v i) :
    covariance c z ≤ regret c z u ∧
    (covariance c z = regret c z u ↔
      ∀ v ∈ Z, (∑ t, ∑ i, c t i * mean z i) ≤ ∑ t, ∑ i, c t i * v i) := by
  have hm := hu (mean z) (mean_mem hconvex z hz)
  have hid : regret c z u - covariance c z =
      (∑ t, ∑ i, c t i * mean z i) - ∑ t, ∑ i, c t i * u i := by
    rw [decomposition]
    simp only [sum_comm (f := fun t i => c t i * _), ← sum_mul,
      sum_eq_card_mean, mul_sub, sum_sub_distrib, mul_sum]
    ring_nf
  constructor
  · linarith
  · constructor
    · intro heq v hv
      have h := hu v hv
      linarith
    · intro hmin
      have h := hmin u huZ
      linarith

end Cslib.Probability.AdaptivePolicy.Pathwise
