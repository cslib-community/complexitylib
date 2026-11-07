/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.RowCompression.Preloss
public import Complexity.Foundations.Probability.RootMetric.Minkowski
public import Complexity.Probability.PairwiseIndependentHash.SliceFourthMoment
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Mean and noise budgets for finite additive sampler prefixes

A row has two raw channels. Its noise envelope is the fourth root of the sum of fourth
powers of its channel errors over the endpoints in a finite set. This explicit envelope
bounds the noise at each retained endpoint; its fourth moment is exactly the corresponding
summed channel moment. The clipped mean/noise comparison requires only a nonnegative true
first channel.

For a finite weighted prefix of actual walk averages, the deterministic mean is the same
weighted sum of full-environment means. Finite Minkowski turns centered input moment budgets
into a noise-envelope budget with no factor counting the groups. The graph and walk length
may vary by group; all groups use the same environment and may be arbitrarily correlated.
A separate result instantiates the single-row bound with the concrete retention-component walk.

These are finite fourth-moment assembly steps toward [OpenAI2026LogSpace, Sections 7.5–7.6,
Lemma 7.8 and Section 8.1, (8.3)]. The source uses exponent eight; here the exponent is four.
The adaptive budget/slack schedule, exact endpoint grouping, and verification that the walks
vary every sample-dependent coordinate remain obligations of the recursive estimator.
The endpoint set and slice/environment are fixed throughout a prefix. The component result
conditions on one fixed retention tuple; it does not identify each row endpoint with its own
conditioning slice. Integrating different endpoint slices is a separate obligation, and their
actual densities are not identified with nominal retention rates.

## Main definitions

* `Cslib.RowCompression.rowNoiseEnvelope`: the explicit two-channel row envelope.

## Main results

* `Cslib.RowCompression.clippedError_le_mean_add_rowNoiseEnvelope`: a derived raw-row budget.
* `Cslib.RotationMap.expect_rowNoiseEnvelope_walk_le`: centered walk moments control row noise.
* `Cslib.RotationMap.expect_rowNoiseEnvelope_prefix_le`: finite additive-prefix noise budgets.
* `Cslib.Probability.expect_rowNoiseEnvelope_componentMove_le`: the concrete conditional walk.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  23 September 2026, revision `7ef5c0cc`, pp. 39–44, Lemma 7.8 and (8.3)
  (preprint, not peer reviewed).
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.RowCompression

variable {ι : Type*}

/-- A two-channel row noise envelope, with zero value for an empty endpoint set. -/
@[expose] noncomputable def rowNoiseEnvelope (S : Finset ι)
    (raw mean : ι → Fin 2 → ℝ) : ℝ :=
  (∑ y ∈ S, ∑ ν : Fin 2, |raw y ν - mean y ν| ^ 4) ^ (4⁻¹ : ℝ)

/-- The row noise envelope is nonnegative. -/
theorem rowNoiseEnvelope_nonneg (S : Finset ι) (raw mean : ι → Fin 2 → ℝ) :
    0 ≤ rowNoiseEnvelope S raw mean := Real.rpow_nonneg (by positivity) _

/-- Taking the fourth power recovers exactly the summed channel errors. -/
theorem rowNoiseEnvelope_pow_four (S : Finset ι) (raw mean : ι → Fin 2 → ℝ) :
    rowNoiseEnvelope S raw mean ^ 4 = ∑ y ∈ S, ∑ ν : Fin 2, |raw y ν - mean y ν| ^ 4 :=
  Real.rpow_inv_natCast_pow (by positivity) (by decide)

/-- Every retained endpoint and channel is bounded by the same explicit row envelope. -/
theorem abs_sub_le_rowNoiseEnvelope (S : Finset ι) (raw mean : ι → Fin 2 → ℝ)
    {y : ι} (hy : y ∈ S) (ν : Fin 2) : |raw y ν - mean y ν| ≤
      rowNoiseEnvelope S raw mean := by
  apply (pow_le_pow_iff_left₀ (abs_nonneg _) (rowNoiseEnvelope_nonneg S raw mean)
    (by decide : (4 : ℕ) ≠ 0)).mp
  rw [rowNoiseEnvelope_pow_four]
  have hν : |raw y ν - mean y ν| ^ 4 ≤ ∑ ν : Fin 2, |raw y ν - mean y ν| ^ 4 :=
    single_le_sum (f := fun ν : Fin 2 => |raw y ν - mean y ν| ^ 4)
      (fun _ _ => by positivity) (mem_univ ν)
  exact hν.trans (single_le_sum (f := fun y => ∑ ν : Fin 2, |raw y ν - mean y ν| ^ 4)
    (fun _ _ => by positivity) hy)

/-- Clipped raw error is at most its actual mean error plus the derived row noise envelope.
No bound on the raw output discrepancy is assumed. -/
theorem clippedError_le_mean_add_rowNoiseEnvelope (S : Finset ι)
    (raw mean : ι → Fin 2 → ℝ) {y : ι} (hy : y ∈ S) {d v : ℝ} (hd : 0 ≤ d) :
    clippedError d v (raw y) ≤ clippedError d v (mean y) + rowNoiseEnvelope S raw mean := by
  have h0 := abs_sub_le_rowNoiseEnvelope S raw mean hy 0
  have h1 := abs_sub_le_rowNoiseEnvelope S raw mean hy 1
  have hγ := rowNoiseEnvelope_nonneg S raw mean
  have ht0 := abs_sub_le (raw y 0) (mean y 0) d
  have ht1 := abs_sub_le (raw y 1) (mean y 1) v
  have hden : 0 < 1 + d := by positivity
  have hdiv : |raw y 0 - d| / (1 + d) ≤
      |mean y 0 - d| / (1 + d) + rowNoiseEnvelope S raw mean := by
    apply (div_le_iff₀ hden).2
    have hpos := mul_nonneg hγ hd
    have hc := (div_mul_cancel₀ |mean y 0 - d| hden.ne')
    nlinarith
  have hclip (a b γ : ℝ) (hγ : 0 ≤ γ) (hab : a ≤ b + γ) :
      min 1 a ≤ min 1 b + γ := by
    calc
      _ ≤ min (1 + γ) (b + γ) := min_le_min (by linarith) hab
      _ = _ := min_add_add_right _ _ _
  unfold clippedError
  exact max_le
    ((hclip _ _ _ hγ hdiv).trans (add_le_add_left (le_max_left _ _) _))
    ((hclip |raw y 1 - v| |mean y 1 - v| _ hγ (by linarith)).trans
      (add_le_add_left (le_max_right _ _) _))

end Cslib.RowCompression

namespace Cslib.RotationMap

open RowCompression

variable {Ω D ι I : Type*} [Fintype Ω] [Fintype D] [Nonempty D]

/-- A walk's actual centered channel errors supply a row-noise moment bound. -/
theorem expect_rowNoiseEnvelope_walk_le (G : RotationMap Ω D) (S : Finset ι)
    (F : ι → Fin 2 → Ω → ℝ) (t : ℕ) :
    (𝔼 σ, rowNoiseEnvelope S (fun y ν => (G.walk ^ (2 * t)) (F y ν) σ)
      (fun y ν => 𝔼 τ, F y ν τ) ^ 4) ≤
      2 * G.spectralExpansion ^ (2 * t) *
        ∑ y ∈ S, ∑ ν : Fin 2, 𝔼 σ, (F y ν σ - 𝔼 τ, F y ν τ) ^ 4 := by
  simp_rw [rowNoiseEnvelope_pow_four]
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm]
  rw [mul_sum]
  refine sum_le_sum fun y _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun ν _ => ?_
  have habs (r : ℝ) : |r| ^ 4 = r ^ 4 := (by decide : Even (4 : ℕ)).pow_abs r
  simpa only [habs] using
    G.expect_walk_pow_two_mul_sub_expect_pow_four_le (F y ν) t

/-- **Finite additive-prefix noise.** The same-seed endpoint functions are averaged before
measuring their errors. Individual centered input budgets imply the fourth power of the sum
of the weighted budgets, with no factor counting the groups and no independence premise. -/
theorem expect_rowNoiseEnvelope_prefix_le [Finite ι] (s : Finset I) (S : Finset ι)
    (G : I → RotationMap Ω D) (t : I → ℕ) (F : I → ι → Fin 2 → Ω → ℝ)
    (w ε : I → ℝ) (hw : ∀ i ∈ s, 0 ≤ w i) (hε : ∀ i ∈ s, 0 ≤ ε i)
    (hbudget : ∀ i ∈ s,
      2 * (G i).spectralExpansion ^ (2 * t i) *
        (∑ y ∈ S, ∑ ν : Fin 2, 𝔼 σ, (F i y ν σ - 𝔼 τ, F i y ν τ) ^ 4) ≤ ε i ^ 4) :
    (𝔼 σ, rowNoiseEnvelope S
      (fun y ν => ∑ i ∈ s, w i * (((G i).walk ^ (2 * t i)) (F i y ν) σ))
      (fun y ν => ∑ i ∈ s, w i * (𝔼 τ, F i y ν τ)) ^ 4) ≤
        (∑ i ∈ s, w i * ε i) ^ 4 := by
  classical
  let := Fintype.ofFinite ι
  let X : Ω → ι × Fin 2 → Prop := fun _ z => z.1 ∈ S
  let noise : I → Ω → ι × Fin 2 → ℝ := fun i σ z =>
    (((G i).walk ^ (2 * t i)) (F i z.1 z.2) σ) - 𝔼 τ, F i z.1 z.2 τ
  have heq (f : Ω → ι × Fin 2 → ℝ) :
      vertexNormPow 4 1 1 X f = 𝔼 σ, ∑ y ∈ S, ∑ ν : Fin 2, |f σ (y, ν)| ^ 4 := by
    simp only [vertexNormPow, one_mul, inv_one, X]
    apply expect_congr rfl
    intro σ _
    simp only [sum_filter, Fintype.sum_prod_type]
    calc
      _ = ∑ y ∈ S, ∑ ν : Fin 2, if y ∈ S then |f σ (y, ν)| ^ 4 else 0 :=
        (sum_subset (subset_univ S) (fun y _ hy => by simp [hy])).symm
      _ = _ := sum_congr rfl fun y hy => by simp [hy]
  have hnoise : ∀ i ∈ s, vertexNormPow 4 1 1 X (noise i) ≤ ε i ^ 4 := by
    intro i hi
    rw [heq]
    have h := (expect_rowNoiseEnvelope_walk_le (G i) S (F i) (t i)).trans (hbudget i hi)
    simpa only [rowNoiseEnvelope_pow_four, noise] using h
  have h := vertexNormPow_sum_le_pow_sum (X := X) (by decide : (4 : ℕ) ≠ 0)
    (by norm_num : (0 : ℝ) ≤ 1 * 1) s noise w ε hw hε hnoise
  rw [heq] at h
  simpa only [rowNoiseEnvelope_pow_four, noise, mul_sub, sum_sub_distrib] using h

end Cslib.RotationMap

namespace Cslib.Probability

open RowCompression RotationMap

/-- The actual lazy component walk supplies the explicit conditional row-noise budget.
All endpoint/channel samples may use the same environment and need not be independent. -/
theorem expect_rowNoiseEnvelope_componentMove_le {ι : Type*} {H M J : ℕ}
    {P L : Fin J → ℕ} [∀ j, Fact (P j).Prime] [∀ j, NeZero (L j)] [NeZero M]
    (hH : 3 ≤ H) (hL : ∀ j, L j ≤ P j) (y : ∀ j, ZMod (P j)) (S : Finset ι)
    (F : ι → Fin 2 →
      ((∀ j, RetentionSlice (P j) H 1 (L j) (y j)) × (Fin H → ZMod M)) → ℝ) (t : ℕ) :
    (𝔼 A, rowNoiseEnvelope S
      (fun z ν => ((((ofPerms (componentMove H M P L)).lazy.reindex
        (componentEquiv M hL y).symm).walk ^ (2 * t)) (F z ν) A))
      (fun z ν => 𝔼 B, F z ν B) ^ 4) ≤
      2 * (1 - 1 / (155648 * (J + 1) * H ^ 4)) ^ (2 * t) *
        ∑ z ∈ S, ∑ ν : Fin 2, 𝔼 A, (F z ν A - 𝔼 B, F z ν B) ^ 4 := by
  simp_rw [rowNoiseEnvelope_pow_four]
  rw [expect_sum_comm]
  simp_rw [expect_sum_comm]
  rw [mul_sum]
  refine sum_le_sum fun z _ => ?_
  rw [mul_sum]
  refine sum_le_sum fun ν _ => ?_
  have habs (r : ℝ) : |r| ^ 4 = r ^ 4 := (by decide : Even (4 : ℕ)).pow_abs r
  simpa only [habs] using
    expect_walk_pow_componentMove_sub_expect_pow_four_le hH hL y (F z ν) t

end Cslib.Probability
