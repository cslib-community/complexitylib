/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Geometry.Euclidean.Angle.Unoriented.Basic
public import CslibFrontier.Probability.LocalitySensitiveHash.Measure
public import Mathlib.Probability.Distributions.Gaussian.Multivariate
import CslibFrontier.Foundations.MeasureTheory.Constructions.BorelSpace.Order
import CslibFrontier.Foundations.Probability.Gaussian.Multivariate
import CslibFrontier.Foundations.Probability.Gaussian.Sheppard

/-!
# SimHash: random-hyperplane locality-sensitive hashing

Charikar's random-hyperplane LSH scheme ([Charikar2002]), commonly called **SimHash**,
draws a random vector `r` from the standard Gaussian measure `stdGaussian E` on a
finite-dimensional real inner product space `E` and maps a vector `u : E` to the sign bit
`decide (0 ≤ ⟪u, r⟫)`. Two nonzero vectors `u` and `v` agree in sign unless the threshold `0` lies
between `⟪u, r⟫` and `⟪v, r⟫`. By Sheppard's formula
(`ProbabilityTheory.measureReal_stdGaussian_zero_mem_uIoc_eq_angle`), their collision probability is
exactly `1 - θ(u, v) / π` (`Cslib.Probability.measureCollisionProb_simHash`), or
`1 - arccos ⟪u, v⟫ / π` on the unit sphere (`measureCollisionProb_simHash_of_norm_eq_one`).

Consequently SimHash is `(θ₁, θ₂, 1 - θ₁ / π, 1 - θ₂ / π)`-sensitive for angular distance on
nonzero vectors (`isLocalitySensitive_simHash`) and
`(1 - arccos s₁ / π, 1 - arccos s₂ / π)`-sensitive for cosine similarity `⟪u, v⟫` on unit vectors
(`isLocalitySensitive_simHash_inner`).

## Main definitions

* `Cslib.Probability.simHash`: random-hyperplane sign hash `decide (0 ≤ ⟪u, r⟫)`.

## Main results

* `Cslib.Probability.measurableSet_simHash_eq`: measurability of the collision event.
* `Cslib.Probability.measureCollisionProb_simHash`:
  `Pr[simHash r u = simHash r v] = 1 - θ(u, v) / π`.
* `Cslib.Probability.measureCollisionProb_simHash_of_norm_eq_one`: unit-vector correlation form
  `1 - arccos ⟪u, v⟫ / π`.
* `Cslib.Probability.measureCollisionProb_simHash_pi`: coordinate-product Gaussian form on
  `EuclideanSpace ℝ ι`.
* `Cslib.Probability.isLocalitySensitive_simHash`,
  `Cslib.Probability.isLocalitySensitive_simHash_subtype`,
  `Cslib.Probability.isLocalitySensitive_simHash_inner`: sensitivity for angular distance and
  cosine similarity.

## References

* [M. S. Charikar, *Similarity estimation techniques from rounding algorithms*][Charikar2002]
-/

public section

namespace Cslib.Probability

open MeasureTheory ProbabilityTheory Real Set
open scoped RealInnerProductSpace Interval

section Definition

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- **SimHash** ([Charikar2002]): map `u` to the side of the hyperplane orthogonal to `r` on which
it lies, `decide (0 ≤ ⟪u, r⟫)`. -/
@[expose] noncomputable def simHash (r u : E) : Bool :=
  decide (0 ≤ ⟪u, r⟫)

/-- Two vectors share the same SimHash bit for `r` exactly when `0` does not lie strictly on one
side of `⟪u, r⟫` and weakly on the other. -/
theorem simHash_eq_iff (r u v : E) :
    simHash r u = simHash r v ↔ (0 : ℝ) ∉ Ι ⟪u, r⟫ ⟪v, r⟫ := by
  simp only [simHash, decide_eq_decide, mem_uIoc, not_or, not_and, not_le]
  rcases le_or_gt 0 ⟪u, r⟫ with hu | hu <;> rcases le_or_gt 0 ⟪v, r⟫ with hv | hv
  · exact iff_of_true (iff_of_true hu hv) ⟨fun h => absurd h hu.not_gt, fun h => absurd h hv.not_gt⟩
  · refine iff_of_false (fun h => not_lt.2 (h.1 hu) hv) ?_
    rintro ⟨_, h2⟩
    exact absurd (h2 hv) hu.not_gt
  · refine iff_of_false (fun h => not_lt.2 (h.2 hv) hu) ?_
    rintro ⟨h1, _⟩
    exact absurd (h1 hu) hv.not_gt
  · exact iff_of_true (iff_of_false (not_le.2 hu) (not_le.2 hv))
      ⟨fun _ => hv, fun _ => hu⟩

end Definition

section Collision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- The SimHash collision event `{r | simHash r u = simHash r v}` is measurable. -/
theorem measurableSet_simHash_eq (u v : E) :
    MeasurableSet {r : E | simHash r u = simHash r v} := by
  have hev : {r : E | simHash r u = simHash r v} = {r : E | (0 : ℝ) ∈ Ι ⟪u, r⟫ ⟪v, r⟫}ᶜ := by
    ext r
    exact simHash_eq_iff r u v
  rw [hev]
  exact (measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) 0).compl

variable [FiniteDimensional ℝ E]

/-- **Charikar's SimHash collision law** ([Charikar2002]): under the standard Gaussian measure,
two nonzero vectors collide with probability `1 - angle u v / π`. -/
theorem measureCollisionProb_simHash {u v : E} (hu : u ≠ 0) (hv : v ≠ 0) :
    measureCollisionProb (stdGaussian E) simHash u v = 1 - InnerProductGeometry.angle u v / π := by
  have hev : {r : E | simHash r u = simHash r v} = {r : E | (0 : ℝ) ∈ Ι ⟪u, r⟫ ⟪v, r⟫}ᶜ := by
    ext r
    exact simHash_eq_iff r u v
  rw [measureCollisionProb, hev,
    probReal_compl_eq_one_sub (measurableSet_setOf_mem_uIoc (by fun_prop) (by fun_prop) 0),
    measureReal_stdGaussian_zero_mem_uIoc_eq_angle hu hv]

/-- **SimHash collision law on unit vectors**: for `‖u‖ = 1` and `‖v‖ = 1`, the collision
probability equals `1 - arccos ⟪u, v⟫ / π`. -/
theorem measureCollisionProb_simHash_of_norm_eq_one {u v : E} (hu : ‖u‖ = 1) (hv : ‖v‖ = 1) :
    measureCollisionProb (stdGaussian E) simHash u v = 1 - Real.arccos ⟪u, v⟫ / π := by
  rw [measureCollisionProb_simHash (norm_ne_zero_iff.1 (by simp [hu]))
    (norm_ne_zero_iff.1 (by simp [hv])),
    InnerProductGeometry.angle_eq_arccos_inner_of_norm_eq_one hu hv]

/-- **SimHash under independent standard Gaussian coordinates** on `EuclideanSpace ℝ ι`. -/
theorem measureCollisionProb_simHash_pi {ι : Type*} [Fintype ι] {u v : EuclideanSpace ℝ ι}
    (hu : u ≠ 0) (hv : v ≠ 0) :
    measureCollisionProb (Measure.pi fun _ : ι => gaussianReal 0 1)
        (fun a x => simHash (WithLp.toLp 2 a) x) u v =
      1 - InnerProductGeometry.angle u v / π := by
  have hpre : {a : ι → ℝ | simHash (WithLp.toLp 2 a) u = simHash (WithLp.toLp 2 a) v} =
      {a : ι → ℝ | WithLp.toLp 2 a ∈ {r : EuclideanSpace ℝ ι | simHash r u = simHash r v}} := rfl
  rw [measureCollisionProb, hpre, measureReal_pi_gaussianReal_eq (measurableSet_simHash_eq u v),
    ← measureCollisionProb, measureCollisionProb_simHash hu hv]

/-- SimHash on `{u : E // u ≠ 0}` is `(θ₁, θ₂, 1 - θ₁ / π, 1 - θ₂ / π)`-sensitive for the
angular distance. -/
theorem isLocalitySensitive_simHash_subtype (θ₁ θ₂ : ℝ) :
    IsLocalitySensitive
      (measureCollisionProb (stdGaussian E) (fun r (u : {x : E // x ≠ 0}) => simHash r u.1))
      (fun u v => InnerProductGeometry.angle u.1 v.1 ≤ θ₁)
      (fun u v => θ₂ ≤ InnerProductGeometry.angle u.1 v.1)
      (1 - θ₁ / π) (1 - θ₂ / π) where
  le_of_near u v h := by
    change 1 - θ₁ / π ≤ measureCollisionProb (stdGaussian E) simHash u.1 v.1
    rw [measureCollisionProb_simHash u.2 v.2]
    exact sub_le_sub_left (div_le_div_of_nonneg_right h pi_pos.le) 1
  le_of_far u v h := by
    change measureCollisionProb (stdGaussian E) simHash u.1 v.1 ≤ 1 - θ₂ / π
    rw [measureCollisionProb_simHash u.2 v.2]
    exact sub_le_sub_left (div_le_div_of_nonneg_right h pi_pos.le) 1

/-- SimHash on `E` is `(1 - θ₁ / π, 1 - θ₂ / π)`-sensitive for pairs of nonzero vectors with
angles `≤ θ₁` vs `≥ θ₂`. -/
theorem isLocalitySensitive_simHash (θ₁ θ₂ : ℝ) :
    IsLocalitySensitive (measureCollisionProb (stdGaussian E) simHash)
      (fun u v => u ≠ 0 ∧ v ≠ 0 ∧ InnerProductGeometry.angle u v ≤ θ₁)
      (fun u v => u ≠ 0 ∧ v ≠ 0 ∧ θ₂ ≤ InnerProductGeometry.angle u v)
      (1 - θ₁ / π) (1 - θ₂ / π) where
  le_of_near u v h := by
    rw [measureCollisionProb_simHash h.1 h.2.1]
    exact sub_le_sub_left (div_le_div_of_nonneg_right h.2.2 pi_pos.le) 1
  le_of_far u v h := by
    rw [measureCollisionProb_simHash h.1 h.2.1]
    exact sub_le_sub_left (div_le_div_of_nonneg_right h.2.2 pi_pos.le) 1

/-- SimHash on unit vectors `{u : E // ‖u‖ = 1}` is
`(1 - arccos s₁ / π, 1 - arccos s₂ / π)`-sensitive for cosine similarity `⟪u, v⟫` (`s₁ ≤ ⟪u, v⟫`
for near pairs and `⟪u, v⟫ ≤ s₂` for far pairs). -/
theorem isLocalitySensitive_simHash_inner (s₁ s₂ : ℝ) :
    IsLocalitySensitive
      (measureCollisionProb (stdGaussian E) (fun r (u : {x : E // ‖x‖ = 1}) => simHash r u.1))
      (fun u v => s₁ ≤ ⟪u.1, v.1⟫) (fun u v => ⟪u.1, v.1⟫ ≤ s₂)
      (1 - Real.arccos s₁ / π) (1 - Real.arccos s₂ / π) where
  le_of_near u v h := by
    change 1 - Real.arccos s₁ / π ≤ measureCollisionProb (stdGaussian E) simHash u.1 v.1
    rw [measureCollisionProb_simHash_of_norm_eq_one u.2 v.2]
    exact sub_le_sub_left (div_le_div_of_nonneg_right (Real.arccos_le_arccos h) pi_pos.le) 1
  le_of_far u v h := by
    change measureCollisionProb (stdGaussian E) simHash u.1 v.1 ≤ 1 - Real.arccos s₂ / π
    rw [measureCollisionProb_simHash_of_norm_eq_one u.2 v.2]
    exact sub_le_sub_left (div_le_div_of_nonneg_right (Real.arccos_le_arccos h) pi_pos.le) 1

end Collision

end Cslib.Probability
