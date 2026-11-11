/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Probability.StatisticalDistance
public import CslibFrontier.Probability.Conditioning
public import Mathlib.Analysis.Real.Sqrt
import CslibFrontier.Probability.PMF.Map
import CslibFrontier.Probability.PMF.ToReal

/-!
# Collision probability

The collision probability of a discrete distribution is the probability that two independent
samples agree, equivalently the sum of the squared masses. This quantity lets extraction bounds
avoid logarithms: a pointwise mass bound also bounds collision probability. The ambient type
may be infinite, including the type of binary words used by the computational definitions.

The distance-to-uniform estimate is the Cauchy–Schwarz step in the leftover hash lemma.

## Main definitions

* `Cslib.Probability.PMF.collisionProbability`: sum of squared probability masses.

## Main results

* `Cslib.Probability.PMF.collisionProbability_eq_probability`: independent-sample experiment.
* `Cslib.Probability.PMF.collisionProbability_le_of_mass_le`: pointwise mass upper bounds.
* `Cslib.Probability.PMF.collisionProbability_pos`, `collisionProbability_le_one`,
  `toReal_le_sqrt_of_collisionProbability_le`: elementary bounds.
* `Cslib.Probability.PMF.collisionProbability_sq_le_sum_pow_three`: Jensen, `‖p‖₂⁴ ≤ ‖p‖₃³`.
* `Cslib.Probability.PMF.four_mul_dist_sq_le_card_mul_sum_sq`: Cauchy–Schwarz between
  statistical distance and `ℓ₂` distance.
* `Cslib.Probability.PMF.dist_uniform_le`: distance to uniform from excess collisions.

## References

* [T. Holenstein, *Pseudorandom Generators from One-Way Functions: A Simple Construction for
  Any Hardness*][Holenstein2006], Section 3.3, proof of Lemma 1, equation (2).

Adapted from Probability/Collision.lean on the cslib `crypto` branch at
`5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the upstream statistical-distance metric.
-/

@[expose] public section

namespace Cslib.Probability.PMF

variable {α β : Type*}

/-- The probability that two independent samples from a discrete distribution agree. -/
noncomputable def collisionProbability (p : PMF α) : ℝ := ∑' a, (p a).toReal ^ 2

/-- For a finite ambient type, collision probability is a finite sum. -/
theorem collisionProbability_eq_sum [Fintype α] (p : PMF α) :
    collisionProbability p = ∑ a, (p a).toReal ^ 2 := tsum_fintype _

/-- The collision probability is nonnegative. -/
theorem collisionProbability_nonneg (p : PMF α) : 0 ≤ collisionProbability p :=
  tsum_nonneg (fun _ => sq_nonneg _)

/-- The squared probability masses of a `PMF` are summable. -/
theorem summable_collision (p : PMF α) : Summable (fun a => (p a).toReal ^ 2) := by
  apply Summable.of_nonneg_of_le (fun _ => sq_nonneg _) _ (summable_toReal p)
  intro a
  nlinarith [ENNReal.toReal_nonneg (a := p a), toReal_apply_le_one p a]

/-- The sum of squared masses is exactly the success probability of comparing independent draws,
using any equality decision procedure. -/
theorem collisionProbability_eq_probability [DecidableEq α] (p : PMF α) :
    collisionProbability p =
      ((p.bind (fun a => p.map (fun b => decide (a = b)))) true).toReal := by
  have hmap (a : α) : (p.map (fun b => decide (a = b))) true = p a := by
    rw [PMF.map_apply, tsum_eq_single a]
    · simp
    · intro b hb
      simp [Ne.symm hb]
  simp only [collisionProbability, bind_apply_toReal_tsum, hmap, sq]

/-- The collision probability of a uniform source is its reciprocal cardinality. -/
@[simp] theorem collisionProbability_uniform [Fintype α] [Nonempty α] :
    collisionProbability (PMF.uniformOfFintype α) = (Fintype.card α : ℝ)⁻¹ := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [collisionProbability_eq_sum, PMF.uniformOfFintype_apply, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

/-- Independent sources multiply their collision probabilities. -/
theorem collisionProbability_prod [Finite α] [Finite β] (p : PMF α) (q : PMF β) :
    collisionProbability (p.bind (fun a => q.map (a, ·))) =
      collisionProbability p * collisionProbability q := by
  let := Fintype.ofFinite α
  let := Fintype.ofFinite β
  simp only [collisionProbability_eq_sum, Fintype.sum_prod_type, bind_map_prodMk_apply,
    ENNReal.toReal_mul, mul_pow, ← Finset.mul_sum, ← Finset.sum_mul]

/-- A bound on each individual mass also bounds the probability of a collision. -/
theorem collisionProbability_le_of_mass_le (p : PMF α) {bound : ℝ}
    (h : ∀ a, (p a).toReal ≤ bound) : collisionProbability p ≤ bound := by
  calc
    _ ≤ ∑' a, (p a).toReal * bound := by
      apply Summable.tsum_le_tsum _ (summable_collision p) ((summable_toReal p).mul_right bound)
      intro a
      simpa only [sq] using mul_le_mul_of_nonneg_left (h a) (ENNReal.toReal_nonneg (a := p a))
    _ = bound := by rw [tsum_mul_right, tsum_toReal, one_mul]

/-- The collision probability is at most `1`. -/
theorem collisionProbability_le_one (p : PMF α) : collisionProbability p ≤ 1 :=
  collisionProbability_le_of_mass_le p fun a => toReal_apply_le_one p a

/-- The squared mass of each point is at most the collision probability. -/
theorem toReal_sq_le_collisionProbability (p : PMF α) (a : α) :
    (p a).toReal ^ 2 ≤ collisionProbability p :=
  (summable_collision p).le_tsum a fun _ _ => sq_nonneg _

/-- Every mass is at most the square root of a bound on the collision probability. -/
theorem toReal_le_sqrt_of_collisionProbability_le (p : PMF α) {b : ℝ}
    (hb : collisionProbability p ≤ b) (a : α) : (p a).toReal ≤ Real.sqrt b :=
  Real.le_sqrt_of_sq_le ((toReal_sq_le_collisionProbability p a).trans hb)

/-- The collision probability is positive. -/
theorem collisionProbability_pos (p : PMF α) : 0 < collisionProbability p := by
  obtain ⟨a, ha⟩ := p.support_nonempty
  have hpos : 0 < (p a).toReal :=
    ENNReal.toReal_pos ((PMF.mem_support_iff p a).mp ha) (p.apply_ne_top a)
  exact (pow_pos hpos 2).trans_le (toReal_sq_le_collisionProbability p a)

/-- **Jensen's inequality** for the collision probability: `‖p‖₂⁴ ≤ ‖p‖₃³`, since the variance of
`p(a)` for `a` drawn from `p` is nonnegative. -/
theorem collisionProbability_sq_le_sum_pow_three [Fintype α] (p : PMF α) :
    collisionProbability p ^ 2 ≤ ∑ a, (p a).toReal ^ 3 := by
  have key (s : ℝ) : ∑ a, (p a).toReal * ((p a).toReal - s) ^ 2 =
      ∑ a, (p a).toReal ^ 3 - 2 * s * ∑ a, (p a).toReal ^ 2 + s ^ 2 * ∑ a, (p a).toReal := by
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun a _ => by ring
  have h0 : 0 ≤ ∑ a, (p a).toReal * ((p a).toReal - ∑ b, (p b).toReal ^ 2) ^ 2 :=
    Finset.sum_nonneg fun a _ => mul_nonneg ENNReal.toReal_nonneg (sq_nonneg _)
  rw [key, sum_toReal] at h0
  rw [collisionProbability_eq_sum]
  nlinarith

/-- A deterministic image collides exactly when the original samples have the same image. -/
theorem collisionProbability_map [Fintype α] [DecidableEq β] (p : PMF α) (f : α → β) :
    collisionProbability (p.map f) =
      ∑ a, ∑ b, if f a = f b then (p a).toReal * (p b).toReal else 0 := by
  rw [collisionProbability_eq_probability]
  simp only [PMF.bind_map, PMF.map_comp, Function.comp_def, bind_apply_toReal,
    map_apply_toReal, true_eq_decide_iff, Finset.mul_sum, mul_ite, mul_zero]

/-- An injective encoding does not change collision probability. Both types may be infinite. -/
theorem collisionProbability_map_of_injective (p : PMF α)
    (f : α → β) (hf : Function.Injective f) :
    collisionProbability (p.map f) = collisionProbability p := by
  classical
  simp [collisionProbability_eq_probability, PMF.map, Function.comp_def, hf.eq_iff]

/-- A uniform input conditioned on its image has collision probability reciprocal to the
size of that image's fiber, even when different images have different fiber sizes. -/
theorem collisionProbability_conditionalSnd_uniform_map [Fintype α] [Nonempty α]
    (f : α → β) (b : β) [Nonempty {a // f a = b}] :
    collisionProbability
      (conditionalSnd ((PMF.uniformOfFintype α).map (fun a => (f a, a))) b) =
        (Nat.card {a // f a = b} : ℝ)⁻¹ := by
  classical
  rw [conditionalSnd_uniform_map, collisionProbability_map_of_injective _ _ Subtype.val_injective,
    collisionProbability_uniform, Nat.card_eq_fintype_card]

/-- **Cauchy–Schwarz between `ℓ₁` and `ℓ₂`.** On `n` points, `4 dist(p, q)² ≤ n ‖p - q‖₂²`. -/
theorem four_mul_dist_sq_le_card_mul_sum_sq [Fintype α] (p q : PMF α) :
    4 * dist p q ^ 2 ≤ Fintype.card α * ∑ a, ((p a).toReal - (q a).toReal) ^ 2 := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun a => |(p a).toReal - (q a).toReal|)
    (fun _ => (1 : ℝ))
  simp only [mul_one, sq_abs, one_pow, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [dist_eq]
  nlinarith

/-- Squared distance to uniform is controlled by the excess collision probability. -/
theorem dist_uniform_sq_le [Fintype α] [Nonempty α] (p : PMF α) :
    4 * dist p (PMF.uniformOfFintype α) ^ 2 ≤
      Fintype.card α * collisionProbability p - 1 := by
  have hcard : (Fintype.card α : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  have hsum : ∑ a, ((p a).toReal - (Fintype.card α : ℝ)⁻¹) ^ 2 =
      collisionProbability p - (Fintype.card α : ℝ)⁻¹ := by
    simp only [sub_sq, Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.sum_mul, collisionProbability_eq_sum]
    rw [← Finset.mul_sum, sum_toReal]
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    field_simp
    ring
  have h := four_mul_dist_sq_le_card_mul_sum_sq p (PMF.uniformOfFintype α)
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast, hsum] at h
  rw [mul_sub, mul_inv_cancel₀ hcard] at h
  exact h

/-- Cauchy–Schwarz bounds distance to uniform by the square root of excess collisions. -/
theorem dist_uniform_le [Fintype α] [Nonempty α] (p : PMF α) :
    dist p (PMF.uniformOfFintype α) ≤
      Real.sqrt (Fintype.card α * collisionProbability p - 1) / 2 := by
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
  apply Real.le_sqrt_of_sq_le
  nlinarith [dist_uniform_sq_le p]

end Cslib.Probability.PMF
