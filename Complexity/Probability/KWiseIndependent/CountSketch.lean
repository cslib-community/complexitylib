/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Probability.KWiseIndependent
public import Complexity.Probability.UniversalHash
import Complexity.Foundations.Data.Finset.Expect
import Complexity.Probability.KWiseIndependent.TugOfWar
import Mathlib.Algebra.Order.BigOperators.Expect
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# One row of a Count-Sketch

A row of the **Count-Sketch** of Charikar, Chen and Farach-Colton [CharikarChenFarachColton2004]
has `w` buckets. Its seed `(θ, φ)` consists of a seed `θ` of a bucket hash `h θ : X → Fin w` and
an independent seed `φ` of a sign hash `ε (g φ x) = ±1`. For weights `f : X → ℝ` on a finite set
`S`, the bucket `j` holds `∑ x ∈ S with h θ x = j, f x ε (g φ x)`, and the estimate of `f a` is the
bucket of `a` times the sign of `a`. Collisions of `a` with the other points add the noise
`∑ x ∈ S with h θ x = h θ a, f x ε (g φ x)`, summed over `x ≠ a`.

For a two-universal bucket family and a pairwise independent family of signs of mean zero:

* the estimate is unbiased (`Cslib.Probability.CountSketch.expect_sum_ite_mul_sign_mul_sign`);
* the noise has second moment at most `∑_{x ≠ a} f x ² / w`
  (`Cslib.Probability.CountSketch.expect_sq_sum_ite_mul_sign_le`), so by Chebyshev's inequality the
  noise exceeds `t` for at most a third of the seeds once `3 ∑_{x ≠ a} f x ² ≤ w t²`
  (`Cslib.Probability.CountSketch.dens_abs_sum_ite_mul_sign_gt_le`).

These are equations (5.1)–(5.6) of [Chakrabarti2025, Section 5.3.1], for arbitrary real weights, so
they apply to turnstile streams as well as to insertion streams. Only an upper bound on collision
probabilities is assumed of the bucket family.

## Main results

* `Cslib.Probability.CountSketch.expect_sum_ite_mul_sign_mul_sign`: the estimate is unbiased.
* `Cslib.Probability.CountSketch.expect_sq_sum_ite_mul_sign_le`: the second moment of the noise.
* `Cslib.Probability.CountSketch.dens_abs_sum_ite_mul_sign_gt_le`: the tail bound of one row.

## References

* [M. Charikar, K. Chen, M. Farach-Colton, *Finding frequent items in data
  streams*][CharikarChenFarachColton2004]
* [A. Chakrabarti, *Data Stream Algorithms*, Section 5.3][Chakrabarti2025]
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.Probability.CountSketch

variable {ι κ X Y : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Fintype Y] [DecidableEq Y]
  {w : ℕ} {h : ι → X → Fin w} {g : κ → X → Y} {ε : Y → ℝ}

/-- **The Count-Sketch estimate is unbiased** [Chakrabarti2025, equations (5.1)–(5.2)]: with a
two-universal bucket family `h`, an independent pairwise independent sign family `ε ∘ g` of mean
zero, and `a ∈ S`, the bucket of `a` times the sign of `a` has mean `f a`. Only the pairwise
independence of the signs is used. -/
theorem expect_sum_ite_mul_sign_mul_sign (hg : IsKWiseIndependentHash 2 g)
    (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0) {S : Finset X} {a : X} (ha : a ∈ S)
    (f : X → ℝ) :
    𝔼 p : ι × κ, (∑ x ∈ S, if h p.1 x = h p.1 a then f x * ε (g p.2 x) else 0) *
      ε (g p.2 a) = f a := by
  classical
  have hκ := hg.nonempty
  rw [Fintype.expect_prod_type]
  have hrow (θ : ι) : 𝔼 φ, (∑ x ∈ S, if h θ x = h θ a then f x * ε (g φ x) else 0) *
      ε (g φ a) = f a := by
    simp only [sum_mul, ite_mul, zero_mul]
    rw [expect_sum_comm, ← add_sum_erase S _ ha]
    have hdiag : 𝔼 φ, f a * ε (g φ a) * ε (g φ a) = f a := by
      have : Nonempty Y := ⟨g (Classical.arbitrary κ) a⟩
      simp only [mul_assoc, ← sq, hε, mul_one, Fintype.expect_const]
    simp only [eq_self, ↓reduceIte]
    rw [hdiag, add_eq_left]
    refine sum_eq_zero fun x hx => ?_
    split_ifs
    · simp only [mul_assoc, ← mul_expect]
      rw [hg.expect_sign_mul_sign hε₀ (ne_of_mem_erase hx), mul_zero]
    · exact expect_const_zero _
  simp only [hrow, Fintype.expect_const]

/-- **The second moment of the Count-Sketch noise** [Chakrabarti2025, equations (5.3)–(5.5)]: with
a two-universal bucket family `h` and an independent pairwise independent sign family `ε ∘ g` of
mean zero, the noise added to the bucket of `a ∉ S` by the points of `S` has second moment at most
`∑ x ∈ S, f x ² / w`. -/
theorem expect_sq_sum_ite_mul_sign_le (hh : IsTwoUniversal (PMF.uniformOfFintype ι) h)
    (hg : IsKWiseIndependentHash 2 g) (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0)
    {S : Finset X} {a : X} (ha : a ∉ S) (f : X → ℝ) :
    𝔼 p : ι × κ, (∑ x ∈ S, if h p.1 x = h p.1 a then f x * ε (g p.2 x) else 0) ^ 2 ≤
      (∑ x ∈ S, f x ^ 2) / w := by
  rw [Fintype.expect_prod_type]
  have hrow (θ : ι) : 𝔼 φ, (∑ x ∈ S, if h θ x = h θ a then f x * ε (g φ x) else 0) ^ 2 =
      ∑ x ∈ S, (if h θ x = h θ a then f x else 0) ^ 2 := by
    have := hg.expect_sq_sum_mul_sign hε hε₀ S fun x => if h θ x = h θ a then f x else 0
    simpa only [ite_mul, zero_mul] using this
  simp only [hrow]
  rw [expect_sum_comm, sum_div]
  refine sum_le_sum fun x hx => ?_
  have hxa : x ≠ a := fun hxa => ha (hxa ▸ hx)
  have hcoll := hh.expect_boole_le hxa
  rw [Fintype.card_fin] at hcoll
  calc 𝔼 θ, (if h θ x = h θ a then f x else 0) ^ 2
      = f x ^ 2 * 𝔼 θ, (if h θ x = h θ a then (1 : ℝ) else 0) := by
        rw [mul_expect]
        refine expect_congr rfl fun θ _ => ?_
        split_ifs <;> ring
    _ ≤ f x ^ 2 * (w : ℝ)⁻¹ := mul_le_mul_of_nonneg_left hcoll (sq_nonneg _)
    _ = f x ^ 2 / w := (div_eq_mul_inv _ _).symm

/-- **One row of a Count-Sketch** [Chakrabarti2025, equation (5.6)]: with a two-universal bucket
family `h` and an independent pairwise independent sign family `ε ∘ g` of mean zero, the noise added
to the bucket of `a ∉ S` by the points of `S` exceeds `t ≥ 0` in absolute value for at most a third
of the seeds once `3 ∑ x ∈ S, f x ² ≤ w t²`. -/
theorem dens_abs_sum_ite_mul_sign_gt_le (hh : IsTwoUniversal (PMF.uniformOfFintype ι) h)
    (hg : IsKWiseIndependentHash 2 g) (hε : ∀ y, ε y ^ 2 = 1) (hε₀ : 𝔼 y, ε y = 0)
    {S : Finset X} {a : X} (ha : a ∉ S) (f : X → ℝ) {t : ℝ} (ht : 0 ≤ t)
    (hw : 3 * ∑ x ∈ S, f x ^ 2 ≤ w * t ^ 2) :
    (dens {p : ι × κ |
      t < |∑ x ∈ S, if h p.1 x = h p.1 a then f x * ε (g p.2 x) else 0|} : ℝ) ≤ 1 / 3 := by
  classical
  have hκ := hg.nonempty
  set V := ∑ x ∈ S, f x ^ 2
  have hV : 0 ≤ V := sum_nonneg fun _ _ => sq_nonneg _
  rcases hV.eq_or_lt with hV0 | hVpos
  · -- No noise at all: every weight on `S` vanishes.
    have hf : ∀ x ∈ S, f x = 0 := fun x hx =>
      pow_eq_zero_iff (n := 2) two_ne_zero |>.1 ((Finset.sum_eq_zero_iff_of_nonneg fun _ _ =>
        sq_nonneg _).1 hV0.symm x hx)
    have hempty : ({p : ι × κ |
        t < |∑ x ∈ S, if h p.1 x = h p.1 a then f x * ε (g p.2 x) else 0|} : Finset _) = ∅ := by
      refine filter_false_of_mem fun p _ => ?_
      rw [Finset.sum_eq_zero fun x hx => by rw [hf x hx, zero_mul, ite_self], abs_zero, not_lt]
      exact ht
    rw [hempty, dens_empty, NNRat.cast_zero]
    norm_num
  have ht0 : 0 < t := by
    rcases ht.eq_or_lt with rfl | ht0
    · have : (0 : ℝ) < 3 * V := by positivity
      simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero] at hw
      linarith
    · exact ht0
  have hw0 : (0 : ℝ) < w := by
    by_contra hw0
    have : (w : ℝ) = 0 := le_antisymm (not_lt.1 hw0) (Nat.cast_nonneg w)
    rw [this, zero_mul] at hw
    linarith
  set N := fun p : ι × κ => ∑ x ∈ S, if h p.1 x = h p.1 a then f x * ε (g p.2 x) else 0
  have hsub : (dens {p : ι × κ | t < |N p|} : ℝ) ≤ dens {p : ι × κ | t ^ 2 ≤ N p ^ 2} := by
    exact_mod_cast dens_le_dens fun p hp => by
      simp only [mem_filter, mem_univ, true_and] at hp ⊢
      rw [← sq_abs (N p)]
      exact pow_le_pow_left₀ ht hp.le 2
  have hmarkov := Fintype.mul_dens_filter_le_expect (f := fun p => N p ^ 2)
    (fun _ => sq_nonneg _) (t ^ 2)
  have hsecond := expect_sq_sum_ite_mul_sign_le (κ := κ) hh hg hε hε₀ ha f
  have ht2 : 0 < t ^ 2 := by positivity
  have key : t ^ 2 * (dens {p : ι × κ | t ^ 2 ≤ N p ^ 2} : ℝ) ≤ t ^ 2 / 3 :=
    hmarkov.trans (hsecond.trans (by
      rw [div_le_div_iff₀ hw0 (by norm_num)]
      linarith))
  have : (dens {p : ι × κ | t ^ 2 ≤ N p ^ 2} : ℝ) ≤ 1 / 3 := by
    rw [div_eq_mul_one_div (t ^ 2)] at key
    exact le_of_mul_le_mul_left key ht2
  exact hsub.trans this

end Cslib.Probability.CountSketch
