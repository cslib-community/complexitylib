/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Analysis.Fourier.ZModProd
public import Complexity.Foundations.Algebra.Shear
public import Complexity.Foundations.Combinatorics.Expander.ShearTranslation
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The relative Poincaré inequality for shears and translations

The Poincaré inequality for the shear-translation graph on `ZMod n × ZMod n`
(`sum_norm_sq_le_shearTranslation`) has two consequences proved here.

**On the frequencies.** Through the Fourier transform `ZMod.dftProd`, which is a bijection, the
inequality gives one for an arbitrary function `Φ` on the frequencies that vanishes at
`0` (`sum_norm_sq_le_dual_shearTranslation`). The translations become the weights
`‖e (ξ.1) - 1‖ ^ 2` and `‖e (ξ.2) - 1‖ ^ 2`, and the unit shears become the dual shears by `-1`.

**With a spectator.** Let the shears act on `X × (ZMod n × ZMod n)` together with permutations
`π₁`, `π₂` of a finite set `X`, while the translations leave `X` fixed
(`twistedShearTranslationMove`). Then every function `f` is close to its averages over the fibers
`{x} × (ZMod n × ZMod n)`: their squared distance is at most `512` times the total squared change
of `f` along the four moves (`sum_norm_sq_sub_fiber_le_twistedShearTranslation`, and
`expect_sq_sub_expect_fiber_le_twistedShearTranslation` for real functions and averages). Unlike a
spectral gap, this does not ask the moves to mix `X`: it is a *relative* Poincaré inequality, which
in a representation-theoretic language says that vectors almost invariant under shears and
translations are close to vectors invariant under the translations. The proof transforms `f` in
the second coordinate, `F x = dftProd (f (x, ·))`, and applies the inequality on the frequencies to
`Φ ξ = ‖F · ξ‖` (the `ℓ²` norm over `X`) for `ξ ≠ 0`. The spectator permutations only reindex
this norm, and the reverse triangle inequality bounds the changes of `Φ` by those of `F`.

This is the step that turns the uniform gap on `ZMod n × ZMod n` into closeness to the vectors
fixed by the translations of one coordinate pair, as in the projection argument of the OpenAI
preprint on derandomizing logarithmic space for its affine walks
[OpenAI, proof of Lemma 6.1][OpenAI2026LogSpace]. The preprint's text takes it from Shalom's
quantitative relative property (T) of `(SL₂(ℤ) ⋉ ℤ², ℤ²)`; see also [Burger][Burger1991]. An
elementary version with external permutations of a spectator, built on a uniform Fourier gap, is
in OpenAI's Lean development, the file
[`AffineSampling.lean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/AffineSampling.lean)
at revision `7ef5c0cc`: `ExactDerandomization.Analysis.Square.square_gap`, with the external
permutations `u` in `changeF`. The same file lifts it to frames (`slice_frame`, `frame_gap`,
`slice_gap`). The statements and the proof here are independent of that code, which was not
consulted: they are derived from `sum_norm_sq_le_shearTranslation`.

## Main definitions

* `Cslib.RotationMap.twistedShearTranslationMove`: the shears and translations of the second
  coordinate of `X × (ZMod n × ZMod n)`, with the shears also permuting `X`.

## Main results

* `Cslib.RotationMap.sum_norm_sq_le_dual_shearTranslation`: the Poincaré inequality on the
  frequencies.
* `Cslib.RotationMap.sum_norm_sq_sub_fiber_le_twistedShearTranslation`,
  `Cslib.RotationMap.expect_sq_sub_expect_fiber_le_twistedShearTranslation`: the relative
  Poincaré inequality with a spectator.

## References

* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace]
* [M. Burger, *Kazhdan constants for SL(3, ℤ)*][Burger1991]
-/

public section

open Finset
open scoped BigOperators

namespace Cslib.RotationMap

variable {n : ℕ} [NeZero n]

/-- **The Poincaré inequality for shears and translations, on the frequencies**: a function `Φ` on
`ZMod n × ZMod n` vanishing at `0` has squared norm at most `512` times the sum of its squared
changes along the dual unit shears and of its squared norm weighted by the translation weights
`‖e (ξ.1) - 1‖ ^ 2` and `‖e (ξ.2) - 1‖ ^ 2`, where `e = ZMod.stdAddChar`. -/
theorem sum_norm_sq_le_dual_shearTranslation (Φ : ZMod n × ZMod n → ℂ) (h0 : Φ 0 = 0) :
    ∑ ξ, ‖Φ ξ‖ ^ 2 ≤ 512 * (∑ ξ, ‖Φ (shearSnd (-1) ξ) - Φ ξ‖ ^ 2 +
      ∑ ξ, ‖Φ (shearFst (-1) ξ) - Φ ξ‖ ^ 2 +
      ∑ ξ, ‖ZMod.stdAddChar ξ.1 - 1‖ ^ 2 * ‖Φ ξ‖ ^ 2 +
      ∑ ξ, ‖ZMod.stdAddChar ξ.2 - 1‖ ^ 2 * ‖Φ ξ‖ ^ 2) := by
  obtain ⟨f, rfl⟩ := ZMod.dftProd_surjective Φ
  have hf : ∑ v, f v = 0 := by rwa [ZMod.dftProd_zero] at h0
  have hP := sum_norm_sq_le_shearTranslation f hf
  simp only [Fin.sum_univ_four, shearTranslationMove, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Equiv.coe_addRight] at hP
  have e₁ := ZMod.sum_norm_sq_dftProd_shearFst_sub f f 1
  have e₂ := ZMod.sum_norm_sq_dftProd_shearSnd_sub f f 1
  have e₃ := ZMod.sum_norm_sq_dftProd_translate f (1, 0)
  have e₄ := ZMod.sum_norm_sq_dftProd_translate f (0, 1)
  simp only [mul_one, mul_zero, add_zero, zero_add] at e₃ e₄
  have hM := ZMod.sum_norm_sq_dftProd f
  have hn : (0 : ℝ) ≤ (n : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left hP hn
  rw [hM, e₁, e₂, e₃, e₄]
  linarith

omit [NeZero n] in
/-- Only the zero vector is sheared to zero. -/
private theorem shearFst_eq_zero_iff (k : ZMod n) (ξ : ZMod n × ZMod n) :
    shearFst k ξ = 0 ↔ ξ = 0 := by
  have h0 : shearFst k (0 : ZMod n × ZMod n) = 0 := by simp [shearFst_apply]
  exact ⟨fun h ↦ (shearFst k).injective (h.trans h0.symm), fun h ↦ h ▸ h0⟩

omit [NeZero n] in
private theorem shearSnd_eq_zero_iff (k : ZMod n) (ξ : ZMod n × ZMod n) :
    shearSnd k ξ = 0 ↔ ξ = 0 := by
  have h0 : shearSnd k (0 : ZMod n × ZMod n) = 0 := by simp [shearSnd_apply]
  exact ⟨fun h ↦ (shearSnd k).injective (h.trans h0.symm), fun h ↦ h ▸ h0⟩

variable {X : Type*}

/-- The shears and translations of the second coordinate of `X × (ZMod n × ZMod n)`, with the
shears also permuting the spectator coordinate: `(x, w) ↦ (π₁ x, shearFst 1 w)`,
`(x, w) ↦ (π₂ x, shearSnd 1 w)`, `(x, w) ↦ (x, w + (1, 0))` and `(x, w) ↦ (x, w + (0, 1))`. -/
@[expose]
def twistedShearTranslationMove (π₁ π₂ : Equiv.Perm X) (n : ℕ) :
    Fin 4 → Equiv.Perm (X × (ZMod n × ZMod n)) :=
  ![π₁.prodCongr (shearFst 1), π₂.prodCongr (shearSnd 1),
    (Equiv.refl X).prodCongr (Equiv.addRight (1, 0)),
    (Equiv.refl X).prodCongr (Equiv.addRight (0, 1))]

/-- The reverse triangle inequality for the `ℓ²` norm of complex functions on a finite set. -/
private theorem sq_sqrt_sub_sqrt_le [Fintype X] (a b : X → ℂ) :
    (√(∑ x, ‖a x‖ ^ 2) - √(∑ x, ‖b x‖ ^ 2)) ^ 2 ≤ ∑ x, ‖a x - b x‖ ^ 2 := by
  have h := abs_norm_sub_norm_le (WithLp.toLp 2 a : EuclideanSpace ℂ X) (WithLp.toLp 2 b)
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq] at h
  simp only [PiLp.sub_apply] at h
  calc _ = |√(∑ x, ‖a x‖ ^ 2) - √(∑ x, ‖b x‖ ^ 2)| ^ 2 := (sq_abs _).symm
    _ ≤ √(∑ x, ‖a x - b x‖ ^ 2) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) h 2
    _ = _ := Real.sq_sqrt (sum_nonneg fun _ _ ↦ by positivity)

variable [Fintype X]

/-- **The relative Poincaré inequality for shears and translations**, uniformly in `n` and with a
spectator: every complex function `f` on `X × (ZMod n × ZMod n)` is within `512` times its total
squared change along the four moves of its averages over the fibers `{x} × (ZMod n × ZMod n)`. -/
theorem sum_norm_sq_sub_fiber_le_twistedShearTranslation (π₁ π₂ : Equiv.Perm X)
    (f : X × (ZMod n × ZMod n) → ℂ) :
    ∑ p, ‖f p - (∑ w, f (p.1, w)) / (n : ℂ) ^ 2‖ ^ 2 ≤
      512 * ∑ k, ∑ p, ‖f (twistedShearTranslationMove π₁ π₂ n k p) - f p‖ ^ 2 := by
  have hn : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  have hnC : (n : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.2 (NeZero.ne n))
  -- The transforms of the fibers, and of the fibers minus their averages.
  set F : X → ZMod n × ZMod n → ℂ := fun x ↦ ZMod.dftProd fun w ↦ f (x, w) with hF
  set g : X → ℂ := fun x ↦ (∑ w, f (x, w)) / (n : ℂ) ^ 2 with hg
  have hcard : (Fintype.card (ZMod n × ZMod n) : ℂ) = (n : ℂ) ^ 2 := by
    simp [Fintype.card_prod, ZMod.card, sq]
  have hdft (x : X) (ξ : ZMod n × ZMod n) :
      ‖ZMod.dftProd (fun w ↦ f (x, w) - g x) ξ‖ ^ 2 = if ξ = 0 then 0 else ‖F x ξ‖ ^ 2 := by
    split_ifs with hξ
    · subst hξ
      rw [ZMod.dftProd_zero, sum_sub_distrib, sum_const, card_univ, nsmul_eq_mul, hcard]
      simp only [hg]
      rw [mul_div_cancel₀ _ hnC, sub_self, norm_zero, sq, mul_zero]
    · have : (fun w ↦ f (x, w) - g x) = (fun w ↦ f (x, w)) - fun _ ↦ g x := rfl
      rw [this, ZMod.dftProd_sub, Pi.sub_apply, ZMod.dftProd_const_of_ne_zero _ hξ, sub_zero]
  -- The function on the frequencies: the `ℓ²` norm over `X` of the nonzero frequencies.
  set ψ : ZMod n × ZMod n → ℝ := fun ξ ↦ if ξ = 0 then 0 else √(∑ x, ‖F x ξ‖ ^ 2) with hψ
  have hψsq (ξ : ZMod n × ZMod n) :
      ‖(ψ ξ : ℂ)‖ ^ 2 = ∑ x, if ξ = 0 then 0 else ‖F x ξ‖ ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    simp only [hψ]
    split_ifs
    · simp
    · exact Real.sq_sqrt (sum_nonneg fun _ _ ↦ by positivity)
  have hmain := sum_norm_sq_le_dual_shearTranslation (fun ξ ↦ (ψ ξ : ℂ)) (by simp [hψ])
  -- The mass of `ψ` is that of the fibers minus their averages.
  have hL : ∑ ξ, ‖(ψ ξ : ℂ)‖ ^ 2 =
      (n : ℝ) ^ 2 * ∑ p, ‖f p - (∑ w, f (p.1, w)) / (n : ℂ) ^ 2‖ ^ 2 := by
    calc ∑ ξ, ‖(ψ ξ : ℂ)‖ ^ 2 = ∑ x, ∑ ξ, if ξ = 0 then 0 else ‖F x ξ‖ ^ 2 := by
          simp only [hψsq]
          exact sum_comm
      _ = ∑ x, ∑ ξ, ‖ZMod.dftProd (fun w ↦ f (x, w) - g x) ξ‖ ^ 2 := by simp only [hdft]
      _ = ∑ x, (n : ℝ) ^ 2 * ∑ w, ‖f (x, w) - g x‖ ^ 2 :=
          sum_congr rfl fun x _ ↦ ZMod.sum_norm_sq_dftProd _
      _ = _ := by rw [← mul_sum, Fintype.sum_prod_type]
  -- The changes of `ψ` along the dual shears are at most those of `F`.
  have hshear (π : Equiv.Perm X) (s : Equiv.Perm (ZMod n × ZMod n)) (hs : ∀ ξ, s ξ = 0 ↔ ξ = 0)
      (ξ : ZMod n × ZMod n) :
      ‖(ψ (s ξ) : ℂ) - ψ ξ‖ ^ 2 ≤ ∑ x, ‖F (π x) (s ξ) - F x ξ‖ ^ 2 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    by_cases hξ : ξ = 0
    · subst hξ
      have h0 : s 0 = 0 := (hs 0).2 rfl
      have e : ψ (s 0) - ψ 0 = 0 := by simp only [hψ, h0, ite_true, sub_self]
      rw [e, sq, mul_zero]
      exact sum_nonneg fun _ _ ↦ by positivity
    · have : s ξ ≠ 0 := fun h ↦ hξ ((hs ξ).1 h)
      simp only [hψ, this, hξ, ite_false]
      rw [← Equiv.sum_comp π fun x ↦ ‖F x (s ξ)‖ ^ 2]
      exact sq_sqrt_sub_sqrt_le (fun x ↦ F (π x) (s ξ)) (fun x ↦ F x ξ)
  have hS₁ : ∑ ξ, ‖(ψ (shearSnd (-1) ξ) : ℂ) - ψ ξ‖ ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ p, ‖f (twistedShearTranslationMove π₁ π₂ n 0 p) - f p‖ ^ 2 := by
    calc _ ≤ ∑ ξ, ∑ x, ‖F (π₁ x) (shearSnd (-1) ξ) - F x ξ‖ ^ 2 :=
          sum_le_sum fun ξ _ ↦ hshear π₁ _ (shearSnd_eq_zero_iff _) ξ
      _ = _ := by
        rw [sum_comm, Fintype.sum_prod_type, mul_sum]
        refine sum_congr rfl fun x _ ↦ ?_
        exact ZMod.sum_norm_sq_dftProd_shearFst_sub (fun w ↦ f (π₁ x, w)) (fun w ↦ f (x, w)) 1
  have hS₂ : ∑ ξ, ‖(ψ (shearFst (-1) ξ) : ℂ) - ψ ξ‖ ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ p, ‖f (twistedShearTranslationMove π₁ π₂ n 1 p) - f p‖ ^ 2 := by
    calc _ ≤ ∑ ξ, ∑ x, ‖F (π₂ x) (shearFst (-1) ξ) - F x ξ‖ ^ 2 :=
          sum_le_sum fun ξ _ ↦ hshear π₂ _ (shearFst_eq_zero_iff _) ξ
      _ = _ := by
        rw [sum_comm, Fintype.sum_prod_type, mul_sum]
        refine sum_congr rfl fun x _ ↦ ?_
        exact ZMod.sum_norm_sq_dftProd_shearSnd_sub (fun w ↦ f (π₂ x, w)) (fun w ↦ f (x, w)) 1
  -- The translation weights of `ψ` are those of `F`.
  have hweight (c : ZMod n × ZMod n → ℝ) (hc : ∀ ξ, 0 ≤ c ξ) :
      ∑ ξ, c ξ * ‖(ψ ξ : ℂ)‖ ^ 2 ≤ ∑ x, ∑ ξ, c ξ * ‖F x ξ‖ ^ 2 := by
    rw [sum_comm]
    refine sum_le_sum fun ξ _ ↦ ?_
    rw [hψsq, mul_sum]
    refine sum_le_sum fun x _ ↦ ?_
    split_ifs
    · have := hc ξ
      simp only [mul_zero]
      positivity
    · exact le_rfl
  have hT₁ : ∑ ξ, ‖ZMod.stdAddChar ξ.1 - 1‖ ^ 2 * ‖(ψ ξ : ℂ)‖ ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ p, ‖f (twistedShearTranslationMove π₁ π₂ n 2 p) - f p‖ ^ 2 := by
    refine (hweight _ fun _ ↦ by positivity).trans_eq ?_
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    have := ZMod.sum_norm_sq_dftProd_translate (fun w ↦ f (x, w)) (1, 0)
    simp only [mul_one, mul_zero, add_zero] at this
    exact this
  have hT₂ : ∑ ξ, ‖ZMod.stdAddChar ξ.2 - 1‖ ^ 2 * ‖(ψ ξ : ℂ)‖ ^ 2 ≤
      (n : ℝ) ^ 2 * ∑ p, ‖f (twistedShearTranslationMove π₁ π₂ n 3 p) - f p‖ ^ 2 := by
    refine (hweight _ fun _ ↦ by positivity).trans_eq ?_
    rw [Fintype.sum_prod_type, mul_sum]
    refine sum_congr rfl fun x _ ↦ ?_
    have := ZMod.sum_norm_sq_dftProd_translate (fun w ↦ f (x, w)) (0, 1)
    simp only [mul_one, mul_zero, zero_add] at this
    exact this
  refine le_of_mul_le_mul_left ?_ hn
  rw [← hL, Fin.sum_univ_four, mul_left_comm]
  linarith

/-- **The relative Poincaré inequality for shears and translations**, for real functions and
averages: the second moment of `f` about its averages over the fibers `{x} × (ZMod n × ZMod n)` is
at most `512` times the sum of its mean squared changes along the four moves. -/
theorem expect_sq_sub_expect_fiber_le_twistedShearTranslation (π₁ π₂ : Equiv.Perm X)
    (f : X × (ZMod n × ZMod n) → ℝ) :
    𝔼 p, (f p - 𝔼 w, f (p.1, w)) ^ 2 ≤
      512 * ∑ k, 𝔼 p, (f (twistedShearTranslationMove π₁ π₂ n k p) - f p) ^ 2 := by
  have h := sum_norm_sq_sub_fiber_le_twistedShearTranslation π₁ π₂ fun p ↦ (f p : ℂ)
  have hfib (x : X) : (∑ w, (f (x, w) : ℂ)) / (n : ℂ) ^ 2 = ((𝔼 w, f (x, w) : ℝ) : ℂ) := by
    rw [Fintype.expect_eq_sum_div_card, Fintype.card_prod, ZMod.card]
    push_cast
    ring
  simp only [hfib, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] at h
  simp only [Fintype.expect_eq_sum_div_card, ← sum_div]
  rw [← mul_div_assoc]
  exact div_le_div_of_nonneg_right (by simpa [Fintype.expect_eq_sum_div_card] using h)
    (Nat.cast_nonneg _)

end Cslib.RotationMap
