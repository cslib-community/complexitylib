/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Combinatorics.Expander.Lazy
public import Complexity.Foundations.Combinatorics.Expander.Perm
public import Complexity.Foundations.Algebra.Shear
public import Mathlib.Data.ZMod.Basic
import Complexity.Foundations.Analysis.Fourier.ZModProd
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Data.ZMod.ValMinAbs

/-!
# The shear-translation expander on `ZMod n × ZMod n`

The four moves `(x, y) ↦ (x + y, y)`, `(x, y) ↦ (x, y + x)`, `(x, y) ↦ (x + 1, y)` and
`(x, y) ↦ (x, y + 1)` of `ZMod n × ZMod n` and their inverses form an `8`-regular multigraph
(`shearTranslation n`). It is an expander uniformly in `n`: its second eigenvalue is at most
`1 - 1 / 4096`, and its lazy version has spectral expansion at most `1 - 1 / 8192`, for every
`n ≥ 1`. It is a variant of the graphs of Margulis [Margulis][Margulis1973] and of Gabber and
Galil [Gabber and Galil][GabberGalil1981], whose expansion the chapter on the Margulis construction
[Hoory, Linial and Wigderson, Section 8][HooryLinialWigderson2006] proves by Fourier analysis
on `ZMod n × ZMod n`, following Jimbo and Maruoka [Jimbo and Maruoka][JimboMaruoka1987]. Here
the translations are separate moves rather than combined with the shears.

The proof is elementary Fourier analysis, organised differently from the cited one. Write `F` for
the discrete Fourier transform of a function `f` of sum zero (`ZMod.dftProd`), so `F 0 = 0`. By
Parseval's identity, the squared changes of `f` along the moves are the corresponding quantities
for `F`: a translation multiplies `F ξ` by a root of unity, which is far from `1` unless `ξ` is a
small frequency, and a shear permutes the frequencies by a shear. So if `f` changes little along
the moves, the mass `‖F ξ‖ ^ 2` lies mostly on small frequencies and is almost invariant under the
dual shears. On the small frequencies, whose centered representatives are at most `n / 11` in
absolute value, the dual shears by `±4` act as integer shears, and they play ping-pong: they move
the frequencies `(a, b)` with `|b| < |a|` to two disjoint sets of frequencies with `|a| < |b|`,
and those with `0 < |b|`, `|a| ≤ |b|` to two disjoint sets with `|b| < |a|`. Each class therefore
carries at least twice the mass of the other, up to small errors, so both are nearly empty. This
is a finite, quantitative argument in the spirit of the proof of the relative property (T) of
`SL₂(ℤ) ⋉ ℤ²` [Burger][Burger1991].

The OpenAI preprint on derandomizing logarithmic space [OpenAI2026LogSpace] derives its uniform
mixing bound from Shalom's property (T) results. The elementary route used here, a Fourier
ping-pong on the small frequencies of `ZMod n × ZMod n` instead of property (T), follows the Lean
development accompanying the preprint, the file
[`AffineSampling.lean`](https://github.com/openai/math/blob/7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a/lean/OAI/Computability/Logspace/AffineSampling.lean)
at revision `7ef5c0cc`, namespace `ExactDerandomization.Analysis.Square`, lemmas `ping` and
`squash`. The proof here is an independent formulation: the frequency box, the shears by `±4`,
the disjoint-image mass transfer, the constants and all names differ. The works of Margulis,
Gabber and Galil, Jimbo and Maruoka, Burger and Hoory, Linial and Wigderson are background.

The explicit constants are far from optimal; the point is that they do not depend on `n`.

## Main definitions

* `Cslib.RotationMap.shearTranslationMove`: the four moves of the graph.
* `Cslib.RotationMap.shearTranslation`: the `8`-regular shear-translation multigraph on
  `ZMod n × ZMod n`.

## Main results

* `Cslib.RotationMap.sum_norm_sq_le_shearTranslation`: the Poincaré inequality
  `∑ v, ‖f v‖ ^ 2 ≤ 512 * ∑ k, ∑ v, ‖f (shearTranslationMove n k v) - f v‖ ^ 2` for every
  complex function of sum zero.
* `Cslib.RotationMap.secondEigenvalue_shearTranslation_le`: `λ₂ ≤ 1 - 1 / 4096`.
* `Cslib.RotationMap.spectralExpansion_lazy_shearTranslation_le`: the lazy graph has spectral
  expansion at most `1 - 1 / 8192`.

## References

* [G. A. Margulis, *Explicit constructions of concentrators*][Margulis1973]
* [O. Gabber, Z. Galil, *Explicit constructions of linear-sized
  superconcentrators*][GabberGalil1981]
* [S. Jimbo, A. Maruoka, *Expanders obtained from affine transformations*][JimboMaruoka1987]
* [M. Burger, *Kazhdan constants for SL(3, ℤ)*][Burger1991]
* [S. Hoory, N. Linial, A. Wigderson, *Expander graphs and their
  applications*][HooryLinialWigderson2006]
* [OpenAI, *Exact Derandomization of Logarithmic Space: L = RL = BPL*][OpenAI2026LogSpace],
  and its Lean development, the file `AffineSampling.lean` linked above (revision `7ef5c0cc`,
  `ExactDerandomization.Analysis.Square.ping`, `squash`), for the elementary route
-/

@[expose] public section

namespace Cslib

open Finset

namespace RotationMap

/-- The four moves of the shear-translation graph on `ZMod n × ZMod n`: the shears
`(x, y) ↦ (x + y, y)` and `(x, y) ↦ (x, y + x)` and the translations by `(1, 0)` and `(0, 1)`. -/
def shearTranslationMove (n : ℕ) : Fin 4 → Equiv.Perm (ZMod n × ZMod n) :=
  ![shearFst 1, shearSnd 1, Equiv.addRight (1, 0), Equiv.addRight (0, 1)]

/-- The **shear-translation graph** on `ZMod n × ZMod n`: the `8`-regular multigraph of the two
unit shears and the two unit translations, a variant of the Margulis–Gabber–Galil graphs
[Hoory, Linial and Wigderson, Section 8][HooryLinialWigderson2006]. -/
def shearTranslation (n : ℕ) : RotationMap (ZMod n × ZMod n) (Fin 4 × Bool) :=
  ofPerms (shearTranslationMove n)

/-! ### Squared changes along permutations -/

section Energy

variable {α : Type*} [Fintype α]

/-- The squared change of `f` along `σ ^ m` is at most `m ^ 2` times that along `σ`. -/
private theorem sum_norm_sub_sq_pow_le (f : α → ℂ) (σ : Equiv.Perm α) (m : ℕ) :
    ∑ v, ‖f ((σ ^ m) v) - f v‖ ^ 2 ≤ m ^ 2 * ∑ v, ‖f (σ v) - f v‖ ^ 2 := by
  have htel (v : α) : f ((σ ^ m) v) - f v =
      ∑ j ∈ range m, (f (σ ((σ ^ j) v)) - f ((σ ^ j) v)) := by
    have := Finset.sum_range_sub (fun j ↦ f ((σ ^ j) v)) m
    simp only [pow_succ', Equiv.Perm.mul_apply, pow_zero, Equiv.Perm.one_apply] at this
    exact this.symm
  calc ∑ v, ‖f ((σ ^ m) v) - f v‖ ^ 2
      ≤ ∑ v, m * ∑ j ∈ range m, ‖f (σ ((σ ^ j) v)) - f ((σ ^ j) v)‖ ^ 2 := by
        refine sum_le_sum fun v _ ↦ ?_
        rw [htel]
        calc ‖∑ j ∈ range m, (f (σ ((σ ^ j) v)) - f ((σ ^ j) v))‖ ^ 2
            ≤ (∑ j ∈ range m, ‖f (σ ((σ ^ j) v)) - f ((σ ^ j) v)‖) ^ 2 := by
              gcongr
              exact norm_sum_le _ _
          _ ≤ _ := by
              simpa using sq_sum_le_card_mul_sum_sq (s := range m)
                (f := fun j ↦ ‖f (σ ((σ ^ j) v)) - f ((σ ^ j) v)‖)
    _ = m * ∑ j ∈ range m, ∑ v, ‖f (σ ((σ ^ j) v)) - f ((σ ^ j) v)‖ ^ 2 := by
        rw [← mul_sum, sum_comm]
    _ = m * ∑ _j ∈ range m, ∑ v, ‖f (σ v) - f v‖ ^ 2 := by
        congr 1
        exact sum_congr rfl fun j _ ↦
          Equiv.sum_comp (σ ^ j) (fun v ↦ ‖f (σ v) - f v‖ ^ 2)
    _ = _ := by
        rw [sum_const, card_range, nsmul_eq_mul]
        ring

/-- The squared change of `f` along `σ⁻¹` equals that along `σ`. -/
private theorem sum_norm_sub_sq_symm (f : α → ℂ) (σ : Equiv.Perm α) :
    ∑ v, ‖f (σ.symm v) - f v‖ ^ 2 = ∑ v, ‖f (σ v) - f v‖ ^ 2 := by
  rw [← Equiv.sum_comp σ]
  simp [norm_sub_rev]

/-- **Mass transfer**: moving a set of points by a permutation `g` changes the mass `‖F z‖ ^ 2`
on it by at most `8` times the squared change of `F` along `g` plus `1 / 8` of the total mass. -/
private theorem sum_norm_sq_le_sum_comp (F : α → ℂ) (g : Equiv.Perm α) (E : Finset α) :
    ∑ z ∈ E, ‖F z‖ ^ 2 ≤
      ∑ z ∈ E, ‖F (g z)‖ ^ 2 + 8 * ∑ z, ‖F (g z) - F z‖ ^ 2 + (∑ z, ‖F z‖ ^ 2) / 8 := by
  have hpt (x y : ℂ) : ‖x‖ ^ 2 ≤ ‖y‖ ^ 2 + 8 * ‖y - x‖ ^ 2 + (‖x‖ ^ 2 + ‖y‖ ^ 2) / 16 := by
    have h : ‖x‖ - ‖y‖ ≤ ‖y - x‖ := by
      rw [norm_sub_rev]
      exact norm_sub_norm_le x y
    nlinarith [mul_le_mul_of_nonneg_right h (add_nonneg (norm_nonneg x) (norm_nonneg y)),
      sq_nonneg (‖x‖ + ‖y‖ - 16 * ‖y - x‖), sq_nonneg (‖x‖ - ‖y‖)]
  have hE (u : α → ℝ) (hu : ∀ z, 0 ≤ u z) : ∑ z ∈ E, u z ≤ ∑ z, u z :=
    sum_le_univ_sum_of_nonneg hu
  have hg : ∑ z, ‖F (g z)‖ ^ 2 = ∑ z, ‖F z‖ ^ 2 := Equiv.sum_comp g fun z ↦ ‖F z‖ ^ 2
  calc ∑ z ∈ E, ‖F z‖ ^ 2
      ≤ ∑ z ∈ E, (‖F (g z)‖ ^ 2 + 8 * ‖F (g z) - F z‖ ^ 2 +
          (‖F z‖ ^ 2 + ‖F (g z)‖ ^ 2) / 16) := sum_le_sum fun z _ ↦ hpt _ _
    _ = ∑ z ∈ E, ‖F (g z)‖ ^ 2 + 8 * ∑ z ∈ E, ‖F (g z) - F z‖ ^ 2 +
          (∑ z ∈ E, ‖F z‖ ^ 2 + ∑ z ∈ E, ‖F (g z)‖ ^ 2) / 16 := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, ← sum_div, sum_add_distrib]
    _ ≤ _ := by
        have h₁ := hE (fun z ↦ ‖F (g z) - F z‖ ^ 2) fun _ ↦ by positivity
        have h₂ := hE (fun z ↦ ‖F z‖ ^ 2) fun _ ↦ by positivity
        have h₃ := hE (fun z ↦ ‖F (g z)‖ ^ 2) fun _ ↦ by positivity
        linarith

omit [Fintype α] in
/-- **Two disjoint images**: if `g₁` and `g₂` map `E` into `T` with disjoint images, the mass of
`T` is at least the masses of the two images together. -/
private theorem sum_comp_add_sum_comp_le (F : α → ℂ) (g₁ g₂ : Equiv.Perm α)
    (E T : Finset α) (h₁ : ∀ z ∈ E, g₁ z ∈ T) (h₂ : ∀ z ∈ E, g₂ z ∈ T)
    (hd : ∀ z ∈ E, ∀ w ∈ E, g₁ z ≠ g₂ w) :
    ∑ z ∈ E, ‖F (g₁ z)‖ ^ 2 + ∑ z ∈ E, ‖F (g₂ z)‖ ^ 2 ≤ ∑ z ∈ T, ‖F z‖ ^ 2 := by
  classical
  have hmap (g : Equiv.Perm α) : ∑ z ∈ E, ‖F (g z)‖ ^ 2 =
      ∑ z ∈ E.map g.toEmbedding, ‖F z‖ ^ 2 := by
    rw [sum_map]
    rfl
  rw [hmap, hmap, ← sum_union]
  · refine sum_le_sum_of_subset_of_nonneg (fun w hw ↦ ?_) fun _ _ _ ↦ by positivity
    rcases mem_union.1 hw with hw | hw <;> obtain ⟨z, hz, rfl⟩ := mem_map.1 hw
    exacts [h₁ z hz, h₂ z hz]
  · refine disjoint_left.2 fun w hw₁ hw₂ ↦ ?_
    obtain ⟨z, hz, rfl⟩ := mem_map.1 hw₁
    obtain ⟨z', hz', hzz'⟩ := mem_map.1 hw₂
    exact hd z hz z' hz' hzz'.symm

end Energy

/-! ### Small frequencies -/

section Frequencies

variable {n : ℕ} [NeZero n]

/-- On small frequencies, a shear by at most `4` acts on the centered representatives as the
integer shear. -/
private theorem valMinAbs_add_mul {a b : ZMod n} {k : ℤ} (hk : |k| ≤ 4)
    (ha : 11 * |a.valMinAbs| ≤ n) (hb : 11 * |b.valMinAbs| ≤ n) :
    (a + k * b).valMinAbs = a.valMinAbs + k * b.valMinAbs := by
  rw [ZMod.valMinAbs_spec]
  refine ⟨by push_cast [ZMod.coe_valMinAbs]; rfl, ?_⟩
  have hn : (0 : ℤ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have h₁ : |a.valMinAbs + k * b.valMinAbs| ≤ |a.valMinAbs| + |k| * |b.valMinAbs| :=
    (abs_add_le _ _).trans_eq (by rw [abs_mul])
  have h₂ : |k| * |b.valMinAbs| ≤ 4 * |b.valMinAbs| :=
    mul_le_mul_of_nonneg_right hk (abs_nonneg _)
  have h₃ := neg_abs_le (a.valMinAbs + k * b.valMinAbs)
  have h₄ := le_abs_self (a.valMinAbs + k * b.valMinAbs)
  constructor <;> linarith

/-- The ping-pong inequality: a shear by `±4` moves a frequency `(p, q)` with `|p| ≤ |q|` and
`q ≠ 0` to one whose first coordinate is larger than the second. -/
private theorem abs_lt_abs_add_mul {p q k : ℤ} (hk : |k| = 4) (hpq : |p| ≤ |q|) (hq : q ≠ 0) :
    |q| < |p + k * q| := by
  have h : |k * q| ≤ |p + k * q| + |p| := by
    have := abs_sub (p + k * q) p
    rwa [add_sub_cancel_left] at this
  rw [abs_mul, hk] at h
  have := abs_pos.2 hq
  linarith

/-- The images of a frequency `(p, q)` with `|p| ≤ |q|` under the shears by `4` and `-4` differ. -/
private theorem add_four_mul_ne {p p' q : ℤ} (hp : |p| ≤ |q|) (hp' : |p'| ≤ |q|) (hq : q ≠ 0) :
    p + 4 * q ≠ p' + -4 * q := by
  intro h
  have h' : p' - p = 8 * q := by linarith
  have h₁ : |p' - p| ≤ |p'| + |p| := abs_sub _ _
  rw [h', abs_mul, show |(8 : ℤ)| = 8 by norm_num] at h₁
  have := abs_pos.2 hq
  linarith

/-- A frequency outside the small box is moved far by one of the unit translations: the
corresponding root of unity is at distance at least `1 / sqrt 8` from `1`. -/
private theorem one_div_eight_le_norm_stdAddChar_sub_one {a : ZMod n}
    (ha : (n : ℤ) < 11 * |a.valMinAbs|) : 1 / 8 ≤ ‖ZMod.stdAddChar a - 1‖ ^ 2 := by
  set A := a.valMinAbs with hA
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
  have hhalf : 2 * |(A : ℝ)| ≤ n := by
    have h := ZMod.natAbs_valMinAbs_le a
    have : 2 * A.natAbs ≤ n := by omega
    rw [← Int.cast_abs, ← Int.natCast_natAbs]
    exact_mod_cast this
  have hbig : (n : ℝ) < 11 * |(A : ℝ)| := by
    rw [← Int.cast_abs]
    exact_mod_cast ha
  have hexp : ZMod.stdAddChar a = Complex.exp (Complex.I * ((2 * Real.pi * A / n : ℝ) : ℂ)) := by
    conv_lhs => rw [← ZMod.coe_valMinAbs a, ← hA, ZMod.stdAddChar_coe]
    congr 1
    push_cast
    ring
  rw [hexp, Complex.norm_exp_I_mul_ofReal_sub_one, norm_mul, Real.norm_eq_abs,
    Real.norm_eq_abs, abs_two]
  have hsin : 2 / 11 ≤ |Real.sin (2 * Real.pi * A / n / 2)| := by
    have hx : 2 * Real.pi * A / n / 2 = Real.pi * A / n := by ring
    have hxabs : |Real.sin (Real.pi * A / n)| = Real.sin (Real.pi * |(A : ℝ)| / n) := by
      have hle : Real.pi * |(A : ℝ)| / n ≤ Real.pi := by
        rw [div_le_iff₀ hn]
        nlinarith [Real.pi_pos, abs_nonneg (A : ℝ)]
      have hs := Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) hle
      rcases le_or_gt 0 (A : ℝ) with h | h
      · rw [abs_of_nonneg h] at hs ⊢
        exact abs_of_nonneg hs
      · have e : Real.sin (Real.pi * -(A : ℝ) / n) = -Real.sin (Real.pi * A / n) := by
          rw [mul_neg, neg_div, Real.sin_neg]
        rw [abs_of_neg h, e] at hs ⊢
        exact abs_of_nonpos (by linarith)
    rw [hx, hxabs]
    have hle : Real.pi * |(A : ℝ)| / n ≤ Real.pi / 2 := by
      rw [div_le_iff₀ hn]
      nlinarith [Real.pi_pos]
    have := Real.mul_le_sin (by positivity) hle
    have heq : 2 / Real.pi * (Real.pi * |(A : ℝ)| / n) = 2 * |(A : ℝ)| / n := by
      field_simp
    rw [heq] at this
    have : 2 / 11 ≤ 2 * |(A : ℝ)| / n := by
      rw [le_div_iff₀ hn]
      linarith
    linarith
  nlinarith [abs_nonneg (Real.sin (2 * Real.pi * A / n / 2))]

end Frequencies

/-! ### The ping-pong argument on the frequencies -/

section PingPong

variable {n : ℕ} [NeZero n]

/-- The frequencies whose centered representatives are both at most `n / 11` in absolute value. -/
private def IsSmall (ξ : ZMod n × ZMod n) : Prop :=
  11 * |ξ.1.valMinAbs| ≤ n ∧ 11 * |ξ.2.valMinAbs| ≤ n

private instance : DecidablePred (IsSmall (n := n)) := fun _ ↦ instDecidableAnd

/-- **The ping-pong inequality** for a function on the frequencies vanishing at `0`: its mass is
at most `6` times its mass outside the small box plus `16` times its squared changes along the
four dual shears by `±4`. -/
private theorem sum_norm_sq_le_pingPong (F : ZMod n × ZMod n → ℂ) (h0 : F 0 = 0) :
    ∑ ξ, ‖F ξ‖ ^ 2 ≤ 6 * ∑ ξ ∈ univ.filter (fun ξ ↦ ¬ IsSmall ξ), ‖F ξ‖ ^ 2 +
      16 * (∑ ξ, ‖F (shearSnd (4 : ZMod n) ξ) - F ξ‖ ^ 2 +
        ∑ ξ, ‖F (shearSnd (-4 : ZMod n) ξ) - F ξ‖ ^ 2 +
        ∑ ξ, ‖F (shearFst (4 : ZMod n) ξ) - F ξ‖ ^ 2 +
        ∑ ξ, ‖F (shearFst (-4 : ZMod n) ξ) - F ξ‖ ^ 2) := by
  obtain ⟨Out, hOut⟩ : ∃ s : Finset (ZMod n × ZMod n), s = univ.filter (¬ IsSmall ·) :=
    ⟨_, rfl⟩
  obtain ⟨X, hX⟩ : ∃ s : Finset (ZMod n × ZMod n),
      s = univ.filter (fun ξ ↦ IsSmall ξ ∧ |ξ.2.valMinAbs| < |ξ.1.valMinAbs|) := ⟨_, rfl⟩
  obtain ⟨Y, hY⟩ : ∃ s : Finset (ZMod n × ZMod n),
      s = univ.filter (fun ξ ↦ IsSmall ξ ∧ |ξ.1.valMinAbs| ≤ |ξ.2.valMinAbs| ∧ ξ ≠ 0) :=
    ⟨_, rfl⟩
  rw [← hOut]
  have hite (p : Prop) [Decidable p] (ξ : ZMod n × ZMod n) :
      0 ≤ if p then ‖F ξ‖ ^ 2 else 0 := by
    split_ifs <;> positivity
  -- The two classes and the large frequencies cover everything but `0`, where `F` vanishes.
  have hpart : ∑ ξ, ‖F ξ‖ ^ 2 ≤
      ∑ ξ ∈ Out, ‖F ξ‖ ^ 2 + ∑ ξ ∈ X, ‖F ξ‖ ^ 2 + ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 := by
    rw [hOut, hX, hY, sum_filter, sum_filter, sum_filter, ← sum_add_distrib, ← sum_add_distrib]
    refine sum_le_sum fun ξ _ ↦ ?_
    by_cases h : ξ = 0
    · subst h
      simp [h0]
    have h₁ := hite (¬ IsSmall ξ) ξ
    have h₂ := hite (IsSmall ξ ∧ |ξ.2.valMinAbs| < |ξ.1.valMinAbs|) ξ
    have h₃ := hite (IsSmall ξ ∧ |ξ.1.valMinAbs| ≤ |ξ.2.valMinAbs| ∧ ξ ≠ 0) ξ
    by_cases hs : IsSmall ξ
    · by_cases hlt : |ξ.2.valMinAbs| < |ξ.1.valMinAbs|
      · rw [ite_eq_left (show IsSmall ξ ∧ |ξ.2.valMinAbs| < |ξ.1.valMinAbs| from ⟨hs, hlt⟩)]
        linarith
      · rw [ite_eq_left (show IsSmall ξ ∧ |ξ.1.valMinAbs| ≤ |ξ.2.valMinAbs| ∧ ξ ≠ 0 from
          ⟨hs, not_lt.1 hlt, h⟩)]
        linarith
    · rw [ite_eq_left hs]
      linarith
  -- A frequency with a larger second coordinate is small and in `Y`, or large.
  have hY' : ∑ ξ ∈ univ.filter (fun ξ : ZMod n × ZMod n ↦ |ξ.1.valMinAbs| < |ξ.2.valMinAbs|),
      ‖F ξ‖ ^ 2 ≤ ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 + ∑ ξ ∈ Out, ‖F ξ‖ ^ 2 := by
    rw [hOut, hY, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun ξ _ ↦ ?_
    have h₁ := hite (¬ IsSmall ξ) ξ
    have h₃ := hite (IsSmall ξ ∧ |ξ.1.valMinAbs| ≤ |ξ.2.valMinAbs| ∧ ξ ≠ 0) ξ
    by_cases hlt : |ξ.1.valMinAbs| < |ξ.2.valMinAbs|
    · have hne : ξ ≠ 0 := by
        rintro rfl
        simp at hlt
      rw [ite_eq_left hlt]
      by_cases hs : IsSmall ξ
      · rw [ite_eq_left (show IsSmall ξ ∧ |ξ.1.valMinAbs| ≤ |ξ.2.valMinAbs| ∧ ξ ≠ 0 from
          ⟨hs, hlt.le, hne⟩)]
        linarith
      · rw [ite_eq_left hs]
        linarith
    · rw [ite_eq_right hlt]
      linarith
  have hX' : ∑ ξ ∈ univ.filter (fun ξ : ZMod n × ZMod n ↦ |ξ.2.valMinAbs| < |ξ.1.valMinAbs|),
      ‖F ξ‖ ^ 2 ≤ ∑ ξ ∈ X, ‖F ξ‖ ^ 2 + ∑ ξ ∈ Out, ‖F ξ‖ ^ 2 := by
    rw [hOut, hX, sum_filter, sum_filter, sum_filter, ← sum_add_distrib]
    refine sum_le_sum fun ξ _ ↦ ?_
    have h₁ := hite (¬ IsSmall ξ) ξ
    have h₂ := hite (IsSmall ξ ∧ |ξ.2.valMinAbs| < |ξ.1.valMinAbs|) ξ
    by_cases hlt : |ξ.2.valMinAbs| < |ξ.1.valMinAbs|
    · rw [ite_eq_left hlt]
      by_cases hs : IsSmall ξ
      · rw [ite_eq_left (show IsSmall ξ ∧ |ξ.2.valMinAbs| < |ξ.1.valMinAbs| from ⟨hs, hlt⟩)]
        linarith
      · rw [ite_eq_left hs]
        linarith
    · rw [ite_eq_right hlt]
      linarith
  -- The dual shears `(a, b) ↦ (a, b ± 4 a)` move `X` into two disjoint sets of `Y'`.
  have hXY : ∑ ξ ∈ X, ‖F (shearSnd (4 : ZMod n) ξ)‖ ^ 2 +
      ∑ ξ ∈ X, ‖F (shearSnd (-4 : ZMod n) ξ)‖ ^ 2 ≤
      ∑ ξ ∈ univ.filter (fun ξ : ZMod n × ZMod n ↦ |ξ.1.valMinAbs| < |ξ.2.valMinAbs|),
        ‖F ξ‖ ^ 2 := by
    have himage (k : ℤ) (hk : |k| = 4) (ξ : ZMod n × ZMod n) (hξ : ξ ∈ X) :
        (shearSnd (k : ZMod n) ξ).2.valMinAbs = ξ.2.valMinAbs + k * ξ.1.valMinAbs ∧
          |ξ.1.valMinAbs| < |(shearSnd (k : ZMod n) ξ).2.valMinAbs| := by
      simp only [hX, mem_filter, mem_univ, true_and] at hξ
      unfold IsSmall at hξ
      have h := valMinAbs_add_mul (a := ξ.2) (b := ξ.1) hk.le hξ.1.2 hξ.1.1
      refine ⟨h, ?_⟩
      rw [shearSnd_apply, h]
      refine abs_lt_abs_add_mul hk hξ.2.le fun h0 ↦ ?_
      rw [h0, abs_zero] at hξ
      exact (abs_nonneg _).not_gt hξ.2
    refine sum_comp_add_sum_comp_le F _ _ X _ (fun ξ hξ ↦ ?_) (fun ξ hξ ↦ ?_)
      fun ξ hξ ξ' hξ' h ↦ ?_
    · simpa using (himage 4 (by norm_num) ξ hξ).2
    · simpa using (himage (-4) (by norm_num) ξ hξ).2
    · have h₁ := (himage 4 (by norm_num) ξ hξ).1
      have h₂ := (himage (-4) (by norm_num) ξ' hξ').1
      simp only [Int.cast_ofNat, Int.cast_neg] at h₁ h₂
      have hfst : ξ.1 = ξ'.1 := by simpa using congrArg Prod.fst h
      rw [h, h₂, ← hfst] at h₁
      simp only [hX, mem_filter, mem_univ, true_and] at hξ hξ'
      refine add_four_mul_ne hξ.2.le (hfst ▸ hξ'.2.le) ?_ h₁.symm
      intro h0
      rw [h0, abs_zero] at hξ
      exact (abs_nonneg _).not_gt hξ.2
  -- The dual shears `(a, b) ↦ (a ± 4 b, b)` move `Y` into two disjoint sets of `X'`.
  have hYX : ∑ ξ ∈ Y, ‖F (shearFst (4 : ZMod n) ξ)‖ ^ 2 +
      ∑ ξ ∈ Y, ‖F (shearFst (-4 : ZMod n) ξ)‖ ^ 2 ≤
      ∑ ξ ∈ univ.filter (fun ξ : ZMod n × ZMod n ↦ |ξ.2.valMinAbs| < |ξ.1.valMinAbs|),
        ‖F ξ‖ ^ 2 := by
    have hq (ξ : ZMod n × ZMod n) (hξ : ξ ∈ Y) : ξ.2.valMinAbs ≠ 0 := by
      simp only [hY, mem_filter, mem_univ, true_and] at hξ
      intro h0
      rw [h0, abs_zero, abs_nonpos_iff, ZMod.valMinAbs_eq_zero] at hξ
      rw [ZMod.valMinAbs_eq_zero] at h0
      exact hξ.2.2 (Prod.ext hξ.2.1 h0)
    have himage (k : ℤ) (hk : |k| = 4) (ξ : ZMod n × ZMod n) (hξ : ξ ∈ Y) :
        (shearFst (k : ZMod n) ξ).1.valMinAbs = ξ.1.valMinAbs + k * ξ.2.valMinAbs ∧
          |ξ.2.valMinAbs| < |(shearFst (k : ZMod n) ξ).1.valMinAbs| := by
      have hq := hq ξ hξ
      simp only [hY, mem_filter, mem_univ, true_and] at hξ
      unfold IsSmall at hξ
      have h := valMinAbs_add_mul (a := ξ.1) (b := ξ.2) hk.le hξ.1.1 hξ.1.2
      refine ⟨h, ?_⟩
      rw [shearFst_apply, h]
      exact abs_lt_abs_add_mul hk hξ.2.1 hq
    refine sum_comp_add_sum_comp_le F _ _ Y _ (fun ξ hξ ↦ ?_) (fun ξ hξ ↦ ?_)
      fun ξ hξ ξ' hξ' h ↦ ?_
    · simpa using (himage 4 (by norm_num) ξ hξ).2
    · simpa using (himage (-4) (by norm_num) ξ hξ).2
    · have h₁ := (himage 4 (by norm_num) ξ hξ).1
      have h₂ := (himage (-4) (by norm_num) ξ' hξ').1
      simp only [Int.cast_ofNat, Int.cast_neg] at h₁ h₂
      have hsnd : ξ.2 = ξ'.2 := by simpa using congrArg Prod.snd h
      rw [h, h₂, ← hsnd] at h₁
      have hq := hq ξ hξ
      simp only [hY, mem_filter, mem_univ, true_and] at hξ hξ'
      exact add_four_mul_ne hξ.2.1 (hsnd ▸ hξ'.2.1) hq h₁.symm
  -- Mass transfer along each of the four dual shears.
  have t₁ : ∑ ξ ∈ X, ‖F ξ‖ ^ 2 ≤ ∑ ξ ∈ X, ‖F (shearSnd (4 : ZMod n) ξ)‖ ^ 2 +
      8 * ∑ ξ, ‖F (shearSnd (4 : ZMod n) ξ) - F ξ‖ ^ 2 + (∑ ξ, ‖F ξ‖ ^ 2) / 8 :=
    sum_norm_sq_le_sum_comp F _ X
  have t₂ : ∑ ξ ∈ X, ‖F ξ‖ ^ 2 ≤ ∑ ξ ∈ X, ‖F (shearSnd (-4 : ZMod n) ξ)‖ ^ 2 +
      8 * ∑ ξ, ‖F (shearSnd (-4 : ZMod n) ξ) - F ξ‖ ^ 2 + (∑ ξ, ‖F ξ‖ ^ 2) / 8 :=
    sum_norm_sq_le_sum_comp F _ X
  have t₃ : ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 ≤ ∑ ξ ∈ Y, ‖F (shearFst (4 : ZMod n) ξ)‖ ^ 2 +
      8 * ∑ ξ, ‖F (shearFst (4 : ZMod n) ξ) - F ξ‖ ^ 2 + (∑ ξ, ‖F ξ‖ ^ 2) / 8 :=
    sum_norm_sq_le_sum_comp F _ Y
  have t₄ : ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 ≤ ∑ ξ ∈ Y, ‖F (shearFst (-4 : ZMod n) ξ)‖ ^ 2 +
      8 * ∑ ξ, ‖F (shearFst (-4 : ZMod n) ξ) - F ξ‖ ^ 2 + (∑ ξ, ‖F ξ‖ ^ 2) / 8 :=
    sum_norm_sq_le_sum_comp F _ Y
  have s₁ : 2 * ∑ ξ ∈ X, ‖F ξ‖ ^ 2 ≤ (∑ ξ ∈ Y, ‖F ξ‖ ^ 2 + ∑ ξ ∈ Out, ‖F ξ‖ ^ 2) +
      8 * (∑ ξ, ‖F (shearSnd (4 : ZMod n) ξ) - F ξ‖ ^ 2 +
        ∑ ξ, ‖F (shearSnd (-4 : ZMod n) ξ) - F ξ‖ ^ 2) + (∑ ξ, ‖F ξ‖ ^ 2) / 4 := by
    calc 2 * ∑ ξ ∈ X, ‖F ξ‖ ^ 2 = ∑ ξ ∈ X, ‖F ξ‖ ^ 2 + ∑ ξ ∈ X, ‖F ξ‖ ^ 2 := two_mul _
      _ ≤ _ := add_le_add t₁ t₂
      _ = (∑ ξ ∈ X, ‖F (shearSnd (4 : ZMod n) ξ)‖ ^ 2 +
            ∑ ξ ∈ X, ‖F (shearSnd (-4 : ZMod n) ξ)‖ ^ 2) +
          8 * (∑ ξ, ‖F (shearSnd (4 : ZMod n) ξ) - F ξ‖ ^ 2 +
            ∑ ξ, ‖F (shearSnd (-4 : ZMod n) ξ) - F ξ‖ ^ 2) + (∑ ξ, ‖F ξ‖ ^ 2) / 4 := by
          ring
      _ ≤ _ := add_le_add (add_le_add (hXY.trans hY') le_rfl) le_rfl
  have s₂ : 2 * ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 ≤ (∑ ξ ∈ X, ‖F ξ‖ ^ 2 + ∑ ξ ∈ Out, ‖F ξ‖ ^ 2) +
      8 * (∑ ξ, ‖F (shearFst (4 : ZMod n) ξ) - F ξ‖ ^ 2 +
        ∑ ξ, ‖F (shearFst (-4 : ZMod n) ξ) - F ξ‖ ^ 2) + (∑ ξ, ‖F ξ‖ ^ 2) / 4 := by
    calc 2 * ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 = ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 + ∑ ξ ∈ Y, ‖F ξ‖ ^ 2 := two_mul _
      _ ≤ _ := add_le_add t₃ t₄
      _ = (∑ ξ ∈ Y, ‖F (shearFst (4 : ZMod n) ξ)‖ ^ 2 +
            ∑ ξ ∈ Y, ‖F (shearFst (-4 : ZMod n) ξ)‖ ^ 2) +
          8 * (∑ ξ, ‖F (shearFst (4 : ZMod n) ξ) - F ξ‖ ^ 2 +
            ∑ ξ, ‖F (shearFst (-4 : ZMod n) ξ) - F ξ‖ ^ 2) + (∑ ξ, ‖F ξ‖ ^ 2) / 4 := by
          ring
      _ ≤ _ := add_le_add (add_le_add (hYX.trans hX') le_rfl) le_rfl
  linarith only [s₁, s₂, hpart]

end PingPong

/-! ### The Poincaré inequality and the spectral gap -/

section Gap

variable {n : ℕ} [NeZero n]

/-- Parseval's identity for the change of `f` along a translation. -/
private theorem sum_norm_sq_translate (f : ZMod n × ZMod n → ℂ) (t : ZMod n × ZMod n) :
    ∑ ξ, ‖ZMod.stdAddChar (ξ.1 * t.1 + ξ.2 * t.2) - 1‖ ^ 2 * ‖ZMod.dftProd f ξ‖ ^ 2 =
      n ^ 2 * ∑ v, ‖f (v + t) - f v‖ ^ 2 := by
  rw [← ZMod.sum_norm_sq_dftProd (fun v ↦ f (v + t) - f v)]
  refine sum_congr rfl fun ξ _ ↦ ?_
  have : (fun v ↦ f (v + t) - f v) = (fun v ↦ f (v + t)) - f := rfl
  rw [this, ZMod.dftProd_sub, Pi.sub_apply, ZMod.dftProd_comp_add, ← sub_one_mul, norm_mul,
    mul_pow]

/-- Parseval's identity for the change of `f` along the shear `(x, y) ↦ (x + k * y, y)`. -/
private theorem sum_norm_sq_shearFst (f : ZMod n × ZMod n → ℂ) (k : ZMod n) :
    ∑ ξ, ‖ZMod.dftProd f (shearSnd (-k) ξ) - ZMod.dftProd f ξ‖ ^ 2 =
      n ^ 2 * ∑ v, ‖f (shearFst k v) - f v‖ ^ 2 := by
  rw [← ZMod.sum_norm_sq_dftProd (fun v ↦ f (shearFst k v) - f v)]
  refine sum_congr rfl fun ξ _ ↦ ?_
  have : (fun v ↦ f (shearFst k v) - f v) = (fun v ↦ f (v.1 + k * v.2, v.2)) - f := rfl
  rw [this, ZMod.dftProd_sub, Pi.sub_apply, ZMod.dftProd_comp_shearFst, shearSnd_apply, neg_mul,
    ← sub_eq_add_neg]

/-- Parseval's identity for the change of `f` along the shear `(x, y) ↦ (x, y + k * x)`. -/
private theorem sum_norm_sq_shearSnd (f : ZMod n × ZMod n → ℂ) (k : ZMod n) :
    ∑ ξ, ‖ZMod.dftProd f (shearFst (-k) ξ) - ZMod.dftProd f ξ‖ ^ 2 =
      n ^ 2 * ∑ v, ‖f (shearSnd k v) - f v‖ ^ 2 := by
  rw [← ZMod.sum_norm_sq_dftProd (fun v ↦ f (shearSnd k v) - f v)]
  refine sum_congr rfl fun ξ _ ↦ ?_
  have : (fun v ↦ f (shearSnd k v) - f v) = (fun v ↦ f (v.1, v.2 + k * v.1)) - f := rfl
  rw [this, ZMod.dftProd_sub, Pi.sub_apply, ZMod.dftProd_comp_shearSnd, shearFst_apply, neg_mul,
    ← sub_eq_add_neg]

/-- The change along the shears by `4` and `-4` is at most `16` times that along the unit
shear. -/
private theorem sum_norm_sq_shearFst_four_le (f : ZMod n × ZMod n → ℂ) :
    ∑ v, ‖f (shearFst (4 : ZMod n) v) - f v‖ ^ 2 ≤ 16 * ∑ v, ‖f (shearFst 1 v) - f v‖ ^ 2 ∧
      ∑ v, ‖f (shearFst (-4 : ZMod n) v) - f v‖ ^ 2 ≤
        16 * ∑ v, ‖f (shearFst 1 v) - f v‖ ^ 2 := by
  have h4 : shearFst (4 : ZMod n) = shearFst 1 ^ 4 := by
    rw [shearFst_pow]
    norm_num
  have hle := sum_norm_sub_sq_pow_le f (shearFst (1 : ZMod n)) 4
  rw [← h4, show ((4 : ℕ) : ℝ) ^ 2 = 16 by norm_num] at hle
  refine ⟨hle, ?_⟩
  rw [← shearFst_symm, sum_norm_sub_sq_symm]
  exact hle

/-- The change along the shears by `4` and `-4` is at most `16` times that along the unit
shear. -/
private theorem sum_norm_sq_shearSnd_four_le (f : ZMod n × ZMod n → ℂ) :
    ∑ v, ‖f (shearSnd (4 : ZMod n) v) - f v‖ ^ 2 ≤ 16 * ∑ v, ‖f (shearSnd 1 v) - f v‖ ^ 2 ∧
      ∑ v, ‖f (shearSnd (-4 : ZMod n) v) - f v‖ ^ 2 ≤
        16 * ∑ v, ‖f (shearSnd 1 v) - f v‖ ^ 2 := by
  have h4 : shearSnd (4 : ZMod n) = shearSnd 1 ^ 4 := by
    rw [shearSnd_pow]
    norm_num
  have hle := sum_norm_sub_sq_pow_le f (shearSnd (1 : ZMod n)) 4
  rw [← h4, show ((4 : ℕ) : ℝ) ^ 2 = 16 by norm_num] at hle
  refine ⟨hle, ?_⟩
  rw [← shearSnd_symm, sum_norm_sub_sq_symm]
  exact hle

/-- **The Poincaré inequality for the shear-translation graph**, uniformly in `n`: a complex
function of sum zero on `ZMod n × ZMod n` has squared norm at most `512` times its total squared
change along the four moves. -/
theorem sum_norm_sq_le_shearTranslation (f : ZMod n × ZMod n → ℂ) (hf : ∑ v, f v = 0) :
    ∑ v, ‖f v‖ ^ 2 ≤ 512 * ∑ k, ∑ v, ‖f (shearTranslationMove n k v) - f v‖ ^ 2 := by
  set F := ZMod.dftProd f with hF
  have h0 : F 0 = 0 := by simp [F, hf]
  have hpp := sum_norm_sq_le_pingPong F h0
  have hM : ∑ ξ, ‖F ξ‖ ^ 2 = n ^ 2 * ∑ v, ‖f v‖ ^ 2 := ZMod.sum_norm_sq_dftProd f
  -- Large frequencies are paid for by the translations.
  have hOut : ∑ ξ ∈ univ.filter (fun ξ ↦ ¬ IsSmall ξ), ‖F ξ‖ ^ 2 ≤
      8 * (n ^ 2 * ∑ v, ‖f (v + (1, 0)) - f v‖ ^ 2 + n ^ 2 * ∑ v, ‖f (v + (0, 1)) - f v‖ ^ 2) := by
    have hw (ξ : ZMod n × ZMod n) (hs : ¬ IsSmall ξ) :
        1 / 8 ≤ ‖ZMod.stdAddChar ξ.1 - 1‖ ^ 2 + ‖ZMod.stdAddChar ξ.2 - 1‖ ^ 2 := by
      unfold IsSmall at hs
      rcases not_and_or.1 hs with hs | hs
      · linarith [one_div_eight_le_norm_stdAddChar_sub_one (not_le.1 hs),
          sq_nonneg ‖ZMod.stdAddChar ξ.2 - 1‖]
      · linarith [one_div_eight_le_norm_stdAddChar_sub_one (not_le.1 hs),
          sq_nonneg ‖ZMod.stdAddChar ξ.1 - 1‖]
    rw [← sum_norm_sq_translate, ← sum_norm_sq_translate, ← sum_add_distrib, mul_sum, sum_filter]
    refine sum_le_sum fun ξ _ ↦ ?_
    have e₁ : ξ.1 * ((1, 0) : ZMod n × ZMod n).1 + ξ.2 * ((1, 0) : ZMod n × ZMod n).2 = ξ.1 := by
      simp
    have e₂ : ξ.1 * ((0, 1) : ZMod n × ZMod n).1 + ξ.2 * ((0, 1) : ZMod n × ZMod n).2 = ξ.2 := by
      simp
    rw [e₁, e₂]
    split_ifs with hs
    · positivity
    · have := mul_le_mul_of_nonneg_right (hw ξ hs) (sq_nonneg ‖F ξ‖)
      linarith
  -- The dual shears are paid for by the primal shears.
  have hD₁ := sum_norm_sq_shearFst f (-4 : ZMod n)
  have hD₂ := sum_norm_sq_shearFst f (4 : ZMod n)
  have hD₃ := sum_norm_sq_shearSnd f (-4 : ZMod n)
  have hD₄ := sum_norm_sq_shearSnd f (4 : ZMod n)
  rw [neg_neg] at hD₁ hD₃
  rw [← hF] at hD₁ hD₂ hD₃ hD₄
  have e₁ := sum_norm_sq_shearFst_four_le f
  have e₂ := sum_norm_sq_shearSnd_four_le f
  have hn : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne n)
    positivity
  simp only [Fin.sum_univ_four, shearTranslationMove, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons,
    Equiv.coe_addRight]
  rw [← mul_le_mul_iff_right₀ hn]
  have k₁ := mul_le_mul_of_nonneg_left e₁.1 hn.le
  have k₂ := mul_le_mul_of_nonneg_left e₁.2 hn.le
  have k₃ := mul_le_mul_of_nonneg_left e₂.1 hn.le
  have k₄ := mul_le_mul_of_nonneg_left e₂.2 hn.le
  have p₁ : 0 ≤ (n : ℝ) ^ 2 * ∑ v, ‖f (v + (1, 0)) - f v‖ ^ 2 := by positivity
  have p₂ : 0 ≤ (n : ℝ) ^ 2 * ∑ v, ‖f (v + (0, 1)) - f v‖ ^ 2 := by positivity
  linarith

/-- **The spectral gap of the shear-translation graph**, uniformly in `n`: its second eigenvalue
is at most `1 - 1 / 4096`. -/
theorem secondEigenvalue_shearTranslation_le (n : ℕ) [NeZero n] :
    (shearTranslation n).secondEigenvalue ≤ 1 - 1 / 4096 := by
  rcases subsingleton_or_nontrivial (ZMod n × ZMod n) with hV | hV
  · rw [secondEigenvalue_eq_zero_of_subsingleton]
    norm_num
  have h := secondEigenvalue_ofPerms_le (shearTranslationMove n) (c := 1 / 512) fun f hf ↦ ?_
  · rw [shearTranslation]
    refine h.trans_eq ?_
    norm_num
  have hsum : ∑ v, (f v : ℂ) = 0 := by
    rw [Fintype.expect_eq_sum_div_card, div_eq_zero_iff] at hf
    rcases hf with hf | hf
    · exact_mod_cast hf
    · exact absurd hf (by positivity)
  have hP := sum_norm_sq_le_shearTranslation (fun v ↦ (f v : ℂ)) hsum
  simp only [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs] at hP
  simp only [Fintype.expect_eq_sum_div_card, ← sum_div]
  have hcard : (0 : ℝ) < Fintype.card (ZMod n × ZMod n) := by positivity
  rw [← mul_div_assoc, div_le_div_iff_of_pos_right hcard]
  linarith

/-- **The lazy shear-translation graph is an expander** uniformly in `n`: its spectral expansion is
at most `1 - 1 / 8192`. -/
theorem spectralExpansion_lazy_shearTranslation_le (n : ℕ) [NeZero n] :
    (shearTranslation n).lazy.spectralExpansion ≤ 1 - 1 / 8192 := by
  have := (shearTranslation n).spectralExpansion_lazy_le_one_add_secondEigenvalue_div_two
  have := secondEigenvalue_shearTranslation_le n
  linarith

end Gap

end RotationMap

end Cslib
