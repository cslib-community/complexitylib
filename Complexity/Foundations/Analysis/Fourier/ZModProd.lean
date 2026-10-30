/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Complexity.Foundations.Algebra.Shear
import Mathlib.Analysis.Complex.Basic
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

/-!
# The discrete Fourier transform on `ZMod N × ZMod N`

The Fourier transform of `f : ZMod N × ZMod N → ℂ` at the frequency `ξ` is
`∑ v, e (-(ξ.1 * v.1 + ξ.2 * v.2)) * f v`, where `e = ZMod.stdAddChar` sends `j` to
`exp (2 π i j / N)`. This is Mathlib's `ZMod.dft` in each coordinate, written for the two
coordinates together. The characters `v ↦ e (ξ.1 * v.1 + ξ.2 * v.2)` are orthogonal, so the
transform preserves the `ℓ²` norm up to the factor `N ^ 2` (Parseval's identity).

Translations and shears of the plane act on the transform by simple rules: a translation by `t`
multiplies the transform at `ξ` by `e (ξ.1 * t.1 + ξ.2 * t.2)`, and the shear
`(x, y) ↦ (x + k * y, y)` acts on the frequencies by the transposed inverse shear
`(a, b) ↦ (a, b - k * a)`, and symmetrically for `(x, y) ↦ (x, y + k * x)`.

## Main definitions

* `ZMod.dftProd`: the discrete Fourier transform on `ZMod N × ZMod N`.

## Main results

* `ZMod.sum_norm_sq_dftProd`: Parseval's identity
  `∑ ξ, ‖dftProd f ξ‖ ^ 2 = N ^ 2 * ∑ v, ‖f v‖ ^ 2`.
* `ZMod.dftProd_zero`: the transform at the zero frequency is the sum of the values.
* `ZMod.dftProd_comp_add`: translation multiplies the transform by a character value.
* `ZMod.dftProd_comp_shearFst`, `ZMod.dftProd_comp_shearSnd`: shears permute the frequencies.
-/

public section

namespace ZMod

open Finset ComplexConjugate

variable {N : ℕ} [NeZero N]

/-- The discrete Fourier transform of `f : ZMod N × ZMod N → ℂ` at the frequency `ξ`:
`∑ v, e (-(ξ.1 * v.1 + ξ.2 * v.2)) * f v` with `e = ZMod.stdAddChar`. -/
noncomputable def dftProd (f : ZMod N × ZMod N → ℂ) (ξ : ZMod N × ZMod N) : ℂ :=
  ∑ v, stdAddChar (-(ξ.1 * v.1 + ξ.2 * v.2)) * f v

/-- The transform at the zero frequency is the sum of the values. -/
@[simp]
theorem dftProd_zero (f : ZMod N × ZMod N → ℂ) : dftProd f 0 = ∑ v, f v := by
  simp [dftProd]

/-- The transform is additive. -/
theorem dftProd_sub (f g : ZMod N × ZMod N → ℂ) :
    dftProd (f - g) = dftProd f - dftProd g := by
  ext ξ
  simp only [dftProd, Pi.sub_apply, mul_sub, sum_sub_distrib]

/-- **Orthogonality of the characters of `ZMod N × ZMod N`**: summed over all frequencies, a
nontrivial character value vanishes. -/
private theorem sum_stdAddChar_mul_add (u : ZMod N × ZMod N) :
    ∑ ξ : ZMod N × ZMod N, stdAddChar (ξ.1 * u.1 + ξ.2 * u.2) =
      if u = 0 then (N : ℂ) ^ 2 else 0 := by
  simp only [AddChar.map_add_eq_mul, Fintype.sum_prod_type, ← mul_sum, ← sum_mul,
    AddChar.sum_mulShift _ (isPrimitive_stdAddChar N), ZMod.card]
  rcases u with ⟨u₁, u₂⟩
  by_cases h₁ : u₁ = 0 <;> by_cases h₂ : u₂ = 0 <;> simp [h₁, h₂, sq]

/-- **Parseval's identity** on `ZMod N × ZMod N`. -/
theorem sum_norm_sq_dftProd (f : ZMod N × ZMod N → ℂ) :
    ∑ ξ, ‖dftProd f ξ‖ ^ 2 = N ^ 2 * ∑ v, ‖f v‖ ^ 2 := by
  apply Complex.ofReal_injective
  push_cast
  simp only [← Complex.mul_conj', dftProd, map_sum, map_mul, ← AddChar.map_neg_eq_conj, neg_neg,
    sum_mul_sum]
  calc ∑ ξ : ZMod N × ZMod N, ∑ v, ∑ w,
        stdAddChar (-(ξ.1 * v.1 + ξ.2 * v.2)) * f v * (stdAddChar (ξ.1 * w.1 + ξ.2 * w.2) *
          conj (f w))
      = ∑ v, ∑ w, f v * conj (f w) *
          ∑ ξ : ZMod N × ZMod N, stdAddChar (ξ.1 * (w - v).1 + ξ.2 * (w - v).2) := by
        rw [sum_comm]
        refine sum_congr rfl fun v _ ↦ ?_
        rw [sum_comm]
        refine sum_congr rfl fun w _ ↦ ?_
        rw [mul_sum]
        refine sum_congr rfl fun ξ _ ↦ ?_
        have : stdAddChar (ξ.1 * (w - v).1 + ξ.2 * (w - v).2) =
            stdAddChar (-(ξ.1 * v.1 + ξ.2 * v.2)) * stdAddChar (ξ.1 * w.1 + ξ.2 * w.2) := by
          rw [← AddChar.map_add_eq_mul]
          congr 1
          simp only [Prod.fst_sub, Prod.snd_sub]
          ring
        rw [this]
        ring
    _ = (N : ℂ) ^ 2 * ∑ v, f v * conj (f v) := by
        simp only [sum_stdAddChar_mul_add, sub_eq_zero, mul_ite, mul_zero, sum_ite_eq',
          mem_univ, ite_true, mul_sum]
        exact sum_congr rfl fun v _ ↦ by ring

/-- **Translation** multiplies the transform at `ξ` by `e (ξ.1 * t.1 + ξ.2 * t.2)`. -/
theorem dftProd_comp_add (f : ZMod N × ZMod N → ℂ) (t ξ : ZMod N × ZMod N) :
    dftProd (fun v ↦ f (v + t)) ξ = stdAddChar (ξ.1 * t.1 + ξ.2 * t.2) * dftProd f ξ := by
  rw [dftProd, dftProd, mul_sum]
  refine Fintype.sum_equiv (Equiv.addRight t) _ _ fun v ↦ ?_
  simp only [Equiv.coe_addRight, Prod.fst_add, Prod.snd_add, ← mul_assoc,
    ← AddChar.map_add_eq_mul]
  congr 2
  ring

/-- **The shear `(x, y) ↦ (x + k * y, y)`** acts on frequencies by `(a, b) ↦ (a, b - k * a)`. -/
theorem dftProd_comp_shearFst (f : ZMod N × ZMod N → ℂ) (k : ZMod N) (ξ : ZMod N × ZMod N) :
    dftProd (fun v ↦ f (v.1 + k * v.2, v.2)) ξ = dftProd f (ξ.1, ξ.2 - k * ξ.1) := by
  rw [dftProd, dftProd]
  refine Fintype.sum_equiv (Cslib.shearFst k) _ _ fun v ↦ ?_
  rw [Cslib.shearFst_apply]
  congr 2
  ring

/-- **The shear `(x, y) ↦ (x, y + k * x)`** acts on frequencies by `(a, b) ↦ (a - k * b, b)`. -/
theorem dftProd_comp_shearSnd (f : ZMod N × ZMod N → ℂ) (k : ZMod N) (ξ : ZMod N × ZMod N) :
    dftProd (fun v ↦ f (v.1, v.2 + k * v.1)) ξ = dftProd f (ξ.1 - k * ξ.2, ξ.2) := by
  rw [dftProd, dftProd]
  refine Fintype.sum_equiv (Cslib.shearSnd k) _ _ fun v ↦ ?_
  rw [Cslib.shearSnd_apply]
  congr 2
  ring

end ZMod
