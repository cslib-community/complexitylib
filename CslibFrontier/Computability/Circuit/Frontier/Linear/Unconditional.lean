/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Frontier.Layouts.General
public import CslibFrontier.Computability.Circuit.Frontier.Linear.LowerBound
public import Mathlib.Algebra.CharZero.Infinite

/-!
# Unconditional frontier lower bounds for linear maps

The frontier lower bound for linear maps
(`Cslib.Circuits.Frontier.eventually_lt_mul_innerSize_of_isTotallyRegular`) is conditional on the
layout hypothesis `LayoutBound (r + 1) A`. Spanning trees prove it with coefficient `A = 1` in
every degree (`Cslib.Circuits.Frontier.layoutBound_one`), which removes the hypothesis: for every
fan-in `r ≥ 2`, every `ε > 0` and all large `N`, every circuit of fan-in at most `r` computing a
totally regular map `F^N → F^N` has `s` inner gates with

`(r - 1) s > (2 - ε) N`,

over finite fields with any basis, and over infinite fields with polynomial operations. Gates of
arity zero, the constants, are not counted.

For the explicit Cauchy matrices `1 / (i - (N + j))` this gives, for fan-in two:

* **Arithmetic circuits**: over every field of characteristic zero, in particular over `ℚ`, `ℝ`
  and `ℂ`, every circuit of additions, multiplications and constants computing
  `x ↦ (∑_j x_j / (i - N - j))_i` uses more than `(2 - ε) N` additions and multiplications.
* **Prime fields**: the same maps over `ZMod q`, for every prime `q ≥ 2 N`, need more than
  `(2 - ε) N` inner gates in every basis of fan-in two, uniformly in `q`.

## Main results

* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_mul_innerSize_of_isTotallyRegular`: for
  circuits with linear capacity; `..._finite` and `..._isPolynomial` specialize it.
* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_arith_cauchyNat`: arithmetic
  circuits for the Cauchy maps.
* `Cslib.Circuits.Frontier.eventually_two_sub_mul_lt_innerSize_cauchyNat_zmod`: the Cauchy maps
  over prime fields.
-/

public section

namespace Cslib.Circuits.Frontier

open Filter Matrix

universe u v

/-- **The unconditional frontier lower bound for linear maps.** Let `r ≥ 2`. For every `ε > 0`
and all large `N`, every circuit of fan-in at most `r` with linear capacity, over any field and
any basis, that computes `x ↦ M x` for a totally regular `N × N` matrix `M`, has `s` inner gates
with `(r - 1) s > (2 - ε) N`. -/
theorem eventually_two_sub_mul_lt_mul_innerSize_of_isTotallyRegular {r : ℕ} (hr : 2 ≤ r) {ε : ℝ}
    (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] (σ : Signature.{v}) (I : Interpretation σ F)
      (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N), M.IsTotallyRegular →
        c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) → c.LinearCapacity I →
          (2 - ε) * N < (r - 1) * c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_mul_innerSize_of_isTotallyRegular hr one_pos (layoutBound_one (r + 1)) hε

/-- **The unconditional frontier lower bound for linear maps over finite fields**, for every
basis: `(r - 1) s > (2 - ε) N` for fan-in at most `r`. -/
theorem eventually_two_sub_mul_lt_mul_innerSize_of_isTotallyRegular_finite {r : ℕ} (hr : 2 ≤ r)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Finite F] (σ : Signature.{v})
      (I : Interpretation σ F) (M : Matrix (Fin N) (Fin N) F) (c : Circuit σ N N),
        M.IsTotallyRegular → c.FanInAtMost r → c.Computes I (fun x => M *ᵥ x) →
          (2 - ε) * N < (r - 1) * c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_mul_innerSize_of_isTotallyRegular_finite hr one_pos (layoutBound_one (r + 1)) hε

/-- **The unconditional frontier lower bound for linear maps over infinite fields**, for every
basis of polynomial operations: `(r - 1) s > (2 - ε) N` for fan-in at most `r`. -/
theorem eventually_two_sub_mul_lt_mul_innerSize_of_isTotallyRegular_isPolynomial {r : ℕ}
    (hr : 2 ≤ r) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [Infinite F] (σ : Signature.{v})
      (I : Interpretation σ F), I.IsPolynomial → ∀ (M : Matrix (Fin N) (Fin N) F)
        (c : Circuit σ N N), M.IsTotallyRegular → c.FanInAtMost r →
          c.Computes I (fun x => M *ᵥ x) → (2 - ε) * N < (r - 1) * c.innerSize := by
  simpa only [div_one, one_add_one_eq_two] using
    eventually_lt_mul_innerSize_of_isTotallyRegular_isPolynomial hr one_pos
      (layoutBound_one (r + 1)) hε

/-- **Arithmetic circuits for the Cauchy maps.** Over every field of characteristic zero, every
arithmetic circuit computing `x ↦ (∑_j x_j / (i - N - j))_i` uses more than `(2 - ε) N` additions
and multiplications, for all large `N`. Constants are free. -/
theorem eventually_two_sub_mul_lt_innerSize_arith_cauchyNat {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (F : Type u) [Field F] [CharZero F] (c : Circuit (arithSignature F) N N),
      c.Computes (arithInterpretation F) (fun x => cauchyNat F N *ᵥ x) →
        (2 - ε) * N < c.innerSize := by
  filter_upwards [eventually_two_sub_mul_lt_mul_innerSize_of_isTotallyRegular_isPolynomial.{u, u}
    le_rfl hε] with N hN
  intro F _ _ c hc
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hN F _ _ isPolynomial_arithInterpretation _ c (isTotallyRegular_cauchyNat N)
      c.fanInAtMost_two_arith hc

/-- **The Cauchy maps over prime fields.** For all large `N` and every prime `q ≥ 2 N`, every
circuit of fan-in at most two, over any basis on `ZMod q`, computing
`x ↦ (∑_j x_j / (i - N - j))_i` has more than `(2 - ε) N` inner gates. -/
theorem eventually_two_sub_mul_lt_innerSize_cauchyNat_zmod {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ N in atTop, ∀ (q : ℕ) [Fact q.Prime], 2 * N ≤ q → ∀ (σ : Signature.{v})
      (I : Interpretation σ (ZMod q)) (c : Circuit σ N N), c.FanInAtMost 2 →
        c.Computes I (fun x => cauchyNat (ZMod q) N *ᵥ x) → (2 - ε) * N < c.innerSize := by
  filter_upwards [eventually_two_sub_mul_lt_mul_innerSize_of_isTotallyRegular_finite.{0, v}
    le_rfl hε] with N hN
  intro q _ hq σ I c hfan hc
  have : NeZero q := ⟨(Fact.out : q.Prime).ne_zero⟩
  simpa only [Nat.cast_ofNat, show (2 : ℝ) - 1 = 1 by norm_num, one_mul] using
    hN (ZMod q) σ I _ c (isTotallyRegular_cauchyNat_zmod hq) hfan hc

end Cslib.Circuits.Frontier
