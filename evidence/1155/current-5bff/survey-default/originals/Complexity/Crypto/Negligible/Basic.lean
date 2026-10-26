/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Negligible
public import Mathlib.Analysis.Real.Sqrt
import Complexity.Foundations.Data.Nat.PolynomialBound.Closure
import Mathlib.Analysis.SpecificLimits.Normed

/-!
# Negligible bounds and real-valued estimates

The security-game API uses nonnegative advantages. Real-valued estimates, including the pinned
finite PRG API, express the same decay after coercion. A positive constant advantage cannot be
negligible.

## Main results

* `Cslib.Crypto.negligible_iff_coe`: pass between nonnegative and real-valued decay bounds.
* `Cslib.Crypto.Negligible.eventually_le_inv_polynomial`: compare with positive polynomial losses.
* `Cslib.Crypto.negligible_geometric`: geometric decay of nonnegative error bounds.
* `Cslib.Crypto.not_negligible_const`: constant nonzero success contradicts security.
* `Cslib.Crypto.Negligible.comp_of_polynomial_bound`: polynomially related parameters.
* `Cslib.Crypto.Negligible.div_const`: division of the parameter by a positive constant.
* `Cslib.Crypto.Negligible.sqrt`: taking square roots preserves negligible decay.

## References

The geometric, constant and inverse-polynomial bounds are adapted from
Crypto/Negligible.lean on the
cslib `crypto` branch at `5ff69ca93402e7c947208dc56396d6d86203ccd8`, using the current upstream
nonnegative API.
-/

@[expose] public section

namespace Cslib.Crypto

open scoped NNReal

/-- Nonnegative advantages decay negligibly exactly when their real coercions do. -/
theorem negligible_iff_coe {ε : ℕ → ℝ≥0} : Negligible ε ↔
    Asymptotics.SuperpolynomialDecay Filter.atTop (fun n : ℕ => (n : ℝ))
      (fun n => (ε n : ℝ)) := by
  simp only [Negligible, Asymptotics.SuperpolynomialDecay, ← NNReal.tendsto_coe,
    NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_natCast, NNReal.coe_zero]

/-- Geometric decay with a nonnegative ratio strictly below one is negligible. -/
theorem negligible_geometric {ratio : ℝ≥0} (h : ratio < 1) :
    Negligible (fun n => ratio ^ n) := by
  apply negligible_iff_coe.mpr
  intro degree
  simpa only [NNReal.coe_pow] using
    tendsto_pow_const_mul_const_pow_of_abs_lt_one degree
      (show |(ratio : ℝ)| < 1 by
        rw [abs_of_nonneg ratio.coe_nonneg]
        exact_mod_cast h)

/-- A constant nonzero advantage is not negligible. -/
theorem not_negligible_const {c : ℝ≥0} (hc : c ≠ 0) : ¬ Negligible (fun _ => c) := by
  intro h
  have ht : Filter.Tendsto (fun _ : ℕ => c) Filter.atTop (nhds 0) := by simpa using h 0
  exact hc (tendsto_nhds_unique tendsto_const_nhds ht)

open Filter in
/-- Negligible success is eventually smaller than the reciprocal of any positive
polynomially bounded loss. The real coercion permits comparison with analytic bounds. -/
theorem Negligible.eventually_le_inv_polynomial {ε : ℕ → ℝ≥0} (hε : Negligible ε)
    {p : ℕ → ℕ} (hp : PolynomiallyBounded p) (hpos : ∀ n, 0 < p n) :
    ∀ᶠ n in atTop, (ε n : ℝ) ≤ 1 / (p n : ℝ) := by
  have h := negligible_iff_coe.mp (hε.polynomiallyBounded_mul hp) 0
  simp only [pow_zero, one_mul, NNReal.coe_mul, NNReal.coe_natCast] at h
  filter_upwards [h.eventually_le_const (by norm_num : (0 : ℝ) < 1)] with n hn
  apply (le_div_iff₀ (by exact_mod_cast hpos n)).mpr
  simpa only [mul_comm] using hn

open Filter Topology in
/-- Negligible decay survives reindexing when the new parameter tends to infinity and the old
parameter is polynomially bounded in it. The reindexing function need not be computable. -/
theorem Negligible.comp_of_polynomial_bound {ε : ℕ → ℝ≥0} {index bound : ℕ → ℕ}
    (hε : Negligible ε) (hindex : Tendsto index atTop atTop)
    (hbound : PolynomiallyBounded bound) (hle : ∀ᶠ n in atTop, n ≤ bound (index n)) :
    Negligible (fun n => ε (index n)) := by
  intro degree
  have hlimit := (hε.polynomiallyBounded_mul (hbound.pow degree) 0).comp hindex
  simp only [pow_zero, one_mul, Nat.cast_pow, Function.comp_def] at hlimit
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlimit
    (Eventually.of_forall (fun _ => zero_le)) ?_
  filter_upwards [hle] with n hn
  exact mul_le_mul' (pow_le_pow_left' (by exact_mod_cast hn) degree) le_rfl

open Filter in
/-- Dividing the security parameter by a fixed positive natural preserves negligible decay. -/
theorem Negligible.div_const {ε : ℕ → ℝ≥0} (hε : Negligible ε) {divisor : ℕ}
    (hpos : 0 < divisor) : Negligible (fun n => ε (n / divisor)) := by
  apply hε.comp_of_polynomial_bound (bound := fun n => divisor * (n + 1))
    (Nat.tendsto_div_const_atTop (by lia)) (by fun_prop)
  exact Eventually.of_forall (fun n => by
    have := Nat.mod_lt n hpos
    have := Nat.div_add_mod n divisor
    nlinarith)

/-- Taking a square root preserves negligible decay. -/
@[fun_prop]
theorem Negligible.sqrt {ε : ℕ → ℝ≥0} (hε : Negligible ε) :
    Negligible (fun n => NNReal.sqrt (ε n)) := by
  intro degree
  have hlimit := NNReal.continuous_sqrt.continuousAt.tendsto.comp (hε (degree * 2))
  simpa only [Function.comp_def, pow_mul, NNReal.sqrt_mul, NNReal.sqrt_sq, NNReal.sqrt_zero]
    using hlimit

/-- Shifting the security parameter by a fixed additive offset preserves negligibility. -/
theorem Negligible.shift {ε : ℕ → ℝ≥0} (hε : Negligible ε) (c : ℕ) :
    Negligible (fun n => ε (n + c)) :=
  hε.comp_of_polynomial_bound (bound := id) (Filter.tendsto_add_atTop_nat c) (by fun_prop)
    (Filter.Eventually.of_forall (fun n => Nat.le_add_right n c))

end Cslib.Crypto
