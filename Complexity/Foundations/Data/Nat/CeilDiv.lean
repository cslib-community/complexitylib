/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.Order.Floor.Div
public import Mathlib.Algebra.Order.Archimedean.Real.Basic

/-!
# Natural ceilings of quotients

## Main results

* `Nat.ceil_div_eq_ceilDiv`: real quotient ceilings equal natural ceiling division.
* `Nat.le_ceilDiv_mul`, `Nat.ceilDiv_mul_lt`: covering and overshoot bounds.

## References

Adapted from [Ceil.lean](https://github.com/anthropics/formal-math/blob/16a5ce41304fcdaea4e0be7c132e1c361dc26da5/3sum-apsp/ThreeSumApsp/Util/Ceil.lean) at
`anthropics/formal-math@16a5ce41304fcdaea4e0be7c132e1c361dc26da5`.
-/

@[expose] public section

namespace Nat

/-! ## The ceiling of a quotient of natural numbers -/

/-- `a ⌈/⌉ b ≤ k` says that `k` pieces of size `b` cover `a`. Mathlib's `ceilDiv_le_iff_le_mul` has
`b * k` on the right. -/
theorem ceilDiv_le_iff {a b k : ℕ} (hb : 0 < b) : a ⌈/⌉ b ≤ k ↔ a ≤ k * b := by
  rw [ceilDiv_le_iff_le_mul hb, Nat.mul_comm]

/-- `a ⌈/⌉ b` pieces of size `b` cover `a`. -/
theorem le_ceilDiv_mul {a b : ℕ} (hb : 0 < b) : a ≤ a ⌈/⌉ b * b :=
  (ceilDiv_le_iff hb).1 le_rfl

/-- `a ⌈/⌉ b` pieces of size `b` overshoot `a` by less than one piece. -/
theorem ceilDiv_mul_lt {a b : ℕ} (hb : 0 < b) : a ⌈/⌉ b * b < a + b := by
  have := Nat.div_mul_le_self (a + b - 1) b
  rw [Nat.ceilDiv_eq_add_pred_div]
  omega

/-- The ceiling of the real quotient of two natural numbers, in natural numbers. -/
theorem ceil_div_eq_ceilDiv (a : ℕ) {b : ℕ} (hb : 0 < b) : ⌈(a : ℝ) / (b : ℝ)⌉₊ = a ⌈/⌉ b := by
  refine eq_of_forall_ge_iff fun k => ?_
  rw [Nat.ceil_le, div_le_iff₀ (Nat.cast_pos.2 hb), ceilDiv_le_iff hb]
  exact_mod_cast Iff.rfl

end Nat
