/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Computability.Circuit.Boolean.Iteration
public import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity

/-!
# Optimizing the checkpoint parameter

Balancing the two terms of `powerBudget` over the integer parameter `L` gives a fixed-power
circuit of size at most `120000 * (s' + √((n + 1) ^ 3 * M * s'))` with `s' = s + (n + 1) ^ 3`
(`fixed_power_on_optimized`): rounding the real balancing point costs a factor three. In
particular every fixed power has a circuit of size at most
`120000 * (s + (n + 1) ^ 3) * 2 ^ ((n + 1) / 2)` (`fixed_power_half_exponent`), and transition
circuits of polynomial size give fixed powers of polynomial times half-exponential size
(`fixed_power_polynomial`).

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.optimizedBudget`: the balanced square-root budget.

## Main results

* `Cslib.Circuits.Boolean.Iteration.fixed_power_optimized`, `fixed_power_on_optimized`: the
  square-root bounds.
* `Cslib.Circuits.Boolean.Iteration.fixed_power_half_exponent`: a closed-form bound.
* `Cslib.Circuits.Boolean.Iteration.fixed_power_polynomial`: polynomial transition circuits.

## References

* Adapted from lean/Proofs/Optimization.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

/-- The balanced budget `s' + √((n + 1) ^ 3 * M * s')` with `s' = s + (n + 1) ^ 3`. -/
noncomputable def optimizedBudget (n s M : ℕ) : ℝ :=
  (s + (n + 1) ^ 3 : ℕ) + Real.sqrt ((n + 1 : ℝ) ^ 3 * M * (s + (n + 1) ^ 3 : ℕ))

/-- Rounding the balancing point of `a * L + b * (M / L + 1)` costs at most a factor three. -/
theorem exists_le_three_mul_add_sqrt (a b M N : ℕ) (hb : 0 < b) (hba : b ≤ a)
    (hMN : M ≤ N) (hN : 0 < N) :
    ∃ L : ℕ, 0 < L ∧ L ≤ N ∧
      (a * L + b * (M / L + 1) : ℕ) ≤ (3 : ℝ) * (a + Real.sqrt ((b : ℝ) * M * a)) := by
  have ha : 0 < (a : ℝ) := by exact_mod_cast lt_of_lt_of_le hb hba
  have hb0 : 0 ≤ (b : ℝ) := by positivity
  have hba' : (b : ℝ) ≤ a := by exact_mod_cast hba
  let q : ℝ := (b : ℝ) * M
  let z : ℝ := Real.sqrt (q * a)
  have hz0 : 0 ≤ z := Real.sqrt_nonneg _
  have hz2 : z ^ 2 = q * a := Real.sq_sqrt (by dsimp [q]; positivity)
  by_cases hsmall : q ≤ a
  · refine ⟨1, by omega, hN, ?_⟩
    simp only [Nat.mul_one, Nat.div_one, Nat.cast_add, Nat.cast_mul, Nat.cast_one]
    change (a : ℝ) + b * (M + 1) ≤ 3 * (a + z)
    dsimp [q] at hsmall
    nlinarith
  have hqa : (a : ℝ) ≤ q := (lt_of_not_ge hsmall).le
  have hza : (a : ℝ) ≤ z := by nlinarith
  have hzpos : 0 < z := lt_of_lt_of_le ha hza
  have hM : 0 < M := by
    by_contra h
    have : M = 0 := by omega
    simp only [q, this, Nat.cast_zero, mul_zero] at hqa
    linarith
  have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hzM : z ≤ (a : ℝ) * M := by
    have hq : q ≤ (a : ℝ) * M := by dsimp [q]; gcongr
    have hsq : q * a ≤ ((a : ℝ) * M) ^ 2 := by nlinarith
    nlinarith [mul_nonneg ha.le (show (0 : ℝ) ≤ M by positivity)]
  let L := Nat.ceil (z / a)
  have hL : 0 < L := Nat.one_le_ceil_iff.mpr (div_pos hzpos ha)
  have hLM : L ≤ M := Nat.ceil_le.mpr ((div_le_iff₀ ha).mpr (by simpa [mul_comm] using hzM))
  have hlo : z ≤ (a : ℝ) * L := by
    have := (div_le_iff₀ ha).mp (Nat.le_ceil (z / a))
    nlinarith
  have hhi : (a : ℝ) * L ≤ z + a := by
    have := Nat.ceil_lt_add_one (div_nonneg hz0 ha.le)
    have hh := (lt_div_iff₀ ha).mp (show (L : ℝ) < (z + a) / a by
      simpa only [add_div, div_self ha.ne'] using this)
    nlinarith
  have hquot : ((M / L : ℕ) : ℝ) * L ≤ M := by exact_mod_cast Nat.div_mul_le_self M L
  have hterm : (b : ℝ) * (M / L : ℕ) ≤ z := by
    have h1 := mul_le_mul_of_nonneg_left hquot hb0
    have h2 := mul_le_mul_of_nonneg_left hlo (show 0 ≤ (b : ℝ) * (M / L : ℕ) by positivity)
    have h3 := mul_le_mul_of_nonneg_left h1 ha.le
    dsimp [q] at hz2
    nlinarith
  refine ⟨L, hL, hLM.trans hMN, ?_⟩
  push_cast
  change (a : ℝ) * L + b * ((M / L : ℕ) + 1) ≤ 3 * (a + z)
  nlinarith

/-- For any `M ≤ 2 ^ n`, there is a checkpoint parameter `0 < L ≤ 2 ^ n` with
`powerBudget n s M L ≤ 3 * optimizedBudget n s M`. -/
theorem exists_powerBudget_le_optimizedBudget (n s M : ℕ) (hM : M ≤ 2 ^ n) :
    ∃ L : ℕ, 0 < L ∧ L ≤ 2 ^ n ∧ (powerBudget n s M L : ℝ) ≤ 3 * optimizedBudget n s M := by
  obtain ⟨L, hL, hLN, h⟩ := exists_le_three_mul_add_sqrt (s + (n + 1) ^ 3) ((n + 1) ^ 3)
    M (2 ^ n) (by positivity) (by omega) hM (by positivity)
  refine ⟨L, hL, hLN, ?_⟩
  have he : powerBudget n s M L = (s + (n + 1) ^ 3) * L + (n + 1) ^ 3 * (M / L + 1) := by
    unfold powerBudget
    ring
  simpa [he, optimizedBudget, Nat.cast_add, Nat.cast_pow] using h

/-- **Square-root fixed powers.** -/
theorem fixed_power_optimized {n : ℕ} (c : Circuit signature n n) (T : ℕ) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      (out.size : ℝ) ≤ 120000 * optimizedBudget n c.size (2 ^ n) := by
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size (2 ^ n) le_rfl
  obtain ⟨out, hout, hs⟩ := fixed_power n c T L hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 40000 * (powerBudget n c.size (2 ^ n) L : ℝ) := by
    exact_mod_cast hs
  linarith

/-- **Square-root fixed powers on an invariant set.** -/
theorem fixed_power_on_optimized {n : ℕ} (c : Circuit signature n n) (S : Finset (BitString n))
    (hS : ∀ x ∈ S, c.eval interpretation x ∈ S) (T : ℕ) :
    ∃ out : Circuit signature n n,
      out.ComputesOn interpretation ↑S (c.eval interpretation)^[T] ∧
      (out.size : ℝ) ≤ 120000 * optimizedBudget n c.size S.card := by
  have hcard : S.card ≤ 2 ^ n := by simpa using Finset.card_le_univ S
  obtain ⟨L, hL, hLN, hopt⟩ := exists_powerBudget_le_optimizedBudget n c.size S.card hcard
  obtain ⟨out, hout, hs⟩ := fixed_power_on n c S T L hS hL hLN
  refine ⟨out, hout, ?_⟩
  have hs' : (out.size : ℝ) ≤ 40000 * (powerBudget n c.size S.card L : ℝ) := by
    exact_mod_cast hs
  linarith

/-- A closed-form half-exponential bound. -/
theorem fixed_power_half_exponent {n : ℕ} (c : Circuit signature n n) (T : ℕ) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 120000 * (c.size + (n + 1) ^ 3) * 2 ^ ((n + 1) / 2) := by
  let L := 2 ^ (n / 2)
  have hL : 0 < L := by positivity
  have hLN : L ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) (Nat.div_le_self _ _)
  obtain ⟨out, hout, hs⟩ := fixed_power n c T L hL hLN
  have hdiv : 2 ^ n / L = 2 ^ (n - n / 2) := Nat.pow_div (Nat.div_le_self _ _) (by decide)
  have hlow : L ≤ 2 ^ ((n + 1) / 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hupp : 2 ^ (n - n / 2) ≤ 2 ^ ((n + 1) / 2) := Nat.pow_le_pow_right (by decide) (by omega)
  have hone : 1 ≤ 2 ^ ((n + 1) / 2) := Nat.one_le_two_pow
  have hp : powerBudget n c.size (2 ^ n) L ≤ 3 * (c.size + (n + 1) ^ 3) * 2 ^ ((n + 1) / 2) := by
    unfold powerBudget
    rw [hdiv]
    have h1 := Nat.mul_le_mul_right c.size hlow
    have h2 := Nat.mul_le_mul_left ((n + 1) ^ 3)
      (show L + 2 ^ (n - n / 2) + 1 ≤ 3 * 2 ^ ((n + 1) / 2) by omega)
    nlinarith
  refine ⟨out, hout, hs.trans ?_⟩
  have := Nat.mul_le_mul_left 40000 hp
  nlinarith

/-- Transition circuits of size `K * (n + 1) ^ d` give fixed powers of size
`120000 * (K + 1) * (n + 1) ^ max d 3 * 2 ^ ((n + 1) / 2)`. -/
theorem fixed_power_polynomial {n : ℕ} (c : Circuit signature n n) (K d T : ℕ)
    (hs : c.size ≤ K * (n + 1) ^ d) :
    ∃ out : Circuit signature n n,
      out.Computes interpretation (c.eval interpretation)^[T] ∧
      out.size ≤ 120000 * (K + 1) * (n + 1) ^ max d 3 * 2 ^ ((n + 1) / 2) := by
  obtain ⟨out, hout, ho⟩ := fixed_power_half_exponent c T
  have hd : (n + 1) ^ d ≤ (n + 1) ^ max d 3 :=
    Nat.pow_le_pow_right (by omega) (le_max_left _ _)
  have h3 : (n + 1) ^ 3 ≤ (n + 1) ^ max d 3 :=
    Nat.pow_le_pow_right (by omega) (le_max_right _ _)
  have hc : c.size + (n + 1) ^ 3 ≤ (K + 1) * (n + 1) ^ max d 3 := by
    nlinarith [Nat.mul_le_mul_left K hd]
  refine ⟨out, hout, ho.trans ?_⟩
  calc
    _ ≤ 120000 * ((K + 1) * (n + 1) ^ max d 3) * 2 ^ ((n + 1) / 2) := by gcongr
    _ = _ := by ring

end Cslib.Circuits.Boolean.Iteration
