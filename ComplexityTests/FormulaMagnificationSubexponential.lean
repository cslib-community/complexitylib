/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.FormulaMagnification.Subexponential
import Mathlib.Data.Nat.Sqrt

/-!
# Tests for subexponential formula magnification

The growth predicate accepts a stretched exponential and arbitrary finite exceptions, while
rejecting exponential growth. The stretched-exponential schedule is then used in the concrete
MCSP query-length and formula-construction APIs.
-/

namespace ComplexityTests.FormulaMagnificationSubexponential

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Filter

private theorem sqrtRate_subexp : SubexponentiallyBounded (fun n => 2 ^ Nat.sqrt n) := by
  intro c
  filter_upwards [eventually_ge_atTop ((2 * c + 1) ^ 2)] with n hn
  have hc : 2 * c + 1 ≤ Nat.sqrt n := Nat.le_sqrt'.mpr hn
  have hsquare := Nat.sqrt_le' n
  have hlog : Nat.clog 2 (2 ^ Nat.sqrt n + 1) ≤ Nat.sqrt n + 1 := by
    apply (Nat.clog_le_iff_le_pow one_lt_two).mpr
    rw [pow_succ]
    have := Nat.one_le_two_pow (n := Nat.sqrt n)
    omega
  have hmul := Nat.mul_le_mul_left c hlog
  nlinarith

-- An enormous exceptional value at zero does not change the asymptotic condition.
example : SubexponentiallyBounded
    (fun n => if n = 0 then 2 ^ 10000 else (n + 1) ^ 3) := by
  apply ((SubexponentiallyBounded.id.add (.const 1)).pow 3).mono
  filter_upwards [eventually_ge_atTop 1] with n hn
  simp [show n ≠ 0 by omega]

-- Polynomially bounded schedules use the existing polynomial-growth API.
example : SubexponentiallyBounded (fun n => 7 * (n + 1) ^ 4 + 11) := by
  apply PolynomiallyBounded.subexponentiallyBounded
  fun_prop

-- A full exponential must not satisfy the new predicate.
example : ¬ SubexponentiallyBounded (fun n => 2 ^ n) := by
  intro h
  obtain ⟨N, hN⟩ := eventually_atTop.mp (h 2)
  have hn := hN (N + 1) (by omega)
  change 2 * Nat.clog 2 (2 ^ (N + 1) + 1) ≤ N + 1 at hn
  have hlog : N + 1 ≤ Nat.clog 2 (2 ^ (N + 1) + 1) := by
    calc
      N + 1 = Nat.clog 2 (2 ^ (N + 1)) := (Nat.clog_pow 2 (N + 1) one_lt_two).symm
      _ ≤ Nat.clog 2 (2 ^ (N + 1) + 1) := Nat.clog_mono_right 2 (Nat.le_succ _)
  omega

-- The actual encoding remains subexponential with a stretched-exponential size threshold.
example : SubexponentiallyBounded
    (fun n => approxMCSPQueryEncLength n (2 ^ Nat.sqrt n) ((n + 1) ^ 2)) :=
  subexponentiallyBounded_approxMCSPQueryEncLength sqrtRate_subexp
    ((SubexponentiallyBounded.id.add (.const 1)).pow 2)

-- End-to-end client: stretched-exponential parameters give the usual real-exponent bound.
example (hmem : SuccinctMCSP ∈ FormulaPolyOn SuccinctMCSP.enc) :
    ∀ᶠ n in atTop, ∃ F : Formula signature (2 ^ n),
      (F.leafSize : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ (1 + (1 / 10 : ℝ)) ∧
      (∀ T : BitString (2 ^ n),
        List.ofFn T ∈ GapMCSP.yesSet (fun n => 2 ^ Nat.sqrt n) →
        F.eval interpretation T = true) ∧
      (∀ T : BitString (2 ^ n),
        List.ofFn T ∈ ApproxMCSP.noSet (fun n => 2 ^ Nat.sqrt n)
          (fun n => 2 ^ Nat.sqrt n) → F.eval interpretation T = false) :=
  eventually_exists_formula_separating_approxMCSP_rpow_of_mem_FormulaPolyOn
    (fun _ => le_rfl) (fun _ => Nat.one_le_two_pow) sqrtRate_subexp sqrtRate_subexp
    hmem (by norm_num)

end ComplexityTests.FormulaMagnificationSubexponential
