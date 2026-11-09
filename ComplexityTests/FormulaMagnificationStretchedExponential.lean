/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.MCSP.FormulaMagnification.StretchedExponential
import Complexity.Computability.Circuit.Boolean.Hierarchy
import Complexity.Foundations.Analysis.Asymptotics.Exponential

/-!
# Tests for stretched-exponential formula magnification

Polynomial input growth admits one positive exponent that absorbs every fixed multiplicative
constant, even after a finite exceptional prefix. Negative exponents exercise the ceiling
estimate's rounding behavior. A concrete polynomial schedule then produces small separators
that accept the all-true truth table and reject every approximate-MCSP no-instance.
-/

namespace ComplexityTests.FormulaMagnificationStretchedExponential

open Cslib Cslib.Circuits Cslib.Circuits.Boolean Asymptotics Filter

-- The exponent is chosen before the constants, and a large value at zero is harmless.
example :
    ∃ δ : ℝ, 0 < δ ∧ ∀ C : ℝ, 0 ≤ C → ∀ a : ℕ,
      ∀ᶠ n in atTop,
        ((a * ⌈C * (2 : ℝ) ^
          (((if n = 0 then 10 ^ 6 else 3 * n ^ 2 + 7 : ℕ) : ℝ) ^ δ)⌉₊ : ℕ) : ℝ)
          ≤ (2 : ℝ) ^ ((n : ℝ) / 2) := by
  let p : ℕ → ℕ := fun n => if n = 0 then 10 ^ 6 else 3 * n ^ 2 + 7
  have hp : PolynomiallyBounded p := by
    apply (show PolynomiallyBounded (fun n => 3 * n ^ 2 + 7) by fun_prop).mono
    filter_upwards [eventually_ge_atTop 1] with n hn
    simp [p, show n ≠ 0 by omega]
  obtain ⟨δ, hδ, he⟩ := hp.exists_pos_rpow_isLittleO
  refine ⟨δ, hδ, fun C hC a => ?_⟩
  simpa only [p, one_div, inv_mul_eq_div] using
    he.eventually_mul_natCeil_two_rpow_le C hC a (ε := 1 / 2) (by norm_num)

-- The ceiling really rounds 5 * 2^(-1) up to 3; negative exponents are allowed.
example :
    ⌈(5 : ℝ) * (2 : ℝ) ^ (-1 : ℝ)⌉₊ = 3 ∧
      ∀ᶠ n : ℕ in atTop, (9 : ℝ) ≤ (2 : ℝ) ^ ((n : ℝ) / 4) := by
  have hceil : ⌈(5 : ℝ) * (2 : ℝ) ^ (-1 : ℝ)⌉₊ = 3 := by
    rw [Nat.ceil_eq_iff (by decide)]
    norm_num [Real.rpow_neg_one]
  have he : (fun _ : ℕ => (-1 : ℝ)) =o[atTop] (fun n => (n : ℝ)) := by
    apply isLittleO_const_left.mpr
    right
    simpa only [Function.comp_def, Real.norm_eq_abs, Nat.abs_cast] using
      (tendsto_natCast_atTop_atTop (R := ℝ))
  refine ⟨hceil, ?_⟩
  simpa only [hceil, Nat.reduceMul, Nat.cast_ofNat, one_div, inv_mul_eq_div] using
    he.eventually_mul_natCeil_two_rpow_le 5 (by norm_num) 3 (ε := 1 / 4) (by norm_num)

-- A concrete polynomial schedule gives N^(3/2) separators, including an actual yes-table.
example :
    ∃ δ : ℝ, 0 < δ ∧ ∀ L : Language Bool,
      (∀ x, x ∈ SuccinctMCSP ↔ SuccinctMCSP.enc x ∈ L) →
      ((fun m => (formulaSize (L.slice m) : ℝ))
        =O[atTop] (fun m => (2 : ℝ) ^ ((m : ℝ) ^ δ))) →
      ∀ᶠ n in atTop, ∃ F : Formula signature (2 ^ n),
        (F.leafSize : ℝ) ≤ ((2 ^ n : ℕ) : ℝ) ^ (3 / 2 : ℝ) ∧
        F.eval interpretation (fun _ => true) = true ∧
        (∀ T : BitString (2 ^ n),
          List.ofFn T ∈ ApproxMCSP.noSet (fun n => n ^ 2 + 1) (fun n => n + 2) →
          F.eval interpretation T = false) := by
  have hpoly : PolynomiallyBounded
      (fun n => approxMCSPQueryEncLength n (n ^ 2 + 1) (n + 2)) :=
    polynomiallyBounded_approxMCSPQueryEncLength (by fun_prop) (by fun_prop)
  obtain ⟨δ, hδ, hquery⟩ := hpoly.exists_pos_rpow_isLittleO
  refine ⟨δ, hδ, fun L hag hsize => ?_⟩
  have h := eventually_exists_formula_separating_approxMCSP_of_isBigO
    (s₁ := fun _ => 1) (s₂ := fun n => n ^ 2 + 1) (k := fun n => n + 2)
    (fun _ => by omega) (fun _ => by omega) hδ.le hquery hag hsize
    (ε := 1 / 2) (by norm_num)
  filter_upwards [h] with n ⟨F, hF, hyes, hno⟩
  refine ⟨F, ?_, hyes _ ?_, hno⟩
  · simpa only [show 1 + (1 / 2 : ℝ) = 3 / 2 by norm_num] using hF
  · apply GapMCSP.ofFn_mem_yesSet_iff.mpr
    change complexity interpretation (single fun _ : BitString n => true) ≤ 1
    simp only [complexity_const, le_refl]

end ComplexityTests.FormulaMagnificationStretchedExponential
