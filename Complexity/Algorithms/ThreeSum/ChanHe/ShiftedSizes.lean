/-
Copyright (c) 2026 Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.ThreeSum.ChanHe.Sizes

/-!
# Size bounds for the initialized-input magnitude convention

Native parameter computation uses `(n+2)^κ`, including at lengths zero and one. The existing
finite instances retain their actual input-length parameter `n`; only their quantitative upper
bounds are compared with the existing estimates at `n+2`.

## Main results

* `mPar_mono_input`: candidate bounds are monotone in input length.
* `mPar_shifted_pow_le`: square-root times squared-logarithm bound for the actual native modulus.
* `length_instances_shifted_pow_le`: degree-seven logarithmic instance count at every length.
* `packed_length_shifted_pow_le`: linear times fourth-logarithm common packed length.

These elementary parameter bridges are original and reuse the existing finite Chan–He bounds.
They do not change the finite instances or replace the actual input length by a padded input.
-/

@[expose] public section

namespace Cslib.Algorithms.ThreeSum.ChanHe

/-- Increasing the length parameter increases the candidate window without changing magnitude. -/
theorem mPar_mono_input {n n' : ℕ} (hn : n ≤ n') (U : ℕ) : mPar n U ≤ mPar n' U := by
  have hs := Nat.sqrt_le_sqrt hn
  unfold mPar wPar
  gcongr

/-- The actual native parameter keeps length `n` and uses shifted polynomial magnitude. -/
theorem mPar_shifted_pow_le (n κ : ℕ) :
    mPar n (2 * (n + 2) ^ κ) ≤
      (5 * κ + 16) * (10 * κ + 40) * (Nat.sqrt (n + 2) + 1) *
        (Nat.log 2 (n + 2) + 1) ^ 2 :=
  (mPar_mono_input (show n ≤ n + 2 by omega) _).trans (mPar_pow_le (n + 2) κ)

/-- The unchanged actual finite instance list has a logarithmic count even at lengths zero/one. -/
theorem length_instances_shifted_pow_le (n κ : ℕ) (x : Fin n → ℤ) :
    (instances n ((n + 2) ^ κ) x).length ≤ numBound κ (n + 2) := by
  have hlog : 1 ≤ Nat.log 2 (n + 2) := Nat.log_pos (by decide) (by omega)
  have hΛ : labelBits (2 * (n + 2) ^ κ) ≤ (κ + 2) * (Nat.log 2 (n + 2) + 1) :=
    (labelBits_pow_le (n + 2) κ).trans (by rw [add_mul]; omega)
  have hone : 1 ≤ ((κ + 2) * (Nat.log 2 (n + 2) + 1)) ^ 2 :=
    Nat.one_le_pow _ _ (by positivity)
  have hn : Nat.log 2 n ≤ Nat.log 2 (n + 2) := Nat.log_mono_right (by omega)
  calc (instances n ((n + 2) ^ κ) x).length
      ≤ (2 * labelBits (2 * (n + 2) ^ κ) ^ 2 + 2) * (2 * Nat.log 2 n + 2) ^ 5 :=
        length_instances_le ..
    _ ≤ (2 * ((κ + 2) * (Nat.log 2 (n + 2) + 1)) ^ 2 +
        2 * ((κ + 2) * (Nat.log 2 (n + 2) + 1)) ^ 2) *
          (2 * Nat.log 2 (n + 2) + 2) ^ 5 := by gcongr; omega
    _ = numBound κ (n + 2) := by unfold numBound; ring

/-- The unchanged common packed length is bounded by the old estimate evaluated at `n+2`. -/
theorem packed_length_shifted_pow_le (κ n : ℕ) :
    8 * mPar n (2 * (n + 2) ^ κ) ^ 2 ≤
      32 * ((5 * κ + 16) * (10 * κ + 40)) ^ 2 * (n + 2) *
        (Nat.log 2 (n + 2) + 1) ^ 4 := by
  calc 8 * mPar n (2 * (n + 2) ^ κ) ^ 2 ≤ lenOf κ (n + 2) :=
      Nat.mul_le_mul_left 8 (Nat.pow_le_pow_left
        (mPar_mono_input (show n ≤ n + 2 by omega) _) 2)
    _ ≤ _ := lenOf_le κ (n + 2) (by omega)

end Cslib.Algorithms.ThreeSum.ChanHe
