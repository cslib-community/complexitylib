/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryAddition
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import Mathlib.Data.Nat.Size

/-!
# Arithmetic in binary within linear work space

Binary addition reexports the linear zip-transducer certificate, weakened to time quadratic in
the encoded input length and linear charged workspace. The remaining facts bound lengths of
arithmetic outputs and identify successor iteration, for clients with fixed workspace budgets.

## Main results

* `Turing.MultiTapeTM.length_encNat_mono`, `.length_encNat_add_le_add`, `.length_encNat_mul_le`:
  monotonicity and lengths of sums and products in binary.
* `Turing.MultiTapeTM.ComputableInO.natAdd`: binary addition in quadratic time and linear space.
-/

@[expose] public section

namespace Turing.MultiTapeTM

theorem length_encNat_eq_size (n : ℕ) : (encNat n).length = n.size := by
  rw [encNat_apply, Nat.size_eq_bits_len]

/-- Binary length is monotone in the value. -/
theorem length_encNat_mono {m n : ℕ} (h : m ≤ n) : (encNat m).length ≤ (encNat n).length := by
  simp only [length_encNat_eq_size]
  exact Nat.size_le_size h

/-- A number is at least as large as its length. -/
theorem length_encNat_le_self (n : ℕ) : (encNat n).length ≤ n := by
  rw [length_encNat_eq_size]; exact Nat.size_le.mpr Nat.lt_two_pow_self

/-- The binary length of a sum is bounded by the sum of the input lengths plus one. -/
theorem length_encNat_add_le_add (a b : ℕ) :
    (encNat (a + b)).length ≤ (encNat a).length + (encNat b).length + 1 := by
  simp only [length_encNat_eq_size]
  refine Nat.size_le.mpr ?_
  have ha := Nat.lt_size_self a
  have hb := Nat.lt_size_self b
  have h₁ : 2 ^ a.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h₂ : 2 ^ b.size ≤ 2 ^ (a.size + b.size) := Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_succ]
  omega

/-- A product is at most as long as its factors together. -/
theorem length_encNat_mul_le (a b : ℕ) :
    (encNat (a * b)).length ≤ (encNat a).length + (encNat b).length := by
  simp only [length_encNat_eq_size]
  refine Nat.size_le.mpr ?_
  rw [pow_add]
  exact Nat.mul_lt_mul'' (Nat.lt_size_self a) (Nat.lt_size_self b)

namespace ComputableInO

theorem iterate_succ_eq (k n : ℕ) : (· + 1)^[k] n = n + k := by simp

end ComputableInO

namespace ComputableTidilyInO

theorem iterate_succ_eq (k n : ℕ) : (· + 1)^[k] n = n + k :=
  ComputableInO.iterate_succ_eq k n

end ComputableTidilyInO

end Turing.MultiTapeTM
