/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.BigO
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.OCountedIteration
public import Complexity.Computability.Machines.Turing.MultiTape.Combinators.IterateWhile
public import Complexity.Computability.Machines.Turing.MultiTape.Internal.BinaryComparison
public import Mathlib.Data.Nat.Size

/-!
# Arithmetic in binary within linear work space

Addition of binary naturals, by iterating the successor with a binary counter. The time is
polynomial in the values, not in their lengths, but the work space is linear in the lengths of the
encodings. This suits space-bounded algorithms, where only the work space matters.

## Main results

* `Turing.MultiTapeTM.length_encNat_mono`, `.length_encNat_add_le_add`, `.length_encNat_mul_le`:
  monotonicity and lengths of sums and products in binary.
* `Turing.MultiTapeTM.ComputableInO.natAdd`: addition in binary within linear work space.
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

/-- **Addition in binary**, within linear work space. -/
public theorem natAdd :
    ComputableInO (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      (fun p => (p.2 + 1) * ((encPair encNat encNat p).length + 2) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 := by
  have hle (p : ℕ × ℕ) (k : ℕ) (hk : k ≤ p.2) :
      (encNat ((· + 1)^[k] p.1)).length ≤ (encNat p.1).length + (encNat p.2).length + 1 := by
    rw [iterate_succ_eq]
    exact (Turing.MultiTapeTM.length_encNat_mono (by omega : p.1 + k ≤ p.1 + p.2)).trans
      (length_encNat_add_le_add _ _)
  have h := ComputableInO.iterate (n := fun p : ℕ × ℕ => p.2) (init := fun p => p.1)
    (step := (· + 1)) (snd encNat encNat) (fst encNat encNat) ComputableInO.natSucc
    (R := fun p => ((encNat p.1).length + (encNat p.2).length + 2) ^ 2)
    (Q := fun p => (encNat p.1).length + (encNat p.2).length + 2)
    (B := fun p => (encNat p.1).length + (encNat p.2).length + 1)
    (fun p k hk => Nat.pow_le_pow_left (by have := hle p k hk; omega) 2)
    (fun p k hk => by have := hle p k hk; omega) (fun p k hk => hle p k hk)
  refine (h.mono 8 (fun p => ?_) fun p => ?_).of_enc_eq fun p => by rw [iterate_succ_eq]
  · simp only [length_encPair]
    nlinarith [Nat.zero_le ((encNat p.1).length), Nat.zero_le ((encNat p.2).length),
      Nat.zero_le (p.2 * (encNat p.1).length), Nat.zero_le (p.2 * (encNat p.2).length)]
  · simp only [length_encPair]
    omega

end ComputableInO

namespace ComputableTidilyInO

theorem iterate_succ_eq (k n : ℕ) : (· + 1)^[k] n = n + k :=
  ComputableInO.iterate_succ_eq k n

/-- **Addition in binary**, within linear work space. -/
public theorem natAdd :
    ComputableTidilyInO (fun p : ℕ × ℕ => p.1 + p.2) (encPair encNat encNat) encNat
      (fun p => (p.2 + 1) * ((encPair encNat encNat p).length + 2) ^ 2)
      fun p => (encPair encNat encNat p).length + 1 :=
  ComputableInO.natAdd.tidy

end ComputableTidilyInO

end Turing.MultiTapeTM
