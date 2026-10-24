/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Nat.ModEq
public import Mathlib.Data.Nat.Squarefree
public import Mathlib.Data.ZMod.Units
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.GroupTheory.Exponent
import Mathlib.Tactic.NormNum

/-!
# Sequential squaring modulo a fixed squarefree modulus

For a squarefree modulus `M`, write `λ(M)` for the Carmichael exponent, here the exponent of the
unit group `(ZMod M)ˣ` (`carmichael`). Every residue, unit or not, satisfies
`x ^ (λ(M) + 1) = x` (`pow_carmichael_succ`), so two positive exponents that agree modulo `λ(M)`
give the same power map (`pow_eq_pow_of_modEq`). Consequently `T` sequential squarings are the
single power `x ↦ x ^ e` with `e = 1 + (2 ^ T - 1) % λ(M)` (`reducedExponent`,
`iterate_square_reduced`), for every `T`, including `T = 0`, and every residue.

## Main definitions

* `Cslib.Circuits.Boolean.Iteration.SequentialSquaring.carmichael`: the Carmichael exponent `λ(M)`
  of `ZMod M`, defined as `Monoid.exponent (ZMod M)ˣ`.
* `Cslib.Circuits.Boolean.Iteration.SequentialSquaring.reducedExponent`: the reduced exponent
  `1 + (2 ^ T - 1) % λ(M)` of `T` sequential squarings.

## Main results

* `Cslib.Circuits.Boolean.Iteration.SequentialSquaring.pow_carmichael_succ`: for squarefree `M`,
  every `x : ZMod M` satisfies `x ^ (carmichael M + 1) = x`.
* `Cslib.Circuits.Boolean.Iteration.SequentialSquaring.pow_eq_pow_of_modEq`: positive exponents
  congruent modulo `carmichael M` induce identical power maps on `ZMod M`.
* `Cslib.Circuits.Boolean.Iteration.SequentialSquaring.iterate_square_reduced`: `T` sequential
  squarings modulo squarefree `M` equal `x ^ reducedExponent M T`.
* `Cslib.Circuits.Boolean.Iteration.SequentialSquaring.crypto_table_entries`: parameter table
  values for `n = 512, 256, 128` and `T = 2 ^ 40`.

## References

* Adapted from lean/Proofs/SequentialSquaring.lean in
  [S. Schlesinger,
  *Square-root circuit bounds for iterated functions*][Schlesinger2026IteratedFunctions].
-/

@[expose] public section

namespace Cslib.Circuits.Boolean.Iteration

namespace SequentialSquaring

/-- The Carmichael exponent `λ(M)`: the exponent of the unit group of `ZMod M`. -/
noncomputable abbrev carmichael (M : ℕ) : ℕ := Monoid.exponent (ZMod M)ˣ

/-- The Carmichael exponent of any modulus is positive. -/
theorem carmichael_pos (M : ℕ) : 0 < carmichael M :=
  Nat.pos_of_ne_zero Monoid.exponent_ne_zero_of_finite

/-- Modulo a prime divisor `p` of `M`, every residue satisfies `y ^ (λ(M) + 1) = y`. -/
private theorem pow_carmichael_succ_prime {M p : ℕ} [NeZero M] (hp : p.Prime) (hpM : p ∣ M)
    (y : ZMod p) : y ^ (carmichael M + 1) = y := by
  have := Fact.mk hp
  by_cases hy : y = 0
  · simp [hy]
  · obtain ⟨v, hv⟩ := ZMod.unitsMap_surjective hpM (Units.mk0 y hy)
    have hu : (Units.mk0 y hy) ^ carmichael M = 1 := by
      rw [← hv, ← map_pow, Monoid.pow_exponent_eq_one, map_one]
    have hy1 : y ^ carmichael M = 1 := by
      simpa using congrArg Units.val hu
    rw [pow_succ, hy1, one_mul]

/-- For squarefree `M`, every residue modulo `M`, unit or not, satisfies `x ^ (λ(M) + 1) = x`. -/
theorem pow_carmichael_succ {M : ℕ} (hM : Squarefree M) (x : ZMod M) :
    x ^ (carmichael M + 1) = x := by
  have hM0 : M ≠ 0 := by
    rintro rfl
    exact not_squarefree_zero hM
  have : NeZero M := ⟨hM0⟩
  rw [← sub_eq_zero]
  set z := x ^ (carmichael M + 1) - x with hz
  rw [← ZMod.natCast_zmod_val z, ZMod.natCast_eq_zero_iff]
  have key := Finset.prod_primes_dvd z.val
    (fun p hp => Nat.prime_iff.mp (Nat.prime_of_mem_primeFactors hp)) (fun p hp => by
      have hpM : p ∣ M := Nat.dvd_of_mem_primeFactors hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      have := Fact.mk hpp
      rw [← ZMod.natCast_eq_zero_iff, ← ZMod.cast_eq_val, ← ZMod.castHom_apply (h := hpM)]
      rw [hz, map_sub, map_pow, pow_carmichael_succ_prime hpp hpM, sub_self])
  rwa [Nat.prod_primeFactors_of_squarefree hM] at key

/-- Adding a multiple of `λ(M)` to a positive exponent does not change the power map. -/
private theorem pow_add_mul_carmichael {M : ℕ} (hM : Squarefree M) (x : ZMod M) {a : ℕ}
    (ha : 1 ≤ a) (k : ℕ) : x ^ (a + carmichael M * k) = x ^ a := by
  induction k with
  | zero => simp
  | succ k ih =>
    have : a + carmichael M * (k + 1) = (a - 1) + (carmichael M + 1) + carmichael M * k := by
      rw [Nat.mul_succ]; omega
    rw [this, pow_add, pow_add, pow_carmichael_succ hM, ← pow_succ, Nat.sub_add_cancel ha,
      ← pow_add, ih]

/-- For squarefree `M`, positive exponents congruent modulo `λ(M)` give the same power of every
residue, including non-units. -/
theorem pow_eq_pow_of_modEq {M : ℕ} (hM : Squarefree M) (x : ZMod M) {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) (h : a ≡ b [MOD carmichael M]) : x ^ a = x ^ b := by
  rcases le_total a b with hab | hab
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hab).mp h
    rw [show b = a + carmichael M * k by omega, pow_add_mul_carmichael hM x ha]
  · obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' hab).mp h.symm
    rw [show a = b + carmichael M * k by omega, pow_add_mul_carmichael hM x hb]

/-- The reduced exponent `1 + (2 ^ T - 1) % λ(M)` of `T` squarings. -/
noncomputable def reducedExponent (M T : ℕ) : ℕ := 1 + (2 ^ T - 1) % carmichael M

/-- The reduced exponent is positive and at most `λ(M)`. -/
theorem reducedExponent_le (M T : ℕ) :
    1 ≤ reducedExponent M T ∧ reducedExponent M T ≤ carmichael M := by
  have := Nat.mod_lt (2 ^ T - 1) (carmichael_pos M)
  unfold reducedExponent
  omega

/-- Sequential squaring modulo a fixed squarefree `M`: for every `T` and every residue `x`,
including non-units, `T` squarings equal the single power `x ^ (1 + (2 ^ T - 1) % λ(M))`. -/
theorem iterate_square_reduced {M : ℕ} (hM : Squarefree M) (T : ℕ)
    (x : ZMod M) : (fun y : ZMod M => y ^ 2)^[T] x = x ^ reducedExponent M T := by
  rw [pow_iterate]
  have h1 : 1 ≤ 2 ^ T := Nat.one_le_two_pow
  refine pow_eq_pow_of_modEq hM x h1 (by unfold reducedExponent; omega) ?_
  have h := (Nat.mod_modEq (2 ^ T - 1) (carmichael M)).symm.add_left 1
  unfold reducedExponent
  rwa [Nat.add_sub_cancel' h1] at h

-- `2 ^ 512` exceeds the default `exponentiation.threshold` of 256.
set_option exponentiation.threshold 600 in
/-- The entries of the parameter table in the cryptographic section, without the omitted
constant and polynomial factors. For state lengths `n = 512, 256, 128` and `T = 2 ^ 40`, the
dictionary size `n ^ 3 * 2 ^ n / T` of a constant-factor speed-up is `2 ^ 499`, `2 ^ 240`, and
`2 ^ 109`, and `sqrt (2 ^ n)` is `2 ^ 256`, `2 ^ 128`, and `2 ^ 64`. -/
theorem crypto_table_entries :
    512 ^ 3 * 2 ^ 512 / 2 ^ 40 = 2 ^ 499 ∧ 256 ^ 3 * 2 ^ 256 / 2 ^ 40 = 2 ^ 240 ∧
      128 ^ 3 * 2 ^ 128 / 2 ^ 40 = 2 ^ 109 ∧
      Nat.sqrt (2 ^ 512) = 2 ^ 256 ∧ Nat.sqrt (2 ^ 256) = 2 ^ 128 ∧
      Nat.sqrt (2 ^ 128) = 2 ^ 64 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show (512 : ℕ) ^ 3 = 2 ^ 27 by norm_num, ← pow_add, Nat.pow_div (by norm_num) two_pos,
      show 27 + 512 - 40 = 499 by norm_num]
  · rw [show (256 : ℕ) ^ 3 = 2 ^ 24 by norm_num, ← pow_add, Nat.pow_div (by norm_num) two_pos,
      show 24 + 256 - 40 = 240 by norm_num]
  · rw [show (128 : ℕ) ^ 3 = 2 ^ 21 by norm_num, ← pow_add, Nat.pow_div (by norm_num) two_pos,
      show 21 + 128 - 40 = 109 by norm_num]
  · rw [show (2 : ℕ) ^ 512 = 2 ^ 256 * 2 ^ 256 by rw [← pow_add], Nat.sqrt_eq]
  · rw [show (2 : ℕ) ^ 256 = 2 ^ 128 * 2 ^ 128 by rw [← pow_add], Nat.sqrt_eq]
  · rw [show (2 : ℕ) ^ 128 = 2 ^ 64 * 2 ^ 64 by rw [← pow_add], Nat.sqrt_eq]

end SequentialSquaring

end Cslib.Circuits.Boolean.Iteration
