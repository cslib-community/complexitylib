/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.Totient
public import Mathlib.Data.Int.ModEq

/-!
# Finite prime collision bounds

A nonzero integer has at most its binary logarithm many distinct prime divisors.
The finite-set form avoids reconstructing prime-factor membership in applications.
-/

public section

namespace Nat

/-- A finite set of prime divisors of a nonzero integer has logarithmically bounded size. -/
theorem card_filter_prime_dvd_le_log {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    {d : ℤ} (hd : d ≠ 0) :
    (Q.filter fun (p : ℕ) => (p : ℤ) ∣ d).card ≤ Nat.log 2 d.natAbs := by
  apply le_trans (Finset.card_le_card _) (card_primeFactors_le_log _)
  intro p hp
  obtain ⟨hpQ, hpd⟩ := Finset.mem_filter.mp hp
  exact mem_primeFactors.mpr
    ⟨hQ p hpQ, Int.natCast_dvd.mp hpd, Int.natAbs_ne_zero.mpr hd⟩


/-- Congruence collisions for one fixed pair, among any finite set of primes. -/
theorem card_filter_modEq_le_log {Q : Finset ℕ} (hQ : ∀ p ∈ Q, p.Prime)
    {M a b : ℕ} (ha : a ≤ M) (hb : b ≤ M) (hne : a ≠ b) :
    (Q.filter fun p => Nat.ModEq p a b).card ≤ Nat.log2 M := by
  have hd : (b : ℤ) - a ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast hne.symm)
  have hab : ((b : ℤ) - a).natAbs ≤ M := by omega
  simpa only [Nat.modEq_iff_dvd, Nat.log2_eq_log_two] using
    (card_filter_prime_dvd_le_log hQ hd).trans (Nat.log_mono_right hab)

end Nat
