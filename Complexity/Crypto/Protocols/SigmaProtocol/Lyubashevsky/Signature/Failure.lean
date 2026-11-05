/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Crypto.Protocols.SigmaProtocol.Lyubashevsky.Signature
import Complexity.Probability.PMF

/-!
# Signing failure uniformly over deterministic hashes

The interactive fixed-challenge abort formula does not apply directly when a signing hash
chooses its challenge from the commitment. Instead, every randomness vector in the smaller
box of radius `γ - 2β` succeeds for every challenge. This gives a hash-independent upper bound
on failure. The geometric estimate is an original formalization lemma, not a security reduction.

## Main results

* `lyubashevskySignAttempt_none_le`: failure at most `4 m β / (2γ + 1)` for every hash.
-/

public section

namespace Cslib.Crypto.Protocols.SigmaProtocol

open Probability Probability.PMF
open scoped ENNReal _root_.Matrix

/-- An inner randomness vector succeeds even when the hash chooses a challenge from its
commitment. The public-key relation is unnecessary for this availability estimate. -/
theorem lyubashevskySignAttempt_none_le {n m k q γ β η : ℕ} {M : Type}
    (hβ : 2 * β ≤ γ) (hη : k * η ≤ β)
    {S : Matrix (Fin m) (Fin k) ℤ} (hS : ∀ i j, |S i j| ≤ η)
    (y : Matrix (Fin n) (Fin m) (ZMod q) × Matrix (Fin n) (Fin k) (ZMod q))
    (hash : M × (Fin n → ZMod q) → BitString k) (msg : M) :
    lyubashevskySignAttempt n m k q γ β hash S y msg none ≤
      4 * m * β / (2 * γ + 1 : ℝ≥0∞) := by
  have hsmall (r : Fin m → ℤ) (hr : r ∈ intBox (Fin m) (γ - 2 * β)) :
      r + S *ᵥ lyubashevskyChallenge (hash (msg, y.1 *ᵥ (Int.cast ∘ r))) ∈
        intBox (Fin m) (γ - β) := by
    have hv := intBox_mono hη
      (mulVec_lyubashevskyChallenge_mem_intBox hS (hash (msg, y.1 *ᵥ (Int.cast ∘ r))))
    simp only [mem_intBox] at hr hv ⊢
    intro i
    calc
      |(r + S *ᵥ lyubashevskyChallenge (hash (msg, y.1 *ᵥ (Int.cast ∘ r)))) i| ≤
          |r i| + |(S *ᵥ lyubashevskyChallenge (hash (msg, y.1 *ᵥ (Int.cast ∘ r)))) i| :=
        abs_add_le _ _
      _ ≤ (γ - 2 * β : ℕ) + (β : ℤ) := add_le_add (hr i) (hv i)
      _ = (γ - β : ℕ) := by omega
  have hcompare : lyubashevskySignAttempt n m k q γ β hash S y msg none ≤
      boxReject (Fin m) γ (2 * β) 0 none := by
    rw [← PMF.toOuterMeasure_apply_singleton, ← PMF.toOuterMeasure_apply_singleton]
    simp only [lyubashevskySignAttempt, fsAbortSignAttempt, lyubashevsky, PMF.map_comp,
      boxReject, shiftReject, PMF.toOuterMeasure_map_apply]
    apply MeasureTheory.measure_mono
    intro r hr
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Function.comp_apply,
      fsAbortSignStep, add_zero] at hr ⊢
    by_contra hn
    have hrsmall : r ∈ intBox (Fin m) (γ - 2 * β) := by
      simpa using hn
    have := hsmall r hrsmall
    simp [this] at hr
  refine hcompare.trans ?_
  simpa only [Fintype.card_fin, Nat.cast_mul, Nat.cast_ofNat, mul_assoc, mul_left_comm,
    mul_comm, show (2 * 2 : ℝ≥0∞) = 4 by norm_num] using
    boxReject_apply_none_le hβ (zero_mem_intBox (ι := Fin m) (2 * β))

end Cslib.Crypto.Protocols.SigmaProtocol
