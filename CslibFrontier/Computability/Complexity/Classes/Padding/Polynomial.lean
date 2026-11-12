/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Classes.Time
import CslibFrontier.Computability.Complexity.Classes.Padding.Translation
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Foundations.Data.Nat.AffineBound

/-!
# Degree-preserving deterministic padding

A collapse from time `(n + 1) ^ b` to `(n + 1) ^ a`, where `1 ≤ a ≤ b`, propagates after
multiplying both exponents by a positive integer `k`. This is the translation lemma
`Cslib.Complexity.DTIME_comp_subset_of_subset` for the padding function `(n + 1) ^ k`, which loses
only constant factors.

This specializes the standard translation argument
[Fortnow and Santhanam, §3.3, Lemma 5][FortnowSanthanam2006] to integer powers with all native
computation costs proved. No class-closure or simulation hypothesis is hidden in the statement.

## Main results

* `Cslib.Complexity.DTIME_pow_mul_subset_of_subset`: a deterministic polynomial-time collapse
  propagates after multiplying both exponents by the same positive integer.

## References

* [L. Fortnow and R. Santhanam, §3.3, Lemma 5][FortnowSanthanam2006]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- A collapse between positive polynomial time degrees propagates under polynomial padding:
pad inputs of length `n` to length `(n + 1) ^ k`. -/
theorem DTIME_pow_mul_subset_of_subset {a b k : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) (hk : 1 ≤ k)
    (h : DTIME encBits (fun n => (n + 1) ^ b) ⊆ DTIME encBits (fun n => (n + 1) ^ a)) :
    DTIME encBits (fun n => (n + 1) ^ (b * k)) ⊆
      DTIME encBits (fun n => (n + 1) ^ (a * k)) := by
  have hG : ComputableInPolyTime (fun n : ℕ => (n + 1) ^ k) encNat encNat :=
    ComputableInPolyTime.binary_pow' (by fun_prop) (.const k)
  have hlt (n : ℕ) : n < (n + 1) ^ k :=
    Nat.lt_of_lt_of_le (Nat.lt_succ_self n) (Nat.le_self_pow (by omega) _)
  have hT := DTIME_comp_subset_of_subset (fun _ _ hmn => Nat.pow_le_pow_left (by omega) b)
    (fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _))
    (fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)) hG hlt h
  refine (DTIME_mono fun n => ?_).trans (hT.trans (DTIME_mono_of_le_mul_add (C := 2 ^ a)
    fun n => ?_))
  · rw [Function.comp_apply, Nat.mul_comm b k, pow_mul]
    exact Nat.pow_le_pow_left (Nat.le_succ _) b
  · rw [Function.comp_apply, Nat.mul_comm a k, pow_mul]
    exact Nat.add_one_pow_le_two_pow_mul_add a _

end Cslib.Complexity
