/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.Classes.Hierarchy.Time
public import Complexity.Computability.Complexity.Classes.Padding.Polynomial
public import Complexity.Computability.Complexity.Classes.Time.Polynomial

/-!
# The deterministic hierarchy at every integer polynomial degree

For integers `1 ≤ a < b`, `DTIME (n ^ a)` is strictly contained in `DTIME (n ^ b)` on bit
strings. The result has the conventional native multitape-machine semantics of `DTIME`.

For `a ≥ 2`, the proof amplifies a hypothetical collapse by native polynomial padding. A collapse
between degrees `a` and `b` propagates to degrees `a * k` and `b * k`. Once `a ≤ k`, these
intervals overlap: `a * (k + 1) ≤ b * k`. Consequently all classes at degrees `a * k`, for
`k ≥ a`, collapse to degree `a * a`. The existing polynomial-overhead diagonal theorem gives a
strict hierarchy farther along that tail, a contradiction. Thus sharp separation of integer
degrees does not require a new universal simulator.

For the remaining linear case, rounding the padding length to a power of two permits a faster
native writer. A collapse from quadratic to linear time would then imply a collapse from
quartic to cubic time, contradicting the preceding argument.

The hierarchy is a classical consequence of the deterministic time hierarchy
[Arora and Barak, Theorem 3.1][AroraBarak09]. The proof below combines native polynomial padding
with the library's weaker certified diagonal theorem; the overlapping-exponent amplification
is proved here. Arbitrary real exponents and logarithmic gaps are not claimed by this theorem.

## Main results

* `Cslib.Complexity.DTIME_succ_pow_ssubset_DTIME_succ_pow`: strictness for `(n + 1)` powers.
* `Cslib.Complexity.DTIME_pow_ssubset_DTIME_pow`: strictness for the conventional `n` powers.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM Filter

private theorem coarse_polynomial_hierarchy {d : ℕ} (hd : 2 ≤ d) :
    DTIME encBits (fun n => (n + 1) ^ d) ⊂
      DTIME encBits (fun n => (n + 1) ^ (3 * d + 9)) := by
  refine DTIME_ssubset_DTIME (timeConstructible_succ_pow hd)
    (fun n => (Nat.le_succ n).trans (Nat.le_self_pow (by omega) _)) ?_
  filter_upwards [eventually_ge_atTop 7] with n hn
  have hp : (n + 1) ^ d + 1 ≤ 2 * (n + 1) ^ d := by
    have := Nat.one_le_pow d (n + 1) (by omega)
    omega
  calc (n + 1) ^ 8 * ((n + 1) ^ d + 1) ^ 3
      ≤ (n + 1) ^ 8 * (2 * (n + 1) ^ d) ^ 3 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hp 3)
    _ = 8 * (n + 1) ^ (3 * d + 8) := by
      rw [mul_pow, ← pow_mul (n + 1) d 3,
        show 3 * d + 8 = 8 + d * 3 by omega, pow_add (n + 1) 8 (d * 3)]
      norm_num only [Nat.reducePow]
      ac_rfl
    _ ≤ (n + 1) * (n + 1) ^ (3 * d + 8) := Nat.mul_le_mul_right _ (by omega)
    _ = (n + 1) ^ (3 * d + 9) := by
      rw [show 3 * d + 9 = (3 * d + 8) + 1 by omega]
      exact (pow_succ' _ _).symm

private theorem polynomial_hierarchy_of_two_le {a b : ℕ} (ha : 2 ≤ a) (hab : a < b) :
    DTIME encBits (fun n => (n + 1) ^ a) ⊂ DTIME encBits (fun n => (n + 1) ^ b) := by
  refine ⟨DTIME_mono (fun n => Nat.pow_le_pow_right (by omega) hab.le), ?_⟩
  intro hcollapse
  have hstep (k : ℕ) (hk : a ≤ k) :
      DTIME encBits (fun n => (n + 1) ^ (a * (k + 1))) ⊆
        DTIME encBits (fun n => (n + 1) ^ (a * k)) := by
    have hexp : a * (k + 1) ≤ b * k := by nlinarith
    exact (DTIME_mono fun n => Nat.pow_le_pow_right (by omega) hexp).trans
      (DTIME_pow_mul_subset_of_subset ha hab.le (by omega) hcollapse)
  have htail (k : ℕ) (hk : a ≤ k) :
      DTIME encBits (fun n => (n + 1) ^ (a * k)) ⊆
        DTIME encBits (fun n => (n + 1) ^ (a * a)) := by
    induction k, hk using Nat.le_induction with
    | base => exact Set.Subset.refl _
    | succ k hk ih => exact (hstep k hk).trans ih
  have hstrict := coarse_polynomial_hierarchy (d := a * a) (by nlinarith)
  apply hstrict.2
  have hexp : 3 * (a * a) + 9 ≤ a * (3 * a + 9) := by nlinarith
  exact (DTIME_mono fun n => Nat.pow_le_pow_right (by omega) hexp).trans
    (htail (3 * a + 9) (by omega))

private theorem linear_quadratic_hierarchy :
    DTIME encBits (fun n => (n + 1) ^ 1) ⊂ DTIME encBits (fun n => (n + 1) ^ 2) := by
  refine ⟨DTIME_mono (fun n => Nat.pow_le_pow_right (by omega) (by omega)), ?_⟩
  intro hcollapse
  have hstrict := polynomial_hierarchy_of_two_le (a := 3) (b := 4) (by omega) (by omega)
  apply hstrict.2
  simpa using DTIME_pow_mul_subset_of_subset_max (a := 1) (b := 2) (k := 2)
    (by omega) (by omega) hcollapse

/-- **Every two distinct positive integer polynomial degrees give distinct time classes.**
Above the quadratic threshold, a collapse propagates to overlapping intervals of exponents.
At the linear threshold, rounded padding would turn a quadratic-to-linear collapse into a
quartic-to-cubic collapse. Both conclusions contradict the native diagonal theorem. -/
theorem DTIME_succ_pow_ssubset_DTIME_succ_pow {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    DTIME encBits (fun n => (n + 1) ^ a) ⊂ DTIME encBits (fun n => (n + 1) ^ b) := by
  by_cases htwo : 2 ≤ a
  · exact polynomial_hierarchy_of_two_le htwo hab
  · have haone : a = 1 := by omega
    subst a
    refine ⟨DTIME_mono (fun n => Nat.pow_le_pow_right (by omega) hab.le), ?_⟩
    intro hcollapse
    exact linear_quadratic_hierarchy.2
      ((DTIME_mono fun n => Nat.pow_le_pow_right (by omega) (show 2 ≤ b by omega)).trans
        hcollapse)

/-- **Strict deterministic polynomial time levels.** For integers `1 ≤ a < b`, some binary
language is decidable in time `O(n ^ b)` but not `O(n ^ a)`, using the native finite-state,
binary-alphabet multitape machines and the usual additive constants in `DTIME`. -/
theorem DTIME_pow_ssubset_DTIME_pow {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    DTIME encBits (fun n => n ^ a) ⊂ DTIME encBits (fun n => n ^ b) := by
  simpa only [DTIME_succ_pow_eq] using DTIME_succ_pow_ssubset_DTIME_succ_pow ha hab

end Cslib.Complexity
