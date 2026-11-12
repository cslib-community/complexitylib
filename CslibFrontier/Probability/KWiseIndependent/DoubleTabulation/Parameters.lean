/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.KWiseIndependent.DoubleTabulation
import CslibFrontier.Foundations.Data.Nat.Power
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Parameter arithmetic for Thorup's Double Tabulation bound

Consumers of `card_not_isKUnique_eight_mul_le` (dictionaries hashing with Double Tabulation at
`q = 4`, `d = 8 * c`) all instantiate it the same way: `c = 2 * max c_exp 1` characters of
bit-width `b = (1 + Nat.clog 2 (max n_max 4)) / 2` for a polynomial universe
`U ≤ max n_max 4 ^ c_exp` above `doubleTabThreshold c_exp`, and then turn the counting bound into
a high-probability statement for a load factor `B`. This file packages those steps.

## Main results

* `two_mul_card_not_isKUnique_mul_le`: if `2 * B * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)`
  and `1 ≤ B`, then at most a `1 / (2 * B)` fraction of top-level tables fail to be `k`-unique.
* `doubleTab_canonical_params`: the canonical choice of `c` and `b` covers the universe
  (`U ≤ 2 ^ (c * b)`), clears `doubleTabMinB c_exp ≤ b`, and has `max n_max 4 ≤ 2 ^ (2 * b)`.
* `mul_doubleTabCodeBound_le`: once `doubleTabMinB c_exp ≤ b`, a load factor
  `A ≤ 2 ^ (2 * b) * b ^ 2` times the code bound for `k ≤ b ^ 2` stays below `2 ^ (3 * b)`.

## References

* [M. Thorup, *Simple Tabulation, Fast Expanders, Double Tabulation,
  and High Independence*][Thorup2013]
-/

public section

namespace Cslib.Probability

open Finset

/-- **High-probability `k`-uniqueness of Double Tabulation top tables (`[Thorup2013]`, Theorem
1(a))**: when `1 ≤ B` and `2 * B * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)`, the number of
top-level tables `T₁` whose `simpleTabTuple T₁` fails to be `k`-unique is at most a `1 / (2 * B)`
fraction of all top-level tables. -/
theorem two_mul_card_not_isKUnique_mul_le {c b k B : ℕ} (hc : 1 ≤ c) (hB : 1 ≤ B)
    (hbound : 2 * B * doubleTabCodeBound c (8 * c) 4 k ≤ 2 ^ (3 * b)) :
    2 * #(univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b =>
        ¬ IsKUnique k (simpleTabTuple T₁)) * B ≤
      Fintype.card (DoubleTabTopSeed c (8 * c) b) := by
  set Bad := #(univ.filter fun T₁ : DoubleTabTopSeed c (8 * c) b =>
    ¬ IsKUnique k (simpleTabTuple T₁))
  set Code := doubleTabCodeBound c (8 * c) 4 k
  set N := Fintype.card (DoubleTabTopSeed c (8 * c) b)
  have hbound_code : 2 * Code ≤ 2 ^ (3 * b) := by
    calc 2 * Code = 2 * 1 * Code := by ring
      _ ≤ 2 * B * Code := Nat.mul_le_mul_right Code (Nat.mul_le_mul_left 2 hB)
      _ ≤ 2 ^ (3 * b) := hbound
  have hbad_le : 2 ^ (6 * b) * Bad ≤ 2 * Code ^ 2 * N :=
    card_not_isKUnique_eight_mul_le hc hbound_code
  have hmul : 2 ^ (6 * b) * (2 * Bad * B) ≤ 2 ^ (6 * b) * N := by
    calc 2 ^ (6 * b) * (2 * Bad * B)
        = (2 * B) * (2 ^ (6 * b) * Bad) := by ring
      _ ≤ (2 * B) * (2 * Code ^ 2 * N) := Nat.mul_le_mul_left _ hbad_le
      _ = (2 * B * (2 * Code ^ 2)) * N := by ring
      _ ≤ (2 * B * Code) ^ 2 * N := by
        refine Nat.mul_le_mul_right N ?_
        have hB_sq : B ≤ B * B := Nat.le_mul_of_pos_left B hB
        nlinarith
      _ ≤ (2 ^ (3 * b)) ^ 2 * N := by gcongr
      _ = 2 ^ (6 * b) * N := by
        rw [← Nat.pow_mul]
        congr 2
        ring
  exact Nat.le_of_mul_le_mul_left hmul (Nat.two_pow_pos (6 * b))

/-- **Canonical Double Tabulation parameters**: for `c = 2 * max c_exp 1` characters of bit-width
`b = (1 + Nat.clog 2 (max n_max 4)) / 2`, a polynomial universe `U ≤ max n_max 4 ^ c_exp` fits in
`c` characters, the capacity satisfies `max n_max 4 ≤ 2 ^ (2 * b)`, and above
`doubleTabThreshold c_exp` the bit-width clears `doubleTabMinB c_exp`. -/
theorem doubleTab_canonical_params {c_exp n_max U : ℕ}
    (hge : doubleTabThreshold c_exp ≤ n_max) (hU : U ≤ max n_max 4 ^ c_exp) :
    U ≤ 2 ^ (2 * max c_exp 1 * ((1 + Nat.clog 2 (max n_max 4)) / 2)) ∧
      doubleTabMinB c_exp ≤ (1 + Nat.clog 2 (max n_max 4)) / 2 ∧
      max n_max 4 ≤ 2 ^ (2 * ((1 + Nat.clog 2 (max n_max 4)) / 2)) := by
  have hclog_le : Nat.clog 2 (max n_max 4) ≤ 2 * ((1 + Nat.clog 2 (max n_max 4)) / 2) := by
    omega
  have hmax_le : max n_max 4 ≤ 2 ^ (2 * ((1 + Nat.clog 2 (max n_max 4)) / 2)) :=
    (Nat.le_pow_clog (by decide) (max n_max 4)).trans
      (Nat.pow_le_pow_right (by decide) hclog_le)
  refine ⟨?_, ?_, hmax_le⟩
  · calc U ≤ max n_max 4 ^ c_exp := hU
      _ ≤ max n_max 4 ^ max c_exp 1 :=
        Nat.pow_le_pow_right (by omega) (le_max_left c_exp 1)
      _ ≤ (2 ^ (2 * ((1 + Nat.clog 2 (max n_max 4)) / 2))) ^ max c_exp 1 := by gcongr
      _ = 2 ^ (2 * max c_exp 1 * ((1 + Nat.clog 2 (max n_max 4)) / 2)) := by
        rw [← Nat.pow_mul]
        congr 1
        ring
  · have hpow_le : 2 ^ (2 * doubleTabMinB c_exp) ≤ 2 ^ Nat.clog 2 (max n_max 4) := by
      rw [← doubleTabThreshold_eq]
      exact (hge.trans (le_max_left n_max 4)).trans (Nat.le_pow_clog (by decide) (max n_max 4))
    have hclog_ge : 2 * doubleTabMinB c_exp ≤ Nat.clog 2 (max n_max 4) :=
      (Nat.pow_le_pow_iff_right (by decide)).mp hpow_le
    omega

/-- **Code-bound budget for the canonical parameters**: with `c = 2 * max c_exp 1` and
`doubleTabMinB c_exp ≤ b`, a load factor `A ≤ 2 ^ (2 * b) * b ^ 2` times
`doubleTabCodeBound c (8 * c) 4 k` for a key count `k ≤ b ^ 2` is at most `2 ^ (3 * b)`. -/
theorem mul_doubleTabCodeBound_le {c_exp b k A : ℕ} (hb : doubleTabMinB c_exp ≤ b)
    (hk : k ≤ b ^ 2) (hA : A ≤ 2 ^ (2 * b) * b ^ 2) :
    A * doubleTabCodeBound (2 * max c_exp 1) (8 * (2 * max c_exp 1)) 4 k ≤ 2 ^ (3 * b) := by
  set c := 2 * max c_exp 1
  have hb_min : 4 * (24 * c + 8) ^ 2 ≤ b := doubleTabMinB_eq c_exp ▸ hb
  have hb_8c : 8 * c ≤ b := by nlinarith
  have hck_cube : c * k ≤ b ^ 3 := by
    calc c * k ≤ b * b ^ 2 := Nat.mul_le_mul (by omega) hk
      _ = b ^ 3 := by ring
  have hcode_pow : doubleTabCodeBound c (8 * c) 4 k ≤ b ^ (24 * c + 5) := by
    unfold doubleTabCodeBound
    calc c * ((c * k) ^ (2 * c) * (8 * c)) ^ 4
        ≤ b * (((b ^ 3) ^ (2 * c) * b) ^ 4) :=
          Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left
            (Nat.mul_le_mul (Nat.pow_le_pow_left hck_cube (2 * c)) hb_8c) 4)
      _ = b ^ (24 * c + 5) := by
        rw [← Nat.pow_mul, ← pow_succ, ← Nat.pow_mul, ← pow_succ']
        congr 1
        ring
  calc A * doubleTabCodeBound c (8 * c) 4 k
      ≤ (2 ^ (2 * b) * b ^ 2) * b ^ (24 * c + 5) := Nat.mul_le_mul hA hcode_pow
    _ = 2 ^ (2 * b) * b ^ (24 * c + 7) := by
        rw [Nat.mul_assoc, ← Nat.pow_add]
        congr 2
        ring
    _ ≤ 2 ^ (2 * b) * b ^ (24 * c + 8) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) (by omega))
    _ ≤ 2 ^ (2 * b) * 2 ^ b :=
        Nat.mul_le_mul_left _ (Nat.pow_le_two_pow (by omega) hb_min)
    _ = 2 ^ (3 * b) := by
        rw [← Nat.pow_add]
        congr 1
        ring

end Cslib.Probability
