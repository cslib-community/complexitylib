/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Monotone.Clique.Essential
public import Complexity.Computability.Circuit.Monotone.Clique.LowerBound
import Complexity.Foundations.Data.Nat.Choose
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Monotone clique bounds with logarithmically many petals per unit width

Razborov's approximation theorem permits a free choice of the number `p` of sunflower petals.
For a dyadic width `w = 2 ^ t`, choose `p = 4 * w * t`, instead of `w ^ 2` as in
`Complexity/Computability/Circuit/Monotone/Clique/Asymptotic.lean`.
The bound `sunflowerBound p w ≤ (4 * t * w ^ 2) ^ w`
then gives two improvements using the same approximation theorem:

* For `t ≥ 3`, `4 * w ^ 2 ≤ k - 1`, and `k ^ 4 ≤ n`, every monotone circuit for `k`-clique
  on `n` vertices has more than `w ^ w = 2 ^ (t * 2 ^ t)` gates.
* For `t ≥ 4` and the same width constraint, more than `64 ^ w` gates suffice as a lower bound
  already when `1024 * t ^ 2 * w ^ 4 * k ≤ n`.

Thus taking `w` within a factor two of `√k / 2` recovers a `log k` factor in the exponent in the
first regime, or replaces the fourth-power vertex requirement by `O(k ^ 3 * log(k) ^ 2)` in
the second. The formal statements below give the finite, integer parameter bounds. The variable
`n` counts vertices; the number of Boolean inputs is `edgeCount n`.

These are new parameter instantiations of the library's existing proof, not new lower bounds
against the monotone model beyond the literature.

## Main results

* `Cslib.Circuits.Monotone.two_pow_mul_two_pow_lt_size_of_computes_clique`: the stronger
  exponent under the fourth-power vertex hypothesis.
* `Cslib.Circuits.Monotone.sixtyFour_pow_two_pow_lt_size_of_computes_clique`: the wider range
  of clique sizes for the `64 ^ w` bound.
* `Cslib.Circuits.Monotone.two_pow_mul_two_pow_lt_ecomplexity_clique`,
  `Cslib.Circuits.Monotone.sixtyFour_pow_two_pow_lt_ecomplexity_clique`: the corresponding
  minimum circuit complexity bounds.

## References

* [A. A. Razborov, *Lower bounds on the monotone complexity of some Boolean
  functions*][Razborov1985], for the approximation method.
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Section 14.3][AroraBarak09],
  for the approximation theorem instantiated here.
-/

@[expose] public section

namespace Cslib.Circuits.Monotone

open Cslib.Circuits.Clique

private theorem sq_le_two_mul_two_pow {t : ℕ} (ht : 3 ≤ t) : t ^ 2 ≤ 2 * 2 ^ t := by
  induction t, ht using Nat.le_induction with
  | base => norm_num
  | succ t ht ih =>
      calc (t + 1) ^ 2 ≤ 2 * t ^ 2 := by nlinarith
        _ ≤ 2 * (2 * 2 ^ t) := Nat.mul_le_mul_left 2 ih
        _ = 2 * 2 ^ (t + 1) := by rw [pow_succ]; ring

private theorem sunflower_sq_mul_pow_le (t w a : ℕ) :
    sunflowerBound (4 * w * t) w ^ 2 * a ^ w ≤ (16 * t ^ 2 * w ^ 4 * a) ^ w := by
  have hB : sunflowerBound (4 * w * t) w ≤ (4 * t * w ^ 2) ^ w := by
    calc sunflowerBound (4 * w * t) w = (4 * w * t - 1) ^ w * w.factorial := rfl
      _ ≤ (4 * w * t) ^ w * w ^ w :=
        Nat.mul_le_mul (Nat.pow_le_pow_left (Nat.sub_le _ _) _) (Nat.factorial_le_pow w)
      _ = (4 * t * w ^ 2) ^ w := by rw [← mul_pow]; congr 1; ring
  calc sunflowerBound (4 * w * t) w ^ 2 * a ^ w
      ≤ ((4 * t * w ^ 2) ^ w) ^ 2 * a ^ w := by gcongr
    _ = ((4 * t * w ^ 2) ^ 2 * a) ^ w := by rw [pow_right_comm, ← mul_pow]
    _ = (16 * t ^ 2 * w ^ 4 * a) ^ w := by congr 1; ring

private theorem positive_budget_of_pow {n k p w s q : ℕ} (hq : 1 < q)
    (hwk : w + 1 ≤ k) (hn : q * k ≤ n)
    (hcore : sunflowerBound p w ^ 2 * s ≤ q ^ w) :
    Positive.errorCap n k p w * s < n.choose k := by
  have hkn : k ≤ n := (Nat.le_mul_of_pos_left k (by omega : 0 < q)).trans hn
  have hremaining : 0 < (n - (w + 1)).choose (k - (w + 1)) :=
    Nat.choose_pos (Nat.sub_le_sub_right hkn _)
  have hstrict : sunflowerBound p w ^ 2 * s < q ^ (w + 1) := by
    refine hcore.trans_lt ?_
    rw [pow_succ]
    simpa using Nat.mul_lt_mul_of_pos_left hq (pow_pos (by omega : 0 < q) w)
  calc Positive.errorCap n k p w * s =
      (sunflowerBound p w ^ 2 * s) * (n - (w + 1)).choose (k - (w + 1)) := by
        rw [Positive.errorCap]; ring
    _ < q ^ (w + 1) * (n - (w + 1)).choose (k - (w + 1)) :=
      Nat.mul_lt_mul_of_pos_right hstrict hremaining
    _ ≤ n.choose k := Nat.pow_mul_choose_sub_le_choose (by omega) hwk hn

private theorem negative_budget_of_pow {n k p w s : ℕ} (hw : 0 < w)
    (hk : 4 * w ^ 2 ≤ k - 1) (hp : p ≤ n)
    (hcore : 6 * sunflowerBound p w ^ 2 * s < 4 ^ p) :
    2 * negativeGateCap n (k - 1) p w * s < (k - 1) ^ n := by
  let B := sunflowerBound p w
  have hB : 2 * (2 * B + B ^ 2) ≤ 6 * B ^ 2 := by
    have := Nat.le_self_pow (by norm_num : 2 ≠ 0) B
    omega
  have hkpos : 0 < k - 1 := by
    have := pow_pos hw 2
    omega
  have htail : 0 < (w ^ 2) ^ p * (k - 1) ^ (n - p) := by positivity
  calc 2 * negativeGateCap n (k - 1) p w * s =
      (2 * (2 * B + B ^ 2) * s) * ((w ^ 2) ^ p * (k - 1) ^ (n - p)) := by
        simp only [negativeGateCap, Negative.pluckErrorCap, B]
        ring
    _ ≤ (6 * B ^ 2 * s) * ((w ^ 2) ^ p * (k - 1) ^ (n - p)) := by gcongr
    _ < 4 ^ p * ((w ^ 2) ^ p * (k - 1) ^ (n - p)) :=
      Nat.mul_lt_mul_of_pos_right hcore htail
    _ = (4 * w ^ 2) ^ p * (k - 1) ^ (n - p) := by rw [mul_pow]; ring
    _ ≤ (k - 1) ^ p * (k - 1) ^ (n - p) := by gcongr
    _ = (k - 1) ^ n := by rw [← pow_add, Nat.add_sub_of_le hp]

private theorem negative_core_of_dyadic {t w s a : ℕ} (htw : w = 2 ^ t)
    (hw : 3 ≤ w) (ha : 0 < a) (hbase : 2 * a ≤ w ^ 8)
    (hB : sunflowerBound (4 * w * t) w ^ 2 * s ≤ a ^ w) :
    6 * sunflowerBound (4 * w * t) w ^ 2 * s < 4 ^ (4 * w * t) := by
  have h6 : 6 < 2 ^ w := by
    have := Nat.pow_le_pow_right (by norm_num : 0 < 2) hw
    norm_num at this
    omega
  calc 6 * sunflowerBound (4 * w * t) w ^ 2 * s
      = 6 * (sunflowerBound (4 * w * t) w ^ 2 * s) := by ring
    _ ≤ 6 * a ^ w := Nat.mul_le_mul_left 6 hB
    _ < 2 ^ w * a ^ w := Nat.mul_lt_mul_of_pos_right h6 (pow_pos ha w)
    _ = (2 * a) ^ w := (mul_pow _ _ _).symm
    _ ≤ (w ^ 8) ^ w := Nat.pow_le_pow_left hbase _
    _ = 4 ^ (4 * w * t) := by
      rw [htw, ← pow_mul, ← pow_mul, show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
      congr 1
      ring

/-- With dyadic width `w = 2 ^ t`, `t ≥ 3`, `4 w² ≤ k - 1`, and `k⁴ ≤ n`, every monotone
circuit computing `k`-clique on `n` vertices has more than `w ^ w = 2 ^ (t * 2 ^ t)` gates.
The proof uses `4 * w * t` sunflower petals. -/
theorem two_pow_mul_two_pow_lt_size_of_computes_clique {n k t : ℕ} (ht : 3 ≤ t)
    (hk : 4 * (2 ^ t) ^ 2 ≤ k - 1) (hn : k ^ 4 ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) :
    2 ^ (t * 2 ^ t) < C.size := by
  let w := 2 ^ t
  change 4 * w ^ 2 ≤ k - 1 at hk
  have hw : 8 ≤ w := by
    change (2 : ℕ) ^ 3 ≤ 2 ^ t
    exact Nat.pow_le_pow_right (by norm_num) ht
  have htsq : t ^ 2 ≤ 2 * w := sq_le_two_mul_two_pow ht
  have htw : t ≤ w := Nat.lt_two_pow_self.le
  have hww : w ≤ w ^ 2 := Nat.le_self_pow (by norm_num) w
  have hkn : k ≤ n := (Nat.le_self_pow (by norm_num) k).trans hn
  have hp : 4 * w * t ≤ n := by
    calc 4 * w * t ≤ 4 * w * w := Nat.mul_le_mul_left _ htw
      _ = 4 * w ^ 2 := by ring
      _ ≤ k - 1 := hk
      _ ≤ n := (Nat.sub_le _ _).trans hkn
  have hB : sunflowerBound (4 * w * t) w ^ 2 * w ^ w ≤ (32 * w ^ 6) ^ w := by
    refine (sunflower_sq_mul_pow_le t w w).trans (Nat.pow_le_pow_left ?_ w)
    calc 16 * t ^ 2 * w ^ 4 * w ≤ 16 * (2 * w) * w ^ 4 * w := by gcongr
      _ = 32 * w ^ 6 := by ring
  have hq : 1 < k ^ 3 := by
    have : 2 ≤ k := by omega
    have := Nat.pow_le_pow_left this 3
    norm_num at this
    omega
  have hpos : Positive.errorCap n k (4 * w * t) w * w ^ w < n.choose k := by
    apply positive_budget_of_pow hq (by omega) (q := k ^ 3)
    · simpa [pow_succ] using hn
    · refine hB.trans (Nat.pow_le_pow_left ?_ w)
      calc 32 * w ^ 6 ≤ 64 * w ^ 6 := by omega
        _ = (4 * w ^ 2) ^ 3 := by ring
        _ ≤ k ^ 3 := Nat.pow_le_pow_left (by omega) 3
  have hneg : 2 * negativeGateCap n (k - 1) (4 * w * t) w * w ^ w < (k - 1) ^ n := by
    apply negative_budget_of_pow (by omega) hk hp
    refine negative_core_of_dyadic rfl (by omega) (by positivity) ?_ hB
    have hsq : 64 ≤ w ^ 2 := by simpa using Nat.pow_le_pow_left hw 2
    calc 2 * (32 * w ^ 6) = 64 * w ^ 6 := by ring
      _ ≤ w ^ 2 * w ^ 6 := Nat.mul_le_mul_right _ hsq
      _ = w ^ 8 := by ring
  have hbound := lt_size_of_computes_clique (p := 4 * w * t) (by nlinarith) (by omega)
    (by omega) (by omega) hpos hneg hC
  simpa only [w, ← pow_mul] using hbound

/-- With dyadic width `w = 2 ^ t`, `t ≥ 4`, and `4 w² ≤ k - 1`, every monotone circuit for
`k`-clique on `n` vertices has more than `64 ^ w` gates when
`1024 * t ^ 2 * w ^ 4 * k ≤ n`. The proof uses `4 * w * t` sunflower petals. -/
theorem sixtyFour_pow_two_pow_lt_size_of_computes_clique {n k t : ℕ} (ht : 4 ≤ t)
    (hk : 4 * (2 ^ t) ^ 2 ≤ k - 1)
    (hn : 1024 * t ^ 2 * (2 ^ t) ^ 4 * k ≤ n)
    {C : Circuit signature (edgeCount n) 1}
    (hC : C.Computes interpretation (single (clique n k))) :
    64 ^ (2 ^ t) < C.size := by
  let w := 2 ^ t
  let q := 1024 * t ^ 2 * w ^ 4
  change 4 * w ^ 2 ≤ k - 1 at hk
  change q * k ≤ n at hn
  have hw : 16 ≤ w := by
    change (2 : ℕ) ^ 4 ≤ 2 ^ t
    exact Nat.pow_le_pow_right (by norm_num) ht
  have htsq : t ^ 2 ≤ 2 * w := sq_le_two_mul_two_pow (by omega)
  have htw : t ≤ w := Nat.lt_two_pow_self.le
  have hww : w ≤ w ^ 2 := Nat.le_self_pow (by norm_num) w
  have hq : 1 < q := by
    have htpos : 1 ≤ t ^ 2 := one_le_pow₀ (by omega : 1 ≤ t)
    have hwpos : 1 ≤ w ^ 4 := one_le_pow₀ (by omega : 1 ≤ w)
    dsimp only [q]
    nlinarith
  have hkn : k ≤ n := (Nat.le_mul_of_pos_left k (by omega : 0 < q)).trans hn
  have hp : 4 * w * t ≤ n := by
    calc 4 * w * t ≤ 4 * w * w := Nat.mul_le_mul_left _ htw
      _ = 4 * w ^ 2 := by ring
      _ ≤ k - 1 := hk
      _ ≤ n := (Nat.sub_le _ _).trans hkn
  have hB : sunflowerBound (4 * w * t) w ^ 2 * 64 ^ w ≤ q ^ w := by
    refine (sunflower_sq_mul_pow_le t w 64).trans_eq ?_
    congr 1
    dsimp only [q]
    ring
  have hpos : Positive.errorCap n k (4 * w * t) w * 64 ^ w < n.choose k :=
    positive_budget_of_pow hq (by omega) hn hB
  have hneg : 2 * negativeGateCap n (k - 1) (4 * w * t) w * 64 ^ w < (k - 1) ^ n := by
    apply negative_budget_of_pow (by omega) hk hp
    refine negative_core_of_dyadic rfl (by omega) (by omega) ?_ hB
    have hcube : 4096 ≤ w ^ 3 := by simpa using Nat.pow_le_pow_left hw 3
    calc 2 * q = 2048 * t ^ 2 * w ^ 4 := by dsimp only [q]; ring
      _ ≤ 2048 * (2 * w) * w ^ 4 := by gcongr
      _ = 4096 * w ^ 5 := by ring
      _ ≤ w ^ 3 * w ^ 5 := Nat.mul_le_mul_right _ hcube
      _ = w ^ 8 := by ring
  exact lt_size_of_computes_clique (p := 4 * w * t) (by nlinarith) (by omega)
    (by omega) (by omega) hpos hneg hC

/-- The minimum monotone circuit size for `k`-clique exceeds `2 ^ (t * 2 ^ t)` under the
dyadic-width and fourth-power vertex hypotheses. -/
theorem two_pow_mul_two_pow_lt_ecomplexity_clique {n k t : ℕ} (ht : 3 ≤ t)
    (hk : 4 * (2 ^ t) ^ 2 ≤ k - 1) (hn : k ^ 4 ≤ n) :
    ((2 ^ (t * 2 ^ t) : ℕ) : ℕ∞) < ecomplexity interpretation (single (clique n k)) := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top _), le_ecomplexity_iff]
  intro C hC
  exact_mod_cast two_pow_mul_two_pow_lt_size_of_computes_clique ht hk hn hC

/-- The minimum monotone circuit size for `k`-clique exceeds `64 ^ (2 ^ t)` under the
dyadic-width and `1024 * t ^ 2 * (2 ^ t) ^ 4 * k ≤ n` vertex hypotheses. -/
theorem sixtyFour_pow_two_pow_lt_ecomplexity_clique {n k t : ℕ} (ht : 4 ≤ t)
    (hk : 4 * (2 ^ t) ^ 2 ≤ k - 1)
    (hn : 1024 * t ^ 2 * (2 ^ t) ^ 4 * k ≤ n) :
    ((64 ^ (2 ^ t) : ℕ) : ℕ∞) < ecomplexity interpretation (single (clique n k)) := by
  rw [← ENat.add_one_le_iff (ENat.natCast_ne_top _), le_ecomplexity_iff]
  intro C hC
  exact_mod_cast sixtyFour_pow_two_pow_lt_size_of_computes_clique ht hk hn hC

end Cslib.Circuits.Monotone
