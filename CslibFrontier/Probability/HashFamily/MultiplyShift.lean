/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.HashFamily
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.ModEq

/-!
# Multiply-shift hashing

The multiply-shift family of Dietzfelbinger, Hagerup, Katajainen and Penttonen
[DietzfelbingerHagerupKatajainenPenttonen1997] hashes a `w`-bit word `x` to `M` bits with a random
odd `w`-bit multiplier `a`: it keeps the top `M` bits of the low `w` bits of `a x`, that is
`(a x mod 2 ^ w) / 2 ^ (w - M)`. On a machine this is one multiplication and one shift. It is
`2 / 2 ^ M`-universal: twice the optimal bound.

The proof counts multipliers. Write the difference of two distinct inputs as `2 ^ s z'` with `z'`
odd. If the inputs collide, the top `M` bits of `a x` and `a y` agree, so `a (x - y) mod 2 ^ w`
lies within `2 ^ (w - M)` of `0` modulo `2 ^ w`. As `a` ranges over the odd multipliers,
`a (x - y) mod 2 ^ w` is `2 ^ s` times an odd residue modulo `2 ^ (w - s)`, each attained by
`2 ^ s` multipliers, and at most `2 ^ (w - M - s)` of those residues lie near `0`.

## Main definitions

* `Cslib.Probability.multiplyShift`: multiply-shift hashing with the multiplier `2 b + 1`.

## Main results

* `Cslib.Probability.card_filter_multiplyShift_eq_le`: at most `2 ^ (w - M)` of the
  `2 ^ (w - 1)` multipliers make two distinct inputs collide.
* `Cslib.Probability.isUniversalHash_multiplyShift`: multiply-shift is `2 / 2 ^ M`-universal.

## References

* [M. Dietzfelbinger, T. Hagerup, J. Katajainen, M. Penttonen, *A Reliable Randomized Algorithm
  for the Closest-Pair Problem*][DietzfelbingerHagerupKatajainenPenttonen1997], Lemma 2.4.
-/

@[expose] public section

namespace Cslib.Probability

open Finset
open scoped ENNReal

/-- Multiply-shift hashing of a `w`-bit word to `M` bits, with the odd multiplier `2 b + 1`:
the top `M` of the low `w` bits of the product. -/
def multiplyShift (w M : ℕ) (b : Fin (2 ^ (w - 1))) (x : Fin (2 ^ w)) : ℕ :=
  (2 * b + 1) * x % 2 ^ w / 2 ^ (w - M)

/-- If `u` and `u + t` have the same quotient by `P` modulo `N`, then `t` is within `P` of `0`
modulo `N`. -/
private theorem lt_or_lt_of_div_eq {u t N P : ℕ} (hP : 0 < P) (hu : u < N) (ht : t < N)
    (h : u / P = (u + t) % N / P) : t < P ∨ N - P < t := by
  have h1 := Nat.div_add_mod u P
  have h2 := Nat.div_add_mod ((u + t) % N) P
  have h3 := Nat.mod_lt u hP
  have h4 := Nat.mod_lt ((u + t) % N) hP
  rw [← h] at h2
  generalize P * (u / P) = A at h1 h2
  rcases lt_or_ge (u + t) N with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt] at h2 h4
    omega
  · have hmod : (u + t) % N = u + t - N := by
      rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt (by omega)]
    rw [hmod] at h2 h4
    omega

/-- An odd number modulo an even modulus `2 K` stays odd: `(2 Q + 1) mod 2 K = 2 (Q mod K) + 1`. -/
private theorem two_mul_add_one_mod (Q K : ℕ) (hK : 0 < K) :
    (2 * Q + 1) % (2 * K) = 2 * (Q % K) + 1 := by
  conv_lhs => rw [← Nat.div_add_mod Q K]
  rw [show 2 * (K * (Q / K) + Q % K) + 1 = (2 * K) * (Q / K) + (2 * (Q % K) + 1) by ring,
    Nat.mul_add_mod, Nat.mod_eq_of_lt (by have := Nat.mod_lt Q hK; omega)]

/-- For odd `z'`, at most `2 ^ s` of the numbers below `2 ^ s * 2 ^ j` satisfy
`(b z' + c) mod 2 ^ j = q`: they are congruent modulo `2 ^ j`, and they are told apart by their
quotients by `2 ^ j`, which are below `2 ^ s`. -/
private theorem card_filter_mod_eq_le {n s j z' c q : ℕ} (hn : n ≤ 2 ^ s * 2 ^ j) (hz' : Odd z') :
    #{b : Fin n | ((b : ℕ) * z' + c) % 2 ^ j = q} ≤ 2 ^ s := by
  have hcop : Nat.gcd (2 ^ j) z' = 1 :=
    Nat.Coprime.pow_left j (Nat.coprime_comm.mp hz'.coprime_two_right)
  calc #{b : Fin n | ((b : ℕ) * z' + c) % 2 ^ j = q} ≤ #(range (2 ^ s)) := by
        refine card_le_card_of_injOn (fun b => (b : ℕ) / 2 ^ j) (fun b _ => ?_) ?_
        · rw [coe_range, Set.mem_Iio]
          exact Nat.div_lt_of_lt_mul (by rw [mul_comm]; exact b.2.trans_le hn)
        · intro b₁ hb₁ b₂ hb₂ h
          simp only [coe_filter, mem_univ, true_and, Set.mem_ofPred_eq] at hb₁ hb₂
          have hmod : (b₁ : ℕ) ≡ b₂ [MOD 2 ^ j] :=
            Nat.ModEq.cancel_right_of_coprime hcop
              (Nat.ModEq.add_right_cancel' c (hb₁.trans hb₂.symm))
          apply Fin.ext
          rw [← Nat.div_add_mod (b₁ : ℕ) (2 ^ j), ← Nat.div_add_mod (b₂ : ℕ) (2 ^ j)]
          exact congrArg₂ (· + ·) (congrArg (2 ^ j * ·) h) hmod
    _ = 2 ^ s := card_range _

/-- Among the residues `r < J`, the values `S (2 r + 1)` within `P` of `0` modulo `S (2 J)` number
at most `P / S`, when `P` and `S` are powers of two. -/
private theorem mul_card_filter_bad_le {s j w M : ℕ} (hw : w = s + 1 + j) (hM : M ≤ w) :
    2 ^ s * #((range (2 ^ j)).filter fun r => 2 ^ s * (2 * r + 1) < 2 ^ (w - M) ∨
      2 ^ s * (2 * 2 ^ j) - 2 ^ (w - M) < 2 ^ s * (2 * r + 1)) ≤ 2 ^ (w - M) := by
  set S := 2 ^ s with hS
  set J := 2 ^ j with hJ
  have hSpos : 0 < S := by positivity
  rcases le_or_gt (w - M) s with h | h
  · -- Every value `S (2 r + 1)` is at least `S ≥ 2 ^ (w - M)` and at most `S (2 J) - S`.
    have hP : 2 ^ (w - M) ≤ S := Nat.pow_le_pow_right (by norm_num) h
    rw [filter_eq_empty_iff.mpr fun r hr => ?_, card_empty, mul_zero]
    · exact Nat.zero_le _
    rw [mem_range] at hr
    have h1 : S ≤ S * (2 * r + 1) := Nat.le_mul_of_pos_right _ (by omega)
    have h2 : S * (2 * r + 1) + S ≤ S * (2 * J) := by
      rw [← Nat.mul_add_one]
      exact Nat.mul_le_mul_left S (by omega)
    omega
  · -- The bad residues are the first `E` and the last `E`, where `2 ^ (w - M) = S (2 E)`.
    set E := 2 ^ (w - M - s - 1) with hE
    have hPE : 2 ^ (w - M) = S * (2 * E) := by
      rw [hS, hE, ← pow_succ', ← pow_add]
      congr 1
      omega
    have hEJ : E ≤ J := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [hPE]
    refine Nat.mul_le_mul_left S ?_
    calc #((range J).filter fun r => S * (2 * r + 1) < S * (2 * E) ∨
          S * (2 * J) - S * (2 * E) < S * (2 * r + 1))
        ≤ #(range E ∪ Ico (J - E) J) := by
          refine card_le_card fun r hr => ?_
          rw [mem_filter, mem_range] at hr
          rw [mem_union, mem_range, mem_Ico]
          rcases hr.2 with hA | hB
          · exact Or.inl (by have := Nat.lt_of_mul_lt_mul_left hA; omega)
          · rw [← mul_tsub] at hB
            exact Or.inr ⟨by have := Nat.lt_of_mul_lt_mul_left hB; omega, hr.1⟩
      _ ≤ #(range E) + #(Ico (J - E) J) := card_union_le _ _
      _ ≤ 2 * E := by
          rw [card_range, Nat.card_Ico]
          omega

/-- The counting bound for inputs `y < x`. -/
private theorem card_filter_lt {w M : ℕ} (hw : 0 < w) (hM : M ≤ w) {x y : Fin (2 ^ w)}
    (hxy : y < x) :
    #{b | multiplyShift w M b x = multiplyShift w M b y} ≤ 2 ^ (w - M) := by
  have hxy' : (y : ℕ) < x := hxy
  have hN : 0 < 2 ^ w := by positivity
  obtain ⟨s, z', hz', hz⟩ := Nat.exists_eq_two_pow_mul_odd (n := (x : ℕ) - y) (by omega)
  have hs : s < w := by
    have h1 : 2 ^ s ≤ (x : ℕ) - y := hz ▸ Nat.le_mul_of_pos_right _ hz'.pos
    have h2 : (x : ℕ) - y < 2 ^ w := by have := x.2; omega
    exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp (h1.trans_lt h2)
  obtain ⟨c, hc⟩ := hz'
  set j := w - s - 1 with hj
  have hwj : w = s + 1 + j := by omega
  have hNsj : 2 ^ w = 2 ^ s * (2 * 2 ^ j) := by rw [hwj, pow_add, pow_add, pow_one]; ring
  have hw1 : 2 ^ (w - 1) = 2 ^ s * 2 ^ j := by
    rw [← pow_add]
    congr 1
    omega
  -- The residue of a multiple of the difference of the inputs.
  have hkey (b : Fin (2 ^ (w - 1))) : (2 * (b : ℕ) + 1) * ((x : ℕ) - y) % 2 ^ w =
      2 ^ s * (2 * (((b : ℕ) * z' + c) % 2 ^ j) + 1) := by
    rw [hz, hNsj, show (2 * (b : ℕ) + 1) * (2 ^ s * z') =
      2 ^ s * (2 * ((b : ℕ) * z' + c) + 1) by rw [hc]; ring, Nat.mul_mod_mul_left,
      two_mul_add_one_mod _ _ (by positivity)]
  -- A collision puts that residue within `2 ^ (w - M)` of `0`.
  have hcoll (b : Fin (2 ^ (w - 1))) (h : multiplyShift w M b x = multiplyShift w M b y) :
      ((b : ℕ) * z' + c) % 2 ^ j ∈ (range (2 ^ j)).filter fun r =>
        2 ^ s * (2 * r + 1) < 2 ^ (w - M) ∨
          2 ^ s * (2 * 2 ^ j) - 2 ^ (w - M) < 2 ^ s * (2 * r + 1) := by
    rw [mem_filter, mem_range, ← hkey, ← hNsj]
    refine ⟨Nat.mod_lt _ (by positivity), ?_⟩
    have hsum : ((2 * (b : ℕ) + 1) * y % 2 ^ w + (2 * (b : ℕ) + 1) * ((x : ℕ) - y) % 2 ^ w) %
        2 ^ w = (2 * (b : ℕ) + 1) * x % 2 ^ w := by
      rw [← Nat.add_mod, ← mul_add, Nat.add_sub_cancel' hxy'.le]
    exact lt_or_lt_of_div_eq (u := (2 * (b : ℕ) + 1) * y % 2 ^ w) (by positivity)
      (Nat.mod_lt _ hN) (Nat.mod_lt _ hN) (by rw [hsum]; exact h.symm)
  calc #{b | multiplyShift w M b x = multiplyShift w M b y}
      ≤ 2 ^ s * #((range (2 ^ j)).filter fun r => 2 ^ s * (2 * r + 1) < 2 ^ (w - M) ∨
          2 ^ s * (2 * 2 ^ j) - 2 ^ (w - M) < 2 ^ s * (2 * r + 1)) := by
        refine card_le_mul_card_image_of_maps_to
          (f := fun b : Fin (2 ^ (w - 1)) => ((b : ℕ) * z' + c) % 2 ^ j)
          (fun b hb => hcoll b (mem_filter.mp hb).2) _ fun r _ => ?_
        refine (card_le_card fun b hb => ?_).trans
          (card_filter_mod_eq_le (c := c) (q := r) hw1.le ⟨c, hc⟩)
        simp only [mem_filter, mem_univ, true_and] at hb ⊢
        exact hb.2
    _ ≤ 2 ^ (w - M) := mul_card_filter_bad_le hwj hM

/-- **Multiply-shift collisions**: at most `2 ^ (w - M)` of the `2 ^ (w - 1)` odd multipliers
make two distinct `w`-bit inputs collide. -/
theorem card_filter_multiplyShift_eq_le {w M : ℕ} (hw : 0 < w) (hM : M ≤ w) {x y : Fin (2 ^ w)}
    (hxy : x ≠ y) : #{b | multiplyShift w M b x = multiplyShift w M b y} ≤ 2 ^ (w - M) := by
  rcases lt_or_gt_of_ne hxy with h | h
  · have h' := card_filter_lt hw hM h
    rwa [filter_congr fun b _ => eq_comm] at h'
  · exact card_filter_lt hw hM h

/-- **Multiply-shift is `2 / 2 ^ M`-universal**
([DietzfelbingerHagerupKatajainenPenttonen1997], Lemma 2.4): for a uniform odd `w`-bit
multiplier, two distinct `w`-bit inputs have the same top `M` bits of product with probability at
most `2 / 2 ^ M`. -/
theorem isUniversalHash_multiplyShift {w M : ℕ} (hw : 0 < w) (hM : M ≤ w) :
    IsUniversalHash (PMF.uniformOfFintype (Fin (2 ^ (w - 1)))) (multiplyShift w M)
      (2 / 2 ^ M) := by
  have h := IsUniversalHash.of_card_le (c := 2 ^ (w - M))
    fun x y hxy => card_filter_multiplyShift_eq_le hw hM hxy
  convert h using 1
  rw [Fintype.card_fin]
  push_cast
  rw [ENNReal.div_eq_div_iff (by positivity) (by simp) (by positivity) (by simp), ← pow_succ,
    ← pow_add]
  congr 1
  omega

end Cslib.Probability
