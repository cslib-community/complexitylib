/-
Copyright (c) 2026 Anthropic, PBC, Erik Demaine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Anthropic, PBC, Erik Demaine
-/

module
-- upstream: candidate

public import Complexity.Algorithms.MatrixMultiplication.Schonhage.Full
public import Complexity.Foundations.Algebra.FiniteMagnitude
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Shared coordinate transforms in flat arrays

After `j` coordinates have been transformed, the array has `10^j * 7^k` entries, where
`j + k = L`. Its entry at `(p, r)` sums the input entries with suffix `r`, weighting their
prefixes by the product of the selected coefficients. The next coordinate transform computes
each new entry from seven entries of this shared array. It does not independently enumerate
all input entries for every final leaf.

## Main definitions

* `CoordinateTransform.weight`: product of coefficients along the transformed prefix.
* `CoordinateTransform.value`: prefix expansion at a mixed-radix array position.

## Main results

* `CoordinateTransform.value_step`: the seven-to-ten shared coordinate update.
* `CoordinateTransform.stageSize_le`: every stage has at most `10^L` entries.

## References

An iterative implementation invariant for [AlmanWilliams2026, Section 2.4.1]. The coefficients
are those of the existing encoding API, adapted from Anthropic, PBC's formal source at
`16a5ce41304fcdaea4e0be7c132e1c361dc26da5`. This module defines mathematical arrays and sums,
not a separate machine or an instruction-counting semantics.
-/

@[expose] public section

namespace Cslib.Algorithms.MatrixMultiplication.Schonhage.CoordinateTransform

open Finset

/-- Product of `j` coefficients, reading prefix digits from least significant to most
significant. Values at noncanonical indices are harmless; clients use indices below the powers. -/
def weight (c : ℕ → ℕ → ℤ) : ℕ → ℕ → ℕ → ℤ
  | 0, _, _ => 1
  | j + 1, p, v => weight c j (p / 10) (v / 7) * c (p % 10) (v % 7)

/-- Value at transformed prefix `p` and original suffix `r`. The remaining suffix has `k`
base-seven digits; the original input index is `v * 7^k + r`. -/
def value (c : ℕ → ℕ → ℤ) (j k : ℕ) (a : ℕ → ℤ) (p r : ℕ) : ℤ :=
  ∑ v ∈ range (7 ^ j), weight c j p v * a (v * 7 ^ k + r)

private theorem sum_blocks (m n : ℕ) (f : ℕ → ℤ) :
    ∑ i ∈ range (m * n), f i = ∑ q ∈ range m, ∑ s ∈ range n, f (q * n + s) := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [Nat.succ_mul, sum_range_add, ih, sum_range_succ]

/-- At the initial stage no coordinate is transformed, so the entry is the input itself. -/
theorem value_zero (c : ℕ → ℕ → ℤ) (k : ℕ) (a : ℕ → ℤ) (p r : ℕ) :
    value c 0 k a p r = a r := by
  simp [value, weight]

/-- The next array entry uses seven already shared values. This is the exact algebraic
invariant of the mixed-radix native loop. -/
theorem value_step (c : ℕ → ℕ → ℤ) (j k : ℕ) (a : ℕ → ℤ) (p r : ℕ)
    {t : ℕ} (ht : t < 10) :
    value c (j + 1) k a (p * 10 + t) r =
      ∑ s ∈ range 7, c t s * value c j (k + 1) a p (s * 7 ^ k + r) := by
  simp only [value, pow_succ, sum_blocks]
  rw [sum_comm]
  refine sum_congr rfl fun s hs => ?_
  have hs7 := mem_range.mp hs
  simp only [mul_sum]
  refine sum_congr rfl fun q _ => ?_
  have hp : (p * 10 + t) / 10 = p := by omega
  have hq : (q * 7 + s) / 7 = q := by omega
  simp only [weight, hp, hq, Nat.add_mod, Nat.mul_mod_left, Nat.mod_eq_of_lt ht,
    Nat.mod_eq_of_lt hs7, zero_add]
  have hidx : (q * 7 + s) * 7 ^ k + r = q * (7 ^ k * 7) + (s * 7 ^ k + r) := by ring
  rw [hidx]
  ring

/-- Each prefix product has absolute value at most one. -/
theorem abs_weight_le {c : ℕ → ℕ → ℤ} (hc : ∀ t < 10, ∀ s < 7, |c t s| ≤ 1)
    (j p v : ℕ) : |weight c j p v| ≤ 1 := by
  induction j generalizing p v with
  | zero => simp [weight]
  | succ j ih =>
    rw [weight, abs_mul]
    exact (mul_le_mul (ih _ _) (hc _ (Nat.mod_lt _ (by decide)) _
      (Nat.mod_lt _ (by decide))) (abs_nonneg _) (by decide : (0 : ℤ) ≤ 1)).trans
        (by norm_num)

/-- Intermediate transformed values are bounded from the original input values. -/
theorem abs_value_le {c : ℕ → ℕ → ℤ} (hc : ∀ t < 10, ∀ s < 7, |c t s| ≤ 1)
    (j k p r : ℕ) {a : ℕ → ℤ} {A : ℤ}
    (ha : ∀ v < 7 ^ j, |a (v * 7 ^ k + r)| ≤ A) :
    |value c j k a p r| ≤ (7 ^ j : ℕ) * A := by
  exact (abs_sum_mul_le (range (7 ^ j)) (fun v _ => abs_weight_le hc j p v)
    (fun v hv => ha v (mem_range.mp hv))).trans_eq (by simp)

/-- Input bounds suffice for every shared intermediate value, including all depths and all
prefixes. Only the original input segment is used in this estimate. -/
theorem abs_value_le_of_input {c : ℕ → ℕ → ℤ}
    (hc : ∀ t < 10, ∀ s < 7, |c t s| ≤ 1) {L j k : ℕ} (hjk : j + k = L)
    (p r : ℕ) (hr : r < 7 ^ k) {a : ℕ → ℤ} {A : ℤ}
    (ha : ∀ i < 7 ^ L, |a i| ≤ A) : |value c j k a p r| ≤ (7 ^ j : ℕ) * A := by
  apply abs_value_le hc
  intro v hv
  have hprod := Nat.mul_le_mul_right (7 ^ k) (Nat.succ_le_of_lt hv)
  have hidx : v * 7 ^ k + r < 7 ^ j * 7 ^ k := by nlinarith only [hprod, hr]
  rw [← pow_add, hjk] at hidx
  exact ha _ hidx

private theorem index_cons {b L : ℕ} (s : Fin b) (u : Fin L → Fin b) :
    (finFunctionFinEquiv (Fin.cons s u) : ℕ) = s.val + b * (finFunctionFinEquiv u : ℕ) := by
  simp only [finFunctionFinEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ,
    Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ, Finset.mul_sum]
  congr 1
  apply sum_congr rfl
  intro i _
  ring

/-- Digitwise coefficients as a total flat table. Only the first ten rows and seven columns
are read by the transform. -/
def table (c : Fin 10 → Fin 7 → ℤ) (t s : ℕ) : ℤ :=
  c ⟨t % 10, Nat.mod_lt _ (by decide)⟩ ⟨s % 7, Nat.mod_lt _ (by decide)⟩

/-- Flat prefix weights are exactly the product of the original coordinate coefficients.
`finFunctionFinEquiv` supplies the existing Mathlib digit numbering, least significant first. -/
theorem weight_index (c : Fin 10 → Fin 7 → ℤ) {L : ℕ}
    (τ : Fin L → Fin 10) (u : Fin L → Fin 7) :
    weight (table c) L (finFunctionFinEquiv τ) (finFunctionFinEquiv u) =
      ∏ i, c (τ i) (u i) := by
  induction L with
  | zero => simp [weight]
  | succ L ih =>
    rw [← Fin.cons_self_tail τ, ← Fin.cons_self_tail u, index_cons, index_cons, weight]
    have ht : ((τ 0).val + 10 * (finFunctionFinEquiv (Fin.tail τ) : ℕ)) / 10 =
        (finFunctionFinEquiv (Fin.tail τ) : ℕ) := by omega
    have hu : ((u 0).val + 7 * (finFunctionFinEquiv (Fin.tail u) : ℕ)) / 7 =
        (finFunctionFinEquiv (Fin.tail u) : ℕ) := by omega
    have htmod : ((τ 0).val + 10 * (finFunctionFinEquiv (Fin.tail τ) : ℕ)) % 10 =
        (τ 0).val := by omega
    have humod : ((u 0).val + 7 * (finFunctionFinEquiv (Fin.tail u) : ℕ)) % 7 =
        (u 0).val := by omega
    rw [ht, hu, htmod, humod, ih, Fin.prod_univ_succ]
    simp only [table, Nat.mod_eq_of_lt (τ 0).isLt, Nat.mod_eq_of_lt (u 0).isLt,
      Fin.cons_zero, Fin.cons_succ]
    exact mul_comm _ _

/-- At the final stage the flat transform is the tensor encoding sum on digit strings.
The input array is supplied explicitly by its values at Mathlib's numbered string positions. -/
theorem value_final (c : Fin 10 → Fin 7 → ℤ) (L : ℕ)
    (a : (Fin L → Fin 7) → ℤ) (arr : ℕ → ℤ)
    (harr : ∀ u, arr (finFunctionFinEquiv u) = a u) (τ : Fin L → Fin 10) :
    value (table c) L 0 arr (finFunctionFinEquiv τ) 0 =
      ∑ u, a u * ∏ i, c (τ i) (u i) := by
  simp only [value, pow_zero, mul_one, add_zero]
  rw [← Fin.sum_univ_eq_sum_range]
  rw [← (finFunctionFinEquiv (m := 7) (n := L)).sum_comp]
  apply sum_congr rfl
  intro u _
  rw [weight_index, harr, mul_comm]

/-- The mixed-radix stage fits into a buffer of `10^(j+k)` entries. -/
theorem stageSize_le (j k : ℕ) : 10 ^ j * 7 ^ k ≤ 10 ^ (j + k) := by
  rw [pow_add]
  exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (by decide : 7 ≤ 10) k)

/-- Even charging every one of the `L` stages at the maximum array size gives only
`L * 10^L` cells. This is a combinatorial bound; native loop and arithmetic costs are separate. -/
theorem total_stageSize_le (L : ℕ) :
    ∑ j ∈ range L, 10 ^ (j + 1) * 7 ^ (L - (j + 1)) ≤ L * 10 ^ L := by
  calc
    _ ≤ ∑ _j ∈ range L, 10 ^ L := by
      apply sum_le_sum
      intro j hj
      have hjL : j + 1 ≤ L := by have := mem_range.mp hj; omega
      simpa only [Nat.add_sub_of_le hjL] using stageSize_le (j + 1) (L - (j + 1))
    _ = _ := by simp

end Cslib.Algorithms.MatrixMultiplication.Schonhage.CoordinateTransform
