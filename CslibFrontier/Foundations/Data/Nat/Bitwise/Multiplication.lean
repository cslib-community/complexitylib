/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.Nat.Bitwise.SumTree
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Nat.Bitwise
import Mathlib.Tactic.Ring

/-!
# Binary multiplication columns and carries

Each multiplication column is a bitwise subword of the first input. Its number of set bits is
the column's unnormalized coefficient. The weighted coefficients sum to the ordinary product;
bounded carries normalize them to the product bits.

## Main definitions

* `Cslib.BitString.mulColumnWord`: the contributing rows of one multiplication column.
* `Cslib.BitString.mulColumn`: its number of contributing rows.
* `Cslib.BitString.mulPrefix`: the weighted sum `∑ j < k, mulColumn x y j * 2 ^ j` of the columns
  below `k`.
* `Cslib.BitString.mulCarry`: the actual carry entering a column.

## Main results

* `Cslib.BitString.mulColumnWord_le`: each column word fits wherever the first input fits.
* `Cslib.BitString.mulCarry_add_column`: the exact arithmetic carry equation.
* `Cslib.BitString.mul_eq_of_columns`: zero-ended exact carry equations determine multiplication.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 1.17(1) and Lemma 1.18.
  This carry formulation supports a packed-block variant of the source's short-sum proof.
-/

@[expose] public section

namespace Cslib.BitString

open Finset

/-- The set bits record exactly the rows contributing to column `j`. -/
def mulColumnWord (x y j : ℕ) : ℕ :=
  x &&& Nat.ofBits (fun i : Fin (j + 1) => y.testBit (j - i.val))

/-- A column word is a subword of the first input, including in non-power-of-two universes. -/
theorem mulColumnWord_le (x y j : ℕ) : mulColumnWord x y j ≤ x := Nat.and_le_left

/-- The exact bitwise meaning of a multiplication column. -/
theorem mulColumnWord_testBit (x y j i : ℕ) :
    (mulColumnWord x y j).testBit i = true ↔
      x.testBit i = true ∧ i ≤ j ∧ y.testBit (j - i) = true := by
  by_cases hi : i ≤ j <;>
    simp [mulColumnWord, Nat.testBit_ofBits, Nat.lt_succ_iff, hi]

/-- The unnormalized coefficient of `2^j` in binary multiplication. -/
def mulColumn (x y j : ℕ) : ℕ := (mulColumnWord x y j).bitIndices.length

/-- At most one row per input bit contributes to a column. -/
theorem mulColumn_le {x w : ℕ} (hx : x < 2 ^ w) (y j : ℕ) : mulColumn x y j ≤ w := by
  rw [mulColumn, ← Nat.sum_testBit_eq_length_bitIndices
    (lt_of_le_of_lt (mulColumnWord_le _ _ _) hx)]
  calc
    (∑ i ∈ range w, ((mulColumnWord x y j).testBit i).toNat) ≤ ∑ _i ∈ range w, 1 := by
      apply sum_le_sum
      intro i _
      cases (mulColumnWord x y j).testBit i <;> decide
    _ = w := by simp

private def pairs (x y : ℕ) : Finset (ℕ × ℕ) := x.bitIndices.toFinset ×ˢ y.bitIndices.toFinset

private theorem mulColumn_eq_card (x y j : ℕ) :
    mulColumn x y j = ((pairs x y).filter (fun p => p.1 + p.2 = j)).card := by
  rw [mulColumn, ← List.toFinset_card_of_nodup Nat.bitIndices_nodup]
  apply card_bij (fun i _ => (i, j - i))
  · intro i hi
    simp only [List.mem_toFinset, Nat.mem_bitIndices, mulColumnWord_testBit] at hi
    simp only [mem_filter, pairs, mem_product, List.mem_toFinset, Nat.mem_bitIndices]
    exact ⟨⟨hi.1, hi.2.2⟩, by lia⟩
  · intro i _ i' _ he
    exact (Prod.mk.inj he).1
  · intro p hp
    simp only [mem_filter, pairs, mem_product, List.mem_toFinset, Nat.mem_bitIndices] at hp
    refine ⟨p.1, ?_, ?_⟩
    · simp only [List.mem_toFinset, Nat.mem_bitIndices, mulColumnWord_testBit]
      exact ⟨hp.1.1, by lia, by simpa only [show j - p.1 = p.2 by lia] using hp.1.2⟩
    · apply Prod.ext
      · rfl
      · dsimp
        lia

private theorem sum_pairs (x y : ℕ) :
    ∑ p ∈ pairs x y, 2 ^ (p.1 + p.2) = x * y := by
  simp only [pairs, sum_product, pow_add]
  rw [← sum_mul_sum]
  simp only [List.sum_toFinset _ Nat.bitIndices_nodup, Nat.sum_map_two_pow_bitIndices]

/-- The weighted contribution of all columns strictly below `k`. -/
def mulPrefix (x y k : ℕ) : ℕ := ∑ j ∈ range k, mulColumn x y j * 2 ^ j

theorem mulPrefix_succ (x y k : ℕ) :
    mulPrefix x y (k + 1) = mulPrefix x y k + mulColumn x y k * 2 ^ k := sum_range_succ _ _

private theorem mulPrefix_eq_filter (x y k : ℕ) :
    mulPrefix x y k = ∑ p ∈ (pairs x y).filter (fun p => p.1 + p.2 < k), 2 ^ (p.1 + p.2) := by
  have hf (j : ℕ) (hj : j ∈ range k) :
      ((pairs x y).filter (fun p => p.1 + p.2 < k)).filter (fun p => p.1 + p.2 = j) =
        (pairs x y).filter (fun p => p.1 + p.2 = j) := by
    ext p
    simp only [mem_filter]
    constructor
    · exact fun h => ⟨h.1.1, h.2⟩
    · rintro ⟨hp, he⟩
      exact ⟨⟨hp, he ▸ mem_range.mp hj⟩, he⟩
  calc
    mulPrefix x y k = ∑ j ∈ range k,
        ∑ p ∈ ((pairs x y).filter (fun p => p.1 + p.2 < k)).filter
          (fun p => p.1 + p.2 = j), 2 ^ (p.1 + p.2) := by
      apply sum_congr rfl
      intro j hj
      rw [hf j hj, sum_const_nat (fun p hp => by rw [(mem_filter.mp hp).2]), mulColumn_eq_card]
    _ = _ := sum_fiberwise_of_maps_to (fun p hp => mem_range.mpr (mem_filter.mp hp).2) _

/-- Omitting higher columns preserves all lower product bits. -/
private theorem mulPrefix_mod (x y k : ℕ) : mulPrefix x y k % 2 ^ k = x * y % 2 ^ k := by
  rw [mulPrefix_eq_filter, sum_filter, ← sum_pairs]
  conv_lhs => rw [sum_nat_mod]
  conv_rhs => rw [sum_nat_mod]
  congr 1
  apply sum_congr rfl
  intro p _
  by_cases hp : p.1 + p.2 < k
  · simp [hp]
  · simp only [hp, ite_false, Nat.zero_mod]
    exact (Nat.mod_eq_zero_of_dvd (Nat.pow_dvd_pow 2 (by lia))).symm

/-- Once both inputs' bit widths are covered, the weighted columns give the whole product. -/
private theorem mulPrefix_eq_mul {x y w k : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hk : 2 * w ≤ k) : mulPrefix x y k = x * y := by
  rw [mulPrefix_eq_filter]
  have hp : (pairs x y).filter (fun p => p.1 + p.2 < k) = pairs x y := by
    apply filter_eq_self.mpr
    intro p hp
    simp only [pairs, mem_product, List.mem_toFinset, Nat.mem_bitIndices] at hp
    have hi := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
      (lt_of_le_of_lt (Nat.ge_two_pow_of_testBit hp.1) hx)
    have hj := (Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp
      (lt_of_le_of_lt (Nat.ge_two_pow_of_testBit hp.2) hy)
    lia
  rw [hp, sum_pairs]

/-- The carry entering column `k`, constructed from the actual lower columns. -/
def mulCarry (x y k : ℕ) : ℕ := mulPrefix x y k / 2 ^ k

/-- No carry enters column `0`. -/
@[simp] theorem mulCarry_zero (x y : ℕ) : mulCarry x y 0 = 0 := by simp [mulCarry, mulPrefix]

theorem mulCarry_succ (x y k : ℕ) :
    mulCarry x y (k + 1) = (mulCarry x y k + mulColumn x y k) / 2 := by
  simp only [mulCarry, mulPrefix_succ, pow_succ, ← Nat.div_div_eq_div_mul,
    Nat.add_mul_div_right _ _ (Nat.two_pow_pos k)]

private theorem testBit_toNat (x k : ℕ) : (x.testBit k).toNat = x / 2 ^ k % 2 := by
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have := Nat.mod_lt (x / 2 ^ k) two_pos
  by_cases h : x / 2 ^ k % 2 = 1
  · simp [h]
  · have hz : x / 2 ^ k % 2 = 0 := by lia
    simp [hz]

/-- The actual carries satisfy the exact, nonmodular column equation. -/
theorem mulCarry_add_column (x y k : ℕ) :
    mulCarry x y k + mulColumn x y k = ((x * y).testBit k).toNat + 2 * mulCarry x y (k + 1) := by
  have hm := congrArg (fun t => t / 2 ^ k) (mulPrefix_mod x y (k + 1))
  rw [pow_succ, Nat.mod_mul_right_div_self, Nat.mod_mul_right_div_self,
    mulPrefix_succ, Nat.add_mul_div_right _ _ (Nat.two_pow_pos k)] at hm
  change (mulCarry x y k + mulColumn x y k) % 2 = x * y / 2 ^ k % 2 at hm
  rw [mulCarry_succ, testBit_toNat, ← hm]
  exact (Nat.mod_add_div _ _).symm

/-- Carries never exceed the number of available rows. -/
theorem mulCarry_le {x w : ℕ} (hx : x < 2 ^ w) (y k : ℕ) : mulCarry x y k ≤ w := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [mulCarry_succ]
    have := mulColumn_le hx y k
    lia

/-- The terminal carry vanishes once the full product width is covered. -/
theorem mulCarry_eq_zero {x y w k : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hk : 2 * w ≤ k) : mulCarry x y k = 0 := by
  rw [mulCarry, mulPrefix_eq_mul hx hy hk]
  apply Nat.div_eq_of_lt
  calc
    x * y ≤ x * 2 ^ w := Nat.mul_le_mul_left x (Nat.le_of_lt hy)
    _ < 2 ^ w * 2 ^ w := Nat.mul_lt_mul_of_pos_right hx (Nat.two_pow_pos w)
    _ = 2 ^ (2 * w) := by rw [← pow_add]; congr 1; lia
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by decide) hk

/-- Exact carry equations propagate the weighted-prefix invariant through a block. -/
private theorem mulPrefix_eq_of_carries {x y z j s : ℕ} (c : ℕ → ℕ)
    (hstart : mulPrefix x y j = z % 2 ^ j + c 0 * 2 ^ j)
    (hstep : ∀ t < s, c t + mulColumn x y (j + t) =
      (z.testBit (j + t)).toNat + 2 * c (t + 1)) :
    mulPrefix x y (j + s) = z % 2 ^ (j + s) + c s * 2 ^ (j + s) := by
  have hp (t : ℕ) (ht : t ≤ s) :
      mulPrefix x y (j + t) = z % 2 ^ (j + t) + c t * 2 ^ (j + t) := by
    induction t with
    | zero => simpa using hstart
    | succ t ih =>
      rw [show j + (t + 1) = j + t + 1 by lia]
      calc
        mulPrefix x y (j + t + 1) =
            mulPrefix x y (j + t) + mulColumn x y (j + t) * 2 ^ (j + t) := mulPrefix_succ ..
        _ = z % 2 ^ (j + t) + (c t + mulColumn x y (j + t)) * 2 ^ (j + t) := by
          rw [ih (by lia)]; ring
        _ = z % 2 ^ (j + t) + ((z.testBit (j + t)).toNat + 2 * c (t + 1)) * 2 ^ (j + t) := by
          rw [hstep t (by lia)]
        _ = z % 2 ^ (j + t + 1) + c (t + 1) * 2 ^ (j + t + 1) := by
          rw [pow_succ, Nat.mod_mul, ← testBit_toNat]
          ring
  exact hp s (le_refl s)

/-- Any exact zero-ended carry sequence determines ordinary multiplication. -/
theorem mul_eq_of_columns {x y z w k : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hz : z < 2 ^ k) (hk : 2 * w ≤ k) (c : ℕ → ℕ) (hzero : c 0 = 0) (hend : c k = 0)
    (hstep : ∀ i < k, c i + mulColumn x y i = (z.testBit i).toNat + 2 * c (i + 1)) :
    x * y = z := by
  have hp := mulPrefix_eq_of_carries (j := 0) c
    (by simp [mulPrefix, hzero, Nat.mod_one]) (by simpa only [Nat.zero_add] using hstep)
  simpa only [Nat.zero_add, mulPrefix_eq_mul hx hy hk, hend, Nat.zero_mul, Nat.add_zero,
    Nat.mod_eq_of_lt hz] using hp

/-- Blocks sharing their endpoint carries determine multiplication. The boundary sequence
is global, while the interior witnesses may be chosen separately for every block. -/
theorem mul_eq_of_blocks {x y z w k s : ℕ} (hx : x < 2 ^ w) (hy : y < 2 ^ w)
    (hz : z < 2 ^ k) (hk : 2 * w ≤ k) (hs : 0 < s) (hks : s ∣ k)
    (c : ℕ → ℕ) (hzero : c 0 = 0) (hend : c k = 0)
    (hblock : ∀ q, q * s < k → ∃ a : ℕ → ℕ,
      a 0 = c (q * s) ∧ a s = c (q * s + s) ∧
      ∀ t < s, a t + mulColumn x y (q * s + t) =
        (z.testBit (q * s + t)).toNat + 2 * a (t + 1)) : x * y = z := by
  have hp (q : ℕ) (hq : q * s ≤ k) :
      mulPrefix x y (q * s) = z % 2 ^ (q * s) + c (q * s) * 2 ^ (q * s) := by
    induction q with
    | zero => simp [mulPrefix, hzero, Nat.mod_one]
    | succ q ih =>
      rw [Nat.succ_mul] at hq ⊢
      obtain ⟨a, ha0, has, hast⟩ := hblock q (by lia)
      have hstart : mulPrefix x y (q * s) = z % 2 ^ (q * s) + a 0 * 2 ^ (q * s) := by
        rw [ha0]
        exact ih (by lia)
      simpa only [has] using mulPrefix_eq_of_carries a hstart hast
  have he : k / s * s = k := Nat.div_mul_cancel hks
  have hp' := hp (k / s) (by rw [he])
  rw [he] at hp'
  simpa only [mulPrefix_eq_mul hx hy hk, hend, Nat.zero_mul, Nat.add_zero,
    Nat.mod_eq_of_lt hz] using hp'

end Cslib.BitString
