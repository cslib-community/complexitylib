/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.Khrapchenko
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Zify

/-!
# Yablonskii's formulas for parity

Write `n = 2 ^ k + r` with `r ≤ 2 ^ k`. Splitting the bits into blocks of `2 ^ (k - 1) + ⌊r / 2⌋`
and `2 ^ (k - 1) + ⌈r / 2⌉` bits and combining formulas for their parities by
`x ⊕ y = (x ∧ ¬y) ∨ (¬x ∧ y)` gives a De Morgan formula (see
`CslibFrontier/Computability/Circuit/Boolean/Formula.lean`) for
the parity of `n` bits of leaf size at most `2 ^ k (2 ^ k + 3 r)` [Yablonskii1954], [Jukna2012]
(`exists_formula_parity_two_pow_add`). The bound is exactly additive along the recursion:
`2 m (2 m + 3 r) = 2 · m (m + 3 s) + 2 · m (m + 3 t)` for `m = 2 ^ (k - 1)`, `s = ⌊r / 2⌋` and
`t = ⌈r / 2⌉`, and an exclusive or doubles the leaves of both arguments.

As `9 (2 ^ k + r) ^ 2 - 8 · 2 ^ k (2 ^ k + 3 r) = (2 ^ k - 3 r) ^ 2`, the parity of any number
`n` of bits has a formula of leaf size at most `9 n ^ 2 / 8`
(`exists_formula_parity_eight_mul_leafSize_le`), within a factor `9 / 8` of Khrapchenko's lower
bound `n ^ 2` (`sq_le_leafSize_of_computes_parity`). For `r = 0` the construction is the balanced
formula `parityFormula`, whose leaf size `n ^ 2` is optimal.

The formulas are balanced: they have at most `2 ⌈log₂ n⌉` AND and OR gates on every path
(`depthWith_binaryCost_yablonskiiFormula`), so the formula depth of parity, with negations free,
is at most `2 ⌈log₂ n⌉` (`formulaDepth_parity_le_two_mul_clog`).

## Main definitions

* `Cslib.Circuits.Boolean.yablonskiiFormula`: Yablonskii's formula for the parity of `2 ^ k + r`
  consecutive bits.

## Main results

* `Cslib.Circuits.Boolean.exists_formula_parity_two_pow_add`: the parity of `2 ^ k + r` bits,
  `r ≤ 2 ^ k`, has a De Morgan formula of leaf size at most `2 ^ k (2 ^ k + 3 r)`.
* `Cslib.Circuits.Boolean.exists_formula_parity_eight_mul_leafSize_le`: the parity of `n` bits has
  a De Morgan formula of leaf size at most `9 n ^ 2 / 8`.
* `Cslib.Circuits.Boolean.formulaDepth_parity_le_two_mul_clog`: the formula depth of the parity of
  `n` bits is at most `2 ⌈log₂ n⌉`.

## References

* [S. V. Yablonskii, *Realization of a linear function in the class of π-schemes*][Yablonskii1954]
* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib.Circuits.Boolean

open Finset

variable {n : ℕ}

/-- **Yablonskii's formula** for the parity of the `2 ^ k + r` bits from `o` on, where `r ≤ 2 ^ k`:
the exclusive or of such formulas for the first `2 ^ (k - 1) + ⌊r / 2⌋` and the remaining
`2 ^ (k - 1) + ⌈r / 2⌉` bits. For `r = 0` it is `parityFormula k o` (`yablonskiiFormula_zero`). -/
def yablonskiiFormula : (k r o : ℕ) → r ≤ 2 ^ k → o + (2 ^ k + r) ≤ n → Formula signature n
  | 0, 0, o, _, h => .input ⟨o, by rw [pow_zero] at h; omega⟩
  | 0, _ + 1, o, _, h =>
    (Formula.input ⟨o, by rw [pow_zero] at h; omega⟩).xor
      (.input ⟨o + 1, by rw [pow_zero] at h; omega⟩)
  | k + 1, r, o, hr, h =>
    (yablonskiiFormula k (r / 2) o (by rw [pow_succ] at hr; omega)
      (by rw [pow_succ] at h; omega)).xor
      (yablonskiiFormula k (r - r / 2) (o + (2 ^ k + r / 2)) (by rw [pow_succ] at hr; omega)
        (by rw [pow_succ] at h; omega))

/-- Yablonskii's formula computes the parity of the `2 ^ k + r` bits from `o` on. -/
theorem eval_yablonskiiFormula (k r o : ℕ) (hr : r ≤ 2 ^ k) (h : o + (2 ^ k + r) ≤ n)
    (x : BitString n) :
    (yablonskiiFormula k r o hr h).eval interpretation x =
      parityOn ({i | o ≤ (i : ℕ) ∧ (i : ℕ) < o + (2 ^ k + r)} : Finset (Fin n)) x := by
  induction k generalizing r o with
  | zero =>
    rw [pow_zero] at hr
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with rfl | rfl
    · rw [pow_zero, parityOn_consecutive_one o (by rw [pow_zero] at h; omega)]
      rfl
    · rw [pow_zero] at h
      rw [pow_zero, parityOn_consecutive_add, parityOn_consecutive_one o (by omega),
        parityOn_consecutive_one (o + 1) (by omega)]
      exact Formula.eval_xor _ _ x
  | succ k ih =>
    rw [yablonskiiFormula, Formula.eval_xor, ih, ih, ← parityOn_consecutive_add]
    congr 1
    ext i
    simp only [mem_filter, mem_univ, true_and, pow_succ]
    omega

/-- Yablonskii's formula has leaf size at most `2 ^ k (2 ^ k + 3 r)`. -/
theorem leafSize_yablonskiiFormula_le (k r o : ℕ) (hr : r ≤ 2 ^ k) (h : o + (2 ^ k + r) ≤ n) :
    (yablonskiiFormula k r o hr h).leafSize ≤ 2 ^ k * (2 ^ k + 3 * r) := by
  induction k generalizing r o with
  | zero =>
    rw [pow_zero] at hr
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with rfl | rfl
    · simp [yablonskiiFormula]
    · simp [yablonskiiFormula]
  | succ k ih =>
    rw [yablonskiiFormula, Formula.leafSize_xor]
    have e : 2 ^ (k + 1) * (2 ^ (k + 1) + 3 * r) =
        2 * (2 ^ k * (2 ^ k + 3 * (r / 2))) + 2 * (2 ^ k * (2 ^ k + 3 * (r - r / 2))) := by
      have hr2 : r = r / 2 + (r - r / 2) := by omega
      conv_lhs => rw [hr2]
      ring
    rw [e]
    exact Nat.add_le_add (Nat.mul_le_mul_left 2 (ih ..)) (Nat.mul_le_mul_left 2 (ih ..))

/-- Counting only AND and OR gates, Yablonskii's formula has depth `2 k` for `r = 0` and
`2 (k + 1)` for `r > 0`. -/
theorem depthWith_binaryCost_yablonskiiFormula (k r o : ℕ) (hr : r ≤ 2 ^ k)
    (h : o + (2 ^ k + r) ≤ n) :
    (yablonskiiFormula k r o hr h).depthWith binaryCost = 2 * k + if r = 0 then 0 else 2 := by
  induction k generalizing r o with
  | zero =>
    rw [pow_zero] at hr
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hr with rfl | rfl
    · rfl
    · simp [yablonskiiFormula, Formula.xor]
  | succ k ih =>
    rw [yablonskiiFormula]
    simp only [Formula.xor, Formula.depthWith_or, Formula.depthWith_and, Formula.depthWith_not,
      binaryCost_and, binaryCost_or, binaryCost_not, ih]
    split_ifs <;> omega

/-- For `r = 0`, Yablonskii's formula is the balanced formula `parityFormula`. -/
theorem yablonskiiFormula_zero (k o : ℕ) (h : o + (2 ^ k + 0) ≤ n) :
    yablonskiiFormula k 0 o (Nat.zero_le _) h = parityFormula k o h := by
  induction k generalizing o with
  | zero => rfl
  | succ k ih =>
    rw [yablonskiiFormula, parityFormula, ih, ih]
    rfl

/-- Counting only AND and OR gates, the balanced formula `parityFormula k o` has depth `2 k`. -/
theorem depthWith_binaryCost_parityFormula (k o : ℕ) (h : o + 2 ^ k ≤ n) :
    (parityFormula k o h).depthWith binaryCost = 2 * k := by
  rw [← yablonskiiFormula_zero k o h, depthWith_binaryCost_yablonskiiFormula]
  simp

/-- Yablonskii's formula on all `2 ^ k + r` bits computes their parity. -/
theorem computes_yablonskiiFormula (k r : ℕ) (hr : r ≤ 2 ^ k) :
    (yablonskiiFormula k r 0 hr (Nat.zero_add _).le : Formula signature (2 ^ k + r)).Computes
      interpretation (parity (2 ^ k + r)) := fun x => by
  rw [eval_yablonskiiFormula]
  congr 1
  ext i
  simp

/-- The constant formula `false` computes the parity of no bits. -/
theorem computes_const_false_parity_zero :
    (Formula.const false : Formula signature 0).Computes interpretation (parity 0) := fun x => by
  rw [Formula.eval_const, parity, univ_eq_empty, parityOn_empty]

/-- **Yablonskii's bound.** The parity of `2 ^ k + r` bits, `r ≤ 2 ^ k`, has a De Morgan formula of
leaf size at most `2 ^ k (2 ^ k + 3 r)`. -/
theorem exists_formula_parity_two_pow_add {k r : ℕ} (hr : r ≤ 2 ^ k) :
    ∃ F : Formula signature (2 ^ k + r), F.Computes interpretation (parity (2 ^ k + r)) ∧
      F.leafSize ≤ 2 ^ k * (2 ^ k + 3 * r) :=
  ⟨_, computes_yablonskiiFormula k r hr, leafSize_yablonskiiFormula_le ..⟩

/-- Every `n ≠ 0` is `2 ^ k + r` with `r ≤ 2 ^ k`, for `k = ⌊log₂ n⌋`. -/
private theorem exists_eq_two_pow_add {n : ℕ} (hn : n ≠ 0) :
    ∃ k r, r ≤ 2 ^ k ∧ n = 2 ^ k + r := by
  have h₁ := Nat.pow_log_le_self 2 hn
  have h₂ := Nat.lt_pow_succ_log_self one_lt_two n
  rw [Nat.pow_succ] at h₂
  exact ⟨Nat.log 2 n, n - 2 ^ Nat.log 2 n, by omega, by omega⟩

/-- **Yablonskii's bound, uniformly.** The parity of `n` bits has a De Morgan formula of leaf size
at most `9 n ^ 2 / 8`. -/
theorem exists_formula_parity_eight_mul_leafSize_le (n : ℕ) :
    ∃ F : Formula signature n, F.Computes interpretation (parity n) ∧
      8 * F.leafSize ≤ 9 * n ^ 2 := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact ⟨_, computes_const_false_parity_zero, by simp⟩
  obtain ⟨k, r, hr, rfl⟩ := exists_eq_two_pow_add hn
  obtain ⟨F, hF, hL⟩ := exists_formula_parity_two_pow_add hr
  refine ⟨F, hF, (Nat.mul_le_mul_left 8 hL).trans ?_⟩
  zify
  nlinarith [sq_nonneg ((2 : ℤ) ^ k - 3 * r)]

/-- The formula depth of the parity of `n` bits, with negations free, is at most `2 ⌈log₂ n⌉`. -/
theorem formulaDepth_parity_le_two_mul_clog (n : ℕ) :
    formulaDepth (parity n) ≤ 2 * Nat.clog 2 n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact (formulaDepth_le computes_const_false_parity_zero).trans (by simp)
  obtain ⟨k, r, hr, rfl⟩ := exists_eq_two_pow_add hn
  refine (formulaDepth_le (computes_yablonskiiFormula k r hr)).trans ?_
  rw [depthWith_binaryCost_yablonskiiFormula]
  split_ifs with h
  · rw [h, Nat.add_zero, Nat.add_zero, Nat.clog_pow 2 k one_lt_two]
  · have : k < Nat.clog 2 (2 ^ k + r) := (Nat.lt_clog_iff_pow_lt one_lt_two).2 (by omega)
    omega

end Cslib.Circuits.Boolean
