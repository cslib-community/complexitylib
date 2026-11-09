/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
import Mathlib.Data.Nat.Log
import Batteries.Data.Nat.Lemmas
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# Packing bounds for native multiplication

For every universe of size at least 257, eight words hold the carries at block boundaries,
and sixteen words hold the carries of one block. The terminal column covers both input widths.
Every bound applies to arbitrary universe sizes, including sizes between powers of two.

## Main results

* `Cslib.Logic.FO.Ordered.Multiplication.exists_parameters`: uniform packing witnesses.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999], Theorem 1.17(1).
  These bounds support the carry-table variant of the source's packed short sums.
-/

@[expose] public section

namespace Cslib.Logic.FO.Ordered.Multiplication

private theorem sixteen_mul_le_pow {h : ℕ} (hh : 8 ≤ h) : 16 * h ≤ 2 ^ h := by
  induction h, hh using Nat.le_induction with
  | base => decide
  | succ h hh ih => rw [pow_succ]; lia

private theorem sq_le_pow {d : ℕ} (hd : 4 ≤ d) : d * d ≤ 2 ^ d := by
  induction d, hd using Nat.le_induction with
  | base => decide
  | succ d hd ih => rw [pow_succ]; nlinarith

/-- Powers of two give a block size and terminal column whose packed carries fit in a fixed
number of words. The first pair characterizes the actual highest bit of `n-1`. -/
theorem exists_parameters {n : ℕ} (hn : 257 ≤ n) :
    ∃ h e m : ℕ, 2 ^ h ≤ n - 1 ∧ n - 1 < 2 ^ (h + 1) ∧
      8 ≤ h ∧ 16 * h < n ∧ e ≤ m ∧ 2 ^ e ≤ h ∧
      h + 1 < 2 ^ (2 ^ e) ∧ 2 * (h + 1) ≤ 2 ^ m ∧
      2 ^ m + 2 ^ e ≤ 8 * h ∧ (2 ^ e + 1) * 2 ^ e ≤ 16 * h := by
  let h := (n - 1).log2
  have hn0 : n - 1 ≠ 0 := by lia
  have hh : 8 ≤ h := (Nat.le_log2 hn0).mpr (by norm_num; lia)
  have hlo : 2 ^ h ≤ n - 1 := Nat.log2_self_le hn0
  have hhi : n - 1 < 2 ^ (h + 1) := (Nat.log2_lt hn0).mp (by dsimp [h]; lia)
  have hspace : 16 * h < n := lt_of_le_of_lt (sixteen_mul_le_pow hh) (by lia)
  let d := h.log2 + 1
  have hd4 : 4 ≤ d := by
    have := (Nat.le_log2 (by lia : h ≠ 0)).mpr (show 2 ^ 3 ≤ h by norm_num; lia)
    dsimp [d]
    lia
  have hpowlo : 2 ^ (d - 1) ≤ h := by simpa [d] using Nat.log2_self_le (by lia : h ≠ 0)
  have hpowhi : h < 2 ^ d := (Nat.log2_lt (by lia : h ≠ 0)).mp (by dsimp [d]; lia)
  have hd2 : d * d ≤ 2 * h := by
    have hs := sq_le_pow hd4
    have he : d = d - 1 + 1 := by lia
    rw [he, pow_succ] at hs
    nlinarith
  let e := d.log2 + 1
  have hds : d < 2 ^ e := (Nat.log2_lt (by lia : d ≠ 0)).mp (by dsimp [e]; lia)
  have hsd : 2 ^ e ≤ 2 * d := by
    have := Nat.log2_self_le (by lia : d ≠ 0)
    dsimp [e]
    rw [pow_succ]
    lia
  have hdh : 2 * d ≤ h := by nlinarith
  have he : e ≤ d + 1 := by
    have := (Nat.log2_lt (by lia : d ≠ 0)).mpr (Nat.lt_two_pow_self (n := d))
    dsimp [e]
    lia
  refine ⟨h, e, d + 1, hlo, hhi, hh, hspace, he, by lia, ?_, ?_, ?_, ?_⟩
  · have hp := Nat.pow_lt_pow_right Nat.one_lt_two hds
    have : h + 1 ≤ 2 ^ d := by lia
    exact lt_of_le_of_lt this hp
  · rw [pow_succ]
    lia
  · rw [pow_succ]
    have heq : 2 ^ d = 2 ^ (d - 1) * 2 := by rw [← pow_succ]; congr 1
    nlinarith
  · nlinarith

end Cslib.Logic.FO.Ordered.Multiplication
