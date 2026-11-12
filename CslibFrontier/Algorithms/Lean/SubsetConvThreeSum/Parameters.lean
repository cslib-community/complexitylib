/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Nat.Choose.Basic
import CslibFrontier.Foundations.Data.Nat.Choose.MaxTerm
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Tactic.NormNum

/-!
# The parameters of the truly subquadratic 3SUM algorithm

The parameter family used for [ChanItakuraMaYu2026], Corollary 2.4. For a unit `m ≥ 1`, inputs
have at most `n = 2 ^ (100 m)` elements, and the reduction uses rank `t = 18 m`, dimension
`d = 119 m`, threshold `s = 33 m` and `μ = ⌊4 ^ (d + 2) / #P⌋ + 1` trials, where
`#P = (d choose 2 t) (2 t choose t)`. These are the paper's `t = γ lg n̂`, `d = t + lg n̂ + O(…)`,
`s = (2 γ - δ) lg n̂` with `γ = 0.18`, one extra bit of `d` per unit and `δ = 0.03`; the ratios
are integers so that every estimate is a comparison of integers.

The binomial estimates, with the powers of `m` cancelled
(`Nat.pow_le_succ_mul_choose_mul_pow_mul_pow` and its companions in
`CslibFrontier.Foundations.Data.Nat.Choose.MaxTerm`):

* `119 ^ (119 m) ≤ (119 m + 1) (119 m choose 36 m) 36 ^ (36 m) 83 ^ (83 m)` (`choose_d_lower`),
* `(119 m choose 36 m) 36 ^ (36 m) 83 ^ (83 m) ≤ 119 ^ (119 m)` (`choose_d_upper`),
* `Pre · 33 ^ (33 m) 86 ^ (86 m) ≤ 119 ^ (119 m)` for `Pre = ∑_{j ≤ 33 m} (119 m choose j)`
  (`pre_upper`),
* `Q · 3 ^ (3 m) 33 ^ (33 m) ≤ 36 ^ (36 m)` for `Q = ∑_{33 m ≤ j ≤ 36 m} (36 m choose j)`
  (`query_upper`).

The comparisons of the resulting bases with `2 ^ 199`, which make the exponent `2 - 1/100`, are
checked in `CslibFrontier.Algorithms.Lean.SubsetConvThreeSum.ExpectedCost`.

## References

* [T. M. Chan, R. Itakura, Z. Ma, Y. Yu, *3SUM Made Simpler (Without Matrix Multiplication),
  k-SUM Hypothesis Refuted for Odd k, and Real 3SUM/APSP Derandomized*][ChanItakuraMaYu2026]
-/

public section

namespace Cslib.Algorithms.Lean.SubsetConvThreeSum.Params

open Finset

/-- The rank `t = 18 m`. -/
@[expose] def t (m : ℕ) : ℕ := 18 * m
/-- The dimension `d = 119 m`. -/
@[expose] def d (m : ℕ) : ℕ := 119 * m
/-- The threshold `s = 33 m`. -/
@[expose] def s (m : ℕ) : ℕ := 33 * m
/-- The input size bound `n = 2 ^ (100 m)`. -/
@[expose] def n (m : ℕ) : ℕ := 2 ^ (100 * m)
/-- `#P = (d choose 2 t) (2 t choose t)`, the number of ordered pairs of disjoint `t`-sets. -/
@[expose] def numPairs (m : ℕ) : ℕ := (d m).choose (2 * t m) * (2 * t m).choose (t m)
/-- The number of trials `μ = ⌊4 ^ (d + 2) / #P⌋ + 1`. -/
@[expose] def μ (m : ℕ) : ℕ := 4 ^ (d m + 2) / numPairs m + 1
/-- The preprocessing sum `Pre = ∑_{j ≤ s} (d choose j)`. -/
@[expose] def pre (m : ℕ) : ℕ := ∑ j ∈ range (s m + 1), (d m).choose j
/-- The query sum `Q = ∑_{s ≤ j ≤ 2 t} (2 t choose j)`. -/
@[expose] def query (m : ℕ) : ℕ := ∑ j ∈ Icc (s m) (2 * t m), (2 * t m).choose j

theorem two_mul_t (m : ℕ) : 2 * t m = 36 * m := by unfold t; ring

private theorem cancel {m A B : ℕ} (hm : 1 ≤ m) {k : ℕ} (h : A * m ^ k ≤ B * m ^ k) : A ≤ B :=
  Nat.le_of_mul_le_mul_right h (pow_pos (by omega) _)

/-- `119 ^ (119 m) ≤ (119 m + 1) (119 m choose 36 m) 36 ^ (36 m) 83 ^ (83 m)`. -/
theorem choose_d_lower {m : ℕ} (hm : 1 ≤ m) :
    119 ^ (119 * m) ≤ (d m + 1) * ((d m).choose (2 * t m) * 36 ^ (36 * m) * 83 ^ (83 * m)) := by
  have h := Nat.pow_le_succ_mul_choose_mul_pow_mul_pow (36 * m) (83 * m)
  rw [show 36 * m + 83 * m = 119 * m by ring, mul_pow, mul_pow, mul_pow] at h
  refine cancel (k := 119 * m) hm ?_
  rw [two_mul_t]; unfold d
  calc 119 ^ (119 * m) * m ^ (119 * m) ≤ _ := h
    _ = _ := by rw [show 119 * m = 36 * m + 83 * m by ring, pow_add m]; ring

/-- `(119 m choose 36 m) 36 ^ (36 m) 83 ^ (83 m) ≤ 119 ^ (119 m)`. -/
theorem choose_d_upper {m : ℕ} (hm : 1 ≤ m) :
    (d m).choose (2 * t m) * 36 ^ (36 * m) * 83 ^ (83 * m) ≤ 119 ^ (119 * m) := by
  have h := Nat.choose_mul_pow_mul_pow_le_pow (36 * m) (83 * m)
  rw [show 36 * m + 83 * m = 119 * m by ring, mul_pow, mul_pow, mul_pow] at h
  refine cancel (k := 119 * m) hm ?_
  rw [two_mul_t]; unfold d
  calc _ = (119 * m).choose (36 * m) * (36 ^ (36 * m) * m ^ (36 * m)) *
        (83 ^ (83 * m) * m ^ (83 * m)) := by
          rw [show 119 * m = 36 * m + 83 * m by ring, pow_add m]; ring
    _ ≤ _ := h

/-- `Pre · 33 ^ (33 m) 86 ^ (86 m) ≤ 119 ^ (119 m)`. -/
theorem pre_upper {m : ℕ} (hm : 1 ≤ m) :
    pre m * (33 ^ (33 * m) * 86 ^ (86 * m)) ≤ 119 ^ (119 * m) := by
  have h := Nat.sum_choose_mul_pow_mul_pow_le_pow (n := 119 * m) (s := 33 * m) (by omega)
  rw [show 119 * m - 33 * m = 86 * m by omega, mul_pow, mul_pow, mul_pow] at h
  refine cancel (k := 119 * m) hm ?_
  unfold pre s d
  calc _ = (∑ j ∈ range (33 * m + 1), (119 * m).choose j) *
        (33 ^ (33 * m) * m ^ (33 * m) * (86 ^ (86 * m) * m ^ (86 * m))) := by
          rw [show 119 * m = 33 * m + 86 * m by ring, pow_add m]; ring
    _ ≤ _ := h

/-- `Q · 3 ^ (3 m) 33 ^ (33 m) ≤ 36 ^ (36 m)`. -/
theorem query_upper {m : ℕ} (hm : 1 ≤ m) :
    query m * (3 ^ (3 * m) * 33 ^ (33 * m)) ≤ 36 ^ (36 * m) := by
  have hQ : query m = ∑ j ∈ range (3 * m + 1), (36 * m).choose j := by
    unfold query s
    rw [two_mul_t]
    refine sum_bij' (fun j _ => 36 * m - j) (fun j _ => 36 * m - j) ?_ ?_ ?_ ?_ ?_
    · intro j hj; rw [mem_Icc] at hj; rw [mem_range]; omega
    · intro j hj; rw [mem_range] at hj; rw [mem_Icc]; omega
    · intro j hj; rw [mem_Icc] at hj; omega
    · intro j hj; rw [mem_range] at hj; omega
    · intro j hj
      rw [mem_Icc] at hj
      exact (Nat.choose_symm (by omega)).symm
  have h := Nat.sum_choose_mul_pow_mul_pow_le_pow (n := 36 * m) (s := 3 * m) (by omega)
  rw [show 36 * m - 3 * m = 33 * m by omega, mul_pow, mul_pow, mul_pow] at h
  refine cancel (k := 36 * m) hm ?_
  rw [hQ]
  calc _ = (∑ j ∈ range (3 * m + 1), (36 * m).choose j) *
        (3 ^ (3 * m) * m ^ (3 * m) * (33 ^ (33 * m) * m ^ (33 * m))) := by
          rw [show 36 * m = 3 * m + 33 * m by ring, pow_add m]; ring
    _ ≤ _ := h

/-- The central binomial coefficient: `4 ^ t ≤ (2 t + 1) (2 t choose t)`. -/
theorem central_lower (m : ℕ) : 4 ^ t m ≤ (2 * t m + 1) * (2 * t m).choose (t m) :=
  Nat.four_pow_le_two_mul_add_one_mul_centralBinom (t m)

end Cslib.Algorithms.Lean.SubsetConvThreeSum.Params
