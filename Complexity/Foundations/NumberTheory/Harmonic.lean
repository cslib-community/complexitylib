/-
Copyright (c) 2026 Renfei Zhou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Renfei Zhou
-/

module
-- upstream: candidate (Mathlib, `Mathlib/NumberTheory/Harmonic/Bounds.lean`)

public import Complexity.Init
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Data.Nat.Log
public import Mathlib.NumberTheory.Harmonic.Defs
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.Interval.Finset.Nat
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.IntervalCases
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Algebraic identities and dyadic bounds for harmonic numbers

Elementary order properties, a weighted summation identity, and a base-2 discrete logarithmic upper
bound for Mathlib's rational harmonic numbers `harmonic : ℕ → ℚ`.

Mathlib's `Mathlib.NumberTheory.Harmonic.Bounds` bounds `harmonic n` in `ℝ` by `1 + Real.log n` via
improper-style interval integrals. Grouping the upper half `[⌊n / 2⌋, n)` of the harmonic sum gives
a purely rational bound `harmonic n ≤ Nat.log 2 n + 1` (`harmonic_le_log_add_one`) with no real
analysis dependencies. The weighted sum identity `two_mul_sum_add_one_mul_harmonic` evaluates the
average recursive subproblem cost arising in randomized quicksort and random binary search trees.

## Main results

* `harmonic_nonneg`, `harmonic_mono`: nonnegativity and monotonicity of `harmonic`.
* `two_mul_sum_add_one_mul_harmonic`:
  `2 * ∑ r ∈ Finset.range m, (r + 1) * harmonic r = m * (m + 1) * harmonic m - m * (m + 3) / 2`.
* `harmonic_le_log_add_one`: `harmonic n ≤ Nat.log 2 n + 1` in `ℚ`.

The dyadic grouping argument is classical; see [CLRS2009], Appendix A.2, pp. 1153–1154.
The rational half-splitting and weighted-sum induction proofs below are this formalization's
adaptations for the word-RAM analysis.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Appendix A.2, pp. 1153–1154.
-/

@[expose] public section

/-- Every harmonic number is nonnegative. -/
theorem harmonic_nonneg (n : ℕ) : 0 ≤ harmonic n :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- Harmonic numbers are monotone in their index. -/
theorem harmonic_mono : Monotone harmonic :=
  fun _ _ hab => Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hab) fun _ _ _ => by
    positivity

/-- Weighted summation identity
`2 ∑_{r < m} (r + 1) H_r = m (m + 1) H_m - m (m + 3) / 2` in `ℚ`. -/
theorem two_mul_sum_add_one_mul_harmonic (m : ℕ) :
    2 * ∑ r ∈ Finset.range m, ((r : ℚ) + 1) * harmonic r =
      (m : ℚ) * ((m : ℚ) + 1) * harmonic m - (m : ℚ) * ((m : ℚ) + 3) / 2 := by
  induction m with
  | zero => simp
  | succ m ih =>
    have hm1 : (m : ℚ) + 1 ≠ 0 := by positivity
    rw [Finset.sum_range_succ, mul_add, ih, harmonic_succ]
    push_cast
    field_simp [hm1]
    ring

/-- Dyadic condensation upper bound `H_n ≤ ⌊log₂ n⌋ + 1` in `ℚ`. -/
theorem harmonic_le_log_add_one (n : ℕ) :
    harmonic n ≤ (Nat.log 2 n : ℚ) + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases lt_or_ge n 2 with hn2 | hn2
    · interval_cases n <;> norm_num [harmonic]
    · set half := n / 2
      have hhalf_lt : half < n := Nat.div_lt_self (by omega) (by decide)
      have hlog : Nat.log 2 n = Nat.log 2 half + 1 :=
        Nat.log_of_one_lt_of_le (by decide) (by omega)
      have hsplit : harmonic n =
          harmonic half + ∑ i ∈ Finset.Ico half n, ((i : ℚ) + 1)⁻¹ := by
        unfold harmonic
        rw [← Finset.sum_range_add_sum_Ico _ (Nat.le_of_lt hhalf_lt)]
        simp only [Nat.cast_add, Nat.cast_one]
      have htail : ∑ i ∈ Finset.Ico half n, ((i : ℚ) + 1)⁻¹ ≤ 1 := by
        calc
          ∑ i ∈ Finset.Ico half n, ((i : ℚ) + 1)⁻¹
            ≤ ∑ _i ∈ Finset.Ico half n, ((half : ℚ) + 1)⁻¹ := by
              refine Finset.sum_le_sum fun i hi => ?_
              have hle : (half : ℚ) + 1 ≤ (i : ℚ) + 1 := by
                exact_mod_cast Nat.add_le_add_right (Finset.mem_Ico.mp hi).1 1
              exact inv_anti₀ (by positivity) hle
          _ = ((n - half : ℕ) : ℚ) / ((half : ℚ) + 1) := by
              simp [div_eq_mul_inv]
          _ ≤ 1 := by
              rw [div_le_one (by positivity)]
              have hcnt : n - half ≤ half + 1 := by omega
              exact_mod_cast hcnt
      rw [hsplit, hlog]
      push_cast
      linarith [ih half hhalf_lt]
