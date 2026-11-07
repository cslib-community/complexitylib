/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.QueryComplexity.Quantum.UnknownSearch
import Complexity.Computability.QueryComplexity.Quantum.Polynomial

/-! Search with an unknown number of marked items, and deciding `OR_N`: concrete instances with
`N = 4` items. Search uses `m = ⌊√4⌋ + 1 = 3` iteration counts and `⌊√4⌋ = 2` queries; the
decision algorithm uses the range `orRange 4 = 12` and `24` queries. -/

namespace ComplexityTests.QuantumUnknownSearch

open Cslib Cslib.Quantum Cslib.BitString Finset Real

/-- No marked item. -/
def none4 : Fin 4 → Bool := fun _ => false

/-- One marked item. -/
def one4 : Fin 4 → Bool := fun i => decide (i = 0)

/-- Two marked items. -/
def two4 : Fin 4 → Bool := fun i => decide (i.val < 2)

example : weight none4 = 0 := by decide
example : weight one4 = 1 := by decide
example : weight two4 = 2 := by decide
example : Nat.sqrt 4 + 1 = 3 := by rw [show 4 = 2 * 2 from rfl, Nat.sqrt_eq]

-- The initial state is a unit vector.
example : ‖randomGroverInit 4 3‖ = 1 := norm_randomGroverInit (by norm_num) (by norm_num)

-- With no marked item there is nothing to find.
example :
    ∑ i with none4 i = true, regProb (run (randomGrover 4 3) (randomGroverInit 4 3) none4 2) i =
      0 := by
  simp [none4]

-- With one marked item among four, `θ = arcsin(1/2) = π / 6`: zero, one and two iterations
-- succeed with probabilities `1/4`, `1` and `1/4`, so the average is `1/2`.
theorem searchAngle_four_one : searchAngle 4 1 = π / 6 := by
  have h : Real.sqrt ((1 : ℕ) / (4 : ℕ)) = Real.sin (π / 6) := by
    rw [Real.sin_pi_div_six, show ((1 : ℕ) : ℝ) / (4 : ℕ) = (1 / 2) ^ 2 by norm_num,
      Real.sqrt_sq (by norm_num)]
  rw [searchAngle, h, Real.arcsin_sin] <;> linarith [Real.pi_pos]

example :
    ∑ i with one4 i = true, regProb (run (randomGrover 4 3) (randomGroverInit 4 3) one4 2) i =
      1 / 2 := by
  rw [sum_regProb_run_randomGrover (by norm_num) (by norm_num), show weight one4 = 1 by decide,
    searchAngle_four_one]
  simp only [sum_range_succ, sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  rw [show (2 * 0 + 1 : ℝ) * (π / 6) = π / 6 by ring,
    show (2 * 1 + 1 : ℝ) * (π / 6) = π / 2 by ring,
    show (2 * 2 + 1 : ℝ) * (π / 6) = π - π / 6 by ring, Real.sin_pi_sub, Real.sin_pi_div_six,
    Real.sin_pi_div_two]
  norm_num

-- With two marked items among four, `θ = π / 4` and every number of iterations succeeds with
-- probability `1/2`.
theorem searchAngle_four_two : searchAngle 4 2 = π / 4 := by
  have h : Real.sqrt ((2 : ℕ) / (4 : ℕ)) = Real.sin (π / 4) := by
    rw [Real.sin_pi_div_four, show ((2 : ℕ) : ℝ) / (4 : ℕ) = (Real.sqrt 2 / 2) ^ 2 by
      rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num, Real.sqrt_sq (by positivity)]
  rw [searchAngle, h, Real.arcsin_sin] <;> linarith [Real.pi_pos]

example :
    ∑ i with two4 i = true, regProb (run (randomGrover 4 3) (randomGroverInit 4 3) two4 2) i =
      1 / 2 := by
  rw [sum_regProb_run_randomGrover (by norm_num) (by norm_num), show weight two4 = 2 by decide,
    searchAngle_four_two]
  simp only [sum_range_succ, sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat]
  rw [show (2 * 0 + 1 : ℝ) * (π / 4) = π / 4 by ring,
    show (2 * 1 + 1 : ℝ) * (π / 4) = π - π / 4 by ring,
    show (2 * 2 + 1 : ℝ) * (π / 4) = π / 4 + π by ring, Real.sin_pi_sub, Real.sin_add_pi,
    Real.sin_pi_div_four]
  have : (Real.sqrt 2 / 2) ^ 2 = 1 / 2 := by rw [div_pow, Real.sq_sqrt (by norm_num)]; norm_num
  rw [neg_sq, this]
  norm_num

-- The general bound applies to both inputs, a non-vacuous instance of the headline theorem.
example (x : Fin 4 → Bool) (hx : ∃ i, x i = true) :
    1 / 4 ≤ ∑ i with x i = true, regProb (run (randomGrover 4 (Nat.sqrt 4 + 1))
      (randomGroverInit 4 (Nat.sqrt 4 + 1)) x (Nat.sqrt 4)) i :=
  (randomGrover_search (by norm_num)).2.2 x hx

example : ∃ i, two4 i = true := ⟨0, by decide⟩

-- Lemma 2 of Boyer–Brassard–Høyer–Tapp at `θ = π / 6` and `m = 3`: `1/2 - sin(2π) / (12 sin(π/3))`.
example :
    (∑ j ∈ range 3, Real.sin ((2 * j + 1) * (π / 6)) ^ 2) / 3 =
      1 / 2 - Real.sin (4 * 3 * (π / 6)) / (4 * 3 * Real.sin (2 * (π / 6))) := by
  have := sum_sin_sq_div (π / 6) (m := 3) (by norm_num) (by
    rw [show 2 * (π / 6) = π / 3 by ring, Real.sin_pi_div_three]
    positivity)
  exact_mod_cast this

/-! ### Deciding `OR_4` -/

theorem orRange_four : orRange 4 = 12 := by
  rw [orRange, show 4 = 2 * 2 from rfl, Nat.sqrt_eq]

-- The all-zero input is accepted with probability `0`.
example : measureProb (run (orSearch 4) (orSearchInit 4) none4 (orRange 4 + orRange 4))
    (orAccept 4) = 0 := by
  rw [measureProb_run_orSearch (by norm_num), show weight none4 = 0 by decide, searchAngle_zero]
  simp

-- With one or two marked items, each stage succeeds with probability `1/2` by Lemma 2
-- (`sin(4 · 12 θ) = 0` for `θ = π / 6` and `θ = π / 4`), so the input is accepted with
-- probability `1 - (1/2)² = 3/4`.
example : measureProb (run (orSearch 4) (orSearchInit 4) one4 (orRange 4 + orRange 4))
    (orAccept 4) = 3 / 4 := by
  have hP : (∑ j ∈ range (orRange 4), Real.sin ((2 * j + 1) * searchAngle 4 (weight one4)) ^ 2) /
      (orRange 4 : ℝ) = 1 / 2 := by
    rw [orRange_four, show weight one4 = 1 by decide, searchAngle_four_one,
      sum_sin_sq_div _ (by norm_num) (by
        rw [show 2 * (π / 6) = π / 3 by ring, Real.sin_pi_div_three]; positivity),
      show 4 * ((12 : ℕ) : ℝ) * (π / 6) = (8 : ℕ) * π by push_cast; ring, Real.sin_nat_mul_pi]
    ring
  rw [measureProb_run_orSearch (by norm_num), hP]
  norm_num

example : measureProb (run (orSearch 4) (orSearchInit 4) two4 (orRange 4 + orRange 4))
    (orAccept 4) = 3 / 4 := by
  have hP : (∑ j ∈ range (orRange 4), Real.sin ((2 * j + 1) * searchAngle 4 (weight two4)) ^ 2) /
      (orRange 4 : ℝ) = 1 / 2 := by
    rw [orRange_four, show weight two4 = 2 by decide, searchAngle_four_two,
      sum_sin_sq_div _ (by norm_num) (by
        rw [show 2 * (π / 4) = π / 2 by ring, Real.sin_pi_div_two]; norm_num),
      show 4 * ((12 : ℕ) : ℝ) * (π / 4) = (12 : ℕ) * π by push_cast; ring, Real.sin_nat_mul_pi]
    ring
  rw [measureProb_run_orSearch (by norm_num), hP]
  norm_num

-- `orSearch` satisfies the hypothesis of the polynomial-method lower bound, a non-vacuous
-- instance of it: its `T = 2 · orRange N` queries satisfy `N ≤ 16 T²`.
example (N : ℕ) (hN : 0 < N) : N ≤ 16 * (orRange N + orRange N) ^ 2 :=
  card_le_sixteen_mul_sq_of_threshold_one_right (orSearch N) (norm_orSearchInit hN) _
    (orAccept N) (abs_measureProb_run_orSearch_sub_le hN)

end ComplexityTests.QuantumUnknownSearch
