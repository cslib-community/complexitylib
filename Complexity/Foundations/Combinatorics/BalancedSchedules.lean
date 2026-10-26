/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Algebra.Field.Rat
import Mathlib.Tactic

/-!
# Collision potentials for balanced label schedules

The proof of Lemma 4.5, printed pp. 30–31 of [OpenAI2026ETH], balances incidence labels and
variable groups using two sums of squared deviations. This module supplies the exact finite
collision identity and the deterministic implication from a potential bound to an occupancy
bound. It does not yet supply the finite-average estimates, select schedules, or certify the
paper's bit-operation bound.

All sums of collisions count ordered pairs, including diagonal pairs. Empty source and empty
fibers are included. A variable's label is data attached to that variable, not independently
chosen for its occurrences.
-/

public section

namespace Cslib.BalancedSchedules

open Finset
open scoped BigOperators

variable {A B : Type*} [Fintype A] [Fintype B] [DecidableEq B]

/-- Number of objects receiving a specified label. -/
def occupancy (label : A → B) (u : B) : ℕ :=
  Fintype.card {a // label a = u}

/-- The total occupancy is the number of objects, also when that number is zero. -/
theorem sum_occupancy (label : A → B) :
    ∑ u, occupancy label u = Fintype.card A := by
  simpa only [occupancy, Finset.sum_const, Finset.card_univ, smul_eq_mul, mul_one] using
    (Fintype.sum_fiberwise' label (fun _ => (1 : ℕ)))

/-- Counting collisions by their common label or by their first object gives the same result. -/
theorem sum_occupancy_sq (label : A → B) :
    ∑ u, occupancy label u ^ 2 = ∑ a, occupancy label (label a) := by
  simpa only [occupancy, Finset.sum_const, Finset.card_univ, smul_eq_mul, pow_two] using
    (Fintype.sum_fiberwise' label (fun u => occupancy label u))

/-- Exact ordered-pair expansion of the collision count. Diagonal collisions are retained. -/
theorem sum_occupancy_sq_eq_collisions (label : A → B) :
    ∑ u, occupancy label u ^ 2 =
      ∑ a, ∑ a', if label a = label a' then 1 else 0 := by
  rw [sum_occupancy_sq]
  apply Finset.sum_congr rfl
  intro a _
  simp only [occupancy, Fintype.card_subtype, eq_comm (a := label a)]
  simp

/-- Rational squared-deviation potential at the exact uniform average. -/
def potential (label : A → B) : ℚ :=
  ∑ u, ((occupancy label u : ℚ) - Fintype.card A / (Fintype.card B : ℚ)) ^ 2

/-- A squared-deviation potential is nonnegative, without nonemptiness assumptions. -/
theorem potential_nonneg (label : A → B) : 0 ≤ potential label :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

/-- Each individual squared deviation is bounded by the full potential. -/
theorem deviation_sq_le_potential (label : A → B) (u : B) :
    ((occupancy label u : ℚ) - Fintype.card A / (Fintype.card B : ℚ)) ^ 2 ≤
      potential label := by
  unfold potential
  exact Finset.single_le_sum (fun v _ => sq_nonneg
    ((occupancy label v : ℚ) - Fintype.card A / (Fintype.card B : ℚ))) (Finset.mem_univ u)

/-- If the total potential is at most the squared mean, every fiber has occupancy at most
 twice the mean. This is the square-root-free step used for both bounds in Lemma 4.5. -/
theorem occupancy_le_twice_mean (label : A → B)
    (hpotential : potential label ≤
      ((Fintype.card A : ℚ) / Fintype.card B) ^ 2) (u : B) :
    (occupancy label u : ℚ) ≤ 2 * (Fintype.card A : ℚ) / Fintype.card B := by
  have hmean : 0 ≤ (Fintype.card A : ℚ) / Fintype.card B := by positivity
  have hsq := (deviation_sq_le_potential label u).trans hpotential
  rw [mul_div_assoc]
  by_contra h
  have hlt : 2 * ((Fintype.card A : ℚ) / Fintype.card B) < occupancy label u := lt_of_not_ge h
  have hx : 0 < (occupancy label u : ℚ) := by linarith
  have hdiff : 0 < (occupancy label u : ℚ) -
      2 * ((Fintype.card A : ℚ) / Fintype.card B) := by linarith
  nlinarith [mul_pos hx hdiff]

end Cslib.BalancedSchedules
