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
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

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
@[expose] def occupancy (label : A → B) (u : B) : ℕ :=
  Fintype.card {a // label a = u}

/-- The total occupancy is the number of objects, also when that number is zero. -/
theorem sum_occupancy (label : A → B) :
    ∑ u, occupancy label u = Fintype.card A := by
  simpa only [occupancy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id, mul_one] using
    (Fintype.sum_fiberwise' label (fun _ => (1 : ℕ)))

/-- Counting collisions by their common label or by their first object gives the same result. -/
theorem sum_occupancy_sq (label : A → B) :
    ∑ u, occupancy label u ^ 2 = ∑ a, occupancy label (label a) := by
  simpa only [occupancy, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
    Nat.cast_id, pow_two] using
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
@[expose] def potential (label : A → B) : ℚ :=
  ∑ u, ((occupancy label u : ℚ) - Fintype.card A / (Fintype.card B : ℚ)) ^ 2

/-- Exact centered-square expansion used in the paper's two collision potentials. -/
theorem potential_eq_collisions_sub (label : A → B) (hB : 0 < Fintype.card B) :
    potential label =
      (∑ a, ∑ a', if label a = label a' then (1 : ℚ) else 0) -
        (Fintype.card A : ℚ) ^ 2 / Fintype.card B := by
  have hsum : ∑ u, (occupancy label u : ℚ) = Fintype.card A := by
    exact_mod_cast sum_occupancy label
  have hsq : ∑ u, (occupancy label u : ℚ) ^ 2 =
      ∑ a, ∑ a', if label a = label a' then (1 : ℚ) else 0 := by
    exact_mod_cast sum_occupancy_sq_eq_collisions label
  have hB' : (Fintype.card B : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hB
  unfold potential
  simp_rw [sub_sq]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.sum_mul, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
    nsmul_eq_mul, hsum, hsq]
  field_simp
  ring

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

/-- The second collision expansion in Lemma 4.5, summed over the schedule coordinates. -/
theorem sum_potential_eq_collisions_sub {T : Type*} [Fintype T]
    (label : T → A → B) (hB : 0 < Fintype.card B) :
    ∑ t, potential (label t) =
      (∑ t, ∑ a, ∑ a', if label t a = label t a' then (1 : ℚ) else 0) -
        Fintype.card T * (Fintype.card A : ℚ) ^ 2 / Fintype.card B := by
  simp_rw [potential_eq_collisions_sub _ hB]
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-- The paper's normalized potential bound controls both nonnegative components separately.
No relation between the two normalization factors is assumed. -/
theorem components_le_of_normalized_le_two {Φ Ξ x y : ℚ}
    (hΦ : 0 ≤ Φ) (hΞ : 0 ≤ Ξ) (hx : 0 < x) (hy : 0 < y)
    (h : Φ / x + Ξ / y ≤ 2) : Φ ≤ 2 * x ∧ Ξ ≤ 2 * y := by
  have hΦ' : 0 ≤ Φ / x := div_nonneg hΦ hx.le
  have hΞ' : 0 ≤ Ξ / y := div_nonneg hΞ hy.le
  constructor
  · apply (div_le_iff₀ hx).mp
    linarith
  · apply (div_le_iff₀ hy).mp
    linarith

/-- Cross-multiplied natural form of the pointwise occupancy bound. -/
theorem occupancy_mul_card_le (label : A → B) (hB : 0 < Fintype.card B)
    (hpotential : potential label ≤
      ((Fintype.card A : ℚ) / Fintype.card B) ^ 2) (u : B) :
    occupancy label u * Fintype.card B ≤ 2 * Fintype.card A := by
  have hB' : (0 : ℚ) < Fintype.card B := by exact_mod_cast hB
  have h := occupancy_le_twice_mean label hpotential u
  have hmul := (le_div_iff₀ hB').mp h
  exact_mod_cast hmul

/-- The size hypothesis in (4.13) absorbs the collision variance bound, without rounding the
source's `2 * M / D` bound up to an integer. Here `C` will be `b + w`. -/
theorem occupancy_mul_card_le_of_variance_bound (label : A → B)
    (hB : 0 < Fintype.card B) (C : ℕ)
    (hpotential : potential label ≤ 2 * Fintype.card A * C)
    (hsize : 2 * C * Fintype.card B ^ 2 ≤ Fintype.card A) (u : B) :
    occupancy label u * Fintype.card B ≤ 2 * Fintype.card A := by
  apply occupancy_mul_card_le label hB _ u
  apply hpotential.trans
  rw [div_pow]
  have hB' : (0 : ℚ) < Fintype.card B := by exact_mod_cast hB
  apply (le_div_iff₀ (sq_pos_of_pos hB')).2
  have hsize' : (2 : ℚ) * C * (Fintype.card B : ℚ) ^ 2 ≤ Fintype.card A := by
    exact_mod_cast hsize
  have hM : (0 : ℚ) ≤ Fintype.card A := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hsize' hM]

/-- The two conclusions of Lemma 4.5 follow from its normalized potential bound and size
hypotheses. `incidence` may be the pair `(a v, d f)` and `group t v` is the SAME variable
label `a v` at coordinate `t`. This implication does not construct labels or assume they exist. -/
theorem incidence_and_group_bounds {T V G : Type*} [Fintype T] [Fintype V] [Fintype G]
    [DecidableEq G] (incidence : A → B) (group : T → V → G) (C : ℕ)
    (hA : 0 < Fintype.card A) (hB : 0 < Fintype.card B) (hC : 0 < C)
    (hT : 0 < Fintype.card T) (hV : 0 < Fintype.card V) (hG : 0 < Fintype.card G)
    (hincidenceSize : 2 * C * Fintype.card B ^ 2 ≤ Fintype.card A)
    (hgroupSize : 2 * Fintype.card T * Fintype.card G ^ 2 ≤ Fintype.card V)
    (hpotential : potential incidence / ((Fintype.card A : ℚ) * C) +
      (∑ t, potential (group t)) / ((Fintype.card T : ℚ) * Fintype.card V) ≤ 2) :
    (∀ u, occupancy incidence u * Fintype.card B ≤ 2 * Fintype.card A) ∧
      (∀ t g, occupancy (group t) g * Fintype.card G ≤ 2 * Fintype.card V) := by
  have hx : (0 : ℚ) < Fintype.card A * (C : ℚ) := by positivity
  have hy : (0 : ℚ) < Fintype.card T * (Fintype.card V : ℚ) := by positivity
  have hcomponents := components_le_of_normalized_le_two (potential_nonneg incidence)
    (Finset.sum_nonneg fun t _ => potential_nonneg (group t)) hx hy hpotential
  constructor
  · intro u
    apply occupancy_mul_card_le_of_variance_bound incidence hB C _ hincidenceSize u
    simpa only [mul_assoc] using hcomponents.1
  · intro t g
    apply occupancy_mul_card_le_of_variance_bound (group t) hG (Fintype.card T) _
      hgroupSize g
    have hle : potential (group t) ≤ ∑ t', potential (group t') :=
      Finset.single_le_sum (fun t' _ => potential_nonneg (group t')) (Finset.mem_univ t)
    nlinarith [hcomponents.2]

end Cslib.BalancedSchedules
