/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Karn Seth
-/

import Complexity.Computability.Complexity.FineGrained.PPSZ.AssignSL
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.NormNum

/-! AssignSL on small formulas: the example `x₀ ∨ x₁` of [Hertli, p. 7], whose output distribution
is not uniform on the solutions, with Observation 13 and a strict instance of Lemma 16 checked on
it, and the satisfying literals of a formula with a frozen variable. -/

namespace ComplexityTests.PPSZAssignSL

open Cslib.Logic.PL Cslib.Complexity.PPSZ Function
open Cslib.BitString.PartialAssignment (free free_update)

/-! ### `x₀ ∨ x₁` -/

/-- The formula `x₀ ∨ x₁`. -/
def φ : CNF (Fin 2) := [[(0, true), (1, true)]]

/-- The empty partial assignment. -/
def τ₀ : Fin 2 → Option Bool := fun _ => none

-- Every literal is satisfying at the start: `x₀ = false` still allows `x₁ = true`.
example : satLits φ τ₀ = Finset.univ := by decide

-- After `x₀ = false`, only `x₁ = true` is satisfying.
example : satLits φ (update τ₀ 0 (some false)) = {(1, true)} := by decide

/-- One step of AssignSL from the empty assignment, by its definition: each of the four
satisfying literals is set with probability `1/4`. -/
theorem assignProb_τ₀ (α : Fin 2 → Bool) :
    assignProb φ τ₀ α = 4⁻¹ * (assignProb φ (update τ₀ 0 (some true)) α +
      assignProb φ (update τ₀ 0 (some false)) α + (assignProb φ (update τ₀ 1 (some true)) α +
      assignProb φ (update τ₀ 1 (some false)) α)) := by
  rw [assignProb_eq_sum, show satLits φ τ₀ = Finset.univ by decide, Fintype.sum_prod_type,
    Fin.sum_univ_two, Fintype.sum_bool, Fintype.sum_bool,
    show (Finset.univ : Finset (Fin 2 × Bool)).card = 4 by decide]
  · norm_num
  · decide

/-- With one variable `y` set, the process sets the remaining variable `z` and outputs `α` with
probability `1/s`, if `α` is a satisfying extension. -/
theorem assignProb_update (y z : Fin 2) (b : Bool) (s : ℕ) (α : Fin 2 → Bool)
    (hyz : free (update τ₀ y (some b)) = {z})
    (hs : (satLits φ (update τ₀ y (some b))).card = s)
    (hα : IsSatExtension φ (update (update τ₀ y (some b)) z (some (α z))) α) :
    assignProb φ (update τ₀ y (some b)) α = (s : ℝ)⁻¹ := by
  rw [assignProb_eq_inv_mul_sum (hyz ▸ Finset.singleton_nonempty z), hyz, Finset.sum_singleton,
    hs, assignProb_of_free_eq_empty
      (by rw [free_update, hyz, Finset.erase_singleton]), ite_eq_left hα, mul_one]

/-- After `x₀ = true` the formula is satisfied, and `x₁` is set uniformly. -/
theorem x₀_true (b : Bool) : assignProb φ (update τ₀ 0 (some true)) ![true, b] = 1 / 2 :=
  (assignProb_update 0 1 true 2 ![true, b] (by decide) (by cases b <;> decide)
    (by cases b <;> decide)).trans (by norm_num)

/-- After `x₁ = true` the formula is satisfied, and `x₀` is set uniformly. -/
theorem x₁_true (b : Bool) : assignProb φ (update τ₀ 1 (some true)) ![b, true] = 1 / 2 :=
  (assignProb_update 1 0 true 2 ![b, true] (by decide) (by cases b <;> decide)
    (by cases b <;> decide)).trans (by norm_num)

/-- After `x₀ = false`, the only satisfying literal is `x₁ = true`. -/
theorem x₀_false : assignProb φ (update τ₀ 0 (some false)) ![false, true] = 1 :=
  (assignProb_update 0 1 false 1 ![false, true] (by decide) (by decide) (by decide)).trans
    (by norm_num)

/-- After `x₁ = false`, the only satisfying literal is `x₀ = true`. -/
theorem x₁_false : assignProb φ (update τ₀ 1 (some false)) ![true, false] = 1 :=
  (assignProb_update 1 0 false 1 ![true, false] (by decide) (by decide) (by decide)).trans
    (by norm_num)

/-- AssignSL outputs `x₀ = x₁ = true` with probability `1/4` [Hertli, p. 7]. -/
theorem assignProb_true_true : assignProb φ τ₀ ![true, true] = 1 / 4 := by
  rw [assignProb_τ₀, x₀_true, x₁_true, assignProb_eq_zero, assignProb_eq_zero]
  · norm_num
  · decide
  · decide

/-- AssignSL outputs `x₀ = true, x₁ = false` with probability `3/8` [Hertli, p. 7]. -/
theorem assignProb_true_false : assignProb φ τ₀ ![true, false] = 3 / 8 := by
  rw [assignProb_τ₀, x₀_true, x₁_false, assignProb_eq_zero, assignProb_eq_zero]
  · norm_num
  · decide
  · decide

/-- AssignSL outputs `x₀ = false, x₁ = true` with probability `3/8` [Hertli, p. 7]. -/
theorem assignProb_false_true : assignProb φ τ₀ ![false, true] = 3 / 8 := by
  rw [assignProb_τ₀, x₀_false, x₁_true, assignProb_eq_zero, assignProb_eq_zero]
  · norm_num
  · decide
  · decide

-- The non-solution has probability `0`, so the four probabilities sum to `1`.
example : assignProb φ τ₀ ![false, false] = 0 := assignProb_eq_zero (by decide)

-- Observation 13 at `α = (true, false)`: `s · R(τ₀)(α) = R(x₀ = true)(α) + R(x₁ = false)(α)`,
-- that is `4 · 3/8 = 1/2 + 1`.
example : ((satLits φ τ₀).card : ℝ) * assignProb φ τ₀ ![true, false] =
    assignProb φ (update τ₀ 0 (some true)) ![true, false] +
      assignProb φ (update τ₀ 1 (some false)) ![true, false] := by
  rw [show satLits φ τ₀ = Finset.univ by decide, assignProb_true_false, x₀_true, x₁_false,
    show (Finset.univ : Finset (Fin 2 × Bool)).card = 4 by decide]
  norm_num

-- Lemma 16 can be strict: setting `x₀ = true` raises the probability of `(true, false)` from
-- `3/8` to `1/2`.
example :
    assignProb φ τ₀ ![true, false] < assignProb φ (update τ₀ 0 (some true)) ![true, false] := by
  rw [assignProb_true_false, x₀_true]
  norm_num

/-! ### A frozen variable -/

/-- The formula `x₀ ∧ (x₁ ∨ x₂)`, in which `x₀` is frozen. -/
def ψ : CNF (Fin 3) := [[(0, true)], [(1, true), (2, true)]]

-- The satisfying literals are `x₀ = true` and all four literals on `x₁, x₂`: one per frozen
-- variable and two per non-frozen variable, `5` in all, between the `3` unassigned variables and
-- twice that.
example : satLits ψ (fun _ => none) =
    {(0, true), (1, true), (1, false), (2, true), (2, false)} := by
  decide

end ComplexityTests.PPSZAssignSL
