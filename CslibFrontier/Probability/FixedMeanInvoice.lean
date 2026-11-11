/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.FiniteTable.Expectation
import CslibFrontier.Probability.PMF.Expect
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Tactic

/-!
# Natural token invoices with prescribed real means

A finite vector of nonnegative real expected costs is realized by natural token
counts. One categorical draw chooses at most one charged coordinate. Thus the
invoices can be correlated while every selected coordinate has its prescribed
mean. Nothing serializes an arbitrary real number into a token-report word.

## Main definitions

* `cap`, `choice`, `invoice`, `law`: concrete finite-support invoice kernel.

## Main results

* `mean_call`, `mean_batch`, `expected_batch`: exact real and extended expectations.
* `invoice_le`: a bound derived from the construction, not a total-bill premise.
-/

public section
noncomputable section
namespace Cslib.Probability.FixedMeanInvoice
open Finset Cslib.Optimization.OneConstraint
open scoped NNReal ENNReal
variable {n : ℕ} (cost : Fin n → ℝ≥0)

/-- An integral invoice large enough to normalize all declared expected costs. -/
@[expose] def cap : ℕ := Nat.ceil (∑ i, (cost i : ℝ)) + 1

private theorem cap_pos : (0 : ℝ) < cap cost := by
  simp only [cap, Nat.cast_add, Nat.cast_one]
  positivity

private theorem sum_le_cap : (∑ i, (cost i : ℝ)) ≤ cap cost := by
  have h := Nat.le_ceil (∑ i, (cost i : ℝ))
  change _ ≤ ((Nat.ceil (∑ i, (cost i : ℝ)) + 1 : ℕ) : ℝ)
  push_cast
  linarith

/-- A zero invoice, or one selected coordinate with probability cost/cap. -/
@[expose] def choice : Distribution (Option (Fin n)) ℝ where
  weight j := j.elim (1 - (∑ i, (cost i : ℝ)) / cap cost)
    (fun i => (cost i : ℝ) / cap cost)
  nonneg j := by
    cases j with
    | none =>
      exact sub_nonneg.mpr ((div_le_one (cap_pos cost)).mpr (sum_le_cap cost))
    | some i => exact div_nonneg (cost i).coe_nonneg (cap_pos cost).le
  total := by
    rw [Fintype.sum_option]
    simp only [Option.elim_none, Option.elim_some, ← sum_div]
    ring

/-- Only the selected coordinate is charged, by a natural token count. -/
@[expose] def invoice (j : Option (Fin n)) (i : Fin n) : ℕ :=
  if j = some i then cap cost else 0

/-- Every realized coordinate is bounded by the derived integral cap. -/
theorem invoice_le (j : Option (Fin n)) (i : Fin n) : invoice cost j i ≤ cap cost := by
  unfold invoice
  split_ifs <;> omega

/-- A single actual natural invoice has the declared arbitrary real mean. -/
theorem mean_call (i : Fin n) :
    (choice cost).mean (fun j => (invoice cost j i : ℝ)) = cost i := by
  classical
  simp only [Distribution.mean, choice, invoice, Fintype.sum_option, Option.elim_none,
    Option.elim_some, reduceCtorEq, ite_false, Nat.cast_zero, mul_zero, zero_add,
    Option.some.injEq]
  simp only [Nat.cast_ite, Nat.cast_zero, mul_ite, mul_zero, sum_ite_eq', mem_univ, ite_true]
  exact div_mul_cancel₀ _ (ne_of_gt (cap_pos cost))

/-- Linearity gives the fixed expected bill for any batch selected before the draw. -/
theorem mean_batch (A : Finset (Fin n)) :
    (choice cost).mean (fun j => ((∑ i ∈ A, invoice cost j i : ℕ) : ℝ)) =
      ∑ i ∈ A, (cost i : ℝ) := by
  classical
  simp only [Nat.cast_sum, Distribution.mean, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro i hi
  exact mean_call cost i

/-- The invoice vector is sampled once per batch, jointly for all opportunities. -/
@[expose] def law : PMF (Fin n → ℕ) := (choice cost).toPMF.map (invoice cost)

/-- Exact native nonnegative expectation, without an integrability assumption. -/
theorem expected_batch (A : Finset (Fin n)) :
    (∑' f, law cost f * (∑ i ∈ A, (f i : ℝ≥0∞))) =
      ENNReal.ofReal (∑ i ∈ A, (cost i : ℝ)) := by
  rw [law, PMF.tsum_map_mul]
  have h := Distribution.ofReal_mean (choice cost)
    (fun j => ((∑ i ∈ A, invoice cost j i : ℕ) : ℝ)) (fun _ => by positivity)
  rw [mean_batch] at h
  simp only [ENNReal.ofReal_natCast] at h
  simpa only [Nat.cast_sum] using h.symm

end Cslib.Probability.FixedMeanInvoice
