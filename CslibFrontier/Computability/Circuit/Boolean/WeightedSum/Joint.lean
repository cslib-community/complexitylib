/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Boolean.WeightedSum.Comparisons

/-!
# Correlated polynomial-weight tests and signed-coefficient normalization

A fixed family of actual comparisons shares the original input variables and has disjoint,
functional gates. This is the functional preservation clause of [ChenJiangZhu2027], Lemma A.1 /
Corollary A.2 (PDF pp.28–29), not yet the encoded counting-resource or full distribution transfer.
Signed coefficients are an explicit extension: flip a negative coefficient's literal and subtract
its negative constant offset from the target. No absolute-value-only substitution is used.

## Main definitions

* `joint`, `jointFormula`: actual simultaneous comparison circuits and full 3-CNF.
* `signedValue`, `negativeOffset`, `signedTest`: ordinary integer normalization and circuit.

## Main results

* `count_jointFormula`: exact extension counts with arbitrary original-input correlations.
* `joint_bounds`: linear gates and clauses for each fixed number of comparisons/exponent.
* `signed_normalization`, `eval_signedTest`: exact negative-coefficient cancellation/target shift.
-/

public section

namespace Cslib.Circuits.Boolean.WeightedSum

open scoped BigOperators

/-- Actual simultaneous tests, sharing original variables and only duplicating functional gates. -/
@[expose] def joint {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) : Circuit signature n r :=
  Circuit.pi fun j => test (op j) c (weights j) (positive j) (target j)

/-- Full functional encoding of all tests, retaining correlations between their original bits. -/
@[expose] def jointFormula {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) : Logic.PL.CNF ℕ :=
  FunctionalCNF.write (FunctionalCNF.ofCircuit (joint op c weights positive target) (fun _ => true))

/-- Exact simultaneous semantics; different tests need not be independent. -/
theorem eval_joint {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) (x : BitString n) (hw : ∀ j i, weights j i ≤ n ^ c) :
    (joint op c weights positive target).eval interpretation x =
      fun j => decide ((op j).Holds (value (weights j) (positive j) x) (target j)) := by
  funext j
  simp only [joint, Circuit.eval_pi, eval_test _ c _ _ x _ (hw j)]

open Classical in
/-- Tests preserve every original annotation/correlation; gate traces add no multiplicity. -/
theorem count_jointFormula {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) (hw : ∀ j i, weights j i ≤ n ^ c)
    (P : (Fin n → Bool) → Prop) :
    Fintype.card {y : Fin (n + (joint op c weights positive target).size) → Bool //
      (jointFormula op c weights positive target).eval
        (Function.extend Fin.val y (fun _ => false)) = true ∧
        P (fun i => y (Fin.castAdd (joint op c weights positive target).size i))} =
      Fintype.card {x : Fin n → Bool //
        (∀ j, (op j).Holds (value (weights j) (positive j) x) (target j)) ∧ P x} := by
  calc _ = Fintype.card {x : Fin n → Bool //
        (joint op c weights positive target).eval interpretation x = (fun _ => true) ∧ P x} :=
          FunctionalCNF.count_extensions _ _ P
    _ = _ := Fintype.card_congr (Equiv.subtypeEquivRight fun x => by
      rw [eval_joint op c weights positive target x hw]
      simp only [funext_iff, decide_eq_true_eq])

/-- A fixed family adds only a fixed linear factor, even with correlated equalities/inequalities. -/
theorem joint_bounds {n r : ℕ} (op : Fin r → Comparison) (c : ℕ)
    (weights : Fin r → Fin n → ℕ) (positive : Fin r → Fin n → Bool)
    (target : Fin r → ℤ) :
    (joint op c weights positive target).size ≤ r * comparisonBudget c * (n + 1) ∧
    (jointFormula op c weights positive target).length ≤
      r + 3 * r * comparisonBudget c * (n + 1) ∧
    (∀ clause ∈ jointFormula op c weights positive target, clause.length ≤ 3) := by
  have hs : (joint op c weights positive target).size ≤
      r * comparisonBudget c * (n + 1) := by
    rw [joint, Circuit.size_pi]
    calc _ ≤ ∑ _ : Fin r, comparisonBudget c * (n + 1) :=
          Finset.sum_le_sum fun j _ => size_test_linear _ c _ _ _
      _ = _ := by simp [Nat.mul_assoc]
  refine ⟨hs, ?_, ?_⟩
  · rw [jointFormula, FunctionalCNF.write_length]
    nlinarith
  · intro clause hc
    exact (FunctionalCNF.write_bounds _ _ clause hc).1.le

/-- Ordinary signed integer sum; negative coefficients are not silently dropped or absolutized. -/
@[expose] def signedValue {n : ℕ} (coeff : Fin n → ℤ) (x : BitString n) : ℤ :=
  ∑ i, coeff i * (x i).toNat

/-- Negative coefficients contribute this constant when the corresponding literal is flipped. -/
@[expose] def negativeOffset {n : ℕ} (coeff : Fin n → ℤ) : ℤ := ∑ i, min (coeff i) 0

/-- Exact cancellation identity, valid also for zero coefficients and empty inputs. -/
theorem signed_normalization {n : ℕ} (coeff : Fin n → ℤ) (x : BitString n) :
    signedValue coeff x =
      (value (fun i => (coeff i).natAbs) (fun i => decide (0 ≤ coeff i)) x : ℤ) +
        negativeOffset coeff := by
  unfold signedValue value negativeOffset
  rw [Nat.cast_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [Nat.cast_mul, Int.natCast_natAbs]
  by_cases h : 0 ≤ coeff i
  · cases x i <;> simp [literal, h, abs_of_nonneg h]
  · have hn : coeff i ≤ 0 := by omega
    cases x i <;> simp [literal, h, abs_of_nonpos hn, min_eq_left hn]

/-- Actual negative-coefficient extension, including the indispensable integer target offset. -/
@[expose] def signedTest {n : ℕ} (op : Comparison) (c : ℕ) (coeff : Fin n → ℤ)
    (target : ℤ) : Circuit signature n 1 :=
  test op c (fun i => (coeff i).natAbs) (fun i => decide (0 ≤ coeff i))
    (target - negativeOffset coeff)

/-- Normalized comparison is exactly the original signed integer comparison, without loss at
negative targets, zero coefficients, cancellations or strict boundaries. -/
theorem eval_signedTest {n : ℕ} (op : Comparison) (c : ℕ) (coeff : Fin n → ℤ)
    (target : ℤ) (x : BitString n) (hw : ∀ i, (coeff i).natAbs ≤ n ^ c) :
    (signedTest op c coeff target).eval interpretation x =
      fun _ => decide (op.Holds (signedValue coeff x) target) := by
  rw [signedTest, eval_test _ c _ _ x _ hw, signed_normalization]
  funext j
  apply decide_eq_decide.mpr
  cases op <;> unfold Comparison.Holds <;> omega

end Cslib.Circuits.Boolean.WeightedSum
