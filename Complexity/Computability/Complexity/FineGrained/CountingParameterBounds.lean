/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Complexity.FineGrained.SparseCountingScale
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Pair
public import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Unary
public import Complexity.Computability.Machines.Turing.MultiTape.ResourceBounds.Polynomial
public import Complexity.Logics.Propositional.ClauseSet.Sparsification.CountingParameters
import Mathlib.Tactic.IntervalCases

/-!
# Numerical depth bounds for the counting parameter schedule

At the existing schedule `max 1 (ReplacementParams.numGroups N)`, the first-success dyadic
base is at most `A * (Nat.clog 2 N + 1)` for one width-dependent constant `A`. Its geometric
depth coefficient is therefore at most `D * (Nat.clog 2 N + 1) ^ (k - 2)`. Both constants are
chosen before every `N`, including zero and the small sizes where the schedule is clamped to one.

These are original all-input corollaries of the parameter estimates in Section 6.4 and
Appendix A.3 of [OpenAI2026ETH], using the existing `numGroups_mul_clog_le_clog` estimate.
They bound numerical values, independently of binary encoding lengths or parameter-computation
cost. The final corollary charges an external unary declared size in a retained context/formula
pair. No new schedule, traversal or native counting certificate is introduced.

## Main results

* `exists_countingThresholdBase_numGroups_le_clog`: one logarithmic numerical-base bound for all N.
* `exists_countingDepthCoeff_numGroups_le_pow_clog`: one depth-coefficient bound with degree
  `k - 2`.
* `polyBounded_countingDepthCoeff_numGroups`: composition with a charged declared-size bound.
* `polyBounded_countingDepthCoeff_numGroups_encPair`: the bound for a context, unary size
  and input.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*, Section 6.4, pp. 43–44 and
  Appendix A.3, pp. 46–47][OpenAI2026ETH]
-/

public section

namespace Cslib.Complexity.SubexponentialSAT.SparseCountingScale

open ReplacementParams Cslib.Logic.PL.ClauseSet.Sparsification Turing.MultiTapeTM

private theorem max_one_numGroups_mul_clog_le (n : ℕ) :
    max 1 (numGroups n) * (Nat.clog 2 (max 1 (numGroups n)) + 1) ≤ Nat.clog 2 n + 1 := by
  by_cases hn : 5 ≤ n
  · by_cases hs : 1 ≤ numGroups n
    · rw [max_eq_right hs]
      calc numGroups n * (Nat.clog 2 (numGroups n) + 1)
          ≤ numGroups n * (Nat.clog 2 (2 * numGroups n) + 1) :=
            Nat.mul_le_mul_left _ (Nat.add_le_add_right
              (Nat.clog_mono_right 2 (by omega)) 1)
        _ ≤ Nat.clog 2 n := numGroups_mul_clog_le_clog hn
        _ ≤ Nat.clog 2 n + 1 := Nat.le_succ _
    · have hs0 : numGroups n = 0 := by omega
      simp [hs0]
  · have hn' : n < 5 := by omega
    interval_cases n
    · decide
    · decide
    · decide
    · rw [show numGroups 3 = 1 from (numGroups_eq_iff (by decide)).mpr (by decide)]
      decide
    · rw [show numGroups 4 = 1 from (numGroups_eq_iff (by decide)).mpr (by decide)]
      decide

/-- For fixed width at least two, the same constant bounds the numerical first-success base
at every declared size. The clamped schedule includes sizes where `numGroups` is zero. -/
theorem exists_countingThresholdBase_numGroups_le_clog {k : ℕ} (hk : 2 ≤ k) :
    ∃ A : ℕ, ∀ n : ℕ,
      countingThresholdBase k (max 1 (numGroups n)) ≤ A * (Nat.clog 2 n + 1) := by
  obtain ⟨A, hA⟩ := exists_countingThresholdBase_le_mul_clog hk
  refine ⟨A, fun n => (hA _ (le_max_left _ _)).trans ?_⟩
  rw [Nat.mul_assoc]
  exact Nat.mul_le_mul_left A (max_one_numGroups_mul_clog_le n)

/-- One constant and the fixed degree `k - 2` bound the numerical depth coefficient for all
declared sizes. In particular, width two has degree zero. -/
theorem exists_countingDepthCoeff_numGroups_le_pow_clog {k : ℕ} (hk : 2 ≤ k) :
    ∃ D : ℕ, ∀ n : ℕ,
      countingDepthCoeff k (countingThresholdBase k (max 1 (numGroups n))) ≤
        D * (Nat.clog 2 n + 1) ^ (k - 2) := by
  obtain ⟨A, hA⟩ := exists_countingThresholdBase_numGroups_le_clog hk
  refine ⟨countingBChoiceCoeff k * A ^ (k - 2), fun n => ?_⟩
  calc countingDepthCoeff k (countingThresholdBase k (max 1 (numGroups n)))
      ≤ countingBChoiceCoeff k * countingThresholdBase k (max 1 (numGroups n)) ^ (k - 2) :=
        countingDepthCoeff_le_mul_pow ((by decide : 1 ≤ 2).trans (two_le_countingThresholdBase _ _))
    _ ≤ countingBChoiceCoeff k * (A * (Nat.clog 2 n + 1)) ^ (k - 2) :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (hA n) _)
    _ = (countingBChoiceCoeff k * A ^ (k - 2)) * (Nat.clog 2 n + 1) ^ (k - 2) := by
        rw [Nat.mul_pow, Nat.mul_assoc]

/-- A polynomial charge for the declared size supplies a uniform polynomial bound on the
numerical depth coefficient. This is a growth statement, not a machine certificate. -/
theorem polyBounded_countingDepthCoeff_numGroups {α : Type*} {size N : α → ℕ}
    {k : ℕ} (hk : 2 ≤ k) (hN : PolyBounded size N) :
    PolyBounded size (fun x =>
      countingDepthCoeff k (countingThresholdBase k (max 1 (numGroups (N x))))) := by
  obtain ⟨D, hD⟩ := exists_countingDepthCoeff_numGroups_le_pow_clog hk
  have h : PolyBounded id (fun n =>
      countingDepthCoeff k (countingThresholdBase k (max 1 (numGroups n)))) := by
    refine PolyBounded.of_forall_le D (k - 2) fun n => (hD n).trans ?_
    have hn : Nat.clog 2 n ≤ n := Nat.clog_le_of_le_pow n.lt_two_pow_self.le
    exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_left (Nat.add_le_add_right hn 1) _)
  exact h.comp hN

/-- A retained context, external unary declared size and encoded input charge the numerical
depth coefficient uniformly. The context and input encodings are arbitrary; the declared size
is not replaced by the input's occurring support or its binary bit length. -/
theorem polyBounded_countingDepthCoeff_numGroups_encPair {α β : Type}
    (encC : α ↪ List Bool) (encInput : β ↪ List Bool) {k : ℕ} (hk : 2 ≤ k) :
    PolyBounded (fun x : α × ℕ × β => (encPair encC (encPair encUnary encInput) x).length)
      (fun x => countingDepthCoeff k (countingThresholdBase k (max 1 (numGroups x.2.1)))) := by
  apply polyBounded_countingDepthCoeff_numGroups hk
  apply PolyBounded.self.mono
  intro x
  simp only [length_encPair, encUnary_apply, List.length_replicate]
  omega

end Cslib.Complexity.SubexponentialSAT.SparseCountingScale
