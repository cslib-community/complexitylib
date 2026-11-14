/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Cslib.Computability.QueryComplexity.Measures
public import CslibFrontier.Foundations.Data.BitString.LocalBoundary
public import Mathlib.Data.Nat.Log
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise

/-!
# Maximum sensitivity bounds the number of relevant coordinates

The set of inputs sensitive to a relevant coordinate has local boundary at most twice the
maximum sensitivity. The cube-cardinality bound and double-counting sensitive incidences give
at most `s(f) * 4 ^ s(f)` relevant coordinates. Consequently, dependence on all `n` coordinates
implies `Nat.clog 2 n ≤ 3 * sensitivity f`, an explicit uniform logarithmic lower bound.
The measures are CSLib's native maximum sensitivity, not average sensitivity or Fourier degree.

## Main results

* `Cslib.BitString.card_relevant_le_sensitivity_mul_four_pow`: relevant-coordinate cardinality.
* `Cslib.BitString.clog_le_three_mul_sensitivity_of_depends_on_all`: the logarithmic corollary.

## References

* [AroraBarak07], Chapter 11 Exercise 1, printed page 218 / PDF page 234.
-/

public section

namespace Cslib.BitString
open Finset

private theorem flip_comm {n : ℕ} (x : BitString n) (i j : Fin n) :
    Function.update (Function.update x j (!x j)) i (!(Function.update x j (!x j)) i) =
      Function.update (Function.update x i (!x i)) j (!(Function.update x i (!x i)) j) := by
  by_cases hij : i = j
  · subst j
    rfl
  · simp only [Function.update_of_ne hij, Function.update_of_ne (Ne.symm hij)]
    exact Function.update_comm (Ne.symm hij) _ _ _

private theorem sensitiveInputs_boundary {n : ℕ} (f : BooleanFunction n) (i : Fin n)
    (x : BitString n) (hx : IsSensitiveCoord f x i) :
    #{j : Fin n | ¬IsSensitiveCoord f (Function.update x j (!x j)) i} ≤ 2 * sensitivity f := by
  have hsub : ({j : Fin n | ¬IsSensitiveCoord f (Function.update x j (!x j)) i} :
      Finset (Fin n)) ⊆
      sensitiveCoords f x ∪ sensitiveCoords f (Function.update x i (!x i)) := by
    intro j hj
    by_contra hn
    have hnot : ¬IsSensitiveCoord f x j ∧
        ¬IsSensitiveCoord f (Function.update x i (!x i)) j := by
      simpa only [Finset.mem_union, mem_sensitiveCoords, not_or] using hn
    obtain ⟨hne0, hne1⟩ := hnot
    have h0 : f (Function.update x j (!x j)) = f x := not_ne_iff.mp hne0
    have h1 : f (Function.update (Function.update x i (!x i)) j
        (!(Function.update x i (!x i)) j)) = f (Function.update x i (!x i)) :=
      not_ne_iff.mp hne1
    have h2 : f (Function.update (Function.update x j (!x j)) i
        (!(Function.update x j (!x j)) i)) = f (Function.update x j (!x j)) := by
      exact not_ne_iff.mp (Finset.mem_filter.mp hj).2
    exact hx (h1.symm.trans ((congrArg f (flip_comm x i j).symm).trans (h2.trans h0)))
  calc
    _ ≤ #(sensitiveCoords f x ∪ sensitiveCoords f (Function.update x i (!x i))) := card_le_card hsub
    _ ≤ sensitivityAt f x + sensitivityAt f (Function.update x i (!x i)) := card_union_le _ _
    _ ≤ 2 * sensitivity f := by
      have := sensitivityAt_le_sensitivity f x
      have := sensitivityAt_le_sensitivity f (Function.update x i (!x i))
      omega

/-- A Boolean function has at most `s(f) * 4 ^ s(f)` relevant coordinates. -/
theorem card_relevant_le_sensitivity_mul_four_pow {n : ℕ} (f : BooleanFunction n) :
    #{i : Fin n | ∃ x, IsSensitiveCoord f x i} ≤ sensitivity f * 4 ^ sensitivity f := by
  classical
  let A : Fin n → Finset (BitString n) := fun i => univ.filter fun x => IsSensitiveCoord f x i
  let R : Finset (Fin n) := univ.filter fun i => ∃ x, IsSensitiveCoord f x i
  have hi (i : Fin n) (hi : i ∈ R) : 2 ^ n ≤ 2 ^ (2 * sensitivity f) * (A i).card := by
    apply two_pow_le_two_pow_mul_card_of_boundary_bound (A i) (2 * sensitivity f)
    · obtain ⟨x, hx⟩ := (Finset.mem_filter.mp hi).2
      exact ⟨x, Finset.mem_filter.mpr ⟨Finset.mem_univ x, hx⟩⟩
    · intro x hx
      have hxi : IsSensitiveCoord f x i := (Finset.mem_filter.mp hx).2
      simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using
        sensitiveInputs_boundary f i x hxi
  have hdouble : ∑ i, (A i).card = ∑ x : BitString n, sensitivityAt f x := by
    simp only [A, Finset.card_filter, sensitivityAt, sensitiveCoords]
    rw [Finset.sum_comm]
  have htotal : ∑ i, (A i).card ≤ 2 ^ n * sensitivity f := by
    rw [hdouble]
    calc
      _ ≤ ∑ _x : BitString n, sensitivity f :=
        sum_le_sum fun x _ => sensitivityAt_le_sensitivity f x
      _ = _ := by simp [BitString]
  have hpartial : ∑ i ∈ R, (A i).card ≤ ∑ i, (A i).card :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) fun _ _ _ => Nat.zero_le _
  have hproduct : R.card * 2 ^ n ≤ 2 ^ (2 * sensitivity f) * (2 ^ n * sensitivity f) := by
    calc
      _ = ∑ _i ∈ R, 2 ^ n := by simp
      _ ≤ ∑ i ∈ R, 2 ^ (2 * sensitivity f) * (A i).card := sum_le_sum hi
      _ = 2 ^ (2 * sensitivity f) * ∑ i ∈ R, (A i).card := (Finset.mul_sum ..).symm
      _ ≤ _ := Nat.mul_le_mul_left _ (hpartial.trans htotal)
  have hbound : R.card * 2 ^ n ≤ (sensitivity f * 4 ^ sensitivity f) * 2 ^ n := by
    simpa only [show 4 = 2 ^ 2 from rfl, pow_mul, Nat.mul_comm, Nat.mul_left_comm,
      Nat.mul_assoc] using hproduct
  exact Nat.le_of_mul_le_mul_right hbound (Nat.pow_pos (by decide))

/-- Depending on every coordinate forces logarithmic maximum sensitivity: the ceiling of
`log₂ n` is at most three times the sensitivity, including the empty-coordinate case. -/
theorem clog_le_three_mul_sensitivity_of_depends_on_all {n : ℕ} (f : BooleanFunction n)
    (hdep : ∀ i : Fin n, ∃ x, IsSensitiveCoord f x i) :
    Nat.clog 2 n ≤ 3 * sensitivity f := by
  have hcard : #{i : Fin n | ∃ x, IsSensitiveCoord f x i} = n := by simp [hdep]
  have hn : n ≤ sensitivity f * 4 ^ sensitivity f := by
    simpa only [hcard] using card_relevant_le_sensitivity_mul_four_pow f
  apply Nat.clog_le_of_le_pow
  refine hn.trans ?_
  calc
    sensitivity f * 4 ^ sensitivity f ≤ 2 ^ sensitivity f * 4 ^ sensitivity f :=
      Nat.mul_le_mul_right _ (Nat.le_of_lt Nat.lt_two_pow_self)
    _ = 2 ^ (3 * sensitivity f) := by
      rw [show 4 = 2 ^ 2 from rfl, ← pow_mul, ← pow_add]
      congr 1
      omega

end Cslib.BitString
