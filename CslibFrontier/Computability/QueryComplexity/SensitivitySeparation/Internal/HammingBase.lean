/-
Copyright (c) 2026 OpenAI, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.QueryComplexity.SensitivitySeparation.Internal.Defs
public import Mathlib.InformationTheory.Hamming
import CslibFrontier.Foundations.Data.BitString.Hamming

/-!
# Superquadratic sensitivity separation: hamming base

This file provides the Hamming-distance facts behind the initial nested predicates. A one-bit
flip changes the Hamming distance to any point by at most one, which controls how the indicator
`ballPredicate` of a union of radius-`R` Hamming balls can change. For well-separated centers a
rejected input has sensitivity at most `R + 1`, and ball predicates with radii `R < S` have no
common sensitive coordinate at an input on which they take the same value.

## Main definitions

* `ballPredicate`: the indicator of the union of radius-`R` Hamming balls around given centers.

## Main results

* `ballPredicate_sensitivityAt_zero_le`: for centers more than `2 * (R + 1)` apart, the radius-`R`
  ball predicate has sensitivity at most `R + 1` at every rejected input.
* `ballPredicate_no_joint_zero`, `ballPredicate_no_joint_one`: for `R < S`, no one-bit flip
  changes both the radius-`R` and the radius-`S` predicates from a common value.

## References

* Adapted from OpenAI's formalization [OpenAI2026Sensitivity] at revision
  adc7f1241b42e322a6451854ab7e4b4c146bf78a (file
  lean/OAI/Combinatorics/Sensitivity/HammingBase.lean), via the complexitylib port
  [Schlesinger2026Sensitivity] at revision add0aca8ee0d71e68969f2cb45cf91554a50f787.
-/

@[expose] public section

namespace Cslib.QueryComplexity.SensitivitySeparation

noncomputable section

namespace Internal

open Cslib.BitString (hammingDist_le_flip_add_one hammingDist_flip_le_add_one
  hammingDist_flip_eq_add_one)

variable {I C : Type} [Fintype I]

open scoped Classical in
/-- The union of equal-radius Hamming balls. -/
def ballPredicate [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) : Bool :=
  decide (∃ c, hammingDist x (centers c) ≤ R)

open scoped Classical in
/-- `ballPredicate centers R x` holds iff `x` is within Hamming distance `R` of some
center. -/
theorem ballPredicate_eq_true [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) :
    ballPredicate centers R x = true ↔ ∃ c, hammingDist x (centers c) ≤ R := by
  simp [ballPredicate]

/-- Ball predicates are monotone in the radius: for `R ≤ S`, acceptance at radius `R`
implies acceptance at radius `S`. -/
theorem ballPredicate_nested [Fintype C] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R ≤ S) (x : I → Bool)
    (h : ballPredicate centers R x = true) : ballPredicate centers S x = true := by
  rcases (ballPredicate_eq_true centers R x).1 h with ⟨c, hc⟩
  exact (ballPredicate_eq_true centers S x).2 ⟨c, hc.trans hRS⟩

open scoped Classical in
/-- If `x` is rejected at radius `R` but `BitString.flipOn {i} x` is accepted, then some center is
at Hamming distance exactly `R + 1` from `x` and differs from `x` at coordinate `i`. -/
private theorem ballPredicate_zero_flip [Fintype C] (centers : C → I → Bool) (R : ℕ)
    (x : I → Bool) (i : I) (hx : ballPredicate centers R x = false)
    (hi : ballPredicate centers R (BitString.flipOn {i} x) = true) :
    ∃ c, hammingDist x (centers c) = R + 1 ∧ x i ≠ centers c i := by
  rcases (ballPredicate_eq_true centers R (BitString.flipOn {i} x)).1 hi with ⟨c, hc⟩
  have hn : ¬ hammingDist x (centers c) ≤ R := by
    intro h
    have := (ballPredicate_eq_true centers R x).2 ⟨c, h⟩
    simp_all
  have hd := hammingDist_le_flip_add_one x (centers c) i
  refine ⟨c, by omega, ?_⟩
  intro heq
  rw [hammingDist_flip_eq_add_one x (centers c) i heq] at hc
  omega

open scoped Classical in
/-- If distinct centers are at Hamming distance greater than `2 * (R + 1)`, then any two
centers within distance `R + 1` of the same input coincide. -/
private theorem near_center_unique (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) {a b : C} (ha : hammingDist x (centers a) ≤ R + 1)
    (hb : hammingDist x (centers b) ≤ R + 1) : a = b := by
  by_contra h
  have hs := hsep a b h
  have ht := hammingDist_triangle (centers a) x (centers b)
  rw [hammingDist_comm (centers a) x] at ht
  omega

open scoped Classical in
/-- If distinct centers are at Hamming distance greater than `2 * (R + 1)`, then the
radius-`R` ball predicate has sensitivity at most `R + 1` at every rejected input. -/
theorem ballPredicate_sensitivityAt_zero_le [Fintype C]
    (centers : C → I → Bool) (R : ℕ)
    (hsep : ∀ a b, a ≠ b → 2 * (R + 1) < hammingDist (centers a) (centers b))
    (x : I → Bool) (hx : ballPredicate centers R x = false) :
    sensitivityAt (ballPredicate centers R) x ≤ R + 1 := by
  let A := Finset.univ.filter fun i =>
    ballPredicate centers R (BitString.flipOn {i} x) ≠ ballPredicate centers R x
  change A.card ≤ R + 1
  by_cases hA : A.Nonempty
  · obtain ⟨i, hi⟩ := hA
    have hi' : ballPredicate centers R (BitString.flipOn {i} x) = true := by
      simpa [A, hx] using hi
    obtain ⟨c, hc, _⟩ := ballPredicate_zero_flip centers R x i hx hi'
    have hsub : A ⊆ Finset.univ.filter fun j => x j ≠ centers c j := by
      intro j hj
      have hj' : ballPredicate centers R (BitString.flipOn {j} x) = true := by
        simpa [A, hx] using hj
      obtain ⟨c', hc', hjc⟩ := ballPredicate_zero_flip centers R x j hx hj'
      have heq : c' = c := near_center_unique centers R hsep x (by omega) (by omega)
      simpa [heq] using hjc
    exact (Finset.card_le_card hsub).trans_eq hc
  · rw [Finset.not_nonempty_iff_eq_empty.mp hA]
    simp

/-- For `R < S`, if `x` is rejected at radius `S`, then no one-bit flip of `x` is
accepted at radius `R`. -/
theorem ballPredicate_no_joint_zero [Fintype C] [DecidableEq I] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hS : ballPredicate centers S x = false)
    (hR : ballPredicate centers R (BitString.flipOn {i} x) = true) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R (BitString.flipOn {i} x)).1 hR
  have hd := hammingDist_le_flip_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S x).2 ⟨c, by omega⟩
  simp_all

/-- For `R < S`, if `x` is accepted at radius `R`, then no one-bit flip of `x` is
rejected at radius `S`. -/
theorem ballPredicate_no_joint_one [Fintype C] [DecidableEq I] (centers : C → I → Bool)
    {R S : ℕ} (hRS : R < S) (x : I → Bool) (i : I)
    (hR : ballPredicate centers R x = true)
    (hS : ballPredicate centers S (BitString.flipOn {i} x) = false) : False := by
  obtain ⟨c, hc⟩ := (ballPredicate_eq_true centers R x).1 hR
  have hd := hammingDist_flip_le_add_one x (centers c) i
  have ht := (ballPredicate_eq_true centers S (BitString.flipOn {i} x)).2 ⟨c, by omega⟩
  simp_all

end Internal

end

end Cslib.QueryComplexity.SensitivitySeparation
