/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Probability.BitString.LinearHash
public import Mathlib.Algebra.BigOperators.Expect
public import Mathlib.Data.Finset.Prod
public import Mathlib.Order.PiLex
import CslibFrontier.Foundations.Data.Finset.Expect
import Mathlib.Algebra.Order.BigOperators.Expect

/-!
# Almost-injective binary linear maps

Two-universality bounds the expected number of collisions on any finite collection of distinct
input pairs. Averaging chooses a matrix attaining this bound. Choosing one orientation of each
pair in a finite set gives the almost-injective map used in circuit upper bounds for partial
Boolean functions. If the bound is below one, the matrix is injective on the set.

The matrices use the existing `LinearHash.hash` implementation. Selection here is existential;
these results give no efficiency guarantee for finding a suitable matrix.

## Main results

* `Cslib.BitString.LinearHash.expect_card_collisions_le`: the expected number of collisions.
* `Cslib.BitString.LinearHash.exists_card_collisions_le`: existence for specified distinct pairs.
* `Cslib.BitString.LinearHash.exists_card_collisions_le_choose`: the unordered-pair bound on a set.
* `Cslib.BitString.LinearHash.exists_injOn`: a collision-free hash when the output space suffices.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012], Lemma 1.17
  and its application to sparse partial functions in Section 1.4.2.
-/

public section

namespace Cslib.BitString.LinearHash

open Finset Cslib.Probability Cslib.Probability.PMF
open scoped BigOperators

/-- A uniform Boolean matrix collides on at most a `2⁻ᵐ` fraction of any specified distinct
input pairs, in expectation. Pairs may be chosen to represent unordered pairs or cross-pairs
between two sets. -/
theorem expect_card_collisions_le {n m : ℕ} (pairs : Finset (BitString n × BitString n))
    (distinct : ∀ p ∈ pairs, p.1 ≠ p.2) :
    (𝔼 rows : Fin m → BitString n,
      ((pairs.filter fun p => hash rows p.1 = hash rows p.2).card : ℝ)) ≤
      pairs.card / (2 : ℝ) ^ m := by
  simp only [← sum_boole]
  rw [expect_sum_comm]
  calc
    _ ≤ ∑ _p ∈ pairs, (Fintype.card (BitString m) : ℝ)⁻¹ :=
      sum_le_sum fun p hp => (isTwoUniversal n m).expect_boole_le (distinct p hp)
    _ = _ := by simp [div_eq_mul_inv]

/-- Some Boolean matrix collides on at most a `2⁻ᵐ` fraction of the specified distinct pairs.
The natural-number form avoids rounding or division conventions. -/
theorem exists_card_collisions_le {n m : ℕ} (pairs : Finset (BitString n × BitString n))
    (distinct : ∀ p ∈ pairs, p.1 ≠ p.2) :
    ∃ rows : Fin m → BitString n,
      2 ^ m * (pairs.filter fun p => hash rows p.1 = hash rows p.2).card ≤ pairs.card := by
  obtain ⟨rows, _, hrows⟩ := exists_le_of_expect_le univ_nonempty
    (expect_card_collisions_le (m := m) pairs distinct)
  have h := (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ m)).mp hrows
  exact ⟨rows, by exact_mod_cast (by simpa only [mul_comm] using h :
    (2 : ℝ) ^ m * (pairs.filter fun p => hash rows p.1 = hash rows p.2).card ≤ pairs.card)⟩

open Classical in
/-- Jukna's almost-injective linear map lemma. Lexicographic order selects each unordered
pair once, so the right side is `S.card.choose 2`. Zero-width inputs and outputs are allowed. -/
theorem exists_card_collisions_le_choose {n m : ℕ} (S : Finset (BitString n)) :
    ∃ rows : Fin m → BitString n,
      2 ^ m * ((S ×ˢ S).filter fun p =>
        toLex p.1 < toLex p.2 ∧ hash rows p.1 = hash rows p.2).card ≤ S.card.choose 2 := by
  classical
  obtain ⟨rows, hrows⟩ := exists_card_collisions_le (m := m)
    ((S ×ˢ S).filter fun p => toLex p.1 < toLex p.2)
    (fun _ hp heq => (ne_of_lt (Finset.mem_filter.mp hp).2) (congrArg toLex heq))
  have hcard : ((S ×ˢ S).filter fun p => toLex p.1 < toLex p.2).card = S.card.choose 2 := by
    simpa only [LT.lt] using (@Finset.card_product_filter_lt (BitString n) S
      (LinearOrder.lift' toLex toLex.injective))
  exact ⟨rows, by simpa only [hcard, Finset.filter_filter] using hrows⟩

/-- A finite set admits an injective linear hash whenever the output space is larger than
its number of unordered distinct pairs. This is an existence theorem, not a construction-time
bound for finding the matrix. -/
theorem exists_injOn {n m : ℕ} (S : Finset (BitString n))
    (hsize : S.card.choose 2 < 2 ^ m) :
    ∃ rows : Fin m → BitString n, Set.InjOn (hash rows) S := by
  classical
  obtain ⟨rows, hrows⟩ := exists_card_collisions_le_choose (m := m) S
  have hempty : ((S ×ˢ S).filter fun p =>
      toLex p.1 < toLex p.2 ∧ hash rows p.1 = hash rows p.2).card = 0 := by
    nlinarith
  refine ⟨rows, ?_⟩
  intro x hx y hy hxy
  by_contra hne
  have horder : toLex x < toLex y ∨ toLex y < toLex x :=
    lt_or_gt_of_ne (by simpa using hne)
  have hnot := Finset.filter_eq_empty_iff.mp (Finset.card_eq_zero.mp hempty)
  exact horder.elim
    (fun h => hnot (x := (x, y)) (Finset.mem_product.mpr ⟨hx, hy⟩) ⟨h, hxy⟩)
    (fun h => hnot (x := (y, x)) (Finset.mem_product.mpr ⟨hy, hx⟩) ⟨h, hxy.symm⟩)

end Cslib.BitString.LinearHash
