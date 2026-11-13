/-
Copyright (c) 2026 Aviv Bar Natan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Aviv Bar Natan
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Circuit.Arithmetic.HittingSet.BoundedDegreeShifts
public import CslibFrontier.Foundations.Combinatorics.PerfectHashFamily.Basic

/-!
# An explicit set of concentrating shifts for multilinear polynomials

From a family `P` of colourings `Fin n → Fin k` of the variables, perfect for sets of `k`
variables, `concentratingShifts F P` is a finite set of shifts in `Fⁿ` such that every nonzero
multilinear polynomial of split rank less than `2 ^ k` across every set of `k` variables has,
after one of the shifts, a monomial with fewer than `k` variables
(`exists_mem_concentratingShifts`).

The set is `boundedDegreeShifts F 1 P`, the case of individual degree one of the construction
for every individual degree: the values on a grid of the point with coordinates
`∑ₑ Lₑ(s) τ ^ 2 ^ hₑ(j)`, where `hₑ` runs over `P` and `Lₑ` is the Lagrange basis on the nodes
`0, 1, …, |P| - 1`. The statements of this file are those of `exists_mem_boundedDegreeShifts` and
`card_boundedDegreeShifts_le` at `δ = 1`.

A criterion that does not go through this construction and has no hypothesis on the
characteristic, for points whose products over subsets are linearly independent, is
`exists_mem_support_shift_card_lt`.

The role of the seed variable `s` is that of the seed of the Klivans–Spielman generator in
[ForbesSaptharishiShpilka2014, Lemma 4.4]; the construction from a perfect hash family is ours.
Characteristic zero is used to have the nodes `0, 1, …` distinct.

## Main definitions

* `concentratingShifts`: the set of shifts.

## Main results

* `exists_mem_concentratingShifts`: some shift in the set gives a monomial with fewer than `k`
  variables.
* `card_concentratingShifts_le`: the set has at most `(n |P| + 1) (n 2 ^ k + 1)` points.
* `exists_mem_concentratingShifts_perfectHashFamily`,
  `card_concentratingShifts_perfectHashFamily_le`: the same with `Cslib.perfectHashFamily` and
  `k = ⌊lg w⌋ + 1`, a set of size polynomial in `n` and `w`.

## References

* [M. A. Forbes, R. Saptharishi, A. Shpilka, *Pseudorandomness for multilinear read-once
  algebraic branching programs, in any order*][ForbesSaptharishiShpilka2014]
* [A. Shpilka, *Polynomial-size hitting sets for multilinear any-order read-once algebraic
  branching programs and for set-multilinear depth-3 circuits with constant-size variable
  sets*][Shpilka2026], Theorem 2.3 and Corollary 2.4 (unrefereed preprint)
-/

public section

namespace Cslib.Circuits.Arithmetic

open Finset MvPolynomial

variable (F : Type*) [Field F] [CharZero F] {n k : ℕ}

/-- An explicit set of shifts of size at most `(n * P.card + 1) * (n * 2 ^ k + 1)`: the set
`boundedDegreeShifts F 1 P` for individual degree one. -/
noncomputable def concentratingShifts (P : Finset (Fin n → Fin k)) : Finset (Fin n → F) :=
  boundedDegreeShifts F 1 P

variable {F}

omit [CharZero F] in
/-- The set of shifts has at most `(n * P.card + 1) * (n * 2 ^ k + 1)` points. -/
theorem card_concentratingShifts_le (P : Finset (Fin n → Fin k)) :
    (concentratingShifts F P).card ≤ (n * P.card + 1) * (n * 2 ^ k + 1) := by
  simpa [concentratingShifts] using card_boundedDegreeShifts_le (F := F) 1 P

/-- **Support-concentrating shifts.** Let `P` be a perfect family of colourings of `n` variables
with `k` colours and `w < 2 ^ k`. Every nonzero multilinear polynomial in `n` variables of split
rank at most `w` across every set of `k` variables has, after shifting by some point of
`concentratingShifts F P`, a monomial with fewer than `k` variables. -/
theorem exists_mem_concentratingShifts {P : Finset (Fin n → Fin k)}
    (hP : IsPerfectHashFamily P k) {w : ℕ} (hw : w < 2 ^ k)
    {f : MvPolynomial (Fin n) F} (hf0 : f ≠ 0) (hmul : ∀ i, f.degreeOf i ≤ 1)
    (hf : ∀ Y : Finset (Fin n), Y.card = k → SplitRankLE (Y : Set (Fin n)) w f) :
    ∃ a ∈ concentratingShifts F P, ∃ m ∈ (shift a f).support, m.support.card < k :=
  exists_mem_boundedDegreeShifts hP hw hf0 hmul hf

/-- **Support-concentrating shifts, with the perfect hash family of the library.** Every nonzero
multilinear polynomial in `n` variables of split rank at most `w` across every set of
`⌊lg w⌋ + 1` variables has, after shifting by some point of an explicit set, a monomial with at
most `⌊lg w⌋` variables. -/
theorem exists_mem_concentratingShifts_perfectHashFamily {w : ℕ} {f : MvPolynomial (Fin n) F}
    (hf0 : f ≠ 0) (hmul : ∀ i, f.degreeOf i ≤ 1)
    (hf : ∀ Y : Finset (Fin n), Y.card = Nat.log 2 w + 1 → SplitRankLE (Y : Set (Fin n)) w f) :
    ∃ a ∈ concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1)),
      ∃ m ∈ (shift a f).support, m.support.card ≤ Nat.log 2 w := by
  obtain ⟨a, ha, m, hm, hmk⟩ := exists_mem_concentratingShifts
    (isPerfectHashFamily_perfectHashFamily n _ (Nat.succ_pos _))
    (Nat.lt_pow_succ_log_self (by norm_num) w) hf0 hmul hf
  exact ⟨a, ha, m, hm, Nat.lt_succ_iff.1 hmk⟩

omit [CharZero F] in
/-- The explicit set of shifts for width `w` has at most
`(n² 2 ^ (25 (⌊lg w⌋ + 1)) + 1) (n 2 ^ (⌊lg w⌋ + 1) + 1)` points, which is polynomial in `n`
and `w`. -/
theorem card_concentratingShifts_perfectHashFamily_le (n w : ℕ) :
    (concentratingShifts F (perfectHashFamily n (Nat.log 2 w + 1))).card ≤
      (n * (n * 2 ^ (25 * (Nat.log 2 w + 1))) + 1) * (n * 2 ^ (Nat.log 2 w + 1) + 1) :=
  (card_concentratingShifts_le _).trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right
    (Nat.mul_le_mul_left _ (card_perfectHashFamily_le _ _)) _))

end Cslib.Circuits.Arithmetic
