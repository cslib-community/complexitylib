/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Threshold
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Combinatorics.Enumerative.DoubleCounting

/-!
# Approximate majorities: averaging and strict-majority votes

A finite family `P i` of predicates on a finite type is an *approximate majority* when, at every
point, at least a fraction `r` of the family holds. Double counting the incidence relation then
gives a single member that holds on at least the same fraction `r` of the points. Applied to
`P i x := f i x = g x`, this turns an approximate majority of functions computing `g` into one
function agreeing with `g` on a `r` fraction of inputs; this is the averaging step of
[KaneWilliams2016], `arXiv:1511.07860v1`, Corollary 1.1.

A strict-majority vote of an odd number of bits that outputs `bit` has strictly more than half of
its votes equal to `bit`. For even fan-in a tie outputs `false`, so a correct vote need not have a
strict majority of correct votes.

## Main results

* `Cslib.exists_mul_card_le_card_filter_of_forall`: the averaging lemma.
* `Cslib.lt_two_mul_card_filter_eq_of_strictMajority_eq`: a correct strict-majority vote of odd
  fan-in has a strict majority of correct votes.

## References

* [D. M. Kane and R. Williams, *Super-Linear Gate and Super-Quadratic Wire Lower Bounds for
  Depth-Two and Depth-Three Threshold Circuits*][KaneWilliams2016]
-/

public section

namespace Cslib

open Finset

/-- **Averaging over an approximate majority.** If at every point `x` at least a fraction `r` of a
nonempty finite family of predicates `P i` hold, then some member `P i` holds on at least a
fraction `r` of the points. -/
theorem exists_mul_card_le_card_filter_of_forall {R ι α : Type*} [CommSemiring R] [LinearOrder R]
    [IsStrictOrderedRing R] [Fintype ι] [Nonempty ι] [Fintype α] (P : ι → α → Prop)
    [∀ i x, Decidable (P i x)] {r : R}
    (h : ∀ x, r * Fintype.card ι ≤ (#{i | P i x} : R)) :
    ∃ i, r * Fintype.card α ≤ (#{x | P i x} : R) := by
  have hcount : ∑ i, (#{x | P i x} : R) = ∑ x, (#{i | P i x} : R) := by
    exact_mod_cast sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow
      (s := (univ : Finset ι)) (t := (univ : Finset α)) (r := P)
  obtain ⟨i, -, hi⟩ := exists_le_of_sum_le (s := (univ : Finset ι)) univ_nonempty
    (f := fun _ => r * Fintype.card α) (g := fun i => (#{x | P i x} : R)) <| by
      rw [hcount]
      calc ∑ _i : ι, r * (Fintype.card α : R) = ∑ _x : α, r * (Fintype.card ι : R) := by
            simp only [sum_const, card_univ, nsmul_eq_mul]; ring
        _ ≤ ∑ x, (#{i | P i x} : R) := sum_le_sum fun x _ => h x
  exact ⟨i, hi⟩

/-- A strict-majority vote of odd fan-in that outputs `bit` has strictly more than half of its
votes equal to `bit`. -/
theorem lt_two_mul_card_filter_eq_of_strictMajority_eq {t : ℕ} (ht : Odd t) {v : BitString t}
    {bit : Bool} (h : strictMajority t v = bit) : t < 2 * #{i | v i = bit} := by
  obtain ⟨q, rfl⟩ := ht
  have hsplit := card_filter_add_card_filter_not (s := (univ : Finset (Fin (2 * q + 1))))
    (fun i => v i = true)
  simp only [card_univ, Fintype.card_fin, Bool.not_eq_true] at hsplit
  have hw : strictMajority (2 * q + 1) v = decide ((2 * q + 1) / 2 + 1 ≤ #{i | v i = true}) := rfl
  cases bit with
  | true =>
    rw [hw, decide_eq_true_iff] at h
    omega
  | false =>
    rw [hw, decide_eq_false_iff_not] at h
    omega

end Cslib
