/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

import CslibFrontier.Foundations.Data.Fin.Counting
public import CslibFrontier.Foundations.Data.BitString.Flip
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.Order.Ring.Nat
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# Cardinality of a cube set from a pointwise boundary bound

If a nonempty subset of the Boolean cube has at most `b` outgoing single-coordinate flips
at every member, its cardinality is at least `2 ^ (n - b)`, in the subtraction-free form
`2 ^ n ≤ 2 ^ b * A.card`. The proof slices one coordinate and uses the smaller budget only
when the opposite slice is empty.

## Main results

* `Cslib.BitString.two_pow_le_two_pow_mul_card_of_boundary_bound`: the subtraction-free
  cardinality bound from a uniform per-member bound on outgoing coordinate directions.

## References

* A cube-counting lemma for [AroraBarak07], Chapter 11 Exercise 1, printed page 218 / PDF page 234.
-/

public section

namespace Cslib.BitString

open Finset Function

private def cubeSlice {n : ℕ} (A : Finset (Fin (n + 1) → Bool)) (a : Bool) :
    Finset (Fin n → Bool) :=
  univ.filter fun x => Fin.cons a x ∈ A

@[simp] private theorem mem_cubeSlice {n : ℕ} {A : Finset (Fin (n + 1) → Bool)}
    {a : Bool} {x : Fin n → Bool} : x ∈ cubeSlice A a ↔ Fin.cons a x ∈ A := by
  simp [cubeSlice]

private def outgoing {n : ℕ} (A : Finset (Fin n → Bool)) (x : Fin n → Bool) : ℕ :=
  #{i | update x i (!x i) ∉ A}

/-- Use the extracted original tuple-count lemma, rather than reproving the count. -/
private theorem card_cubeSlices {n : ℕ} (A : Finset (Fin (n + 1) → Bool)) :
    A.card = (cubeSlice A true).card + (cubeSlice A false).card := by
  have h := Fin.card_filter_zero_tail (fun a x => Fin.cons a x ∈ A)
  simpa [cubeSlice, Fintype.sum_bool, filter_mem_eq_inter] using h

/-- All successor-coordinate exits remain in a slice; only the head flip crosses slices. -/
private theorem outgoing_cons {n : ℕ} (A : Finset (Fin (n + 1) → Bool))
    (a : Bool) (x : Fin n → Bool) :
    outgoing A (Fin.cons a x) = outgoing (cubeSlice A a) x +
      if Fin.cons (!a) x ∉ A then 1 else 0 := by
  have htail :
      #{j : Fin n | update (Fin.cons a x : Fin (n + 1) → Bool) j.succ (!x j) ∉ A} =
        outgoing (cubeSlice A a) x := by
    unfold outgoing
    congr 1
    ext j
    simp only [mem_filter, mem_univ, true_and]
    rw [← Fin.cons_update (α := fun _ => Bool)]
    simp only [mem_cubeSlice]
  change #{i : Fin (n + 1) |
    update (Fin.cons a x) i (!((Fin.cons a x : Fin (n + 1) → Bool) i)) ∉ A} = _
  rw [Fin.card_filter_univ_succ]
  simp only [Fin.cons_zero, Fin.update_cons_zero, Fin.cons_succ]
  rw [htail]
  split_ifs <;> omega

/-- **Cube minimum-degree/cardinality bound**, in local-boundary form. The budget counts
outgoing directions at each member, rather than the union of external boundary vertices. -/
theorem two_pow_le_two_pow_mul_card_of_boundary_bound {n : ℕ}
    (A : Finset (Fin n → Bool)) (b : ℕ) (hA : A.Nonempty)
    (hbound : ∀ x ∈ A, #{i | update x i (!x i) ∉ A} ≤ b) :
    2 ^ n ≤ 2 ^ b * A.card := by
  classical
  induction n generalizing b with
  | zero =>
    have hpos : 0 < 2 ^ b * A.card := Nat.mul_pos (by positivity) hA.card_pos
    simp only [pow_zero]
    omega
  | succ n ih =>
    change ∀ x ∈ A, outgoing A x ≤ b at hbound
    -- A nonempty slice inherits the same budget. Dropping the head direction only helps.
    have hslice (a : Bool) (x : Fin n → Bool) (hx : x ∈ cubeSlice A a) :
        outgoing (cubeSlice A a) x ≤ b := by
      have h := hbound (Fin.cons a x) (mem_cubeSlice.mp hx)
      rw [outgoing_cons] at h
      omega
    -- Handle either orientation of the one-empty-slice case without a repeated argument.
    have hsingle (a : Bool) (hother : cubeSlice A (!a) = ∅) :
        2 ^ (n + 1) ≤ 2 ^ b * A.card := by
      have hcard : A.card = (cubeSlice A a).card := by
        cases a <;> simp only [Bool.not_false, Bool.not_true] at hother <;>
          simpa [hother] using card_cubeSlices A
      have hnonempty : (cubeSlice A a).Nonempty := by
        apply card_pos.mp
        rw [← hcard]
        exact hA.card_pos
      have hcross (x : Fin n → Bool) : Fin.cons (!a) x ∉ A := by
        intro hx
        have hx' : x ∈ cubeSlice A (!a) := mem_cubeSlice.mpr hx
        simp [hother] at hx'
      have hsmall (x : Fin n → Bool) (hx : x ∈ cubeSlice A a) :
          outgoing (cubeSlice A a) x + 1 ≤ b := by
        have h := hbound (Fin.cons a x) (mem_cubeSlice.mp hx)
        simpa [outgoing_cons, hcross x] using h
      have hb : 1 ≤ b := by
        obtain ⟨x, hx⟩ := hnonempty
        have := hsmall x hx
        omega
      have hrec : 2 ^ n ≤ 2 ^ (b - 1) * (cubeSlice A a).card :=
        ih (cubeSlice A a) (b - 1) hnonempty fun x hx => by
          have := hsmall x hx
          change outgoing (cubeSlice A a) x ≤ b - 1
          omega
      have hpow : 2 * 2 ^ (b - 1) = 2 ^ b := by
        rw [← pow_succ']
        congr 1
        omega
      calc
        2 ^ (n + 1) = 2 * 2 ^ n := by rw [pow_succ']
        _ ≤ 2 * (2 ^ (b - 1) * (cubeSlice A a).card) := Nat.mul_le_mul_left 2 hrec
        _ = (2 * 2 ^ (b - 1)) * (cubeSlice A a).card := by ring
        _ = 2 ^ b * A.card := by rw [hpow, ← hcard]
    by_cases hfalse : cubeSlice A false = ∅
    · exact hsingle true (by simpa only [Bool.not_true] using hfalse)
    by_cases htrue : cubeSlice A true = ∅
    · exact hsingle false (by simpa only [Bool.not_false] using htrue)
    have hrecTrue := ih (cubeSlice A true) b (nonempty_iff_ne_empty.mpr htrue)
      (hslice true)
    have hrecFalse := ih (cubeSlice A false) b (nonempty_iff_ne_empty.mpr hfalse)
      (hslice false)
    rw [card_cubeSlices, Nat.mul_add, pow_succ]
    omega

end Cslib.BitString
