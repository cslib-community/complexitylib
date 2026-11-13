/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Foundations.Data.BitString.Weight
public import Cslib.Computability.QueryComplexity.Measures

/-!
# A block containing exactly two adjacent true bits

`adjacentPair n` accepts exactly the words whose two true positions are consecutive in the
linear order on `Fin n`. Overlapping choices are allowed: the middle pair of a four-bit word
is accepted. This is the local predicate in [AroraBarak07], Chapter 11 Exercise 2, printed
page 218 / PDF page 234. The global exercise takes an OR over disjoint blocks.

## Main definitions

* `Cslib.BitString.adjacentPair`: the local adjacent-pair predicate.

## Main results

* `Cslib.BitString.weight_eq_two_of_adjacentPair`: every accepted word has weight two.
* `Cslib.BitString.sensitivityAt_adjacentPair_of_true`: every bit is sensitive at acceptance.
* `Cslib.BitString.sensitivityAt_adjacentPair_le_three`: rejected-input sensitivity is at most
  three.
-/

public section

namespace Cslib.BitString

open Finset

/-- Exactly two positions are true, and they are adjacent without wraparound. The body is
exposed so finite checked examples can evaluate the predicate. -/
@[expose] def adjacentPair (n : ℕ) : BooleanFunction n := fun x =>
  decide (∃ a b : Fin n, b.val = a.val + 1 ∧ ∀ i, x i = decide (i = a ∨ i = b))

/-- Accepted words are precisely the indicators of adjacent pairs. -/
theorem adjacentPair_eq_true_iff {n : ℕ} {x : BitString n} :
    adjacentPair n x = true ↔
      ∃ a b : Fin n, b.val = a.val + 1 ∧ ∀ i, x i = decide (i = a ∨ i = b) := by
  simp [adjacentPair]

/-- An adjacent pair has two distinct endpoints, hence exactly two true bits. -/
theorem weight_eq_two_of_adjacentPair {n : ℕ} {x : BitString n}
    (h : adjacentPair n x = true) : weight x = 2 := by
  obtain ⟨a, b, hab, hx⟩ := adjacentPair_eq_true_iff.mp h
  have hne : a ≠ b := by
    intro he
    subst b
    omega
  have hs : ({i | x i = true} : Finset (Fin n)) = {a, b} := by
    ext i
    simp [hx]
  simp only [weight, hs, card_pair hne]

/-- The all-false word is not an adjacent pair, including lengths zero and one. -/
@[simp] theorem adjacentPair_zero (n : ℕ) : adjacentPair n (fun _ => false) = false := by
  cases h : adjacentPair n (fun _ => false) with
  | false => rfl
  | true => have hw := weight_eq_two_of_adjacentPair h; simp [weight] at hw

/-- One true bit does not meet the two-bit acceptance condition. -/
@[simp] theorem adjacentPair_singleton {n : ℕ} (a : Fin n) :
    adjacentPair n (fun i => decide (i = a)) = false := by
  cases h : adjacentPair n (fun i => decide (i = a)) with
  | false => rfl
  | true =>
    have hw := weight_eq_two_of_adjacentPair h
    have hs : ({i : Fin n | i = a} : Finset (Fin n)) = {a} := by
      ext i
      simp
    simp only [weight, decide_eq_true_eq, hs, card_singleton] at hw
    omega

/-- Every pair of consecutive positions gives an accepted input. -/
theorem adjacentPair_pair {n : ℕ} (a b : Fin n) (hab : b.val = a.val + 1) :
    adjacentPair n (fun i => decide (i = a ∨ i = b)) = true :=
  adjacentPair_eq_true_iff.mpr ⟨a, b, hab, fun _ => rfl⟩

/-- Flipping one bit into an accepted word starts at weight one or weight three. -/
theorem weight_eq_one_or_three_of_update_adjacentPair {n : ℕ} {x : BitString n} {i : Fin n}
    (h : adjacentPair n (Function.update x i (!x i)) = true) :
    weight x = 1 ∨ weight x = 3 := by
  have hw := weight_eq_two_of_adjacentPair h
  cases hi : x i with
  | false =>
    simp only [hi, Bool.not_false] at hw
    rw [weight_update_true hi] at hw
    omega
  | true =>
    simp only [hi, Bool.not_true] at hw
    have ht := weight_update_false hi
    omega

/-- Changing any single bit of an accepted pair destroys acceptance. -/
theorem adjacentPair_update_of_true {n : ℕ} {x : BitString n}
    (hx : adjacentPair n x = true) (i : Fin n) :
    adjacentPair n (Function.update x i (!x i)) = false := by
  cases h : adjacentPair n (Function.update x i (!x i)) with
  | false => rfl
  | true =>
    have hw := weight_eq_two_of_adjacentPair hx
    rcases weight_eq_one_or_three_of_update_adjacentPair h with ht | ht <;> omega

/-- Every coordinate is sensitive at an accepted adjacent pair. -/
theorem sensitivityAt_adjacentPair_of_true {n : ℕ} {x : BitString n}
    (hx : adjacentPair n x = true) : sensitivityAt (adjacentPair n) x = n := by
  apply le_antisymm (sensitivityAt_le_card _ _)
  simpa only [card_univ, Fintype.card_fin] using
    (card_le_sensitivityAt (S := univ) (f := adjacentPair n) (x := x) (fun i _ => by
      change adjacentPair n (Function.update x i (!x i)) ≠ adjacentPair n x
      rw [adjacentPair_update_of_true hx i, hx]
      decide))

private theorem card_neighbors_le_two {n : ℕ} (a : Fin n) :
    #{i : Fin n | i.val + 1 = a.val ∨ a.val + 1 = i.val} ≤ 2 := by
  have hl : #{i : Fin n | i.val + 1 = a.val} ≤ 1 := by
    refine card_le_one.mpr fun i hi j hj => Fin.ext ?_
    simp only [mem_filter, mem_univ, true_and] at hi hj
    omega
  have hr : #{i : Fin n | a.val + 1 = i.val} ≤ 1 := by
    refine card_le_one.mpr fun i hi j hj => Fin.ext ?_
    simp only [mem_filter, mem_univ, true_and] at hi hj
    omega
  rw [filter_or]
  exact (card_union_le _ _).trans (Nat.add_le_add hl hr)

/-- At a rejected word, at most three single-bit changes can create an adjacent pair.
A change into weight two starts at weight one or three. In the former case only the two
neighbors of the sole true bit can work; in the latter only its three true bits can work. -/
theorem sensitivityAt_adjacentPair_le_three {n : ℕ} {x : BitString n}
    (hx : adjacentPair n x = false) : sensitivityAt (adjacentPair n) x ≤ 3 := by
  have hacc (i : Fin n) (hi : i ∈ sensitiveCoords (adjacentPair n) x) :
      adjacentPair n (Function.update x i (!x i)) = true := by
    have h := mem_sensitiveCoords.mp hi
    simpa only [IsSensitiveCoord, hx, Bool.not_eq_false] using h
  by_cases hs : (sensitiveCoords (adjacentPair n) x).Nonempty
  · obtain ⟨j, hj⟩ := hs
    rcases weight_eq_one_or_three_of_update_adjacentPair (hacc j hj) with hw | hw
    · obtain ⟨a, ha⟩ := card_eq_one.mp hw
      have hxtrue (i : Fin n) : x i = true ↔ i = a := by
        have hh := Finset.ext_iff.mp ha i
        simpa only [mem_filter, mem_univ, true_and, mem_singleton] using hh
      refine (card_le_card (t := {i : Fin n | i.val + 1 = a.val ∨ a.val + 1 = i.val})
        (fun i hi => ?_)).trans ((card_neighbors_le_two a).trans (by decide))
      have hxi : x i = false := by
        cases ht : x i with
        | false => rfl
        | true =>
          have ht' := weight_update_false ht
          have hw' := weight_eq_two_of_adjacentPair (hacc i hi)
          simp only [ht, Bool.not_true] at hw'
          omega
      have hai : a ≠ i := by
        intro he
        have ht : x i = true := (hxtrue i).mpr he.symm
        rw [hxi] at ht
        exact Bool.false_ne_true ht
      obtain ⟨p, q, hpq, hp⟩ := adjacentPair_eq_true_iff.mp (hacc i hi)
      have hpa : a = p ∨ a = q := by
        have hh := hp a
        rw [Function.update_of_ne hai, (hxtrue a).mpr rfl] at hh
        exact of_decide_eq_true hh.symm
      have hpi : i = p ∨ i = q := by
        have hh := hp i
        rw [Function.update_self, hxi] at hh
        exact of_decide_eq_true hh.symm
      simp only [mem_filter, mem_univ, true_and]
      rcases hpa with rfl | rfl <;> rcases hpi with rfl | rfl <;> simp_all
    · refine (card_le_card (t := {i | x i = true}) (fun i hi => ?_)).trans hw.le
      have ht := weight_eq_two_of_adjacentPair (hacc i hi)
      have hxi : x i = true := by
        cases hi' : x i with
        | true => rfl
        | false =>
          simp only [hi', Bool.not_false] at ht
          rw [weight_update_true hi'] at ht
          omega
      exact mem_filter.mpr ⟨mem_univ i, hxi⟩
  · simp [sensitivityAt, not_nonempty_iff_eq_empty.mp hs]

end Cslib.BitString
