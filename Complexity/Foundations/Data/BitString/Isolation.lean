/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset

/-!
# Isolated directions of a set of bit strings

For a set `S` of bit strings of length `n` and `σ ∈ S`, the *isolation* of `σ` is the number of
coordinates `i` such that flipping coordinate `i` of `σ` leaves `S` (`Cslib.BitString.isolation`).
Every nonempty `S` satisfies `2^n ≤ ∑_{σ ∈ S} 2^{isolation S σ}`
(`Cslib.BitString.two_pow_le_sum_two_pow_isolation`): a single point is isolated in all `n`
directions, and in general the bound follows by induction on `n`, splitting `S` by its first
coordinate. This is the counting step of the PPZ analysis for formulas with several satisfying
assignments [Paturi, Pudlák, Zane][PPZ1997].

## Main definitions

* `Cslib.BitString.isolation`: the number of directions in which `σ` is isolated in `S`.

## Main results

* `Cslib.BitString.two_pow_le_sum_two_pow_isolation`: `2^n ≤ ∑_{σ ∈ S} 2^{isolation S σ}`.

## References

* [R. Paturi, P. Pudlák, F. Zane, *Satisfiability Coding Lemma*][PPZ1997]
-/

@[expose] public section

namespace Cslib.BitString

open Finset

variable {n : ℕ}

/-- The number of coordinates `i` such that flipping coordinate `i` of `σ` leaves `S`. -/
def isolation (S : Finset (Fin n → Bool)) (σ : Fin n → Bool) : ℕ :=
  (univ.filter fun i => Function.update σ i (!σ i) ∉ S).card

/-- The strings of `S` with first coordinate `b`, with that coordinate removed. -/
def slice (S : Finset (Fin (n + 1) → Bool)) (b : Bool) : Finset (Fin n → Bool) :=
  univ.filter fun τ => Fin.cons b τ ∈ S

theorem mem_slice {S : Finset (Fin (n + 1) → Bool)} {b : Bool} {τ : Fin n → Bool} :
    τ ∈ slice S b ↔ Fin.cons b τ ∈ S := by
  simp [slice]

/-- Flipping a coordinate of `Fin.cons b τ` other than the first. -/
private theorem update_cons_succ (b : Bool) (τ : Fin n → Bool) (j : Fin n) (c : Bool) :
    Function.update (Fin.cons b τ : Fin (n + 1) → Bool) j.succ c =
      Fin.cons b (Function.update τ j c) := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp [Function.update_of_ne (Fin.succ_ne_zero j).symm]
  · by_cases hk : k = j
    · subst hk
      simp
    · simp [Function.update_of_ne hk, Function.update_of_ne (fun e => hk (Fin.succ_injective _ e))]

/-- Flipping the first coordinate of `Fin.cons b τ`. -/
private theorem update_cons_zero (b : Bool) (τ : Fin n → Bool) (c : Bool) :
    Function.update (Fin.cons b τ : Fin (n + 1) → Bool) 0 c = Fin.cons c τ := by
  ext i
  refine Fin.cases ?_ (fun k => ?_) i
  · simp
  · simp

/-- The isolation of `Fin.cons b τ` in `S` is at least the isolation of `τ` in its slice, plus one
if flipping the first coordinate leaves `S`. -/
theorem isolation_cons_ge (S : Finset (Fin (n + 1) → Bool)) (b : Bool) (τ : Fin n → Bool) :
    isolation (slice S b) τ + (if Fin.cons (!b) τ ∈ S then 0 else 1) ≤
      isolation S (Fin.cons b τ) := by
  unfold isolation
  set A := univ.filter fun j : Fin n => Function.update τ j (!τ j) ∉ slice S b
  set B := univ.filter fun i : Fin (n + 1) =>
    Function.update (Fin.cons b τ : Fin (n + 1) → Bool) i (!(Fin.cons b τ : Fin (n + 1) → Bool) i)
      ∉ S
  have hA : A.map (Fin.succEmb n) ⊆ B := by
    intro i hi
    obtain ⟨j, hj, rfl⟩ := mem_map.mp hi
    simp only [A, mem_filter, mem_univ, true_and, mem_slice] at hj
    simp only [B, mem_filter, mem_univ, true_and]
    change Function.update (Fin.cons b τ : Fin (n + 1) → Bool) j.succ
      (!(Fin.cons b τ : Fin (n + 1) → Bool) j.succ) ∉ S
    rwa [Fin.cons_succ, update_cons_succ]
  split_ifs with h
  · simpa using card_le_card hA
  · have h0 : (0 : Fin (n + 1)) ∈ B := by
      simp only [B, mem_filter, mem_univ, true_and, Fin.cons_zero]
      rwa [update_cons_zero]
    have h0A : (0 : Fin (n + 1)) ∉ A.map (Fin.succEmb n) := by
      simp [Fin.succ_ne_zero]
    calc
      A.card + 1 = (insert 0 (A.map (Fin.succEmb n))).card := by
        rw [card_insert_of_notMem h0A, card_map]
      _ ≤ B.card := card_le_card (insert_subset h0 hA)

/-- The sum over `S` of a function of `σ`, split by the first coordinate. -/
private theorem sum_split (S : Finset (Fin (n + 1) → Bool)) (f : (Fin (n + 1) → Bool) → ℕ) :
    ∑ σ ∈ S, f σ = ∑ b : Bool, ∑ τ ∈ slice S b, f (Fin.cons b τ) := by
  rw [Fintype.sum_bool]
  have hsplit (b : Bool) : ∑ τ ∈ slice S b, f (Fin.cons b τ) =
      ∑ σ ∈ S.filter (fun σ => σ 0 = b), f σ := by
    refine sum_nbij' (fun τ => Fin.cons b τ) (fun σ => Fin.tail σ) ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      rw [mem_slice] at hτ
      rw [mem_filter]
      exact ⟨hτ, rfl⟩
    · intro σ hσ
      rw [mem_filter] at hσ
      rw [mem_slice, ← hσ.2, Fin.cons_self_tail]
      exact hσ.1
    · intro τ _
      exact Fin.tail_cons _ _
    · intro σ hσ
      rw [mem_filter] at hσ
      change Fin.cons b (Fin.tail σ) = σ
      rw [← hσ.2]
      exact Fin.cons_self_tail σ
    · intro τ _
      rfl
  rw [hsplit, hsplit, ← sum_filter_add_sum_filter_not S (fun σ => σ 0 = true)]
  congr 1

/-- When `slice S (!b)` is empty, each element of `slice S b` gains at least one isolation bit
under `Fin.cons b`. -/
private theorem sum_slice_mul_two_le_of_not_nonempty {n : ℕ} (S : Finset (Fin (n + 1) → Bool))
    (b : Bool) (hnot : ¬(slice S (!b)).Nonempty) :
    (∑ τ ∈ slice S b, 2 ^ isolation (slice S b) τ) * 2 ≤
      ∑ τ ∈ slice S b, 2 ^ isolation S (Fin.cons b τ) := by
  have hmem : ∀ τ ∈ slice S b, Fin.cons (!b) τ ∉ S := fun τ _ h => hnot ⟨τ, mem_slice.mpr h⟩
  calc (∑ τ ∈ slice S b, 2 ^ isolation (slice S b) τ) * 2
      = ∑ τ ∈ slice S b, 2 ^ (isolation (slice S b) τ +
          if Fin.cons (!b) τ ∈ S then 0 else 1) := by
        rw [sum_mul]
        exact sum_congr rfl fun τ hτ => by rw [ite_eq_right (hmem τ hτ), pow_succ]
    _ ≤ ∑ τ ∈ slice S b, 2 ^ isolation S (Fin.cons b τ) :=
        sum_le_sum fun τ _ => Nat.pow_le_pow_right two_pos (isolation_cons_ge S b τ)

/-- Lifting `slice S b` by `Fin.cons b` does not decrease `∑ 2 ^ isolation`. -/
private theorem sum_slice_le {n : ℕ} (S : Finset (Fin (n + 1) → Bool)) (b : Bool) :
    ∑ τ ∈ slice S b, 2 ^ isolation (slice S b) τ ≤
      ∑ τ ∈ slice S b, 2 ^ isolation S (Fin.cons b τ) :=
  sum_le_sum fun τ _ =>
    Nat.pow_le_pow_right two_pos ((Nat.le_add_right _ _).trans (isolation_cons_ge S b τ))

/-- **The isolation inequality**: every nonempty set `S` of bit strings of length `n` satisfies
`2^n ≤ ∑_{σ ∈ S} 2^{isolation S σ}`. -/
theorem two_pow_le_sum_two_pow_isolation :
    ∀ {n : ℕ} (S : Finset (Fin n → Bool)), S.Nonempty →
      2 ^ n ≤ ∑ σ ∈ S, 2 ^ isolation S σ
  | 0, S, hS => by
    obtain ⟨σ, hσ⟩ := hS
    calc
      2 ^ 0 = 1 := rfl
      _ ≤ 2 ^ isolation S σ := Nat.one_le_two_pow
      _ ≤ ∑ σ ∈ S, 2 ^ isolation S σ :=
        single_le_sum (f := fun σ => 2 ^ isolation S σ) (fun _ _ => Nat.zero_le _) hσ
  | n + 1, S, hS => by
    rw [sum_split S fun σ => 2 ^ isolation S σ]
    by_cases h0 : (slice S false).Nonempty <;> by_cases h1 : (slice S true).Nonempty
    · -- Both slices are nonempty.
      have ih0 := two_pow_le_sum_two_pow_isolation (slice S false) h0
      have ih1 := two_pow_le_sum_two_pow_isolation (slice S true) h1
      have e0 := sum_slice_le S false
      have e1 := sum_slice_le S true
      rw [Fintype.sum_bool, pow_succ]
      omega
    · -- Only the slice with first coordinate `false` is nonempty.
      have ih0 := two_pow_le_sum_two_pow_isolation (slice S false) h0
      rw [Fintype.sum_bool, not_nonempty_iff_eq_empty.mp h1, sum_empty, zero_add, pow_succ]
      exact (Nat.mul_le_mul_right 2 ih0).trans (sum_slice_mul_two_le_of_not_nonempty S false h1)
    · -- Only the slice with first coordinate `true` is nonempty.
      have ih1 := two_pow_le_sum_two_pow_isolation (slice S true) h1
      rw [Fintype.sum_bool, not_nonempty_iff_eq_empty.mp h0, sum_empty, add_zero, pow_succ]
      exact (Nat.mul_le_mul_right 2 ih1).trans (sum_slice_mul_two_le_of_not_nonempty S true h0)
    · -- Both slices are empty, so `S` is empty.
      exfalso
      obtain ⟨σ, hσ⟩ := hS
      cases hb : σ 0
      · exact h0 ⟨Fin.tail σ, mem_slice.mpr (by rw [← hb, Fin.cons_self_tail]; exact hσ)⟩
      · exact h1 ⟨Fin.tail σ, mem_slice.mpr (by rw [← hb, Fin.cons_self_tail]; exact hσ)⟩

end Cslib.BitString
