/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.GameTheory.FairDivision.MMSAsymptotic
public import Complexity.Foundations.Data.Code.HammingBound
import Complexity.Foundations.Data.Code.HammingBallBounds
import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Nat.Log
import Mathlib.Tactic.Positivity

/-!
# Exponentially large balanced codes for MMS types

A Gilbert–Varshamov code on 32s bits has at least 2^(16s) words and distance
at least s+1. Appending each word's complement produces balanced words on 64s
bits without losing rate or relative distance. This alternative to the exact
constants in [EzraGarbuz2027], Lemma 5, is intended for the same asymptotic MMS
construction; it does not assert Lemma 5's stronger distance k/4.
-/

public section

namespace Cslib.FairDivision.MMSCodes

open scoped BigOperators

/-- A binary code of positive rate and positive relative distance for each s. -/
theorem exists_binary_code (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : Finset (Fin (32 * s) → Bool), 2 ^ (16 * s) ≤ C.card ∧
      ∀ a ∈ C, ∀ b ∈ C, a ≠ b → s + 1 ≤ hammingDist a b := by
  classical
  obtain ⟨C, hmin, hsize⟩ := Code.exists_le_minDist_and_pow_le_card_mul_sum_choose
    (ι := Fin (32 * s)) (β := fun _ => Bool) (q := 2)
    (fun _ => Fintype.card_bool) (Nat.succ_pos s)
  simp only [Fintype.card_fin, Nat.add_one_sub_one, one_pow, mul_one] at hsize
  have hb : (∑ j ∈ Finset.range (s + 1), (32 * s).choose j) ≤ 2 ^ (16 * s) := by
    have h := Code.sum_range_choose_two_mul_sixteen_mul_le hs
    have he : 2 * (16 * s) = 32 * s := by omega
    rw [he] at h
    exact h.trans (Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _))
  refine ⟨C, ?_, fun a ha b hb hab => ?_⟩
  · apply Nat.le_of_mul_le_mul_right (c := 2 ^ (16 * s)) _ (by positivity)
    calc 2 ^ (16 * s) * 2 ^ (16 * s) = 2 ^ (32 * s) := by rw [← pow_add]; congr 1; omega
      _ ≤ C.card * ∑ j ∈ Finset.range (s + 1), (32 * s).choose j := hsize
      _ ≤ C.card * 2 ^ (16 * s) := Nat.mul_le_mul_left _ hb
  · exact_mod_cast Code.le_minDist_iff.mp hmin a ha b hb hab

/-- Append the bitwise complement to make a word balanced. -/
@[expose] def balance {r : ℕ} (a : Fin r → Bool) : Fin (r + r) → Bool :=
  Fin.addCases a (fun h => !(a h))

/-- The balanced encoding retains the original word. -/
theorem balance_injective (r : ℕ) : Function.Injective (@balance r) := by
  intro a b he
  funext h
  have hh := congrFun he (Fin.castAdd r h)
  simpa only [balance, Fin.addCases_left] using hh

/-- Every encoded word has exactly half of its bits set. -/
theorem balance_weight {r : ℕ} (a : Fin r → Bool) :
    (Finset.univ.filter fun h => balance a h).card = r := by
  have heq := (Finset.sum_boole (R := ℕ) (fun h => balance a h = true) Finset.univ).symm
  simp only [Nat.cast_id] at heq
  rw [heq, Fin.sum_univ_add]
  simp only [balance, Fin.addCases_left, Fin.addCases_right]
  rw [← Finset.sum_add_distrib]
  have he (h : Fin r) : (if a h = true then (1 : ℕ) else 0) +
      (if (!a h) = true then 1 else 0) = 1 := by cases a h <;> decide
  simp only [he, Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one]

/-- Complementing preserves each bit comparison, so balancing doubles distance. -/
theorem balance_distance {r : ℕ} (a b : Fin r → Bool) :
    hammingDist (balance a) (balance b) = 2 * hammingDist a b := by
  have heq (n : ℕ) (x y : Fin n → Bool) : hammingDist x y =
      ∑ h, if x h ≠ y h then (1 : ℕ) else 0 := by
    simpa only [hammingDist, Nat.cast_id] using
      (Finset.sum_boole (R := ℕ) (fun h => x h ≠ y h) Finset.univ).symm
  rw [heq, heq, Fin.sum_univ_add]
  simp only [balance, Fin.addCases_left, Fin.addCases_right]
  have he (h : Fin r) : ((!a h) ≠ (!b h)) ↔ a h ≠ b h := by
    cases a h <;> cases b h <;> decide
  simp only [he]
  omega

/-- Actual balanced codes, uniformly in s; code existence is not a hypothesis. -/
theorem exists_balanced_code (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : Finset (Fin (32 * s + 32 * s) → Bool), 2 ^ (16 * s) ≤ C.card ∧
      (∀ a ∈ C, (Finset.univ.filter fun h => a h).card = 32 * s) ∧
      ∀ a ∈ C, ∀ b ∈ C, a ≠ b → 2 * (s + 1) ≤ hammingDist a b := by
  classical
  obtain ⟨C, hcard, hdist⟩ := exists_binary_code s hs
  refine ⟨C.image balance, ?_, ?_, ?_⟩
  · simpa only [Finset.card_image_of_injective _ (balance_injective _)] using hcard
  · intro a ha
    obtain ⟨a, _, rfl⟩ := Finset.mem_image.mp ha
    exact balance_weight a
  · intro a ha b hb hab
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hb
    rw [balance_distance]
    exact Nat.mul_le_mul_left 2 (hdist x hx y hy (fun h => hab (h ▸ rfl)))

/-- For every requested population, choose that many distinct balanced types on
64(floor(log₂ n)+1) bits, with explicit linear pairwise distance. -/
theorem exists_population_code (n : ℕ) :
    ∃ a : Fin n → Fin (32 * (Nat.log 2 n + 1) + 32 * (Nat.log 2 n + 1)) → Bool,
      Function.Injective a ∧
      (∀ i, (Finset.univ.filter fun h => a i h).card = 32 * (Nat.log 2 n + 1)) ∧
      ∀ i j, i ≠ j → 2 * (Nat.log 2 n + 2) ≤ hammingDist (a i) (a j) := by
  classical
  obtain ⟨C, hcard, hbal, hdist⟩ := exists_balanced_code (Nat.log 2 n + 1) (by omega)
  have hn : n ≤ C.card := by
    have hp := Nat.lt_pow_succ_log_self (b := 2) (by decide) n
    exact hp.le.trans ((Nat.pow_le_pow_right (by decide) (by omega)).trans hcard)
  obtain ⟨D, hDC, hD⟩ := Finset.exists_subset_card_eq hn
  let e : Fin n ≃ D := (Finset.equivFinOfCardEq hD).symm
  refine ⟨fun i => (e i).val, ?_, ?_, ?_⟩
  · intro i j hij
    exact e.injective (Subtype.ext hij)
  · intro i
    exact hbal _ (hDC (e i).property)
  · intro i j hij
    exact hdist _ (hDC (e i).property) _ (hDC (e j).property)
      (fun h => hij (e.injective (Subtype.ext h)))

/-- Large enough populations have room for all high items in the construction. -/
theorem high_items_le_population (n : ℕ) (hn : 65536 ≤ n) :
    2 * (32 * (Nat.log 2 n + 1) + 32 * (Nat.log 2 n + 1)) + 2 ≤ n := by
  have hlog : 16 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by decide) (by norm_num; exact hn)
  have hlin : ∀ r : ℕ, 16 ≤ r → 128 * (r + 1) + 2 ≤ 2 ^ r := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => norm_num
    | succ r hr ih =>
      rw [pow_succ]
      nlinarith
  have hp := Nat.pow_log_le_self 2 (show n ≠ 0 by omega)
  have hl := hlin _ hlog
  omega

/-- The actual source item type has n+5k items, at most n+640 floor(log₂ n),
when instantiated with the constructed population code. -/
theorem population_item_count (n : ℕ) (hn : 65536 ≤ n) :
    let k := 32 * (Nat.log 2 n + 1) + 32 * (Nat.log 2 n + 1)
    Fintype.card (MMSAsymptotic.Good k (n - (2 * k + 2))) = n + 5 * k ∧
      Fintype.card (MMSAsymptotic.Good k (n - (2 * k + 2))) ≤ n + 640 * Nat.log 2 n := by
  dsimp only
  rw [MMSAsymptotic.card_goods]
  have hi := high_items_le_population n hn
  have hl : 16 ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by decide) (by norm_num; exact hn)
  omega

end Cslib.FairDivision.MMSCodes
