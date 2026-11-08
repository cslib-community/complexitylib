/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.BooleanAnalysis.MobiusInsert
import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Subset coefficients factor across disjoint coordinate colors

## Main results

* `Cslib.BitString.subsetMobius_color_product`: the coefficient of a product of functions on
  disjoint color classes is the product of their coefficients.
-/

public section

namespace Cslib.BitString

open Finset

/-- Extracting a coefficient of a product on disjoint color classes factors test by test. -/
theorem subsetMobius_color_product {α κ R : Type*} [DecidableEq κ]
    [CommRing R] (I : Finset κ) (color : α → κ) (f : κ → Finset α → R) (S : Finset α)
    (hS : ∀ a ∈ S, color a ∈ I) :
    subsetMobius (fun T => ∏ i ∈ I, f i (T.filter fun a => color a = i)) S =
      ∏ i ∈ I, subsetMobius (f i) (S.filter fun a => color a = i) := by
  classical
  induction S using Finset.induction_on generalizing f with
  | empty => simp [subsetMobius]
  | @insert a S ha ih =>
    have hj := hS a (mem_insert_self _ _)
    have ht : ∀ b ∈ S, color b ∈ I := fun b hb => hS b (mem_insert_of_mem hb)
    let g : κ → Finset α → R := fun i T =>
      if i = color a then f i (insert a T) else f i T
    have he : (fun T : Finset α => ∏ i ∈ I, f i ((insert a T).filter fun b => color b = i)) =
        (fun T : Finset α => ∏ i ∈ I, g i (T.filter fun b => color b = i)) := by
      funext T
      apply prod_congr rfl
      intro i _
      by_cases hi : i = color a
      · simp [g, hi, filter_insert]
      · simp [g, hi, Ne.symm hi, filter_insert]
    rw [subsetMobius_insert _ ha, he, ih g ht, ih f ht]
    rw [← mul_prod_erase I (fun i => subsetMobius (g i) (S.filter fun b => color b = i)) hj,
      ← mul_prod_erase I (fun i => subsetMobius (f i) (S.filter fun b => color b = i)) hj,
      ← mul_prod_erase I
        (fun i => subsetMobius (f i) ((insert a S).filter fun b => color b = i)) hj]
    have hg : (∏ i ∈ I.erase (color a), subsetMobius (g i) (S.filter fun b => color b = i)) =
        ∏ i ∈ I.erase (color a), subsetMobius (f i) (S.filter fun b => color b = i) := by
      apply prod_congr rfl
      intro i hi
      simp [g, (mem_erase.mp hi).1]
    have hs : (∏ i ∈ I.erase (color a),
        subsetMobius (f i) ((insert a S).filter fun b => color b = i)) =
        ∏ i ∈ I.erase (color a), subsetMobius (f i) (S.filter fun b => color b = i) := by
      apply prod_congr rfl
      intro i hi
      simp [filter_insert, Ne.symm (mem_erase.mp hi).1]
    rw [hg, hs]
    have haf : a ∉ S.filter (fun b => color b = color a) := fun h => ha (mem_filter.mp h).1
    simp only [filter_insert, ↓reduceIte]
    rw [subsetMobius_insert _ haf, sub_mul]
    simp [g]

end Cslib.BitString
