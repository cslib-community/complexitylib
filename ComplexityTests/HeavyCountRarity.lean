/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Foundations.Probability.HeavyCount
import Complexity.Foundations.Probability.HeavyCountRarity
import Complexity.Probability.PairwiseIndependentHash.HeavyCount
import Mathlib.Tactic.NormNum

/-!
# Tests for heavy-count rarity and deterministic mean errors

The heavy endpoints in the first example are perfectly correlated except for one always-kept
endpoint. The integrated examples use a separate event coordinate, correlated source/endpoint
masks, and nonzero signed fourth-moment errors. A noise counterexample records why the mean
error must be independent of the environment after fixing the source and endpoint.
-/

namespace ComplexityTests.HeavyCountRarity

open Finset Cslib Cslib.Probability
open scoped BigOperators

private abbrev correlated (σ y : Fin 5) : Prop := y = 0 ∨ σ = 0

-- All four non-forced endpoints appear together with probability `1/5`.
example : ({σ | correlated σ 1 ∧ correlated σ 2} : Finset (Fin 5)) = {0} := by
  decide

private theorem heavy_iff (σ : Fin 5) :
    heavyCountEvent correlated (fun _ => 1 / 3) 1 8 σ ↔ σ = 0 := by
  classical
  by_cases hσ : σ = 0
  · subst σ
    norm_num [heavyCountEvent, correlated]
  · have hsingle : ({y : Fin 5 | y = 0} : Finset (Fin 5)) = {0} := by
      ext y
      simp
    norm_num [heavyCountEvent, correlated, hσ, hsingle]

-- The rare event has positive probability, and the explicit upper bound is below one.
open scoped Classical in
example : (dens {σ | heavyCountEvent correlated (fun _ => 1 / 3) 1 8 σ} : ℝ) = 1 / 5 := by
  classical
  have hevent : ({σ | heavyCountEvent correlated (fun _ => 1 / 3) 1 8 σ} :
      Finset (Fin 5)) = {0} := by
    ext σ
    simp only [mem_filter, mem_univ, true_and, mem_singleton]
    exact heavy_iff σ
  rw [hevent, dens_eq_card_div_card]
  norm_num

open scoped Classical in
example : (#{σ : Fin 5 | heavyCountEvent correlated (fun _ => 1 / 3) 1 8 σ} : ℝ) ≤
    (7 / 12) * Fintype.card (Fin 5) := by
  classical
  have hpair : ∀ y : Fin 5, y ≠ 0 →
      (#{σ ∈ (univ : Finset (Fin 5)) | correlated σ y} : ℝ) ≤
        (1 : ℝ) * (1 / 5) * #(univ : Finset (Fin 5)) := by
    intro y hy
    have hs : ({σ : Fin 5 | correlated σ y} : Finset (Fin 5)) = {0} := by
      ext σ
      simp [correlated, hy]
    norm_num [hs]
  have h := @card_filter_heavyCountEvent_le (Fin 5) (Fin 5) (inferInstance : Fintype (Fin 5))
    correlated univ (0 : Fin 5)
    (a := 1 / 5) (ρ := 1) (c := 1) (M := 1 / 3) (d := fun _ => 1 / 3)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun _ => by norm_num) (by norm_num)
    (by
      intro w hw
      convert hpair w hw using 1
      congr 2
      ext σ
      simp) (n := 8) (by decide)
  norm_num at h ⊢
  exact h

-- An odd capacity requires rounding up; equality with the heavy threshold is excluded.
example : ¬ heavyCountEvent (fun (_ : Unit) (y : Fin 3) => y = 0)
    (fun _ => 1) 1 3 () := by
  classical
  norm_num [heavyCountEvent, show ({y : Fin 3 | y = 0} : Finset (Fin 3)) = {0} by decide]

example : heavyCountEvent (fun (_ : Unit) (y : Fin 3) => y ≠ 2)
    (fun _ => 1) 1 3 () := by
  classical
  norm_num [heavyCountEvent, show ({y : Fin 3 | y ≠ 2} : Finset (Fin 3)) = {0, 1} by decide]

example : ¬ heavyCountEvent (fun (_ : Unit) (_ : Fin 3) => True)
    (fun _ => 1 / 4) 1 1 () := by
  classical
  norm_num [heavyCountEvent]

private abbrev kept (σ : Fin 2 × Fin 2) (x : Fin 2) : Prop := σ.1 = x
private abbrev rare (σ : Fin 2 × Fin 2) (_ : Fin 2) : Prop := σ.2 = 0
private def meanError (x _ : Fin 2) : ℝ := if x = 0 then -2 else 3

private theorem rare_on_slice (x y : Fin 2) :
    (#{σ | kept σ x ∧ kept σ y ∧ rare σ x} : ℝ) ≤
      (1 / 2) * #{σ | kept σ x ∧ kept σ y} := by
  have hn : ∀ x y : Fin 2, #{σ | kept σ x ∧ kept σ y ∧ rare σ x} =
      if x = y then 1 else 0 := by decide
  have hd : ∀ x y : Fin 2, #{σ | kept σ x ∧ kept σ y} =
      if x = y then 2 else 0 := by decide
  rw [hn, hd]
  split_ifs <;> norm_num

example :
    rowNormPow 4 2 (1 / 2) kept kept
        (fun σ x y => if rare σ x then meanError x y else 0) ≤
      (1 / 2) * rowNormPow 4 2 (1 / 2) kept kept (fun _ x y => meanError x y) :=
  rowNormPow_event_le (by decide) (by norm_num) rare_on_slice meanError

example :
    vertexNormPow 4 2 (1 / 2) kept (fun σ x =>
        if rare σ x then kthLargest 1 {y | kept σ y} (fun y => |meanError x y|) else 0) ≤
      (1 / 2) * rowNormPow 4 2 (1 / 2) kept kept (fun _ x y => meanError x y) :=
  vertexNormPow_kthLargest_event_le (by decide) (by norm_num) rare_on_slice meanError

example :
    vertexNormPow 4 2 (1 / 2) kept
        (fun σ x => if rare σ x then meanError x x else 0) ≤
      (1 / 2) * rowNormPow 4 2 (1 / 2) kept kept (fun _ x y => meanError x y) := by
  apply vertexNormPow_event_le_rowNormPow (by decide) (by norm_num) rare_on_slice meanError
    (fun _ x => meanError x x)
  intro σ x hx
  have hY : ({y | kept σ y} : Finset (Fin 2)) = {x} := by
    ext y
    simp only [mem_filter, mem_univ, true_and, mem_singleton, kept]
    rw [show σ.1 = x from hx]
    exact eq_comm
  rw [hY, sum_singleton]

private theorem card_kept (x : Fin 2) : #{y : Fin 2 | x = y} = 1 := by
  have h : ({y : Fin 2 | x = y} : Finset (Fin 2)) = {x} := by
    ext y
    simp [eq_comm]
  rw [h, card_singleton]

private theorem full_mean_power :
    rowNormPow 4 2 (1 / 2) kept kept (fun _ x y => meanError x y) = 97 / 2 := by
  norm_num [rowNormPow, kept, meanError, sum_filter, expect_eq_sum_div_card,
    Fintype.sum_prod_type, Fin.sum_univ_two, card_kept]

private theorem masked_mean_power :
    rowNormPow 4 2 (1 / 2) kept kept
      (fun σ x y => if rare σ x then meanError x y else 0) = 97 / 4 := by
  norm_num [rowNormPow, kept, rare, meanError, sum_filter, expect_eq_sum_div_card,
    Fintype.sum_prod_type, Fin.sum_univ_two, card_kept]

-- Both means are nonzero, and masking halves the integrated fourth moment exactly.
example :
    rowNormPow 4 2 (1 / 2) kept kept
        (fun σ x y => if rare σ x then meanError x y else 0) =
      (1 / 2) * rowNormPow 4 2 (1 / 2) kept kept (fun _ x y => meanError x y) := by
  rw [masked_mean_power, full_mean_power]
  norm_num

private def noise (σ : Fin 2 × Fin 2) (x y : Fin 2) : ℝ :=
  if rare σ x then meanError x y else 0

-- Environment-dependent noise concentrated on the rare event receives no rarity gain.
example :
    ¬ rowNormPow 4 2 (1 / 2) kept kept
        (fun σ x y => if rare σ x then noise σ x y else 0) ≤
      (1 / 2) * rowNormPow 4 2 (1 / 2) kept kept noise := by
  norm_num [rowNormPow, kept, rare, noise, meanError, sum_filter, expect_eq_sum_div_card,
    Fintype.sum_prod_type, Fin.sum_univ_two, card_kept]

-- Empty conditioning slices and an empty environment have zero integrated contribution.
example : rowNormPow 4 2 (1 / 2) (fun (_ : Fin 2 × Fin 2) (_ : Fin 2) => False)
    kept (fun _ x y => meanError x y) = 0 := by
  simp [rowNormPow]

example : rowNormPow 4 1 1 (fun (_ : Empty) (_ : Fin 1) => True)
    (fun _ _ => True) (fun _ _ _ => 5) = 0 := by
  simp [rowNormPow]

private instance : Fact (Nat.Prime 5) := ⟨by decide⟩

-- The concrete affine channel has a conditional bound strictly below one.
open scoped Classical in
example :
    (#{σ | affineRetains 5 1 1 σ 0 ∧ heavyCountEvent
      (fun σ (y : ZMod 5) => affineRetains 5 1 1 σ y) (fun _ => 1 / 3) 1 8 σ} : ℝ) ≤
      (11 / 12) * #{σ | affineRetains 5 1 1 σ 0} := by
  classical
  have h := card_heavyCountEvent_affineRetains_le
    (V := ZMod 5) (P := 5) (H := 1) (ident := id) Function.injective_id
    (a := 1 / 5) (by norm_num) (by norm_num) (Lt := 1) (by norm_num)
    (d := fun _ => 1 / 3) (ρ := 1) (M := 1 / 3)
    (by norm_num) (by norm_num) (fun _ => by norm_num) (by norm_num)
    (n := 8) (by decide) 0
  norm_num at h ⊢
  exact h

private abbrev forced (_ : Fin 5) (y : Fin 5) : Prop := y = 0

-- The actual nonempty heavy event controls the retained maximum after narrowing the usage mask.
open scoped Classical in
example :
    vertexNormPow 4 5 1 (fun (_ _ : Fin 5) => True) (fun σ _ =>
      if heavyCountEvent correlated (fun _ => 1 / 3) 1 8 σ then
        kthLargest 1 {y | forced σ y} (fun _ => |(2 : ℝ)|) else 0) ≤
      (7 / 12) * rowNormPow 4 5 1 (fun (_ _ : Fin 5) => True) forced (fun _ _ _ => 2) := by
  classical
  have hpair : ∀ x y w : Fin 5, w ≠ y →
      (#{σ | True ∧ forced σ y ∧ correlated σ w} : ℝ) ≤
        (1 : ℝ) * (1 / 5) * #{σ | True ∧ forced σ y} := by
    intro _ y w hwy
    by_cases hy : y = 0
    · subst y
      have hs : ({σ : Fin 5 | correlated σ w} : Finset (Fin 5)) = {0} := by
        ext σ
        simp [correlated, hwy]
      norm_num [forced, hs]
    · simp [forced, hy]
  have h := vertexNormPow_heavyCountEvent_le (Ω := Fin 5) (V := Fin 5)
    (s := 4) (N := 5) (u := 1)
    (by decide) (by norm_num) (fun (_ _ : Fin 5) => True) correlated forced
    (a := 1 / 5) (ρ := 1) (c := 1) (M := 1 / 3) (n := 8)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by decide)
    (fun _ _ => 1 / 3) (fun _ _ => by norm_num) (fun _ => by norm_num)
    (by
      intro x y w hwy
      convert hpair x y w hwy using 1
      congr 2
      ext σ
      simp) (fun _ _ => 2)
  have hfactor : (2 * (1 + 4 * (1 : ℝ) * (1 / 3)) / (((8 : ℕ) : ℝ) * 1)) = 7 / 12 := by
    norm_num
  rw [hfactor] at h
  exact h

end ComplexityTests.HeavyCountRarity
