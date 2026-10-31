/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/
import Complexity.Probability.PairwiseIndependentHash.HeavyCount
import Mathlib.Tactic.NormNum

/-!
# Tests for conditional heavy-count rarity

Three off-endpoint hits are perfectly correlated: they all occur on one of eight draws.
The distinguished endpoint is always retained. All four targets have value `1/2`, so with
`a = 1/8`, `ρ = 1`, and capacity eight, the exceptional frequency is exactly `1/8` and the
proved bound is `1/2 < 1`. An odd capacity exercises the ceiling in finite Markov.

The affine example uses all seven field elements, broad side two and narrower endpoint side
one. Its deterministic row is constantly `1/3`; the actual bound is `19/21 < 1`. The zero
affine map is an exceptional seed in the conditioning slice, while the identity map belongs
to the same slice and is not exceptional.

A finite set of natural-number endpoints exercises the absence of a `Fintype` requirement.
At zero scale, its always-retained light endpoint violates the old all-endpoint pair premise
but does not affect the heavy count; the stronger division-free bound is attained exactly.
-/

namespace ComplexityTests.CompressionHeavyCount

open Finset Cslib.Probability
open scoped BigOperators

private abbrev hit (σ : Fin 8) (y : Fin 4) : Prop := y = 0 ∨ σ = 0

private theorem row_mass : (1 / 8 : ℝ) * ∑ _y : Fin 4, (1 / 2 : ℝ) ≤ 1 / 4 := by
  norm_num

private theorem pair_count (y : Fin 4) (_ : y ∈ (univ : Finset (Fin 4)))
    (_ : (1 : ℝ) / 4 < 1 / 2) (hy : y ≠ 0) :
    (#{σ ∈ (univ : Finset (Fin 8)) | hit σ y} : ℝ) ≤ 1 * (1 / 8) * #(univ : Finset (Fin 8)) := by
  have hset : {σ ∈ (univ : Finset (Fin 8)) | hit σ y} = {0} := by
    ext σ
    simp [hit, hy]
  rw [hset]
  norm_num

private theorem retained_heavy (σ : Fin 8) :
    {y ∈ (univ : Finset (Fin 4)) | hit σ y ∧ (1 : ℝ) / 4 < 1 / 2} =
      if σ = 0 then univ else {0} := by
  by_cases hσ : σ = 0 <;> ext y <;> norm_num [hit, hσ]

private theorem bad_seeds :
    {σ ∈ (univ : Finset (Fin 8)) |
      8 ≤ 2 * #{y ∈ (univ : Finset (Fin 4)) | hit σ y ∧ (1 : ℝ) / 4 < 1 / 2}} = {0} := by
  ext σ
  simp only [mem_filter, mem_univ, true_and, retained_heavy, mem_singleton]
  by_cases hσ : σ = 0 <;> simp [hσ]

-- Distinct off-endpoint hits are correlated, not independent Bernoulli trials.
example : ({σ : Fin 8 | hit σ 1 ∧ hit σ 2} : Finset (Fin 8)) = {0} ∧
    (1 / 8 : ℝ) ≠ (1 / 8) ^ 2 := by
  constructor
  · ext σ
    norm_num [hit]
  · norm_num

example : (#{σ ∈ (univ : Finset (Fin 8)) |
      8 ≤ 2 * #{y ∈ (univ : Finset (Fin 4)) | hit σ y ∧ (1 : ℝ) / 4 < 1 / 2}} : ℝ) /
      #(univ : Finset (Fin 8)) = 1 / 8 := by
  rw [bad_seeds]
  norm_num

-- The theorem consumes the actual row mass and off-endpoint pair counts.
example : (#{σ ∈ (univ : Finset (Fin 8)) |
      8 ≤ 2 * #{y ∈ (univ : Finset (Fin 4)) | hit σ y ∧ (1 : ℝ) / 4 < 1 / 2}} : ℝ) /
      #(univ : Finset (Fin 8)) ≤ 1 / 2 ∧ (1 / 2 : ℝ) < 1 := by
  have h := card_filter_heavyCountEvent_div_card_le hit univ univ 0
    (d := fun _ => (1 / 2 : ℝ)) (a := 1 / 8) (c := 1) (ρ := 1) (M := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ _ => by norm_num)
    row_mass (by
      intro w hw hdw hwy
      convert pair_count w hw hdw hwy using 1
      congr 2
      ext σ
      simp) (n := 8) (by decide)
  norm_num [heavyCountEvent] at h ⊢
  exact h

example : (#{σ ∈ (univ : Finset (Fin 8)) |
      7 ≤ 2 * #{y ∈ (univ : Finset (Fin 4)) | hit σ y ∧ (1 : ℝ) / 4 < 1 / 2}} : ℝ) /
      #(univ : Finset (Fin 8)) ≤ 4 / 7 := by
  have h := card_filter_heavyCountEvent_div_card_le hit univ univ 0
    (d := fun _ => (1 / 2 : ℝ)) (a := 1 / 8) (c := 1) (ρ := 1) (M := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ _ => by norm_num)
    row_mass (by
      intro w hw hdw hwy
      convert pair_count w hw hdw hwy using 1
      congr 2
      ext σ
      simp) (n := 7) (by decide)
  norm_num [heavyCountEvent] at h ⊢
  exact h

-- A value exactly at the light/heavy threshold is not heavy.
example : #{y ∈ (univ : Finset (Fin 4)) | (1 : ℝ) / 4 < if y = 0 then 1 / 4 else 1 / 2} = 3 := by
  have hset : {y ∈ (univ : Finset (Fin 4)) |
      (1 : ℝ) / 4 < if y = 0 then 1 / 4 else 1 / 2} = (univ : Finset (Fin 4)).erase 0 := by
    ext y
    by_cases hy : y = 0 <;> norm_num [hy]
  rw [hset]
  norm_num

-- Either conditioning slice may be empty.
example : (#{σ ∈ (∅ : Finset (Fin 8)) |
      8 ≤ 2 * #{y ∈ (univ : Finset (Fin 4)) | hit σ y ∧ (1 : ℝ) / 4 < 1 / 2}} : ℝ) /
      #(∅ : Finset (Fin 8)) ≤ 1 / 2 := by
  have h := card_filter_heavyCountEvent_div_card_le hit ∅ univ 0
    (d := fun _ => (1 / 2 : ℝ)) (a := 1 / 8) (c := 1) (ρ := 1) (M := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ _ => by norm_num)
    row_mass (fun _ _ _ _ => by simp) (n := 8) (by decide)
  norm_num [heavyCountEvent] at h ⊢

example (R : Finset Bool) :
    (#{σ ∈ R ×ˢ (univ : Finset (Fin 8)) |
      8 ≤ 2 * #{y ∈ (univ : Finset (Fin 4)) | hit σ.2 y ∧ (1 : ℝ) / 4 < 1 / 2}} : ℝ) /
      #(R ×ˢ (univ : Finset (Fin 8))) ≤ 1 / 2 := by
  have h := card_filter_heavyCountEvent_product_div_card_le hit R univ univ 0
    (d := fun _ => (1 / 2 : ℝ)) (a := 1 / 8) (c := 1) (ρ := 1) (M := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (fun _ _ => by norm_num)
    row_mass (by
      intro w hw hdw hwy
      convert pair_count w hw hdw hwy using 1
      congr 2
      ext σ
      simp) (n := 8) (by decide)
  norm_num [heavyCountEvent] at h ⊢
  exact h

private instance : Fact (Nat.Prime 7) := ⟨by decide⟩

private abbrev AffineSeed := Matrix (Fin 1) (Fin 1) (ZMod 7) × (Fin 1 → ZMod 7)
private def narrowSlice : Finset AffineSeed := {σ | affineRetains 7 1 1 σ 0}
private abbrev affineBad (σ : AffineSeed) : Prop :=
  14 ≤ 2 * #({y : ZMod 7 | affineRetains 7 1 2 σ y} : Finset (ZMod 7))

-- An actual affine specialization with a strictly narrower positive endpoint box.
example : (#{σ ∈ narrowSlice | affineBad σ} : ℝ) / #narrowSlice ≤ 19 / 21 ∧
    (19 / 21 : ℝ) < 1 := by
  have h := card_heavyCountEvent_affineRetains_div_card_le (univ : Finset (ZMod 7))
    Function.injective_id (H := 1) (a := (2 / 7 : ℝ)) (by norm_num) (by norm_num)
    (Lt := 1) (by norm_num) (d := fun _ => (1 / 3 : ℝ)) (ρ := 1) (M := 2 / 3)
    (by norm_num) (by norm_num) (fun _ _ => by norm_num) (by norm_num) (n := 14) (by decide) 0
  norm_num [narrowSlice, affineBad, heavyCountEvent] at h ⊢
  exact h

-- The conditioning event and exceptional event are nonempty, while not all its seeds are bad.
example : ((0, 0) : AffineSeed) ∈ narrowSlice ∧ affineBad (0, 0) := by
  constructor
  · decide
  · decide

example : ((fun _ _ => 1, 0) : AffineSeed) ∈ narrowSlice ∧
    ¬ affineBad (fun _ _ => 1, 0) := by
  constructor
  · decide
  · decide

private abbrev finiteHits (_ : Unit) (_ : ℕ) : Prop := True
private def finiteSignal (w : ℕ) : ℝ := if w = 1 then 0 else 1

private theorem zero_scale_pair {ρ : ℝ} (hρ : 0 ≤ ρ) (w : ℕ) (hw : w ∈ ({0, 1} : Finset ℕ))
    (hd : ρ / 4 < finiteSignal w) (hw0 : w ≠ 0) :
    (#{σ ∈ (univ : Finset Unit) | finiteHits σ w} : ℝ) ≤ 0 * 0 * #(univ : Finset Unit) := by
  rcases mem_insert.mp hw with hw | hw
  · exact (hw0 hw).elim
  · have hw1 := mem_singleton.mp hw
    subst w
    norm_num [finiteSignal] at hd
    linarith

-- A nonempty heavy event over a finite subset of an infinite endpoint type; only zero is heavy.
example : heavyCountEvent finiteHits {0, 1} finiteSignal (1 / 2) 2 () ∧
    ¬ heavyCountEvent finiteHits {0, 1} finiteSignal (1 / 2) 3 () := by
  norm_num [heavyCountEvent, finiteHits, finiteSignal, filter_insert, filter_singleton]

-- Requiring the pair bound at the light endpoint one would rule this instance out.
example : ¬ (#{σ ∈ (univ : Finset Unit) | finiteHits σ 1} : ℝ) ≤
    0 * 0 * #(univ : Finset Unit) := by
  norm_num [finiteHits]

-- The original stronger bound has RHS one, while replacing ρ by one would give RHS two.
open scoped Classical in
example : (#{σ ∈ (univ : Finset Unit) |
      heavyCountEvent finiteHits {0, 1} finiteSignal (1 / 2) 2 σ} : ℝ) * 2 * (1 / 2) ≤ 1 := by
  have h := card_filter_heavyCountEvent_mul_le finiteHits univ {0, 1} 0
    (d := finiteSignal) (a := 0) (ρ := 1 / 2) (c := 0) (M := 0)
    (by norm_num) (by norm_num) (by norm_num)
    (fun w _ => by unfold finiteSignal; split_ifs <;> norm_num) (by simp)
    (by
      intro w hw hdw hwy
      convert zero_scale_pair (ρ := 1 / 2) (by norm_num) w hw hdw hwy using 1
      congr 2
      ext σ
      simp) 2
  norm_num at h ⊢
  exact h

open scoped Classical in
example : (#{σ ∈ (univ : Finset Unit) |
      heavyCountEvent finiteHits {0, 1} finiteSignal 1 2 σ} : ℝ) / #(univ : Finset Unit) ≤ 1 := by
  have h := card_filter_heavyCountEvent_div_card_le finiteHits univ {0, 1} 0
    (d := finiteSignal) (a := 0) (ρ := 1) (c := 0) (M := 0)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (fun w _ => by unfold finiteSignal; split_ifs <;> norm_num) (by simp)
    (by
      intro w hw hdw hwy
      convert zero_scale_pair (ρ := 1) (by norm_num) w hw hdw hwy using 1
      congr 2
      ext σ
      simp) (n := 2) (by decide)
  norm_num at h ⊢
  exact h

end ComplexityTests.CompressionHeavyCount
