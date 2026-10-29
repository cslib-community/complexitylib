/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import Complexity.Computability.Circuit.Fusion.Sampling
import Mathlib.Tactic.FinCases

/-!
# Nonvacuous clients of the Fusion sampling barrier

The negative inputs of two-bit conjunction carry the nonempty-set semifilter. It accepts the
matching literals of the positive input. A complementary pair covers it, and the proved
sampling and fixed-distribution theorems apply to its probability-one point mass.
-/

namespace ComplexityTests.FusionSampling

open Cslib.Circuits.Fusion
open scoped BigOperators

private abbrev target : Set (Fin 2 → Bool) := {x | x 0 = true ∧ x 1 = true}
private abbrev point : target := ⟨![true, true], by decide⟩

private instance : Nonempty ↥(targetᶜ) := ⟨⟨![false, false], by decide⟩⟩

private def nonemptySets : Semifilter ↥(targetᶜ) where
  toFun s := s.Nonempty
  monotone' _ _ h hs := hs.mono h
  map_top' := by simp
  map_bot' := by simp

private theorem matching (i : Fin 2) :
    nonemptySets {x | x.val i = point.val i} := by
  fin_cases i
  · exact ⟨⟨![true, false], by decide⟩, rfl⟩
  · exact ⟨⟨![false, true], by decide⟩, rfl⟩

example : ¬ nonemptySets.PreservesPair (booleanPairSample target none false (fun x => x 0)) := by
  intro h
  have hbad := h ⟨⟨![true, false], by decide⟩, rfl⟩
    ⟨⟨![false, true], by decide⟩, Bool.false_ne_true⟩
  obtain ⟨x, hx, hn⟩ := hbad
  exact hn hx

open Classical in
example :
    ((1 : ℝ) / 24 ≤ 𝔼 level : Option (Fin 2), 𝔼 b : Bool,
      𝔼 h : (Fin 2 → Bool) → Bool,
        if ¬ nonemptySets.PreservesPair (booleanPairSample target level b h) then 1 else 0) ∧
    ∃ p : Set ↥(targetᶜ) × Set ↥(targetᶜ),
      (1 : ℝ) / 24 ≤ if ¬ nonemptySets.PreservesPair p then 1 else 0 := by
  refine ⟨?_, ?_⟩
  · simpa [show (8 : ℝ) * 2 + 8 = 24 by norm_num] using
      le_booleanPairSample_expect nonemptySets point matching
  · simpa [show (8 : ℝ) * 2 + 8 = 24 by norm_num] using
      exists_pair_weight_ge (fun _ : Unit => nonemptySets) (fun _ => point)
      (fun _ => matching) (fun _ => 1) (fun _ => zero_le_one)

open Classical in
example : ¬ ∀ p : Set ↥(targetᶜ) × Set ↥(targetᶜ),
    (if ¬ nonemptySets.PreservesPair p then (1 : ℝ) else 0) ≤ 1 / 25 := by
  intro hd
  have h := fixedDistribution_counting_bound (fun _ : Unit => nonemptySets)
    (fun _ => point) (fun _ => matching) (fun _ => 1) (fun _ => zero_le_one)
    (by simp) (d := 1 / 25) (by simpa using hd)
  norm_num at h

end ComplexityTests.FusionSampling
