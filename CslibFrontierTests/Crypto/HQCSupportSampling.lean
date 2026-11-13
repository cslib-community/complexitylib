/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontier.Crypto.Primitives.HQC.SupportDensity
import Mathlib.Data.Fin.VecNotation

/-! Source-array checks, biased finite-word laws, and HQC parameter side conditions. -/

namespace CslibFrontierTests.HQCSupportSampling

open Cslib Cslib.Crypto.HQC Cslib.Probability Finset
open scoped ENNReal

-- The descending pass uses the corrected suffix. The duplicate at index one becomes one;
-- index zero then sees a collision with the retained four and becomes zero.
example : scanSupport 0 ![4, 4, 4] = ![0, 1, 4] := by decide
example : supportFromWords 3 5 ![7, 7, 7] = {0, 1, 4} := by decide
example : supportFromWords 3 5 ![6, 4] = {0, 3} := by decide

-- The source's scan and the set-level resolver agree even without range or freshness premises.
example : scanSupport 0 ![0, 0, 0] = ![0, 1, 0] := by decide
example : (resolveSupport 0 ![0, 0, 0]).card = 2 := by decide
example : (List.ofFn (scanSupport 0 ![0, 0, 0])).toFinset =
    resolveSupport 0 ![0, 0, 0] := toFinset_scanSupport _

example (width n : ℕ) : sampleSupport2 width n 0 = pure ∅ := sampleSupport2_zero width n
example (words : Fin 5 → Fin 8) : supportFromWords 3 5 words = range 5 :=
  supportFromWords_full 3 5 words

-- This fibre distinguishes multiply-high from reduction modulo five.
example : Nat.card {u : Fin 8 // u.val * 5 / 8 = 2} = 1 := by
  rw [Nat.card_mul_div_fiber (M := 8) (d := 5) (by decide) (by decide) ⟨2, by decide⟩]
  decide
example : Fintype.card {u : Fin 8 // u.val % 5 = 2} = 2 := by decide

-- Of the 64 equiprobable two-word arrays, four give {2,4}; the ideal law gives mass 1/10.
private theorem toy_fiber :
    Nat.card {words : Fin 2 → Fin 8 // supportFromWords 3 5 words = {2, 4}} = 4 := by
  rw [Nat.card_eq_fintype_card]
  decide

example : (ProbComp.eval (sampleSupport2 3 5 2) {2, 4}).toReal = 1 / 16 := by
  rw [eval_sampleSupport2, PMF.uniformOfFintype_map_apply]
  change ((Nat.card {words : Fin 2 → Fin 8 // supportFromWords 3 5 words = {2, 4}} : ℝ≥0∞) /
    Fintype.card (Fin 2 → Fin 8)).toReal = _
  rw [toy_fiber]
  norm_num [ENNReal.toReal_div]

example : (ProbComp.eval (sampleSupportFrom (idealCandidate 5) 0 2) {2, 4}).toReal = 1 / 10 := by
  rw [eval_idealSupport (by decide)]
  norm_num [PMF.uniformOfFinset_apply, Finset.mem_powersetCard, Finset.card_powersetCard,
    Finset.subset_iff, ENNReal.toReal_inv, Nat.choose]

example : (supportLowerDensity 3 5 0 2).toReal = 5 / 8 ∧
    (supportUpperDensity 3 5 0 2).toReal = 15 / 8 := by
  rw [supportLowerDensity_toReal, supportUpperDensity_toReal (by decide)]
  norm_num [Fin.prod_univ_succ]

-- Empty and full supports instantiate the abstract bounds without a positivity assumption on w.
example : supportLowerDensity 0 0 0 0 = 1 ∧ supportUpperDensity 0 0 0 0 = 1 := by
  simp [supportLowerDensity, supportUpperDensity]

example (S : Finset ℕ) :
    supportLowerDensity 3 5 0 2 *
        PMF.uniformOfFinset ((range 5).powersetCard 2) (by decide) S ≤
      ProbComp.eval (sampleSupport2 3 5 2) S :=
  (sampleSupport2_density_bounds (by decide) S).1

-- The nonnegative payoff and event interfaces apply to a meaningful nonconstant payoff/event.
example : ProbComp.expect (sampleSupport2 3 5 2) (fun S => if 4 ∈ S then 3 else 0) ≤
    supportUpperDensity 3 5 0 2 *
      ProbComp.expect (sampleSupportFrom (idealCandidate 5) 0 2)
        (fun S => if 4 ∈ S then 3 else 0) :=
  (sampleSupport2_expect_bounds (by decide) _).2

example : Pr[(fun S => decide (4 ∈ S)) <$> sampleSupport2 3 5 2] ≤
    (supportUpperDensity 3 5 0 2).toReal *
      Pr[(fun S => decide (4 ∈ S)) <$> sampleSupportFrom (idealCandidate 5) 0 2] :=
  (sampleSupport2_event_bounds (by decide) {S | 4 ∈ S}).2

-- A constant negative payoff refutes the unqualified real-valued formulation printed in Lemma 6.5.
example : ¬ ((-1 : ℝ) ≤ (15 / 8) * (-1)) := by norm_num

-- HQC v5.1 Tables 8 and 17: both secret and encryption weights fit the support, every index fits
-- 16 bits, and every shrinking interval is at most the 32-bit word range.
example : 67 ≤ 17669 ∧ 76 ≤ 17669 ∧ 17669 < 2 ^ 16 ∧ 17669 ≤ 2 ^ 32 := by decide
example : 101 ≤ 35851 ∧ 114 ≤ 35851 ∧ 35851 < 2 ^ 16 ∧ 35851 ≤ 2 ^ 32 := by decide
example : 132 ≤ 57637 ∧ 150 ≤ 57637 ∧ 57637 < 2 ^ 16 ∧ 57637 ≤ 2 ^ 32 := by decide

example {S : Finset ℕ} (hS : S ∈ (ProbComp.eval (sampleSupport2 32 17669 76)).support) :
    S.card = 76 :=
  (mem_powersetCard.mp (sampleSupport2_mem_powersetCard (by decide) hS)).2

end CslibFrontierTests.HQCSupportSampling
