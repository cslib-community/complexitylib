/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

import CslibFrontierTests.BooleanAnalysisExamples
import CslibFrontier.Foundations.BooleanAnalysis.Affinity
import CslibFrontier.Foundations.BooleanAnalysis.LinearityRejection

/-! # BLR rejection and affinity testing on small cubes

Concrete instances of the BLR rejection bounds and of the affinity tests [O'Donnell, Exercises
1.28 and 1.29][ODonnell2014]. The indicator of the all-ones point on three bits is at relative
distance `1/8` from the zero parity and is rejected with probability `9/32`, which lies strictly
between the cubic lower bound `15/64` and the linear term `3/8`. The conjunction of two bits
attains the coefficient bound of Exercise 1.28(a), passes the affinity test on `40` of the `64`
triples, and is not affine. A negated parity passes both affinity tests with probability one and
the BLR test with probability zero, so the affinity tests accept functions the BLR test rejects.
-/

namespace CslibFrontierTests.BooleanAnalysisLinearityTesting

open Cslib Cslib.BitString Finset CslibFrontierTests.BooleanAnalysisExamples

/-! ### The BLR rejection probability -/

/-- The indicator of the all-ones point on three bits. -/
def point₃ (x : Fin 3 → Bool) : Bool :=
  decide (x = fun _ => true)

/-- The BLR test accepts the indicator of a nonzero point on three bits with probability
`1 - 3/8 + 6/64 = 23/32`. -/
theorem blrAcceptance_point₃ : blrAcceptance point₃ = 23 / 32 := by
  have ha : (fun _ => true : Fin 3 → Bool) ≠ 0 := fun h => by simpa using congr_fun h 0
  change blrAcceptance (fun x => decide (x = fun _ => true)) = _
  rw [blrAcceptance_decide_eq ha, Fintype.card_fin]
  norm_num

-- On two bits the indicator of the all-ones point is the conjunction, and the closed form
-- agrees with the brute-force acceptance probability `5 / 8`.
example : blrAcceptance (fun x : Fin 2 → Bool => decide (x = fun _ => true)) = 5 / 8 ∧
    (fun x : Fin 2 → Bool => decide (x = fun _ => true)) = and₂ := by
  refine ⟨?_, by decide⟩
  have ha : (fun _ => true : Fin 2 → Bool) ≠ 0 := fun h => by simpa using congr_fun h 0
  rw [blrAcceptance_decide_eq ha, Fintype.card_fin]
  norm_num

-- The indicator is at relative distance `δ = 1/8` from its nearest parity, the zero parity. Its
-- rejection probability `9/32` is at least `3δ - 10δ² + 8δ³ = 15/64` (Exercise 1.28(b)) and
-- strictly below `3δ = 3/8`, so the quadratic correction is needed at this distance.
example : (∀ T, hammingDist point₃ (parityOn ∅) ≤ hammingDist point₃ (parityOn T)) ∧
    (hammingDist point₃ (parityOn ∅) : ℝ) / 2 ^ Fintype.card (Fin 3) = 1 / 8 ∧
    blrAcceptance point₃ ≤ 1 - 3 * (1 / 8) + 10 * (1 / 8) ^ 2 - 8 * (1 / 8) ^ 3 ∧
    (15 / 64 : ℝ) < 1 - blrAcceptance point₃ ∧ 1 - blrAcceptance point₃ < 3 * (1 / 8) := by
  have hd : hammingDist point₃ (parityOn ∅) = 1 := hammingDist_decide_eq_parityOn_empty _
  have hδ : (hammingDist point₃ (parityOn ∅) : ℝ) / 2 ^ Fintype.card (Fin 3) = 1 / 8 := by
    rw [hd, Fintype.card_fin]
    norm_num
  refine ⟨fun T => ?_, hδ, blrAcceptance_le_of_hammingDist_parityOn point₃ hδ, ?_, ?_⟩
  · rw [hd]
    exact one_le_hammingDist_decide_eq_parityOn _ (by simp) T
  · rw [blrAcceptance_point₃]
    norm_num
  · rw [blrAcceptance_point₃]
    norm_num

-- Exercise 1.28(a) is attained by the conjunction: it is at relative distance `1/4` from the
-- zero parity, and its coefficient on `{0}` has absolute value exactly `2 · 1/4`.
example : fourierCoeff (fun x => signVal (and₂ x)) {0} = 1 / 2 ∧
    2 * ((hammingDist and₂ (parityOn ∅) : ℝ) / 2 ^ Fintype.card (Fin 2)) = 1 / 2 := by
  refine ⟨?_, ?_⟩
  · simp only [fourierCoeff, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
    norm_num [chi, and₂]
  · have hd : hammingDist and₂ (parityOn ∅) = 1 := by decide
    rw [hd, Fintype.card_fin]
    norm_num

/-! ### Affinity testing -/

/-- The affinity test accepts the conjunction of two bits on `40` of the `64` triples. -/
theorem affinityAcceptance_and₂ : affinityAcceptance and₂ = 5 / 8 := by
  simp only [affinityAcceptance, Fin.expect_univ_cons, Fintype.expect_bool, Fintype.expect_unique]
  norm_num [and₂, Bool.add_eq_xor]

-- The conjunction is not affine: it fails the three-point identity at the two unit vectors and
-- the zero string. Through the Fourier formula, its fourth powers of coefficients sum to `1/4`.
example : (¬ ∃ b S, and₂ = fun x => b ^^ parityOn S x) ∧
    ∑ S, fourierCoeff (fun x => signVal (and₂ x)) S ^ 4 = 1 / 4 := by
  refine ⟨fun h => ?_, ?_⟩
  · have h₁ := exists_eq_xor_parityOn_iff.1 h ![true, false] ![false, true] 0
    revert h₁
    decide
  · have h := affinityAcceptance_eq_sum_fourierCoeff_pow_four and₂
    rw [affinityAcceptance_and₂] at h
    linarith

-- Soundness at `ε = 3/8` gives an affine function at Hamming distance at most one from the
-- conjunction, and the zero function attains that bound.
example : (∃ b S, hammingDist and₂ (fun x => b ^^ parityOn S x) ≤ 1) ∧
    hammingDist and₂ (fun x => false ^^ parityOn ∅ x) = 1 := by
  refine ⟨?_, by decide⟩
  obtain ⟨b, S, hS⟩ := exists_hammingDist_xor_parityOn_le_of_le_affinityAcceptance
    (f := and₂) (ε := 3 / 8) (by rw [affinityAcceptance_and₂]; norm_num)
  refine ⟨b, S, ?_⟩
  have h : (hammingDist and₂ (fun x => b ^^ parityOn S x) : ℝ) < 2 := by
    rw [Fintype.card_fin] at hS
    linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast h)

-- The anchored test on the conjunction is the BLR test on the conjunction, since `and₂ 0` is
-- `false`, so it accepts with probability `5 / 8` as well.
example : anchoredAffinityAcceptance and₂ = 5 / 8 := by
  have h0 : and₂ 0 = false := by decide
  rw [anchoredAffinityAcceptance_eq_blrAcceptance, h0]
  simp only [Bool.xor_false]
  exact blrAcceptance_and₂

/-! ### Affine functions that are not linear -/

/-- The negation of the parity of two bits. -/
def negParity₂ (x : Fin 2 → Bool) : Bool :=
  true ^^ parityOn {0, 1} x

-- The negated parity differs from the parity everywhere, so Exercise 1.28(b) at `δ = 1` bounds
-- its BLR acceptance by `0`; the BLR test always rejects it, while both affinity tests always
-- accept it.
example : blrAcceptance negParity₂ = 0 ∧ affinityAcceptance negParity₂ = 1 ∧
    anchoredAffinityAcceptance negParity₂ = 1 := by
  refine ⟨?_, affinityAcceptance_xor_parityOn true {0, 1},
    anchoredAffinityAcceptance_xor_parityOn true {0, 1}⟩
  have hd : hammingDist negParity₂ (parityOn {0, 1}) = 4 := by decide
  have hδ : (hammingDist negParity₂ (parityOn {0, 1}) : ℝ) / 2 ^ Fintype.card (Fin 2) = 1 := by
    rw [hd, Fintype.card_fin]
    norm_num
  have hle := blrAcceptance_le_of_hammingDist_parityOn negParity₂ hδ
  have hnonneg : 0 ≤ blrAcceptance negParity₂ :=
    expect_nonneg fun x _ => expect_nonneg fun y _ => by split_ifs <;> norm_num
  norm_num at hle
  linarith

end CslibFrontierTests.BooleanAnalysisLinearityTesting
