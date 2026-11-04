/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.UnroutedBinRegularity

/-! Nonzero actual top/fine numerators on the ratio-16 grid with valid preparation.
The existing constant-one compressed fixture remains a construction-only fixture. -/

public section
noncomputable section
open Cslib Matrix Matrix.FourthRootHierarchyParams

private def scales (i : ℕ) : ℝ := (1 / 16) ^ i

private theorem scales_pos (i : ℕ) : 0 < scales i := by
  unfold scales
  positivity

private theorem scales_step (i : ℕ) : scales i = 16 * scales (i + 1) := by
  simp only [scales, pow_succ]
  ring

private def numerator (i : ℕ) (d : ℝ) : ℝ :=
  boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) scales 2 i (fun _ => 1) d

-- Positive top values, at the cap and beyond it, retain the actual clipped multiplier.
example : numerator 0 1 = 1 ∧ numerator 0 2 = 2 ∧ numerator 0 3 = 2 := by
  norm_num [numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight, scales,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

-- Both transition boundaries and the interior fine-bin value depend on the ratio 16.
example : numerator 1 1 = 1 ∧ numerator 1 8 = 8 ∧
    numerator 1 12 = 6 ∧ numerator 1 16 = 0 := by
  norm_num [numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight, scales,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

-- Negative and light estimates are zero for every bin; fine support closes at its own ratio.
example (i : ℕ) : numerator i (-1) = 0 ∧ numerator i 0 = 0 ∧ numerator i (1 / 2) = 0 := by
  have hanti : Antitone scales := antitone_nat_of_succ_le fun j => by
    have hp := scales_pos (j + 1)
    rw [scales_step j]
    linarith
  have hz (d : ℝ) (hd : d ≤ 1 / 2) : numerator i d = 0 :=
    boundedRoutedBinCutoff_eq_zero (by norm_num)
      (fun _ h => polynomialSwitch4_of_le (by norm_num) h) scales_pos hanti hd i (fun _ => 1)
  exact ⟨hz _ (by norm_num), hz _ (by norm_num), hz _ le_rfl⟩

example (i : ℕ) {d : ℝ} (hd : 16 ≤ d) : numerator (i + 1) d = 0 :=
  boundedRoutedBinCutoff_succ_eq_zero scales_pos (by norm_num) scales_step 2 i hd

-- A zero cap kills the top bin at every signed input.
example (d : ℝ) :
    boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) scales 0 0 (fun _ => 1) d = 0 := by
  simp [boundedRoutedBinCutoff, routedBinCutoff]

/-- A nonempty hierarchy witness supplies all scalar numerator/preparation contracts
simultaneously, with genuinely nonzero top and fine bins and `h 0 = 0`, `h 1 = 1`.
No compressed-parent accuracy or global invariant is part of this witness. -/
theorem valid_unrouted_recipe :
    ∃ HP : FourthRootHierarchyParams 16 1 16 32 8,
      let R := DenseBinRecipe.polynomialUnrouted HP (fun i => (1 / 16 : ℝ) ^ i) 2
      let k := fun i => boundedRoutedBinCutoff R.χ R.scales R.cap i R.route
      k 0 1 = 1 ∧ k 1 8 = 8 ∧
      (∀ i d, k i d ∈ Set.Icc 0 16) ∧
      (∀ i d, d ≤ 1 / 2 → k i d = 0) ∧
      R.h 0 = 0 ∧ R.h 1 = 1 ∧
      (∀ d, R.h d ∈ Set.Icc 0 1) ∧
      (∀ d, d ≤ HP.θ / 2 → R.h d = 0) ∧
      (∀ i d, k i d ≠ 0 → R.h d = 1) ∧
      (∃ L : ℝ, 0 ≤ L ∧ ∀ i v w,
        |k i v ^ (4⁻¹ : ℝ) - k i w ^ (4⁻¹ : ℝ)| ≤ L * |v - w|) ∧
      (∃ L : ℝ, 0 ≤ L ∧ ∀ v w,
        |R.h v ^ (4⁻¹ : ℝ) - R.h w ^ (4⁻¹ : ℝ)| ≤ L * |v - w|) := by
  obtain ⟨HP⟩ := FourthRootHierarchyParams.nonempty (Cπ := 16) (Cpair := 32) (Cvar := 8)
    (by norm_num : (0 : ℝ) < 16) (by norm_num : (0 : ℝ) < 1)
  refine ⟨HP, ?_⟩
  dsimp only
  have htop : numerator 0 1 = 1 := by
    norm_num [numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight, scales,
      polynomialSwitch4, polynomialTransition4, transitionPolynomial4]
  have hfine : numerator 1 8 = 8 := by
    norm_num [numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight, scales,
      polynomialSwitch4, polynomialTransition4, transitionPolynomial4]
  have hanti : Antitone scales := antitone_nat_of_succ_le fun j => by
    have hp := scales_pos (j + 1)
    rw [scales_step j]
    linarith
  have hχ (v : ℝ) (hv : v ≤ 1 / 2) : polynomialSwitch4 (1 / 2) 1 v = 0 :=
    polynomialSwitch4_of_le (by norm_num) hv
  have hlaws := DenseBinRecipe.polynomialUnrouted_numerator_laws HP scales_pos scales_step
    (by norm_num : (0 : ℝ) ≤ 2)
  have hprep := routedBin_prep_laws HP
  refine ⟨htop, hfine, ?_, ?_, ?_, ?_, hprep.1, hprep.2.1, ?_, ?_, hprep.2.2.2⟩
  · intro i d
    change numerator i d ∈ Set.Icc 0 16
    have h := (hlaws i d).1
    change numerator i d ∈ Set.Icc 0 (max 2 16) at h
    rw [max_eq_right (by norm_num : (2 : ℝ) ≤ 16)] at h
    exact h
  · exact fun i d hd => (hlaws i d).2 hd
  · exact polynomialPrepCutoff4_eq_zero HP.θ_pos
      (div_nonneg HP.θ_pos.le (by norm_num))
  · exact routedBin_prep_eq_one HP (cap := 2) (by norm_num) hχ scales_pos hanti 0 (fun _ => 1)
      (by change numerator 0 1 ≠ 0; rw [htop]; norm_num)
  · exact fun i d hd => routedBin_prep_eq_one HP (cap := 2) (by norm_num) hχ scales_pos hanti i
      (fun _ => 1) hd
  · obtain ⟨L, hL, hroot⟩ := exists_boundedRoutedBinCutoff_root_lipschitz
      (cap := 2) (by norm_num : (2 : ℝ) ≤ 16)
    exact ⟨L, hL, hroot scales scales_pos scales_step⟩
