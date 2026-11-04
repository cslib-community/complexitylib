/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.UnroutedBinDecoder
import Complexity.Foundations.Data.Finset.KthLargest.Stability

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

-- The accuracy kernel is exercised on an actual finite compression iterate, including
-- arbitrary positive horizons and floors. The initial row is supplied here; this test
-- does not claim that the public evaluator's zero-start history already satisfies it.
open Finset Cslib.RowCompression Matrix.FourthRootHierarchyParams.NormalizedRow in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {scale : ℝ}
    (hs : 0 < scale) (hsmall : scale ≤ (16 : ℝ) / 10000) (hmarg : scale ≤ HP.η)
    (m : ℕ) (hm : 0 < m) (n : ℕ → ℕ) (hn : ∀ i < m, HP.K ≤ n i)
    (floors : ℕ → ℝ) (hf : ∀ i < m, floors i ≤ scale) (bin : ℕ) :
    let ζ := scale / 4
    let truth : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else ζ
    let a := iterate {()} n (fun _ => HP.K) floors (fun _ => 0) ⟨0, truth⟩ m
    output (numerator bin) HP.ρ ζ (a.row () 0) (a.row () 1)
      (firstRank {()} HP.K a.defaultValue a.row) = numerator bin 1 := by
  intro ζ truth a
  obtain ⟨C, _, hc⟩ := DenseBinRecipe.exists_polynomialUnrouted_iterate_bound HP
    (cap := 2) (by norm_num) (show 0 < ζ by dsimp only [ζ]; positivity)
  have herr (i : ℕ) : uncompressedRow (fun _ => 0) truth i = truth := by
    induction i with
    | zero => exact uncompressedRow_zero
    | succ i ih =>
      funext y ν
      simp only [uncompressedRow_succ, ih, Pi.zero_apply, add_zero]
  have hb := hc scales scales_pos scales_step bin {()} n floors (fun _ => 0)
    truth truth scale m hs
    (by rw [max_eq_right (by norm_num : (2 : ℝ) ≤ 16)]; exact hsmall) hmarg hm hn hf
    (fun _ _ => by norm_num [truth])
    (fun _ _ => by
      simp only [truth, Fin.isValue, one_ne_zero, ↓reduceIte]
      rw [abs_of_pos (show 0 < ζ by dsimp only [ζ]; positivity)]
      dsimp only [ζ]
      linarith)
    (fun _ => 0) (fun _ _ => le_rfl)
    (fun i _ _ _ => by rw [herr i]; exact le_of_eq (clippedError_self _ _ _ rfl rfl))
    () (by simp)
  have hzero : prefixErrorBudget (fun _ => 0) m = 0 := by simp [prefixErrorBudget]
  rw [hzero, mul_zero, abs_nonpos_iff] at hb
  have hrank : firstRank {()} HP.K 0 truth = 0 := by
    simp only [firstRank]
    rw [kthLargest_eq_zero_of_card_lt (by simpa using rank_gt_one HP)]
    norm_num
  unfold stateRootError at hb
  rw [hrank] at hb
  have htruth : output (numerator bin) HP.ρ ζ (truth () 0) (truth () 1) 0 =
      numerator bin 1 := by
    simp only [truth, Fin.isValue, ↓reduceIte, one_ne_zero, output,
      HP.ρ_one 0 HP.η_pos.le, mul_one, clip, div_self (ne_of_gt (show 0 < ζ by
        dsimp only [ζ]; positivity))]
    norm_num
  have hroot : output (numerator bin) HP.ρ ζ (a.row () 0) (a.row () 1)
      (firstRank {()} HP.K a.defaultValue a.row) ^ (4⁻¹ : ℝ) =
      numerator bin 1 ^ (4⁻¹ : ℝ) := by
    change _ - _ = 0 at hb
    exact (sub_eq_zero.mp hb).trans (congrArg (fun z : ℝ => z ^ (4⁻¹ : ℝ)) htruth)
  have hc0 := (DenseBinRecipe.polynomialUnrouted_numerator_laws HP scales_pos scales_step
    (by norm_num : (0 : ℝ) ≤ 2) bin 1).1.1
  have hout : 0 ≤ output (numerator bin) HP.ρ ζ (a.row () 0) (a.row () 1)
      (firstRank {()} HP.K a.defaultValue a.row) := by
    exact (output_mem_Icc _ _ (by norm_num : (0 : ℝ) ≤ 16)
      (fun d => by
        have h := (DenseBinRecipe.polynomialUnrouted_numerator_laws HP
          scales_pos scales_step (by norm_num : (0 : ℝ) ≤ 2) bin d).1
        rw [max_eq_right (by norm_num : (2 : ℝ) ≤ 16)] at h
        exact h)
      (fun q => ⟨HP.ρ_nonneg q, HP.ρ_le_one q⟩) _ _ _ _).1
  exact (Real.rpow_left_inj hout hc0 (show (4⁻¹ : ℝ) ≠ 0 by norm_num)).mp hroot
