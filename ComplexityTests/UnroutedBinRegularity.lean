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

-- This uses the real polynomial preparation, starts at zero and charges no initial error.
-- Choosing D = 1 gives a nonzero top/fine truth; arbitrary D also checks cap/light edges.
open Finset Cslib.RowCompression Matrix.FourthRootHierarchyParams.NormalizedRow in
private theorem polynomial_bin_zero_start (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ℝ) (hD : 0 ≤ D) (bin : ℕ) :
    let scale := HP.η / 2
    let ζ := scale / 4
    let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then D else ζ * polynomialPrepCutoff4 HP.θ D
    let a := iterate univ (fun _ => HP.K) (fun _ => HP.K) (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ 1
    stateRootError (output (numerator bin) HP.ρ ζ) univ HP.K a ⟨0, w⟩ () = 0 := by
  classical
  let scale := HP.η / 2
  let ζ := scale / 4
  let w : Unit → Fin 2 → ℝ := fun _ ν => if ν = 0 then D else ζ * polynomialPrepCutoff4 HP.θ D
  have hs : 0 < scale := half_pos HP.η_pos
  have hζ : 0 < ζ := div_pos hs (by norm_num)
  have hmargin : scale ≤ HP.η := by dsimp only [scale]; linarith [HP.η_pos]
  have h16 : scale ≤ max (2 : ℝ) 16 := by
    have hθ := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at hθ
    dsimp only [scale]
    have hm := threshold_margin HP
    have ht := HP.η_lt_η₂
    have hp := HP.η_pos
    rw [max_eq_right (by norm_num : (2 : ℝ) ≤ 16)]
    linarith
  obtain ⟨Cf, _, hfinal⟩ := DenseBinRecipe.exists_polynomialUnrouted_sharp_noOverflow HP
    (cap := 2) (by norm_num) hζ
  obtain ⟨Cp, _, hbound⟩ := hfinal scale hs hmargin h16
  have singleton_rank (d : Unit → ℝ) : kthLargest HP.K univ d = 0 :=
    kthLargest_eq_zero_of_card_lt (by simpa using rank_gt_one HP) d
  have hno : ∀ i < 1, stepThreshold univ (fun _ => HP.K) (fun _ => HP.K)
      (dyadicFloor scale 1) (fun _ => w) (⟨0, 0⟩ : State Unit) i ≤ dyadicFloor scale 1 i := by
    intro i hi
    have hi0 : i = 0 := by omega
    subst i
    simp only [stepThreshold, inputRow, iterate_zero, zero_add, threshold, singleton_rank]
    rw [max_eq_left (dyadicFloor_nonneg hs.le 1 0),
      max_eq_right (dyadicFloor_nonneg hs.le 1 0)]
  have he (i : ℕ) (_hi : i < 1) (y : Unit) (_hy : y ∈ (univ : Finset Unit))
      (_hd : scale / 2 ≤ w y 0) :
      clippedError (w y 0) (w y 1) (uncompressedRow (fun _ => w) 0 (i+1) y) ≤ 0 := by
    have hi0 : i = 0 := by omega
    subst i
    have hw : uncompressedRow (fun _ => w) 0 1 y = w y := by
      funext ν
      simp only [uncompressedRow, sum_range_one, Pi.zero_apply, zero_add]
    rw [hw, clippedError_self (w y 0) (w y 1) (w y) rfl rfl]
  have hf : ∀ y ∈ (univ : Finset Unit),
      clippedError (w y 0) (w y 1) (uncompressedRow (fun _ => w) 0 1 y) ≤ 0 := by
    intro y hy
    have hw : uncompressedRow (fun _ => w) 0 1 y = w y := by
      funext ν
      simp only [uncompressedRow, sum_range_one, Pi.zero_apply, zero_add]
    rw [hw, clippedError_self (w y 0) (w y 1) (w y) rfl rfl]
  have hb := hbound scales scales_pos scales_step bin univ (fun _ => HP.K) (fun _ => w) w 0 1 hno
    (fun _ _ => hD) (fun _ => 0) (by intros; exact le_rfl) he 0 le_rfl hf () (mem_univ _)
  simp only [mul_zero, sum_const_zero, add_zero] at hb
  exact abs_nonpos_iff.mp hb

-- Prefix zero is inaccurate for the positive truth used by the zero-start regression.
-- The sharp theorem nevertheless concludes zero final discrepancy after the exact increment.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    Cslib.RowCompression.clippedError 1 (HP.η / 8 * polynomialPrepCutoff4 HP.θ 1) 0 > 0 := by
  unfold Cslib.RowCompression.clippedError
  norm_num

example (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    let scale := HP.η / 2
    let ζ := scale / 4
    let w : Unit → Fin 2 → ℝ := fun _ ν =>
      if ν = 0 then 1 else ζ * polynomialPrepCutoff4 HP.θ 1
    let a := Cslib.RowCompression.iterate Finset.univ (fun _ => HP.K) (fun _ => HP.K)
      (Cslib.RowCompression.dyadicFloor scale 1) (fun _ => w) ⟨0, 0⟩ 1
    Cslib.RowCompression.stateRootError
      (FourthRootHierarchyParams.NormalizedRow.output (numerator 0) HP.ρ ζ)
      Finset.univ HP.K a ⟨0, w⟩ () = 0 :=
  polynomial_bin_zero_start HP 1 (by norm_num) 0

-- The polynomial preparation makes the true decoder output positive, rather than
-- concealing a zero target behind the exact-discrepancy assertion above.
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {ζ : ℝ} (hζ : 0 < ζ) :
    FourthRootHierarchyParams.NormalizedRow.output (numerator 0) HP.ρ ζ 1
      (ζ * polynomialPrepCutoff4 HP.θ 1) 0 = 1 := by
  have hθ := HP.θ_lt_θ₂.trans HP.θ₂_lt
  norm_num at hθ
  have hp : polynomialPrepCutoff4 HP.θ 1 = 1 :=
    polynomialPrepCutoff4_eq_one HP.θ_pos (by linarith)
  simp only [FourthRootHierarchyParams.NormalizedRow.output, hp, mul_one,
    HP.ρ_one 0 HP.η_pos.le, FourthRootHierarchyParams.NormalizedRow.clip,
    div_self hζ.ne', min_self]
  norm_num [numerator, boundedRoutedBinCutoff, routedBinCutoff, binWeight, scales,
    polynomialSwitch4, polynomialTransition4, transitionPolynomial4]

-- A genuine first overflow at the initial group exercises the preloaded tail boundary.
-- There are K+1 identical entries and capacity K, so the size rank exceeds the tiny floor.
open Finset Cslib.RowCompression Matrix.FourthRootHierarchyParams.NormalizedRow in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {scale : ℝ}
    (hs : 0 < scale) (hscale : scale ≤ (16 : ℝ) / 10000) (bin : ℕ) :
    let ζ := scale / 4
    let w : Fin (HP.K + 1) → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else 0
    let a := iterate univ (fun _ => HP.K) (fun _ => HP.K) (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ 1
    let c := stationaryContinuation univ (fun _ => HP.K) HP.K (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ w 0 1
    IsFirstOverflow univ (fun _ => HP.K) (fun _ => HP.K) (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ 0 ∧
      stateRootError (output (numerator bin) HP.ρ ζ) univ HP.K a c 0 = 0 := by
  classical
  intro ζ w a c
  have hf : dyadicFloor scale 1 0 < 1 :=
    (dyadicFloor_le_scale_div hs.le 1 0).trans_lt (by linarith)
  have hrank : dyadicFloor scale 1 0 < kthLargest HP.K univ (fun y => entrySize (w y)) := by
    apply (lt_kthLargest_iff (rank_pos HP) (dyadicFloor_nonneg hs.le 1 0)).mpr
    have hw (y : Fin (HP.K + 1)) : entrySize (w y) = 1 := by norm_num [entrySize, w]
    simp only [hw, hf, filter_true, card_univ, Fintype.card_fin]
    omega
  have hover : IsFirstOverflow univ (fun _ => HP.K) (fun _ => HP.K)
      (dyadicFloor scale 1) (fun _ => w) (⟨0, 0⟩ : State (Fin (HP.K + 1))) 0 := by
    refine ⟨fun i hi => by omega, ?_⟩
    simp only [stepThreshold, inputRow, iterate_zero, zero_add, threshold]
    exact hrank.trans_le ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨hover, ?_⟩
  obtain ⟨Ct, _, ht⟩ := DenseBinRecipe.exists_polynomialUnrouted_firstOverflow HP
    (cap := 2) (by norm_num) (show 0 < ζ by dsimp only [ζ]; positivity) hs
    (by simpa only [max_eq_right (by norm_num : (2 : ℝ) ≤ 16)] using hscale)
  have he (i : ℕ) (_h0 : 0 ≤ i) (hi : i < 1) (y : Fin (HP.K + 1)) (_hy : y ∈ univ) :
      clippedError (w y 0) (w y 1) (uncompressedRow (fun _ => w) 0 (i + 1) y) ≤ 0 := by
    have hi0 : i = 0 := by omega
    subst i
    have hw : uncompressedRow (fun _ => w) 0 1 y = w y := by
      funext ν
      simp only [uncompressedRow, sum_range_one, Pi.zero_apply, zero_add]
    rw [hw, clippedError_self (w y 0) (w y 1) (w y) rfl rfl]
  have hb := ht scales scales_pos scales_step bin univ (fun _ => HP.K) (fun _ => w)
    0 w scale hs le_rfl 1 0 (by omega) hover
    (fun _ _ => by norm_num [w]) (fun _ _ => by
      change |(0 : ℝ)| ≤ scale / 2
      rw [abs_zero]
      linarith)
    (fun _ _ _ => le_rfl) (fun _ => 0) (fun _ _ _ => le_rfl) he 0 (mem_univ _)
  simp only [mul_zero, sum_const_zero] at hb
  exact abs_nonpos_iff.mp hb

-- The integrated theorem also starts at zero against nonzero polynomial-preparation truth.
-- Both masks and increments live on the same Bool environment; no seed is factored out.
open Finset Cslib.RowCompression Matrix.FourthRootHierarchyParams.NormalizedRow in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {scale : ℝ}
    (hs : 0 < scale) (hsmall : scale ≤ (16 : ℝ) / 10000) (hmargin : scale ≤ HP.η)
    (hscale1 : scale ≤ 1) (bin : ℕ) :
    let ζ := scale / 4
    let w : Unit → Fin 2 → ℝ := fun _ ν =>
      if ν = 0 then 1 else ζ * polynomialPrepCutoff4 HP.θ 1
    let a := iterate univ (fun _ => HP.K) (fun _ => HP.K) (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ 1
    rowNormPow 4 1 1 (fun (_ : Bool) (_ : Unit) => True) (fun _ _ => True)
      (fun _ _ y => stateRootError (output (numerator bin) HP.ρ ζ) univ HP.K a ⟨0, w⟩ y) = 0 := by
  classical
  intro ζ w a
  have hζ : 0 < ζ := by dsimp only [ζ]; positivity
  obtain ⟨C, _, hC⟩ := DenseBinRecipe.exists_polynomialUnrouted_rowNormPow_le HP
    (cap := 2) (by norm_num) hζ hs hmargin
    (by simpa only [max_eq_right (by norm_num : (2 : ℝ) ≤ 16)] using hsmall)
  obtain ⟨A, _, hA⟩ := hC scale hs le_rfl hscale1
  have he (i : ℕ) (hi : i < 1) (y : Unit) :
      clippedError (w y 0) (w y 1) (uncompressedRow (fun _ => w) 0 (i + 1) y) = 0 := by
    have hi0 : i = 0 := by omega
    subst i
    have hw : uncompressedRow (fun _ => w) 0 1 y = w y := by
      funext ν
      simp only [uncompressedRow, sum_range_one, Pi.zero_apply, zero_add]
    rw [hw, clippedError_self (w y 0) (w y 1) (w y) rfl rfl]
  have hb := hA scales scales_pos scales_step bin (Ω := Bool) (V := Unit) 1 1 (by norm_num)
    (fun _ _ => True) (fun _ _ => True) (fun _ => HP.K) 1 (by intros; rfl)
    (fun _ _ _ => w) 0 (fun _ _ => w)
    (by intros; norm_num [w])
    (by
      intros
      change |ζ * polynomialPrepCutoff4 HP.θ 1| ≤ scale / 2
      rw [abs_of_nonneg (mul_nonneg hζ.le (polynomialPrepCutoff4_nonneg _ _))]
      have := mul_le_of_le_one_right hζ.le (polynomialPrepCutoff4_le_one HP.θ 1)
      dsimp only [ζ] at *
      linarith)
    (by
      intro j _ σ x y _ _ hd
      have hf := dyadicFloor_le_scale_div hs.le 1 j
      change 1 ≤ dyadicFloor scale 1 j / 4 at hd
      linarith)
    (fun _ _ _ => 0) (fun _ _ => 0) (by intros; rfl) (by intros; rfl)
    (fun i hi _ _ y _ _ => (he i hi y).le)
    (fun _ _ y _ _ => (he 0 (by decide) y).le)
  dsimp only at hb
  simp only [sum_range_one, Pi.zero_apply, he 0 (by decide), mul_zero, ite_self,
    vertexNormPow, abs_zero, zero_pow (by decide : (4 : ℕ) ≠ 0), sum_const_zero,
    expect_const_zero, add_zero, rowNormPow] at hb
  have hn := rowNormPow_nonneg (s := 4) (N := 1) (u := 1)
    (X := fun (_ : Bool) (_ : Unit) => True) (Y := fun _ _ => True) (by norm_num)
    (fun _ _ y => stateRootError (output (numerator bin) HP.ρ ζ) univ HP.K a ⟨0, w⟩ y)
  unfold numerator at hn ⊢
  exact le_antisymm (by simpa only [rowNormPow, filter_true, a] using hb) hn

-- Tail-to-truth also handles first overflow at group zero, with no preloss term.
-- The previous regression retains its stationary-continuation check separately.
open Finset Cslib.RowCompression Matrix.FourthRootHierarchyParams.NormalizedRow in
example (HP : FourthRootHierarchyParams 16 1 16 32 8) {scale : ℝ}
    (hs : 0 < scale) (hscale : scale ≤ (16 : ℝ) / 10000)
    (hmargin : scale ≤ HP.η) (bin : ℕ) :
    let ζ := scale / 4
    let w : Fin (HP.K + 1) → Fin 2 → ℝ := fun _ ν => if ν = 0 then 1 else 0
    let a := iterate univ (fun _ => HP.K) (fun _ => HP.K) (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ 1
    IsFirstOverflow univ (fun _ => HP.K) (fun _ => HP.K) (dyadicFloor scale 1)
      (fun _ => w) ⟨0, 0⟩ 0 ∧
      stateRootError (output (numerator bin) HP.ρ ζ) univ HP.K a ⟨0, w⟩ 0 = 0 := by
  classical
  intro ζ w a
  have hf : dyadicFloor scale 1 0 < 1 :=
    (dyadicFloor_le_scale_div hs.le 1 0).trans_lt (by linarith)
  have hrank : dyadicFloor scale 1 0 < kthLargest HP.K univ (fun y => entrySize (w y)) := by
    apply (lt_kthLargest_iff (rank_pos HP) (dyadicFloor_nonneg hs.le 1 0)).mpr
    have hw (y : Fin (HP.K + 1)) : entrySize (w y) = 1 := by norm_num [entrySize, w]
    simp only [hw, hf, filter_true, card_univ, Fintype.card_fin]
    omega
  have hover : IsFirstOverflow univ (fun _ => HP.K) (fun _ => HP.K)
      (dyadicFloor scale 1) (fun _ => w) (⟨0, 0⟩ : State (Fin (HP.K + 1))) 0 := by
    refine ⟨fun i hi => by omega, ?_⟩
    simp only [stepThreshold, inputRow, iterate_zero, zero_add, threshold]
    exact hrank.trans_le ((le_max_right _ _).trans (le_max_right _ _))
  refine ⟨hover, ?_⟩
  obtain ⟨Ct, _, htail⟩ := DenseBinRecipe.exists_polynomialUnrouted_sharp_firstOverflow HP
    (cap := 2) (by norm_num) (show 0 < ζ by dsimp only [ζ]; positivity) hs hmargin
    (by simpa only [max_eq_right (by norm_num : (2 : ℝ) ≤ 16)] using hscale)
  obtain ⟨Cp, _, ht⟩ := htail scale hs le_rfl
  have he (i : ℕ) (_h0 : 0 ≤ i) (hi : i < 1) (y : Fin (HP.K + 1)) (_hy : y ∈ univ) :
      clippedError (w y 0) (w y 1) (uncompressedRow (fun _ => w) 0 (i + 1) y) ≤ 0 := by
    have hi0 : i = 0 := by omega
    subst i
    have hw : uncompressedRow (fun _ => w) 0 1 y = w y := by
      funext ν
      simp only [uncompressedRow, sum_range_one, Pi.zero_apply, zero_add]
    rw [hw, clippedError_self (w y 0) (w y 1) (w y) rfl rfl]
  have hb := ht scales scales_pos scales_step bin univ (fun _ => HP.K) (fun _ => w)
    0 w 1 0 (by omega) hover
    (fun _ _ => by norm_num [w]) (fun _ _ => by
      change |(0 : ℝ)| ≤ scale / 2
      rw [abs_zero]
      linarith)
    (fun _ _ _ => le_rfl) (fun _ => 0) (fun _ _ => le_rfl)
    (fun i hi => by omega) he 0 (mem_univ _)
  simp only [range_zero, mul_zero, sum_const_zero, add_zero] at hb
  exact abs_nonpos_iff.mp hb
