/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.UnroutedBinRegularity
public import Complexity.Foundations.Probability.NormalizedAtomRows.Output
public import Complexity.Foundations.Analysis.RowCompression.Decoder

/-!
# Accuracy kernel for actual unrouted normalized bins

The ratio-16 numerator uses its actual top clipping and fine-bin upper vanishing.
Its decoder has the hierarchy gate and the unchanged clipped second signal. The
constant is fixed before scales, bin, compression schedule and input rows. Fine-bin
numerators need not be monotone. This instantiates the shared saturated comparison,
rather than substituting the hierarchy atom cutoff for the bin numerator.

The conclusion is conditional on all raw-prefix clipped errors, including prefix zero.
It does not derive conditional mean/noise envelopes from lower-budget evaluator errors.
The preparation of `DenseBinRecipe.polynomialUnrouted` remains the existing polynomial
preparation; its support and covering laws are in `RoutedBinPreparation`.
-/

public section
universe u
namespace Matrix.DenseBinRecipe
open Finset Cslib Cslib.RowCompression FourthRootHierarchyParams.NormalizedRow

/-- A single accuracy coefficient for every actual ratio-16 bin decoder. The numerator
cap and normalization scale are chosen before the scales, bin and all input data.
Truth first entries have no upper bound, and compression support is not assumed. -/
theorem exists_polynomialUnrouted_iterate_bound
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {cap ζ : ℝ}
    (hcap : 0 ≤ cap) (hζ : 0 < ζ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
      (∀ i, b i = 16 * b (i + 1)) → ∀ bin : ℕ,
      ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ) (floors : ℕ → ℝ)
        (Δ : ℕ → ι → Fin 2 → ℝ) (truth raw : ι → Fin 2 → ℝ) (scale : ℝ) (m : ℕ),
      0 < scale → scale ≤ max cap 16 / 10000 → scale ≤ HP.η → 0 < m →
      (∀ i < m, HP.K ≤ n i) → (∀ i < m, floors i ≤ scale) →
      (∀ y ∈ s, 0 ≤ truth y 0) → (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      ∀ ε : ℕ → ℝ, (∀ i ≤ m, 0 ≤ ε i) →
      (∀ i ≤ m, ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw i y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError
        (output (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1))
          HP.ρ ζ) s HP.K (iterate s n (fun _ => HP.K) floors Δ ⟨0, raw⟩ m)
          ⟨0, truth⟩ y| ≤ C * prefixErrorBudget ε m := by
  let T : ℝ := max cap 16
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16) (le_max_right _ _)
  have hθ : HP.θ < (1 / 2 : ℝ) := by
    have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at h
    linarith
  have hη : HP.η₂ ≤ T := by
    have hm := threshold_margin HP
    have ht := HP.η_lt_η₂
    have hp := HP.η_pos
    have h16 : (16 : ℝ) ≤ T := le_max_right _ _
    linarith
  obtain ⟨Lq, hLq, hq⟩ := exists_boundedRoutedBinCutoff_root_lipschitz
    (cap := cap) (r := 16) (by norm_num)
  obtain ⟨⟨Lr, hr⟩, _⟩ := HP.cutoff_roots HP.ρ (by simp)
  let B := T ^ (4⁻¹ : ℝ)
  have hB : 0 ≤ B := Real.rpow_nonneg hT.le _
  -- The scalar proof gives one coefficient for all bins; its displayed formula is
  -- retained here so the compression coefficient is also selected before b/bin.
  let L := 2 * Lq + 4 * B / ζ + 2 * B * (Lr : ℝ)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  let R := (2 * T) ^ (4⁻¹ : ℝ)
  have hR : 0 ≤ R := Real.rpow_nonneg (by positivity) _
  -- Every bin shares the displayed root coefficient L, range R and saturation T.
  have laws (b : ℕ → ℝ) (hb : ∀ i, 0 < b i)
      (hstep : ∀ i, b i = 16 * b (i + 1)) (bin : ℕ) :
      let cutoff := boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)
      (∀ d, cutoff d ∈ Set.Icc 0 T) ∧
      (∀ d, d ≤ HP.θ → cutoff d = 0) ∧
      (∀ d d', T ≤ d → T ≤ d' → cutoff d = cutoff d') := by
    intro cutoff
    have hn := polynomialUnrouted_numerator_laws HP hb hstep hcap
    refine ⟨fun d => (hn bin d).1, fun d hd => (hn bin d).2 (hd.trans hθ.le), ?_⟩
    intro d d' hd hd'
    dsimp only [cutoff]
    cases bin with
    | zero =>
      exact boundedRoutedBinCutoff_zero_saturates hcap
        ((le_max_left _ _).trans hd) ((le_max_left _ _).trans hd')
    | succ i => rw [boundedRoutedBinCutoff_succ_eq_zero hb (by norm_num) hstep cap i
        ((le_max_right _ _).trans hd),
        boundedRoutedBinCutoff_succ_eq_zero hb (by norm_num) hstep cap i
        ((le_max_right _ _).trans hd')]
  -- Uniformity follows from the explicit coefficient of the shared engine, which
  -- depends only on T, R and L, never on the particular scalar function.
  let C := (8 * R + 3 * L) * (1 + 16 * (16 * (T + 1) + 1))
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro b hb hstep bin ι s n floors Δ truth raw scale m hs hscale hmargin hm hn hf
    hfirst hsecond ε hε herr y hy
  let cutoff := boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)
  obtain ⟨hc, hz, hsat⟩ := laws b hb hstep bin
  have hbound (d : ℝ) : |cutoff d ^ (4⁻¹ : ℝ)| ≤ B := by
    rw [abs_of_nonneg (Real.rpow_nonneg (hc d).1 _)]
    exact Real.rpow_le_rpow (hc d).1 (hc d).2 (by norm_num)
  have ha := root_dist_le_of_bounds cutoff HP.ρ hζ hB hLq Lr.coe_nonneg
    (fun d => (hc d).1) HP.ρ_nonneg HP.ρ_le_one hbound (hq b hb hstep bin)
    (fun q q' => by simpa only [Real.dist_eq] using hr.dist_le_mul q q')
  have hrange (d v r : ℝ) :
      0 ≤ output cutoff HP.ρ ζ d v r ^ (4⁻¹ : ℝ) ∧
      output cutoff HP.ρ ζ d v r ^ (4⁻¹ : ℝ) ≤ R := by
    have h := output_mem_Icc cutoff HP.ρ hT.le hc
      (fun q => ⟨HP.ρ_nonneg q, HP.ρ_le_one q⟩) ζ d v r
    exact ⟨Real.rpow_nonneg h.1 _, Real.rpow_le_rpow h.1 h.2 (by norm_num)⟩
  exact iterate_truth_root_bound (output cutoff HP.ρ ζ) hT hR
    (fun d d' v r hd hd' => by
      dsimp only [output, cutoff]
      rw [hsat d d' hd hd']) hrange hL ha
    hη (threshold_margin HP) HP.η_lt_η₂
    (fun d v r hd => by
      dsimp only [output, cutoff]
      rw [hz d hd, zero_mul, zero_div])
    (fun d v r hr => by simp only [output, HP.ρ_zero r hr, mul_zero, zero_div])
    (fun d v q r hq hr => by simp only [output, HP.ρ_one q hq, HP.ρ_one r hr])
    s n floors Δ truth raw scale HP.K m hs hscale hmargin (rank_pos HP) hm hn hf
    hfirst hsecond ε hε herr y hy

/-- Actual polynomial-bin support after compression, for arbitrary defaults and second
signals. This is a decoder property; no sparsity hypothesis on walk inputs is used. -/
theorem polynomialUnrouted_support
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {b : ℕ → ℝ} {cap : ℝ}
    (hcap : 0 ≤ cap) (hb : ∀ i, 0 < b i) (hstep : ∀ i, b i = 16 * b (i + 1))
    (bin : ℕ) {ι : Type*} (s : Finset ι) (a : State ι) (ζ : ℝ) :
    #{y ∈ s | output
      (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1))
      HP.ρ ζ (a.row y 0) (a.row y 1) (firstRank s HP.K a.defaultValue a.row) ≠ 0} < HP.K := by
  classical
  have hθ : HP.θ ≤ (1 / 2 : ℝ) := by
    have h := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at h
    linarith
  apply support_of_cutoff _ _ (rank_pos HP) HP.θ_pos.le
    (show HP.η₂ ≤ HP.θ by linarith [threshold_margin HP, HP.η_pos, HP.η_lt_η₂])
    _ HP.ρ_zero
  intro d hd
  exact (polynomialUnrouted_numerator_laws HP hb hstep hcap bin d).2 (hd.trans hθ)

end Matrix.DenseBinRecipe
