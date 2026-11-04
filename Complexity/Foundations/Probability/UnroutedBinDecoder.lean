/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.UnroutedBinRegularity
public import Complexity.Foundations.Probability.CompressionIntegrated
public import Complexity.Foundations.Probability.NormalizedAtomRows.Output
public import Complexity.Foundations.Analysis.RowCompression.DecoderSharp

/-!
# Accuracy kernel for actual unrouted normalized bins

The ratio-16 numerator uses its actual top clipping and fine-bin upper vanishing.
Its decoder has the hierarchy gate and the unchanged clipped second signal. The
constant is fixed before scales, bin, compression schedule and input rows. Fine-bin
numerators need not be monotone. This instantiates the shared saturated comparison,
rather than substituting the hierarchy atom cutoff for the bin numerator.

The general iterate comparison assumes all raw-prefix errors, including prefix zero.
The sharp no-overflow comparison charges only post-increment errors and a final raw error;
the first-overflow tail starts at the already-added overflow input. Tail-to-truth assembly
adds stationary preloss, with its tail coefficient fixed before the later floor. The integrated
specialization reuses supported-decoder moments and charges false overflow at prefix j+1.
None derives mean/noise envelopes or their weighted payments from lower-budget evaluator errors.
The preparation of `DenseBinRecipe.polynomialUnrouted` remains the existing polynomial
preparation; its support and covering laws are in `RoutedBinPreparation`.
-/

public section
universe u
namespace Matrix.DenseBinRecipe
open Finset Cslib Cslib.RowCompression Cslib.Probability FourthRootHierarchyParams.NormalizedRow

/-- Uniform scalar contracts for the actual ratio-16 decoder. The root coefficient
is selected before scales and bin; saturation uses top clipping or fine upper vanishing. -/
theorem exists_polynomialUnrouted_decoder_laws
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {cap ζ : ℝ}
    (hcap : 0 ≤ cap) (hζ : 0 < ζ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
      (∀ i, b i = 16 * b (i + 1)) → ∀ bin : ℕ,
      let H := output
        (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)) HP.ρ ζ
      (∀ d v r, H d v r = H (min (max cap 16) d) v (min (max cap 16) r)) ∧
      (∀ d v r, 0 ≤ H d v r ^ (4⁻¹ : ℝ) ∧
        H d v r ^ (4⁻¹ : ℝ) ≤ (2 * max cap 16) ^ (4⁻¹ : ℝ)) ∧
      (∀ d v r d' v' r',
        |H d v r ^ (4⁻¹ : ℝ) - H d' v' r' ^ (4⁻¹ : ℝ)| ≤
          L * (|d - d'| + |v - v'| + |r - r'|)) ∧
      (∀ d v r, d ≤ HP.θ → H d v r = 0) := by
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
    have hθ := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at hθ
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
  refine ⟨L, hL, ?_⟩
  intro b hb hstep bin
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
  refine ⟨?_, hrange, ha, ?_⟩
  · intro d v r
    have hd : cutoff d = cutoff (min T d) := by
      by_cases h : d ≤ T
      · rw [min_eq_right h]
      · rw [min_eq_left (not_le.mp h).le]
        exact hsat d T (not_le.mp h).le le_rfl
    change output cutoff HP.ρ ζ d v r = output cutoff HP.ρ ζ (min T d) v (min T r)
    by_cases hr : r ≤ T
    · simp only [output, hd, min_eq_right hr]
    · have hgate : HP.ρ r = 0 := HP.ρ_zero r (hη.trans (not_le.mp hr).le)
      simp only [output, min_eq_left (not_le.mp hr).le, hgate, HP.ρ_zero T hη,
        mul_zero, zero_div]
  · intro d v r hd
    simp only [output, hz d hd, zero_mul, zero_div]

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
  obtain ⟨L, hL, laws⟩ := exists_polynomialUnrouted_decoder_laws HP hcap hζ
  let T : ℝ := max cap 16
  let R : ℝ := (2 * T) ^ (4⁻¹ : ℝ)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16) (le_max_right _ _)
  refine ⟨(8 * R + 3 * L) * (1 + 16 * (16 * (T + 1) + 1)), by positivity, ?_⟩
  intro b hb hstep bin ι s n floors Δ truth raw scale m hs hscale hmargin hm hn hf
    hfirst hsecond ε hε herr y hy
  obtain ⟨hsat, hrange, hdist, hentry⟩ := laws b hb hstep bin
  let H := output
    (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)) HP.ρ ζ
  have hsat' (d d' v r : ℝ) (hd : T ≤ d) (hd' : T ≤ d') : H d v r = H d' v r := by
    dsimp only [H]
    rw [hsat, hsat d', min_eq_left hd, min_eq_left hd']
  have hη : HP.η₂ ≤ T := by
    have hm := threshold_margin HP
    have ht := HP.η_lt_η₂
    have hp := HP.η_pos
    have h16 : (16 : ℝ) ≤ T := le_max_right _ _
    have hθ := HP.θ_lt_θ₂.trans HP.θ₂_lt
    norm_num at hθ
    linarith
  exact iterate_truth_root_bound H hT (Real.rpow_nonneg (by positivity) _) hsat'
    hrange hL hdist hη (threshold_margin HP) HP.η_lt_η₂ hentry
    (fun d v r hr => by simp only [H, output, HP.ρ_zero r hr, mul_zero, zero_div])
    (fun d v q r hq hr => by simp only [H, output, HP.ρ_one q hq, HP.ρ_one r hr])
    s n floors Δ truth raw scale HP.K m hs hscale hmargin (rank_pos HP) hm hn hf
    hfirst hsecond ε hε herr y hy

/-- Sharp actual-bin comparison on the no-overflow event. The final coefficient is
chosen before δ, scales, bin and rows. Only post-increment errors enter the stationary
weighted sum; the final raw error is charged separately. -/
theorem exists_polynomialUnrouted_sharp_noOverflow
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {cap ζ : ℝ}
    (hcap : 0 ≤ cap) (hζ : 0 < ζ) :
    ∃ Cfinal : ℝ, 0 ≤ Cfinal ∧ ∀ δ : ℝ, 0 < δ → δ ≤ HP.η → δ ≤ max cap 16 →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
      (∀ i, b i = 16 * b (i + 1)) → ∀ bin : ℕ,
      ∀ {ι : Type*} (s : Finset ι) (n : ℕ → ℕ) (Δ : ℕ → ι → Fin 2 → ℝ)
        (truth raw : ι → Fin 2 → ℝ) (m : ℕ),
      (∀ i < m, stepThreshold s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ i ≤
        dyadicFloor δ m i) → (∀ y ∈ s, 0 ≤ truth y 0) →
      ∀ ε : ℕ → ℝ, (∀ i < m, 0 ≤ ε i) →
      (∀ i < m, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ εfinal : ℝ, 0 ≤ εfinal →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw m y) ≤ εfinal) →
      ∀ y ∈ s, |stateRootError
        (output (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1))
          HP.ρ ζ) s HP.K (iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m)
          ⟨0, truth⟩ y| ≤
        Cpre * ∑ i ∈ range m, dyadicFloor δ m i * ε i + Cfinal * εfinal := by
  obtain ⟨L, hL, laws⟩ := exists_polynomialUnrouted_decoder_laws HP hcap hζ
  let T : ℝ := max cap 16
  let R : ℝ := (2 * T) ^ (4⁻¹ : ℝ)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16) (le_max_right _ _)
  refine ⟨4 * R + L * (2 * (4 * T + 5) + 1), by positivity, ?_⟩
  intro δ hδ hδη hδT
  refine ⟨3 * L * (12 * (1 + δ / 2) / (δ / 2)), by positivity, ?_⟩
  intro b hb hstep bin ι s n Δ truth raw m hno hfirst ε hε herr εf hεf herrf y hy
  obtain ⟨hsat, hrange, hroot, hentry⟩ := laws b hb hstep bin
  have hδθ : δ ≤ HP.θ := by
    have h := threshold_margin HP
    linarith [HP.η_pos, HP.η_lt_η₂]
  exact sharp_noOverflow_decoder_bound _ hT (Real.rpow_nonneg (by positivity) _) hL
    hsat hrange hroot (rank_pos HP) hδ (by dsimp only [T]; linarith)
    (fun d v r hd => hentry d v r (hd.trans hδθ))
    (fun d v q r hq hr => by
      simp only [output, HP.ρ_one q (hq.trans hδη), HP.ρ_one r (hr.trans hδη)])
    s n Δ raw truth m hno hfirst ε hε herr εf hεf herrf y hy

/-- Actual-bin first-overflow tail against its stationary continuation. The coefficient
is selected before scales, bin, inputs and δ. Errors begin at the overflow input already added. -/
theorem exists_polynomialUnrouted_firstOverflow
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {cap ζ scale : ℝ}
    (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale)
    (hscale : scale ≤ max cap 16 / 10000) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
      (∀ i, b i = 16 * b (i + 1)) → ∀ bin : ℕ, ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (δ : ℝ),
      0 < δ → δ ≤ scale → ∀ m j : ℕ, j < m →
      IsFirstOverflow s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ j →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      (∀ i, j ≤ i → i < m → HP.K ≤ n i) →
      ∀ ε : ℕ → ℝ, (∀ i, j ≤ i → i < m → 0 ≤ ε i) →
      (∀ i, j ≤ i → i < m → ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError (output
        (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)) HP.ρ ζ) s HP.K
        (iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m)
        (stationaryContinuation s n HP.K (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j (m - j)) y| ≤
        Ctail * ∑ i ∈ Ico j m, 28^(m - i) * ε i := by
  obtain ⟨L, hL, laws⟩ := exists_polynomialUnrouted_decoder_laws HP hcap hζ
  let T : ℝ := max cap 16
  let R : ℝ := (2 * T) ^ (4⁻¹ : ℝ)
  have hT : 0 < T := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 16) (le_max_right _ _)
  refine ⟨4 * ((8 * R + 3 * L) * (1 + 16 * (16 * (T + 1) + 1))), by positivity, ?_⟩
  intro b hb hstep bin ι
  obtain ⟨hsat, hrange, hroot, _⟩ := laws b hb hstep bin
  apply firstOverflow_decoder_bound _ hT (Real.rpow_nonneg (by positivity) _) hL
    ?_ hrange hroot ?_ (rank_pos HP) hs hscale
  · intro d d' v r hd hd'
    rw [hsat, hsat d', min_eq_left hd, min_eq_left hd']
  · intro d v r hr
    have hη : HP.η₂ ≤ T := by
      have hm := threshold_margin HP
      have hθ := HP.θ_lt_θ₂.trans HP.θ₂_lt
      norm_num at hθ
      have h16 : (16 : ℝ) ≤ T := le_max_right _ _
      linarith [HP.η_pos, HP.η_lt_η₂]
    simp only [output, HP.ρ_zero r (hη.trans hr), mul_zero, zero_div]

/-- Actual-bin tail-to-truth comparison. The pre-overflow stationary loss and the
preloaded tail are charged separately; Ctail is selected before δ and all bin data. -/
theorem exists_polynomialUnrouted_sharp_firstOverflow
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {cap ζ scale : ℝ}
    (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hcapscale : scale ≤ max cap 16 / 10000) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ δ : ℝ, 0 < δ → δ ≤ scale →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
      (∀ i, b i = 16 * b (i + 1)) → ∀ bin : ℕ, ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (m j : ℕ), j < m →
      IsFirstOverflow s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ j →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      (∀ i, j ≤ i → i < m → HP.K ≤ n i) →
      ∀ ε : ℕ → ℝ, (∀ i < m, 0 ≤ ε i) →
      (∀ i < j, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      (∀ i, j ≤ i → i < m → ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError (output (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b
        cap bin (fun _ => 1)) HP.ρ ζ) s HP.K
        (iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
        Cpre*∑ i ∈ range j, dyadicFloor δ m i * ε i + Ctail*∑ i ∈ Ico j m, 28^(m - i) * ε i := by
  obtain ⟨Ct, hCt, htail⟩ := exists_polynomialUnrouted_firstOverflow HP hcap hζ hs hcapscale
  obtain ⟨L, hL, laws⟩ := exists_polynomialUnrouted_decoder_laws HP hcap hζ
  refine ⟨Ct, hCt, ?_⟩
  intro δ hδ hδs
  refine ⟨3 * L * (12 * (1 + δ / 2) / (δ / 2)), by positivity, ?_⟩
  intro b hb hstep bin ι s n Δ raw truth m j hj hover hfirst hsecond hn ε hε
    herrpre herrtail y hy
  let H := output
    (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)) HP.ρ ζ
  obtain ⟨_, _, hroot, hentry⟩ := laws b hb hstep bin
  have hδθ : δ ≤ HP.θ := by
    have h := threshold_margin HP
    linarith [HP.η_lt_η₂, HP.η_pos]
  let a := iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m
  let ref := stationaryState s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j
  let c := stationaryContinuation s n HP.K (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j (m - j)
  have ht := htail b hb hstep bin s n Δ raw truth δ hδ hδs m j hj hover hfirst hsecond hn ε
    (fun i _ hi => hε i hi) herrtail y hy
  have hp := stationary_decoder_bound H hL hδ
    (fun d v r hd => hentry d v r (hd.trans hδθ))
    (fun d v q r hq hr => by simp only [H, output,
      HP.ρ_one q (hq.trans (hδs.trans hmargin)), HP.ρ_one r (hr.trans (hδs.trans hmargin))])
    hroot (rank_pos HP) s n Δ raw truth m j hj.le hover.1 ε
    (fun i hi => hε i (hi.trans hj)) herrpre y hy
  have hc := stationary_decoder_continuation H hs
    (hmargin.trans_lt HP.η_lt_η₂) (threshold_margin HP) hentry
    (fun d v r hr => by simp only [H, output, HP.ρ_zero r hr, mul_zero, zero_div])
    (fun d v q r hq hr => by simp only [H, output,
      HP.ρ_one q (hq.trans hmargin), HP.ρ_one r (hr.trans hmargin)])
    (rank_pos HP) s n Δ raw truth hδ hδs m j (m - j) (by omega)
    hover.1 hfirst hsecond hn y hy
  change H (c.row y 0) (c.row y 1) (firstRank s HP.K
    c.defaultValue c.row) =
    H (ref.row y 0) (ref.row y 1) (firstRank s HP.K
      ref.defaultValue ref.row) at hc
  have href : stateRootError H s HP.K c ⟨0, truth⟩
    y = stateRootError H
    s HP.K ref ⟨0, truth⟩ y := by
    unfold stateRootError
    rw [hc]
  calc
    _ ≤ |stateRootError H s HP.K a c y| +
      |stateRootError H s HP.K c
      ⟨0, truth⟩ y| := abs_sub_le _ _ _
    _ ≤ Ct * ∑ i ∈ Ico j m, 28^(m - i) * ε i +
        (3 * L * (12 * (1 + δ / 2) / (δ / 2))) *
          ∑ i ∈ range j, dyadicFloor δ m i * ε i :=
      add_le_add ht (by rw [href]; exact hp)
    _ = _ := add_comm _ _




open Classical in
/-- The actual-bin sharp truth comparison outside false overflow events. Final and tail
coefficients precede δ, scales and bin; the stationary coefficient alone depends on δ. -/
theorem exists_polynomialUnrouted_sharp_compression
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {cap ζ scale : ℝ}
    (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hcapscale : scale ≤ max cap 16 / 10000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ scale →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
        (∀ i, b i = 16 * b (i + 1)) → ∀ bin : ℕ, ∀ {ι : Type u} (S : Finset ι) (n : ℕ → ℕ)
        (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ)
        (m : ℕ) (heavy : ℕ → Prop),
        (∀ y ∈ S, 0 ≤ truth y 0) →
        (∀ y ∈ S, |truth y 1| ≤ scale / 2) →
        (∀ i < m, HP.K ≤ n i) → ∀ (ε : ℕ → ℝ),
        (∀ i < m, 0 ≤ ε i) →
        (∀ i < m, ∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
        ∀ εfinal : ℝ, 0 ≤ εfinal →
        (∀ y ∈ S,
          clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw m y) ≤ εfinal) →
        (¬ ∃ j < m, IsFirstOverflow S n (fun _ => HP.K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ ¬heavy j) →
        ∀ y ∈ S,
        |stateRootError (output (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin
          (fun _ => 1)) HP.ρ ζ) S HP.K
          (iterate S n (fun _ => HP.K) (dyadicFloor η m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
          A * (∑ i ∈ range m, dyadicFloor η m i * ε i) +
          C * (if ∀ i < m, stepThreshold S n (fun _ => HP.K) (dyadicFloor η m) Δ ⟨0, raw⟩ i ≤
            dyadicFloor η m i then εfinal else 0) + C * (∑ j ∈ range m,
            if IsFirstOverflow S n (fun _ => HP.K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ heavy j then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0) := by
  classical
  obtain ⟨Cf, hCf, hno⟩ := exists_polynomialUnrouted_sharp_noOverflow HP hcap hζ
  obtain ⟨Ct, hCt, hover⟩ := exists_polynomialUnrouted_sharp_firstOverflow HP hcap hζ hs hmargin
    hcapscale
  refine ⟨max Cf Ct, le_trans hCf (le_max_left _ _), ?_⟩
  intro η hη hηs
  obtain ⟨An, hAn, hn⟩ := hno η hη (hηs.trans hmargin) (by have h := le_max_right cap 16; linarith)
  obtain ⟨At, hAt, ht⟩ := hover η hη hηs
  refine ⟨max An At, le_trans hAn (le_max_left _ _), ?_⟩
  intro b hb hstep bin
  exact sharp_compression_of_bounds _ HP.K hη hCf hCt hAn hAt
    (fun s n Δ raw truth => hn b hb hstep bin s n Δ truth raw) (ht b hb hstep bin)


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

open Classical in
/-- Integrated actual-bin truth error with post-increment false-overflow payment.
This conditional bound retains the weighted mean/noise and heavy-tail budgets; it is
not a recursive evaluator accuracy certificate. -/
theorem exists_polynomialUnrouted_rowNormPow_le
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {cap ζ scale : ℝ}
    (hcap : 0 ≤ cap) (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hcapscale : scale ≤ max cap 16 / 10000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ scale → η ≤ 1 →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : ℕ → ℝ), (∀ i, 0 < b i) →
        (∀ i, b i = 16 * b (i + 1)) → ∀ bin : ℕ, ∀ {Ω V : Type u} [Fintype Ω] [Fintype V]
        (N u : ℝ), 0 ≤ N * u → ∀ (X Y : Ω → V → Prop)
        [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
        (n : ℕ → ℕ) (m : ℕ), (∀ i < m, HP.K ≤ n i) →
        ∀ (Δ : Ω → V → ℕ → V → Fin 2 → ℝ) (raw : Ω → V → V → Fin 2 → ℝ)
        (truth : Ω → V → V → Fin 2 → ℝ),
        (∀ σ x y, X σ x → Y σ y → 0 ≤ truth σ x y 0) →
        (∀ σ x y, X σ x → Y σ y → |truth σ x y 1| ≤ scale / 2) →
        (∀ j < m, ∀ σ x y, X σ x → Y σ y →
          truth σ x y 0 ≤ dyadicFloor η m j / 4 → truth σ x y 1 = 0) →
        ∀ (ε : ℕ → Ω → V → ℝ) (εfinal : Ω → V → ℝ),
        (∀ i < m, ∀ σ x, X σ x → 0 ≤ ε i σ x) →
        (∀ σ x, X σ x → 0 ≤ εfinal σ x) →
        (∀ i < m, ∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) (i + 1) y) ≤ ε i σ x) →
        (∀ σ x y, X σ x → Y σ y →
          clippedError (truth σ x y 0) (truth σ x y 1)
            (uncompressedRow (Δ σ x) (raw σ x) m y) ≤ εfinal σ x) →
        let S := fun σ => ({y | Y σ y} : Finset V)
        let actual := fun σ x => iterate (S σ) n (fun _ => HP.K)
          (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m
        let Pre := fun σ x => ∑ i ∈ range m, dyadicFloor η m i * ε i σ x
        let No := fun σ x => if ∀ i < m,
          stepThreshold (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ i ≤
            dyadicFloor η m i then εfinal σ x else 0
        let Tail := fun σ x => ∑ j ∈ range m,
          if IsFirstOverflow (S σ) n (fun _ => HP.K) (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ j ∧
            heavyCountEvent Y univ (fun y => truth σ x y 0) (dyadicFloor η m j) (n j) σ then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i σ x else 0
        rowNormPow 4 N u X Y (fun σ x y =>
          stateRootError (output
            (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)) HP.ρ ζ)
              (S σ) HP.K (actual σ x)
            ⟨0, truth σ x⟩ y) ≤
          128 * (HP.K : ℝ) * (A ^ 4 * vertexNormPow 4 N u X Pre +
            C ^ 4 * vertexNormPow 4 N u X No + C ^ 4 * vertexNormPow 4 N u X Tail) +
          ∑ j ∈ range m, (64 * (HP.K : ℝ) * ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 / ((n j : ℝ) *
            dyadicFloor η m j ^ 4)) *
            rowNormPow 4 N u X Y (fun σ x y => clippedError (truth σ x y 0) (truth σ x y 1)
              (uncompressedRow (Δ σ x) (raw σ x) (j + 1) y)) := by
  obtain ⟨C, hC, hscales⟩ := exists_polynomialUnrouted_sharp_compression
    HP hcap hζ hs hmargin hcapscale
  refine ⟨C, hC, ?_⟩
  intro η hη hηs hη1
  obtain ⟨A, hA, hbound⟩ := hscales η hη hηs
  refine ⟨A, hA, ?_⟩
  intro b hb hstep bin
  obtain ⟨_, _, laws⟩ := exists_polynomialUnrouted_decoder_laws HP hcap hζ
  exact Cslib.RowCompression.compression_rowNormPow_le
    (output (boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1) b cap bin (fun _ => 1)) HP.ρ ζ)
    HP.K ((2 * max cap 16) ^ (4⁻¹ : ℝ)) (Real.rpow_nonneg (by positivity) _)
    (fun S a => polynomialUnrouted_support HP hcap hb hstep bin S a ζ)
    (laws b hb hstep bin).2.1 (rank_pos HP) hη hη1 hC hA (hbound b hb hstep bin)

end Matrix.DenseBinRecipe
