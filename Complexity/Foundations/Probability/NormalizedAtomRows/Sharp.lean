/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.BoundedLoss
import Complexity.Foundations.Analysis.RowCompression.PreloadedIteration
public import Complexity.Foundations.Analysis.RowCompression.DecoderSharp
public import Complexity.Foundations.Analysis.RowCompression.FalseOverflow

/-!
# Sharp cap-free comparison for actual normalized atoms

The stationary, no-overflow and first-overflow comparisons adapt the proof patterns of
Samuel Schlesinger's polynomial rows to the actual hierarchy decoder. True first entries
are arbitrary nonnegative reals. The actual stationary preloss supplies the bounded common
loss and default needed by the landed saturated-root API; no compression state is capped.
Final and tail constants are fixed before the later dyadic compression floor; only the
stationary coefficient may depend on that floor. The positive post-overflow horizon starts
at the already-added raw input. The assembly excludes false first overflows explicitly.

This is the deterministic fourth-root comparison part of §8.2, Lemmas 8.2–8.3
(printed pp. 46–48), of [OpenAI2026LogSpace], revision 7ef5c0cc, using fourth rather than
eighth roots. Raw prefix errors and capacity schedules remain caller inputs. It does not
prove Proposition 8.5, integrated moments, recursive budget induction or native RL.
-/

public section
universe u
namespace Matrix.FourthRootHierarchyParams.NormalizedRow
open Finset Cslib Matrix Cslib.RowCompression
open scoped BigOperators
variable (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ : ℝ) (hζ : 0 < ζ)
include hζ

/-- Weighted stationary preloss reuses the existing theorem. Only this coefficient may
blow up as the later compression scale tends to zero; scalar root sensitivity stays fixed. -/
theorem stationary_bound {scale : ℝ} (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    {δ : ℝ} (hδ : 0 < δ) (hδs : δ ≤ scale) :
    ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {ι : Type*} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (m j : ℕ), j ≤ m →
      (∀ i < j, stepThreshold s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ i ≤ dyadicFloor δ
        m i) →
      ∀ ε : ℕ → ℝ, (∀ i < j, 0 ≤ ε i) →
      (∀ i < j, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K
        (stationaryState s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j) ⟨0, truth⟩ y| ≤
        Cpre * ∑ i ∈ range j, dyadicFloor δ m i * ε i := by
  obtain ⟨L, hL, hroot⟩ := root_dist HP hζ
  refine ⟨3 * L * (12 * (1 + δ / 2) / (δ / 2)), by positivity, ?_⟩
  intro ι s n Δ raw truth m j hj hno ε hε herr y hy
  have hηθ : δ ≤ HP.θ := by
    have h := threshold_margin HP
    linarith [HP.η_lt_η₂, HP.η_pos]
  exact stationary_decoder_bound (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) hL hδ
    (fun d _ _ hd => entry_zero HP (hd.trans hηθ))
    (fun _ _ q r hq hr => gate_flat HP (hq.trans (hδs.trans hmargin))
      (hr.trans (hδs.trans hmargin))) hroot (rank_pos HP)
    s n Δ raw truth m j hj hno ε hε herr y hy


omit hζ in
/-- Zero-increment continuation preserves the actual normalized decoder. -/
theorem continuation_preserved {ι : Type*} (s : Finset ι) (n : ℕ → ℕ)
    (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ)
    {scale δ : ℝ} (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hδ : 0 < δ) (hδs : δ ≤ scale) (m j r : ℕ) (hr : j + r ≤ m)
    (hno : ∀ i < j, stepThreshold s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ i ≤
      dyadicFloor δ m i)
    (hfirst : ∀ y ∈ s, 0 ≤ truth y 0) (hsecond : ∀ y ∈ s, |truth y 1| ≤ scale / 2)
    (hn : ∀ i, j ≤ i → i < m → HP.K ≤ n i) (y : ι) (hy : y ∈ s) :
    let b := stationaryState s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j
    let c := stationaryContinuation s n HP.K (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j r
    output HP.toHierarchyParams.atomCutoff HP.ρ ζ (c.row y 0) (c.row y 1) (firstRank s HP.K
      c.defaultValue c.row) =
      output HP.toHierarchyParams.atomCutoff HP.ρ ζ (b.row y 0) (b.row y 1) (firstRank s HP.K
        b.defaultValue b.row) := by
  exact stationary_decoder_continuation (output HP.toHierarchyParams.atomCutoff HP.ρ ζ)
    hs (hmargin.trans_lt HP.η_lt_η₂) (threshold_margin HP)
    (fun _ _ _ hd => entry_zero HP hd) (fun _ _ _ hr => gate_zero HP hr)
    (fun _ _ _ _ hq hr => gate_flat HP (hq.trans hmargin) (hr.trans hmargin))
    (rank_pos HP) s n Δ raw truth hδ hδs m j r hr hno hfirst hsecond hn y hy

/-- Cap-free actual relative comparison at fixed shape. The bounded initial default is
necessary for the sentinel coupling; it is supplied by actual stationary preloss. -/
theorem relative_bound {scale : ℝ} (hs : 0 < scale)
    (hscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (floors : ℕ → ℝ) (Δ : ℕ → ι → Fin 2 → ℝ)
      (truth raw loss : ι → Fin 2 → ℝ) (z : ℝ) (m : ℕ), z ≤ scale → 0 < m →
      (∀ i < m, HP.K ≤ n i) → (∀ i < m, floors i ≤ scale) →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      (∀ y ∈ s, ∀ ν, |loss y ν| ≤ scale / 2) →
      ∀ ε : ℕ → ℝ, (∀ i ≤ m, 0 ≤ ε i) →
      (∀ i ≤ m, ∀ y ∈ s, clippedError (truth y 0) (truth y 1)
        (uncompressedRow Δ raw i y) ≤ ε i) → ∀ y ∈ s,
      |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K (iterate s n (fun _
        => HP.K) floors Δ ⟨z, raw + loss⟩ m)
        (iterate s n (fun _ => HP.K) floors (fun _ => 0) ⟨z, truth + loss⟩ m) y| ≤
        C * prefixErrorBudget ε m := by
  let T := HP.toHierarchyParams.atomCap
  let R := 2 * HP.Q T ^ (4⁻¹ : ℝ)
  have hR : 0 ≤ R := mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _)
  have hsat (d d' v r : ℝ) (hd : T ≤ d) (hd' : T ≤ d') :
      output HP.toHierarchyParams.atomCutoff HP.ρ ζ d v r = output
      HP.toHierarchyParams.atomCutoff HP.ρ ζ d' v r := by
    rw [output_upperCapped HP ζ d, output_upperCapped HP ζ d']
    rw [min_eq_left hd, min_eq_left hd']
  have hrange {ι : Type u} (s : Finset ι) (K : ℕ) (a b : State ι) (y : ι) :
      |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s K a b y| ≤ R := by
    have ha := root_range HP ζ (a.row y 0) (a.row y 1) (firstRank s K a.defaultValue a.row)
    have hb := root_range HP ζ (b.row y 0) (b.row y 1) (firstRank s K b.defaultValue b.row)
    change 0 ≤ _ ∧ _ ≤ R at ha hb
    unfold stateRootError
    exact abs_sub_le_iff.mpr
      ⟨by linarith [ha.1, ha.2, hb.1, hb.2], by linarith [ha.1, ha.2, hb.1, hb.2]⟩
  have hg (d v r : ℝ) (hr : T ≤ r) : output HP.toHierarchyParams.atomCutoff HP.ρ ζ d v r = 0 := by
    apply gate_zero HP
    have hc := HP.toHierarchyParams.atomCap_gt
    have hm := threshold_margin HP
    have ht := HP.θ_lt_θ₂
    dsimp only [T] at hr
    linarith [le_max_right ((HP.k : ℝ) + 1) HP.θ₂]
  obtain ⟨C, hC, hbound⟩ := Cslib.RowCompression.exists_iterate_root_bound
    (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) hsat R hR hrange (root_dist HP hζ) hg
      (cap_pos HP)
  refine ⟨C, hC, ?_⟩
  intro ι s n floors Δ truth raw loss z m hz hm hn hf hfirst hsecond hloss ε hε herr y hy
  simpa only [stateRootError] using
    hbound s n floors Δ truth raw loss z scale HP.K hs hscale hz
      (rank_pos HP) m hm hn hf hfirst hsecond hloss ε hε herr y hy

/-- Sharp no-overflow comparison. Cfinal is chosen before the later compression scale δ.
No initial-prefix error enters a 28-weighted budget. -/
theorem sharp_noOverflow {scale : ℝ} (hs : 0 < scale) (hmargin : scale ≤ HP.η) :
    ∃ Cfinal : ℝ, 0 ≤ Cfinal ∧ ∀ δ : ℝ, 0 < δ → δ ≤ scale →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (m : ℕ),
      (∀ i < m, stepThreshold s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ i ≤ dyadicFloor δ
        m i) →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      ∀ ε : ℕ → ℝ, (∀ i < m, 0 ≤ ε i) →
      (∀ i < m, ∀ y ∈ s, δ / 2 ≤ truth y 0 →
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ εfinal : ℝ, 0 ≤ εfinal →
      (∀ y ∈ s, clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw m y) ≤ εfinal) →
        ∀ y ∈ s, |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K
        (iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
        Cpre * ∑ i ∈ range m, dyadicFloor δ m i * ε i + Cfinal * εfinal := by
  obtain ⟨L, hL, hroot⟩ := root_dist HP hζ
  let T := HP.toHierarchyParams.atomCap
  let R := 2 * HP.Q T ^ (4⁻¹ : ℝ)
  have hT : 0 < T := cap_pos HP
  have hR : 0 ≤ R := mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _)
  refine ⟨4 * R + L * (2 * (4 * T + 5) + 1), by positivity, ?_⟩
  intro δ hδ hδs
  refine ⟨3 * L * (12 * (1 + δ / 2) / (δ / 2)), by positivity, ?_⟩
  intro ι s n Δ raw truth m hno hfirst ε hε herr εf hεf herrf y hy
  have hηθ : δ ≤ HP.θ := by
    have h := threshold_margin HP
    linarith [HP.η_lt_η₂, HP.η_pos]
  have hδT : δ / 100 ≤ T := by
    have hcap := HP.toHierarchyParams.atomCap_gt
    dsimp only [T]
    linarith [HP.η_lt_η₂, HP.θ_lt_θ₂,
      le_max_right ((HP.k : ℝ) + 1) HP.θ₂]
  exact sharp_noOverflow_decoder_bound (output HP.toHierarchyParams.atomCutoff HP.ρ ζ)
    (cap_pos HP) hR hL (output_upperCapped HP ζ)
    (root_range HP ζ) hroot (rank_pos HP) hδ hδT
    (fun d _ _ hd => entry_zero HP (hd.trans hηθ))
    (fun _ _ q r hq hr => gate_flat HP (hq.trans (hδs.trans hmargin))
      (hr.trans (hδs.trans hmargin)))
    s n Δ raw truth m hno hfirst ε hε herr εf hεf herrf y hy

/-- Actual first-overflow tail compared with the stationary continuation. Errors start
at the already-added overflow input, not the earlier global prefix. -/
theorem firstOverflow_bound {scale : ℝ} (hs : 0 < scale) (_hmargin : scale ≤ HP.η)
    (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
      (Δ : ℕ → ι → Fin 2 → ℝ) (raw truth : ι → Fin 2 → ℝ) (δ : ℝ),
      0 < δ → δ ≤ scale → ∀ m j : ℕ, j < m →
      IsFirstOverflow s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ j →
      (∀ y ∈ s, 0 ≤ truth y 0) →
      (∀ y ∈ s, |truth y 1| ≤ scale / 2) →
      (∀ i, j ≤ i → i < m → HP.K ≤ n i) →
      ∀ ε : ℕ → ℝ, (∀ i, j ≤ i → i < m → 0 ≤ ε i) →
      (∀ i, j ≤ i → i < m → ∀ y ∈ s,
        clippedError (truth y 0) (truth y 1) (uncompressedRow Δ raw (i + 1) y) ≤ ε i) →
      ∀ y ∈ s, |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K
        (iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m)
        (stationaryContinuation s n HP.K (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j (m - j)) y| ≤
        Ctail * ∑ i ∈ Ico j m, 28^(m - i) * ε i := by
  obtain ⟨L, hL, hroot⟩ := root_dist HP hζ
  let T := HP.toHierarchyParams.atomCap
  let R := 2 * HP.Q T ^ (4⁻¹ : ℝ)
  have hT : 0 < T := cap_pos HP
  have hR : 0 ≤ R := mul_nonneg (by norm_num) (Real.rpow_nonneg (HP.Q_nonneg _) _)
  refine ⟨4 * ((8 * R + 3 * L) * (1 + 16 * (16 * (T + 1) + 1))), by positivity, ?_⟩
  intro ι
  apply firstOverflow_decoder_bound (output HP.toHierarchyParams.atomCutoff HP.ρ ζ)
    hT hR hL ?_ (root_range HP ζ) hroot ?_ (rank_pos HP) hs hcapscale
  · intro d d' v r hd hd'
    rw [output_upperCapped HP ζ d, output_upperCapped HP ζ d',
      min_eq_left hd, min_eq_left hd']
  · intro d v r hr
    apply gate_zero HP
    have hcap := HP.toHierarchyParams.atomCap_gt
    have hm := threshold_margin HP
    dsimp only [T] at hr
    linarith [HP.θ_lt_θ₂, le_max_right ((HP.k : ℝ) + 1) HP.θ₂]

/-- Actual first-overflow truth decomposition. Ctail is chosen once at fixed signalScale;
only Cpre depends on the subsequently chosen compressionScale. -/
theorem sharp_firstOverflow {scale : ℝ} (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ Ctail : ℝ, 0 ≤ Ctail ∧ ∀ δ : ℝ, 0 < δ → δ ≤ scale →
      ∃ Cpre : ℝ, 0 ≤ Cpre ∧ ∀ {ι : Type u} (s : Finset ι) (n : ℕ → ℕ)
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
      ∀ y ∈ s, |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K
        (iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
        Cpre*∑ i ∈ range j, dyadicFloor δ m i * ε i + Ctail*∑ i ∈ Ico j m, 28^(m - i) * ε i := by
  obtain ⟨Ct, hCt, htail⟩ := firstOverflow_bound HP ζ hζ hs hmargin hcapscale
  refine ⟨Ct, hCt, ?_⟩
  intro δ hδ hδs
  obtain ⟨Cp, hCp, hpre⟩ := stationary_bound HP ζ hζ hs hmargin hδ hδs
  refine ⟨Cp, hCp, ?_⟩
  intro ι s n Δ raw truth m j hj hover hfirst hsecond hn ε hε herrpre herrtail y hy
  let a := iterate s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ m
  let b := stationaryState s n (fun _ => HP.K) (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j
  let c := stationaryContinuation s n HP.K (dyadicFloor δ m) Δ ⟨0, raw⟩ truth j (m - j)
  have ht := htail s n Δ raw truth δ hδ hδs m j hj hover hfirst hsecond hn ε
    (fun i _ hi => hε i hi) herrtail y hy
  have hp := hpre s n Δ raw truth m j hj.le hover.1 ε (fun i hi => hε i (hi.trans hj)) herrpre y hy
  have hc := continuation_preserved HP ζ s n Δ raw truth hs hmargin hδ hδs m j (m - j)
    (by omega) hover.1 hfirst hsecond hn y hy
  change output HP.toHierarchyParams.atomCutoff HP.ρ ζ (c.row y 0) (c.row y 1) (firstRank s HP.K
    c.defaultValue c.row) =
    output HP.toHierarchyParams.atomCutoff HP.ρ ζ (b.row y 0) (b.row y 1) (firstRank s HP.K
      b.defaultValue b.row) at hc
  have href : stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K c ⟨0, truth⟩
    y = stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ)
    s HP.K b ⟨0, truth⟩ y := by
    unfold stateRootError; rw [hc]
  calc
    _ ≤ |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K a c y| +
      |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) s HP.K c
      ⟨0, truth⟩ y| := abs_sub_le _ _ _
    _ ≤ Ct*∑ i ∈ Ico j m, 28^(m - i) * ε i + Cp*∑ i ∈ range j, dyadicFloor δ m i * ε i :=
      add_le_add ht (by rw [href]; exact hp)
    _ = _ := add_comm _ _



open Classical in
/-- Sharp actual-output decomposition on the complement of false first overflow. -/
theorem sharp_compression {scale : ℝ} (hs : 0 < scale) (hmargin : scale ≤ HP.η)
    (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ η : ℝ, 0 < η → η ≤ scale →
      ∃ A : ℝ, 0 ≤ A ∧ ∀ {ι : Type*} (S : Finset ι) (n : ℕ → ℕ)
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
        |stateRootError (output HP.toHierarchyParams.atomCutoff HP.ρ ζ) S HP.K
          (iterate S n (fun _ => HP.K) (dyadicFloor η m) Δ ⟨0, raw⟩ m) ⟨0, truth⟩ y| ≤
          A * (∑ i ∈ range m, dyadicFloor η m i * ε i) +
          C * (if ∀ i < m, stepThreshold S n (fun _ => HP.K) (dyadicFloor η m) Δ ⟨0, raw⟩ i ≤
            dyadicFloor η m i then εfinal else 0) + C * (∑ j ∈ range m,
            if IsFirstOverflow S n (fun _ => HP.K) (dyadicFloor η m) Δ ⟨0, raw⟩ j ∧ heavy j then
              ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i else 0) := by
  classical
  obtain ⟨Cf, hCf, hno⟩ := sharp_noOverflow HP ζ hζ hs hmargin
  obtain ⟨Ct, hCt, hover⟩ := sharp_firstOverflow HP ζ hζ hs hmargin hcapscale
  refine ⟨max Cf Ct, le_trans hCf (le_max_left _ _), ?_⟩
  intro η hη hmargin
  obtain ⟨An, hAn, hn⟩ := hno η hη hmargin
  obtain ⟨At, hAt, ht⟩ := hover η hη hmargin
  refine ⟨max An At, le_trans hAn (le_max_left _ _), ?_⟩
  exact sharp_compression_of_bounds _ HP.K hη hCf hCt hAn hAt hn ht


omit HP ζ hζ in
/-- A fixed shape and positive denominator encoding can be chosen before any later floor.
This is compatible with the actual preparation mean in [0,1] vanishing on light first input. -/
theorem fixed_shape (HP : FourthRootHierarchyParams 16 1 16 32 8) :
    ∃ scale ζ : ℝ, 0 < scale ∧ scale ≤ HP.η ∧
      scale ≤ HP.toHierarchyParams.atomCap / 10000 ∧ 0 < ζ ∧
      ζ ≤ scale / 2 ∧ ζ ≤ HP.θ / 2 := by
  let scale := min (HP.η / 2) (HP.toHierarchyParams.atomCap / 20000)
  have hs : 0 < scale := lt_min (half_pos HP.η_pos) (div_pos (cap_pos HP) (by norm_num))
  refine ⟨scale, min (scale / 4) (HP.θ / 4), hs, ?_, ?_, ?_, ?_, ?_⟩
  · exact (min_le_left _ _).trans (by linarith [HP.η_pos])
  · exact (min_le_right _ _).trans (by linarith [cap_pos HP])
  · exact lt_min (by positivity) (by have := HP.θ_pos; positivity)
  · exact (min_le_left _ _).trans (by linarith)
  · exact (min_le_right _ _).trans (by linarith [HP.θ_pos])


end Matrix.FourthRootHierarchyParams.NormalizedRow
