/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.Moment

/-!
# Actual normalized-output fourth moment at arbitrary fixed hierarchy rank

`actualNormalizedCapacity` runs the actual iterate at the supplied capacity sequence, with
zero default, unchanged raw increments/floor, core rank gate, atom cutoff and uncentered
second/ζ denominator. The first rank is full terminal rank; the final output uses usage.
`genuineNormalizedRecipe_eq_request` identifies the target with the existing normalizedRequest
and its genuine full-environment joint preparation mean, preserving roles and copy suffixes.

`actual_normalized_fourth_moment_capacity` proves row fourth-root error at most C*ε^4 from
explicit clipped mean envelopes and strong endpoint row-noise moments on their respective
masks. The actual first-overflow masks and false-event charges use the new capacities.
`compatibleCapacity_bounds` discharges both capacity lower bounds for arbitrary fixed K;
`actual_normalized_fourth_moment_compatible` specializes the actual output accordingly.
The final coefficient may depend on the positive floor, fixed before P/J/N/u, width,
positive horizon and capacity sequence. No true-entry cap, output-error certificate,
output/event monotonicity or adaptive-endpoint independence is assumed.

This is a conditional fourth-moment adaptation of §8.2, Proposition 8.5 (printed pp. 45–49),
of [OpenAI2026LogSpace], revision 7ef5c0cc. Lower-child envelopes/noise estimates, recursive
induction and native/RL endpoints remain open. Christian Reitwiessner supplied the actual
H4 specialization; compression and norm proof patterns are adapted from Samuel Schlesinger.
-/

public section
open Matrix.FourthRootHierarchyParams Matrix.HierarchyParams.H4RankEnvironment
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- Genuine normalized recipe, with its actual joint source/usage preparatory mean. -/
@[expose] noncomputable def genuineNormalizedRecipe
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x y : ZMod P) : ℝ :=
  if retainedMask t Lt D suffix σ y then
    HP.toHierarchyParams.atomCutoff (G x y / rate k) *
      rowGate HP.ρ HP.K (rate k) G {z | retainedMask t (side P k) D suffix σ z} x /
      NormalizedRow.clip (genuineMean HP s t Ls Lt (CopyPadding.identifier D sourceSuffix x) D
        suffix k G x y)
  else 0

open Classical in
lemma genuine_recipe_identity
    (HP : FourthRootHierarchyParams 16 1 16 32 8) {ζ : ℝ} (hζ : 0 < ζ)
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) (x y : ZMod P) :
    genuineNormalizedRecipe HP s t Ls Lt D sourceSuffix suffix k G σ x y =
    if retainedMask t Lt D suffix σ y then NormalizedRow.output HP ζ
      (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 0)
      (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 1)
      (firstRank {z | retainedMask t (side P k) D suffix σ z} HP.K 0
        (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x)) else 0 := by
  unfold genuineNormalizedRecipe
  split_ifs with hy
  · simp only [NormalizedRow.output, genuineTarget, Fin.isValue, ↓reduceIte, one_ne_zero, hy,
      mul_div_cancel_left₀ _ hζ.ne', firstRank, max_eq_right kthLargest_nonneg, rowGate]
  · rfl

open Classical in
/-- Genuine preparation's full-environment mean agrees with the actual request slice,
including its source identifier and inherited terminal/usage suffix. -/
lemma request_genuineMean_eq {q : ℕ} (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (r : HierarchyTask.Request q (Fin J) (ZMod P)) (hr : Admissible r)
    (ks kt k : ℕ) (hs : r.source.rate = rate ks) (ht : r.usage.rate = rate kt)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) :
    rowSliceMean (fun τ v => r.source.retains (channels D) τ v)
      (fun τ v => r.usage.retains (channels D) τ v)
      (genuinePrep HP r.terminal.role D r.terminal.suffix k G) x y =
    genuineMean HP r.source.role r.terminal.role (side P ks) (side P kt)
      (CopyPadding.identifier D r.source.suffix x) D r.terminal.suffix k G x y := by
  classical
  simp only [genuineMean, rowSliceMean, CorrectionRowTask.Channel.retains, channels,
    hs, ht, semanticSide_grid, hr.2.1, hr.2.2]

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Matrix Matrix.HierarchyParams Cslib.RowCompression Cslib.Probability
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- Identification with the already approved actual normalized request, including its
split terminal coordinate and inherited source/terminal suffixes. -/
lemma genuineNormalizedRecipe_eq_request {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (D : ZMod P) (r : HierarchyTask.Request q (Fin J) (ZMod P)) (hr : Admissible r)
    (ks kt k : ℕ) (hs : r.source.rate = rate ks) (ht : r.usage.rate = rate kt)
    (ha : r.terminal.rate = rate k) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x y : ZMod P) :
    genuineNormalizedRecipe HP r.source.role r.terminal.role (side P ks) (side P kt) D
      r.source.suffix r.terminal.suffix k G σ x y =
    normalizedRequest D id r HP.toHierarchyParams.atomCutoff HP.ρ HP.K (fun _ => G)
      (genuinePrep HP r.terminal.role D r.terminal.suffix k G) σ x y := by
  rw [normalizedRequest_formula D id r hr]
  simp only [id_eq]
  rw [request_genuineMean_eq HP D r hr ks kt k hs ht G x y]
  simp only [genuineNormalizedRecipe, retainedMask, CorrectionRowTask.Channel.retains, channels,
    ht, ha, semanticSide_grid, hr.2.1, hr.2.2, NormalizedRow.clip]
  congr 3
  congr 1
  ext z
  simp
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Matrix Cslib.RowCompression Cslib.Probability
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- The actual usage-masked normalized output of the real compression recursion.
Both the unmasked first row and its full terminal rank are preserved. -/
@[expose] noncomputable def actualNormalizedCapacity
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ η : ℝ)
    (t : Fin J) (Lt : ℕ) (D : ZMod P) (suffix : List (ZMod P)) (k m : ℕ) (n : ℕ → ℕ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (σ : Environment P J) (x y : ZMod P) : ℝ :=
  let S := ({z | retainedMask t (side P k) D suffix σ z} : Finset (ZMod P))
  let a := iterate S n (fun _ => HP.K)
    (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m
  if retainedMask t Lt D suffix σ y then
    NormalizedRow.output HP ζ (a.row y 0) (a.row y 1) (firstRank S HP.K a.defaultValue a.row) else 0

open Classical in
/-- Actual normalized compressed-output fourth moment. The only stochastic hypotheses are
clipped slope-one conditional mean envelopes and 64^-d row-noise budgets on their proper
masks. The genuine preparatory mean, heavy rarity, final/preloss and false charge are derived.
Cap-free sharp comparison is reused; no true-entry cap is required. Lower-child induction is
  separate. -/
theorem actual_normalized_fourth_moment_capacity
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η) (hsmall : ζ ≤ scale / 2)
    (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ Cfixed : ℝ, 0 ≤ Cfixed ∧ ∀ η : ℝ, 0 < η → η ≤ scale → η ≤ 1 → η ≤ HP.θ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P J : ℕ) [Fact P.Prime] (s t : Fin J), t ≠ s → ∀ (Ls Lt : ℕ) (D : ZMod P),
      D ≠ 0 →
      ∀ (sourceSuffix suffix : List (ZMod P)) (H : Horizon P) (k : ℕ), k ≤ H.maxExponent →
      Lt ≤ side P k → ∀ (G : Matrix (ZMod P) (ZMod P) ℝ),
      (∀ x y, 0 ≤ G x y) → (∀ x, ∑ y, G x y ≤ (HP.k : ℝ) + 1) →
      ∀ (N u ε : ℝ), 0 ≤ N * u → 0 ≤ ε → ∀ m : ℕ, 0 < m →
      ∀ n : ℕ → ℕ, (∀ i < m, HP.K ≤ n i) →
      (∀ i < m, 2 ^ (64 * dyadicSlack m i) ≤ n i) →
      ∀ (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
        (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
        (B : Fin 2 → Matrix (ZMod P) (ZMod P) ℝ),
      (∀ ν x y, 0 ≤ B ν x y) →
      (∀ ν i, i < m → ∀ x y,
        |actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν i x y| ≤
          B ν x y * 2 ^ dyadicSlack m i) →
      (∀ ν, rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
        (retainedMask t (if ν = 0 then side P k else Lt) D suffix) (fun _ x y => B ν x y) ≤ ε ^ 4) →
      (∀ ν i, i < m → rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
        (retainedMask t (if ν = 0 then side P k else Lt) D suffix)
        (actualNoiseEntry s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν i) ≤
          (ε * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4) →
      (∀ i σ x y, ¬retainedMask t Lt D suffix σ y → actualPrefix Δ raw i σ x y 1 = 0) →
      rowNormPow 4 N u (retainedMask s Ls D sourceSuffix) (retainedMask t Lt D suffix)
        (fun σ x y => actualNormalizedCapacity HP ζ η t Lt D suffix k m n Δ raw σ x y ^ (4⁻¹ : ℝ) -
          genuineNormalizedRecipe HP s t Ls Lt D sourceSuffix suffix k G σ x y ^ (4⁻¹ : ℝ)) ≤ C * ε
 ^ 4 := by
  obtain ⟨Cf, hCf, hfloor⟩ := NormalizedRow.uniform_moment_capacity HP ζ hζ hs hmargin hcapscale
  refine ⟨Cf, hCf, ?_⟩
  intro η hη hηs hη1 hηθ
  obtain ⟨A, hA, hbound⟩ := hfloor η hη hηs hη1
  let M : ℝ := (HP.k : ℝ) + 1
  let T : ℝ := ((2 + 256 * M / η) * 2) / 63 + 2 * (7 / 9)
  have hT : 0 ≤ T := by dsimp only [T, M]; positivity
  let C := (128 * (HP.K : ℝ) * (A ^ 4 * (η / 511) ^ 4 + Cf ^ 4 * 2 ^ 4 + Cf ^ 4 * T ^ 4) +
    64 * (HP.K : ℝ) * (NormalizedRow.rangeBound HP) ^ 4 / η ^ 4 / 63) * 4 ^ 4
  refine ⟨C, by dsimp only [C]; positivity, ?_⟩
  intro P J _ s t hst Ls Lt D hD sourceSuffix suffix H k hk hLt G hG hmass N u ε hNu hε m hm n hn
    hnscale Δ raw B hB hμ hb hz hzero
  let X := retainedMask s Ls D sourceSuffix
  let Ya := retainedMask t (side P k) D suffix
  let Yt := retainedMask t Lt D suffix
  let truth := genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ
  have hsub (σ : Environment P J) (y : ZMod P) : Yt σ y → Ya σ y := by
    intro hy
    exact mem_retentionBox.mpr (fun a => (mem_retentionBox.mp hy a).trans_le hLt)
  have hmean (ν : Fin 2) (i : ℕ) (hi : i < m) : rowNormPow 4 N u X
      (retainedMask t (if ν = 0 then side P k else Lt) D suffix)
      (fun _ x y => actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν
        i x y) ≤
      (ε * 2 ^ dyadicSlack m i) ^ 4 := by
    have hh := row_mono_abs X (retainedMask t (if ν = 0 then side P k else Lt) D suffix) hNu
      (fun (_ : Environment P J) x y => actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix
        suffix k G ζ Δ raw ν i x y)
      (fun (_ : Environment P J) x y => (2 : ℝ) ^ dyadicSlack m i * B ν x y) (by
        intro σ x y _ _
        rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ dyadicSlack m i), abs_of_nonneg
          (hB ν x y)]
        simpa only [mul_comm] using hμ ν i hi x y)
    rw [row_const_mul X (retainedMask t (if ν = 0 then side P k else Lt) D suffix) N u (2 ^
      dyadicSlack
      m i) (fun (_ : Environment P J) x y => B ν x y)] at hh
    have hh' := hh.trans (mul_le_mul_of_nonneg_left (hb ν) (by positivity))
    simpa only [abs_of_nonneg (by positivity : (0 : ℝ) ≤ 2 ^ dyadicSlack m i), mul_pow, mul_comm]
      using hh'
  have hrow (i : ℕ) (hi : i < m) := raw_prefix_row_budget HP s t Ls (side P k) Lt D sourceSuffix
    suffix
    k G hG ζ Δ raw m i (hzero i) hsub hNu hε (fun ν => hmean ν i hi) (fun ν => hz ν i hi)
  have htail := integrated_actual_clipped_tail_capacity HP s t hst Ls Lt D hD sourceSuffix suffix
    H hk
    (hLt.trans (side_le P k)) G hG ζ hη hNu hmass m n (fun _ => HP.K) hnscale Δ raw
    (fun _ => ε) (fun _ => ε) (fun _ => hε) (fun _ => hε) B hB hμ hb
    (fun ν i hi => actualNoiseMax_budget s t Ls (side P k) Lt D sourceSuffix suffix k G hG Δ raw
      hNu ν i (hz ν i hi)) hzero
  have ht : vertexNormPow 4 N u X
      (actualClippedTail HP s t Ls Lt D sourceSuffix suffix k m η G ζ
        n (fun _ => HP.K) Δ raw) ≤ (T * (4 * ε)) ^ 4 := by
    have he : (((2 + 256 * M / η) * (ε + ε)) / 63 + (ε + ε) * (7 / 9)) = T * ε := by
      dsimp only [T]
      ring
    change _ ≤ (T * (4 * ε)) ^ 4
    apply htail.trans
    rw [show (((2 + 256 * ((HP.k : ℝ) + 1) / η) * (ε + ε)) / 63 + (ε + ε) * (7 / 9)) = T * ε from
      he]
    exact pow_le_pow_left₀ (mul_nonneg hT hε) (by nlinarith [mul_nonneg hT hε]) 4
  have hout := hbound N u hNu X Ya m hm n hnscale Δ raw truth hn
    (fun σ x y _ _ => div_nonneg (hG x y) (rate_pos k).le)
    (fun σ x y _ _ => by
      change |ζ * (if Yt σ y then genuineMean HP s t Ls Lt (CopyPadding.identifier D sourceSuffix
        x) D suffix k G x y else 0)| ≤ scale / 2
      split_ifs
      · rw [abs_mul, abs_of_pos hζ, abs_of_nonneg (genuineMean_range HP s t Ls Lt _ D suffix k G x
        y).1]
        exact (mul_le_of_le_one_right hζ.le (genuineMean_range HP s t Ls Lt _ D suffix k G x
          y).2).trans hsmall
      · simp only [mul_zero, abs_zero]; linarith)
    (fun j _ σ x y _ _ hy => by
      have hf := dyadicFloor_le_scale_div hη.le m j
      have hq := genuineMean_zero HP s t Ls Lt (CopyPadding.identifier D sourceSuffix x) D suffix
        k G x y (by
        change G x y / rate k ≤ dyadicFloor η m j / 4 at hy
        linarith)
      simp only [truth, genuineTarget, Fin.isValue, one_ne_zero, ↓reduceIte, hq, ite_self,
        mul_zero])
    (4 * ε) T (by positivity) hT hrow (by
      unfold actualClippedTail at ht
      dsimp only [actualClippedTail, meanFirstEvent, truth, genuineTarget, Ya, actualPrefix] at ht ⊢
      simpa only [Fin.isValue, one_ne_zero, ↓reduceIte] using ht)
  dsimp only at hout
  have hrestrict : rowNormPow 4 N u X Yt (fun σ x y =>
      actualNormalizedCapacity HP ζ η t Lt D suffix k m n Δ raw σ x y ^ (4⁻¹ : ℝ) -
      genuineNormalizedRecipe HP s t Ls Lt D sourceSuffix suffix k G σ x y ^ (4⁻¹ : ℝ)) ≤
    rowNormPow 4 N u X Ya (fun σ x y => stateRootError (NormalizedRow.output HP ζ) {z | Ya σ z} HP.K
      (iterate {z | Ya σ z} n (fun _ => HP.K)
        (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m) ⟨0, truth σ x⟩ y) := by
    rw [←row_mask_subset X Ya Yt hsub]
    apply row_mono_abs X Ya hNu
    intro σ x y _ _
    by_cases hy : Yt σ y
    · rw [ite_eq_left hy, genuine_recipe_identity HP hζ]
      simp only [actualNormalizedCapacity, hy, ↓reduceIte, stateRootError, truth, Yt, Ya]
      exact le_rfl
    · rw [ite_eq_right hy, abs_zero]
      exact abs_nonneg _
  apply hrestrict.trans
  convert hout using 1
  dsimp only [C]
  ring
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Cslib Cslib.RowCompression Matrix
open Classical in
/-- K is fixed with the hierarchy, before the environment, width and horizon.
The prefactor is part of the actual compression schedule. -/
@[expose] def compatibleCapacity (K m i : ℕ) : ℕ := (K + 1) * 2 ^ (64 * dyadicSlack m i)

open Classical in
/-- Both capacity conditions hold at every horizon, with no upper bound on K. -/
lemma compatibleCapacity_bounds (K m i : ℕ) :
    K ≤ compatibleCapacity K m i ∧ 2 ^ (64 * dyadicSlack m i) ≤ compatibleCapacity K m i := by
  have hp : 1 ≤ 2 ^ (64 * dyadicSlack m i) := Nat.one_le_pow _ _ (by decide)
  constructor
  · exact (Nat.le_succ K).trans (Nat.le_mul_of_pos_right _ (by omega))
  · exact Nat.le_mul_of_pos_left _ (by omega)

open Classical in
/-- The compatible capacities replace the fixed schedule in the actual output. -/
@[expose] noncomputable def actualNormalizedCompatible {P J : ℕ} [Fact P.Prime]
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (ζ η : ℝ)
    (t : Fin J) (Lt : ℕ) (D : ZMod P) (suffix : List (ZMod P)) (k m : ℕ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (σ : Environment P J) (x y : ZMod P) : ℝ :=
  actualNormalizedCapacity HP ζ η t Lt D suffix k m (compatibleCapacity HP.K m) Δ raw σ x y
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Matrix Cslib.RowCompression Cslib.Probability
open scoped BigOperators
open Classical in
/-- Actual normalized-output fourth moment for arbitrary fixed hierarchy K.
The compatible capacities are used in the iterate itself. The endpoint row-noise
contracts and positive horizon are explicit; lower-child induction is separate. -/
theorem actual_normalized_fourth_moment_compatible
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    {ζ scale : ℝ} (hζ : 0 < ζ) (hs : 0 < scale) (hmargin : scale ≤ HP.η) (hsmall : ζ ≤ scale / 2)
    (hcapscale : scale ≤ HP.toHierarchyParams.atomCap / 10000) :
    ∃ Cfixed : ℝ, 0 ≤ Cfixed ∧ ∀ η : ℝ, 0 < η → η ≤ scale → η ≤ 1 → η ≤ HP.θ →
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (P J : ℕ) [Fact P.Prime] (s t : Fin J), t ≠ s → ∀ (Ls Lt : ℕ) (D : ZMod P),
      D ≠ 0 →
      ∀ (sourceSuffix suffix : List (ZMod P)) (H : Horizon P) (k : ℕ), k ≤ H.maxExponent →
      Lt ≤ side P k → ∀ (G : Matrix (ZMod P) (ZMod P) ℝ),
      (∀ x y, 0 ≤ G x y) → (∀ x, ∑ y, G x y ≤ (HP.k : ℝ) + 1) →
      ∀ (N u ε : ℝ), 0 ≤ N * u → 0 ≤ ε → ∀ m : ℕ, 0 < m →
      ∀ (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
        (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
        (B : Fin 2 → Matrix (ZMod P) (ZMod P) ℝ),
      (∀ ν x y, 0 ≤ B ν x y) →
      (∀ ν i, i < m → ∀ x y,
        |actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν i x y| ≤
          B ν x y * 2 ^ dyadicSlack m i) →
      (∀ ν, rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
        (retainedMask t (if ν = 0 then side P k else Lt) D suffix) (fun _ x y => B ν x y) ≤ ε ^ 4) →
      (∀ ν i, i < m → rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
        (retainedMask t (if ν = 0 then side P k else Lt) D suffix)
        (actualNoiseEntry s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν i) ≤
          (ε * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4) →
      (∀ i σ x y, ¬retainedMask t Lt D suffix σ y → actualPrefix Δ raw i σ x y 1 = 0) →
      rowNormPow 4 N u (retainedMask s Ls D sourceSuffix) (retainedMask t Lt D suffix)
        (fun σ x y => actualNormalizedCompatible HP ζ η t Lt D suffix k m Δ raw σ x y ^ (4⁻¹ : ℝ) -
          genuineNormalizedRecipe HP s t Ls Lt D sourceSuffix suffix k G σ x y ^ (4⁻¹ : ℝ)) ≤ C * ε
 ^ 4 := by
  obtain ⟨Cf, hCf, hfloor⟩ := actual_normalized_fourth_moment_capacity HP hζ hs hmargin hsmall
    hcapscale
  refine ⟨Cf, hCf, ?_⟩
  intro η hη hηs hη1 hηθ
  obtain ⟨C, hC, hbound⟩ := hfloor η hη hηs hη1 hηθ
  refine ⟨C, hC, ?_⟩
  intro P J _ s t hst Ls Lt D hD sourceSuffix suffix H k hk hLt G hG hmass N u ε hNu hε m hm Δ raw
    B hB hμ hb hz hzero
  exact hbound P J s t hst Ls Lt D hD sourceSuffix suffix H k hk hLt G hG hmass N u ε hNu hε m hm
    (compatibleCapacity HP.K m) (fun i _ => (compatibleCapacity_bounds HP.K m i).1)
    (fun i _ => (compatibleCapacity_bounds HP.K m i).2) Δ raw B hB hμ hb hz hzero
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
