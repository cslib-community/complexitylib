/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.NormalizedAtomRows.MeanTail
public import CslibFrontier.Computability.LogSpaceDerandomization.RowCompression.FourthMoment

/-!
# Full-rank first means and narrow-usage second means

The actual H4 environment and uncentered hierarchy decoder are preserved. This fourth-moment
adaptation of §8.2, Proposition 8.5 (printed pp. 45–49), of [OpenAI2026LogSpace], revision
7ef5c0cc, retains explicit lower-child contracts; it does not establish recursive induction
or native resource bounds. Christian Reitwiessner supplied the H4 specialization; the
compression and norm proof patterns are adapted from Samuel Schlesinger.
-/

public section
open Matrix.FourthRootHierarchyParams Matrix.HierarchyParams.H4RankEnvironment
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- Actual conditional means: first on full terminal rank, second on narrow usage. -/
@[expose] noncomputable def twoMaskMean (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P)
    (sourceSuffix suffix : List (ZMod P))
    (F : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (x y : ZMod P) (ν : Fin 2) : ℝ :=
  rowSliceMean (retainedMask s Ls D sourceSuffix)
    (retainedMask t (if ν = 0 then La else Lt) D suffix) (fun σ x y => F σ x y ν) x y

open Classical in
/-- Genuine target with unmasked first input and zero-extended uncentered preparatory mean. -/
@[expose] noncomputable def genuineTarget (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ)
    (σ : Environment P J) (x y : ZMod P) (ν : Fin 2) : ℝ :=
  if ν = 0 then G x y / rate k else ζ * (if retainedMask t Lt D suffix σ y then
    genuineMean HP s t Ls Lt (CopyPadding.identifier D sourceSuffix x) D suffix k G x y else 0)

open Classical in
/-- Checked actual H4 pointwise client. The first mean uses rank La, never usage Lt.
Outside usage, the second raw prefix and target are both zero. -/
theorem actual_two_mask_clipped_split
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (F : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, ¬retainedMask t Lt D suffix σ y → F σ x y 1 = 0)
    (σ : Environment P J) (x y : ZMod P) :
    let a := twoMaskMean s t Ls La Lt D sourceSuffix suffix F x y
    let d := G x y / rate k
    let v := ζ * genuineMean HP s t Ls Lt (CopyPadding.identifier D sourceSuffix x) D suffix k G x y
    clippedError (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 0)
      (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 1) (F σ x y) ≤
      min 1 (|a 0 - d| / (1 + d)) +
      (if retainedMask t Lt D suffix σ y then min 1 |a 1 - v| else 0) +
      |F σ x y 0 - a 0| / (1 + d) +
      (if retainedMask t Lt D suffix σ y then |F σ x y 1 - a 1| else 0) := by
  dsimp only
  have hd := div_nonneg (hG x y) (rate_pos k).le
  by_cases hy : retainedMask t Lt D suffix σ y
  · simpa only [genuineTarget, Fin.isValue, ↓reduceIte, one_ne_zero, hy] using
      clipped_two_mean_split (F σ x y)
        (twoMaskMean s t Ls La Lt D sourceSuffix suffix F x y 0)
        (twoMaskMean s t Ls La Lt D sourceSuffix suffix F x y 1)
        (G x y / rate k)
        (ζ * genuineMean HP s t Ls Lt (CopyPadding.identifier D sourceSuffix x) D suffix k G x y) hd
  · have hh := clipped_two_mean_split (F σ x y)
        (twoMaskMean s t Ls La Lt D sourceSuffix suffix F x y 0) 0 (G x y / rate k) 0 hd
    simpa only [genuineTarget, Fin.isValue, ↓reduceIte, one_ne_zero, hy, hz σ x y hy,
      sub_self, abs_zero, min_eq_right (by norm_num : (0 : ℝ) ≤ 1), mul_zero, add_zero] using hh

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Cslib.RowCompression
open scoped BigOperators

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- Real conditional-walk prefixes on the usage slice, with telescoping increments and
zero initial second signal, satisfy the support premise of the actual clipped split. -/
theorem actual_walk_prefix_support {E : Type*} [Fintype E]
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (graphs : ℕ → ∀ x y, RotationMap
      (RetainedPairSlice (retainedMask s Ls D sourceSuffix) (retainedMask t Lt D suffix) x y) E)
    (times : ℕ → ZMod P → ZMod P → ℕ)
    (child : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (first : ℕ → Environment P J → ZMod P → ZMod P → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hzero : ∀ σ x y, raw σ x y 1 = 0)
    (σ : Environment P J) (x y : ZMod P) (hy : ¬retainedMask t Lt D suffix σ y) :
    let p := fun i σ x y => conditionalWalk (retainedMask s Ls D sourceSuffix)
      (retainedMask t Lt D suffix) (graphs i) (times i) (child i) σ x y
    let Δ := fun i y ν => if ν = 0 then first i σ x y else
      p (i + 1) σ x y - (if i=0 then 0 else p i σ x y)
    (∀ i, uncompressedRow Δ (raw σ x) (i + 1) y 1 = 0) ∧
    (∀ S n K ρ m, (iterate S n K ρ Δ ⟨0, raw σ x⟩ m).row y 1 = 0) := by
  dsimp only
  have hp (i : ℕ) := conditionalWalk_zero_off (retainedMask s Ls D sourceSuffix)
    (retainedMask t Lt D suffix) (graphs i) (times i) (child i) σ x y hy
  constructor
  · intro i
    have ht := uncompressed_second_telescope
      (fun j z => conditionalWalk (retainedMask s Ls D sourceSuffix)
        (retainedMask t Lt D suffix) (graphs j) (times j) (child j) σ x z)
      (fun j z => first j σ x z) (raw σ x) (hzero σ x) i y
    exact ht.trans (hp (i + 1))
  · intro S n K ρ m
    apply iterate_second_zero_off S n K ρ _ _ y (hzero σ x y) _ m
    intro i
    simp only [Fin.isValue, one_ne_zero, ↓reduceIte, hp, ite_self, sub_self]

open Classical in
/-- Explicit full-rank client for the four-max split, using the genuine target. -/
theorem actual_two_mask_row_max
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    (F : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, ¬retainedMask t Lt D suffix σ y → F σ x y 1 = 0)
    (σ : Environment P J) (x : ZMod P) :
    let a := twoMaskMean s t Ls La Lt D sourceSuffix suffix F x
    let d := fun y => G x y / rate k
    let v := fun y => ζ * genuineMean HP s t Ls Lt
      (CopyPadding.identifier D sourceSuffix x) D suffix k G x y
    kthLargest 1 {y | retainedMask t La D suffix σ y} (fun y =>
      clippedError (d y) (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 1) (F σ x
        y)) ≤
      kthLargest 1 {y | retainedMask t La D suffix σ y} (fun y => |min 1 (|a y 0 - d y| / (1 + d
        y))|) +
      kthLargest 1 {y | retainedMask t Lt D suffix σ y} (fun y => |min 1 (abs (a y 1 - v y))|) +
      kthLargest 1 {y | retainedMask t La D suffix σ y} (fun y => abs (|F σ x y 0 - a y 0| / (1 + d
        y))) +
      kthLargest 1 {y | retainedMask t Lt D suffix σ y} (fun y => abs (abs (F σ x y 1 - a y 1)))
        := by
  dsimp only
  apply full_rank_four_max
  intro y _
  have hh := actual_two_mask_clipped_split HP s t Ls La Lt D sourceSuffix suffix k G hG ζ F hz σ x y
  dsimp only at hh
  have hd : 0 ≤ G x y / rate k := div_nonneg (hG x y) (rate_pos k).le
  have hb : 0 ≤ min 1 (|twoMaskMean s t Ls La Lt D sourceSuffix suffix F x y 0 - G x y / rate k| /
    (1 + G x y / rate k)) := le_min (by norm_num) (by positivity)
  have hc : 0 ≤ min 1 |twoMaskMean s t Ls La Lt D sourceSuffix suffix F x y 1-
    ζ * genuineMean HP s t Ls Lt (CopyPadding.identifier D sourceSuffix x) D suffix k G x y| :=
    le_min (by norm_num) (abs_nonneg _)
  simpa only [genuineTarget, Fin.isValue, ↓reduceIte, mem_filter, mem_univ, true_and,
    abs_of_nonneg hb, abs_of_nonneg hc, abs_of_nonneg (div_nonneg (abs_nonneg _) (by linarith : 0
      ≤ 1 + G x y / rate k)),
    abs_abs] using hh

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- Actual prefix array, shared by both conditioning slices. -/
@[expose] noncomputable def actualPrefix
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ) (i : ℕ) :=
  fun σ x y => uncompressedRow (Δ σ x) (raw σ x) (i + 1) y

open Classical in
/-- Clipped deterministic discrepancy on the appropriate actual slice; the second
true signal is unmasked here because this coordinate is used only on usage. -/
@[expose] noncomputable def actualClippedMean
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (ν : Fin 2) (i : ℕ) (x y : ZMod P) : ℝ :=
  let a := twoMaskMean s t Ls La Lt D sourceSuffix suffix (actualPrefix Δ raw i) x y ν
  if ν = 0 then min 1 (|a - G x y / rate k| / (1 + G x y / rate k)) else
    min 1 |a - ζ * genuineMean HP s t Ls Lt (CopyPadding.identifier D sourceSuffix x) D suffix k G
      x y|

open Classical in
/-- Same-environment uncentered noise maximum. The first is relative and full-rank;
the second is absolute and usage-only. No rarity factor is applied to either. -/
@[expose] noncomputable def actualNoiseMax
    (s t : Fin J) (Ls La Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (ν : Fin 2) (i : ℕ) (σ : Environment P J) (x : ZMod P) : ℝ :=
  kthLargest 1 {y | retainedMask t (if ν = 0 then La else Lt) D suffix σ y} (fun y =>
    |(actualPrefix Δ raw i) σ x y ν-
      twoMaskMean s t Ls La Lt D sourceSuffix suffix (actualPrefix Δ raw i) x y ν| /
      (if ν = 0 then 1 + G x y / rate k else 1))

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- Actual two-scope noise tails, using absolute prefix budgets in one environment.
The relative first normalization is already included in actualNoiseMax. -/
theorem integrated_two_mask_noise
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k m : ℕ) (η : ℝ) (n K : ℕ → ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    {N u : ℝ} (hNu : 0 ≤ N * u) (ε : Fin 2 → ℝ) (hε : ∀ ν, 0 ≤ ε ν)
    (hbudget : ∀ ν i, i < m → vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν i) ≤
      (ε ν * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4) :
    let tail := fun ν σ x => firstOverflowNoiseTail {y | retainedMask t (side P k) D suffix σ y}
      n K (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m (fun i => (28 : ℝ) ^ (m - i))
      (fun i => actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν i σ x)
    vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix) (fun σ x => tail 0 σ x + tail 1 σ x) ≤
      ((ε 0 + ε 1) * (7 / 9)) ^ 4 := by
  dsimp only
  have hh (ν : Fin 2) := correlated_noise_tail s t Ls D sourceSuffix suffix k m η n K Δ raw
    hNu (hε ν) (actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν)
    (fun _ _ _ _ _ => kthLargest_nonneg) (hbudget ν)
  have hsum := vertex_add_budget (retainedMask s Ls D sourceSuffix) hNu
    (mul_nonneg (hε 0) (by norm_num : (0 : ℝ) ≤ 7 / 9))
    (mul_nonneg (hε 1) (by norm_num : (0 : ℝ) ≤ 7 / 9)) _ _ (hh 0) (hh 1)
  convert hsum using 1; ring

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- Integrated heavy-event mean tail on BOTH scopes. Rarity is separately derived on the
rank-conditioned and usage-conditioned H4 slices, using the same actual compression masks. -/
theorem integrated_two_mask_clipped_means_capacity
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ) (D : ZMod P) (hD : D ≠ 0)
    (sourceSuffix suffix : List (ZMod P)) (H : Horizon P)
    {k : ℕ} (hk : k ≤ H.maxExponent) (hLt : Lt ≤ P)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    {η M N u : ℝ} (hη : 0 < η) (hNu : 0 ≤ N * u)
    (hmass : ∀ x, ∑ y, G x y ≤ M) (m : ℕ) (n K : ℕ → ℕ) (hn : ∀ j < m, 2 ^ (64 * dyadicSlack m j)
      ≤ n j)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (ε : Fin 2 → ℝ) (hε : ∀ ν, 0 ≤ ε ν)
    (B : Fin 2 → Matrix (ZMod P) (ZMod P) ℝ) (hB : ∀ ν x y, 0 ≤ B ν x y)
    (hμ : ∀ ν i, i < m → ∀ x y,
      |actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν i x y| ≤
        B ν x y * 2 ^ dyadicSlack m i)
    (hbudget : ∀ ν, rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (retainedMask t (if ν = 0 then side P k else Lt) D suffix) (fun _ x y => B ν x y) ≤ (ε ν) ^
        4) :
    let tail := fun ν σ x => ∑ j ∈ range m,
      if meanFirstEvent t D suffix k m j η G n K Δ raw σ x then
        meanRowTail t (if ν = 0 then side P k else Lt) D suffix m j
          (actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν) σ x else 0
    vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix) (fun σ x => tail 0 σ x + tail 1 σ x) ≤
      (((2 + 256 * M / η) * (ε 0 + ε 1)) / 63) ^ 4 := by
  dsimp only
  have hM : 0 ≤ M := (sum_nonneg (fun y _ => hG 0 y)).trans (hmass 0)
  have hC : 0 ≤ 2 + 256 * M / η := by positivity
  have hh (ν : Fin 2) := integrated_mean_tail_capacity s t hst Ls
    (if ν = 0 then side P k else Lt) D hD sourceSuffix suffix H hk
    (by split_ifs
        · exact side_le P k
        · exact hLt) G hG hη (hε ν) hNu hmass m n K hn Δ raw
    (actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν)
    (B ν) (hB ν) (hμ ν) (hbudget ν)
  have hh' := vertex_add_budget (retainedMask s Ls D sourceSuffix) hNu
    (mul_nonneg (mul_nonneg hC (hε 0)) (by norm_num : (0 : ℝ) ≤ 1 / 63))
    (mul_nonneg (mul_nonneg hC (hε 1)) (by norm_num : (0 : ℝ) ≤ 1 / 63)) _ _ (hh 0) (hh 1)
  convert hh' using 1; ring

open Classical in
/-- Combined scope-correct envelope: clipped deterministic means get rarity, correlated
noise does not. Constants are independent of row width, horizon and vertex normalization. -/
theorem integrated_two_mask_envelope_capacity
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ) (D : ZMod P) (hD : D ≠ 0)
    (sourceSuffix suffix : List (ZMod P)) (H : Horizon P)
    {k : ℕ} (hk : k ≤ H.maxExponent) (hLt : Lt ≤ P)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y) (ζ : ℝ)
    {η M N u : ℝ} (hη : 0 < η) (hNu : 0 ≤ N * u)
    (hmass : ∀ x, ∑ y, G x y ≤ M) (m : ℕ) (n K : ℕ → ℕ) (hn : ∀ j < m, 2 ^ (64 * dyadicSlack m j)
      ≤ n j)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (εμ εz : Fin 2 → ℝ) (hεμ : ∀ ν, 0 ≤ εμ ν) (hεz : ∀ ν, 0 ≤ εz ν)
    (B : Fin 2 → Matrix (ZMod P) (ZMod P) ℝ) (hB : ∀ ν x y, 0 ≤ B ν x y)
    (hμ : ∀ ν i, i < m → ∀ x y,
      |actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν i x y| ≤
        B ν x y * 2 ^ dyadicSlack m i)
    (hbudget : ∀ ν, rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (retainedMask t (if ν = 0 then side P k else Lt) D suffix) (fun _ x y => B ν x y) ≤ (εμ ν) ^
        4)
    (hzbudget : ∀ ν i, i < m → vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν i) ≤
      (εz ν * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4) :
    let mt := fun ν σ x => ∑ j ∈ range m,
      if meanFirstEvent t D suffix k m j η G n K Δ raw σ x then
        meanRowTail t (if ν = 0 then side P k else Lt) D suffix m j
          (actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν) σ x else 0
    let zt := fun ν σ x => firstOverflowNoiseTail {y | retainedMask t (side P k) D suffix σ y}
      n K (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m (fun i => (28 : ℝ) ^ (m - i))
      (fun i => actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν i σ x)
    vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (fun σ x => (mt 0 σ x + mt 1 σ x) + (zt 0 σ x + zt 1 σ x)) ≤
      (((2 + 256 * M / η) * (εμ 0 + εμ 1)) / 63 + (εz 0 + εz 1) * (7 / 9)) ^ 4 := by
  dsimp only
  have hM : 0 ≤ M := (sum_nonneg (fun y _ => hG 0 y)).trans (hmass 0)
  have hm0 := hεμ 0
  have hm1 := hεμ 1
  have hz0 := hεz 0
  have hz1 := hεz 1
  exact vertex_add_budget (retainedMask s Ls D sourceSuffix) hNu (by positivity) (by positivity) _ _
    (integrated_two_mask_clipped_means_capacity HP s t hst Ls Lt D hD sourceSuffix suffix H hk hLt
      G hG ζ hη hNu hmass m n K hn Δ raw εμ hεμ B hB hμ hbudget)
    (integrated_two_mask_noise s t Ls Lt D sourceSuffix suffix k m η _ K G Δ raw hNu εz hεz
      hzbudget)


end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
