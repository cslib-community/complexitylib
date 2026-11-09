/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.NormalizedAtomRows.TwoMask

/-!
# Integrated actual full-rank clipped tails

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
/-- Full-rank clipped error tail on actual heavy first overflows. -/
@[expose] noncomputable def actualClippedTail
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k m : ℕ) (η : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ) (ζ : ℝ) (n K : ℕ → ℕ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (σ : Environment P J) (x : ZMod P) : ℝ :=
  ∑ j ∈ range m, if meanFirstEvent t D suffix k m j η G n K Δ raw σ x then
    ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * kthLargest 1 {y | retainedMask t (side P k) D suffix σ y}
      (fun y => clippedError (G x y / rate k)
        (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 1)
        (actualPrefix Δ raw i σ x y)) else 0

open Classical in
lemma actual_tail_le_envelope
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (Ls Lt : ℕ) (D : ZMod P) (sourceSuffix suffix : List (ZMod P))
    (k m : ℕ) (η : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (ζ : ℝ) (n K : ℕ → ℕ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ i σ x y, ¬retainedMask t Lt D suffix σ y → actualPrefix Δ raw i σ x y 1 = 0)
    (σ : Environment P J) (x : ZMod P) :
    let mt := fun ν => ∑ j ∈ range m,
      if meanFirstEvent t D suffix k m j η G n K Δ raw σ x then
        meanRowTail t (if ν = 0 then side P k else Lt) D suffix m j
          (actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw ν) σ x else 0
    let zt := fun ν => firstOverflowNoiseTail {y | retainedMask t (side P k) D suffix σ y}
      n K (dyadicFloor η m) (Δ σ x) ⟨0, raw σ x⟩ m (fun i => (28 : ℝ) ^ (m - i))
      (fun i => actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw ν i σ x)
    actualClippedTail HP s t Ls Lt D sourceSuffix suffix k m η G ζ n K Δ raw σ x ≤
      (mt 0 + mt 1) + (zt 0 + zt 1) := by
  dsimp only
  unfold actualClippedTail meanRowTail firstOverflowNoiseTail
  rw [←sum_add_distrib, ←sum_add_distrib, ←sum_add_distrib]
  apply sum_le_sum
  intro j _
  by_cases he : meanFirstEvent t D suffix k m j η G n K Δ raw σ x
  · have ho := he.1
    simp only [he, ho, ↓reduceIte, Fin.isValue, one_ne_zero]
    rw [←sum_add_distrib, ←sum_add_distrib, ←sum_add_distrib]
    apply sum_le_sum
    intro i _
    have hh := actual_two_mask_row_max HP s t Ls (side P k) Lt D sourceSuffix suffix k G hG ζ
      (actualPrefix Δ raw i) (hz i) σ x
    dsimp only at hh
    have hd (y : ZMod P) : 0 ≤ G x y / rate k := div_nonneg (hG x y) (rate_pos k).le
    have hden (y : ZMod P) : |1 + G x y / rate k| = 1 + G x y / rate k :=
      abs_of_pos (by linarith [hd y])
    have hh' : kthLargest 1 {y | retainedMask t (side P k) D suffix σ y}
        (fun y => clippedError (G x y / rate k)
          (genuineTarget HP s t Ls Lt D sourceSuffix suffix k G ζ σ x y 1)
          (actualPrefix Δ raw i σ x y)) ≤
      kthLargest 1 {y | retainedMask t (side P k) D suffix σ y}
        (fun y => |actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw 0 i
          x y|) +
      kthLargest 1 {y | retainedMask t Lt D suffix σ y}
        (fun y => |actualClippedMean HP s t Ls (side P k) Lt D sourceSuffix suffix k G ζ Δ raw 1 i
          x y|) +
      actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw 0 i σ x +
      actualNoiseMax s t Ls (side P k) Lt D sourceSuffix suffix k G Δ raw 1 i σ x := by
      simpa only [actualClippedMean, actualNoiseMax, Fin.isValue, one_ne_zero, ↓reduceIte,
        div_one, abs_div, abs_abs, hden] using hh
    have hm := mul_le_mul_of_nonneg_left hh' (by positivity : 0 ≤ (28 : ℝ) ^ (m - i))
    linarith
  · simp only [he, ↓reduceIte, zero_add]
    apply add_nonneg <;> split_ifs
    all_goals first
      | exact le_rfl
      | exact sum_nonneg fun i _ => mul_nonneg (by positivity) kthLargest_nonneg

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- Actual full-rank clipped prefix tail with rank/usage rarity separated. This is a
compression input tail, not yet the normalized compressed-output moment theorem. -/
theorem integrated_actual_clipped_tail_capacity
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
      (εz ν * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4)
    (hz : ∀ i σ x y, ¬retainedMask t Lt D suffix σ y → actualPrefix Δ raw i σ x y 1 = 0) :
    vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (actualClippedTail HP s t Ls Lt D sourceSuffix suffix k m η G ζ n K Δ raw) ≤
      (((2 + 256 * M / η) * (εμ 0 + εμ 1)) / 63 + (εz 0 + εz 1) * (7 / 9)) ^ 4 := by
  have hb := integrated_two_mask_envelope_capacity HP s t hst Ls Lt D hD sourceSuffix suffix H hk
    hLt
    G hG ζ hη hNu hmass m n K hn Δ raw εμ εz hεμ hεz B hB hμ hbudget hzbudget
  dsimp only at hb ⊢
  apply le_trans (vertex_mono_nonneg (retainedMask s Ls D sourceSuffix) hNu _ _ ?_ ?_) hb
  · intro σ x
    unfold actualClippedTail
    apply sum_nonneg
    intro j _
    split_ifs
    · exact sum_nonneg fun i _ => mul_nonneg (by positivity) kthLargest_nonneg
    · exact le_rfl
  · intro σ x
    exact actual_tail_le_envelope HP s t Ls Lt D sourceSuffix suffix k m η G hG ζ _ K Δ raw hz σ x

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
