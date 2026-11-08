/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.MeanEvent
public import Complexity.Foundations.Analysis.RowCompression.MomentSchedule

/-!
# Summable actual mean tails at arbitrary capacities

The actual H4 environment and uncentered hierarchy decoder are preserved. This fourth-moment
adaptation of §8.2, Proposition 8.5 (printed pp. 45–49), of [OpenAI2026LogSpace], revision
7ef5c0cc, retains explicit lower-child contracts; it does not establish recursive induction
or native resource bounds. Christian Reitwiessner supplied the H4 specialization; the
compression and norm proof patterns are adapted from Samuel Schlesinger.
-/

public section
open Matrix.FourthRootHierarchyParams Matrix.HierarchyParams.H4RankEnvironment

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- Actual narrower endpoint usage mask; rank sampling remains at the terminal rate. -/
@[expose] noncomputable def retainedMask (t : Fin J) (Lt : ℕ) (D : ZMod P) (suffix : List (ZMod P))
    (σ : Environment P J) (y : ZMod P) : Prop :=
  frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y)

open Classical in
/-- Sum of the raw-prefix row maxima, allowing a different maximizing endpoint at each prefix. -/
@[expose] noncomputable def meanRowTail (t : Fin J) (Lt : ℕ) (D : ZMod P) (suffix : List (ZMod P))
    (m j : ℕ) (μ : ℕ → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x : ZMod P) : ℝ :=
  ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
    kthLargest 1 {y | retainedMask t Lt D suffix σ y} (fun y => |μ i x y|)

open Classical in
/-- A common deterministic endpoint envelope controls the sum of adaptively chosen row maxima. -/
lemma meanRowTail_le (t : Fin J) (Lt : ℕ) (D : ZMod P) (suffix : List (ZMod P))
    (m j : ℕ) (hj : j < m) (μ : ℕ → Matrix (ZMod P) (ZMod P) ℝ)
    (B : Matrix (ZMod P) (ZMod P) ℝ) (hB : ∀ x y, 0 ≤ B x y)
    (hμ : ∀ i < m, ∀ x y, |μ i x y| ≤ B x y * 2 ^ dyadicSlack m i)
    (σ : Environment P J) (x : ZMod P) :
    meanRowTail t Lt D suffix m j μ σ x ≤ (128 : ℝ) ^ dyadicSlack m j *
      kthLargest 1 {y | retainedMask t Lt D suffix σ y} (fun y => |B x y|) := by
  let S := ({y | retainedMask t Lt D suffix σ y} : Finset (ZMod P))
  let b := kthLargest 1 S (fun y => |B x y|)
  have hb : 0 ≤ b := kthLargest_nonneg
  have hy (y : ZMod P) (hy : y ∈ S) : B x y ≤ b := by
    by_cases hzero : B x y = 0
    · simpa only [hzero] using hb
    · have hp : 0 < B x y := lt_of_le_of_ne (hB x y) (Ne.symm hzero)
      apply (le_kthLargest_iff (by norm_num : 0 < 1) hp).mpr
      exact card_pos.mpr ⟨y, mem_filter.mpr ⟨hy, by rw [abs_of_nonneg (hB x y)]⟩⟩
  have ht := mean_tail_growth hb m j hj
    (fun i => kthLargest 1 S (fun y => |μ i x y|)) (fun i _ hi =>
      kthLargest_le (mul_nonneg hb (by positivity)) (fun y hy' =>
        (hμ i hi x y).trans (mul_le_mul_of_nonneg_right (hy y hy') (by positivity))))
  exact ht.trans_eq (mul_comm _ _)

open Classical in
/-- The actual first-overflow mask, intersected with the genuine first-channel heavy event.
No rare-event discount for correlated noise is built into this definition. -/
@[expose] noncomputable def meanFirstEvent (t : Fin J) (D : ZMod P) (suffix : List (ZMod P))
    (k m j : ℕ) (η : ℝ) (G : Matrix (ZMod P) (ZMod P) ℝ)
    (n K : ℕ → ℕ) (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (σ : Environment P J) (x : ZMod P) : Prop :=
  IsFirstOverflow {y | retainedMask t (side P k) D suffix σ y} n K (dyadicFloor η m)
    (Δ σ x) ⟨0, raw σ x⟩ j ∧
  heavyCountEvent (retainedMask t (side P k) D suffix) univ
    (fun y => G x y / rate k) (dyadicFloor η m j) (n j) σ

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- Actual rarity-weighted first-overflow deterministic mean tail. Means are deterministic
conditional discrepancies; their lower-child derivation remains an input. The row maximum
may choose an endpoint using the same environment as the overflow event. -/
theorem integrated_mean_tail_capacity
    (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ) (D : ZMod P) (hD : D ≠ 0)
    (sourceSuffix suffix : List (ZMod P)) (H : Horizon P)
    {k : ℕ} (hk : k ≤ H.maxExponent) (hLt : Lt ≤ P)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {η M ε N u : ℝ} (hη : 0 < η) (hε : 0 ≤ ε) (hNu : 0 ≤ N * u)
    (hmass : ∀ x, ∑ y, G x y ≤ M)
    (m : ℕ) (n K : ℕ → ℕ) (hn : ∀ j < m, 2 ^ (64 * dyadicSlack m j) ≤ n j)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (μ : ℕ → Matrix (ZMod P) (ZMod P) ℝ) (B : Matrix (ZMod P) (ZMod P) ℝ)
    (hB : ∀ x y, 0 ≤ B x y)
    (hμ : ∀ i < m, ∀ x y, |μ i x y| ≤ B x y * 2 ^ dyadicSlack m i)
    (hbudget : rowNormPow 4 N u (retainedMask s Ls D sourceSuffix)
      (retainedMask t Lt D suffix) (fun _ x y => B x y) ≤ ε ^ 4) :
    vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix) (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent t D suffix k m j η G n K Δ raw σ x then
        meanRowTail t Lt D suffix m j μ σ x
        else 0) ≤ (((2 + 256 * M / η) * ε) * (1 / 63)) ^ 4 := by
  let X := retainedMask s Ls D sourceSuffix
  let Yt := retainedMask t Lt D suffix
  let C := 2 + 256 * M / η
  have hM : 0 ≤ M := (sum_nonneg (fun y _ => hG 0 y)).trans (hmass 0)
  have hC : 2 ≤ C := by
    dsimp [C]
    linarith [div_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 256) hM) hη.le]
  have hC0 : 0 ≤ C := (by norm_num : (0 : ℝ) ≤ 2).trans hC
  have hCC : C ≤ C ^ 4 := by
    have h1 : C ≤ C ^ 2 := by nlinarith
    have h2 : C ^ 2 ≤ C ^ 4 := by nlinarith [sq_nonneg (C ^ 2 - 1)]
    exact h1.trans h2
  let f := fun j σ x => if meanFirstEvent t D suffix k m j η G n K Δ raw σ x then
    meanRowTail t Lt D suffix m j μ σ x else 0
  have hterm (j : ℕ) (hj : j < m) : vertexNormPow 4 N u X (f j) ≤
      (C * ε * (1 / 64 : ℝ) ^ dyadicSlack m j) ^ 4 := by
    let q := (2 + 256 * M / dyadicFloor η m j) / (n j : ℝ)
    have hq : 0 ≤ q := by
      have hf := dyadicFloor_pos hη m j
      dsimp [q]
      positivity
    have hr (x y : ZMod P) :
        (#{σ : Environment P J | X σ x ∧ Yt σ y ∧ meanFirstEvent t D suffix k m j η G n K Δ raw σ
          x}:ℝ) ≤
        q * #{σ : Environment P J | X σ x ∧ Yt σ y} := by
      have hc := actual_rarity_card s t hst Ls Lt D hD sourceSuffix suffix H hk hLt G hG hmass
        (dyadicFloor_pos hη m j) (lt_of_lt_of_le (by positivity) (hn j hj)) x y
      have hsub : (
        {σ : Environment P J | X σ x ∧ Yt σ y ∧ meanFirstEvent t D suffix k m j η G n K Δ raw σ x}
          : Finset _) ⊆
        ({σ : Environment P J | X σ x ∧ Yt σ y ∧ heavyCountEvent (retainedMask t (side P k) D
          suffix)
          univ (fun y => G x y / rate k) (dyadicFloor η m j) (n j) σ} : Finset _) := by
          intro σ hσ
          have hh := (mem_filter.mp hσ).2
          exact mem_filter.mpr ⟨mem_univ _, hh.1, hh.2.1, hh.2.2.2⟩
      apply (Nat.cast_le.mpr (card_le_card hsub)).trans
      rw [show retainedMask t (side P k) D suffix =
        (fun (τ : Environment P J) w => frameRetains P 4 (side P k) (τ t)
          (CopyPadding.identifier D suffix w)) from rfl]
      simpa only [X, Yt, retainedMask, retainedMask, q] using hc
    let g := fun σ x => if meanFirstEvent t D suffix k m j η G n K Δ raw σ x then
      kthLargest 1 {y | Yt σ y} (fun y => |B x y|) else 0
    have ha := vertexNormPow_kthLargest_event_le (by norm_num : 4 ≠ 0) hNu hr B
    have hp : vertexNormPow 4 N u X (f j) ≤
        ((128 : ℝ) ^ dyadicSlack m j) ^ 4 * vertexNormPow 4 N u X g := by
      unfold vertexNormPow
      rw [←mul_assoc, mul_comm (((128 : ℝ) ^ dyadicSlack m j) ^ 4), mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hNu)
      rw [mul_expect]
      apply expect_le_expect
      intro σ _
      rw [mul_sum]
      apply sum_le_sum
      intro x _
      by_cases hevent : meanFirstEvent t D suffix k m j η G n K Δ raw σ x
      · have ht := meanRowTail_le t Lt D suffix m j hj μ B hB hμ σ x
        have hn : 0 ≤ meanRowTail t Lt D suffix m j μ σ x :=
          sum_nonneg fun i _ => mul_nonneg (by positivity) kthLargest_nonneg
        simp only [f, g, hevent, ↓reduceIte, abs_of_nonneg hn, abs_of_nonneg kthLargest_nonneg]
        have hh := pow_le_pow_left₀ hn ht 4
        simpa only [mul_pow] using hh
      · simp only [f, g, hevent, ↓reduceIte, abs_zero, zero_pow (by norm_num : 4 ≠ 0), mul_zero];
        exact le_rfl
    have hb := (mul_le_mul_of_nonneg_left (ha.trans (mul_le_mul_of_nonneg_left hbudget hq))
      (show 0 ≤ ((128 : ℝ) ^ dyadicSlack m j) ^ 4 by positivity))
    have hnum := mean_schedule_budget hη hM (ε := ε) m j
    have hncast : (2 : ℝ) ^ (64 * dyadicSlack m j) ≤ (n j : ℝ) := by exact_mod_cast hn j hj
    have hqle : q ≤ (2 + 256 * M / dyadicFloor η m j) / (2 : ℝ) ^ (64 * dyadicSlack m j) := by
      have hf := dyadicFloor_pos hη m j
      apply div_le_div_of_nonneg_left _ (by positivity) hncast
      positivity
    calc
      _ ≤ ((128 : ℝ) ^ dyadicSlack m j) ^ 4 * (q * ε ^ 4) := hp.trans hb
      _ = q * (ε * 128 ^ dyadicSlack m j) ^ 4 := by ring
      _ ≤ ((2 + 256 * M / dyadicFloor η m j) / (2 : ℝ) ^ (64 * dyadicSlack m j)) * (ε * 128 ^
        dyadicSlack m j) ^ 4 :=
        mul_le_mul_of_nonneg_right hqle (by positivity)
      _ ≤ C * ε ^ 4 * ((1 / 64 : ℝ) ^ dyadicSlack m j) ^ 4 := hnum
      _ ≤ (C * ε * (1 / 64 : ℝ) ^ dyadicSlack m j) ^ 4 := by
        have hh := mul_le_mul_of_nonneg_right hCC
          (show 0 ≤ ε ^ 4 * ((1 / 64 : ℝ) ^ dyadicSlack m j) ^ 4 by positivity)
        nlinarith [hh]
  have hs := vertexNormPow_sum_le_pow_sum (by norm_num : 4 ≠ 0) hNu (range m) f
    (fun _ => 1) (fun j => C * ε * (1 / 64 : ℝ) ^ dyadicSlack m j)
    (fun _ _ => by norm_num) (fun _ _ => by positivity) (fun j hj => hterm j (mem_range.mp hj))
  simp only [one_mul] at hs
  have hsum := sum_propagation_mul_dyadic_decay_le (C := 1) (q := (1 / 64 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) m
  norm_num only [one_pow, one_mul] at hsum
  have hsum' : ∑ j ∈ range m, C * ε * (1 / 64 : ℝ) ^ dyadicSlack m j ≤ C * ε * (1 / 63) := by
    rw [←mul_sum]
    exact mul_le_mul_of_nonneg_left hsum (by positivity)
  exact hs.trans (pow_le_pow_left₀ (sum_nonneg fun j _ => by positivity) hsum' 4)

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.RowCompression
variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- The correlated noise tail in the same actual terminal row and full environment.
Unlike deterministic mean tails, noise gets no heavy-event rarity discount. -/
theorem correlated_noise_tail (s t : Fin J) (Ls : ℕ) (D : ZMod P)
    (sourceSuffix suffix : List (ZMod P)) (k m : ℕ) (η : ℝ) (n K : ℕ → ℕ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    {N u ε : ℝ} (hNu : 0 ≤ N * u) (hε : 0 ≤ ε)
    (γ : ℕ → Environment P J → ZMod P → ℝ)
    (hγ : ∀ i < m, ∀ σ x, retainedMask s Ls D sourceSuffix σ x → 0 ≤ γ i σ x)
    (hbudget : ∀ i < m, vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix) (γ i) ≤
      (ε * (1 / 64 : ℝ) ^ dyadicSlack m i) ^ 4) :
    vertexNormPow 4 N u (retainedMask s Ls D sourceSuffix) (fun σ x =>
      firstOverflowNoiseTail {y | retainedMask t (side P k) D suffix σ y} n K (dyadicFloor η m)
        (Δ σ x) ⟨0, raw σ x⟩ m (fun i => (28 : ℝ) ^ (m - i)) (fun i => γ i σ x)) ≤
      (ε * (7 / 9)) ^ 4 := by
  have h := vertexNormPow_firstOverflowNoiseTail_le_dyadic_budget
    (fun σ (_x : ZMod P) => {y | retainedMask t (side P k) D suffix σ y})
    n K (dyadicFloor η m) Δ (fun σ x => ⟨0, raw σ x⟩) m (by norm_num : 4 ≠ 0)
    hNu (retainedMask s Ls D sourceSuffix) (C := 28) (q := (1 / 64 : ℝ))
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) hε γ hγ hbudget
  norm_num only [show (28 : ℝ) * (1 / 64) / (1 - 28 * (1 / 64)) = 7 / 9 by norm_num] at h
  exact h

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
