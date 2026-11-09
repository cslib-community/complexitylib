/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.HierarchyRankEnvironment
public import Complexity.Computability.LogSpaceDerandomization.DenseRowRecipes
public import Complexity.Computability.LogSpaceDerandomization.PolynomialAtomCutoffs
public import Complexity.Computability.LogSpaceDerandomization.HeavyCountRarity
public import Complexity.Computability.LogSpaceDerandomization.RowCompression.NoiseDecay

/-!
# Actual heavy-event mean charges

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
/-- Mixed-rate pair count on the actual independently source-conditioned slice.
No independence among endpoints of the terminal coordinate is assumed. -/
theorem source_mixed_pair (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ)
    (a b : ZMod P) (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (hLt : Lt ≤ P) {w : ZMod P} (hwb : w ≠ b) :
    (#{σ : Environment P J | frameRetains P 4 Ls (σ s) a ∧
      frameRetains P 4 Lt (σ t) b ∧ frameRetains P 4 (side P k) (σ t) w} : ℝ) ≤
    32 * rate k * #{σ : Environment P J |
      frameRetains P 4 Ls (σ s) a ∧ frameRetains P 4 Lt (σ t) b} := by
  classical
  have hi := dens_filter_pi_eval_and_pi_eval hst
    (fun A : FrameChannel P 4 1 => frameRetains P 4 Ls A a)
    (fun A : FrameChannel P 4 1 => frameRetains P 4 Lt A b ∧ frameRetains P 4 (side P k) A w)
  have hj := independent s t hst Ls Lt a b
  have hp := mixed_pair_density t H hk Lt hLt hwb
  have hc := dens_filter_pi_eval t (fun A : FrameChannel P 4 1 =>
    frameRetains P 4 Lt A b ∧ frameRetains P 4 (side P k) A w)
  have hd := dens_filter_pi_eval t (fun A : FrameChannel P 4 1 => frameRetains P 4 Lt A b)
  have hp' : (dens {A : FrameChannel P 4 1 |
      frameRetains P 4 Lt A b ∧ frameRetains P 4 (side P k) A w} : ℝ) ≤
      32 * rate k * dens {A : FrameChannel P 4 1 | frameRetains P 4 Lt A b} := by
    simpa only [hc, hd, and_comm] using hp
  suffices h : (dens {σ : Environment P J | frameRetains P 4 Ls (σ s) a ∧
      frameRetains P 4 Lt (σ t) b ∧ frameRetains P 4 (side P k) (σ t) w} : ℝ) ≤
      32 * rate k * dens {σ : Environment P J | frameRetains P 4 Ls (σ s) a ∧ frameRetains P 4 Lt
        (σ t) b} by
    have hh := card_filter_and_le_of_dens_le
      (A := fun (σ : Environment P J) => frameRetains P 4 Ls (σ s) a ∧ frameRetains P 4 Lt (σ t) b)
      (B := fun σ => frameRetains P 4 (side P k) (σ t) w)
      (q := 32 * rate k) (by simpa only [and_assoc, and_comm, and_left_comm] using h)
    simpa only [and_assoc] using hh
  have hh := mul_le_mul_of_nonneg_left hp'
    (show (0 : ℝ) ≤ dens {A : FrameChannel P 4 1 | frameRetains P 4 Ls A a} by positivity)
  have hiR := congrArg (fun q : ℚ≥0 => (q : ℝ)) hi
  have hjR := congrArg (fun q : ℚ≥0 => (q : ℝ)) hj
  simp only [NNRat.cast_mul] at hiR hjR
  rw [hiR, hjR]
  nlinarith

variable (HP : FourthRootHierarchyParams 16 1 16 32 8)
open Classical in
/-- Exact preparation evaluated on the full environment's terminal role. -/
@[expose] noncomputable def genuinePrep (t : Fin J) (D : ZMod P) (suffix : List (ZMod P))
    (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (σ : Environment P J) : Matrix (ZMod P) (ZMod P) ℝ :=
  DenseRowRecipe.preparation (polynomialPrepCutoff4 HP.θ) HP.ρ HP.K (rate k)
    (fun (τ : Environment P J) v => frameRetains P 4 (side P k) (τ t) (CopyPadding.identifier D
      suffix v)) G σ

open Classical in
/-- This is the actual joint source/usage conditional mean, not a second copy of the environment. -/
@[expose] noncomputable def genuineMean (s t : Fin J) (Ls Lt : ℕ) (a D : ZMod P)
    (suffix : List (ZMod P)) (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) : ℝ :=
  rowSliceMean (fun (σ : Environment P J) _ => frameRetains P 4 Ls (σ s) a)
    (fun σ v => frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix v))
    (genuinePrep HP t D suffix k G) x y

open Classical in
lemma genuineMean_range (s t : Fin J) (Ls Lt : ℕ) (a D : ZMod P)
    (suffix : List (ZMod P)) (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) :
    genuineMean HP s t Ls Lt a D suffix k G x y ∈ Set.Icc 0 1 := by
  classical
  let T : Finset (Environment P J) := {σ | frameRetains P 4 Ls (σ s) a ∧
    frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y)}
  change (𝔼 σ ∈ T, genuinePrep HP t D suffix k G σ x y) ∈ Set.Icc 0 1
  constructor
  · apply expect_nonneg
    intro σ _
    exact mul_nonneg (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_nonneg _)
  · rcases T.eq_empty_or_nonempty with h | h
    · rw [h]; norm_num
    · apply expect_le h
      intro σ _
      exact (mul_le_of_le_one_right (polynomialPrepCutoff4_nonneg _ _) (HP.ρ_le_one _)).trans
        (polynomialPrepCutoff4_le_one _ _)

open Classical in
lemma genuineMean_zero (s t : Fin J) (Ls Lt : ℕ) (a D : ZMod P)
    (suffix : List (ZMod P)) (k : ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P)
    (hd : G x y / rate k ≤ HP.θ / 2) : genuineMean HP s t Ls Lt a D suffix k G x y = 0 := by
  classical
  unfold genuineMean rowSliceMean
  apply expect_eq_zero
  intro σ _
  simp only [genuinePrep, DenseRowRecipe.preparation, atomPrep,
    polynomialPrepCutoff4_eq_zero HP.θ_pos hd, zero_mul]

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]
open Classical in
/-- The sharper conditional rarity factor retains the distinguished endpoint's contribution
as 2/n. This uses actual H4 mixed-rate laws, deterministic row mass, and source-role independence.
-/
theorem actual_conditional_rarity (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ)
    (a D : ZMod P) (hD : D ≠ 0) (suffix : List (ZMod P)) (H : Horizon P)
    {k : ℕ} (hk : k ≤ H.maxExponent) (hLt : Lt ≤ P)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {M floor : ℝ} (hmass : ∀ x, ∑ y, G x y ≤ M) (hf : 0 < floor)
    {n : ℕ} (hn : 0 < n) (x y : ZMod P) :
    let T : Finset (Environment P J) := {σ | frameRetains P 4 Ls (σ s) a ∧
      frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y)}
    let Y := fun (σ : Environment P J) w =>
      frameRetains P 4 (side P k) (σ t) (CopyPadding.identifier D suffix w)
    (#{σ ∈ T | heavyCountEvent Y univ (fun w => G x w / rate k) floor n σ} : ℝ) / #T ≤
      (2 + 8 * 32 * M / floor) / (n : ℝ) := by
  classical
  dsimp only
  let T : Finset (Environment P J) := {σ | frameRetains P 4 Ls (σ s) a ∧
    frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y)}
  let Y := fun (σ : Environment P J) w => frameRetains P 4 (side P k) (σ t)
    (CopyPadding.identifier D suffix w)
  have hM : 0 ≤ M := (sum_nonneg (fun w _ => hG x w)).trans (hmass x)
  have hd (w : ZMod P) (_hw : w ∈ (univ : Finset (ZMod P))) : 0 ≤ G x w / rate k :=
    div_nonneg (hG x w) (rate_pos k).le
  have hm : rate k * ∑ w, G x w / rate k ≤ M := by
    rw [← sum_div, mul_div_cancel₀ _ (rate_pos k).ne']
    exact hmass x
  have hp (w : ZMod P) (_hw : w ∈ (univ : Finset (ZMod P)))
      (_hheavy : floor / 4 < G x w / rate k) (hwy : w ≠ y) :
      (#{σ ∈ T | Y σ w} : ℝ) ≤ 32 * rate k * #T := by
    simpa only [T, Y, filter_filter, and_assoc] using
      source_mixed_pair s t hst Ls Lt a (CopyPadding.identifier D suffix y) H hk hLt
        ((CopyPadding.identifier_injective hD suffix).ne hwy)
  have hh := card_filter_heavyCountEvent_mul_le (d := fun w => G x w / rate k) (a := rate k) (ρ :=
    floor) (c := 32) (M := M) Y T univ y (rate_pos k).le hf
    (by norm_num : (0 : ℝ) ≤ 32) hd hm
    (by
      intro w hw hh hwy
      convert hp w hw hh hwy using 1
      congr 2
      ext σ
      simp only [mem_filter]) n
  change (#{σ ∈ T | heavyCountEvent Y univ (fun w => G x w / rate k) floor n σ} : ℝ) / #T ≤ _
  rcases T.eq_empty_or_nonempty with hT | hT
  · rw [hT]; simp only [filter_empty, card_empty, Nat.cast_zero, zero_div]
    positivity
  · have hT0 : (0 : ℝ) < #T := by exact_mod_cast hT.card_pos
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    apply (div_le_iff₀ hT0).mpr
    rw [div_mul_eq_mul_div]
    apply (le_div_iff₀ hn0).mpr
    apply (mul_le_mul_iff_right₀ hf).mp
    calc
      _ = (#{σ ∈ T | heavyCountEvent Y univ (fun w => G x w / rate k) floor n σ} : ℝ) * n * floor
        := by ring
      _ ≤ #T * (2 * (floor + 4 * 32 * M)) := hh
      _ = _ := by field_simp; ring

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Matrix Matrix.HierarchyParams Cslib.RowCompression
open scoped BigOperators
variable {P J : ℕ} [Fact P.Prime]

open Classical in
/-- Cardinal form of actual conditional rarity, including empty conditioning slices. -/
lemma actual_rarity_card (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ)
    (D : ZMod P) (hD : D ≠ 0) (sourceSuffix suffix : List (ZMod P)) (H : Horizon P)
    {k : ℕ} (hk : k ≤ H.maxExponent) (hLt : Lt ≤ P)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {M floor : ℝ} (hmass : ∀ x, ∑ y, G x y ≤ M) (hf : 0 < floor)
    {n : ℕ} (hn : 0 < n) (x y : ZMod P) :
    (#{σ : Environment P J | frameRetains P 4 Ls (σ s) (CopyPadding.identifier D sourceSuffix x) ∧
      frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y) ∧
      heavyCountEvent (fun τ w => frameRetains P 4 (side P k) (τ t)
        (CopyPadding.identifier D suffix w)) univ (fun w => G x w / rate k) floor n σ} : ℝ) ≤
      ((2 + 256 * M / floor) / (n : ℝ)) *
      #{σ : Environment P J | frameRetains P 4 Ls (σ s) (CopyPadding.identifier D sourceSuffix x) ∧
        frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y)} := by
  classical
  let T : Finset (Environment P J) := {σ | frameRetains P 4 Ls (σ s)
    (CopyPadding.identifier D sourceSuffix x) ∧ frameRetains P 4 Lt (σ t)
      (CopyPadding.identifier D suffix y)}
  have h := actual_conditional_rarity s t hst Ls Lt
    (CopyPadding.identifier D sourceSuffix x) D hD suffix H hk hLt G hG hmass hf hn x y
  dsimp only at h
  rcases T.eq_empty_or_nonempty with hT | hT
  · have hz : #{σ : Environment P J | frameRetains P 4 Ls (σ s) (CopyPadding.identifier D
    sourceSuffix x) ∧
        frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y)} = 0 := by
      change #T = 0
      rw [hT]; rfl
    have hsub : ({σ | frameRetains P 4 Ls (σ s) (CopyPadding.identifier D sourceSuffix x) ∧
      frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y) ∧
      heavyCountEvent (fun τ w => frameRetains P 4 (side P k) (τ t)
        (CopyPadding.identifier D suffix w)) univ (fun w => G x w / rate k) floor n σ} : Finset _)
          ⊆ T :=
      fun σ hσ => mem_filter.mpr ⟨mem_univ _, (mem_filter.mp hσ).2.1, (mem_filter.mp hσ).2.2.1⟩
    have hzero := card_le_card hsub
    rw [hT] at hzero
    simp only [card_empty, Nat.le_zero] at hzero
    rw [hzero, hz, Nat.cast_zero, mul_zero]
  · have ht : (0 : ℝ) < #T := by exact_mod_cast hT.card_pos
    have hh := (div_le_iff₀ ht).mp h
    simpa only [T, filter_filter, and_assoc, show (8 : ℝ) * 32 = 256 by norm_num] using hh

open Classical in
/-- Actual mixed-rate H4 rarity contracts any deterministic endpoint mean discrepancy.
The random row magnitude may select an endpoint adaptively; only its endpoint-power
majorant is required. The usage channel is Lt, not the wider rank channel. -/
theorem actual_mean_event_moment (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ)
    (D : ZMod P) (hD : D ≠ 0) (sourceSuffix suffix : List (ZMod P)) (H : Horizon P)
    {k : ℕ} (hk : k ≤ H.maxExponent) (hLt : Lt ≤ P)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {M floor N u : ℝ} (hmass : ∀ x, ∑ y, G x y ≤ M) (hf : 0 < floor)
    {n : ℕ} (hn : 0 < n) (hNu : 0 ≤ N * u)
    (b : Matrix (ZMod P) (ZMod P) ℝ) (v : Environment P J → ZMod P → ℝ)
    (hv : ∀ σ x, frameRetains P 4 Ls (σ s) (CopyPadding.identifier D sourceSuffix x) →
      |v σ x| ^ 4 ≤ ∑ y ∈ ({y | frameRetains P 4 Lt (σ t)
        (CopyPadding.identifier D suffix y)} : Finset (ZMod P)), |b x y| ^ 4) :
    let X := fun (σ : Environment P J) x =>
      frameRetains P 4 Ls (σ s) (CopyPadding.identifier D sourceSuffix x)
    let Yt := fun (σ : Environment P J) y =>
      frameRetains P 4 Lt (σ t) (CopyPadding.identifier D suffix y)
    let Y := fun (σ : Environment P J) y =>
      frameRetains P 4 (side P k) (σ t) (CopyPadding.identifier D suffix y)
    vertexNormPow 4 N u X (fun σ x =>
      if heavyCountEvent Y univ (fun y => G x y / rate k) floor n σ then v σ x else 0) ≤
      ((2 + 256 * M / floor) / (n : ℝ)) * rowNormPow 4 N u X Yt (fun _ x y => b x y) := by
  classical
  dsimp only
  refine vertexNormPow_event_le_rowNormPow (by norm_num) hNu (fun x y => ?_) b v hv
  exact actual_rarity_card s t hst Ls Lt D hD sourceSuffix suffix H hk hLt G hG hmass hf hn x y
end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
