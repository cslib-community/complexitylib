/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchySemanticNoise
public import Complexity.Foundations.Analysis.RowCompression.NoiseDecay

/-!
# Geometric reduction of the combined RAW noise prefix

The actual semantic-plus-transported production budget is bounded using the existing
geometric prefix API. The prefix cube is retained. This is an original finite bound,
not uniform reserve absorption: the remaining coefficient contains precision and
prefix length. No child accuracy, noise rarity or independence is assumed.

## Main results

* `rawRelativeNoiseBudget_residual_prefix_le_of_gates`: actual combined prefix payment.
* `rawFirstPrefixes_decoded_noise_prefix_le`: actual decoder consumer.
* `combinedNoiseEnvelope_final_lower`: the retained envelope has a cubic final term.
-/

public section
noncomputable section
open Finset Cslib Cslib.RowCompression Cslib.Probability
open Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false

/-- Geometric reduction of the exact retained envelope. This does not bound the
prefix length by a constant or discard the spare fourth power of precision. -/
theorem combinedNoiseEnvelope_prefix_le (ε : ℝ) (m j : ℕ) (hj : j ≤ m) :
    16 * ((j : ℝ) ^ 3 * ∑ i ∈ range j,
      64 * (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 8) ≤
    (1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) * ε ^ 8 * (j : ℝ) ^ 3 *
      ((64 : ℝ)⁻¹ ^ dyadicSlack m (j - 1)) ^ 8 := by
  have hs := sum_prefix_dyadic_decay_le
    (by norm_num : (0 : ℝ) ≤ ((64 : ℝ)⁻¹) ^ 8)
    (by norm_num : ((64 : ℝ)⁻¹) ^ 8 < 1) hj
  have hp (i : ℕ) : (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 8 =
      ε ^ 8 * (((64 : ℝ)⁻¹) ^ 8) ^ dyadicSlack m i := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm, pow_mul]
  simp_rw [hp]
  rw [show (∑ i ∈ range j, 64 * (ε ^ 8 * (((64 : ℝ)⁻¹) ^ 8) ^ dyadicSlack m i)) =
      (64 * ε ^ 8) * ∑ i ∈ range j, (((64 : ℝ)⁻¹) ^ 8) ^ dyadicSlack m i by
        rw [mul_sum]; apply sum_congr rfl; intros; ring]
  have h := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 1024 * ε ^ 8 * (j : ℝ) ^ 3 by positivity)
  convert h using 1
  · ring
  · rw [show (((64 : ℝ)⁻¹) ^ 8) ^ dyadicSlack m (j - 1) =
        ((64 : ℝ)⁻¹ ^ dyadicSlack m (j - 1)) ^ 8 by
          rw [← pow_mul, Nat.mul_comm 8, pow_mul]]
    ring

/-- At the full horizon the literal last summand already has cubic growth.
This is a lower bound on the conservative envelope, not on actual estimator noise. -/
theorem combinedNoiseEnvelope_final_lower (ε : ℝ) (m : ℕ) :
    1024 * ε ^ 8 * ((m + 1 : ℕ) : ℝ) ^ 3 * ((64 : ℝ)⁻¹) ^ 8 ≤
      16 * (((m + 1 : ℕ) : ℝ) ^ 3 * ∑ i ∈ range (m + 1),
        64 * (ε * (64 : ℝ)⁻¹ ^ dyadicSlack (m + 1) i) ^ 8) := by
  have hs : 64 * (ε * (64 : ℝ)⁻¹) ^ 8 ≤
      ∑ i ∈ range (m + 1), 64 * (ε * (64 : ℝ)⁻¹ ^ dyadicSlack (m + 1) i) ^ 8 := by
    simpa only [dyadicSlack_last, pow_one] using
      (single_le_sum (f := fun i => 64 *
        (ε * (64 : ℝ)⁻¹ ^ dyadicSlack (m + 1) i) ^ 8)
        (fun i _ => by positivity) (mem_range.mpr (Nat.lt_succ_self m)))
  have h := mul_le_mul_of_nonneg_left hs
    (show 0 ≤ 16 * ((m + 1 : ℕ) : ℝ) ^ 3 by positivity)
  convert h using 1 <;> simp only [mul_pow] <;> ring

variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- The actual combined production input consumes the geometric prefix bound.
Horizon, finite-prefix and literal positive endpoint gates are explicit. -/
theorem rawRelativeNoiseBudget_residual_prefix_le_of_gates
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal.rate = rate ka) (hks : ka ≤ ks)
    (hrate : ∀ i ∈ B.bins, B.binRate i = rate i)
    (H : Horizon P) (hsource : ks ≤ H.maxExponent)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (j : ℕ) (hj : j ≤ Nat.log2 M + 1)
    (hg : ∀ i ∈ range j, ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) i)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) i)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin) :
    B.rawRelativeNoiseBudget M r s t hst ks ka ss st
      (fun i => B.decodedGroupInput history M
        (dyadicSlack (Nat.log2 M + 1) i) .residual r) G j ≤
      (1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) *
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 8 * (j : ℝ) ^ 3 *
        ((64 : ℝ)⁻¹ ^ dyadicSlack (Nat.log2 M + 1) (j - 1)) ^ 8 :=
  (B.rawRelativeNoiseBudget_residual_le_of_gates history M r s t hst ks ka ss st
    hs ht hks hrate H hsource G hG j hg).trans
      (combinedNoiseEnvelope_prefix_le _ _ _ hj)

/-- Actual full-terminal decoder statistic with unchanged production steps.
Successful endpoint calls and gates are separate; neither is recursive IH.
This leaves a numerical horizon/precision coupling, rather than assuming its payment. -/
theorem rawFirstPrefixes_decoded_noise_prefix_le
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t ka st)
    (husage : r.usage = r.terminal) (hks : ka ≤ ks)
    (hrate : ∀ i ∈ B.bins, B.binRate i = rate i)
    (H : Horizon P) (hsource : ks ≤ H.maxExponent)
    (hcalls : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) j
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (i : ℕ) (hi : i < Nat.log2 M + 1)
    (hg : ∀ j ∈ range (i + 1), ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin) :
    rowNormPow 4 P r.source.rate
      (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
      (NormalizedMoments.retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second) 0 0 i) ≤
      (1024 / (1 - ((64 : ℝ)⁻¹) ^ 8)) *
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 8 * ((i + 1 : ℕ) : ℝ) ^ 3 *
        ((64 : ℝ)⁻¹ ^ dyadicSlack (Nat.log2 M + 1) i) ^ 8 := by
  apply (B.rawFirstPrefixes_decoded_noise history M r s t hst ks ka ss st hs ht husage
    hcalls G hG second i hi).trans
  simpa only [Nat.add_sub_cancel] using
    B.rawRelativeNoiseBudget_residual_prefix_le_of_gates history M r s t hst ks ka ss st
      hs (by rw [ht]; rfl) hks hrate H hsource G hG
      (i + 1) (by omega) hg

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
