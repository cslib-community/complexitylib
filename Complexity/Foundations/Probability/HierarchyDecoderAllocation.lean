/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyPrefixAllocation

/-!
# Weighted allocations of actual combined RAW decoder noise

The production decoder consumes the semantic-plus-transported budget, with its
literal denominator, masks, suffixes and unchanged walk steps. An explicit grid
budget guard pays the retained cube and all four existing schedule weights.
Supplied successful endpoint histories and endpoint gates are not recursive IH.
This does not assemble the full reserve or establish joint recursive availability.
These are original finite consumers; no noise rarity or independence is assumed.
Schedule/reserve proof patterns are adapted from Samuel Schlesinger.

## Main results

* `rawFirstPrefixes_decoded_noise_schedule`: all four weighted decoder statistics.
* `rawFirstPrefixes_decoded_noise_reserve_le_payment`: the separated reserve contribution.
* `exists_rawFirstPrefixes_decoded_noise_reserve_charge`: a common charge for actual decoders.
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
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Stationary, final, unconditional factor-28 tail and raw false-charge weights
of the actual first-signal noise. The extra allocation guard is on the budget and
its real source/rank penalties, rather than on a desired moment inequality. -/
theorem rawFirstPrefixes_decoded_noise_schedule
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
    (hg : ∀ j ∈ range (Nat.log2 M + 1), ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin)
    (A : ℕ)
    (hbudget : 16 * (B.slack : ℝ) *
      (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M)
    (floor radius : ℝ) (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let E := (1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-B.requestPrecision M r)
    let a := fun j => rowNormPow 4 P r.source.rate
      (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
      (NormalizedMoments.retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second) 0 0 j)
    (∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ)) ≤ floor * E / 511 ∧
    a (Nat.log2 M) ^ (4⁻¹ : ℝ) ≤ E / 4 ∧
    (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ)) ≤ E * (458752 / 57) ∧
    (∑ j ∈ range m, (64 * (HP.K : ℝ) * radius ^ 4 /
      ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * a j) ≤
      (64 * (HP.K : ℝ) * radius ^ 4 / ((HP.K + 1) * floor ^ 4)) * E ^ 4 / 63 := by
  extract_lets m E a
  have hp := B.requestPrecision_prefix_margin A M ks ka r
    (by rw [hs]; rfl) (by rw [ht]; rfl) hbudget
  have hE : 0 ≤ E := by dsimp only [E]; positivity
  have han (j : ℕ) : 0 ≤ a j := rowNormPow_nonneg (by
    rw [hs]
    exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) _
  have he (j : ℕ) (hj : j < m) :
      0 ≤ a j ^ (4⁻¹ : ℝ) ∧ a j ^ (4⁻¹ : ℝ) ≤ E * (1 / 4 : ℝ) ^ dyadicSlack m j := by
    refine ⟨Real.rpow_nonneg (han j) _, ?_⟩
    have hb := B.rawFirstPrefixes_decoded_noise history M r s t hst ks ka ss st
      hs ht husage hcalls G hG second j hj
    have hc := B.rawRelativeNoiseBudget_residual_le_of_gates history M r s t hst
      ks ka ss st hs (by rw [ht]; rfl) hks hrate H hsource G hG (j + 1)
      (fun i hi bin hb n hn he => hg i
        (mem_range.mpr (by have hh := mem_range.mp hi; omega)) bin hb n hn he)
    have hb' : a j ≤ (E * (1 / 4 : ℝ) ^ dyadicSlack m j) ^ 4 := by
      apply (hb.trans hc).trans
      simpa only [Nat.add_sub_cancel] using
        combinedNoiseEnvelope_allocated A m (j + 1) (by dsimp only [m]; omega)
          (by omega) (B.requestPrecision M r) hp
    have hr := Real.rpow_le_rpow (han j) hb' (by norm_num : (0 : ℝ) ≤ 4⁻¹)
    convert hr using 1
    symm
    convert Real.pow_rpow_inv_natCast (by positivity :
      0 ≤ E * (1 / 4 : ℝ) ^ dyadicSlack m j) (by decide : (4 : ℕ) ≠ 0) using 1
  obtain ⟨hpre, hfinal, htail, hraw⟩ := compatible_quarter_noise_schedule hf hE HP.K m
    radius (fun j => a j ^ (4⁻¹ : ℝ)) he
  refine ⟨hpre, hfinal _ (by dsimp only [m]; omega), htail, ?_⟩
  have hpow (j : ℕ) : (a j ^ (4⁻¹ : ℝ)) ^ 4 = a j := by
    convert Real.rpow_inv_natCast_pow (han j) (by decide : (4 : ℕ) ≠ 0) using 1
  simpa only [hpow] using hraw

/-- Insert the actual decoder statistics into the existing separated reserve.
Only this first centered-noise contribution is paid; other statistics and the full
recursive reserve/availability induction are not asserted. -/
theorem rawFirstPrefixes_decoded_noise_reserve_le_payment
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
    (hg : ∀ j ∈ range (Nat.log2 M + 1), ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin)
    (A : ℕ)
    (hbudget : 16 * (B.slack : ℝ) *
      (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M)
    (floor cap C Cpre : ℝ) (hf : 0 < floor) :
    let m := Nat.log2 M + 1
    let a := fun j => rowNormPow 4 P r.source.rate
      (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
      (NormalizedMoments.retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second) 0 0 j)
    initialSeparatedReserve HP C Cpre
      (∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ))
      (a (Nat.log2 M) ^ (4⁻¹ : ℝ))
      (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ))
      (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
        ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * a j) ≤
      residualFirstNoisePayment HP floor cap C Cpre
        ((1 / 2 : ℝ) ^ A * (2 : ℝ) ^ (-B.requestPrecision M r)) := by
  extract_lets m a
  obtain ⟨hpre, hfinal, htail, hraw⟩ := B.rawFirstPrefixes_decoded_noise_schedule
    history M r s t hst ks ka ss st hs ht husage hks hrate H hsource hcalls G hG
    second hg A hbudget floor ((2 * max cap 16) ^ (4⁻¹ : ℝ)) hf
  have han (j : ℕ) : 0 ≤ a j := rowNormPow_nonneg (by
    rw [hs]
    exact mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le) _
  unfold residualFirstNoisePayment
  apply initialSeparatedReserve_mono HP C Cpre
  · exact sum_nonneg fun _ _ => mul_nonneg
      (dyadicFloor_pos hf _ _).le (Real.rpow_nonneg (han _) _)
  · exact Real.rpow_nonneg (han _) _
  · exact sum_nonneg fun _ _ => mul_nonneg (by positivity) (Real.rpow_nonneg (han _) _)
  · exact hpre
  · exact hfinal
  · exact htail
  · have hh := mul_le_mul_of_nonneg_left hraw (by norm_num : (0 : ℝ) ≤ 64)
    nlinarith only [hh]

/-- Fix structural constants, then choose one charge for every larger charge,
field and actual admitted decoder. The budget allocation guard is explicit. -/
theorem exists_rawFirstPrefixes_decoded_noise_reserve_charge
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (floor cap C Cpre : ℝ) (hf : 0 < floor) (lower : ℕ) :
    ∃ A₀ : ℕ, lower ≤ A₀ ∧ ∀ A ≥ A₀,
    ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (_hst : s ≠ t) (ks ka : ℕ) (ss st : List (ZMod P))
    (_hs : r.source = gridChannel s ks ss) (_ht : r.terminal = gridChannel t ka st)
    (_husage : r.usage = r.terminal) (_hks : ka ≤ ks)
    (_hrate : ∀ i ∈ B.bins, B.binRate i = rate i)
    (H : Horizon P) (_hsource : ks ≤ H.maxExponent)
    (_hcalls : ∀ j < Nat.log2 M + 1, ∀ bin ∈ B.rays .residual,
      let d := dyadicSlack (Nat.log2 M + 1) j
      let f := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
      let c := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
      f ≠ c → (0 < f → ∃ A, B.sample history f .residual r bin = some A) ∧
        (0 < c → ∃ C, B.sample history c .residual r bin = some C))
    (G : Matrix (ZMod P) (ZMod P) ℝ) (_hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P 3 → ZMod P → ℕ → ZMod P → ℝ)
    (_hg : ∀ j ∈ range (Nat.log2 M + 1), ∀ bin ∈ B.rays .residual, ∀ m, 0 < m →
      (m = LogSpaceEstimation.lastBudget M (dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin) ∨
        m = LogSpaceEstimation.lastBudget M (2 * dyadicSlack (Nat.log2 M + 1) j)
          B.slack (B.sampleScale r bin)) → B.ResidualEndpointGates history m r bin)
    (_hbudget : 16 * (B.slack : ℝ) *
      (2 * ((ka : ℝ) + ks) + B.rankCharge * r.task.rank +
        A + (Nat.log2 M + 1 : ℕ) + 3) ≤ M),
    let m := Nat.log2 M + 1
    let a := fun j => rowNormPow 4 P r.source.rate
      (NormalizedMoments.retainedMask s (side P ks) B.padding ss)
      (NormalizedMoments.retainedMask t (side P ka) B.padding st)
      (actualNoiseEntry s t (side P ks) (side P ka) (side P ka) B.padding ss st ka G
        (firstSignalIncrement (B.rawFirstPrefixes history M .residual r) ka second) 0 0 j)
    initialSeparatedReserve HP C Cpre
      (∑ j ∈ range m, dyadicFloor floor m j * a j ^ (4⁻¹ : ℝ))
      (a (Nat.log2 M) ^ (4⁻¹ : ℝ))
      (∑ j ∈ range m, (28 : ℝ) ^ (m - j) * a j ^ (4⁻¹ : ℝ))
      (64 * ∑ j ∈ range m, (64 * (HP.K : ℝ) *
        ((2 * max cap 16) ^ (4⁻¹ : ℝ)) ^ 4 /
        ((compatibleCapacity HP.K m j : ℝ) * dyadicFloor floor m j ^ 4)) * a j) ≤
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  obtain ⟨A₀, hlower, halloc⟩ := exists_residualFirstNoise_reserve_charge
    HP floor cap C Cpre hf lower
  refine ⟨A₀, hlower, ?_⟩
  intro A hA P _ B history M r s t hst ks ka ss st hs ht husage hks hrate H hsource
    hcalls G hG second hg hbudget
  exact (B.rawFirstPrefixes_decoded_noise_reserve_le_payment history M r s t hst
    ks ka ss st hs ht husage hks hrate H hsource hcalls G hG second hg A hbudget
    floor cap C Cpre hf).trans (halloc A hA _)

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
