/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.ClippedTail

/-!
# Rarity with separate deterministic prefix payments

Actual heavy-event rarity is applied to each deterministic prefix before finite Minkowski.
The finite double sum retains the early inactive group's coefficient instead of replacing
all prefixes by one uniform norm. Centered noises are outside this lemma. These are original
finite assembly bounds using the existing actual H4 rarity and compression APIs.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
open Finset Cslib Cslib.Probability Cslib.RowCompression
open scoped BigOperators
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Deterministic prefix row moments receive actual heavy rarity, with every schedule
weight retained. No cardinality of the environment or supplied final accuracy occurs. -/
theorem integrated_mean_tail_schedule
    (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ) (D : ZMod P) (hD : D ≠ 0)
    (ss st : List (ZMod P)) (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (hLt : Lt ≤ P) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {η mass N u : ℝ} (hη : 0 < η) (hNu : 0 ≤ N * u)
    (hmass : ∀ x, ∑ y, G x y ≤ mass) (m : ℕ) (n K : ℕ → ℕ)
    (hn : ∀ j < m, 0 < n j)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (μ : ℕ → Matrix (ZMod P) (ZMod P) ℝ) (ε : ℕ → ℝ)
    (hε : ∀ i < m, 0 ≤ ε i)
    (hbudget : ∀ i < m, rowNormPow 4 N u (retainedMask s Ls D ss)
      (retainedMask t Lt D st) (fun _ => μ i) ≤ ε i ^ 4) :
    let q := fun j => (2 + 256 * mass / dyadicFloor η m j) / (n j : ℝ)
    vertexNormPow 4 N u (retainedMask s Ls D ss) (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent t D st k m j η G n K Δ raw σ x then
        meanRowTail t Lt D st m j μ σ x else 0) ≤
      (∑ j ∈ range m, q j ^ (4⁻¹ : ℝ) *
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i) ^ 4 := by
  extract_lets q
  let X := retainedMask s Ls D ss
  let Y := retainedMask t Lt D st
  let event := fun j => meanFirstEvent t D st k m j η G n K Δ raw
  have hmass0 : 0 ≤ mass := (sum_nonneg fun y _ => hG 0 y).trans (hmass 0)
  have hq (j : ℕ) : 0 ≤ q j := by
    have hf := (dyadicFloor_pos hη m j).le
    dsimp only [q]
    positivity
  have hterm (j : ℕ) (hj : j < m) (i : ℕ) (hi : i < m) :
      vertexNormPow 4 N u X (fun σ x => if event j σ x then
        kthLargest 1 {y | Y σ y} (fun y => |μ i x y|) else 0) ≤
      (q j ^ (4⁻¹ : ℝ) * ε i) ^ 4 := by
    have hr (x y : ZMod P) :
        (#{σ : Environment P J | X σ x ∧ Y σ y ∧ event j σ x} : ℝ) ≤
          q j * #{σ : Environment P J | X σ x ∧ Y σ y} := by
      have hc := actual_rarity_card s t hst Ls Lt D hD ss st H hk hLt G hG hmass
        (dyadicFloor_pos hη m j) (hn j hj) x y
      have hsub : ({σ : Environment P J | X σ x ∧ Y σ y ∧ event j σ x} : Finset _) ⊆
          ({σ : Environment P J | X σ x ∧ Y σ y ∧
            heavyCountEvent (retainedMask t (side P k) D st) univ
              (fun y => G x y / rate k) (dyadicFloor η m j) (n j) σ} : Finset _) := by
        intro σ hσ
        have hh := (mem_filter.mp hσ).2
        exact mem_filter.mpr ⟨mem_univ _, hh.1, hh.2.1, hh.2.2.2⟩
      apply (Nat.cast_le.mpr (card_le_card hsub)).trans
      rw [show retainedMask t (side P k) D st =
        (fun (τ : Environment P J) w => frameRetains P 4 (side P k) (τ t)
          (CopyPadding.identifier D st w)) from rfl]
      simpa only [X, Y, retainedMask, q] using hc
    have ha := vertexNormPow_kthLargest_event_le (by norm_num : 4 ≠ 0) hNu hr (μ i)
    have hb := ha.trans (mul_le_mul_of_nonneg_left (hbudget i hi) (hq j))
    have hroot : (q j ^ (4⁻¹ : ℝ)) ^ 4 = q j := by
      convert Real.rpow_inv_natCast_pow (hq j) (by decide : (4 : ℕ) ≠ 0) using 1
    simpa only [mul_pow, hroot] using hb
  have ht (j : ℕ) (hj : j < m) :
      vertexNormPow 4 N u X (fun σ x => if event j σ x then
        meanRowTail t Lt D st m j μ σ x else 0) ≤
      (q j ^ (4⁻¹ : ℝ) * ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i) ^ 4 := by
    have hb := vertexNormPow_sum_le_pow_sum (by norm_num : 4 ≠ 0) hNu (Ico j m)
      (fun i σ x => if event j σ x then
        kthLargest 1 {y | Y σ y} (fun y => |μ i x y|) else 0)
      (fun i => (28 : ℝ) ^ (m - i)) (fun i => q j ^ (4⁻¹ : ℝ) * ε i)
      (fun _ _ => by positivity)
      (fun i hi => mul_nonneg (Real.rpow_nonneg (hq j) _) (hε i (mem_Ico.mp hi).2))
      (fun i hi => hterm j hj i (mem_Ico.mp hi).2)
    have he (σ : Environment P J) (x : ZMod P) :
        (∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
          if event j σ x then kthLargest 1 {y | Y σ y} (fun y => |μ i x y|) else 0) =
        if event j σ x then meanRowTail t Lt D st m j μ σ x else 0 := by
      by_cases h : event j σ x <;> simp [h, meanRowTail, Y]
    simp_rw [he] at hb
    convert hb using 1
    rw [mul_sum]
    congr 1
    apply sum_congr rfl
    intro i _
    ring
  have hs := vertexNormPow_sum_le_pow_sum (by norm_num : 4 ≠ 0) hNu (range m)
    (fun j σ x => if event j σ x then meanRowTail t Lt D st m j μ σ x else 0)
    (fun _ => 1) (fun j => q j ^ (4⁻¹ : ℝ) *
      ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) * ε i)
    (fun _ _ => by norm_num)
    (fun j hj => mul_nonneg (Real.rpow_nonneg (hq j) _)
      (sum_nonneg fun i hi => mul_nonneg (by positivity) (hε i (mem_Ico.mp hi).2)))
    (fun j hj => ht j (mem_range.mp hj))
  simpa only [one_mul] using hs

/-- The actual four-max tail separates deterministic conditional means from correlated
centered noise. Only the former receive the literal rarity weights. The latter use the
unique first overflow and unconditional prefix moments, on the same environment. -/
theorem integrated_fourMax_tail_schedule
    (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (s t : Fin J) (hst : t ≠ s) (Ls Lt : ℕ) (D : ZMod P) (hD : D ≠ 0)
    (ss st : List (ZMod P)) (H : Horizon P) {k : ℕ} (hk : k ≤ H.maxExponent)
    (hLt : Lt ≤ P) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    {η mass N u : ℝ} (hη : 0 < η) (hNu : 0 ≤ N * u)
    (hmass : ∀ x, ∑ y, G x y ≤ mass) (m : ℕ) (n K : ℕ → ℕ)
    (hn : ∀ j < m, 0 < n j) (ζ : ℝ)
    (Δ : Environment P J → ZMod P → ℕ → ZMod P → Fin 2 → ℝ)
    (raw : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (a b : Fin 2 → ℕ → ℝ) (ha : ∀ ν i, i < m → 0 ≤ a ν i)
    (hb : ∀ ν i, i < m → 0 ≤ b ν i)
    (hmean : ∀ ν i, i < m → rowNormPow 4 N u (retainedMask s Ls D ss)
      (retainedMask t (if ν = 0 then side P k else Lt) D st)
      (fun _ => actualClippedMean HP s t Ls (side P k) Lt D ss st k G ζ Δ raw ν i) ≤
        a ν i ^ 4)
    (hnoise : ∀ ν i, i < m → vertexNormPow 4 N u (retainedMask s Ls D ss)
      (actualNoiseMax s t Ls (side P k) Lt D ss st k G Δ raw ν i) ≤ b ν i ^ 4) :
    let q := fun j => ((2 + 256 * mass / dyadicFloor η m j) / (n j : ℝ)) ^ (4⁻¹ : ℝ)
    vertexNormPow 4 N u (retainedMask s Ls D ss) (fun σ x =>
      ∑ j ∈ range m, if meanFirstEvent t D st k m j η G n K Δ raw σ x then
        ∑ i ∈ Ico j m, (28 : ℝ) ^ (m - i) *
          actualFourMax HP s t Ls (side P k) Lt D ss st k G ζ Δ raw i σ x else 0) ≤
      ((∑ j ∈ range m, q j * ∑ i ∈ Ico j m,
        (28 : ℝ) ^ (m - i) * (a 0 i + a 1 i)) +
        ∑ i ∈ range m, (28 : ℝ) ^ (m - i) * (b 0 i + b 1 i)) ^ 4 := by
  extract_lets q
  let X := retainedMask s Ls D ss
  let mt := fun ν σ x => ∑ j ∈ range m,
    if meanFirstEvent t D st k m j η G n K Δ raw σ x then
      meanRowTail t (if ν = 0 then side P k else Lt) D st m j
        (actualClippedMean HP s t Ls (side P k) Lt D ss st k G ζ Δ raw ν) σ x else 0
  let zt := fun ν σ x => firstOverflowNoiseTail
    {y | retainedMask t (side P k) D st σ y} n K (dyadicFloor η m)
    (Δ σ x) ⟨0, raw σ x⟩ m (fun i => (28 : ℝ) ^ (m - i))
    (fun i => actualNoiseMax s t Ls (side P k) Lt D ss st k G Δ raw ν i σ x)
  let A := fun ν => ∑ j ∈ range m, q j * ∑ i ∈ Ico j m,
    (28 : ℝ) ^ (m - i) * a ν i
  let B := fun ν => ∑ i ∈ range m, (28 : ℝ) ^ (m - i) * b ν i
  have hA (ν : Fin 2) : 0 ≤ A ν := by
    apply sum_nonneg
    intro j _
    have hm0 : 0 ≤ mass := (sum_nonneg fun y _ => hG 0 y).trans (hmass 0)
    have hf := (dyadicFloor_pos hη m j).le
    exact mul_nonneg (Real.rpow_nonneg (by positivity) _)
      (sum_nonneg fun i hi => mul_nonneg (by positivity) (ha ν i (mem_Ico.mp hi).2))
  have hB (ν : Fin 2) : 0 ≤ B ν :=
    sum_nonneg fun i hi => mul_nonneg (by positivity) (hb ν i (mem_range.mp hi))
  have hm (ν : Fin 2) : vertexNormPow 4 N u X (mt ν) ≤ A ν ^ 4 :=
    integrated_mean_tail_schedule s t hst Ls _ D hD ss st H hk
      (by split_ifs <;> first | exact side_le P k | exact hLt)
      G hG hη hNu hmass m n K hn Δ raw _ (a ν) (ha ν) (hmean ν)
  have hz (ν : Fin 2) : vertexNormPow 4 N u X (zt ν) ≤ B ν ^ 4 :=
    vertexNormPow_firstOverflowNoiseTail_le_pow_sum
      (fun σ (_x : ZMod P) => {y | retainedMask t (side P k) D st σ y})
      n K (dyadicFloor η m) Δ (fun σ x => ⟨0, raw σ x⟩) m (by decide : 4 ≠ 0)
      hNu X (fun i => (28 : ℝ) ^ (m - i)) (b ν) _
      (fun _ _ => by positivity) (hb ν) (fun _ _ _ _ _ => kthLargest_nonneg) (hnoise ν)
  have hsum := vertex_add_budget X hNu (add_nonneg (hA 0) (hA 1))
    (add_nonneg (hB 0) (hB 1)) _ _
    (vertex_add_budget X hNu (hA 0) (hA 1) _ _ (hm 0) (hm 1))
    (vertex_add_budget X hNu (hB 0) (hB 1) _ _ (hz 0) (hz 1))
  apply (vertex_mono_nonneg X hNu _ (fun σ x =>
    (mt 0 σ x + mt 1 σ x) + (zt 0 σ x + zt 1 σ x)) ?_ ?_).trans
  · convert hsum using 1
    simp only [A, B, ← sum_add_distrib, ← mul_add]
  · intro σ x
    apply sum_nonneg
    intro j _
    split_ifs
    · exact sum_nonneg fun i _ => mul_nonneg (by positivity)
        (actualFourMax_nonneg HP _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _)
    · exact le_rfl
  · intro σ x
    exact fourMax_tail_le_envelope HP s t Ls Lt D ss st k m η G ζ n K Δ raw σ x

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
