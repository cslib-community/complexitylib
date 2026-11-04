/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.SecondSignal

/-!
# Numerical first-signal payments from actual child ranges

A supplied nonnegative scalar bin bound CB gives direct and right child range 2CB.
Correction range is CA = 2Q(atomCap). The finite payment keeps the actual usage ratios
and midpoint-density divisor, evaluated from the exact one-point frame marginals.
Only source horizons are needed for this deliberately coarse width-P payment. All children,
supports and masks may depend on the same full environment. No mean-bias, recursive reserve,
parameter-growth or workspace conclusion follows. Proof patterns adapt Samuel Schlesinger's
compression and norm APIs; the finite payment is original.

## Main definitions

* `firstSignalPayment`: width-dependent finite density/range payment.

## Main results

* `incomingMomentBudget_le_payment`: all three lower-child norms paid by actual ranges.
* `NormalizedMoments.actualFirstSignal_noise_le_dyadic`: actual positive-tolerance noise contract.
-/

public section

namespace Matrix.HierarchyParams.H4RankEnvironment

open Finset Cslib Cslib.Probability NormalizedMoments
open scoped BigOperators

noncomputable section
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime]

/-- Arbitrary bin cutoffs need an explicit bound. The clipped denominator doubles it. -/
theorem normalizedRequest_mem_Icc {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P)
    (r : HierarchyTask.Request q (Fin J) (ZMod P)) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P J) (x y : ZMod P) :
    normalizedRequest D id r binCutoff HP.ρ HP.K raw prep σ x y ∈ Set.Icc 0 (2 * CB) := by
  unfold normalizedRequest
  split_ifs
  · exact DenseRowRecipe.normalized_mem_Icc _ _ _ _ _ _ _ hCB hbin
      (fun d => ⟨HP.ρ_nonneg d, HP.ρ_le_one d⟩) _ _ _ _ _
  · exact ⟨le_rfl, by positivity⟩

/-- Exact grid frame mass; all prime and rounding dependence is visible. -/
@[expose] def gridMass (P k : ℕ) : ℝ := ((side P k : ℝ) / P) ^ 4

/-- The range-only payment retains width P. It makes no dimension-free recursive claim.
The two importance ratios and the source-released midpoint divisor are literal marginals. -/
@[expose] def firstSignalPayment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (P Kc ks km k kb : ℕ) (CB : ℝ) : ℝ :=
  let CA := 2 * HP.Q HP.toHierarchyParams.atomCap
  let B := rate kb * (gridMass P k / gridMass P (max k kb)) * (2 * CB)
  let BR := rate kb * (gridMass P k / gridMass P (max k kb)) *
    (rate km / gridMass P km) * (2 * CB)
  let A := rate km * (gridMass P k / gridMass P (max k km)) * CA
  64 * (16 * P * B ^ 4 +
    HP.K ^ 3 * CA ^ 4 * Kc * (rate km / rate ks) * (16 * P * BR ^ 4) +
    16 * P * A ^ 4)

/-- A bounded row pays at most the full width times its source density. The bound applies
before any walk, with arbitrary dependence of the row on its source mask. -/
lemma grid_row_moment_le (D : ZMod P) (s : Fin J) (ks : ℕ) (ss : List (ZMod P))
    (H : Horizon P) (hks : ks ≤ H.maxExponent)
    (Y : Environment P J → ZMod P → Prop) [∀ σ y, Decidable (Y σ y)]
    (F : Environment P J → ZMod P → ZMod P → ℝ)
    {B : ℝ} (hB : 0 ≤ B) (hF : ∀ σ x y, |F σ x y| ≤ B) :
    rowNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss) Y F ≤ 16 * P * B ^ 4 := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hr := rate_pos ks
  have hd := (affineRetains_rates (P := P) (H := 4) (horizon_admissible H hks)
    (show ((2 : ℝ) ^ ks)⁻¹ ≤ 1 from inv_le_one_of_one_le₀ (one_le_pow₀ (by norm_num)))).2.2.1
  rw [← side_eq_ceil] at hd
  norm_num only [show (2 : ℝ) ^ 4 = 16 by norm_num] at hd
  change gridMass P ks ≤ 16 * rate ks at hd
  have hv : vertexNormPow 4 P (rate ks) (retainedMask s (side P ks) D ss)
      (fun _ _ => 1) ≤ 16 := by
    rw [vertexNormPow_one_eq_sum_dens, NormalizedMoments.source_density_sum]
    change (↑P * rate ks)⁻¹ * (↑P * gridMass P ks) ≤ 16
    calc
      _ ≤ (↑P * rate ks)⁻¹ * (↑P * (16 * rate ks)) := by gcongr
      _ = 16 := by field_simp [hP.ne', hr.ne']
  have hb := rowNormPow_le_of_card_le (X := retainedMask s (side P ks) D ss)
    (Y := Y) (Z := F) (by decide : 4 ≠ 0) (mul_pos hP hr).le hB hF
    (K := P) (fun σ x _ => (card_le_card (subset_univ _)).trans_eq (by simp))
  have hm := mul_le_mul_of_nonneg_left hv
    (mul_nonneg (Nat.cast_nonneg P) (pow_nonneg hB 4))
  exact hb.trans (by nlinarith only [hm])

/-- All three lower-child norms are paid by actual fixed output ranges. The right factor
retains its midpoint-density normalization. No incomingMomentBudget premise is assumed. -/
theorem incomingMomentBudget_le_payment {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (R : RoleProfile J)
    (H : Horizon P) (l bin ks km k kb : ℕ)
    (hks : ks ≤ H.maxExponent) (hkm : km ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : HierarchyTask.Request (q + 1) (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : HierarchyTask.Request (q + 1) (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ) :
    incomingMomentBudget HP D id R l bin ks km k kb ss sm st Kc binCutoff
      raw prep maximum P (rate ks) ≤ firstSignalPayment HP P Kc ks km k kb CB := by
  let source := gridChannel R.source ks ss
  let mid := gridChannel R.midpoint km sm
  let terminal := gridChannel R.terminal k st
  let req := HierarchyTask.rawRequests (k := q + 1) l bin .residual source mid terminal (rate kb)
  let neg : HierarchyTask.Request (q + 1) (Fin J) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask l false (Fin.last (q + 1)), source,
      {terminal with rate := rate km}, {terminal with rate := min terminal.rate (rate km)}⟩
  let child := incomingChildren HP D id Kc binCutoff raw prep maximum
  let cB := rate kb * (gridMass P k / gridMass P (max k kb))
  let cR := cB * (rate km / gridMass P km)
  let cA := rate km * (gridMass P k / gridMass P (max k km))
  have hb0 : 0 ≤ cB := by dsimp [cB, gridMass, rate]; positivity
  have hr0 : 0 ≤ cR := by dsimp [cR, cB, gridMass, rate]; positivity
  have ha0 : 0 ≤ cA := by dsimp [cA, gridMass, rate]; positivity
  have hd (σ : Environment P J) (x y : ZMod P) :
      child req.direct σ x y ∈ Set.Icc 0 (2 * CB) :=
    normalizedRequest_mem_Icc HP D req.direct binCutoff hCB hbin _ _ σ x y
  have hr (σ : Environment P J) (x y : ZMod P) :
      child req.right σ x y ∈ Set.Icc 0 (2 * CB) :=
    normalizedRequest_mem_Icc HP D req.right binCutoff hCB hbin _ _ σ x y
  have ha (σ : Environment P J) (x y : ZMod P) :
      child neg σ x y ∈ Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap) :=
    selectedRequest_mem_Icc HP D id neg Kc _ _ _ σ x y
  have ratioB (y : ZMod P) :
      HierarchyTask.usageRatio (channels D) terminal req.direct y =
        gridMass P k / gridMass P (max k kb) :=
    usageRatio_grid D terminal req.direct k (max k kb) rfl (rate_min k kb) y
  have ratioR (y : ZMod P) :
      HierarchyTask.usageRatio (channels D) terminal req.right y =
        gridMass P k / gridMass P (max k kb) :=
    usageRatio_grid D terminal req.right k (max k kb) rfl (rate_min k kb) y
  have ratioA (y : ZMod P) :
      HierarchyTask.usageRatio (channels D) terminal neg y =
        gridMass P k / gridMass P (max k km) :=
    usageRatio_grid D terminal neg k (max k km) rfl (rate_min k km) y
  have dm (y : ZMod P) : (dens {σ : Environment P J |
      mid.retains (channels D) σ y} : ℝ) = gridMass P km := channel_density D mid km rfl y
  have direct := grid_row_moment_le D R.source ks ss H hks
    (retainedMask R.terminal (side P k) D st)
    (fun σ x y => cB * child req.direct σ x y) (B := cB * (2 * CB)) (mul_nonneg hb0 (by positivity))
    (fun σ x y => by
      rw [abs_of_nonneg (mul_nonneg hb0 (hd σ x y).1)]
      exact mul_le_mul_of_nonneg_left (hd σ x y).2 hb0)
  have right := grid_row_moment_le D R.midpoint km sm H hkm
    (retainedMask R.terminal (side P k) D st)
    (fun σ x y => cR * child req.right σ x y) (B := cR * (2 * CB)) (mul_nonneg hr0 (by positivity))
    (fun σ x y => by
      rw [abs_of_nonneg (mul_nonneg hr0 (hr σ x y).1)]
      exact mul_le_mul_of_nonneg_left (hr σ x y).2 hr0)
  have negative := grid_row_moment_le D R.source ks ss H hks
    (retainedMask R.terminal (side P k) D st)
    (fun σ x y => cA * child neg σ x y)
    (B := cA * (2 * HP.Q HP.toHierarchyParams.atomCap))
    (mul_nonneg ha0 (mul_nonneg (by norm_num) (HP.Q_nonneg _)))
    (fun σ x y => by
      rw [abs_of_nonneg (mul_nonneg ha0 (ha σ x y).1)]
      exact mul_le_mul_of_nonneg_left (ha σ x y).2 ha0)
  have coeff : 0 ≤ (HP.K : ℝ) ^ 3 * (2 * HP.Q HP.toHierarchyParams.atomCap) ^ 4 *
      Kc * (rate km / rate ks) := by unfold rate; positivity
  have result := mul_le_mul_of_nonneg_left
    (add_le_add (add_le_add direct (mul_le_mul_of_nonneg_left right coeff)) negative)
    (by norm_num : (0 : ℝ) ≤ 64)
  unfold incomingMomentBudget
  dsimp only
  change 64 * (rowNormPow 4 P (rate ks)
    (fun σ x => source.retains (channels D) σ x)
    (fun σ x => terminal.retains (channels D) σ x)
    (fun σ x y => rate kb * HierarchyTask.usageRatio (channels D) terminal req.direct y *
      child req.direct σ x y) +
    _ * rowNormPow 4 P (rate km)
      (fun σ x => mid.retains (channels D) σ x)
      (fun σ x => terminal.retains (channels D) σ x)
      (fun σ x y => rate kb * HierarchyTask.usageRatio (channels D) terminal req.right y *
        (rate km / (dens {τ | mid.retains (channels D) τ y} : ℝ)) * child req.right σ x y) +
    rowNormPow 4 P (rate ks)
      (fun σ x => source.retains (channels D) σ x)
      (fun σ x => terminal.retains (channels D) σ x)
      (fun σ x y => rate km * HierarchyTask.usageRatio (channels D) terminal neg y *
        child neg σ x y)) ≤ _
  simp_rw [ratioB, ratioR, ratioA, dm]
  convert result using 1 <;>
    simp only [rowNormPow, CorrectionRowTask.Channel.retains, source, mid, terminal,
      channels, gridChannel, semanticSide_grid, retainedMask, firstSignalPayment, cR, cB, cA]
  congr! 8 <;> ext y <;> simp

end
end Matrix.HierarchyParams.H4RankEnvironment

namespace Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments

open Finset Cslib Cslib.Probability Cslib.RowCompression
variable {P J : ℕ} [Fact P.Prime]
attribute [local instance] Classical.propDecidable

/-- Numerical actual first noise at budget i+1, with the inverse rate fourth power intact.
The width-dependent payment comes from actual child ranges, not a budget hypothesis. -/
theorem actualFirstSignal_noise_le_payment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (Horizon : Horizon P) (l bin ks km k kb Lt : ℕ)
    (hks : ks ≤ Horizon.maxExponent) (hkm : km ≤ Horizon.maxExponent)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : ∀ j : ℕ, HierarchyTask.Request j (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ∀ j : ℕ, HierarchyTask.Request j (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (steps : ℕ → ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (initial : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, initial σ x y 0 = 0)
    (i : ℕ) :
    let input := fun j => rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff (raw j) (prep j) (maximum j)
    let H := graph R.source R.terminal R.source_terminal (side P ks) (side P k)
      (side_le P ks) (side_le P k) (fun x => CopyPadding.identifier D ss x)
      (fun y => CopyPadding.identifier D st y)
    let F := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) H (fun _ _ => steps j) (input j)
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P k) Lt D ss st k G
        (firstSignalIncrement F k second) initial 0 i) ≤
      (rate k)⁻¹ ^ 4 * (32 *
        (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
        firstSignalPayment HP P Kc ks km k kb CB) := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hb := actualFirstSignal_noise_le_lower HP hK D R l bin ks km k kb Lt ss sm st Kc
    hKc binCutoff raw prep maximum steps G hG second initial hz hP (rate_pos ks) i
  have hm := incomingMomentBudget_le_payment HP D R Horizon l bin ks km k kb hks hkm
    ss sm st Kc binCutoff hCB hbin (raw (i + 1)) (prep (i + 1)) (maximum (i + 1))
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hm (by rw [pow_mul]; positivity)) (by positivity))

/-- Positive-tolerance logarithmic steps discharge the genuine first-prefix dyadic noise
contract. This makes no assertion about the preparation mean's bias. -/
theorem actualFirstSignal_noise_le_dyadic
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (Horizon : Horizon P) (l bin ks km k kb Lt : ℕ)
    (hks : ks ≤ Horizon.maxExponent) (hkm : km ≤ Horizon.maxExponent)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : ∀ j : ℕ, HierarchyTask.Request j (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ∀ j : ℕ, HierarchyTask.Request j (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (steps : ℕ → ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (initial : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, initial σ x y 0 = 0)
    (i m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hsteps : spectralWalkLength (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4))
      ((rate k)⁻¹ ^ 4 * 32 * firstSignalPayment HP P Kc ks km k kb CB)
      ε (dyadicSlack m i) ≤ steps (i + 1)) :
    let input := fun j => rawIncomingNormalized HP D id R l bin ks km k kb ss sm st
      (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff Kc binCutoff (raw j) (prep j) (maximum j)
    let H := graph R.source R.terminal R.source_terminal (side P ks) (side P k)
      (side_le P ks) (side_le P k) (fun x => CopyPadding.identifier D ss x)
      (fun y => CopyPadding.identifier D st y)
    let F := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st) H (fun _ _ => steps j) (input j)
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P k) Lt D ss st k G
        (firstSignalIncrement F k second) initial 0 i) ≤
      (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 4 := by
  have hden : (1 : ℝ) < 155648 * (J + 1) * (4 : ℝ) ^ 4 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hr : 0 < 1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4) :=
    sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hpay : 0 ≤ firstSignalPayment HP P Kc ks km k kb CB := by
    unfold firstSignalPayment gridMass rate
    positivity
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (mul_nonneg (by positivity) hpay) hε (dyadicSlack m i) (steps (i + 1)) hsteps
  have hn := actualFirstSignal_noise_le_payment HP hK D R Horizon l bin ks km k kb Lt
    hks hkm ss sm st Kc hKc binCutoff hCB hbin raw prep maximum steps G hG second initial hz i
  exact hn.trans (by nlinarith only [hp])

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
