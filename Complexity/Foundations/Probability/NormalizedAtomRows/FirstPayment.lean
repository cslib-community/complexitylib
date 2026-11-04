/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.NormalizedAtomRows.SecondSignal
public import Complexity.Foundations.Probability.HierarchyEstimatedInput

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
theorem actualFirstSignal_noise_le_payment {q : ℕ} (hq : 0 < q)
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (Horizon : Horizon P) (l bin ks km k kb Lt : ℕ)
    (hks : ks ≤ Horizon.maxExponent) (hkm : km ≤ Horizon.maxExponent)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (steps : ℕ → ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (initial : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, initial σ x y 0 = 0)
    (i : ℕ) :
    let F := fun j σ x y => completedRawChild HP D R l bin ks km k kb ss sm st Kc
      binCutoff (raw j) (prep j) (maximum j) (steps j) σ x y
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P k) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P k) Lt D ss st k G
        (firstSignalIncrement F k second) initial 0 i) ≤
      (rate k)⁻¹ ^ 4 * (32 *
        (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
        firstSignalPayment HP P Kc ks km k kb CB) := by
  have hP : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hb := actualFirstSignal_noise_le_lower hq HP hK D R l bin ks km k kb Lt ss sm st Kc
    hKc binCutoff raw prep maximum steps G hG second initial hz hP (rate_pos ks) i
  obtain ⟨q, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hq)
  have hm := incomingMomentBudget_le_payment HP D R Horizon l bin ks km k kb hks hkm
    ss sm st Kc binCutoff hCB hbin (raw (i + 1)) (prep (i + 1)) (maximum (i + 1))
  exact hb.trans (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hm (by rw [pow_mul]; positivity)) (by positivity))

/-- Positive-tolerance logarithmic steps discharge the genuine first-prefix dyadic noise
contract. This makes no assertion about the preparation mean's bias. -/
theorem actualFirstSignal_noise_le_dyadic {q : ℕ} (hq : 0 < q)
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (Horizon : Horizon P) (l bin ks km k kb Lt : ℕ)
    (hks : ks ≤ Horizon.maxExponent) (hkm : km ≤ Horizon.maxExponent)
    (ss sm st : List (ZMod P)) (Kc : ℕ) (hKc : 0 < Kc) (binCutoff : ℝ → ℝ)
    {CB : ℝ} (hCB : 0 ≤ CB) (hbin : ∀ d, binCutoff d ∈ Set.Icc 0 CB)
    (raw prep : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → HierarchyTask.Request q (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ)
    (steps : ℕ → ℕ) (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (initial : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, initial σ x y 0 = 0)
    (i m : ℕ) {ε : ℝ} (hε : 0 < ε)
    (hsteps : spectralWalkLength (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4))
      ((rate k)⁻¹ ^ 4 * 32 * firstSignalPayment HP P Kc ks km k kb CB)
      ε (dyadicSlack m i) ≤ steps (i + 1)) :
    let F := fun j σ x y => completedRawChild HP D R l bin ks km k kb ss sm st Kc
      binCutoff (raw j) (prep j) (maximum j) (steps j) σ x y
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
  have hn := actualFirstSignal_noise_le_payment hq HP hK D R Horizon l bin ks km k kb Lt
    hks hkm ss sm st Kc hKc binCutoff hCB hbin raw prep maximum steps G hG second initial hz i
  exact hn.trans (by nlinarith only [hp])


/-- Actual first-signal noise for the finite once-negative input. The inverse parent
rank-rate fourth power is retained in addition to the finite RAW input payment. -/
theorem actualEstimatedFirstSignal_noise_le_payment
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (l ks km kt n : ℕ) (hks : ks ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ) (Kc : ℕ) (cutoff : ℕ → ℝ → ℝ)
    (CB : ℕ → ℝ) (hCB : ∀ i, 0 ≤ CB i)
    (hcut : ∀ i v, cutoff i v ∈ Set.Icc 0 (CB i))
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ) (steps : ℕ → ℕ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (initial : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, initial σ x y 0 = 0) (i : ℕ) :
    let input := estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
      raw prep maximum
    let F := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (input j)
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P kt) (side P kt) D ss st kt G
        (firstSignalIncrement F kt second) initial 0 i) ≤
      (rate kt)⁻¹ ^ 4 * (32 *
        (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4)) ^ (2 * steps (i + 1)) *
        (16 * P * (estimatedResidualBound HP P km kt n kb CB) ^ 4)) := by
  dsimp only
  have hn := actualNoiseEntry_firstSignal_row_le R.source R.terminal
    (side P ks) (side P kt) (side P kt) D ss st
    (fun _ => graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
      (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
      (fun y => CopyPadding.identifier D st y)) (fun j _ _ => steps j)
    (estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff raw prep maximum)
    kt G hG second initial hz i (mul_nonneg (Nat.cast_nonneg P) (rate_pos ks).le)
  exact hn.trans (mul_le_mul_of_nonneg_left
    (estimatedResidualInput_noise_le HP hK D R H l ks km kt n hks ss sm st kb Kc
      cutoff CB hCB hcut raw prep maximum (i + 1) (steps (i + 1))) (by positivity))

/-- Positive-tolerance finite first-input noise contract, with fixed structural requests. -/
theorem actualEstimatedFirstSignal_noise_le_dyadic
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (hK : 0 < HP.K)
    (D : ZMod P) (R : RoleProfile J) (H : Horizon P)
    (l ks km kt n : ℕ) (hks : ks ≤ H.maxExponent)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ) (Kc : ℕ) (cutoff : ℕ → ℝ → ℝ)
    (CB : ℕ → ℝ) (hCB : ∀ i, 0 ≤ CB i)
    (hcut : ∀ i v, cutoff i v ∈ Set.Icc 0 (CB i))
    (raw prep : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix (ZMod P) (ZMod P) ℝ)
    (maximum : ℕ → ℕ → HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → ZMod P → ℝ) (steps : ℕ → ℕ)
    (G : Matrix (ZMod P) (ZMod P) ℝ) (hG : ∀ x y, 0 ≤ G x y)
    (second : Environment P J → ZMod P → ℕ → ZMod P → ℝ)
    (initial : Environment P J → ZMod P → ZMod P → Fin 2 → ℝ)
    (hz : ∀ σ x y, initial σ x y 0 = 0) (i : ℕ)
    {ε : ℝ} (hε : 0 < ε) (m : ℕ)
    (hsteps : spectralWalkLength (1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4))
      ((rate kt)⁻¹ ^ 4 * 32 * (16 * P * (estimatedResidualBound HP P km kt n kb CB) ^ 4))
      ε (dyadicSlack m i) ≤ steps (i + 1)) :
    let input := estimatedResidualInput HP D id R l ks km kt n ss sm st kb Kc cutoff
      raw prep maximum
    let F := fun j => conditionalWalk (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (graph R.source R.terminal R.source_terminal (side P ks) (side P kt)
        (side_le P ks) (side_le P kt) (fun x => CopyPadding.identifier D ss x)
        (fun y => CopyPadding.identifier D st y)) (fun _ _ => steps j) (input j)
    rowNormPow 4 P (rate ks) (retainedMask R.source (side P ks) D ss)
      (retainedMask R.terminal (side P kt) D st)
      (actualNoiseEntry R.source R.terminal (side P ks) (side P kt) (side P kt) D ss st kt G
        (firstSignalIncrement F kt second) initial 0 i) ≤
      (ε * (64 : ℝ)⁻¹ ^ dyadicSlack m i) ^ 4 := by
  dsimp only
  have hden : (1 : ℝ) < 155648 * (J + 1) * (4 : ℝ) ^ 4 := by
    have : (0 : ℝ) ≤ J := Nat.cast_nonneg J
    nlinarith
  have hr : 0 < 1 - 1 / (155648 * (J + 1) * (4 : ℝ) ^ 4) :=
    sub_pos.mpr ((div_lt_one (by linarith)).mpr hden)
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (show 0 ≤ (rate kt)⁻¹ ^ 4 * 32 * (16 * P *
      (estimatedResidualBound HP P km kt n kb CB) ^ 4) from by positivity)
    hε (dyadicSlack m i) (steps (i + 1)) hsteps
  exact (actualEstimatedFirstSignal_noise_le_payment HP hK D R H l ks km kt n hks
    ss sm st kb Kc cutoff CB hCB hcut raw prep maximum steps G hG second initial hz i).trans
      (by convert hp using 1; ring)

end Matrix.HierarchyParams.H4RankEnvironment.NormalizedMoments
