/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyIncomingPreparationBias
public import Complexity.Foundations.Probability.HierarchyProductMean

/-!
# Canonical means at later actual input iterations

A later actual input has reference `C + Eᵢ C`, with no negative ray.
The existing final-residual bridge cannot be reused with its structural iteration
silently changed. This module transports the genuine requested earlier correction,
including the right child's midpoint source reset, actual usage density and suffixes.
The product proof follows Christian Reitwiessner's signed canonical mean construction,
retaining Samuel Schlesinger's adapted hierarchy assembly.

This is a prerequisite for later relative propagation, not that propagation theorem.
Successful estimated children, their own root budgets, spectral noise, omitted finite
bins and a uniform payment into incoming PREP remain separate obligations.

## Main results

* `canonical_laterInput_bin_mean`: actual requested-iterate positive bin mean.
* `BudgetData.canonicalLaterInput_mean`: finite covered bins give the genuine PREP reference.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment
open Finset Cslib Cslib.Probability
open scoped BigOperators
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)

/-- The genuine later actual input averages to the base bin plus the requested
correction times that bin. No subtraction, independence or estimated-child accuracy
is introduced. The structural index is independent of statistical budgets. -/
theorem canonical_laterInput_bin_mean
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P) (R : RoleProfile J)
    (i : Fin HP.k) (j : ℕ) (hij : i.val = j + 1)
    (l bin ks km kt kb : ℕ) (hsH : ks ≤ H.maxExponent) (hms : km ≤ ks)
    (hbH : kb ≤ H.maxExponent) (ss sm st : List (ZMod P))
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate km)
    (cutoff h ρ : ℝ → ℝ) (K : ℕ)
    (hkh : ∀ v, cutoff v ≠ 0 → h v = 1)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ v, v ≤ η → ρ v = 1)
    (hK : 2 * (1 + 32 / η) ≤ K) (x y : V) :
    let source := gridChannel R.source ks ss
    let mid := gridChannel R.midpoint km sm
    let terminal := gridChannel R.terminal kt st
    let B := fun x y => rate kb * cutoff (C x y / rate kb)
    let E := HP.toHierarchyParams.correctionIter (canonicalChannel ident (rate km))
      (canonicalChannel ident (rate km)) (rate km) C i.val
    (𝔼 σ ∈ ({σ : Environment P J |
      source.retains (channels D) σ (ident x) ∧
        terminal.retains (channels D) σ (ident y)} : Finset _),
      HierarchyTask.rawPositiveSample (k := HP.k)
        (fun role b suffix σ v => channels D role b suffix σ (ident v))
        l bin (.input i) source mid terminal (rate kb)
        (fun r => canonicalRequestChild HP D ident C cutoff h ρ K r σ) x y) =
      B x y + (∑ z : V, E x z * B z y) := by
  dsimp only
  let source := gridChannel R.source ks ss
  let mid := gridChannel R.midpoint km sm
  let terminal := gridChannel R.terminal kt st
  let req := HierarchyTask.rawRequests (k := HP.k) l bin (.input i) source mid terminal (rate kb)
  let S := ({σ : Environment P J | source.retains (channels D) σ (ident x) ∧
    terminal.retains (channels D) σ (ident y)} : Finset _)
  let q := fun A => coordinate D terminal A (ident y)
  let E := HP.toHierarchyParams.correctionIter (canonicalChannel ident (rate km))
    (canonicalChannel ident (rate km)) (rate km) C i.val
  let B := fun x y => rate kb * cutoff (C x y / rate kb)
  have hd : Admissible req.direct := ⟨R.source_terminal, rfl, rfl⟩
  have hl : Admissible req.left := ⟨R.source_midpoint, rfl, rfl⟩
  have hr : Admissible req.right := ⟨R.midpoint_terminal, rfl, rfl⟩
  have hj : j < HP.k := by omega
  have hc : HierarchyTask.correctionAtomTask (k := HP.k) l false i.castSucc =
      .row l (.normalized ⟨j, hj⟩) := by
    have he : i.castSucc = (⟨j, hj⟩ : Fin HP.k).succ := by
      apply Fin.ext
      exact hij
    rw [he]
    simp only [HierarchyTask.correctionAtomTask, Fin.cases_succ,
      Bool.false_eq_true, ↓reduceIte]
  have hrow (z : V) : ∑ w, C z w ≤ 1 := by simpa [Matrix.mulVec, dotProduct] using hC1 z
  have hsubD (A : FrameChannel P 4 1) : splitUsage D ident req.direct A y → q A :=
    coordinate_min_grid D R.terminal st kt kb A (ident y)
  have hsubR (A : FrameChannel P 4 1) : splitUsage D ident req.right A y → q A :=
    coordinate_min_grid D R.terminal st kt kb A (ident y)
  have hdirect := denseChild_mean_on_terminal_event D ident req.direct hd hD hid H
    hsH rfl hbH rfl (rate_min kt kb) cutoff h ρ K C q x y hsubD
    hkh hρ0 hρ1 hη hρη (hC x) (hrow x) hK
  have hproduct (z : V) := sourceChild_mul_denseChild_mean HP D ident req.left hl
    req.right hr rfl rfl R.source_terminal R.midpoint_terminal hD hid H
    hsH hms rfl rfl hbH rfl (rate_min kt kb) C hC hC1 hCf hj
    cutoff h ρ K q x z y hsubR hkh hρ0 hρ1 hη hρη hK
  simp only [← hij] at hproduct
  have leftChild (σ : Environment P J) :
      canonicalRequestChild HP D ident C cutoff h ρ K req.left σ =
        sourceChild HP D ident req.left hl C j σ := by
    have ht : req.left.task = .row l (.normalized ⟨j, hj⟩) := hc
    unfold canonicalRequestChild
    rw [ht]
    simp only [dite_eq_left hl]
  have directChild (σ : Environment P J) :
      canonicalRequestChild HP D ident C cutoff h ρ K req.direct σ =
        denseChild D ident req.direct cutoff h ρ K C σ := rfl
  have rightChild (σ : Environment P J) :
      canonicalRequestChild HP D ident C cutoff h ρ K req.right σ =
        denseChild D ident req.right cutoff h ρ K C σ := rfl
  let ratio := fun (r : HierarchyTask.Request HP.k (Fin J) (ZMod P)) =>
    HierarchyTask.usageRatio
    (fun role b suffix σ v => channels D role b suffix σ (ident v)) terminal r y
  change (𝔼 σ ∈ S, (rate kb * ratio req.direct *
      canonicalRequestChild HP D ident C cutoff h ρ K req.direct σ x y +
    rate kb * ratio req.right *
      (mid.rate / (dens {σ : Environment P J | mid.retains (channels D) σ (ident y)} : ℝ)) *
      (∑ z, canonicalRequestChild HP D ident C cutoff h ρ K req.left σ x z *
        canonicalRequestChild HP D ident C cutoff h ρ K req.right σ z y))) =
      B x y + (∑ z : V, E x z * B z y)
  rw [expect_add_distrib]
  have hdmean : (𝔼 σ ∈ S, rate kb * ratio req.direct *
      canonicalRequestChild HP D ident C cutoff h ρ K req.direct σ x y) = B x y := by
    simp_rw [directChild]
    exact hdirect
  rw [hdmean]
  congr 1
  simp_rw [leftChild, rightChild, mul_sum]
  rw [expect_sum_comm]
  apply sum_congr rfl
  intro z _
  convert hproduct z using 1
  · apply expect_congr rfl
    intro σ _
    dsimp only [ratio, HierarchyTask.usageRatio, req, HierarchyTask.rawRequests,
      source, mid, terminal, q, gridChannel, CorrectionRowTask.Channel.retains,
      channels, coordinate]
    ac_rfl
  · rfl


namespace BudgetData
variable {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP P)
variable (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
  (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
    rate 1 i (fun _ => 1))
  (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
  (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
  (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  (s t : Fin 3) (hst : s ≠ t) (ks kt : ℕ) (ss st : List (ZMod P))
  (hs : r.source = gridChannel s ks ss) (ht : r.terminal = gridChannel t kt st)
  (hks : ks ≤ H.maxExponent) (hts : kt ≤ ks)
  (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
  (hCf : ∀ x y, B.base x y ≤ rate kt)
include hbins hrate hcutoff haux hD hnH hst hs ht hks hts hC hC1 hCf

/-- Actual bounded polynomial bins average to the requested later input `C + Eᵢ C`.
Coverage concerns the base matrix only, never approximate children. The rank rate is the
parent terminal rate; the source can be narrower. All suffixes are preserved until the
existing common-environment mean laws transport them. -/
theorem canonicalLaterInput_mean (i : Fin HP.k) (j : ℕ) (hij : i.val = j + 1)
    (x y : ZMod P)
    (hcover : ∀ z, B.base z y = 0 ∨ rate n ≤ B.base z y) :
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun σ x y => ∑ bin ∈ B.bins,
        HierarchyTask.rawPositiveSample (channels B.padding) 0 bin (.input i)
          r.source (midpoint r) r.terminal (B.binRate bin)
          (fun q => B.residualCanonicalChild bin q σ) x y) x y =
    B.canonicalPreparationInput false i r x y := by
  let roles : RoleProfile 3 :=
    ⟨s, midpointRole s t, t, (midpointRole_distinct s t).1, hst,
      (midpointRole_distinct s t).2⟩
  have hm : midpoint r = gridChannel roles.midpoint kt [] := by
    simp only [midpoint, hs, ht, gridChannel, roles]
  have hp (bin : ℕ) (hi : bin ∈ B.bins) (v : ℝ) (hv : B.cutoff bin v ≠ 0) :
      B.auxiliary bin v = 1 := by
    rw [hcutoff] at hv
    rw [haux]
    exact HP.routedBin_prep_eq_one (by norm_num)
      (fun w hw => polynomialSwitch4_of_le (by norm_num) hw) rate_pos rate_antitone
      bin (fun _ => 1) hv
  have hK : 2 * (1 + 32 / HP.η) ≤ HP.K := by
    have hk1 : (1 : ℝ) ≤ HP.k := by exact_mod_cast HP.k_pos
    have hdiv := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left hk1 (by norm_num : (0 : ℝ) ≤ 32)) HP.η_pos.le
    have hg := HP.gate
    norm_num only [mul_one] at hdiv
    nlinarith [div_nonneg (by norm_num : (0 : ℝ) ≤ 32) HP.η_pos.le]
  let E := HP.toHierarchyParams.correctionIter (canonicalChannel id (rate kt))
    (canonicalChannel id (rate kt)) (rate kt) B.base i.val
  have hpositive (bin : ℕ) (hi : bin ∈ B.bins) :
      rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y => HierarchyTask.rawPositiveSample (channels B.padding) 0 bin (.input i)
          r.source (midpoint r) r.terminal (B.binRate bin)
          (fun q => B.residualCanonicalChild bin q σ) x y) x y =
      B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin) +
        ∑ z, E x z * (B.binRate bin * B.cutoff bin (B.base z y / B.binRate bin)) := by
    have hiH : bin ≤ H.maxExponent := by rw [hbins, mem_range] at hi; omega
    have hmean := canonical_laterInput_bin_mean HP B.padding id hD
      Function.injective_id H roles i j hij 0 bin ks kt kt bin hks hts hiH ss [] st B.base
      hC hC1 hCf (B.cutoff bin) (B.auxiliary bin) HP.ρ HP.K (hp bin hi)
      HP.ρ_nonneg HP.ρ_le_one HP.η_pos HP.ρ_one hK x y
    simpa only [rowSliceMean, residualCanonicalChild, hs, ht, hm, hrate, roles, id_eq]
      using hmean
  have hsum (z : ZMod P) :
      ∑ i ∈ B.bins, B.binRate i * B.cutoff i (B.base z y / B.binRate i) = B.base z y := by
    rw [B.initialBins_polynomial_sum n hbins hrate hcutoff hC hC1]
    rcases hcover z with hz | hz
    · rw [hz, zero_mul]
    · rw [polynomialSwitch4_of_ge (by norm_num)
        ((one_le_div (rate_pos n)).mpr hz), mul_one]
  change (𝔼 σ ∈ _, _) = _
  rw [expect_sum_comm]
  change (∑ bin ∈ B.bins, rowSliceMean _ _ _ x y) = _
  rw [sum_congr rfl hpositive, sum_add_distrib, hsum, sum_comm]
  simp_rw [← mul_sum, hsum]
  change B.base x y + (E * B.base) x y = _
  have hf : r.terminal.rate = rate kt := congrArg CorrectionRowTask.Channel.rate ht
  simp only [canonicalPreparationInput, Bool.false_eq_true, ↓reduceIte,
    HierarchyParams.correctionInput, hf, Matrix.add_apply, E]
  rw [hf]

end BudgetData

end Matrix.HierarchyParams.H4RankEnvironment
