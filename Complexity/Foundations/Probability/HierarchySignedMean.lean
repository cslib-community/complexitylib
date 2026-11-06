/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchySharedMidpoint

/-!
# Genuine signed canonical request means

The actual correction child is zero off its usage event. Its source-conditioned canonical
mean transports to the inherited terminal event with the exact density factor. Normalized
index j selects genuine iterate j.val; final dispatch at fixed structural HP.k completes
iterate HP.k. Statistical precision does not change this request structure.

The literal one-bin rawSample mean is C_bin + E C_bin - E. The finite residual assembly
sums actual positive bins using the existing routed-bin partition and subtracts the special
negative request once. Coverage, distinct roles, exact importance/midpoint densities,
source reset, all suffixes and the narrower-source finite horizon remain explicit. This is
one genuine deterministic stage, not recursive correctness of estimated children or a
routed copy-stage/error theorem.

The assembly is original work by Christian Reitwiessner using Samuel Schlesinger's hierarchy
construction and the genuine source sampler. Child-error propagation, numerical envelopes,
recursive reserves, workspace bounds and RL=L remain open.

## Main definitions

* `canonicalRequestChild`: genuine dense or index-matched correction request evaluation.

## Main results

* `sourceChild_mean_on_terminal_event`: derived inherited-terminal correction mean.
* `canonicalRequestChild_final_mean`: actual final structural dispatch and canonical mean.
* `canonical_rawSample_mean`: literal signed one-bin mean on the same full environment.
* `canonical_residual_bins_mean`: exact finite residual with one special negative correction.
-/

public section
open Finset Cslib Cslib.Probability
open scoped BigOperators
noncomputable section


namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]
  (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
  {n : ℕ} (r : HierarchyTask.Request n (Fin J) (ZMod P)) (hr : Admissible r)

/-- A genuine correction child vanishes outside its actual usage slice. -/
theorem sourceChild_zero_off_usage (C : Matrix V V ℝ) (i : ℕ)
    (σ : Environment P J) (x y : V)
    (hy : ¬ splitUsage D ident r (σ r.terminal.role) y) :
    sourceChild HP D ident r hr C i σ x y = 0 := by
  simp only [sourceChild, correctionRequest, dite_eq_left hr, CorrectionRowRecipe.normalized,
    Equiv.piSplitAt_apply]
  change (if splitUsage D ident r (σ r.terminal.role) y then _ else 0) = 0
  simp only [hy, ↓reduceIte]

/-- Genuine canonical correction mean under a containing inherited terminal event.
The statistical expectation uses one full environment with every spectator integrated.
No target-mean hypothesis is supplied. -/
theorem sourceChild_mean_on_terminal_event
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P)
    {k s u : ℕ} (hsH : s ≤ H.maxExponent) (hks : k ≤ s)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = rate u)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate) {i : ℕ} (hi : i < HP.k)
    (q : FrameChannel P 4 1 → Prop) [DecidablePred q]
    (x y : V) (hsub : ∀ A, splitUsage D ident r A y → q A) :
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x) ∧ q (σ r.terminal.role)} : Finset _),
      (r.terminal.rate * ((dens {σ : Environment P J | q (σ r.terminal.role)} : ℝ) /
        dens {σ : Environment P J | r.usage.retains (channels D) σ (ident y)})) *
      sourceChild HP D ident r hr C i σ x y) =
    HP.toHierarchyParams.correctionIter (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C (i + 1) x y := by
  have hm := source_request_mean_canonical HP D ident r hr hD hid H hsH hks
    hs ht hu C hC hC1 hCf hi x y
  change (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x)} : Finset _),
      (r.terminal.rate / (dens {σ : Environment P J |
        r.usage.retains (channels D) σ (ident y)} : ℝ)) *
      sourceChild HP D ident r hr C i σ x y) = _ at hm
  rw [dens_filter_pi_eval r.terminal.role q]
  have he := expect_pi_supported_terminal r.source.role r.terminal.role hr.1
    (fun A => coordinate D r.source A (ident x)) q
    (fun σ => (r.terminal.rate / (dens {τ : Environment P J |
      r.usage.retains (channels D) τ (ident y)} : ℝ)) *
      sourceChild HP D ident r hr C i σ x y) (fun σ hq => by
        rw [sourceChild_zero_off_usage HP D ident r hr C i σ x y
          (fun hy => hq (hsub _ hy)), mul_zero])
  calc
    _ = 𝔼 σ ∈ ({σ : Environment P J |
        r.source.retains (channels D) σ (ident x) ∧ q (σ r.terminal.role)} : Finset _),
        (dens {A | q A} : ℝ) * ((r.terminal.rate /
          (dens {τ : Environment P J | r.usage.retains (channels D) τ (ident y)} : ℝ)) *
          sourceChild HP D ident r hr C i σ x y) := by
      apply expect_congr rfl
      intro σ _
      ring
    _ = _ := he.trans hm

omit [Fintype V] in
/-- Grid usage at the minimum of two rates is contained in the inherited endpoint event.
Both predicates use exactly the same frame and suffix. -/
theorem coordinate_min_grid (role : Fin J) (suffix : List (ZMod P))
    (a b : ℕ) (A : FrameChannel P 4 1) (v : ZMod P) :
    coordinate D ⟨role, min (rate a) (rate b), suffix⟩ A v →
      coordinate D (gridChannel role a suffix) A v := by
  simp only [coordinate, gridChannel, rate_min, semanticSide_grid, frameRetains,
    mem_retentionBox]
  intro h j
  apply (h j).trans_le
  rw [side_eq_ceil, side_eq_ceil]
  apply Nat.ceil_mono
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg P)
  exact inv_anti₀ (by positivity)
    (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_max_left a b))

/-- Genuine actual request children for a selected raw bin. A normalized correction at
index j uses sourceChild at j.val, never a statistical precision or a fixed zero iterate.
Unused constructors return zero; dense requests keep their full source-reset tuple. -/
@[expose] def canonicalRequestChild (C : Matrix V V ℝ)
    (cutoff h ρ : ℝ → ℝ) (K : ℕ)
    (r : HierarchyTask.Request n (Fin J) (ZMod P))
    (σ : Environment P J) : Matrix V V ℝ :=
  match r.task with
  | .baseNormalized _ _ => denseChild D ident r cutoff h ρ K C σ
  | .row _ (.normalized j) =>
    if hr : Admissible r then sourceChild HP D ident r hr C j.val σ else 0
  | _ => 0

/-- Exact final dispatch in the actual child family. -/
theorem canonicalRequestChild_final (hq : 0 < n) (C : Matrix V V ℝ)
    (cutoff h ρ : ℝ → ℝ) (K l : ℕ)
    (htask : r.task = HierarchyTask.correctionAtomTask l false (Fin.last n))
    (σ : Environment P J) :
    canonicalRequestChild HP D ident C cutoff h ρ K r σ =
      sourceChild HP D ident r hr C (n - 1) σ := by
  simp only [canonicalRequestChild, htask, HierarchyTask.correctionAtomTask_last hq,
    dite_eq_left hr]

include hr in
/-- The real final correction request has the final canonical correction mean, including
its inherited terminal conditioning, rather than just a freely chosen iterate. -/
theorem canonicalRequestChild_final_mean
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P)
    {k s u : ℕ} (hsH : s ≤ H.maxExponent) (hks : k ≤ s)
    (hs : r.source.rate = rate s) (ht : r.terminal.rate = rate k)
    (hu : r.usage.rate = rate u) (hn : n = HP.k)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ r.terminal.rate)
    (cutoff h ρ : ℝ → ℝ) (K l : ℕ)
    (htask : r.task = HierarchyTask.correctionAtomTask l false (Fin.last n))
    (q : FrameChannel P 4 1 → Prop) [DecidablePred q]
    (x y : V) (hsub : ∀ A, splitUsage D ident r A y → q A) :
    (𝔼 σ ∈ ({σ : Environment P J |
      r.source.retains (channels D) σ (ident x) ∧ q (σ r.terminal.role)} : Finset _),
      (r.terminal.rate * ((dens {σ : Environment P J | q (σ r.terminal.role)} : ℝ) /
        dens {σ : Environment P J | r.usage.retains (channels D) σ (ident y)})) *
      canonicalRequestChild HP D ident C cutoff h ρ K r σ x y) =
    HP.toHierarchyParams.correctionIter (canonicalChannel ident r.terminal.rate)
      (canonicalChannel ident r.terminal.rate) r.terminal.rate C HP.k x y := by
  have hnpos : 0 < n := hn ▸ HP.k_pos
  simp_rw [canonicalRequestChild_final HP D ident r hr hnpos C cutoff h ρ K l htask]
  have hi : n - 1 < HP.k := by omega
  have hm := sourceChild_mean_on_terminal_event HP D ident r hr hD hid H hsH hks
    hs ht hu C hC hC1 hCf hi q x y hsub
  have heq : n - 1 + 1 = HP.k := by omega
  rw [heq] at hm
  exact hm

/-- Literal one-bin rawSample with the real canonical request family. The negative
correction occurs once in this call; summing unchanged calls would subtract it repeatedly.
Every term uses one full environment, shared midpoint and inherited source/terminal event. -/
theorem canonical_rawSample_mean
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P) (R : RoleProfile J)
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
      (canonicalChannel ident (rate km)) (rate km) C HP.k
    (𝔼 σ ∈ ({σ : Environment P J |
      source.retains (channels D) σ (ident x) ∧
        terminal.retains (channels D) σ (ident y)} : Finset _),
      HierarchyTask.rawSample (k := HP.k)
        (fun role b suffix σ v => channels D role b suffix σ (ident v))
        l bin .residual source mid terminal (rate kb)
        (fun r => canonicalRequestChild HP D ident C cutoff h ρ K r σ) x y) =
      B x y + (∑ z, E x z * B z y) - E x y := by
  dsimp only
  let source := gridChannel R.source ks ss
  let mid := gridChannel R.midpoint km sm
  let terminal := gridChannel R.terminal kt st
  let req := HierarchyTask.rawRequests (k := HP.k) l bin .residual source mid terminal (rate kb)
  let neg : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask l false (Fin.last HP.k), source,
      {terminal with rate := rate km}, {terminal with rate := min terminal.rate (rate km)}⟩
  let S := ({σ : Environment P J | source.retains (channels D) σ (ident x) ∧
    terminal.retains (channels D) σ (ident y)} : Finset _)
  let q := fun A => coordinate D terminal A (ident y)
  let E := HP.toHierarchyParams.correctionIter (canonicalChannel ident (rate km))
    (canonicalChannel ident (rate km)) (rate km) C HP.k
  let B := fun x y => rate kb * cutoff (C x y / rate kb)
  have hd : Admissible req.direct := ⟨R.source_terminal, rfl, rfl⟩
  have hl : Admissible req.left := ⟨R.source_midpoint, rfl, rfl⟩
  have hr : Admissible req.right := ⟨R.midpoint_terminal, rfl, rfl⟩
  have hn : Admissible neg := ⟨R.source_terminal, rfl, rfl⟩
  have hi : HP.k - 1 < HP.k := Nat.sub_lt HP.k_pos (by decide)
  have heq : HP.k - 1 + 1 = HP.k := by have := HP.k_pos; omega
  have hrow (z : V) : ∑ w, C z w ≤ 1 := by simpa [Matrix.mulVec, dotProduct] using hC1 z
  have hsubD (A : FrameChannel P 4 1) : splitUsage D ident req.direct A y → q A :=
    coordinate_min_grid D R.terminal st kt kb A (ident y)
  have hsubR (A : FrameChannel P 4 1) : splitUsage D ident req.right A y → q A :=
    coordinate_min_grid D R.terminal st kt kb A (ident y)
  have hsubN (A : FrameChannel P 4 1) : splitUsage D ident neg A y → q A :=
    coordinate_min_grid D R.terminal st kt km A (ident y)
  have hdirect := denseChild_mean_on_terminal_event D ident req.direct hd hD hid H
    hsH rfl hbH rfl (rate_min kt kb) cutoff h ρ K C q x y hsubD
    hkh hρ0 hρ1 hη hρη (hC x) (hrow x) hK
  have hnegative := canonicalRequestChild_final_mean HP D ident neg hn hD hid H
    hsH hms rfl rfl (rate_min kt km) rfl C hC hC1 hCf cutoff h ρ K l rfl q x y hsubN
  have hproduct (z : V) := sourceChild_mul_denseChild_mean HP D ident req.left hl
    req.right hr rfl rfl R.source_terminal R.midpoint_terminal hD hid H
    hsH hms rfl rfl hbH rfl (rate_min kt kb) C hC hC1 hCf hi
    cutoff h ρ K q x z y hsubR hkh hρ0 hρ1 hη hρη hK
  simp only [heq] at hproduct
  have leftChild (σ : Environment P J) :
      canonicalRequestChild HP D ident C cutoff h ρ K req.left σ =
        sourceChild HP D ident req.left hl C (HP.k - 1) σ :=
    canonicalRequestChild_final HP D ident req.left hl HP.k_pos C cutoff h ρ K l rfl σ
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
        canonicalRequestChild HP D ident C cutoff h ρ K req.right σ z y) -
    mid.rate * ratio neg * canonicalRequestChild HP D ident C cutoff h ρ K neg σ x y)) =
      B x y + (∑ z, E x z * B z y) - E x y
  rw [expect_sub_distrib, expect_add_distrib]
  have hdmean : (𝔼 σ ∈ S, rate kb * ratio req.direct *
      canonicalRequestChild HP D ident C cutoff h ρ K req.direct σ x y) = B x y := by
    simp_rw [directChild]
    exact hdirect
  have hnmean : (𝔼 σ ∈ S, mid.rate * ratio neg *
      canonicalRequestChild HP D ident C cutoff h ρ K neg σ x y) = E x y := hnegative
  rw [hdmean, hnmean]
  congr 1
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

/-- The actual special-negative request has the final canonical mean. Its rank is km,
usage is min(parent terminal, km), and no midpoint density is introduced. -/
theorem canonical_rawNegativeSample_mean
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P) (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (hsH : ks ≤ H.maxExponent) (hms : km ≤ ks)
    (ss sm st : List (ZMod P))
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate km) (cutoff h ρ : ℝ → ℝ) (K : ℕ) (x y : V) :
    (𝔼 σ ∈ ({σ : Environment P J |
      (gridChannel R.source ks ss).retains (channels D) σ (ident x) ∧
        (gridChannel R.terminal kt st).retains (channels D) σ (ident y)} : Finset _),
      HierarchyTask.rawNegativeSample (k := HP.k)
        (fun role b suffix σ v => channels D role b suffix σ (ident v))
        l bin .residual (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
        (gridChannel R.terminal kt st) (rate kb)
        (fun r => canonicalRequestChild HP D ident C cutoff h ρ K r σ) x y) =
    HP.toHierarchyParams.correctionIter (canonicalChannel ident (rate km))
      (canonicalChannel ident (rate km)) (rate km) C HP.k x y := by
  let neg : HierarchyTask.Request HP.k (Fin J) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask l false (Fin.last HP.k), gridChannel R.source ks ss,
      gridChannel R.terminal km st,
      ⟨R.terminal, min (rate kt) (rate km), st⟩⟩
  have hn : Admissible neg := ⟨R.source_terminal, rfl, rfl⟩
  exact canonicalRequestChild_final_mean HP D ident neg hn hD hid H hsH hms rfl rfl
    (rate_min kt km) rfl C hC hC1 hCf cutoff h ρ K l rfl
    (fun A => coordinate D (gridChannel R.terminal kt st) A (ident y)) x y
    (coordinate_min_grid D R.terminal st kt km · (ident y))

/-- Positive bin contribution before the separately routed special negative correction. -/
theorem canonical_rawPositiveSample_mean
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P) (R : RoleProfile J)
    (l bin ks km kt kb : ℕ) (hsH : ks ≤ H.maxExponent) (hms : km ≤ ks)
    (hbH : kb ≤ H.maxExponent) (ss sm st : List (ZMod P))
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate km) (cutoff h ρ : ℝ → ℝ) (K : ℕ)
    (hkh : ∀ v, cutoff v ≠ 0 → h v = 1)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ v, v ≤ η → ρ v = 1)
    (hK : 2 * (1 + 32 / η) ≤ K) (x y : V) :
    let B := fun x y => rate kb * cutoff (C x y / rate kb)
    let E := HP.toHierarchyParams.correctionIter (canonicalChannel ident (rate km))
      (canonicalChannel ident (rate km)) (rate km) C HP.k
    (𝔼 σ ∈ ({σ : Environment P J |
      (gridChannel R.source ks ss).retains (channels D) σ (ident x) ∧
        (gridChannel R.terminal kt st).retains (channels D) σ (ident y)} : Finset _),
      HierarchyTask.rawPositiveSample (k := HP.k)
        (fun role b suffix σ v => channels D role b suffix σ (ident v))
        l bin .residual (gridChannel R.source ks ss) (gridChannel R.midpoint km sm)
        (gridChannel R.terminal kt st) (rate kb)
        (fun r => canonicalRequestChild HP D ident C cutoff h ρ K r σ) x y) =
      B x y + ∑ z, E x z * B z y := by
  have hsigned := canonical_rawSample_mean HP D ident hD hid H R l bin ks km kt kb
    hsH hms hbH ss sm st C hC hC1 hCf cutoff h ρ K hkh hρ0 hρ1 hη hρη hK x y
  have hnegative := canonical_rawNegativeSample_mean HP D ident hD hid H R
    l bin ks km kt kb hsH hms ss sm st C hC hC1 hCf cutoff h ρ K x y
  dsimp only at hsigned ⊢
  simp only [HierarchyTask.rawSample, expect_sub_distrib, hnegative] at hsigned
  linarith only [hsigned]

/-- Actual finite bin decomposition of the canonical signed residual. Positive bin
samples are summed; the special endpoint correction is subtracted ONCE. The cover and
finite horizon are explicit, so this does not assert recursive statistical correctness. -/
theorem canonical_residual_bins_mean
    (hD : D ≠ 0) (hid : Function.Injective ident) (H : Horizon P) (R : RoleProfile J)
    (l ks km kt n : ℕ) (ksH : ks ≤ H.maxExponent) (hms : km ≤ ks)
    (ss sm st : List (ZMod P)) (kb : ℕ → ℕ)
    (hbH : ∀ i ∈ range (n + 1), kb i ≤ H.maxExponent)
    (C : Matrix V V ℝ) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ rate km)
    (χ : ℝ → ℝ) (hχ : ∀ v, 1 ≤ v → χ v = 1)
    (h : ℕ → ℝ → ℝ) (ρ : ℝ → ℝ) (K : ℕ)
    (hkh : ∀ i ∈ range (n + 1), ∀ v,
      routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1) v ≠ 0 → h i v = 1)
    (hρ0 : ∀ v, 0 ≤ ρ v) (hρ1 : ∀ v, ρ v ≤ 1) {η : ℝ}
    (hη : 0 < η) (hρη : ∀ v, v ≤ η → ρ v = 1)
    (hK : 2 * (1 + 32 / η) ≤ K)
    (x y : V) (hcover : ∀ z, C z y = 0 ∨ rate (kb n) ≤ C z y) :
    let cutoff := fun i => routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1)
    let source := gridChannel R.source ks ss
    let mid := gridChannel R.midpoint km sm
    let terminal := gridChannel R.terminal kt st
    (𝔼 σ ∈ ({σ : Environment P J | source.retains (channels D) σ (ident x) ∧
      terminal.retains (channels D) σ (ident y)} : Finset _),
      ((∑ i ∈ range (n + 1), HierarchyTask.rawPositiveSample (k := HP.k)
        (fun role b suffix σ v => channels D role b suffix σ (ident v))
        l i .residual source mid terminal (rate (kb i))
        (fun r => canonicalRequestChild HP D ident C (cutoff i) (h i) ρ K r σ) x y) -
      HierarchyTask.rawNegativeSample (k := HP.k)
        (fun role b suffix σ v => channels D role b suffix σ (ident v))
        l 0 .residual source mid terminal (rate (kb 0))
        (fun r => canonicalRequestChild HP D ident C (cutoff 0) (h 0) ρ K r σ) x y)) =
      HP.toHierarchyParams.residual (canonicalChannel ident (rate km))
        (canonicalChannel ident (rate km)) (rate km) C x y := by
  dsimp only
  rw [expect_sub_distrib, expect_sum_comm]
  simp_rw [canonical_rawNegativeSample_mean HP D ident hD hid H R l 0 ks km kt (kb 0)
    ksH hms ss sm st C hC hC1 hCf]
  have hp (i : ℕ) (hi : i ∈ range (n + 1)) :=
    canonical_rawPositiveSample_mean HP D ident hD hid H R l i ks km kt (kb i)
      ksH hms (hbH i hi) ss sm st C hC hC1 hCf
      (routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1)) (h i) ρ K
      (hkh i hi) hρ0 hρ1 hη hρη hK x y
  simp_rw [sum_congr rfl hp]
  have hsum (z : V) :
      ∑ i ∈ range (n + 1), rate (kb i) *
        routedBinCutoff χ (fun i => rate (kb i)) i (fun _ => 1)
          (C z y / rate (kb i)) = C z y := by
    simpa only [mul_one] using sum_routedBinCutoff (route := fun _ => 1) n
      (fun i => rate_pos (kb i)) hχ (hcover z)
  rw [sum_add_distrib, hsum, sum_comm]
  simp_rw [← mul_sum, hsum]
  rw [HierarchyParams.residual_eq, ← HierarchyParams.correctionIter_last]
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.mul_apply]
  ring

end Matrix.HierarchyParams.H4RankEnvironment
