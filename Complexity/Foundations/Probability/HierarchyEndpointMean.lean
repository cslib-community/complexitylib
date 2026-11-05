/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyCoarseProductMean
public import Complexity.Foundations.Probability.HierarchySignedDomination

/-!
# Clipped endpoint means on their own usage masks

The endpoint comparison clips after conditioning. Only the canonical carried mean
is dominated; estimated tables may depend on the whole environment. The separate
negative request has the parent's terminal usage, so its physical rate cancels
the normalization rate. Its scalar root IH is paid once at `childBudget`.
These original consequences of finite fidelity do not construct recursive availability.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators

namespace Cslib

/-- Positive conditional means with a physical normalization rate. The child error
is integrated on its own usage; no weighted IH or table independence is required. -/
theorem rowNormPow_endpoint_clipped_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u f c K : ℝ}
    (hNu : 0 ≤ N * u) (hf : 0 < f) (hc : 0 ≤ c) (hK : 0 ≤ K)
    (X Y U : Ω → V → Prop) [∀ σ x, Decidable (X σ x)]
    [∀ σ y, Decidable (Y σ y)] [∀ σ y, Decidable (U σ y)]
    (A C : Ω → V → V → ℝ) (G : V → V → ℝ)
    (hA : ∀ σ x y, 0 ≤ A σ x y) (hC : ∀ σ x y, 0 ≤ C σ x y)
    (hG : ∀ x y, 0 ≤ G x y)
    (hoff : ∀ σ x y, ¬ U σ y → A σ x y = C σ x y)
    (hdom : ∀ x y, c * rowSliceMean X Y C x y ≤ K * G x y) :
    rowNormPow 4 N u X Y (fun _ x y =>
      min 1 (|c * rowSliceMean X Y (fun σ x y => A σ x y - C σ x y) x y| /
        (f + G x y))) ≤
      (512 * (3 * K + 3) ^ 3) * (c / f) * rootDistPow 4 N u X U A C := by
  apply rowNormPow_le_rootDistPow_of_conditional hNu X Y U A C _ _
    (by positivity) hoff
  intro x y
  have hd : (c / f) * rowSliceMean X Y C x y ≤ K * (G x y / f) := by
    have hh := div_le_div_of_nonneg_right (hdom x y) hf.le
    convert hh using 1 <;> ring
  have h := min_relative_expect_sub_four_le
    ({σ | X σ x ∧ Y σ y} : Finset Ω) (div_nonneg hc hf.le)
    (div_nonneg (hG x y) hf.le) hK (fun σ _ => hC σ x y)
    (fun σ _ => hA σ x y) hd
  have heq : |(c / f) * rowSliceMean X Y
      (fun σ x y => A σ x y - C σ x y) x y| / (1 + G x y / f) =
      |c * rowSliceMean X Y (fun σ x y => A σ x y - C σ x y) x y| /
        (f + G x y) := by
    rw [div_mul_eq_mul_div, abs_div, abs_of_pos hf]
    field_simp
  change min 1 (|(c / f) * rowSliceMean X Y
    (fun σ x y => A σ x y - C σ x y) x y| / (1 + G x y / f)) ^ 4 ≤ _ at h
  rw [heq] at h
  rw [abs_of_nonneg (show 0 ≤ min 1
    (|c * rowSliceMean X Y (fun σ x y => A σ x y - C σ x y) x y| /
      (f + G x y)) by
      exact le_min (by norm_num)
        (div_nonneg (abs_nonneg _) (add_nonneg hf.le (hG x y))))]
  exact h

/-- An ordinary fourth moment also pays clipped relative error. This fallback can
be minimized with the sharper carried-mean estimate before finite assembly. -/
theorem rowNormPow_clipped_le_of_ordinary
    {Ω V : Type*} [Fintype Ω] [Fintype V] {N u f : ℝ}
    (hNu : 0 ≤ N * u) (hf : 0 < f)
    (X Y : Ω → V → Prop) [∀ σ x, Decidable (X σ x)] [∀ σ y, Decidable (Y σ y)]
    (e G : V → V → ℝ) (hG : ∀ x y, 0 ≤ G x y) :
    rowNormPow 4 N u X Y (fun _ x y => min 1 (|e x y| / (f + G x y))) ≤
      (1 / f) ^ 4 * rowNormPow 4 N u X Y (fun _ => e) := by
  apply rowNormPow_le_mul hNu
  intro σ x y _ _
  have hb : min 1 (|e x y| / (f + G x y)) ≤ (1 / f) * |e x y| := by
    apply (min_le_right _ _).trans
    rw [one_div_mul_eq_div]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hf (le_add_of_nonneg_right (hG x y))
  rw [abs_of_nonneg (show 0 ≤ min 1 (|e x y| / (f + G x y)) from
    le_min (by norm_num) (div_nonneg (abs_nonneg _) (add_nonneg hf.le (hG x y)))),
    ← mul_pow]
  exact pow_le_pow_left₀ (le_min (by norm_num)
    (div_nonneg (abs_nonneg _) (add_nonneg hf.le (hG x y)))) hb 4

end Cslib

namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- The actual direct compressed bin is compared on its own usage mask. The
canonical mean is computed from the dense constructor and the genuine bin
partition. The explicit endpoint density is retained to its first power. -/
theorem residualDirect_parent_clipped_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (hD : B.padding ≠ 0) (H : Horizon P) (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hib : i ∈ B.bins) (hiH : i ≤ H.maxExponent)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hkh : ∀ v, B.cutoff i v ≠ 0 → B.auxiliary i v = 1)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some A)
    (ε : ℝ)
    (hE : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        A (B.residualCanonicalChild i q) ≤ ε ^ 4) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
    let c := B.binRate i * (gridMass P ka / gridMass P (max ka i))
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|c * rowSliceMean
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y => A σ x y - B.residualCanonicalChild i q σ x y) x y| /
          (rate ka + G x y))) ≤
      (512 * (3 * K + 3) ^ 3) * (c / rate ka) * ε ^ 4 := by
  dsimp only
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)).direct
  let C := B.residualCanonicalChild i q
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let c := B.binRate i * (gridMass P ka / gridMass P (max ka i))
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base
  let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
  have hi : B.binRate i = rate i := congrFun hrate i
  have hu : q.usage.rate = rate (max ka i) := by
    dsimp only [q, HierarchyTask.rawRequests]
    rw [ht, hi, rate_min]
  have hqp : Admissible q := ⟨hst, rfl, rfl⟩
  have hbounds := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor q A hA
  have hc (σ : Environment P 3) (x y : ZMod P) : 0 ≤ C σ x y :=
    (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y).1
  have hmean (x y : ZMod P) : c * rowSliceMean X Y C x y =
      B.binRate i * B.cutoff i (B.base x y / B.binRate i) := by
    have hsub (a : FrameChannel P 4 1) : splitUsage B.padding id q a y →
        coordinate B.padding r.terminal a y := by
      have hh := coordinate_min_grid B.padding r.terminal.role r.terminal.suffix ka i a y
      simpa only [splitUsage, q, HierarchyTask.rawRequests, ht, hi,
        coordinate, gridChannel, id_eq] using hh
    have hm := denseChild_mean_on_terminal_event B.padding id q hqp hD
      Function.injective_id H hks hs hiH hi hu (B.cutoff i) (B.auxiliary i)
      HP.ρ HP.K B.base (fun a => coordinate B.padding r.terminal a y) x y hsub
      hkh HP.ρ_nonneg HP.ρ_le_one HP.η_pos HP.ρ_one (hC x)
      (by simpa [Matrix.mulVec, dotProduct] using hC1 x) hK
    change (𝔼 σ ∈ {σ | X σ x ∧ Y σ y},
      (B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal q y) *
        C σ x y) = _ at hm
    rw [usageRatio_grid B.padding r.terminal q ka (max ka i) ht hu y,
      ← mul_expect] at hm
    exact hm
  have hdom (x y : ZMod P) : c * rowSliceMean X Y C x y ≤ K * G x y := by
    rw [hmean]
    apply HP.toHierarchyParams.bin_le_residual
      (canonicalChannel id (rate ka)) (canonicalChannel id (rate ka))
      (rate_pos ka) hC hC1 hCf
      (A := fun x y => B.binRate i * B.cutoff i (B.base x y / B.binRate i)) ?_ x y
    intro x y
    have hb0 (j : ℕ) : 0 ≤ B.binRate j * B.cutoff j (B.base x y / B.binRate j) :=
      mul_nonneg (by rw [hrate]; exact (rate_pos j).le) (B.cutoff_bounds j _).1
    exact (single_le_sum (fun j _ => hb0 j) hib).trans
      ((B.initialBins_polynomial_sum n hbins hrate hcutoff hC hC1 x y).trans_le
        (mul_le_of_le_one_right (hC x y) (polynomialSwitch4_le_one _ _ _)))
  have h := rowNormPow_endpoint_clipped_le (N := (P : ℝ)) (u := r.source.rate)
    (mul_nonneg (Nat.cast_nonneg P) (by rw [hs]; exact (rate_pos ks).le))
    (rate_pos ka) (show 0 ≤ c by
      exact mul_nonneg (by rw [hi]; exact (rate_pos i).le)
        (div_nonneg (gridMass_pos ka).le (gridMass_pos _).le))
    (show 0 ≤ K from le_trans (by norm_num) (le_max_left _ _))
    X Y (fun σ y => q.usage.retains (channels B.padding) σ y) A C G
    (fun σ x y => (hbounds.1 σ x y).1) hc
    (fun x y => HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)
    (fun σ x y hy => by
      change A σ x y = canonicalRequestChild HP B.padding id B.base (B.cutoff i)
        (B.auxiliary i) HP.ρ HP.K q σ x y
      rw [hbounds.2 σ x y hy,
        canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff i)
          (B.auxiliary i) HP.ρ HP.K q σ x y hy]) hdom
  exact h.trans (mul_le_mul_of_nonneg_left hE (by
    exact mul_nonneg (by positivity) (div_nonneg
      (mul_nonneg (by rw [hi]; exact (rate_pos i).le)
        (div_nonneg (gridMass_pos ka).le (gridMass_pos _).le)) (rate_pos ka).le)))

/-- Actual separate negative mean from the scalar root IH of the successful final
correction request at its literal child budget. Canonical domination is derived
from the genuine recurrence. The negative sign is applied only during assembly. -/
theorem residualNegative_parent_clipped_le
    (hD : B.padding ≠ 0) (H : Horizon P) (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      B.evaluate (B.childBudget M) q = some (.row A))
    (ε : ℝ)
    (hE : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        A (B.residualCanonicalChild 0 q) ≤ ε ^ 4) :
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => min 1 (|rowSliceMean
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ x y =>
          HierarchyTask.rawNegativeSample (k := HP.k) (channels B.padding) 0 0 .residual
            r.source (midpoint r) r.terminal (B.binRate 0) (fun _ => A σ) x y -
          HierarchyTask.rawNegativeSample (k := HP.k) (channels B.padding) 0 0 .residual
            r.source (midpoint r) r.terminal (B.binRate 0)
            (fun q => B.residualCanonicalChild 0 q σ) x y) x y| /
        (rate ka + G x y))) ≤ (512 * (3 * K + 3) ^ 3) * ε ^ 4 := by
  dsimp only
  let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
      {r.terminal with rate := (midpoint r).rate},
      {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
  let C := B.residualCanonicalChild 0 q
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base
  let K := max 1 (((HP.k : ℝ) + 1) / HP.θ)
  have hu : q.usage = r.terminal := by simp [q, midpoint]
  have hbounds := B.evaluate_normalized_bounds (B.childBudget M) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ q
    (by simp only [q, HierarchyTask.correctionAtomTask_last HP.k_pos,
      Bool.false_eq_true, ↓reduceIte]) A hA
  have hc (σ : Environment P 3) (x y : ZMod P) : 0 ≤ C σ x y :=
    (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff 0)
      (B.auxiliary 0) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds 0)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y).1
  have hratio (y : ZMod P) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal q y = 1 := by
    unfold HierarchyTask.usageRatio
    rw [hu, channel_density B.padding r.terminal ka ht]
    exact div_self (gridMass_pos ka).ne'
  have hsample (F : HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (σ : Environment P 3) (x y : ZMod P) :
      HierarchyTask.rawNegativeSample (k := HP.k) (channels B.padding) 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0) (fun v => F v σ) x y =
        rate ka * F q σ x y := by
    change (midpoint r).rate * HierarchyTask.usageRatio (channels B.padding)
      r.terminal q y * F q σ x y = _
    rw [hratio, mul_one]
    simp only [midpoint, ht]
  have hmean (x y : ZMod P) : rate ka * rowSliceMean X Y C x y =
      HP.toHierarchyParams.correction (canonicalChannel id (rate ka))
        (canonicalChannel id (rate ka)) (rate ka) B.base x y := by
    let roles : RoleProfile 3 := ⟨r.source.role, midpointRole r.source.role r.terminal.role,
      r.terminal.role, (midpointRole_distinct _ _).1, hst, (midpointRole_distinct _ _).2⟩
    have hsrc : r.source = gridChannel roles.source ks r.source.suffix := by
      change r.source = {r.source with rate := rate ks}; rw [← hs]
    have hterm : r.terminal = gridChannel roles.terminal ka r.terminal.suffix := by
      change r.terminal = {r.terminal with rate := rate ka}; rw [← ht]
    have hm : midpoint r = gridChannel roles.midpoint ka [] := by
      simp only [midpoint, ht, gridChannel, roles]
    have hn := canonical_rawNegativeSample_mean HP B.padding id hD Function.injective_id
      H roles 0 0 ks ka ka 0 hks hka r.source.suffix [] r.terminal.suffix
      B.base hC hC1 hCf (B.cutoff 0) (B.auxiliary 0) HP.ρ HP.K x y
    rw [HP.toHierarchyParams.correctionIter_last] at hn
    rw [← hsrc, ← hterm, ← hm] at hn
    change (𝔼 σ ∈ {σ | X σ x ∧ Y σ y},
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0)
        (fun v => B.residualCanonicalChild 0 v σ) x y) = _ at hn
    simp_rw [hsample] at hn
    rw [← mul_expect] at hn
    exact hn
  have h := rowNormPow_endpoint_clipped_le (N := (P : ℝ)) (u := r.source.rate)
    (mul_nonneg (Nat.cast_nonneg P) (by rw [hs]; exact (rate_pos ks).le))
    (rate_pos ka) (rate_pos ka).le (show 0 ≤ K from le_trans (by norm_num) (le_max_left _ _))
    X Y (fun σ y => q.usage.retains (channels B.padding) σ y) A C G
    (fun σ x y => (hbounds.1 σ x y).1) hc
    (fun x y => HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)
    (fun σ x y hy => by
      change A σ x y = canonicalRequestChild HP B.padding id B.base (B.cutoff 0)
        (B.auxiliary 0) HP.ρ HP.K q σ x y
      rw [hbounds.2.1 σ x y hy,
        canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff 0)
          (B.auxiliary 0) HP.ρ HP.K q σ x y hy])
    (fun x y => by
      rw [hmean]
      exact HP.toHierarchyParams.correction_le_residual _ _ (rate_pos ka) hC hC1 hCf x y)
  rw [div_self (rate_pos ka).ne', mul_one] at h
  apply le_trans ?_ (h.trans (mul_le_mul_of_nonneg_left hE (by positivity)))
  apply le_of_eq
  congr 1
  funext σ x y
  simp_rw [hsample]
  simp only [rowSliceMean, ← mul_sub, ← mul_expect]
  rfl

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
