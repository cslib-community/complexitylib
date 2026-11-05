/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyProductAllocation
public import Complexity.Foundations.Probability.RootMetric.Minkowski
import Complexity.Foundations.Probability.GridRowMoment.Rate
import Complexity.Foundations.Probability.GridRowMoment.JointDensity

/-!
# Terminal transport of actual residual product means

The masks, rather than the tables, use distinct role coordinates. Tables retain the whole
common environment. Usage support transports the literal importance-weighted parent mean
to the right child's own usage, with the actual midpoint density still present.
The actual product consumer derives both left row caps, the canonical right row cap and
estimated left incoming cap from the gates. It consumes unweighted scalar root IH at literal
bin budgets, then converts to ordinary mean error. Its explicit scale cost has cubic fine-bin
decay. Finite signed Minkowski retains a single negative request at its separate child budget.

These original finite results do not allocate the complete direct/product/negative precision
schedule, construct recursively successful availability, or pay later noise. The finite assembly
still takes ordinary component radii; it is not a completed scalar-IH schedule consumer.

## Main definitions

* `BudgetData.residualProductMean`: the literal importance-weighted parent product mean.

## Main results

* `channel_mean_change_terminal`: full-environment supported conditioning transport.
* `BudgetData.residualProduct_parent_root_le`: actual coupled child root payment.
* `BudgetData.residualProductMean_cap`: actual row gates bound both product mean tables.
* `BudgetData.residualProduct_parent_ordinary_le`: ordinary mean payment from scalar child IH.
* `BudgetData.residualProduct_ordinary_grid_coefficient_le`: rounded fine-bin cubic scale cost.
* `BudgetData.finiteInput_residual_mean_minkowski`: actual signed finite-bin assembly.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime]

/-- Grid masses are positive even outside an admitted finite horizon. -/
lemma gridMass_pos (k : ℕ) : 0 < gridMass P k := by
  unfold gridMass
  exact pow_pos (div_pos (by exact_mod_cast side_pos P k (Fact.out : P.Prime).pos)
    (by exact_mod_cast (Fact.out : P.Prime).pos)) 4

/-- Exact joint mask density; this says nothing about independence of estimated tables. -/
theorem channel_joint_density (D : ZMod P) (S T : Channel P 3)
    (hst : S.role ≠ T.role) (ks kt : ℕ) (hs : S.rate = rate ks) (ht : T.rate = rate kt)
    (x y : ZMod P) :
    (dens {σ : Environment P 3 | S.retains (channels D) σ x ∧
      T.retains (channels D) σ y} : ℝ) = gridMass P ks * gridMass P kt := by
  have h := grid_joint_density D S.role T.role hst ks kt S.suffix T.suffix x y
  simpa only [NormalizedMoments.retainedMask, CorrectionRowTask.Channel.retains,
    channels, hs, ht, semanticSide_grid] using h

/-- Change terminal conditioning before powers, preserving every spectator and suffix.
Only the masks factor; the supported table can correlate all environment coordinates. -/
theorem channel_mean_change_terminal (D : ZMod P) (S T U : Channel P 3)
    (hst : S.role ≠ T.role) (hu : U.role = T.role)
    (ka ku : ℕ) (ht : T.rate = rate ka) (hU : U.rate = rate ku)
    (hsub : ∀ σ y, U.retains (channels D) σ y → T.retains (channels D) σ y)
    (F : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hoff : ∀ σ x y, ¬ U.retains (channels D) σ y → F σ x y = 0)
    (x y : ZMod P) :
    conditionalTableMean (fun σ x => S.retains (channels D) σ x)
      (fun σ y => T.retains (channels D) σ y)
      (fun σ x y => (gridMass P ka / gridMass P ku) * F σ x y) x y =
    conditionalTableMean (fun σ x => S.retains (channels D) σ x)
      (fun σ y => U.retains (channels D) σ y) F x y := by
  have ha := expect_pi_supported_terminal S.role T.role hst
    (fun A => coordinate D S A x) (fun A => coordinate D T A y)
    (fun σ => F σ x y) (fun σ hn => hoff σ x y (fun h => hn (hsub σ y h)))
  have hb := expect_pi_supported_terminal S.role U.role (by rwa [hu])
    (fun A => coordinate D S A x) (fun A => coordinate D U A y)
    (fun σ => F σ x y) (fun σ hn => hoff σ x y hn)
  have hdT := congrArg (fun q : ℚ≥0 => (q : ℝ))
    (dens_filter_pi_eval T.role (fun A => coordinate D T A y))
  have hdU := congrArg (fun q : ℚ≥0 => (q : ℝ))
    (dens_filter_pi_eval U.role (fun A => coordinate D U A y))
  change (dens {σ : Environment P 3 | T.retains (channels D) σ y} : ℝ) = _ at hdT
  change (dens {σ : Environment P 3 | U.retains (channels D) σ y} : ℝ) = _ at hdU
  rw [channel_density D T ka ht] at hdT
  rw [channel_density D U ku hU] at hdU
  rw [← hdT, ← mul_expect] at ha
  rw [← hdU, ← mul_expect] at hb
  change gridMass P ka * conditionalTableMean _ _ F x y = _ at ha
  change gridMass P ku * conditionalTableMean _ _ F x y = _ at hb
  simp only [conditionalTableMean, ← mul_expect]
  apply mul_right_cancel₀ (gridMass_pos (P := P) ku).ne'
  dsimp only [conditionalTableMean] at ha hb
  calc
    _ = gridMass P ka * (𝔼 σ ∈ {σ | S.retains (channels D) σ x ∧
        T.retains (channels D) σ y}, F σ x y) := by
          field_simp [(gridMass_pos (P := P) ku).ne']
    _ = _ := (ha.trans hb.symm).trans (mul_comm _ _)

/-- Deterministic mean tables change integrated masks by exactly one density ratio. -/
theorem channel_rowNorm_const_change_terminal (D : ZMod P) (S T U : Channel P 3)
    (hst : S.role ≠ T.role) (hu : U.role = T.role) (ks ka ku : ℕ)
    (hs : S.rate = rate ks) (ht : T.rate = rate ka) (hU : U.rate = rate ku)
    (p : ℕ) (N u : ℝ) (v : Matrix (ZMod P) (ZMod P) ℝ) :
    rowNormPow p N u (fun σ x => S.retains (channels D) σ x)
      (fun σ y => T.retains (channels D) σ y) (fun _ => v) =
    (gridMass P ka / gridMass P ku) *
      rowNormPow p N u (fun σ x => S.retains (channels D) σ x)
        (fun σ y => U.retains (channels D) σ y) (fun _ => v) := by
  rw [rowNormPow_const_eq_dens_sum, rowNormPow_const_eq_dens_sum]
  simp_rw [channel_joint_density D S T hst ks ka hs ht,
    channel_joint_density D S U (by rwa [hu]) ks ku hs hU]
  simp only [← mul_sum]
  field_simp [(gridMass_pos (P := P) ku).ne']

end Matrix.HierarchyParams.H4RankEnvironment

namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} [Fact P.Prime]

/-- Exact root homogeneity and mask transport for deterministic nonnegative means.
The bin coefficient occurs once, as does the actual importance ratio. -/
theorem channel_rootDist_const_change_terminal (D : ZMod P) (S T U : Channel P 3)
    (hst : S.role ≠ T.role) (hu : U.role = T.role) (ks ka ku : ℕ)
    (hs : S.rate = rate ks) (ht : T.rate = rate ka) (hU : U.rate = rate ku)
    (N u c : ℝ) (hc : 0 ≤ c) (v w : Matrix (ZMod P) (ZMod P) ℝ)
    (hv : ∀ x y, 0 ≤ v x y) (hw : ∀ x y, 0 ≤ w x y) :
    rootDistPow 4 N u (fun σ x => S.retains (channels D) σ x)
      (fun σ y => T.retains (channels D) σ y)
      (fun _ x y => c * v x y) (fun _ x y => c * w x y) =
    c * (gridMass P ka / gridMass P ku) *
      rootDistPow 4 N u (fun σ x => S.retains (channels D) σ x)
        (fun σ y => U.retains (channels D) σ y) (fun _ => v) (fun _ => w) := by
  simp only [rootDistPow, Real.mul_rpow hc (hv _ _), Real.mul_rpow hc (hw _ _),
    ← mul_sub]
  rw [rowNormPow_const_mul, abs_of_nonneg (Real.rpow_nonneg hc _),
    Real.rpow_inv_natCast_pow hc (by decide : 4 ≠ 0),
    channel_rowNorm_const_change_terminal D S T U hst hu ks ka ku hs ht hU]
  ring

namespace BudgetData
variable {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP P)

/-- Literal parent product mean expressed on the reset-right child's own usage.
The factors may correlate both endpoints and the midpoint. The coefficient retains the
actual importance and midpoint density; no accuracy premise enters this identity. -/
theorem residualProduct_parent_mean (i ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hoff : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source
      (midpoint r) r.terminal (B.binRate i)).right
      ∀ σ z y, ¬ q.usage.retains (channels B.padding) σ y → R σ z y = 0)
    (x y : ZMod P) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source
      (midpoint r) r.terminal (B.binRate i)).right
    let prod := fun σ x y => ∑ z : ZMod P, L σ x z * R σ z y
    conditionalTableMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun σ x y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
        r.terminal q y * ((midpoint r).rate /
          (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ)) * prod σ x y) x y =
    (B.binRate i * (r.terminal.rate / gridMass P ka)) *
      conditionalTableMean (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y) prod x y := by
  dsimp only
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source
    (midpoint r) r.terminal (B.binRate i)).right
  have hu : q.usage.rate = rate (max ka i) := by
    dsimp only [q, HierarchyTask.rawRequests]
    rw [ht, hi, rate_min]
  have hm : (midpoint r).rate = rate ka := by simp only [midpoint, ht]
  have hratio (y : ZMod P) := usageRatio_grid B.padding r.terminal q ka (max ka i) ht hu y
  have hchange := channel_mean_change_terminal B.padding r.source r.terminal q.usage
    hst rfl ka (max ka i) ht hu (fun σ y hy => by
      change coordinate B.padding
        ⟨r.terminal.role, min r.terminal.rate (B.binRate i), r.terminal.suffix⟩
        (σ r.terminal.role) y at hy
      rw [ht, hi] at hy
      have hh := coordinate_min_grid B.padding r.terminal.role r.terminal.suffix ka i _ y hy
      simpa only [coordinate, gridChannel, ht, CorrectionRowTask.Channel.retains, channels]
        using hh)
    (fun σ x y => ∑ z : ZMod P, L σ x z * R σ z y)
    (fun σ x y hy => by
      apply sum_eq_zero
      intro z _
      rw [hoff σ z y hy, mul_zero]) x y
  calc
    _ = (B.binRate i * (r.terminal.rate / gridMass P ka)) *
        conditionalTableMean (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => (gridMass P ka / gridMass P (max ka i)) *
            ∑ z : ZMod P, L σ x z * R σ z y) x y := by
      simp only [conditionalTableMean, mul_expect]
      apply expect_congr rfl
      intro σ _
      rw [hratio, channel_density B.padding (midpoint r) ka hm]
      change B.binRate i * (gridMass P ka / gridMass P (max ka i)) *
        ((midpoint r).rate / gridMass P ka) * _ = _
      simp only [midpoint]
      ring
    _ = _ := congrArg (fun v => (B.binRate i * (r.terminal.rate / gridMass P ka)) * v) hchange

/-- Actual importance-weighted product mean on the parent terminal slice. -/
@[expose] def residualProductMean (i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    Matrix (ZMod P) (ZMod P) ℝ :=
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source
    (midpoint r) r.terminal (B.binRate i)).right
  conditionalTableMean (fun σ x => r.source.retains (channels B.padding) σ x)
    (fun σ y => r.terminal.retains (channels B.padding) σ y)
    (fun σ x y => B.binRate i * HierarchyTask.usageRatio (channels B.padding)
      r.terminal q y * ((midpoint r).rate /
        (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ)) *
      ∑ z, L σ x z * R σ z y)

/-- The prior unscaled product comparison now pays the literal parent mean. Actual
successful calls supply usage and incoming safety; root IH remains on each child's own
mask. The exact coefficient is bin-rate times terminal-rate divided by usage density. -/
theorem residualProduct_parent_root_le
    (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
    (hlight : ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hL : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row L))
    (hR : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some R) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)
    let C := B.residualCanonicalChild i
    let Xs := fun σ x => r.source.retains (channels B.padding) σ x
    let Zs := fun σ z => (midpoint r).retains (channels B.padding) σ z
    let Yu := fun σ y => Q.right.usage.retains (channels B.padding) σ y
    rootDistPow 4 P r.source.rate Xs
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ => B.residualProductMean i r L R)
      (fun _ => B.residualProductMean i r (C Q.left) (C Q.right)) ≤
    (B.binRate i * (r.terminal.rate / gridMass P ka)) *
      (gridMass P ka / gridMass P (max ka i)) * 33554432 *
      ((2 * B.binCap) * HP.K * rootDistPow 4 P r.source.rate Xs Zs L (C Q.left) +
        (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
          (r.terminal.rate / r.source.rate) *
            rootDistPow 4 P r.terminal.rate Zs Yu R (C Q.right)) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  let prod := fun (A D : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (σ : Environment P 3) (x y : ZMod P) =>
    ∑ z : ZMod P, A σ x z * D σ z y
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have hoffC (σ : Environment P 3) (z y : ZMod P)
      (hy : ¬ Q.right.usage.retains (channels B.padding) σ y) : C Q.right σ z y = 0 :=
    canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K Q.right σ z y hy
  have hmean (A D : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (hoff : ∀ σ z y, ¬ Q.right.usage.retains (channels B.padding) σ y → D σ z y = 0) :
      B.residualProductMean i r A D =
      (fun x y => (B.binRate i * (r.terminal.rate / gridMass P ka)) *
        conditionalTableMean (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => Q.right.usage.retains (channels B.padding) σ y) (prod A D) x y) := by
    funext x y
    exact B.residualProduct_parent_mean i ka r hst ht hi A D hoff x y
  rw [hmean L R hright.2, hmean (C Q.left) (C Q.right) hoffC]
  have hu : Q.right.usage.rate = rate (max ka i) := by
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hi, rate_min]
  have hc : 0 ≤ B.binRate i * (r.terminal.rate / gridMass P ka) := by
    rw [hi, ht]
    exact mul_nonneg (rate_pos i).le (div_nonneg (rate_pos ka).le (gridMass_pos (P := P) ka).le)
  rw [channel_rootDist_const_change_terminal B.padding r.source r.terminal Q.right.usage
    hst rfl ks ka (max ka i) hs ht hu P r.source.rate _ hc]
  · have h := B.residualProduct_compressed_mean_root_le M i k ζ floor r
      (by rw [hs]; exact rate_pos ks) (by rw [ht]; exact rate_pos ka)
      (by rw [hi]; exact (rate_pos i).le) hlight L R hL hR
    have hh := mul_le_mul_of_nonneg_left h
      (mul_nonneg hc (div_nonneg (gridMass_pos (P := P) ka).le
        (gridMass_pos (P := P) (max ka i)).le))
    simpa only [mul_assoc, prod, Q, C] using hh
  · intro x y
    exact expect_nonneg fun σ _ => sum_nonneg fun z _ =>
      mul_nonneg (hleft.1 σ x z).1 (hright.1 σ z y).1
  · intro x y
    apply expect_nonneg
    intro σ _
    apply sum_nonneg
    intro z _
    apply mul_nonneg
    all_goals exact (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) _ σ _ _).1


/-- Successful left row gates bound the normalized parent product mean, without width.
This identifies the ordinary conversion loss before any schedule allocation. The canonical
left cap is derived from its genuine final correction constructor, not assumed. -/
theorem residualProductMean_cap
    (M i k ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hL : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row L))
    (hR : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some R) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)
    let C := B.residualCanonicalChild i
    max ‖fun x y => B.residualProductMean i r L R x y‖
      ‖fun x y => B.residualProductMean i r (C Q.left) (C Q.right) x y‖ ≤
      (B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap)) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  let CA := 2 * HP.Q HP.toHierarchyParams.atomCap
  let CB := 2 * B.binCap
  let c := B.binRate i * (r.terminal.rate / gridMass P ka)
  have hCA : 0 ≤ CA := mul_nonneg (by norm_num) (HP.Q_nonneg _)
  have hCB : 0 ≤ CB := mul_nonneg (by norm_num) B.binCap_nonneg
  have hc : 0 ≤ c := by
    exact mul_nonneg (by rw [hi]; exact (rate_pos i).le)
      (div_nonneg (by rw [ht]; exact (rate_pos ka).le) (gridMass_pos (P := P) ka).le)
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have ha : Admissible Q.left :=
    ⟨(midpointRole_distinct r.source.role r.terminal.role).1, rfl, rfl⟩
  have hcanon (σ : Environment P 3) : C Q.left σ =
      sourceChild HP B.padding id Q.left ha B.base (HP.k - 1) σ := by
    exact canonicalRequestChild_final HP B.padding id Q.left ha HP.k_pos B.base
      (B.cutoff i) (B.auxiliary i) HP.ρ HP.K 0
      rfl σ
  have hcRow (σ : Environment P 3) (x : ZMod P) :
      #{z ∈ ({z | Q.left.terminal.retains (channels B.padding) σ z} : Finset _) |
        C Q.left σ x z ≠ 0} ≤ HP.K := by
    simp_rw [hcanon]
    exact selectedRequest_row_support HP
      (FourthRootHierarchyParams.NormalizedRow.rank_pos HP) B.padding id Q.left _ _ _ _ σ x
  have hcLeft (σ : Environment P 3) (x z : ZMod P) :
      C Q.left σ x z ∈ Set.Icc 0 CA := by
    rw [hcanon]
    exact selectedRequest_mem_Icc HP B.padding id Q.left _ _ _ _ σ x z
  have hcRight (σ : Environment P 3) (z y : ZMod P) :
      C Q.right σ z y ∈ Set.Icc 0 CB :=
    normalizedRequest_mem_Icc HP B.padding Q.right (B.cutoff i) B.binCap_nonneg
      (B.cutoff_bounds i) (fun _ => B.base)
      (densePreparation B.padding id Q.right (B.auxiliary i) HP.ρ HP.K B.base) σ z y
  have bound (A D : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (hA : ∀ σ x z, A σ x z ∈ Set.Icc 0 CA)
      (hD : ∀ σ z y, D σ z y ∈ Set.Icc 0 CB)
      (hAU : ∀ σ x z, ¬ Q.left.usage.retains (channels B.padding) σ z → A σ x z = 0)
      (hDU : ∀ σ z y, ¬ Q.right.usage.retains (channels B.padding) σ y → D σ z y = 0)
      (hrow : ∀ σ x, #{z ∈
        ({z | Q.left.terminal.retains (channels B.padding) σ z} : Finset _) |
          A σ x z ≠ 0} ≤ HP.K) :
      ‖fun x y => B.residualProductMean i r A D x y‖ ≤ c * (HP.K * CA * CB) := by
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro x
    apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
    intro y
    rw [Real.norm_eq_abs]
    simp only [residualProductMean]
    rw [B.residualProduct_parent_mean i ka r hst ht hi A D hDU x y]
    rw [abs_mul, abs_of_nonneg hc]
    apply mul_le_mul_of_nonneg_left _ hc
    rw [conditionalTableMean]
    rw [abs_of_nonneg (expect_nonneg fun σ _ =>
      sum_nonneg fun z _ => mul_nonneg (hA σ x z).1 (hD σ z y).1)]
    rcases ({σ : Environment P 3 | r.source.retains (channels B.padding) σ x ∧
      Q.right.usage.retains (channels B.padding) σ y} : Finset _).eq_empty_or_nonempty
      with hempty | hnonempty
    · change (𝔼 σ ∈ ({σ : Environment P 3 | r.source.retains (channels B.padding) σ x ∧
        Q.right.usage.retains (channels B.padding) σ y} : Finset _), _) ≤ _
      rw [hempty, expect_empty]
      positivity
    apply expect_le hnonempty
    intro σ _
    let T := ({z | Q.left.terminal.retains (channels B.padding) σ z ∧
      A σ x z ≠ 0} : Finset (ZMod P))
    have he : ∑ z, A σ x z * D σ z y = ∑ z ∈ T, A σ x z * D σ z y := by
      rw [sum_filter]
      apply sum_congr rfl
      intro z _
      split_ifs with hz
      · rfl
      · by_cases h : Q.left.usage.retains (channels B.padding) σ z
        · have hzero : A σ x z = 0 := by
            by_contra hn
            exact hz ⟨h, hn⟩
          rw [hzero, zero_mul]
        · rw [hAU σ x z h, zero_mul]
    rw [he]
    calc
      _ ≤ ∑ _z ∈ T, CA * CB := sum_le_sum fun z _ =>
        mul_le_mul (hA σ x z).2 (hD σ z y).2 (hD σ z y).1 hCA
      _ = (#T : ℝ) * (CA * CB) := by simp only [sum_const, nsmul_eq_mul]
      _ ≤ HP.K * (CA * CB) := mul_le_mul_of_nonneg_right
        (by
          have hcard : #T ≤ HP.K := by simpa only [T, filter_filter] using hrow σ x
          exact_mod_cast hcard) (mul_nonneg hCA hCB)
      _ = _ := by ring
  apply max_le
  · exact bound L R hleft.1 hright.1 hleft.2.1 hright.2 hleft.2.2
  · apply bound (C Q.left) (C Q.right) hcLeft hcRight _ _ hcRow
    all_goals
      exact fun σ x y hy => canonicalRequestChild_zero_off_usage HP B.padding id
        B.base (B.cutoff i) (B.auxiliary i) HP.ρ HP.K _ σ x y hy

/-- Ordinary product mean payment from unweighted scalar root IH on the two actual
child masks. Both left row caps come from their actual gates. No field width or bin count
is introduced. The ordinary conversion costs the cube of the explicitly bounded product
mean scale; a uniform precision allocation is not asserted. -/
theorem residualProduct_parent_ordinary_le
    (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i)
    (hlight : ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (L R : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hL : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row L))
    (hR : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some R)
    (εL εR : ℝ)
    (hEL : let Q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
      rootDistPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ z => (midpoint r).retains (channels B.padding) σ z)
        L (B.residualCanonicalChild i Q.left) ≤ εL ^ 4)
    (hER : let Q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
      rootDistPow 4 P r.terminal.rate
        (fun σ z => (midpoint r).retains (channels B.padding) σ z)
        (fun σ y => Q.right.usage.retains (channels B.padding) σ y)
        R (B.residualCanonicalChild i Q.right) ≤ εR ^ 4) :
    let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)
    let A := B.residualProductMean i r L R
    let C := B.residualProductMean i r
      (B.residualCanonicalChild i Q.left) (B.residualCanonicalChild i Q.right)
    let cap := (B.binRate i * (r.terminal.rate / gridMass P ka)) *
      (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))
    rowNormPow 4 P r.source.rate
      (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.terminal.retains (channels B.padding) σ y)
      (fun _ x y => A x y - C x y) ≤
    (4 * cap ^ ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((2 * B.binCap) * HP.K * εL ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * εR ^ 4)) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  have hp := B.residualProduct_parent_root_le M i k ks ka ζ floor r hst hs ht hi hlight
    L R hL hR
  have hspos : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  have htpos : 0 < r.terminal.rate := by rw [ht]; exact rate_pos ka
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have hn (A D : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
      (hA : ∀ σ x z, 0 ≤ A σ x z) (hD : ∀ σ z y, 0 ≤ D σ z y) (x y : ZMod P) :
      0 ≤ B.residualProductMean i r A D x y := by
    apply expect_nonneg
    intro σ _
    have hb : 0 ≤ B.binRate i := by rw [hi]; exact (rate_pos i).le
    exact mul_nonneg (mul_nonneg (mul_nonneg hb (by unfold HierarchyTask.usageRatio; positivity))
      (div_nonneg htpos.le (by positivity)))
      (sum_nonneg fun z _ => mul_nonneg (hA σ x z) (hD σ z y))
  have hcanon (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (σ : Environment P 3) (x y : ZMod P) : 0 ≤ C q σ x y :=
    (canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
      (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y).1
  have hnorm (A : Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) : A x y ≤ ‖fun x y => A x y‖ :=
    (le_abs_self _).trans (by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (fun y => A x y) y).trans
          (norm_le_pi_norm (fun x y => A x y) x))
  have hcap := B.residualProductMean_cap M i k ka ζ floor r hst ht hi L R hL hR
  have hconvert := rowNormPow_sub_le_rootDistPow (s := 4)
    (N := (P : ℝ)) (u := r.source.rate)
    (X := fun σ x => r.source.retains (channels B.padding) σ x)
    (Y := fun σ y => r.terminal.retains (channels B.padding) σ y)
    (C := (B.binRate i * (r.terminal.rate / gridMass P ka)) *
      (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap)))
    (H := fun _ => B.residualProductMean i r L R)
    (H' := fun _ => B.residualProductMean i r (C Q.left) (C Q.right))
    (by decide) (mul_nonneg (Nat.cast_nonneg P) hspos.le)
    (fun _ x y _ _ => ⟨hn L R (fun σ x z => (hleft.1 σ x z).1)
      (fun σ z y => (hright.1 σ z y).1) x y, (hnorm _ x y).trans ((le_max_left _ _).trans hcap)⟩)
    (fun _ x y _ _ => ⟨hn _ _ (hcanon Q.left) (hcanon Q.right) x y,
      (hnorm _ x y).trans ((le_max_right _ _).trans hcap)⟩)
  norm_num only [Nat.cast_ofNat, show ((4 : ℝ) - 1) / 4 = 3 / 4 by norm_num] at hconvert
  apply hconvert.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply hp.trans
  apply mul_le_mul_of_nonneg_left
  · exact add_le_add
      (mul_le_mul_of_nonneg_left hEL
        (mul_nonneg (mul_nonneg (by norm_num) B.binCap_nonneg) (Nat.cast_nonneg _)))
      (mul_le_mul_of_nonneg_left hER (mul_nonneg
        (mul_nonneg (mul_nonneg (by norm_num) (HP.Q_nonneg _)) (Nat.cast_nonneg _))
        (div_nonneg htpos.le hspos.le)))
  · exact mul_nonneg (mul_nonneg
      (mul_nonneg (by rw [hi]; exact (rate_pos i).le)
        (div_nonneg htpos.le (gridMass_pos (P := P) ka).le))
      (div_nonneg (gridMass_pos (P := P) ka).le
        (gridMass_pos (P := P) (max ka i)).le)) (by norm_num)


/-- Exact ordinary conversion coefficient after the actual row cap. In particular root
homogeneity alone does not justify treating this ordinary cost as linear in the bin scale. -/
theorem residualProduct_ordinary_coefficient (c H q : ℝ) (hc : 0 ≤ c) (hH : 0 ≤ H) :
    (4 * (c * H) ^ ((3 : ℝ) / 4)) ^ 4 * (c * q) =
      256 * H ^ 3 * c ^ 4 * q := by
  have he : ((c * H) ^ ((3 : ℝ) / 4)) ^ 4 = (c * H) ^ 3 := by
    rw [← Real.rpow_mul_natCast (mul_nonneg hc hH)]
    norm_num
  rw [mul_pow, he]
  ring

/-- The literal density factor has cubic fine-bin decay before precision or rank salary
is used. Both rounded masses come from an actual admitted horizon; nominal rates are not
substituted for them. The estimate is independent of the field width and bin count. -/
theorem residualProduct_density_cost_le (H : Horizon P) (ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent) :
    (rate i * (rate ka / gridMass P ka)) ^ 4 *
      (gridMass P ka / gridMass P (max ka i)) ≤
        16 * (rate i) ^ 3 * max (rate i) (rate ka) := by
  have hmass := gridMass_bounds H ha
  have hnorm : 0 ≤ rate ka / gridMass P ka :=
    div_nonneg (rate_pos ka).le (gridMass_pos (P := P) ka).le
  have hnorm1 : rate ka / gridMass P ka ≤ 1 :=
    (div_le_one (gridMass_pos (P := P) ka)).mpr hmass.1
  have hpow : (rate ka / gridMass P ka) ^ 4 ≤ 1 := by
    simpa only [one_pow] using pow_le_pow_left₀ hnorm hnorm1 4
  have himportance := gridMass_importance_le H ha hi
  have hratio : 0 ≤ gridMass P ka / gridMass P (max ka i) :=
    div_nonneg (gridMass_pos (P := P) ka).le (gridMass_pos (P := P) (max ka i)).le
  calc
    _ = (rate ka / gridMass P ka) ^ 4 * ((rate i) ^ 3 *
        (rate i * (gridMass P ka / gridMass P (max ka i)))) := by ring
    _ ≤ 1 * ((rate i) ^ 3 *
        (rate i * (gridMass P ka / gridMass P (max ka i)))) :=
      mul_le_mul_of_nonneg_right hpow
        (mul_nonneg (pow_nonneg (rate_pos i).le _) (mul_nonneg (rate_pos i).le hratio))
    _ ≤ (rate i) ^ 3 * (16 * max (rate i) (rate ka)) := by
      rw [one_mul]
      exact mul_le_mul_of_nonneg_left himportance (pow_nonneg (rate_pos i).le _)
    _ = _ := by ring


/-- The ordinary coefficient used by the actual product consumer inherits the rounded
fine-bin cubic estimate. This is a coefficient bound, not a precision allocation. -/
theorem residualProduct_ordinary_grid_coefficient_le (H : Horizon P) (ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent) (W : ℝ) (hW : 0 ≤ W) :
    (4 * ((rate i * (rate ka / gridMass P ka)) * W) ^ ((3 : ℝ) / 4)) ^ 4 *
      ((rate i * (rate ka / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i))) ≤
    256 * W ^ 3 * (16 * (rate i) ^ 3 * max (rate i) (rate ka)) := by
  rw [residualProduct_ordinary_coefficient _ _ _
    (mul_nonneg (rate_pos i).le
      (div_nonneg (rate_pos ka).le (gridMass_pos (P := P) ka).le)) hW]
  rw [mul_assoc (256 * W ^ 3)]
  exact mul_le_mul_of_nonneg_left (residualProduct_density_cost_le H ka i ha hi) (by positivity)


/-- Exact loss when the ordinary product estimate is normalized by the parent terminal
rate. The midpoint rate cancels, but four inverse powers of the actual parent density
remain. A coarse-bin relative/clipped improvement needs additional proved canonical-mean
domination; this identity does not establish an actual-error obstruction. -/
theorem residualProduct_normalized_ordinary_coefficient
    (b f πa πu W : ℝ) (hb : 0 ≤ b) (hf : 0 < f) (hπa : 0 < πa)
    (hπu : 0 < πu) (hW : 0 ≤ W) :
    (1 / f) ^ 4 * ((4 * ((b * (f / πa)) * W) ^ ((3 : ℝ) / 4)) ^ 4 *
      ((b * (f / πa)) * (πa / πu))) =
        256 * W ^ 3 * (b / πa) ^ 4 * (πa / πu) := by
  rw [residualProduct_ordinary_coefficient _ _ _ (mul_nonneg hb (div_nonneg hf.le hπa.le)) hW]
  field_simp [hf.ne', hπa.ne', hπu.ne']

/-- Executed finite means assemble by Minkowski at roots, retaining one negative call
outside the bins. The inputs are ordinary mean estimates, for example those derived from
actual scalar root IH by `residualProduct_parent_ordinary_le`; this assembly does not
supply the missing direct/negative allocations or successful recursive history. -/
theorem finiteInput_residual_mean_minkowski
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : 0 ≤ r.source.rate)
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hc : ∀ i ∈ B.bins, ∀ q ∈
      ({(HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).direct,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).left,
        (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
          r.terminal (B.binRate i)).right} : Finset _),
      row history (B.binBudget M i r) q = some (child i q))
    (hn : let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        {r.terminal with rate := (midpoint r).rate},
        {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩
      row history (B.childBudget M) q = some (child 0 q))
    (ε : Option ℕ → ℝ) (hε : ∀ o, 0 ≤ ε o)
    (hpositive : ∀ i ∈ B.bins,
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
            r.source (midpoint r) r.terminal (B.binRate i) (fun q => child i q σ) x y -
              HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual
                r.source (midpoint r) r.terminal (B.binRate i)
                (fun q => B.residualCanonicalChild i q σ) x y) x y) ≤ ε (some i) ^ 4)
    (hnegative : rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
            r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
              HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
                r.source (midpoint r) r.terminal (B.binRate 0)
                (fun q => B.residualCanonicalChild 0 q σ) x y) x y) ≤ ε none ^ 4) :
    ∃ executed, B.finiteInput history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          (fun σ x y => executed σ x y - B.residualCanonicalInput r σ x y) x y) ≤
        (ε none + ∑ i ∈ B.bins, ε (some i)) ^ 4 := by
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let positive := fun i σ x y => HierarchyTask.rawPositiveSample (channels B.padding)
    0 i .residual r.source (midpoint r) r.terminal (B.binRate i) (fun q => child i q σ) x y -
      HierarchyTask.rawPositiveSample (channels B.padding) 0 i .residual r.source
        (midpoint r) r.terminal (B.binRate i) (fun q => B.residualCanonicalChild i q σ) x y
  let negative := fun σ x y => HierarchyTask.rawNegativeSample (channels B.padding)
    0 0 .residual r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
      HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual r.source
        (midpoint r) r.terminal (B.binRate 0) (fun q => B.residualCanonicalChild 0 q σ) x y
  let F : Option ℕ → Environment P 3 → ZMod P → ZMod P → ℝ := fun o _ x y =>
    match o with
    | none => -(rowSliceMean X Y negative x y)
    | some i => rowSliceMean X Y (positive i) x y
  let S : Finset (Option ℕ) := insert none (B.bins.image some)
  have hnone : (none : Option ℕ) ∉ B.bins.image some := by simp
  have hsum (v : Option ℕ → ℝ) : ∑ o ∈ S, v o = v none + ∑ i ∈ B.bins, v (some i) := by
    rw [show S = insert none (B.bins.image some) from rfl, sum_insert hnone,
      sum_image (fun _ _ _ _ h => Option.some.inj h)]
  have h := rowNormPow_sum_le_pow_sum (X := X) (by decide : 4 ≠ 0)
    (mul_nonneg (Nat.cast_nonneg P) hs) Y S F (fun _ => 1) ε
    (fun _ _ => by norm_num) (fun o _ => hε o) (by
      intro o ho
      cases o with
      | none => simpa only [F, rowNormPow, abs_neg] using hnegative
      | some i =>
        have hi : i ∈ B.bins := by simpa [S] using ho
        exact hpositive i hi)
  simp only [one_mul] at h
  rw [hsum ε] at h
  simp_rw [hsum (fun o => F o _ _ _)] at h
  refine ⟨_, B.finiteInput_residual_of_rows history M r child hc hn, ?_⟩
  convert h using 1
  congr 1
  funext σ x y
  simp only [rowSliceMean, residualCanonicalInput, expect_sub_distrib, expect_sum_comm,
    F, positive, negative, X, Y]
  rw [sum_sub_distrib]
  ring

end BudgetData
end Matrix.HierarchyParams.H4RankEnvironment
