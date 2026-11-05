/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyActiveBins
public import Complexity.Foundations.Probability.HierarchyInitialPerturbation
public import Complexity.Foundations.Probability.RootMetric.BoundedMean
public import Complexity.Foundations.Analysis.GeometricOffset
import Complexity.Foundations.Probability.GridRowMoment.JointDensity

/-!
# Bounded direct means on their own usage slice

The actual signed consumer retains the direct coarse/ordinary minimum alongside
the active product minimum. One fixed charge, chosen after HP and the bin cap,
pays the entire direct sum over arbitrary admitted horizons. The joint signed
fixed-charge theorem, product sum and once-negative allocation remain separate;
this is not completion of the signed allocation or recursive availability.

The ordinary comparison converts bounded entries on the direct child's own usage
before changing the terminal mask. It retains the exact rounded density ratio and
all correlation of the child error with the common environment. These are original
consequences of the bounded conversion and conditional-slice APIs used by the
initial sharp fine comparison.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators

namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- The actual direct compressed and canonical entries lie in the same bounded
interval. Exact mask transport gives one reciprocal rounded mass, not its fourth
power, in the ordinary normalized moment before clipping. -/
theorem residualDirect_parent_ordinary_le
    (hrate : B.binRate = rate) (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin (B.binBudget M i r) i k ζ floor q = some A) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
    let c := B.binRate i * (gridMass P ka / gridMass P (max ka i))
    rowNormPow 4 P r.source.rate X Y
      (fun _ x y => (c / rate ka) * rowSliceMean X Y
        (A - B.residualCanonicalChild i q) x y) ≤
      (256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
      rootDistPow 4 P r.source.rate X
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        A (B.residualCanonicalChild i q) := by
  dsimp only
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)).direct
  let C := B.residualCanonicalChild i q
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let U := fun σ y => q.usage.retains (channels B.padding) σ y
  let t := gridMass P (max ka i) / gridMass P ka
  let c := B.binRate i * (gridMass P ka / gridMass P (max ka i))
  have hNu : 0 ≤ (P : ℝ) * r.source.rate :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hs]; exact (rate_pos ks).le)
  have htp : 0 < t := div_pos (gridMass_pos _) (gridMass_pos _)
  have hu : q.usage.rate = rate (max ka i) := by
    dsimp only [q, HierarchyTask.rawRequests]
    rw [ht, hrate, rate_min]
  have hdens (j : ℕ) (x y : ZMod P) :
      (({σ | X σ x ∧ NormalizedMoments.retainedMask r.terminal.role (side P j)
        B.padding r.terminal.suffix σ y} :
          Finset (Environment P 3)).dens : ℝ) = gridMass P ks * gridMass P j := by
    simpa only [X, CorrectionRowTask.Channel.retains, channels, semanticSide_grid, hs,
      NormalizedMoments.retainedMask, NormalizedMoments.retainedMask] using
      grid_joint_density B.padding r.source.role r.terminal.role hst ks j
        r.source.suffix r.terminal.suffix x y
  have hY : Y = NormalizedMoments.retainedMask r.terminal.role (side P ka)
      B.padding r.terminal.suffix := by
    funext σ y
    simp only [Y, CorrectionRowTask.Channel.retains, channels, semanticSide_grid, ht,
      NormalizedMoments.retainedMask]
  have hU : U = NormalizedMoments.retainedMask r.terminal.role (side P (max ka i))
      B.padding r.terminal.suffix := by
    funext σ y
    simp only [U, q, HierarchyTask.rawRequests, CorrectionRowTask.Channel.retains,
      channels, semanticSide_grid, ht, hrate, rate_min, NormalizedMoments.retainedMask]
  have hsub (σ : Environment P 3) (y : ZMod P) : U σ y → Y σ y := by
    rw [hU, hY]
    intro hy
    apply mem_retentionBox.2
    have hside : side P (max ka i) ≤ side P ka := by
      rw [side_eq_ceil, side_eq_ceil]
      gcongr
      · norm_num
      · exact le_max_left ka i
    exact fun j => ((mem_retentionBox.1 hy) j).trans_le hside
  have hbounds := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor q A hA
  have hoff (σ : Environment P 3) (x y : ZMod P) (hy : ¬ U σ y) :
      (A - C) σ x y = 0 := by
    rw [show (A - C) σ x y = A σ x y - C σ x y from rfl,
      hbounds.2 σ x y hy]
    have hc := canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff i)
      (B.auxiliary i) HP.ρ HP.K q σ x y hy
    change C σ x y = 0 at hc
    rw [hc, sub_self]
  have hmean := rowSliceMean_eq_density_mul_of_subset htp.ne' X Y U (A - C) hsub hoff
    (by intro x y
        apply dens_ne_zero.mp
        have hp : (0 : ℝ) < ({σ | X σ x ∧ U σ y} : Finset (Environment P 3)).dens := by
          simp only [hU, hdens]
          exact mul_pos (gridMass_pos _) (gridMass_pos _)
        exact_mod_cast hp.ne')
    (by intro x y
        simp only [hY, hU, hdens]
        dsimp only [t]
        field_simp [(gridMass_pos (P := P) ks).ne', (gridMass_pos (P := P) ka).ne',
          (gridMass_pos (P := P) (max ka i)).ne'])
  have hh := rowNormPow_bounded_sliceMean_fourth_le hNu htp.le
    (mul_nonneg (by norm_num) B.binCap_nonneg) X Y U A C
    (fun σ x y _ _ => hbounds.1 σ x y)
    (fun σ x y _ _ => by
      change normalizedRequest B.padding id q (B.cutoff i) HP.ρ HP.K
        (fun _ => B.base) (densePreparation B.padding id q (B.auxiliary i) HP.ρ HP.K B.base)
        σ x y ∈ Set.Icc 0 (2 * B.binCap)
      exact normalizedRequest_mem_Icc HP B.padding q (B.cutoff i)
        B.binCap_nonneg (B.cutoff_bounds i) _ _ σ x y) hmean
    (by intro x y
        simp only [hY, hU, hdens]
        dsimp only [t]
        field_simp [(gridMass_pos (P := P) ka).ne'])
  have hscale : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => (c / rate ka) * rowSliceMean X Y (A - C) x y) =
      (c / rate ka) ^ 4 * rowNormPow 4 P r.source.rate X Y
        (fun _ => rowSliceMean X Y (A - C)) := by
    rw [rowNormPow_const_mul]
    exact congrArg (fun z => z * rowNormPow 4 P r.source.rate X Y
      (fun _ => rowSliceMean X Y (A - C))) (by
        rw [pow_abs, abs_of_nonneg (by positivity : 0 ≤ (c / rate ka) ^ 4)])
  change rowNormPow 4 P r.source.rate X Y _ ≤ _
  rw [hscale]
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ (c / rate ka) ^ 4)).trans_eq
  change (c / rate ka) ^ 4 * (t ^ 3 * (256 * (2 * B.binCap) ^ 3) *
    rootDistPow 4 P r.source.rate X U A C) =
    (256 * (2 * B.binCap) ^ 3) *
      ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        rootDistPow 4 P r.source.rate X U A C
  dsimp only [c, t]
  rw [hrate]
  field_simp [(gridMass_pos (P := P) ka).ne',
    (gridMass_pos (P := P) (max ka i)).ne', (rate_pos ka).ne']


/-- The bounded ordinary direct comparison pays relative clipping against the
genuine signed target, from the actual direct child's own-mask scalar IH. -/
theorem residualDirect_parent_fine_clipped_le
    (hrate : B.binRate = rate) (M i k ks ka : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hC : ∀ x y, 0 ≤ B.base x y)
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
    let X := fun σ x => r.source.retains (channels B.padding) σ x
    let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
    let c := B.binRate i * (gridMass P ka / gridMass P (max ka i))
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|c * rowSliceMean X Y
        (A - B.residualCanonicalChild i q) x y| / (rate ka + G x y))) ≤
      (256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε ^ 4 := by
  dsimp only
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)).direct
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let c := B.binRate i * (gridMass P ka / gridMass P (max ka i))
  let e := fun x y => rowSliceMean X Y (A - B.residualCanonicalChild i q) x y
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
    (canonicalChannel id (rate ka)) (rate ka) B.base
  have hNu : 0 ≤ (P : ℝ) * r.source.rate :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hs]; exact (rate_pos ks).le)
  have hc : 0 ≤ c := mul_nonneg (by rw [hrate]; exact (rate_pos i).le)
    (div_nonneg (gridMass_pos _).le (gridMass_pos _).le)
  have hclip : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|c * e x y| / (rate ka + G x y))) ≤
      rowNormPow 4 P r.source.rate X Y (fun _ x y => (c / rate ka) * e x y) := by
    have hh := rowNormPow_le_mul (s := 4) (X := X) (Y := Y) hNu (c := (1 : ℝ))
      (Z := fun (_ : Environment P 3) x y => min 1 (|c * e x y| / (rate ka + G x y)))
      (Z' := fun _ x y => (c / rate ka) * e x y) (by
        intro σ x y _ _
        have hf := rate_pos ka
        have hG : 0 ≤ G x y := HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y
        rw [one_mul, abs_of_nonneg (show 0 ≤ min 1
          (|c * e x y| / (rate ka + G x y)) by positivity)]
        apply pow_le_pow_left₀ (by positivity : 0 ≤ min 1
          (|c * e x y| / (rate ka + G x y)))
        apply (min_le_right _ _).trans
        rw [abs_mul, abs_of_nonneg hc, abs_mul,
          abs_of_nonneg (div_nonneg hc (rate_pos ka).le), div_mul_eq_mul_div]
        exact div_le_div_of_nonneg_left (by positivity) (rate_pos ka)
          (le_add_of_nonneg_right hG))
    simpa only [one_pow, one_mul] using hh
  apply hclip.trans
  apply (B.residualDirect_parent_ordinary_le hrate M i k ks ka ζ floor r hst hs ht A hA).trans
  exact mul_le_mul_of_nonneg_left hE (mul_nonneg
    (by have := B.binCap_nonneg; positivity)
    (mul_nonneg (by positivity) (div_nonneg (gridMass_pos _).le (gridMass_pos _).le)))

/-- Actual signed finite input with coarse/ordinary minima for direct and product payments.
Successful recursive calls and scalar IH remain on their literal own masks and budgets. -/
theorem finiteInput_residual_clipped_direct_min_le
    (n : ℕ) (hbins : B.bins = range (n + 1)) (hrate : B.binRate = rate)
    (hcutoff : B.cutoff = fun i => boundedRoutedBinCutoff (polynomialSwitch4 (1 / 2) 1)
      rate 1 i (fun _ => 1))
    (haux : B.auxiliary = fun _ => polynomialPrepCutoff4 HP.θ)
    (hD : B.padding ≠ 0) (H : Horizon P) (hnH : n ≤ H.maxExponent)
    (M ks ka : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hst : r.source.role ≠ r.terminal.role)
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hks : ks ≤ H.maxExponent) (hka : ka ≤ ks)
    (hC : ∀ x y, 0 ≤ B.base x y) (hC1 : B.base *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, B.base x y ≤ rate ka)
    (hcover : ∀ z y, B.base z y = 0 ∨ rate n ≤ B.base z y)
    (hkh : ∀ i ∈ B.bins, ∀ v, B.cutoff i v ≠ 0 → B.auxiliary i v = 1)
    (hlight : ∀ i ∈ B.bins, ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (hK : 2 * (1 + 32 / HP.η) ≤ HP.K)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (child : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (depth : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℕ)
    (ζ floor : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (ε : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ)
    (hrows : ∀ i ∈ B.bins,
      let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)
      ∀ q ∈ ({Q.direct, Q.left, Q.right} : Finset _),
        row history (B.binBudget M i r) q = some (child i q))
    (hnrow : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      row history (B.childBudget M) q = some (child 0 q))
    (hdirect : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hleft : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      B.evaluate (B.binBudget M i r) q = some (.row (child i q)))
    (hright : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      B.compressedBin (B.binBudget M i r) i (depth i q) (ζ i q) (floor i q) q =
        some (child i q))
    (hnegative : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      B.evaluate (B.childBudget M) q = some (.row (child 0 q)))
    (hID : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIL : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIR : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤ ε (B.binBudget M i r) q ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤ ε (B.childBudget M) q ^ 4) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
    let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let d := fun i => min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
    let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
    let p := fun i => min (pc i) (po i)
    let ne := F * ε (B.childBudget M) neg ^ 4
    let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
    ∃ executed, B.finiteInput history M .residual r = some executed ∧
      rowNormPow 4 P r.source.rate
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun _ x y => min 1 (|rowSliceMean
          (fun σ x => r.source.retains (channels B.padding) σ x)
          (fun σ y => r.terminal.retains (channels B.padding) σ y)
          executed x y - G x y| /
            (rate ka + G x y))) ≤
        (ne ^ (4⁻¹ : ℝ) + ∑ i ∈ B.bins, d i ^ (4⁻¹ : ℝ) +
          ∑ i ∈ B.bins, p i ^ (4⁻¹ : ℝ)) ^ 4 := by
  dsimp only
  let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i))
  let neg := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let d := fun i => min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) *
        ε (B.binBudget M i r) (Q i).direct ^ 4)
  let pc := fun i => (F / rate ka) *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let po := fun i => (1 / rate ka) ^ 4 *
      (4 * ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (HP.K * (2 * HP.Q HP.toHierarchyParams.atomCap) * (2 * B.binCap))) ^
          ((3 : ℝ) / 4)) ^ 4 *
      ((B.binRate i * (r.terminal.rate / gridMass P ka)) *
        (gridMass P ka / gridMass P (max ka i)) * 33554432 *
        ((if ka ≤ i then 2 * B.binCap else 0) * HP.K * ε (B.binBudget M i r) (Q i).left ^ 4 +
          (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
            (r.terminal.rate / r.source.rate) * ε (B.binBudget M i r) (Q i).right ^ 4))
  let p := fun i => min (pc i) (po i)
  let ne := F * ε (B.childBudget M) neg ^ 4
  let G := HP.toHierarchyParams.residual (canonicalChannel id (rate ka))
      (canonicalChannel id (rate ka)) (rate ka) B.base
  let X := fun σ x => r.source.retains (channels B.padding) σ x
  let Y := fun σ y => r.terminal.retains (channels B.padding) σ y
  let de := fun i x y =>
    (B.binRate i * (gridMass P ka / gridMass P (max ka i))) *
      rowSliceMean X Y (fun σ x y =>
        child i (Q i).direct σ x y - B.residualCanonicalChild i (Q i).direct σ x y) x y
  let pe := fun i x y => B.residualProductMean i r (child i (Q i).left)
    (child i (Q i).right) x y - B.residualProductMean i r
      (B.residualCanonicalChild i (Q i).left) (B.residualCanonicalChild i (Q i).right) x y
  let nege := fun x y => -rowSliceMean X Y (fun σ x y =>
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0) (fun q => child 0 q σ) x y -
    HierarchyTask.rawNegativeSample (channels B.padding) 0 0 .residual
      r.source (midpoint r) r.terminal (B.binRate 0)
      (fun q => B.residualCanonicalChild 0 q σ) x y) x y
  have hNu : 0 ≤ (P : ℝ) * r.source.rate :=
    mul_nonneg (Nat.cast_nonneg _) (by rw [hs]; exact (rate_pos ks).le)
  have hiH (i : ℕ) (hi : i ∈ B.bins) : i ≤ H.maxExponent := by
    rw [hbins, mem_range] at hi
    omega
  have hde (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|de i x y| / (rate ka + G x y))) ≤ d i := by
    apply le_min
    · exact B.residualDirect_parent_clipped_le n hbins hrate hcutoff hD H M i
        (depth i (Q i).direct) ks ka (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht
        hks hi (hiH i hi) hC hC1 hCf (hkh i hi) hK
        (child i (Q i).direct) (hdirect i hi) (ε (B.binBudget M i r) (Q i).direct) (hID i hi)
    · exact B.residualDirect_parent_fine_clipped_le hrate M i (depth i (Q i).direct) ks ka
        (ζ i (Q i).direct) (floor i (Q i).direct) r hst hs ht hC
        (child i (Q i).direct) (hdirect i hi) (ε (B.binBudget M i r) (Q i).direct) (hID i hi)
  have hpe (i : ℕ) (hi : i ∈ B.bins) : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|pe i x y| / (rate ka + G x y))) ≤ p i := by
    apply le_min
    · exact B.residualProduct_active_parent_clipped_le n hbins hrate hcutoff haux hD H M i
        (depth i (Q i).right) ks ka (ζ i (Q i).right) (floor i (Q i).right)
        r hst hs ht (congrFun hrate i)
        hks hka hi (hiH i hi) hC hC1 hCf (hlight i hi)
        (child i (Q i).left) (child i (Q i).right) (hleft i hi) (hright i hi)
        (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
        (hIL i hi) (hIR i hi)
    · apply (rowNormPow_clipped_le_of_ordinary hNu (rate_pos ka) X Y (pe i) G
        (fun x y => HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)).trans
      dsimp only [po]
      rw [mul_assoc]
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      exact B.residualProduct_active_parent_ordinary_le M i (depth i (Q i).right) ks ka
        (ζ i (Q i).right) (floor i (Q i).right) r hrate hcutoff hCf hst hs ht (congrFun hrate i)
        (hlight i hi)
        (child i (Q i).left) (child i (Q i).right) (hleft i hi) (hright i hi)
        (ε (B.binBudget M i r) (Q i).left) (ε (B.binBudget M i r) (Q i).right)
        (hIL i hi) (hIR i hi)
  have hne : rowNormPow 4 P r.source.rate X Y
      (fun _ x y => min 1 (|nege x y| / (rate ka + G x y))) ≤ ne := by
    simp only [nege, abs_neg]
    exact B.residualNegative_parent_clipped_le hD H M ks ka r hst hs ht hks hka
      hC hC1 hCf (child 0 neg) hnegative (ε (B.childBudget M) neg) hIN
  let S : Finset (Option (ℕ ⊕ ℕ)) := insert none
    ((B.bins.image (fun i => some (Sum.inl i))) ∪
      (B.bins.image (fun i => some (Sum.inr i))))
  let e : Option (ℕ ⊕ ℕ) → ZMod P → ZMod P → ℝ := fun o =>
    match o with
    | none => nege
    | some (.inl i) => de i
    | some (.inr i) => pe i
  let pay : Option (ℕ ⊕ ℕ) → ℝ := fun o =>
    match o with
    | none => ne
    | some (.inl i) => d i
    | some (.inr i) => p i
  have hsum (v : Option (ℕ ⊕ ℕ) → ℝ) : ∑ o ∈ S, v o =
      v none + ∑ i ∈ B.bins, v (some (.inl i)) + ∑ i ∈ B.bins, v (some (.inr i)) := by
    have hd : Disjoint (B.bins.image (fun i => some (Sum.inl i)))
        (B.bins.image (fun i => some (Sum.inr i))) := by
      simp only [disjoint_left, mem_image]
      rintro o ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
      cases he
    rw [show S = _ from rfl, sum_insert (by simp), sum_union hd,
      sum_image (fun _ _ _ _ h => by simpa using h),
      sum_image (fun _ _ _ _ h => by simpa using h)]
    ring
  have h := rowNormPow_clipped_sum_le_pow_sum S hNu X Y e
    (fun x y => rate ka + G x y)
    (fun x y => add_pos_of_pos_of_nonneg (rate_pos ka)
      (HP.toHierarchyParams.residual_nonneg (rate_pos ka) hC x y)) pay (by
        intro o ho
        cases o with
        | none => exact hne
        | some a =>
          cases a with
          | inl i => exact hde i (by simpa [S] using ho)
          | inr i => exact hpe i (by simpa [S] using ho))
  rw [hsum (fun o => pay o ^ (4⁻¹ : ℝ))] at h
  simp only [pay] at h
  simp_rw [hsum (fun o => e o _ _)] at h
  refine ⟨_, B.finiteInput_residual_of_rows history M r child hrows hnrow, ?_⟩
  have htarget (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (x y : ZMod P) :
      rowSliceMean X Y A x y - G x y = rowSliceMean X Y
        (fun σ x y => A σ x y - B.residualCanonicalInput r σ x y) x y := by
    have href := B.residualCanonicalInput_mean n hbins hrate hcutoff haux hD H hnH
      r r.source.role r.terminal.role hst ks ka r.source.suffix r.terminal.suffix
      (by change r.source = {r.source with rate := rate ks}; rw [← hs])
      (by change r.terminal = { r.terminal with rate := rate ka}; rw [← ht])
      hks hka hC hC1 hCf x y (fun z => hcover z y)
    change rowSliceMean X Y (B.residualCanonicalInput r) x y = G x y at href
    rw [← href]
    exact (expect_sub_distrib _ _ _).symm
  change rowNormPow 4 P r.source.rate X Y (fun _ x y =>
    min 1 (|rowSliceMean X Y _ x y - G x y| / (rate ka + G x y))) ≤ _
  simp_rw [htarget]
  convert h using 1
  congr 1
  funext σ x y
  congr 2
  congr 1
  simp only [rowSliceMean, residualCanonicalInput, expect_sub_distrib,
    expect_sum_comm, HierarchyTask.rawPositiveSample, expect_add_distrib,
    e, de, pe, nege, residualProductMean, conditionalTableMean, X, Y]
  have hratio (i : ℕ) : HierarchyTask.usageRatio (channels B.padding)
      r.terminal (Q i).direct y = gridMass P ka / gridMass P (max ka i) := by
    apply usageRatio_grid B.padding r.terminal (Q i).direct ka (max ka i) ht
    dsimp only [Q, HierarchyTask.rawRequests]
    rw [ht, hrate, rate_min]
  dsimp only [Q] at hratio ⊢
  simp_rw [hratio, ← mul_expect]
  simp only [mul_sub, sum_sub_distrib, sum_add_distrib]
  ring


omit [Fact P.Prime] in
/-- Actual truncated bin budgets lose at most their scale cutoff. This bound holds
also for exhausted budgets; no positive-precision guard is silently assumed. -/
theorem binBudget_precision_loss (M ka i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (ht : r.terminal.rate = rate ka) :
    ((M : ℝ) - B.binBudget M i r) / (16 * B.slack) ≤
      1 / 16 + |(i : ℝ) - ka| / 4 := by
  have hslack : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  have habs : (((ka : ℤ) - i).natAbs : ℝ) = |(i : ℝ) - ka| := by
    rw [Nat.cast_natAbs, Int.cast_abs]
    push_cast
    exact abs_sub_comm _ _
  have hcost : (LogSpaceEstimation.scaleCutoff B.slack
      (B.sampleScale r (some i)) : ℝ) = B.slack * (1 + 4 * |(i : ℝ) - ka|) := by
    rw [B.sampleScale_grid r ka i hrate ht, LogSpaceEstimation.scaleCutoff,
      Int.natAbs_mul]
    norm_num only [Int.natAbs_natCast, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_ofNat, habs]
  have hcut : 1 ≤ LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i)) := by
    unfold LogSpaceEstimation.scaleCutoff
    have hh := B.slack_pos
    have hn := Nat.zero_le (B.sampleScale r (some i)).natAbs
    nlinarith
  have hb : M ≤ B.binBudget M i r +
      LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i)) := by
    simp only [binBudget, sampleScale, Option.map_some, Option.getD_some] at *
    rw [LogSpaceEstimation.lastBudget, max_eq_right hcut]
    omega
  have hc : (M : ℝ) ≤ (B.binBudget M i r : ℝ) +
      (LogSpaceEstimation.scaleCutoff B.slack (B.sampleScale r (some i)) : ℝ) := by
    exact_mod_cast hb
  rw [hcost] at hc
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mpr
  nlinarith

omit [Fact P.Prime] in
/-- The sharp piecewise direct scale leaves three quarters of a bin offset after
paying the actual budget loss. The exact residual-to-direct rank gap is retained. -/
theorem residualDirect_scale_salary (M ks ka i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
    (2 : ℝ) ^ (if i ≤ ka then (ka : ℝ) - i else -3 * ((i : ℝ) - ka)) *
        (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q) ≤
      (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) *
        (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4) := by
  dsimp only
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
    r.source (midpoint r) r.terminal (B.binRate i)).direct
  have hq := B.requestPrecision_residual_direct M (B.binBudget M i r) ks ka i r hs ht
    (congrFun hrate i)
  have hg := residual_base_rank_gap (HP := HP) i
  have hc : (q.task.rank : ℝ) + (80 * (HP.k : ℝ) + 94) = r.task.rank := by
    rw [hr]
    exact_mod_cast hg
  change B.requestPrecision (B.binBudget M i r) q - B.requestPrecision M r = _ at hq
  have hb := B.binBudget_precision_loss M ka i r hrate ht
  rw [sub_div] at hb hq
  rw [← hc] at hq
  simp only [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  split_ifs with hi
  · have hh : (i : ℝ) ≤ ka := by exact_mod_cast hi
    rw [abs_of_nonpos (sub_nonpos.mpr hh)] at hb ⊢
    nlinarith
  · have hh : (ka : ℝ) ≤ i := by exact_mod_cast (Nat.le_of_not_ge hi)
    rw [abs_of_nonneg (sub_nonneg.mpr hh)] at hb ⊢
    nlinarith

/-- The new ordinary direct coefficient agrees with the existing sharp initial
fine coefficient. Its proved rounded-grid envelope supplies cubic moment decay. -/
theorem residualDirect_fine_coefficient_le (H : Horizon P) (ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent) (hai : ka < i) :
    (256 * (2 * B.binCap) ^ 3) *
      ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) ≤
        (32768 * B.binCap ^ 3) * (rate i / rate ka) ^ 3 := by
  have hh := B.initialClippedRootCoefficient_fine_le H ka i ha hi hai
  simpa only [initialClippedRootCoefficient, ite_eq_right (not_le.mpr hai),
    max_eq_right hai.le, show (256 : ℝ) * (2 * B.binCap) ^ 3 =
      2048 * B.binCap ^ 3 by ring] using hh


/-- The actual direct minimum, at literal own precision, has geometric offset
decay. The constant depends on fixed hierarchy primitives and bin cap only. -/
theorem residualDirect_min_root_salary (H : Horizon P) (M ks ka i : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let D := max 1 F * max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)
    let ε := (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q)
    (min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) * ε ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε ^ 4)) ^
      (4⁻¹ : ℝ) ≤
    D ^ (4⁻¹ : ℝ) * (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) *
      (2 : ℝ) ^ (-3 * |(i : ℝ) - ka| / 4) := by
  dsimp only
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let D := max 1 F * max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)
  let ε := (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r)
    (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct)
  let scale := (2 : ℝ) ^ (if i ≤ ka then (ka : ℝ) - i else -3 * ((i : ℝ) - ka))
  have hc := B.binCap_nonneg
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hD : 0 ≤ D := by dsimp only [D]; positivity
  have hmi := gridMass_pos (P := P) i
  have hma := gridMass_pos (P := P) ka
  have hm0 : 0 ≤ gridMass P ka / gridMass P (max ka i) :=
    div_nonneg (gridMass_pos _).le (gridMass_pos _).le
  have hcoarse : 0 ≤ (rate i * (gridMass P ka / gridMass P (max ka i))) / rate ka :=
    div_nonneg (mul_nonneg (rate_pos i).le
      (div_nonneg (gridMass_pos _).le (gridMass_pos _).le)) (rate_pos ka).le
  have hcoef : min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka))
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i)))) ≤
      max 1 F * B.initialClippedRootCoefficient ka i := by
    by_cases hia : i ≤ ka
    · apply (min_le_left _ _).trans
      rw [hrate, initialClippedRootCoefficient, ite_eq_left hia]
      have hb : 1 ≤ (512 : ℝ) * (6 * B.binCap + 3) ^ 3 := by
        have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
          (by linarith : (1 : ℝ) ≤ 6 * B.binCap + 3) 3
        norm_num at hh
        linarith
      have hh : F ≤ max 1 F * (512 * (6 * B.binCap + 3) ^ 3) := by
        exact (le_max_right 1 F).trans
          (le_mul_of_one_le_right (le_trans (by norm_num) (le_max_left _ _)) hb)
      nlinarith [mul_le_mul_of_nonneg_right hh hcoarse]
    · apply (min_le_right _ _).trans
      rw [initialClippedRootCoefficient, ite_eq_right hia]
      have hh : (256 : ℝ) * (2 * B.binCap) ^ 3 = 2048 * B.binCap ^ 3 := by ring
      rw [hh, max_eq_right (Nat.le_of_not_ge hia)]
      exact le_mul_of_one_le_left (by positivity) (le_max_left 1 F)
  have he : min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) * ε ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε ^ 4) ≤
      D * (scale * ε) ^ 4 := by
    rw [← min_mul_of_nonneg _ _ (by positivity : 0 ≤ ε ^ 4)]
    apply (mul_le_mul_of_nonneg_right hcoef (by positivity : 0 ≤ ε ^ 4)).trans
    have hh := mul_le_mul_of_nonneg_left
      (B.initialClippedRootCoefficient_le H ka i ha hi)
      (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left 1 F))
    have hj := mul_le_mul_of_nonneg_right hh (by positivity : 0 ≤ ε ^ 4)
    convert hj using 1; dsimp only [D, scale]; ring
  have hmin : 0 ≤ min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) * ε ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε ^ 4) := by
    rw [hrate]
    exact le_min (mul_nonneg (mul_nonneg hF hcoarse) (by positivity))
      (by positivity)
  have hh := Real.rpow_le_rpow hmin he (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hroot : ((scale * ε) ^ 4) ^ (4⁻¹ : ℝ) = scale * ε := by
    convert Real.pow_rpow_inv_natCast (by positivity : 0 ≤ scale * ε)
      (by decide : (4 : ℕ) ≠ 0) using 1
  rw [Real.mul_rpow hD (by positivity : 0 ≤ (scale * ε) ^ 4), hroot] at hh
  apply hh.trans
  have hp := mul_le_mul_of_nonneg_left
    (B.residualDirect_scale_salary M ks ka i r hrate hs ht hr) (Real.rpow_nonneg hD (4⁻¹ : ℝ))
  simpa only [D, scale, ε, F, mul_assoc] using hp


/-- The direct minima in the actual signed consumer sum geometrically, over any
finite admitted bin set, without a bin-count factor. -/
theorem residualDirect_min_sum_salary (H : Horizon P) (M ks ka : ℕ)
    (ha : ka ≤ H.maxExponent) (hi : ∀ i ∈ B.bins, i ≤ H.maxExponent)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hrate : B.binRate = rate) (hs : r.source.rate = rate ks)
    (ht : r.terminal.rate = rate ka) (hr : r.task = .residual 0) :
    let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
      r.source (midpoint r) r.terminal (B.binRate i)).direct
    let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
    let D := max 1 F * max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)
    let ε := fun i => (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) (Q i))
    (∑ i ∈ B.bins, (min
      (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) * ε i ^ 4)
      ((256 * (2 * B.binCap) ^ 3) *
        ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε i ^ 4)) ^
      (4⁻¹ : ℝ)) ≤
    (2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ))) * D ^ (4⁻¹ : ℝ) *
      (2 : ℝ) ^ (-B.requestPrecision M r) *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge) := by
  dsimp only
  have hh := sum_le_sum fun i hib =>
    B.residualDirect_min_root_salary H M ks ka i ha (hi i hib) r hrate hs ht hr
  apply hh.trans
  simp only [← mul_sum]
  have hc := B.binCap_nonneg
  have hg := mul_le_mul_of_nonneg_left (sum_two_rpow_offset_le B.bins ka)
    (by positivity : 0 ≤
      (max 1 (512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3) *
        max (512 * (6 * B.binCap + 3) ^ 3) (32768 * B.binCap ^ 3)) ^ (4⁻¹ : ℝ) *
          (2 : ℝ) ^ (-B.requestPrecision M r) *
          (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * B.rankCharge))
  convert hg using 1; ring


/-- Primitive constant for the entire direct-bin sum. The hierarchy, including
its iteration count and cutoff parameters, is fixed before this constant. -/
@[expose] def residualDirectRootCost (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (cap : ℝ) : ℝ :=
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  (2 / (1 - (2 : ℝ) ^ (-3 / 4 : ℝ))) *
    (max 1 F * max (512 * (6 * cap + 3) ^ 3) (32768 * cap ^ 3)) ^ (4⁻¹ : ℝ)

omit [Fact P.Prime] in
/-- A direct charge exists before the field, all exponents and the budget.
This allocates the direct sum only; it does not assert joint signed allocation. -/
theorem exists_residualDirect_charge (cap : ℝ) :
    ∃ A : ℕ, residualDirectRootCost HP cap *
      (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * A) ≤ 1 / 4 := by
  let C := residualDirectRootCost HP cap
  obtain ⟨n, hn⟩ := exists_nat_gt C
  have hpow : (n : ℝ) ≤ (2 : ℝ) ^ n := by
    exact_mod_cast (Nat.lt_two_pow_self (n := n)).le
  have hC : C ≤ (2 : ℝ) ^ (n : ℝ) := by
    rw [Real.rpow_natCast]
    exact hn.le.trans hpow
  refine ⟨n + 4, ?_⟩
  change C * (2 : ℝ) ^ (1 / 16 - (80 * (HP.k : ℝ) + 94) * (n + 4 : ℕ)) ≤ 1 / 4
  apply (mul_le_mul_of_nonneg_right hC (by positivity)).trans
  rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  have he : (n : ℝ) + (1 / 16 - (80 * (HP.k : ℝ) + 94) * (n + 4 : ℕ)) ≤ -2 := by
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) n, Nat.cast_nonneg (α := ℝ) HP.k]
  have hh := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) he
  norm_num at hh ⊢
  exact hh


/-- One fixed primitive charge pays every direct bin in every finite grid horizon.
The choice precedes fields, source/terminal exponents, suffixes and budgets. This
is the direct part of the signed consumer, not a payment of its product sum. -/
theorem residualDirect_min_sum_exists_charge (cap : ℝ) :
    ∃ A : ℕ, ∀ {P : ℕ} [Fact P.Prime] (B : BudgetData HP P),
      B.binCap = cap → B.rankCharge = A → B.binRate = rate →
      ∀ (H : Horizon P) (M ks ka : ℕ), ka ≤ H.maxExponent →
      (∀ i ∈ B.bins, i ≤ H.maxExponent) →
      ∀ (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)),
      r.source.rate = rate ks → r.terminal.rate = rate ka → r.task = .residual 0 →
      let Q := fun i => (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).direct
      let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
      let ε := fun i => (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) (Q i))
      (∑ i ∈ B.bins, (min
        (F * ((B.binRate i * (gridMass P ka / gridMass P (max ka i))) / rate ka) * ε i ^ 4)
        ((256 * (2 * B.binCap) ^ 3) *
          ((rate i / rate ka) ^ 4 * (gridMass P ka / gridMass P (max ka i))) * ε i ^ 4)) ^
        (4⁻¹ : ℝ)) ≤ (2 : ℝ) ^ (-B.requestPrecision M r) / 4 := by
  obtain ⟨A, hA⟩ := exists_residualDirect_charge (HP := HP) cap
  refine ⟨A, ?_⟩
  intro P _ B hcap hcharge hrate H M ks ka ha hi r hs ht hr
  apply (B.residualDirect_min_sum_salary H M ks ka ha hi r hrate hs ht hr).trans
  have hh := mul_le_mul_of_nonneg_right hA
    (Real.rpow_nonneg (by norm_num : (0 : ℝ) ≤ 2) (-B.requestPrecision M r))
  rw [← hcap, ← hcharge] at hh
  dsimp only [residualDirectRootCost] at hh
  convert hh using 1 <;> ring

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
