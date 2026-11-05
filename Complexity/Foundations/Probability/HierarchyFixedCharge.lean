/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchySignedClippedMean

/-!
# Fixed primitive charge for the full-rate signed consumer

The admissible family here has one bin, full source and terminal rates, and the
stage-zero residual constructor. The charge depends on the hierarchy parameters
and primitive bin cap, before the field, suffixes, compression depths and budget.
Successful recursive calls and their own-mask IH remain explicit hypotheses.
This bounded rate family does not settle allocation at arbitrary grid exponents.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8}

/-- The exact coarse rooted coefficient at full rates, including direct and
once-negative costs. There is no field width, coordinate or budget in this constant. -/
@[expose] def fullRateRootCost (HP : FourthRootHierarchyParams 16 1 16 32 8)
    (cap : ℝ) : ℝ :=
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  2 * F ^ (4⁻¹ : ℝ) +
    (F * 33554432 * ((2 * cap) * HP.K +
      (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊)) ^ (4⁻¹ : ℝ)

/-- A primitive charge can be fixed before any execution coordinates are chosen.
The absolute logarithm also covers constants below one. -/
theorem exists_fullRate_charge (cap : ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ fullRateRootCost HP cap ≤ (2 : ℝ) ^ (A - 1) := by
  let C := fullRateRootCost HP cap
  refine ⟨1 + |Real.logb 2 (max 1 C)|, by positivity, ?_⟩
  have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
    (le_abs_self (Real.logb 2 (max 1 C)))
  rw [Real.rpow_logb (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_left 1 C))] at h
  simpa only [add_sub_cancel_left] using (le_max_right 1 C).trans h

/-- Literal zero-scale schedule: the precision loss is at most one sixteenth,
including truncated budgets. It is derived, rather than assumed as sample accuracy. -/
theorem childBudget_precision_loss (B : BudgetData HP P) (M : ℕ) :
    ((M : ℝ) - B.childBudget M) / (16 * B.slack) ≤ 1 / 16 := by
  have hs : 1 ≤ B.slack := B.slack_pos
  have hn : M ≤ B.childBudget M + B.slack := by
    simp only [childBudget, LogSpaceEstimation.lastBudget,
      LogSpaceEstimation.scaleCutoff, Int.natAbs_zero, Nat.add_zero, Nat.mul_one]
    omega
  have hc : (M : ℝ) ≤ (B.childBudget M : ℝ) + B.slack := by exact_mod_cast hn
  have hp : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mpr
  nlinarith

/-- Full-rate own-request salary, on the actual child budget. The source may be
inherited or reset: both rates are checked, and the computed rank gap is mandatory. -/
theorem fullRate_child_salary (B : BudgetData HP P) (M : ℕ)
    (r q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate 0) (ht : r.terminal.rate = rate 0)
    (hqs : q.source.rate = rate 0) (hqt : q.terminal.rate = rate 0)
    (hrank : q.task.rank < r.task.rank) (hA : 0 ≤ B.rankCharge) :
    (2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q) ≤
      ((2 : ℝ) ^ (1 - B.rankCharge)) * (2 : ℝ) ^ (-B.requestPrecision M r) := by
  rw [B.requestPrecision_grid M 0 0 r hs ht,
    B.requestPrecision_grid (B.childBudget M) 0 0 q hqs hqt,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  have hr : (q.task.rank : ℝ) + 1 ≤ r.task.rank := by exact_mod_cast hrank
  have hg := mul_le_mul_of_nonneg_left hr hA
  have hb := B.childBudget_precision_loss M
  rw [sub_div] at hb
  norm_num only [Nat.cast_zero, zero_add, mul_zero, sub_zero]
  linarith

/-- Positive precision persists for all sufficiently large budgets after fixing the
charge and constructor. Thus the bounded family is not restricted to inactive calls. -/
theorem fullRate_precision_eventually_pos (B : BudgetData HP P)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate 0) (ht : r.terminal.rate = rate 0) :
    ∃ M₀ : ℕ, ∀ M ≥ M₀, 0 < B.requestPrecision M r := by
  obtain ⟨M₀, hM₀⟩ := exists_nat_gt (16 * (B.slack : ℝ) * (B.rankCharge * r.task.rank))
  refine ⟨M₀, fun M hM => ?_⟩
  rw [B.requestPrecision_grid M 0 0 r hs ht]
  norm_num only [Nat.cast_zero, zero_add, mul_zero, sub_zero]
  apply sub_pos.mpr
  have hslack : (0 : ℝ) < B.slack := by exact_mod_cast B.slack_pos
  apply (lt_div_iff₀ (by positivity : (0 : ℝ) < 16 * B.slack)).mpr
  have hcast : (M₀ : ℝ) ≤ M := by exact_mod_cast hM
  nlinarith

/-- The residual direct/reset-right constructor has a growing actual rank gap. -/
theorem residual_base_rank_gap (i : ℕ) :
    (HierarchyTask.baseNormalized (k := HP.k) 0 i).rank + (80 * HP.k + 94) =
      (HierarchyTask.residual (k := HP.k) 0).rank := by
  simp only [HierarchyTask.rank, Nat.mul_zero, Nat.zero_add]
  omega

/-- The final correction has exactly 32 rank slots below the residual, independent
of the number of iterations. A growing domination constant cannot be charged to
an invented growing gap on this edge. -/
theorem residual_correction_rank_gap :
    (HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k)).rank + 32 =
      (HierarchyTask.residual (k := HP.k) 0).rank := by
  rw [HierarchyTask.correctionAtomTask_last HP.k_pos]
  simp only [HierarchyTask.rank, CorrectionRowTask.rank,
    Nat.mul_zero, Nat.zero_add]
  have hk := HP.k_pos
  omega

/-- Exact remaining negative-child precision coefficient on every grid source and
terminal exponent. The usage mask does not enter precision; it remains part of IH. -/
theorem requestPrecision_residual_negative (B : BudgetData HP P) (M m ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hr : r.task = .residual 0) :
    let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
      ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩
    (2 : ℝ) ^ (-B.requestPrecision m q) =
      (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (((M : ℝ) - m) / (16 * B.slack) - 32 * B.rankCharge) := by
  dsimp only
  let q : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
      { r.terminal with rate := (midpoint r).rate },
      { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩
  have hq := B.requestPrecision_grid m ks ka q hs (by simpa only [q, midpoint] using ht)
  rw [B.requestPrecision_grid M ks ka r hs ht, hq,
    ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  congr 1
  have hg := residual_correction_rank_gap (HP := HP)
  have hc : ((HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k)).rank : ℝ) + 32 =
      r.task.rank := by rw [hr]; exact_mod_cast hg
  rw [sub_div]
  dsimp only [q]
  rw [← hc]
  ring

/-- At the coarse zero bin the actual left request keeps both rates. Its literal
budget loss therefore leaves a growing `ka/4` exponent, rather than direct-child
scale decay. This is the exact scalar coefficient still to be paid in the broader
product comparison; it is not an actual-error impossibility statement. -/
theorem requestPrecision_residual_coarse_left (B : BudgetData HP P) (M ks ka : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hr : r.task = .residual 0) (hrate : B.binRate = rate)
    (hM : B.slack * (1 + 4 * ka) ≤ M) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source (midpoint r)
      r.terminal (B.binRate 0)).left
    (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M 0 r) q) =
      (2 : ℝ) ^ (-B.requestPrecision M r) *
        (2 : ℝ) ^ (1 / 16 + (ka : ℝ) / 4 - 32 * B.rankCharge) := by
  dsimp only
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source (midpoint r)
    r.terminal (B.binRate 0)).left
  have hscale : ⌊Real.logb 2 (B.binRate 0 / r.terminal.rate)⌋ = 4 * (ka : ℤ) := by
    change B.sampleScale r (some 0) = _
    rw [B.sampleScale_grid r ka 0 hrate ht]
    ring
  have hcost : LogSpaceEstimation.scaleCutoff B.slack
      ⌊Real.logb 2 (B.binRate 0 / r.terminal.rate)⌋ = B.slack * (1 + 4 * ka) := by
    rw [hscale, LogSpaceEstimation.scaleCutoff, Int.natAbs_mul]
    norm_num
  have hcost1 : 1 ≤ B.slack * (1 + 4 * ka) := by
    have hslack := B.slack_pos
    nlinarith
  have hbudget : B.binBudget M 0 r = M - B.slack * (1 + 4 * ka) := by
    rw [binBudget, LogSpaceEstimation.lastBudget, hcost, max_eq_right hcost1]
  have hloss : ((M : ℝ) - B.binBudget M 0 r) / (16 * B.slack) =
      1 / 16 + (ka : ℝ) / 4 := by
    rw [hbudget, Nat.cast_sub hM, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_mul, Nat.cast_ofNat]
    have hp : (B.slack : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt B.slack_pos)
    field_simp
    ring
  have hq := B.requestPrecision_residual_left M (B.binBudget M 0 r) ks ka 0 r hs ht
  have hg := residual_correction_rank_gap (HP := HP)
  have hc : (q.task.rank : ℝ) + 32 = r.task.rank := by
    rw [hr]
    exact_mod_cast hg
  have he : -B.requestPrecision (B.binBudget M 0 r) q = -B.requestPrecision M r +
      (1 / 16 + (ka : ℝ) / 4 - 32 * B.rankCharge) := by
    change B.requestPrecision (B.binBudget M 0 r) q - B.requestPrecision M r = _ at hq
    rw [show ((B.binBudget M 0 r : ℕ) : ℝ) - M =
      -((M : ℝ) - B.binBudget M 0 r) by ring, neg_div, hloss] at hq
    rw [← hc] at hq
    linarith
  rw [show -B.requestPrecision (B.binBudget M 0 r) _ = _ from he,
    Real.rpow_add (by norm_num : (0 : ℝ) < 2)]

private theorem payment_root_le {c e t : ℝ} (hc : 0 ≤ c) (he : 0 ≤ e)
    (h : e ≤ t) : (c * e ^ 4) ^ (4⁻¹ : ℝ) ≤ c ^ (4⁻¹ : ℝ) * t := by
  rw [Real.mul_rpow hc (pow_nonneg he 4)]
  have hr : (e ^ 4) ^ (4⁻¹ : ℝ) = e := by
    convert Real.pow_rpow_inv_natCast he (by decide : (4 : ℕ) ≠ 0) using 1
  rw [hr]
  exact mul_le_mul_of_nonneg_left h (Real.rpow_nonneg hc _)

variable [Fact P.Prime] (B : BudgetData HP P)

/-- A fixed primitive charge pays the actual signed clipped consumer on the full-rate,
one-bin family, uniformly in the prime, suffixes, depths and budget. Availability
and scalar IH on each own source/usage mask are supplied, not recursively constructed.
The coarse/fine minimum is retained by the underlying consumer; only its full-rate
boundary is paid here. The charge condition depends solely on fixed primitive data. -/
theorem finiteInput_residual_clipped_fullRate_le
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
        (child i q) (B.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q)) ^ 4)
    (hIL : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).left
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q)) ^ 4)
    (hIR : ∀ i ∈ B.bins, let q :=
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual
        r.source (midpoint r) r.terminal (B.binRate i)).right
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child i q) (B.residualCanonicalChild i q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M i r) q)) ^ 4)
    (hIN : let q := (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
        { r.terminal with rate := (midpoint r).rate },
        { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      rootDistPow 4 P q.source.rate
        (fun σ x => q.source.retains (channels B.padding) σ x)
        (fun σ y => q.usage.retains (channels B.padding) σ y)
        (child 0 q) (B.residualCanonicalChild 0 q) ≤
        ((2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) q)) ^ 4)
    (hn : n = 0) (hks0 : ks = 0) (hka0 : ka = 0)
    (htask : r.task = .residual 0) (hcharge : 0 ≤ B.rankCharge)
    (hfixed : fullRateRootCost HP B.binCap ≤ (2 : ℝ) ^ (B.rankCharge - 1)) :
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
        ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  subst n ks ka
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 0 .residual
    r.source (midpoint r) r.terminal (B.binRate 0)
  let neg : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
      { r.terminal with rate := (midpoint r).rate },
      { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩
  let e := (2 : ℝ) ^ (-B.requestPrecision M r)
  let t := (2 : ℝ) ^ (1 - B.rankCharge) * e
  let F := 512 * (3 * max 1 (((HP.k : ℝ) + 1) / HP.θ) + 3) ^ 3
  let L := (2 * B.binCap) * HP.K
  let R := (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊
  have hF : 0 ≤ F := by dsimp only [F]; positivity
  have hcap := B.binCap_nonneg
  have hQcap := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hK0 : 0 ≤ HP.K := by
    have heta := HP.η_pos
    have : 0 ≤ 2 * (1 + 32 / HP.η) := by positivity
    linarith
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  have he : 0 ≤ e := by positivity
  have ht0 : 0 ≤ t := by positivity
  have hb : B.bins = {0} := by simpa only [Nat.zero_add, range_one] using hbins
  have hi : B.binRate 0 = rate 0 := congrFun hrate 0
  have hm : B.binBudget M 0 r = B.childBudget M := by
    simp only [binBudget, hi, ht, div_self (rate_pos 0).ne', Real.logb_one,
      Int.floor_zero, childBudget]
  have hQ (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
      (hq : q ∈ ({Q.direct, Q.left, Q.right} : Finset _)) :
      (2 : ℝ) ^ (-B.requestPrecision (B.binBudget M 0 r) q) ≤ t := by
    have hrank : q.task.rank < r.task.rank := by
      rw [htask]
      apply HierarchyTask.rawRequests_rank_lt 0 0 .residual
        r.source (midpoint r) r.terminal (B.binRate 0) q
      simp only [HierarchyTask.RawRequests.calls, List.mem_append,
        List.mem_cons, List.not_mem_nil, or_false]
      exact Or.inl (by simpa only [mem_insert, mem_singleton] using hq)
    rw [hm]
    apply B.fullRate_child_salary M r q hs ht _ _ hrank hcharge
    all_goals
      simp only [mem_insert, mem_singleton] at hq
      rcases hq with rfl | rfl | rfl <;>
        simpa only [Q, HierarchyTask.rawRequests, midpoint] using (by
          first | exact hs | exact ht | exact hi)
  have hN : (2 : ℝ) ^ (-B.requestPrecision (B.childBudget M) neg) ≤ t := by
    apply B.fullRate_child_salary M r neg hs ht hs _ _ hcharge
    · simpa only [neg, midpoint] using ht
    · rw [htask]
      exact HierarchyTask.correctionAtomTask_rank_lt 0 (.residual : HierarchyTask.RawTask HP.k)
  have hdirectSalary := hQ Q.direct (by simp)
  have hleftPay := hQ Q.left (by simp)
  have hrightPay := hQ Q.right (by simp)
  have hprod : F * 33554432 *
      (L * ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M 0 r) Q.left)) ^ 4 +
       R * ((2 : ℝ) ^ (-B.requestPrecision (B.binBudget M 0 r) Q.right)) ^ 4) ≤
      (F * 33554432 * (L + R)) * t ^ 4 := by
    have hl := pow_le_pow_left₀ (by positivity) hleftPay 4
    have hr := pow_le_pow_left₀ (by positivity) hrightPay 4
    nlinarith [mul_le_mul_of_nonneg_left hl hL, mul_le_mul_of_nonneg_left hr hR,
      mul_nonneg hF (by norm_num : (0 : ℝ) ≤ 33554432)]
  have hprodRoot := Real.rpow_le_rpow (by positivity) hprod
    (by norm_num : (0 : ℝ) ≤ 4⁻¹)
  have hprodBound := hprodRoot.trans (payment_root_le
    (by positivity : 0 ≤ F * 33554432 * (L + R)) ht0 le_rfl)
  have hdirectBound := payment_root_le hF (by positivity) hdirectSalary
  have hnegativeBound := payment_root_le hF (by positivity) hN
  obtain ⟨executed, hex, hmean⟩ := B.finiteInput_residual_clipped_scalar_le
    0 hbins hrate hcutoff haux hD H hnH M 0 0 r hst hs ht hks hka
    hC hC1 hCf hcover hkh hlight hK history child depth ζ floor
    (fun m q => (2 : ℝ) ^ (-B.requestPrecision m q))
    hrows hnrow hdirect hleft hright hnegative hID hIL hIR hIN
  refine ⟨executed, hex, hmean.trans ?_⟩
  have hg : gridMass P 0 = 1 := by
    simp [gridMass, side]
  have hz : rate 0 = 1 := by norm_num [rate]
  simp only [Q, neg, F, L, R, midpoint, hb, sum_singleton, hi, hs, ht, hg,
    max_self, min_self, div_one, mul_one, one_mul, hz, one_pow, one_div, inv_one, mul_assoc]
      at hnegativeBound hdirectBound hprodBound ⊢
  apply pow_le_pow_left₀ (by positivity)
  have htotal : fullRateRootCost HP B.binCap * t ≤ e := by
    have hh := mul_le_mul_of_nonneg_right hfixed ht0
    have hexp : (2 : ℝ) ^ (B.rankCharge - 1) * (2 : ℝ) ^ (1 - B.rankCharge) = 1 := by
      rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
      ring_nf
      exact Real.rpow_zero 2
    simpa only [t, ← mul_assoc, hexp, one_mul] using hh
  calc
    _ ≤ F ^ (4⁻¹ : ℝ) * t + F ^ (4⁻¹ : ℝ) * t +
        (F * 33554432 * (L + R)) ^ (4⁻¹ : ℝ) * t := by
      simp only [F, L, R, mul_assoc]
      apply add_le_add (add_le_add hnegativeBound hdirectBound)
      apply le_trans ?_ hprodBound
      apply Real.rpow_le_rpow _ (min_le_left _ _) (by norm_num)
      positivity
    _ = fullRateRootCost HP B.binCap * t := by
      dsimp only [fullRateRootCost, F, L, R]
      ring
    _ ≤ e := htotal

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
