/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyProductMean
public import Complexity.Foundations.Probability.HierarchyInitialFeasibility
public import Complexity.Foundations.Probability.ConditionalProductMean

/-!
# Actual product allocation domains and a conservative-payment obstruction

Successful correction compression already supplies an incoming cap on the inherited source.
The precision identities below retain the reset-right source and the actual positive and
negative budgets. They do not infer independence from a reset, or canonical support for an
approximate child.

The width payment in `finiteInput_residual_mean_payment` cannot in general be supplied by
nominal own-request IH allowances with a fixed rank charge: even at the full-rate bin zero,
its sufficient allowance costs at least `8 * P^2`, whereas the precision salary between the
parent and its direct child is bounded independently of the field. The quantitative finite
obstruction concerns that conservative sufficient condition, not the actual estimator error.
A sharper importance-weighted joint-mask mean bound and its schedule allocation remain
unproved here. The unscaled literal product-mean comparison below already avoids width loss.

## Main results

* `requestPrecision_residual_right`, `requestPrecision_residual_left`,
  `requestPrecision_residual_direct`: exact own-request precision differences.
* `evaluate_normalized_col_support`: incoming cap from successful compression.
* `residualProduct_compressed_mean_root_le`: literal product means without a width loss.
* `residual_mean_coarse_allowance_lt_nominal`: finite obstruction to the old reserve.
-/

public section
noncomputable section
open Finset Cslib Cslib.Probability
open scoped BigOperators
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
set_option backward.isDefEq.respectTransparency false
variable {P : ℕ} {HP : FourthRootHierarchyParams 16 1 16 32 8} (B : BudgetData HP P)

/-- Product-right precision uses the midpoint as its complete source. In particular the
source exponent in this formula is `ka`, not the inherited exponent `ks`. -/
theorem requestPrecision_residual_right (M m ks ka i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).right
    B.requestPrecision m q - B.requestPrecision M r =
      ((m : ℝ) - M) / (16 * B.slack) + 2 * ((ks : ℝ) - i) +
        B.rankCharge * ((r.task.rank : ℝ) - q.task.rank) := by
  dsimp only
  rw [B.requestPrecision_grid M ks ka r hs ht,
    B.requestPrecision_grid m ka i _ (by simp only [HierarchyTask.rawRequests, midpoint, ht])
      (by simp only [HierarchyTask.rawRequests, hi])]
  ring

/-- The left correction keeps its own midpoint rank rate at every bin budget; it does
not acquire the bin terminal rate. Its budget still changes with the bin. -/
theorem requestPrecision_residual_left (M m ks ka i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).left
    B.requestPrecision m q - B.requestPrecision M r =
      ((m : ℝ) - M) / (16 * B.slack) +
        B.rankCharge * ((r.task.rank : ℝ) - q.task.rank) := by
  dsimp only
  rw [B.requestPrecision_grid M ks ka r hs ht,
    B.requestPrecision_grid m ks ka _ (by exact hs)
      (by simp only [HierarchyTask.rawRequests, midpoint, ht])]
  ring

/-- The direct request changes its terminal rank rate to the bin rate and retains the
original source. This is an identity at the actual bin budget as well as at any other budget. -/
theorem requestPrecision_residual_direct (M m ks ka i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate ks) (ht : r.terminal.rate = rate ka)
    (hi : B.binRate i = rate i) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
      r.terminal (B.binRate i)).direct
    B.requestPrecision m q - B.requestPrecision M r =
      ((m : ℝ) - M) / (16 * B.slack) + 2 * ((ka : ℝ) - i) +
        B.rankCharge * ((r.task.rank : ℝ) - q.task.rank) := by
  dsimp only
  rw [B.requestPrecision_grid M ks ka r hs ht,
    B.requestPrecision_grid m ks i _ (by exact hs)
      (by simp only [HierarchyTask.rawRequests, hi])]
  ring

/-- A full-rate direct child's nominal IH can receive only a field-independent rank
salary. Increasing the parent budget does not increase this ratio. -/
theorem residual_full_nominal_salary (M m : ℕ) (hm : m ≤ M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : r.source.rate = rate 0) (ht : r.terminal.rate = rate 0)
    (hi : B.binRate 0 = rate 0) (hcharge : 0 ≤ B.rankCharge) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source (midpoint r)
      r.terminal (B.binRate 0)).direct
    ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 ≤
      (2 : ℝ) ^ (4 * B.rankCharge * r.task.rank) *
        ((2 : ℝ) ^ (-B.requestPrecision m q)) ^ 4 := by
  dsimp only
  have hd := B.requestPrecision_residual_direct M m 0 0 0 r hs ht hi
  dsimp only at hd
  have hmr : (m : ℝ) ≤ M := by exact_mod_cast hm
  have hbudget : ((m : ℝ) - M) / (16 * B.slack) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr hmr) (by positivity)
  have hrank : 0 ≤ B.rankCharge *
      (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source (midpoint r)
        r.terminal (B.binRate 0)).direct.task.rank := mul_nonneg hcharge (Nat.cast_nonneg _)
  have hp (v : ℝ) : ((2 : ℝ) ^ v) ^ 4 = (2 : ℝ) ^ (4 * v) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
    congr 1
    ring
  rw [hp, hp, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
  apply Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2)
  norm_num only [Nat.cast_zero, sub_self, mul_zero, add_zero] at hd
  linarith

variable [Fact P.Prime]

/-- The incoming cap follows from actual successful normalization, without accuracy or
canonical-support assumptions. The source predicate is the literal inherited request,
including its suffix; no old parent endpoint is frozen in the resulting table. -/
theorem normalized_col_support
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : Admissible r) (pilot : Bool) (i : Fin HP.k)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.normalized history M r pilot i = some A) (σ : Environment P 3) (z : ZMod P) :
    #{x ∈ ({x | r.source.retains (channels B.padding) σ x} : Finset _) |
      A σ x z ≠ 0} < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
  unfold normalized at hA
  cases hraw : row history (B.childBudget M)
      {r with task := .row 0 (if pilot then .pilotInput i else .input i)} with
  | none => simp [hraw] at hA
  | some raw =>
    cases hprep : row history (B.childBudget M)
        {r with task := .row 0 (if pilot then .pilotPreparation i else .preparation i)} with
    | none => simp [hraw, hprep] at hA
    | some prep =>
      cases hmax : vector history (B.childBudget M)
          {r with task := .row 0 (.maximum (if pilot then i.succ else Fin.last HP.k))} with
      | none => simp [hraw, hprep, hmax] at hA
      | some maximum =>
        simp only [hraw, hprep, hmax] at hA
        have heq : correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ)
            HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
            ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum = A := Option.some.inj hA
        subst A
        have hpos : 0 < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
          apply Nat.ceil_pos.mpr
          have hj : (0 : ℝ) < HP.J := by exact_mod_cast HP.J_pos
          have hR := HP.R_rank
          norm_num only [one_mul] at hR
          linarith
        have hc := selectedRequest_col_support HP B.padding id r hr _ hpos
          raw prep maximum σ z
        simp only [Equiv.piSplitAt_apply, coordinate,
          CorrectionRowTask.Channel.retains, channels, id_eq] at hc ⊢
        exact hc

/-- Successful evaluated normalized children inherit the structural incoming cap.
This is a safety law, not a recursive availability or accuracy theorem. -/
theorem evaluate_normalized_col_support (M : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (ha : Admissible r)
    (hr : r.task = .row 0 (if pilot then .pilotNormalized i else .normalized i))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.evaluate M r = some (.row A)) (σ : Environment P 3) (z : ZMod P) :
    #{x ∈ ({x | r.source.retains (channels B.padding) σ x} : Finset _) |
      A σ x z ≠ 0} < ⌈4 * (1 + 32 * HP.R)⌉₊ := by
  rcases r with ⟨task, source, terminal, usage⟩
  dsimp only at hr
  subst task
  cases pilot
  all_goals
    rw [evaluate_eq] at hA
    simp only [step, Bool.false_eq_true, ↓reduceIte] at hA
    split_ifs at hA with hactive
    · obtain ⟨value, hn, hv⟩ := Option.map_eq_some_iff.mp hA
      cases BudgetValue.row.inj hv
      exact B.normalized_col_support _ M _ ha _ i _ hn σ z

private lemma min_frame_subset (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (A : FrameChannel P 4 1) (v : ZMod P) :
    frameRetains P 4 (semanticSide P (min a b)) A v →
      frameRetains P 4 (semanticSide P b) A v := by
  have hside : semanticSide P (min a b) ≤ semanticSide P b := by
    apply Nat.ceil_mono
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (le_min ha hb) (min_le_right _ _) (by norm_num)) (Nat.cast_nonneg P)
  simp only [frameRetains, mem_retentionBox]
  exact fun h j => (h j).trans_le hside

/-- The actual canonical dense-right gate bounds its complete row support. This is
proved from the numerator support and rank gate, not assumed of approximate rows. -/
theorem residualCanonicalRight_row_support
    (i : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (ht : 0 ≤ r.terminal.rate) (hi : 0 ≤ B.binRate i)
    (hlight : ∀ d, d ≤ HP.θ → B.cutoff i d = 0)
    (σ : Environment P 3) (z : ZMod P) :
    #{y : ZMod P | B.residualCanonicalChild i
      (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
        r.terminal (B.binRate i)).right σ z y ≠ 0} ≤ HP.K := by
  let q := (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)).right
  change #{y : ZMod P | normalizedRequest B.padding id q (B.cutoff i) HP.ρ HP.K
    (fun _ => B.base) (densePreparation B.padding id q (B.auxiliary i) HP.ρ HP.K B.base)
      σ z y ≠ 0} ≤ HP.K
  unfold normalizedRequest
  split_ifs with hq
  · apply Nat.le_of_lt
    apply DenseRowRecipe.card_filter_normalized_ne_zero_lt
      (hK := FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
      (he := HP.θ_pos.le) (hk := hlight)
      (hg := show HP.η₂ ≤ HP.θ by
        linarith [HP.η₂_lt, HP.δ₀_lt_δ₁, HP.δ₁_lt, HP.θ_pos]) (hρ := HP.ρ_zero)
    intro A y hy
    exact min_frame_subset r.terminal.rate (B.binRate i) ht hi A _ hy
  · simp

/-- The literal product of a successful normalized correction and compressed reset-right
child admits a width-free coupled root comparison on the unchanged environment. The true
right row cap comes from its actual gate; the estimated left incoming cap comes from its
successful constructor. No approximate canonical support or independence is assumed.

The conditional mean here is of the literal unfiltered product itself. Usage guards
prove its equality with the intermediate-mask sum used by the coupled product theorem.
Bin importance/density multiplication,
finite signed assembly and schedule allocation remain separate. Both calls execute at the
actual `binBudget M i r`, with their literal source and usage tuples. -/
theorem residualProduct_compressed_mean_root_le
    (M i k : ℕ) (ζ floor : ℝ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hs : 0 < r.source.rate) (ht : 0 < r.terminal.rate) (hi : 0 ≤ B.binRate i)
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
    let prod := fun A D σ x y => ∑ z : ZMod P, A σ x z * D σ z y
    rootDistPow 4 P r.source.rate Xs Yu
      (fun _ x y => conditionalTableMean Xs Yu (prod L R) x y)
      (fun _ x y => conditionalTableMean Xs Yu (prod (C Q.left) (C Q.right)) x y) ≤
      33554432 * ((2 * B.binCap) * HP.K *
        rootDistPow 4 P r.source.rate Xs Zs L (C Q.left) +
        (2 * HP.Q HP.toHierarchyParams.atomCap) * ⌈4 * (1 + 32 * HP.R)⌉₊ *
          (r.terminal.rate / r.source.rate) *
            rootDistPow 4 P r.terminal.rate Zs Yu R (C Q.right)) := by
  dsimp only
  let Q := HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source (midpoint r)
    r.terminal (B.binRate i)
  let C := B.residualCanonicalChild i
  let Xs := fun σ x => r.source.retains (channels B.padding) σ x
  let Zs := fun σ z => (midpoint r).retains (channels B.padding) σ z
  let Yu := fun σ y => Q.right.usage.retains (channels B.padding) σ y
  have hleft := B.evaluate_normalized_bounds (B.binBudget M i r) false
    ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left
    (by simp only [Q, HierarchyTask.rawRequests,
      HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte]) L hL
  have hright := B.compressedBin_range_usage (B.binBudget M i r) i k ζ floor Q.right R hR
  have heL : (fun σ x y => ∑ z : ZMod P, L σ x z * R σ z y) =
      (fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), L σ x z * R σ z y) := by
    funext σ x y
    rw [sum_filter]
    apply sum_congr rfl
    intro z _
    split_ifs with hz
    · rfl
    · rw [(hleft.2.1 σ x z hz), zero_mul]
  have heC : (fun σ x y => ∑ z : ZMod P, C Q.left σ x z * C Q.right σ z y) =
      (fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), C Q.left σ x z * C Q.right σ z y) := by
    funext σ x y
    rw [sum_filter]
    apply sum_congr rfl
    intro z _
    split_ifs with hz
    · rfl
    · have hc := canonicalRequestChild_zero_off_usage HP B.padding id B.base (B.cutoff i)
        (B.auxiliary i) HP.ρ HP.K Q.left σ x z hz
      change C Q.left σ x z = 0 at hc
      rw [hc, zero_mul]
  have htrue (q : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (σ : Environment P 3)
      (x y : ZMod P) := canonicalRequestChild_mem_Icc HP B.padding id B.base (B.cutoff i)
        (B.auxiliary i) HP.ρ HP.K B.binCap_nonneg (B.cutoff_bounds i)
        (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) q σ x y
  have hdense (σ : Environment P 3) (z y : ZMod P) :
      C Q.right σ z y ∈ Set.Icc 0 (2 * B.binCap) :=
    normalizedRequest_mem_Icc HP B.padding Q.right (B.cutoff i) B.binCap_nonneg
      (B.cutoff_bounds i) (fun _ => B.base)
      (densePreparation B.padding id Q.right (B.auxiliary i) HP.ρ HP.K B.base) σ z y
  have ha : Admissible Q.left := by
    refine ⟨?_, rfl, rfl⟩
    exact (midpointRole_distinct r.source.role r.terminal.role).1
  have hcol (σ : Environment P 3) (z : ZMod P) (_hz : Zs σ z) :
      #{x ∈ ({x | Xs σ x} : Finset _) | L σ x z ≠ 0} ≤ ⌈4 * (1 + 32 * HP.R)⌉₊ := by
    exact (B.evaluate_normalized_col_support (B.binBudget M i r) false
      ⟨HP.k - 1, Nat.sub_lt HP.k_pos (by decide)⟩ Q.left ha
      (by simp only [Q, HierarchyTask.rawRequests,
        HierarchyTask.correctionAtomTask_last HP.k_pos, Bool.false_eq_true, ↓reduceIte])
      L hL σ z).le
  have hrow (σ : Environment P 3) (z : ZMod P) (_hz : Zs σ z) :
      #{y ∈ ({y | Yu σ y} : Finset _) | C Q.right σ z y ≠ 0} ≤ HP.K :=
    le_trans (card_le_card (fun _ hy => mem_filter.mpr
      ⟨mem_univ _, (mem_filter.mp hy).2⟩))
      (B.residualCanonicalRight_row_support i r ht.le hi hlight σ z)
  have hp := rootDistPow_mul_le (s := 4) (N := (P : ℝ)) (u := r.source.rate)
    (f := r.terminal.rate) (X := Xs) (Z := Zs) (Y := Yu)
    (F := C Q.left) (F' := L) (B := C Q.right) (B' := R)
    (CF := 2 * HP.Q HP.toHierarchyParams.atomCap) (CB := 2 * B.binCap)
    (by decide) (by exact_mod_cast (Fact.out : P.Prime).pos) hs ht
    (fun σ x z => (htrue Q.left σ x z).1) (fun σ x z => (hleft.1 σ x z).1)
    (fun σ z y => (hdense σ z y).1) (fun σ z y => (hright.1 σ z y).1)
    (mul_nonneg (by norm_num) (HP.Q_nonneg _)) (mul_nonneg (by norm_num) B.binCap_nonneg)
    (fun σ x z => (hleft.1 σ x z).2) (fun σ z y => (hdense σ z y).2) hrow hcol
  rw [rootDistPow_comm] at hp
  have hm := rootDistPow_conditionalTableMean_mul_le (s := 4) (N := (P : ℝ))
    (u := r.source.rate) (X := Xs) (Y := Yu) (c := 1)
    (H := fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), L σ x z * R σ z y)
    (H' := fun σ x y => ∑ z ∈ ({z | Zs σ z} : Finset _), C Q.left σ x z * C Q.right σ z y)
    (by decide) (by exact_mod_cast (Fact.out : P.Prime).pos) hs (by norm_num)
    (fun σ x y => sum_nonneg fun z _ => mul_nonneg (hleft.1 σ x z).1 (hright.1 σ z y).1)
    (fun σ x y => sum_nonneg fun z _ => mul_nonneg (htrue Q.left σ x z).1 (hdense σ z y).1)
  simp only [one_mul] at hm
  rw [heL, heC]
  apply hm.trans
  have hp' := mul_le_mul_of_nonneg_left hp (by norm_num : (0 : ℝ) ≤ 2048)
  rw [rootDistPow_comm (C Q.left) L, rootDistPow_comm (C Q.right) R] at hp'
  norm_num only [Nat.reduceSub, Nat.reduceMul, Nat.reducePow, Nat.cast_ofNat] at hp' ⊢
  convert hp' using 1
  ring

private lemma full_grid (D : ZMod P) (s : Fin 3) (ss : List (ZMod P))
    (σ : Environment P 3) (x : ZMod P) :
    (gridChannel s 0 ss).retains (channels D) σ x := by
  simp only [gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid]
  simpa only [show side P 0 = P by simp [side]] using full_retains (σ s) _

/-- The single negative request alone forces a field-width payment in the conservative
coefficient. This holds independently of every positive bin, range cap and base matrix. -/
theorem residualCostCoefficient_full_lower
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (t : Fin 3) (st : List (ZMod P))
    (ht : r.terminal = gridChannel t 0 st)
    (CA CB : ℝ) :
    8 * (P : ℝ) ≤ HierarchyTask.residualCostCoefficient (k := HP.k) (V := ZMod P)
      (channels B.padding) B.bins 0 r.source (midpoint r) r.terminal B.binRate CA CB := by
  have hm : (midpoint r).rate = 1 := by simp [midpoint, ht, gridChannel, rate]
  have hf (σ : Environment P 3) (y : ZMod P) :
      r.terminal.retains (channels B.padding) σ y := by rw [ht]; exact full_grid ..
  have hratio (y : ZMod P) :
      HierarchyTask.usageRatio (channels B.padding) r.terminal
        (⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
          {r.terminal with rate := (midpoint r).rate},
          {r.terminal with rate := min r.terminal.rate (midpoint r).rate}⟩ :
          HierarchyTask.Request HP.k (Fin 3) (ZMod P)) y = 1 := by
    have he : min r.terminal.rate (midpoint r).rate = r.terminal.rate := by
      simp [ht, hm, gridChannel, rate]
    simp only [HierarchyTask.usageRatio, he]
    have hu : {r.terminal with rate := r.terminal.rate} = r.terminal := by cases r.terminal; rfl
    rw [hu]
    simp [hf]
  unfold HierarchyTask.residualCostCoefficient
  simp only [hm] at hratio
  simp only [hm, hratio, mul_one, abs_one, one_pow, sum_const, card_univ, nsmul_eq_mul,
    ZMod.card]
  have hn : 0 ≤ (#B.bins : ℝ) ^ 4 * ∑ i ∈ B.bins,
      8 * ((∑ y : ZMod P, |B.binRate i * HierarchyTask.usageRatio (channels B.padding)
          r.terminal (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source
            (midpoint r) r.terminal (B.binRate i)).direct y| ^ 4) +
        8 * (Fintype.card (ZMod P) : ℝ) ^ 4 * (CA ^ 4 + CB ^ 4) *
          ∑ y : ZMod P, |B.binRate i * HierarchyTask.usageRatio (channels B.padding)
            r.terminal (HierarchyTask.rawRequests (k := HP.k) 0 i .residual r.source
              (midpoint r) r.terminal (B.binRate i)).right y *
            (1 / (dens {σ | (midpoint r).retains (channels B.padding) σ y} : ℝ))| ^ 4) := by
    positivity
  simp only [ZMod.card] at hn
  linarith

/-- A finite obstruction to paying the existing conservative sufficient mean allowance
from nominal child IH alone. The obstruction is already present in the bin-zero direct
call, at any smaller budget. The charge is fixed first; fields satisfying the displayed
threshold defeat this sufficient allowance. This is not a lower bound on actual mean error. -/
theorem residual_mean_coarse_allowance_lt_nominal
    (M m : ℕ) (hm : m ≤ M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (ss st : List (ZMod P))
    (hs : r.source = gridChannel s 0 ss) (ht : r.terminal = gridChannel t 0 st)
    (hi : B.binRate 0 = rate 0) (hcharge : 0 ≤ B.rankCharge)
    (CA CB : ℝ)
    (hwidth : (2 : ℝ) ^ (4 * B.rankCharge * r.task.rank) < 8 * (P : ℝ) ^ 2) :
    let q := (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source (midpoint r)
      r.terminal (B.binRate 0)).direct
    let scale := (P : ℝ) ^ 2 / (P * r.source.rate) *
      HierarchyTask.residualCostCoefficient (k := HP.k) (V := ZMod P) (channels B.padding)
        B.bins 0 r.source (midpoint r) r.terminal B.binRate CA CB
    ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 / (1 + scale) <
      ((2 : ℝ) ^ (-B.requestPrecision m q)) ^ 4 := by
  dsimp only
  have hp : (0 : ℝ) < P := by exact_mod_cast (Fact.out : P.Prime).pos
  have hc := B.residualCostCoefficient_full_lower r t st ht CA CB
  have hscale : 8 * (P : ℝ) ^ 2 ≤ (P : ℝ) ^ 2 / (P * r.source.rate) *
      HierarchyTask.residualCostCoefficient (k := HP.k) (V := ZMod P) (channels B.padding)
        B.bins 0 r.source (midpoint r) r.terminal B.binRate CA CB := by
    have hr : r.source.rate = 1 := by simp [hs, gridChannel, rate]
    rw [hr, mul_one, pow_two, mul_div_cancel_right₀ _ hp.ne']
    nlinarith [mul_le_mul_of_nonneg_left hc hp.le]
  have hsrate : r.source.rate = rate 0 := by simp only [hs, gridChannel]
  have htrate : r.terminal.rate = rate 0 := by simp only [ht, gridChannel]
  have hsalary := B.residual_full_nominal_salary M m hm r hsrate htrate hi hcharge
  dsimp only at hsalary
  have hchild : 0 < ((2 : ℝ) ^ (-B.requestPrecision m
      (HierarchyTask.rawRequests (k := HP.k) 0 0 .residual r.source (midpoint r)
        r.terminal (B.binRate 0)).direct)) ^ 4 := by positivity
  apply (div_lt_iff₀ (by linarith [sq_nonneg (P : ℝ)])).mpr
  nlinarith [mul_lt_mul_of_pos_right (hwidth.trans_le hscale) hchild]

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
