/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/
module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.HierarchySignedMean
public import Complexity.Computability.LogSpaceDerandomization.ProductError
public import Complexity.Computability.LogSpaceDerandomization.HierarchyRawMoment
public import Complexity.Computability.LogSpaceDerandomization.RoutedBinAgreement

/-!
# Absolute errors of actual shared-environment request samples

Compare estimated requests with the genuine canonical requests on the same environment.
The product splits through estimated-left times canonical-right. Its two coefficients are
therefore the estimated correction range and the genuine dense range, respectively.
Importance and midpoint density factors remain literal, including for empty events.
Finite assembly sums positive errors and charges the special negative correction once.
These original finite absolute comparisons do not establish recursive relative budgets,
copy-stage routing, reserves, workspace bounds or RL=L.
-/

public section
open Finset Cslib
open scoped BigOperators
noncomputable section

namespace Matrix.HierarchyParams.HierarchyTask
open CorrectionRowTask
variable {k : ℕ} {Role Symbol V Ω : Type*} [Fintype V] [Fintype Ω]
  (channels : Role → ℝ → List Symbol → Ω → V → Prop)
  [∀ role rate suffix σ v, Decidable (channels role rate suffix σ v)]

/-- Absolute positive-bin payment from the actual direct, right and left request errors.
CA bounds estimated left; CB bounds canonical right. Only the union of the two actual
left supports is charged. This avoids requesting right-child errors off their reset source
domain when both left factors vanish. No child independence is required. -/
@[expose] def positiveChildError (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b CA CB : ℝ)
    (estimated canonical : Request k Role Symbol → Matrix V V ℝ) (x y : V) : ℝ :=
  let R := rawRequests l bin t source midpoint endpoint b
  |b * usageRatio channels endpoint R.direct y| *
      |estimated R.direct x y - canonical R.direct x y| +
    |b * usageRatio channels endpoint R.right y *
      (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))| *
      ∑ z ∈ univ.filter (fun z => estimated R.left x z ≠ 0 ∨ canonical R.left x z ≠ 0),
        (CA * |estimated R.right z y - canonical R.right z y| +
        |estimated R.left x z - canonical R.left x z| * CB)

/-- The special negative error is zero for tasks without a negative request. -/
@[expose] def negativeChildError (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ)
    (estimated canonical : Request k Role Symbol → Matrix V V ℝ) (x y : V) : ℝ :=
  match (rawRequests l bin t source midpoint endpoint b).negative with
  | none => 0
  | some r => |midpoint.rate * usageRatio channels endpoint r y| *
      |estimated r x y - canonical r x y|

/-- Exact coupled product perturbation followed by the two range payments. -/
theorem rawPositiveSample_sub_le (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b CA CB : ℝ)
    (estimated canonical : Request k Role Symbol → Matrix V V ℝ) (x y : V)
    (hleft : ∀ z, |estimated (rawRequests l bin t source midpoint endpoint b).left x z| ≤ CA)
    (hright : ∀ z, |canonical (rawRequests l bin t source midpoint endpoint b).right z y| ≤ CB) :
    |rawPositiveSample channels l bin t source midpoint endpoint b estimated x y -
      rawPositiveSample channels l bin t source midpoint endpoint b canonical x y| ≤
      positiveChildError channels l bin t source midpoint endpoint b CA CB
        estimated canonical x y := by
  let R := rawRequests l bin t source midpoint endpoint b
  let T := univ.filter (fun z => estimated R.left x z ≠ 0 ∨ canonical R.left x z ≠ 0)
  have he : (∑ z, estimated R.left x z * estimated R.right z y) =
      ∑ z ∈ T, estimated R.left x z * estimated R.right z y := by
    symm
    apply sum_subset (filter_subset _ _)
    intro z _ hz
    have hz0 : estimated R.left x z = 0 := by
      by_contra hn
      exact hz (mem_filter.mpr ⟨mem_univ _, Or.inl hn⟩)
    rw [hz0, zero_mul]
  have hc : (∑ z, canonical R.left x z * canonical R.right z y) =
      ∑ z ∈ T, canonical R.left x z * canonical R.right z y := by
    symm
    apply sum_subset (filter_subset _ _)
    intro z _ hz
    have hz0 : canonical R.left x z = 0 := by
      by_contra hn
      exact hz (mem_filter.mpr ⟨mem_univ _, Or.inr hn⟩)
    rw [hz0, zero_mul]
  have hs := abs_sum_mul_sub_mul_le T
    (estimated R.left x) (canonical R.left x)
    (fun z => estimated R.right z y) (fun z => canonical R.right z y)
    (fun z _ => hleft z) (fun z _ => hright z)
  rw [← he, ← hc] at hs
  unfold rawPositiveSample positiveChildError
  dsimp only
  rw [show b * usageRatio channels endpoint R.direct y * estimated R.direct x y +
      b * usageRatio channels endpoint R.right y *
        (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ)) *
        (∑ z, estimated R.left x z * estimated R.right z y) -
      (b * usageRatio channels endpoint R.direct y * canonical R.direct x y +
      b * usageRatio channels endpoint R.right y *
        (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ)) *
        (∑ z, canonical R.left x z * canonical R.right z y)) =
      b * usageRatio channels endpoint R.direct y *
        (estimated R.direct x y - canonical R.direct x y) +
      (b * usageRatio channels endpoint R.right y *
        (midpoint.rate / (dens {σ | midpoint.retains channels σ y} : ℝ))) *
        ((∑ z, estimated R.left x z * estimated R.right z y) -
          ∑ z, canonical R.left x z * canonical R.right z y) by ring]
  exact (abs_add_le _ _).trans (by
    simp only [abs_mul]
    exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hs (by positivity)))

omit [Fintype V] in
/-- Literal special-negative perturbation, including the zero/base case. -/
theorem rawNegativeSample_sub_abs (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b : ℝ)
    (estimated canonical : Request k Role Symbol → Matrix V V ℝ) (x y : V) :
    |rawNegativeSample channels l bin t source midpoint endpoint b estimated x y -
      rawNegativeSample channels l bin t source midpoint endpoint b canonical x y| =
      negativeChildError channels l bin t source midpoint endpoint b estimated canonical x y := by
  unfold rawNegativeSample negativeChildError
  cases (rawRequests l bin t source midpoint endpoint b).negative <;>
    simp only [sub_self, abs_zero, ← mul_sub, abs_mul]

/-- The actual signed call retains all four errors; a bin sum should instead use positive
calls and one negative payment. -/
theorem rawSample_sub_le (l bin : ℕ) (t : RawTask k)
    (source midpoint endpoint : Channel Role (List Symbol)) (b CA CB : ℝ)
    (estimated canonical : Request k Role Symbol → Matrix V V ℝ) (x y : V)
    (hleft : ∀ z, |estimated (rawRequests l bin t source midpoint endpoint b).left x z| ≤ CA)
    (hright : ∀ z, |canonical (rawRequests l bin t source midpoint endpoint b).right z y| ≤ CB) :
    |rawSample channels l bin t source midpoint endpoint b estimated x y -
      rawSample channels l bin t source midpoint endpoint b canonical x y| ≤
      positiveChildError channels l bin t source midpoint endpoint b CA CB estimated canonical x y +
      negativeChildError channels l bin t source midpoint endpoint b estimated canonical x y := by
  unfold rawSample
  rw [show ∀ a b c d : ℝ, (a-b)-(c-d) = (a-c)-(b-d) by intros; ring]
  exact (abs_sub _ _).trans (add_le_add
    (rawPositiveSample_sub_le channels l bin t source midpoint endpoint b CA CB
      estimated canonical x y hleft hright)
    (rawNegativeSample_sub_abs channels l bin t source midpoint endpoint b
      estimated canonical x y).le)

/-- Finite positive assembly and one negative error, integrated on any joint event.
Empty events are included; no factorization of the environment is used. -/
theorem residual_bins_sub_le (S : Finset Ω) (bins : Finset ℕ) (l : ℕ)
    (source midpoint endpoint : Channel Role (List Symbol)) (b CB : ℕ → ℝ) (CA : ℝ)
    (estimated canonical : ℕ → Ω → Request k Role Symbol → Matrix V V ℝ) (x y : V)
    (hleft : ∀ i ∈ bins, ∀ σ ∈ S, ∀ z,
      |estimated i σ (rawRequests l i .residual source midpoint endpoint (b i)).left x z| ≤ CA)
    (hright : ∀ i ∈ bins, ∀ σ ∈ S, ∀ z,
      |canonical i σ (rawRequests l i .residual source midpoint endpoint (b i)).right z y| ≤ CB i) :
    |(𝔼 σ ∈ S, ((∑ i ∈ bins, rawPositiveSample channels l i .residual
        source midpoint endpoint (b i) (estimated i σ) x y) -
      rawNegativeSample channels l 0 .residual source midpoint endpoint (b 0)
        (estimated 0 σ) x y)) -
      (𝔼 σ ∈ S, ((∑ i ∈ bins, rawPositiveSample channels l i .residual
        source midpoint endpoint (b i) (canonical i σ) x y) -
      rawNegativeSample channels l 0 .residual source midpoint endpoint (b 0)
        (canonical 0 σ) x y))| ≤
    𝔼 σ ∈ S, ((∑ i ∈ bins, positiveChildError channels l i .residual
      source midpoint endpoint (b i) CA (CB i) (estimated i σ) (canonical i σ) x y) +
      negativeChildError channels l 0 .residual source midpoint endpoint (b 0)
        (estimated 0 σ) (canonical 0 σ) x y) := by
  rw [← expect_sub_distrib]
  apply (abs_expect_le _ _).trans
  apply expect_le_expect
  intro σ hσ
  rw [show ∀ a b c d : ℝ, (a-b)-(c-d) = (a-c)-(b-d) by intros; ring]
  apply (abs_sub _ _).trans
  apply add_le_add
  · rw [← sum_sub_distrib]
    exact (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i hi =>
      rawPositiveSample_sub_le channels l i .residual source midpoint endpoint (b i)
        CA (CB i) (estimated i σ) (canonical i σ) x y
        (hleft i hi σ hσ) (hright i hi σ hσ))
  · exact (rawNegativeSample_sub_abs channels l 0 .residual source midpoint endpoint (b 0)
      (estimated 0 σ) (canonical 0 σ) x y).le

end Matrix.HierarchyParams.HierarchyTask

namespace Matrix.HierarchyParams.H4RankEnvironment
attribute [local instance] Classical.propDecidable
variable {P J : ℕ} [Fact P.Prime] {V : Type} [Fintype V]

/-- Actual incoming final correction range. Structural size is HP.k at every precision. -/
theorem incomingChildren_final_range
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (Kc : ℕ) (cutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request HP.k (Fin J) (ZMod P) →
      Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request HP.k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    (r : HierarchyTask.Request HP.k (Fin J) (ZMod P)) (l : ℕ)
    (htask : r.task = HierarchyTask.correctionAtomTask l false (Fin.last HP.k))
    (σ : Environment P J) (x y : V) :
    |incomingChildren HP D ident Kc cutoff raw prep maximum r σ x y| ≤
      2 * HP.Q HP.toHierarchyParams.atomCap := by
  simp only [incomingChildren, htask, HierarchyTask.correctionAtomTask_last HP.k_pos]
  have hb := selectedRequest_mem_Icc HP D ident r Kc (raw r) (prep r) (maximum r) σ x y
  exact (abs_of_nonneg hb.1).trans_le hb.2

/-- A normalized request is zero off its own usage channel. Source membership is not
claimed: arbitrary completed inputs may give nonzero values outside the source domain. -/
theorem normalizedRequest_zero_off_usage {q : ℕ}
    (D : ZMod P) (ident : V → ZMod P)
    (r : HierarchyTask.Request q (Fin J) (ZMod P)) (cutoff gate : ℝ → ℝ) (K : ℕ)
    (raw prep : Environment P J → Matrix V V ℝ) (σ : Environment P J) (x y : V)
    (hy : ¬ r.usage.retains (channels D) σ (ident y)) :
    normalizedRequest D ident r cutoff gate K raw prep σ x y = 0 := by
  unfold normalizedRequest
  split_ifs with hr
  · have ht : ¬ coordinate D r.usage (σ r.terminal.role) (ident y) := by
      simpa only [coordinate, CorrectionRowTask.Channel.retains, channels, hr.2.1] using hy
    simp only [DenseRowRecipe.normalized, Equiv.piSplitAt_apply, ht, ↓reduceIte]
  · rfl

/-- Every actual incoming child is zero off usage, including the literal correction base. -/
theorem incomingChildren_zero_off_usage {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (Kc : ℕ) (cutoff : ℝ → ℝ)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → V → ℝ)
    (r : HierarchyTask.Request q (Fin J) (ZMod P)) (σ : Environment P J) (x y : V)
    (hy : ¬ r.usage.retains (channels D) σ (ident y)) :
    incomingChildren HP D ident Kc cutoff raw prep maximum r σ x y = 0 := by
  cases ht : r.task with
  | row stage task =>
    cases task <;> simp only [incomingChildren, ht]
    all_goals first
    | rfl
    | exact correctionRequest_eq_zero_of_not_usage D ident r _ _ _ _ _ _ _ _ _ _ σ x y hy
    | exact normalizedRequest_zero_off_usage D ident r _ _ _ _ _ σ x y hy
  | _ =>
    simp only [incomingChildren, ht]
    exact normalizedRequest_zero_off_usage D ident r _ _ _ _ _ σ x y hy

/-- The genuine canonical family has the same usage guard. No statement about arbitrary
values outside a child's source domain is needed. -/
theorem canonicalRequestChild_zero_off_usage {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (C : Matrix V V ℝ) (cutoff h ρ : ℝ → ℝ) (K : ℕ)
    (r : HierarchyTask.Request q (Fin J) (ZMod P)) (σ : Environment P J) (x y : V)
    (hy : ¬ r.usage.retains (channels D) σ (ident y)) :
    canonicalRequestChild HP D ident C cutoff h ρ K r σ x y = 0 := by
  cases ht : r.task with
  | baseNormalized stage bin =>
    simp only [canonicalRequestChild, ht, denseChild]
    exact normalizedRequest_zero_off_usage D ident r _ _ _ _ _ σ x y hy
  | row stage task =>
    cases task <;> simp only [canonicalRequestChild, ht]
    all_goals first
    | rfl
    | (split_ifs with hr
       · exact correctionRequest_eq_zero_of_not_usage D ident r _ _ _ _ _ _ _ _ _ _ σ x y hy
       · rfl)
  | _ => simp [canonicalRequestChild, ht]

/-- Range of the actual incoming family, including both normalized dispatches. The
uniform cap is the larger of the correction range and the dense range. -/
theorem incomingChildren_mem_Icc {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (Kc : ℕ) (cutoff : ℝ → ℝ) {CB : ℝ} (hCB : 0 ≤ CB)
    (hcutoff : ∀ v, cutoff v ∈ Set.Icc 0 CB)
    (raw prep : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request q (Fin J) (ZMod P) → Environment P J → V → ℝ)
    (r : HierarchyTask.Request q (Fin J) (ZMod P)) (σ : Environment P J) (x y : V) :
    incomingChildren HP D ident Kc cutoff raw prep maximum r σ x y ∈
      Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) :=
    ⟨le_rfl, (by positivity : (0 : ℝ) ≤ 2 * CB).trans (le_max_right _ _)⟩
  have hc := selectedRequest_mem_Icc HP D ident r Kc (raw r) (prep r) (maximum r) σ x y
  have hcor : correctionRequest D ident r (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.ρ
      HP.toHierarchyParams.atomCutoff HP.γ HP.K Kc (raw r) (prep r) (maximum r) σ x y ∈
      Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) :=
    ⟨hc.1, hc.2.trans (le_max_left _ _)⟩
  have hd : normalizedRequest D ident r cutoff HP.ρ HP.K (raw r) (prep r) σ x y ∈
      Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) := by
    unfold normalizedRequest
    split_ifs
    · apply (show Set.Icc (0 : ℝ) (2 * CB) ⊆
          Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) from
          fun _ hv => ⟨hv.1, hv.2.trans (le_max_right _ _)⟩)
      exact DenseRowRecipe.normalized_mem_Icc _ _ _ _ _ _ _ hCB hcutoff
        (fun v => ⟨HP.ρ_nonneg v, HP.ρ_le_one v⟩) _ _ _ _ _
    · exact hzero
  cases ht : r.task with
  | row stage task =>
    cases task <;> simp only [incomingChildren, ht]
    all_goals first | exact hzero | exact hcor | exact hd
  | _ => simpa only [incomingChildren, ht] using hd

/-- The genuine family inherits the same two normalized ranges. This assumes a bound
on the scalar cutoff, never a bound on the raw target divided by its rate. -/
theorem canonicalRequestChild_mem_Icc {q : ℕ}
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (C : Matrix V V ℝ) (cutoff h ρ : ℝ → ℝ) (K : ℕ) {CB : ℝ} (hCB : 0 ≤ CB)
    (hcutoff : ∀ v, cutoff v ∈ Set.Icc 0 CB) (hρ : ∀ v, ρ v ∈ Set.Icc 0 1)
    (r : HierarchyTask.Request q (Fin J) (ZMod P)) (σ : Environment P J) (x y : V) :
    canonicalRequestChild HP D ident C cutoff h ρ K r σ x y ∈
      Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) := by
  have hzero : (0 : ℝ) ∈ Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) :=
    ⟨le_rfl, (by positivity : (0 : ℝ) ≤ 2 * CB).trans (le_max_right _ _)⟩
  cases ht : r.task with
  | baseNormalized stage bin =>
    simp only [canonicalRequestChild, ht, denseChild, normalizedRequest]
    split_ifs
    · apply (show Set.Icc (0 : ℝ) (2 * CB) ⊆
          Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) from
          fun _ hv => ⟨hv.1, hv.2.trans (le_max_right _ _)⟩)
      exact DenseRowRecipe.normalized_mem_Icc _ _ _ _ _ _ _ hCB hcutoff hρ _ _ _ _ _
    · exact hzero
  | row stage task =>
    cases task <;> simp only [canonicalRequestChild, ht]
    all_goals first
    | exact hzero
    | (split_ifs with hr
       · apply (show Set.Icc (0 : ℝ) (2 * HP.Q HP.toHierarchyParams.atomCap) ⊆
             Set.Icc 0 (max (2 * HP.Q HP.toHierarchyParams.atomCap) (2 * CB)) from
             fun _ hv => ⟨hv.1, hv.2.trans (le_max_left _ _)⟩)
         exact selectedRequest_mem_Icc HP D ident r _ _ _ _ σ x y
       · exact hzero)
  | _ => simpa [canonicalRequestChild, ht] using hzero

/-- Actual positive-bin left support is contained in the midpoint mask. Consequently the
right-child error is called only on its reset source, with the unchanged midpoint suffix. -/
theorem residual_left_support_midpoint
    (HP : FourthRootHierarchyParams 16 1 16 32 8) (D : ZMod P) (ident : V → ZMod P)
    (l bin : ℕ) (source midpoint terminal : Channel P J) (b : ℝ)
    (Kc : ℕ) (bounded cutoff h ρ : ℝ → ℝ) (K : ℕ) (C : Matrix V V ℝ)
    (raw prep : HierarchyTask.Request HP.k (Fin J) (ZMod P) → Environment P J → Matrix V V ℝ)
    (maximum : HierarchyTask.Request HP.k (Fin J) (ZMod P) → Environment P J → V → ℝ)
    (σ : Environment P J) (x z : V) :
    let r := (HierarchyTask.rawRequests (k := HP.k) l bin .residual source midpoint terminal b).left
    incomingChildren HP D ident Kc bounded raw prep maximum r σ x z ≠ 0 ∨
      canonicalRequestChild HP D ident C cutoff h ρ K r σ x z ≠ 0 →
      midpoint.retains (channels D) σ (ident z) := by
  dsimp only
  intro hs
  by_contra hz
  rcases hs with hs | hs
  · exact hs (incomingChildren_zero_off_usage HP D ident Kc bounded raw prep maximum _ σ x z hz)
  · exact hs (canonicalRequestChild_zero_off_usage HP D ident C cutoff h ρ K _ σ x z hz)

/-- Changing the dense scalar recipe only at unused inputs leaves its real evaluation
unchanged. Raw full-rank gates and the genuine preparation are identical. -/
theorem denseChild_congr_cutoff (D : ZMod P) (ident : V → ZMod P)
    {k : ℕ} (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (C : Matrix V V ℝ) (a b h ρ : ℝ → ℝ) (K : ℕ)
    (hab : ∀ x y, a (C x y / r.terminal.rate) = b (C x y / r.terminal.rate))
    (σ : Environment P J) : denseChild D ident r a h ρ K C σ =
      denseChild D ident r b h ρ K C σ := by
  ext x y
  unfold denseChild normalizedRequest
  split_ifs
  · simp only [DenseRowRecipe.normalized, hab]
  · rfl

/-- The genuine dense child range is inherited from the same normalized evaluator.
This remains valid on empty source/usage events. -/
theorem denseChild_range (D : ZMod P) (ident : V → ZMod P)
    {k : ℕ} (r : HierarchyTask.Request k (Fin J) (ZMod P))
    (C : Matrix V V ℝ) (cutoff h ρ : ℝ → ℝ) (K : ℕ)
    {B : ℝ} (hB : 0 ≤ B) (hcutoff : ∀ v, cutoff v ∈ Set.Icc 0 B)
    (hρ : ∀ v, ρ v ∈ Set.Icc 0 1) (σ : Environment P J) (x y : V) :
    |denseChild D ident r cutoff h ρ K C σ x y| ≤ 2 * B := by
  have hb : denseChild D ident r cutoff h ρ K C σ x y ∈ Set.Icc 0 (2 * B) := by
    unfold denseChild normalizedRequest
    split_ifs
    · exact DenseRowRecipe.normalized_mem_Icc _ _ _ _ _ _ _ hB hcutoff hρ _ _ _ _ _
    · exact ⟨le_rfl, by positivity⟩
  exact (abs_of_nonneg hb.1).trans_le hb.2

end Matrix.HierarchyParams.H4RankEnvironment
