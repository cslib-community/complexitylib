/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.LogSpaceDerandomization.PilotTasks
public import Complexity.Computability.LogSpaceDerandomization.HierarchySampling
public import Complexity.Computability.LogSpaceDerandomization.HierarchyAtomCutoff

/-!
# Stochastic pilot preparation and normalization

The complete local pilot family of [OpenAI2026LogSpace, Sections 5.3–5.4 and 7.1–7.2],
revision `7ef5c0cc`, extends `PilotTask` with the preparation (5.13) and normalized correction
(5.14). Our input index `i` is the source's step `i+1`. The pilot multiplier is
`γ(M_(i+1)(y))`, after the current detector, whereas the actual correction uses `γ(M_k(y))`.
Both use the incoming gate on the completed raw table, ranked over the fixed retained source
set before port filtering. The detector score (5.16) remains unnormalized and has no incoming gate.

Recipes accept arbitrary child functions. The raw input is `C + Êᵢ C`, with the right row called
at the midpoint (source release). The preparation and normalized row use the inherited source
channel `Xs`, broad rank channel `Z` at stage rate `f`, and usage channel `Zt` at rate `t ≤ f`.
The channels can already have arbitrary fixed padding suffixes applied: every call keeps those
functions, and the second signal averages on `Xs(x) × Zt(y)`, without an importance factor.
The newly completed maximum is a vertex function on the broad detector domain, not a value
at an endpoint carried as a task parameter. Suffix invariance and admissible rates are supplied
by the channel laws; this file introduces no native suffix encoding.

`PilotRowTask.children` inserts preparation and normalization into the existing deterministic
pilot order, and the correction's expectation is a real client of the normalized child.
`PilotSampling.ofChannels` derives the incoming-count premise from the current pilot detector,
not the final actual multiplier. Exact means follow from primitive pair-count and gate laws,
with no assumed mean/error certificate. The common recipes and atom theory are shared with
`CorrectionRowTasks`; only the true input and maximum differ.

The bounded scalar cutoff agrees with the true pilot input for `i ≤ k`; beyond that range the
recipe remains bounded without a true-mean claim. The gate and preparatory cutoffs retain their
explicit primitive contracts. The shared atom law uses quarter-failure budgets sufficient for
exact means, without claiming the source's stronger `3/4` denominator margin. Range bounds do not
establish root regularity or error recurrence.
The global stage order, routed bins, cross-stage copy/reward assembly, mean prefixes,
noise/compression, strong recursion and native workspace/class equality remain open.
Exact finite means are independent of the fourth/eighth moment choice; precision clients
retain the integer rate grid.

## Main definitions

* `Matrix.HierarchyParams.PilotRowTask`: pilot constructors with stochastic children.
* `Matrix.HierarchyParams.PilotSampling`: primitive laws for the current pilot input/multiplier.
* `Matrix.HierarchyParams.PilotSampling.normalizedRecipe`: bounded arbitrary-child assembly.
* `Matrix.HierarchyParams.PilotSampling.ofChannels`: detector/channel-derived sampling data.

## Main results

* `Matrix.HierarchyParams.PilotRowTask.rank_lt_of_mem_children`: computed dependency decrease.
* `Matrix.HierarchyParams.PilotSampling.normalizedRecipe_mem_Icc`: arbitrary-estimate range.
* `Matrix.HierarchyParams.PilotSampling.expect_normalizedRecipe`: conditional pilot identity.
* `Matrix.HierarchyParams.PilotSampling.value_correction_mean`: actual normalized-child client.
-/

public section

universe u

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

/-- The existing deterministic pilot, with one preparation and normalized row per step. -/
inductive PilotRowTask where
  | pilot (t : PilotTask)
  | preparation (i : ℕ)
  | normalized (i : ℕ)
  deriving DecidableEq

namespace PilotRowTask

/-- Preparations and normalizations read whole earlier children. Corrections additionally use
normalization through its proved conditional mean; deterministic inputs are retained. -/
@[expose] def children : PilotRowTask → List PilotRowTask
  | .pilot (.correction (i + 1)) =>
      [.pilot (.input i), .pilot (.maximum (i + 1)), .normalized i]
  | .pilot t => t.children.map .pilot
  | .preparation i => [.pilot (.input i)]
  | .normalized i => [.pilot (.input i), .preparation i, .pilot (.maximum (i + 1))]

/-- Three slots per old pilot rank leave room after the current maximum and before correction. -/
@[expose] def rank : PilotRowTask → ℕ
  | .pilot t => 3 * t.rank
  | .preparation i => 15 * i + 19
  | .normalized i => 15 * i + 20

/-- Every actual child is earlier, including the newly completed maximum and normalized row. -/
theorem rank_lt_of_mem_children {parent child : PilotRowTask} (h : child ∈ parent.children) :
    child.rank < parent.rank := by
  cases parent with
  | pilot t =>
    cases t with
    | correction i =>
      cases i with
      | zero => simp [children, PilotTask.children] at h
      | succ i =>
        simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl <;> simp only [rank, PilotTask.rank] <;> omega
    | base => simp [children, PilotTask.children] at h
    | input i | score i | detector i | maximum i =>
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
      have := PilotTask.rank_lt_of_mem_children hs
      simp only [rank]
      omega
  | preparation i =>
    simp only [children, List.mem_singleton] at h
    subst child
    simp only [rank, PilotTask.rank]
    omega
  | normalized i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp only [rank, PilotTask.rank] <;> omega

/-- Expanded tasks have a fixed number of slots per finite pilot iteration. -/
@[expose] def iteration : PilotRowTask → ℕ
  | .pilot t => t.iteration
  | .preparation i | .normalized i => i

/-- Bound computed from the original finite iteration count, including stochastic children. -/
theorem rank_le {t : PilotRowTask} {k : ℕ} (h : t.iteration ≤ k) :
    t.rank ≤ 15 * k + 20 := by
  cases t with
  | pilot t =>
    have := PilotTask.rank_le h
    simp only [rank]
    omega
  | preparation i | normalized i => simp only [iteration, rank] at *; omega

/-- The original rank is preserved up to a fixed factor on deterministic tasks. -/
theorem rank_pilot (t : PilotTask) : (pilot t).rank = 3 * t.rank := rfl

/-- Child decrease pays the existing scheduled fourth-moment precision cost. -/
theorem scheduled_child_cost_le {parent child : PilotRowTask} (hchild : child ∈ parent.children)
    {A a a' u u' : ℝ} (hA : 0 ≤ A) (M d c : ℕ) (hc : 0 < c) (h : ℤ)
    (ha : 0 < a) (ha' : 0 < a') (hu : 0 < u) (huu' : u ≤ u')
    (hscale : Real.logb 2 (a' / a) = (h : ℝ)) :
    Cslib.LogSpaceEstimation.binNormCost 4 (h : ℝ) *
        (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4) *
        (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A
          (Cslib.LogSpaceEstimation.lastBudget M d c h) child.rank a' u') ≤
      (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A M parent.rank a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * Cslib.LogSpaceEstimation.scaleMajorant h :=
  Cslib.LogSpaceEstimation.scheduled_child_cost_le hA M d c parent.rank child.rank hc h
    (rank_lt_of_mem_children hchild) ha ha' hu huu' hscale

/-- Actual direct/product input calls inherit their rates from `PilotTask.inputRequests`.
In particular the right base call resets the source to the midpoint rate. -/
theorem rank_lt_of_mem_inputRequests {f u : ℝ} {i : ℕ} {r : PilotTask.Request}
    (hr : r ∈ PilotTask.inputRequests f u i) :
    (pilot r.task).rank < (pilot (.input i)).rank := by
  have := PilotTask.rank_lt_of_mem_inputRequests hr
  simp only [rank]
  omega

/-- The expanded pilot order pays for a real child call with its inherited/reset source rate. -/
theorem input_request_cost_le {f u a A : ℝ} {i : ℕ} {r : PilotTask.Request}
    (hr : r ∈ PilotTask.inputRequests f u i) (hA : 0 ≤ A) (M d c : ℕ) (hc : 0 < c) (h : ℤ)
    (ha : 0 < a) (hf : 0 < f) (hu : 0 < u) (huf : u ≤ f)
    (hscale : Real.logb 2 (f / a) = (h : ℝ)) :
    Cslib.LogSpaceEstimation.binNormCost 4 (h : ℝ) *
        (2 : ℝ) ^ (Real.logb 2 (r.sourceRate / u) / 4) *
        (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A
          (Cslib.LogSpaceEstimation.lastBudget M d c h)
          (pilot r.task).rank r.endRate r.sourceRate) ≤
      (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A M
        (pilot (.input i)).rank a u - A + (d : ℝ) / (16 * c) + 1 / 16) *
          Cslib.LogSpaceEstimation.scaleMajorant h := by
  have hrank := rank_lt_of_mem_inputRequests hr
  have hrates : r.endRate = f ∧ u ≤ r.sourceRate := by
    simp only [PilotTask.inputRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> exact ⟨rfl, by first | exact le_rfl | exact huf⟩
  apply Cslib.LogSpaceEstimation.scheduled_child_cost_le hA M d c
    (pilot (.input i)).rank (pilot r.task).rank hc h hrank
    ha (hrates.1.symm ▸ hf) hu hrates.2
  rwa [hrates.1]

/-- Sampled rows use independent source/terminal seeds; old tasks retain their exact types. -/
abbrev Value (V κ Γ Ζ : Type u) : PilotRowTask → Type _
  | .pilot t => PilotTask.Value V κ t
  | .preparation _ | .normalized _ => Γ × Ζ → Matrix V V ℝ

end PilotRowTask

namespace PilotRowRecipe

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  (f : ℝ)

/-- Unnormalized detector score on an arbitrary completed raw child. It has no incoming gate
or preparatory denominator, as in [OpenAI2026LogSpace, Section 5.4, (5.16)]. -/
@[expose] noncomputable def score (input : Matrix V V ℝ) (t : κ) : Matrix V V ℝ :=
  atomPrep P.ϕ P.ρ P.K f input {w | Y t w}

omit [Fintype κ] in
/-- Arbitrary raw estimates still produce detector scores in the fixed gate range. -/
theorem score_mem_Icc (hρ : ∀ r, 0 ≤ P.ρ r) (input : Matrix V V ℝ) (t : κ) (x y : V) :
    score P Y f input t x y ∈ Set.Icc 0 1 :=
  ⟨mul_nonneg (P.ϕ_nonneg _) (hρ _),
    (mul_le_mul_of_nonneg_left (P.ρ_le_one _) (P.ϕ_nonneg _)).trans
      (by simpa only [mul_one] using P.ϕ_le_one _)⟩

/-- The detector reads the whole score child and averages its padded rank on the broad stage
source/terminal roles. Vector answers are clipped as prescribed after (7.5). -/
@[expose] noncomputable def detector (scores : κ → Matrix V V ℝ) (y : V) : ℝ :=
  min 1 (max 0 (𝔼 s, 𝔼 t ∈ {t | Y t y}, kthLargest P.J {x | X s x}
    (fun x => scores t x y)))

/-- Clipping bounds arbitrary estimated detector children, without assuming their mean. -/
theorem detector_mem_Icc (scores : κ → Matrix V V ℝ) (y : V) :
    detector P X Y scores y ∈ Set.Icc 0 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- The current maximum is assembled from two whole vertex children, then clipped. -/
@[expose] def maximum (previous current : V → ℝ) (y : V) : ℝ :=
  min 1 (max 0 (max (previous y) (current y)))

omit [Fintype V] in
/-- Every pair of estimated vector children gives a bounded running maximum. -/
theorem maximum_mem_Icc (previous current : V → ℝ) (y : V) :
    maximum previous current y ∈ Set.Icc 0 1 :=
  ⟨le_min zero_le_one (le_max_left _ _), min_le_left _ _⟩

/-- Interpret the expanded family with shared preparation and normalization recipes.
The recipes are functions of whole child tables; their sampling laws are separate. -/
@[expose] noncomputable def value
    {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
    {V κ Γ Ζ : Type u} {ι : Type*} [Fintype V] [Fintype ι] [Fintype κ]
    (X : ι → V → Prop) (Y : κ → V → Prop)
    [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
    (f : ℝ) (C : Matrix V V ℝ)
    (prepare : Matrix V V ℝ → Γ × Ζ → Matrix V V ℝ)
    (normalize : Matrix V V ℝ → (Γ × Ζ → Matrix V V ℝ) →
      (V → ℝ) → Γ × Ζ → Matrix V V ℝ) :
    (t : PilotRowTask) → t.Value V κ Γ Ζ
  | .pilot t => PilotTask.value P X Y f C t
  | .preparation j => prepare (PilotTask.value P X Y f C (.input j))
  | .normalized j => normalize (PilotTask.value P X Y f C (.input j))
      (prepare (PilotTask.value P X Y f C (.input j)))
      (PilotTask.value P X Y f C (.maximum (j + 1)))

end PilotRowRecipe

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V κ Γ Ζ : Type u} {ι : Type*} [Fintype V] [Fintype ι] [Fintype κ]
  [Fintype Γ] [Fintype Ζ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  (Xs : Γ → V → Prop) (Z Zt : Ζ → V → Prop)
  [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
  (f : ℝ) (C : Matrix V V ℝ) (i : ℕ)

/-- Primitive sampling data for the pilot input and its current completed maximum. The laws are
shared with actual corrections, but their input and multiplier are different. -/
structure PilotSampling extends
    CorrectionSamplingLaws P.Q (PilotTask.value P X Y f C (.input i))
      (fun y => P.γ (PilotTask.value P X Y f C (.maximum (i + 1)) y))
      Xs Z Zt f ((i : ℝ) + 1)

namespace PilotSampling

variable {P X Y Xs Z Zt f C i}
  (A : P.PilotSampling X Y Xs Z Zt f C i)

/-- Preparation recomputes all incoming scores from the substituted raw child. -/
@[expose] noncomputable def preparationRecipe (input : Matrix V V ℝ)
    (σ : Γ × Ζ) : Matrix V V ℝ :=
  CorrectionRowRecipe.preparation A.I A.τ A.h A.ρ A.K A.Kc f Xs Z input σ

/-- The pilot uses the same bounded normalized row recipe as actual corrections; its maximum
child is the current one. The child functions may be arbitrary estimates. -/
@[expose] noncomputable def normalizedRecipe (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : Γ × Ζ) (x y : V) : ℝ :=
  CorrectionRowRecipe.normalized A.I A.τ A.ρ P.atomCutoff P.γ A.K A.Kc f Xs Z Zt
    input prep maximum σ x y

/-- Arbitrary oversized/negative raw, preparatory and maximum estimates stay uniformly bounded. -/
theorem normalizedRecipe_mem_Icc (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V) :
    A.normalizedRecipe input prep maximum σ x y ∈ Set.Icc 0 (2 * P.Q P.atomCap) :=
  CorrectionRowRecipe.normalized_mem_Icc A.I A.τ A.ρ P.atomCutoff P.γ A.K A.Kc f Xs Z Zt
    (P.Q_nonneg _) P.atomCutoff_nonneg P.atomCutoff_le A.ρ_nonneg A.ρ_le_one
    A.τ_nonneg A.τ_le_one P.γ_nonneg P.γ_le_one input prep maximum σ x y

/-- Nonpositive first signals cannot introduce support under estimated-child substitution. -/
theorem normalizedRecipe_eq_zero_of_nonpos (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V)
    (hd : input x y / f ≤ 0) : A.normalizedRecipe input prep maximum σ x y = 0 := by
  simp only [normalizedRecipe, CorrectionRowRecipe.normalized, P.atomCutoff_eq_zero hd,
    zero_mul, zero_div, ite_self]

/-- Only the narrower usage mask controls zero extension, for all substituted children. -/
theorem normalizedRecipe_eq_zero_of_not_usage (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V)
    (hy : ¬ Zt σ.2 y) : A.normalizedRecipe input prep maximum σ x y = 0 := by
  simp only [normalizedRecipe, CorrectionRowRecipe.normalized, ite_eq_right hy]

/-- Bounded estimated rows retain the original row-support guarantee. Preparation substitution
cannot create a nonzero entry when the cutoff or row gate vanishes. -/
theorem card_filter_normalizedRecipe_row_ne_zero_lt (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x : V)
    (hK : 0 < A.K) {e g : ℝ} (he : 0 ≤ e)
    (hQ : ∀ d, d ≤ e → P.Q d = 0) (hg : g ≤ e)
    (hρ : ∀ r, g ≤ r → A.ρ r = 0) :
    #{y ∈ ({w | Z σ.2 w} : Finset V) |
      A.normalizedRecipe input prep maximum σ x y ≠ 0} < A.K := by
  exact CorrectionRowRecipe.card_filter_normalized_row_ne_zero_lt
    A.I A.τ A.ρ P.atomCutoff P.γ A.K A.Kc f Xs Z Zt input prep maximum σ x hK he
    (fun d hd => P.atomCutoff_eq_zero_of_Q_eq_zero (hQ d hd)) hg hρ

/-- The incoming support bound also survives arbitrary child substitutions. Scores and ranks
use the original raw table, and the cap cannot introduce new scalar support. -/
theorem card_filter_normalizedRecipe_col_ne_zero_lt (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (y : V)
    (hKc : 0 < A.Kc) (hIQ : ∀ v r, P.Q v ≠ 0 → A.ρ r ≠ 0 → A.I v r = 1)
    {g : ℝ} (hg : g ≤ 1) (hτ : ∀ r, g ≤ r → A.τ r = 0) :
    #{x ∈ ({w | Xs σ.1 w} : Finset V) |
      A.normalizedRecipe input prep maximum σ x y ≠ 0} < A.Kc := by
  exact CorrectionRowRecipe.card_filter_normalized_col_ne_zero_lt
    A.I A.τ A.ρ P.atomCutoff P.γ A.K A.Kc f Xs Z Zt input prep maximum σ y hKc
    (fun v r hv hr => hIQ v r
      (fun h0 => hv (P.atomCutoff_eq_zero_of_Q_eq_zero h0)) hr) hg hτ

/-- Values of the complete local family use the existing pilot at every deterministic task. -/
@[expose] noncomputable def value : (t : PilotRowTask) → t.Value V κ Γ Ζ :=
  PilotRowRecipe.value P X Y f C A.preparationRecipe A.normalizedRecipe

/-- Raw input calls the right base row at the midpoint, releasing the old source. -/
theorem value_input (j : ℕ) : A.value (.pilot (.input j)) =
    CorrectionRowRecipe.input (A.value (.pilot .base)) (A.value (.pilot (.correction j)))
      (A.value (.pilot .base)) := rfl

/-- Preparatory calls retain the same source/rank functions, including all fixed suffixes. -/
theorem value_preparation (j : ℕ) : A.value (.preparation j) =
    A.preparationRecipe (A.value (.pilot (.input j))) := rfl

/-- The normalized child uses the just-completed maximum, not the final pilot maximum. -/
theorem value_normalized (j : ℕ) : A.value (.normalized j) =
    A.normalizedRecipe (A.value (.pilot (.input j))) (A.value (.preparation j))
      (A.value (.pilot (.maximum (j + 1)))) := rfl

/-- The detector still reads the earlier score row without normalization or an incoming gate. -/
theorem value_detector (j : ℕ) (y : V) : A.value (.pilot (.detector j)) y =
    𝔼 s, 𝔼 t ∈ {t | Y t y}, kthLargest P.J {x | X s x}
      (fun x => A.value (.pilot (.score j)) t x y) := rfl

/-- Substituting the true input in the score recipe gives the original detector table. -/
theorem value_score_recipe (j : ℕ) : A.value (.pilot (.score j)) =
    PilotRowRecipe.score P Y f (A.value (.pilot (.input j))) := rfl

/-- The clipped detector recipe agrees on true scores, including empty/zero-padded ranks. -/
theorem value_detector_recipe (j : ℕ) : A.value (.pilot (.detector j)) =
    PilotRowRecipe.detector P X Y (A.value (.pilot (.score j))) := by
  ext y
  change columnDetector X Y P.ϕ P.ρ P.J P.K f
    (PilotTask.value P X Y f C (.input j)) y = min 1 (max 0 _)
  have h0 := columnDetector_nonneg (X := X) (Y := Y) (ϕ := P.ϕ) (ρ := P.ρ)
    (J := P.J) (K := P.K) (f := f) (G := PilotTask.value P X Y f C (.input j)) (y := y)
  have h1 := columnDetector_le_one (X := X) (Y := Y) (ϕ := P.ϕ) (ρ := P.ρ)
    (J := P.J) (K := P.K) (f := f) (G := PilotTask.value P X Y f C (.input j)) (y := y)
    P.ϕ_nonneg P.ϕ_le_one P.ρ_le_one
  exact (min_eq_right h1).symm.trans (congrArg (min 1) (max_eq_right h0).symm)

/-- The true running maximum stays in the vector range at every iteration. -/
theorem value_maximum_mem_Icc (j : ℕ) (y : V) :
    A.value (.pilot (.maximum j)) y ∈ Set.Icc 0 1 := by
  induction j with
  | zero =>
    change pilotMax _ _ _ _ 0 y ∈ Set.Icc (0 : ℝ) 1
    rw [pilotMax_zero]
    exact ⟨le_rfl, zero_le_one⟩
  | succ j ih =>
    have hd := PilotRowRecipe.detector_mem_Icc P X Y (A.value (.pilot (.score j))) y
    rw [← A.value_detector_recipe] at hd
    change PilotTask.value P X Y f C (.maximum (j + 1)) y ∈ Set.Icc (0 : ℝ) 1
    rw [PilotTask.value_maximum_succ, Pi.sup_apply]
    exact ⟨ih.1.trans (le_max_left _ _), max_le ih.2 hd.2⟩

/-- Substituting the two earlier vector children gives the actual current maximum. -/
theorem value_maximum_recipe (j : ℕ) : A.value (.pilot (.maximum (j + 1))) =
    PilotRowRecipe.maximum (A.value (.pilot (.maximum j)))
      (A.value (.pilot (.detector j))) := by
  ext y
  have hm := A.value_maximum_mem_Icc (j + 1) y
  have hv : A.value (.pilot (.maximum (j + 1))) y =
      max (A.value (.pilot (.maximum j)) y) (A.value (.pilot (.detector j)) y) :=
    congrFun (PilotTask.value_maximum_succ P X Y f C j) y
  rw [hv] at hm ⊢
  simp only [PilotRowRecipe.maximum, max_eq_right hm.1, min_eq_right hm.2]

/-- The maximum child includes the current detector. -/
theorem value_maximum_succ (j : ℕ) : A.value (.pilot (.maximum (j + 1))) =
    A.value (.pilot (.maximum j)) ⊔ A.value (.pilot (.detector j)) :=
  PilotTask.value_maximum_succ P X Y f C j

/-- True-input clipping agreement follows from the pilot's correction-sequence entry bound. -/
theorem normalizedRecipe_eq_atom (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    (σ : Γ × Ζ) (x y : V) :
    A.value (.normalized i) σ x y =
      correctionAtom A.I A.τ A.K A.Kc f (PilotTask.value P X Y f C (.input i))
        Xs Z Zt P.Q A.h A.ρ
        (fun y => P.γ (PilotTask.value P X Y f C (.maximum (i + 1)) y)) σ x y := by
  have hb := PilotTask.value_input_bounds P X Y f C hf hC hC1 i
  have hseq := isCorrectionSeq_pilotCorrection
    (U := columnDetector X Y P.ϕ P.ρ P.J P.K f) hC (P.cutoff_nonneg hf)
    (fun t ht => (P.cutoff_le hf t).trans (max_le (by
      have := mul_nonneg P.θ_pos.le hf.le
      linarith) ht)) P.γ_nonneg P.γ_le_one
  have hd0 : 0 ≤ PilotTask.value P X Y f C (.input i) x y / f :=
    div_nonneg (hb.1 x y) hf.le
  have hdk : PilotTask.value P X Y f C (.input i) x y / f ≤ (P.k : ℝ) + 1 := by
    apply (div_le_iff₀ hf).mpr
    exact (hseq.input_le_mul hCf hf.le hC1 i x y).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.add_le_add_right hi 1) hf.le)
  simp only [value, PilotRowRecipe.value, normalizedRecipe, CorrectionRowRecipe.normalized,
    correctionAtom,
    P.atomCutoff_eq hd0 hdk]
  rfl

/-- On the source/usage slice, the normalized pilot row has the exact pilot correction mean. -/
theorem expect_normalizedRecipe (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (y : V) :
    (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({t | Zt t y} : Finset Ζ),
      f * A.value (.normalized i) σ x y) = A.value (.pilot (.correction (i + 1))) x y := by
  simp_rw [A.normalizedRecipe_eq_atom hf hC hC1 hCf hi]
  rw [← mul_expect, A.toCorrectionSamplingLaws.expect_atom hf
    (PilotTask.value_input_bounds P X Y f C hf hC hC1 i).1
    (PilotTask.value_input_bounds P X Y f C hf hC hC1 i).2 hx y]
  simp only [value, PilotRowRecipe.value]
  rw [PilotTask.value_correction_succ]
  ring

/-- The actual deterministic correction constructor is the mean of its earlier normalized child.
The actual usage density, rather than the nominal rate, cancels the membership mask. -/
theorem value_correction_mean (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (y : V) :
    A.value (.pilot (.correction (i + 1))) x y =
      𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
        (f / A.π) * A.value (.normalized i) σ x y := by
  simp_rw [A.normalizedRecipe_eq_atom hf hC hC1 hCf hi]
  rw [A.toCorrectionSamplingLaws.expect_atom_unconditioned hf
    (PilotTask.value_input_bounds P X Y f C hf hC hC1 i).1
    (PilotTask.value_input_bounds P X Y f C hf hC hC1 i).2 hx y]
  exact PilotTask.value_correction_succ P X Y f C i x y

/-- The second signal uses the same preparatory child and narrower channel functions. -/
theorem secondChannel_eq (ζ : ℝ) (σ : Γ × Ζ) (x y : V) :
    CorrectionRowRecipe.secondChannel Xs Zt ζ (A.value (.preparation i)) σ x y =
      if Zt σ.2 y then ζ * correctionNormalizer A.I A.τ A.K A.Kc f
        (PilotTask.value P X Y f C (.input i)) Xs Z Zt A.h A.ρ x y else 0 := rfl

end PilotSampling
end Matrix.HierarchyParams

namespace Matrix.HierarchyParams.PilotSampling

variable {q cπ Cπ Cpair Cvar : ℝ} (P : FourthRootHierarchyParams q cπ Cπ Cpair Cvar)
  {V ι κ : Type u} [Fintype V] [Fintype ι] [Fintype κ]
  (X : ι → V → Prop) (Y : κ → V → Prop)
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {f π : ℝ} {C : Matrix V V ℝ} {i : ℕ}

/-- Build pilot correction sampling data from two ordered channel laws and primitive cutoffs.
The incoming count follows from the hierarchy detector, rather than being a supplied field. -/
noncomputable def ofChannels
    (hXY : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hYX : Cslib.Probability.RetentionChannels Y X f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hπ : 0 < π) (hcπ : 0 < cπ) (hpair : 0 ≤ Cpair)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hi : i < P.k)
    (I : ℝ → ℝ → ℝ) (τ h : ℝ → ℝ) (τ₀ : ℝ)
    (hQ : ∀ v, P.Q v ≠ 0 → h v = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) (hτ₀ : 0 ≤ τ₀)
    (hτ : ∀ r, r ≤ τ₀ → τ r = 1) (hI : ∀ v r, v ≤ P.δ₁ → I v r = 0) :
    P.toHierarchyParams.PilotSampling X Y X Y Y f C i where
  toCorrectionSamplingLaws := CorrectionSamplingLaws.ofHierarchyChannels P X Y
    hXY hYX hf hπ hpair hi
    (fun z hg => P.toHierarchyParams.pilotInput_count_le X Y hXY hf hcπ hpair hC hC1 hi (z := z) hg)
    I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

variable
    (hXY : Cslib.Probability.RetentionChannels X Y f π cπ Cπ Cpair Cvar)
    (hYX : Cslib.Probability.RetentionChannels Y X f π cπ Cπ Cpair Cvar)
    (hf : 0 < f) (hπ : 0 < π) (hcπ : 0 < cπ) (hpair : 0 ≤ Cpair)
    (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1) (hi : i < P.k)
    (I : ℝ → ℝ → ℝ) (τ h : ℝ → ℝ) (τ₀ : ℝ)
    (hQ : ∀ v, P.Q v ≠ 0 → h v = 1)
    (hτ0 : ∀ r, 0 ≤ τ r) (hτ1 : ∀ r, τ r ≤ 1) (hτ₀ : 0 ≤ τ₀)
    (hτ : ∀ r, r ≤ τ₀ → τ r = 1) (hI : ∀ v r, v ≤ P.δ₁ → I v r = 0)

/-- The channel constructor preserves its `I` parameter. -/
theorem ofChannels_I :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).I = I := by
  unfold ofChannels
  exact CorrectionSamplingLaws.ofHierarchyChannels_I P X Y hXY hYX hf hπ hpair hi
    _ I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

/-- The channel constructor preserves its `τ` parameter. -/
theorem ofChannels_τ :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).τ = τ := by
  unfold ofChannels
  exact CorrectionSamplingLaws.ofHierarchyChannels_τ P X Y hXY hYX hf hπ hpair hi
    _ I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

/-- The channel constructor preserves its `ρ` parameter. -/
theorem ofChannels_ρ :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).ρ = P.ρ := by
  unfold ofChannels
  exact CorrectionSamplingLaws.ofHierarchyChannels_ρ P X Y hXY hYX hf hπ hpair hi
    _ I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

/-- The channel constructor preserves its `Kc` parameter. -/
theorem ofChannels_Kc :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).Kc = ⌈4 * (1
        + Cpair * P.R)⌉₊ := by
  unfold ofChannels
  exact CorrectionSamplingLaws.ofHierarchyChannels_Kc P X Y hXY hYX hf hπ hpair hi
    _ I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

/-- The pilot channel constructor retains its preparation cutoff. -/
theorem ofChannels_h :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).h = h := by
  unfold ofChannels
  exact CorrectionSamplingLaws.ofHierarchyChannels_h P X Y hXY hYX hf hπ hpair hi
    _ I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

/-- The pilot channel constructor retains the hierarchy row rank. -/
theorem ofChannels_K :
    (ofChannels P X Y hXY hYX hf hπ hcπ hpair hC hC1 hi
      I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI).K = P.K := by
  unfold ofChannels
  exact CorrectionSamplingLaws.ofHierarchyChannels_K P X Y hXY hYX hf hπ hpair hi
    _ I τ h τ₀ hQ hτ0 hτ1 hτ₀ hτ hI

end Matrix.HierarchyParams.PilotSampling
