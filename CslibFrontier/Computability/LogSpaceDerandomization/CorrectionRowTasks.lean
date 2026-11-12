/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.LogSpaceDerandomization.PilotRowTasks
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchySampling
public import CslibFrontier.Computability.LogSpaceDerandomization.HierarchyAtomCutoff

/-!
# Unified pilot, actual-correction and copy/reward tasks

This is the actual-correction family of [OpenAI2026LogSpace, Sections 5.3, 7.1–7.4], revision
`7ef5c0cc`: the raw input is `C + Eᵢ C`, the preparation is (5.13), and the normalized row is
(5.14), using the bounded cutoff `Qat(d) = Q(clip_[0,B_Q](d))` on arbitrary computed inputs.
We choose `B_Q = max (k + 1) θ₂ + 1`, strictly above the true normalized entry bound and `θ₂`.
Only the argument to `Q` is clipped: gates and ranks still read the original child table.
The exact hierarchy continues to use uncapped `Q`. The multiplier is the final pilot maximum,
rather than the current pilot maximum.
The incoming scores and gates are local operations on the completed raw matrix, not recursive
calls to another task. Constructor ranks below account for the final pilot and actual iterations.
True agreement is proved for `i ≤ k` from nonnegative substochastic `C` with entries at most `f`.
Beyond this iteration range the constructor is still bounded, without a true-mean claim.

The recipes take child *functions*, so substituting estimates changes all entries before ranks
are evaluated. Source and terminal channels are explicit function arguments: `Xs` has the inherited
source role/rate, `Z` the stage-rank role/rate, and `Zt` the usage role/rate. They may already be
partially applied to fixed padding suffixes. Every call below retains these same functions and
suffixes. The preparation's conditional mean uses `Xs(x)` and `Zt(y)`, with no importance factor;
the normalized row is extended by zero outside `Zt(y)`. Neither an old source nor a fixed endpoint
is retained as a child parameter. Both remain arguments of the child row.

The actual family embeds the expanded stochastic `PilotRowTask`, including its normalized
child-to-correction edge. A pilot of at most `k` iterations uses at most `15*k+20` rank slots;
actual iterations, the copy weights and the reward/projection constructors follow this bound.
No caller supplies a rank certificate. The shared evaluator accepts whole preparation and
normalization functions; embedded pilot mean laws require the pilot's own primitive sampling
contract, with the same recipes, rather than using actual-correction laws for a different input.

`inputRequests` and `rewardRequests` retain channel roles, rates and already applied suffixes.
The right child restarts on the midpoint tuple. `expect_rewardRequests` instantiates those tuples
as actual channel predicates and proves the mean and computed dependency decrease for (7.5).
`expect_hierarchyTaskReward` connects this local recipe to the existing `DetectedHierarchy` reward,
including nonprimary copy weights computed from the final pilot vector.

This completes the unified local families and copy/reward client. `HierarchyTasks` connects the
local previous-reward and base-matrix leaves to bounded earlier-stage constructors. Raw
direct/routed-bin recursion, cross-stage role tuple assembly and the scheduled mean-prefix
theorem remain open. Range and exact means do not prove root regularity
or the full error recurrence. Primitive cutoffs retain the explicit contracts
of `CorrectionSampling`. Mean identities are exact finite identities, independent of the source's
eighth versus our fourth moments; no new real-valued rate schedule is asserted.

## Main definitions

* `Matrix.HierarchyParams.CorrectionRowTask`: unified expanded pilot/actual/copy/reward order.
* `Matrix.HierarchyParams.CorrectionRowTask.rewardRequests`: actual role/rate/suffix calls.
* `Matrix.HierarchyParams.CorrectionSampling.preparationRecipe`: local incoming-gate assembly.
* `Matrix.HierarchyParams.CorrectionSampling.normalizedRecipe`: actual child-function recipe.

## Main results

* `Matrix.HierarchyParams.CorrectionRowTask.rank_lt_of_mem_children`: computed rank decrease.
* `Matrix.HierarchyParams.CorrectionSampling.normalizedRecipe_mem_Icc`: arbitrary-child range.
* `Matrix.HierarchyParams.CorrectionSampling.normalizedRecipe_eq_atom`: true-input agreement.
* `Matrix.HierarchyParams.CorrectionSampling.expect_normalizedRecipe`: channel-derived true mean.
* `Matrix.expect_hierarchyTaskReward`: local task recipe realizes the actual hierarchy reward.
-/

public section

universe u

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

/-- Fixed-stage constructors, including stochastic pilot preparation and normalization. -/
inductive CorrectionRowTask where
  | pilot (t : PilotRowTask)
  | correction (i : ℕ)
  | input (i : ℕ)
  | preparation (i : ℕ)
  | normalized (i : ℕ)
  /-- Reward inherited from the previous stage; cross-stage assembly is separate. -/
  | previousReward
  /-- All copy weights, computed from the completed pilot maximum. -/
  | weights
  /-- Reward after the specified actual correction iterate. -/
  | reward (i : ℕ)
  /-- Copy projection of the corrected reward. -/
  | projectedReward (i : ℕ)
  deriving DecidableEq

namespace CorrectionRowTask

/-- Actual inputs of a constructor. The final pilot is completed before actual corrections begin. -/
@[expose] def children (k : ℕ) : CorrectionRowTask → List CorrectionRowTask
  | .pilot t => t.children.map .pilot
  | .correction 0 => []
  | .correction (i + 1) => [.input i, .pilot (.pilot (.maximum k)), .normalized i]
  | .input i => [.pilot (.pilot .base), .correction i]
  | .preparation i => [.input i]
  | .normalized i => [.input i, .preparation i, .pilot (.pilot (.maximum k))]
  | .previousReward => []
  | .weights => [.pilot (.pilot (.maximum k))]
  | .reward i => [.previousReward, .correction i]
  | .projectedReward 0 => [.weights, .reward 0]
  | .projectedReward (i + 1) => [.weights, .reward (i + 1), .previousReward, .normalized i]

/-- The finite expanded pilot occupies at most `15 * k + 20` slots. Actual iterations
follow it with five slots each; reward and copy projection follow their correction. -/
@[expose] def rank (k : ℕ) : CorrectionRowTask → ℕ
  | .pilot t => t.rank
  | .correction i => 15 * k + 5 * i + 21
  | .input i => 15 * k + 5 * i + 22
  | .preparation i => 15 * k + 5 * i + 23
  | .normalized i => 15 * k + 5 * i + 24
  | .previousReward => 1
  | .weights => 15 * k + 21
  | .reward i => 15 * k + 5 * i + 25
  | .projectedReward i => 15 * k + 5 * i + 26

/-- Iteration bound inherited from the actual constructor, including the expanded pilot. -/
@[expose] def iteration : CorrectionRowTask → ℕ
  | .pilot t => t.iteration
  | .correction i | .input i | .preparation i | .normalized i | .reward i |
      .projectedReward i => i
  | .previousReward | .weights => 0

/-- Both finite local families and their copy/reward client fit in a computed stage block.
This is a local bound; no global stage recursion is defined here. -/
theorem rank_le {t : CorrectionRowTask} {k : ℕ} (h : t.iteration ≤ k) :
    t.rank k ≤ 20 * k + 26 := by
  cases t with
  | pilot t =>
    have := PilotRowTask.rank_le h
    simp only [rank]
    omega
  | correction i | input i | preparation i | normalized i | reward i | projectedReward i =>
    simp only [iteration, rank] at *
    omega
  | previousReward | weights => simp only [rank]; omega

/-- Every actual child is earlier, including preparation and the final pilot multiplier. -/
theorem rank_lt_of_mem_children {k : ℕ} {parent child : CorrectionRowTask}
    (h : child ∈ parent.children k) : child.rank k < parent.rank k := by
  cases parent with
  | pilot t =>
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact PilotRowTask.rank_lt_of_mem_children hs
  | correction i =>
    cases i with
    | zero => simp [children] at h
    | succ i =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl <;>
        simp only [rank, PilotRowTask.rank, PilotTask.rank] <;> omega
  | input i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [rank, PilotRowTask.rank, PilotTask.rank] <;> omega
  | preparation i =>
    simp only [children, List.mem_singleton] at h
    subst child
    simp only [rank]
    omega
  | normalized i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp only [rank, PilotRowTask.rank, PilotTask.rank] <;> omega
  | previousReward => simp [children] at h
  | weights =>
    simp only [children, List.mem_singleton] at h
    subst child
    simp only [rank, PilotRowTask.rank, PilotTask.rank]
    omega
  | reward i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [rank] <;> omega
  | projectedReward i =>
    cases i with
    | zero =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp only [rank] <;> omega
    | succ i =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl | rfl | rfl <;> simp only [rank] <;> omega

/-- A channel argument includes its role, rate and already inherited padding.
The suffix type is abstract: this does not introduce a native identifier encoding. -/
structure Channel (Role Suffix : Type*) where
  /-- Independent channel role. -/
  role : Role
  /-- Retention rate on this vertex domain. -/
  rate : ℝ
  /-- Fixed padding passed unchanged to child calls. -/
  suffix : Suffix

/-- Interpret a channel tuple with the existing channel family. Padding is passed as is. -/
abbrev Channel.retains {Role Suffix Ω V : Type*}
    (ch : Channel Role Suffix) (channels : Role → ℝ → Suffix → Ω → V → Prop) : Ω → V → Prop :=
  channels ch.role ch.rate ch.suffix

/-- A genuine row or vector call, with explicit conditioning and usage domains. -/
structure Request (Role Suffix : Type*) where
  /-- Constructor whose whole function is called. -/
  task : CorrectionRowTask
  /-- Inherited source, or the midpoint channel after source release. -/
  source : Channel Role Suffix
  /-- Row endpoint domain; absent for vectors. -/
  terminal : Option (Channel Role Suffix)
  /-- Usage domain; absent for vectors. -/
  usage : Option (Channel Role Suffix)

/-- Direct and product calls for the actual raw input. Right multiplication resets the
source to the midpoint role, rate and padding; it does not retain the old source vertex. -/
@[expose] def inputRequests {Role Suffix : Type*}
    (source midpoint terminal : Channel Role Suffix) (i : ℕ) : List (Request Role Suffix) :=
  [⟨.pilot (.pilot .base), source, some terminal, some terminal⟩,
   ⟨.correction i, source, some midpoint, some midpoint⟩,
   ⟨.pilot (.pilot .base), midpoint, some terminal, some terminal⟩]

/-- The copy/reward sample calls the broad copy weight, the inherited reward, the
normalized correction and the reward restarted on the midpoint domain, in (7.5) order.
Channels may already include fixed copy-symbol padding and inherited suffixes. -/
@[expose] def rewardRequests {Role Suffix : Type*}
    (source broadSource midpoint : Channel Role Suffix) (i : ℕ) :
    List (Request Role Suffix) :=
  [⟨.weights, broadSource, none, none⟩,
   ⟨.previousReward, source, none, none⟩,
   ⟨.normalized i, source, some midpoint, some midpoint⟩,
   ⟨.previousReward, midpoint, none, none⟩]

/-- The task of every request in `inputRequests` is a child of `input i`, so it has smaller rank
(`rank_lt_of_mem_children`). -/
theorem inputRequest_mem_children {Role Suffix : Type*}
    {source midpoint terminal : Channel Role Suffix} {i k : ℕ} {r : Request Role Suffix}
    (hr : r ∈ inputRequests source midpoint terminal i) : r.task ∈ (input i).children k := by
  simp only [inputRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl <;> simp [children]

/-- The task of every request in `rewardRequests` is a child of `projectedReward (i + 1)`, so it
has smaller rank (`rank_lt_of_mem_children`). -/
theorem rewardRequest_mem_children {Role Suffix : Type*}
    {source broadSource midpoint : Channel Role Suffix} {i k : ℕ} {r : Request Role Suffix}
    (hr : r ∈ rewardRequests source broadSource midpoint i) :
    r.task ∈ (projectedReward (i + 1)).children k := by
  simp only [rewardRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl <;> simp [children]

/-- The unified constructor order pays the existing fourth-moment precision cost. -/
theorem scheduled_child_cost_le {k : ℕ} {parent child : CorrectionRowTask}
    (hchild : child ∈ parent.children k)
    {A a a' u u' : ℝ} (hA : 0 ≤ A) (M d c : ℕ) (hc : 0 < c) (h : ℤ)
    (ha : 0 < a) (ha' : 0 < a') (hu : 0 < u) (huu' : u ≤ u')
    (hscale : Real.logb 2 (a' / a) = (h : ℝ)) :
    Cslib.LogSpaceEstimation.binNormCost 4 (h : ℝ) *
        (2 : ℝ) ^ (Real.logb 2 (u' / u) / 4) *
        (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A
          (Cslib.LogSpaceEstimation.lastBudget M d c h) (child.rank k) a' u') ≤
      (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A M (parent.rank k) a u - A +
        (d : ℝ) / (16 * c) + 1 / 16) * Cslib.LogSpaceEstimation.scaleMajorant h :=
  Cslib.LogSpaceEstimation.scheduled_child_cost_le hA M d c (parent.rank k) (child.rank k) hc h
    (rank_lt_of_mem_children hchild) ha ha' hu huu' hscale

/-- Calls of the concrete copy/reward recipe pay for their inherited or reset source rate.
The broad detector and midpoint channels are at the stage rate, as in (7.5). -/
theorem reward_request_cost_le {Role Suffix : Type*}
    {source broadSource midpoint : Channel Role Suffix} {i k : ℕ} {r : Request Role Suffix}
    (hr : r ∈ rewardRequests source broadSource midpoint i)
    {f A : ℝ} (hbroad : broadSource.rate = f) (hmid : midpoint.rate = f)
    (hA : 0 ≤ A) (M d c : ℕ) (hc : 0 < c)
    (hf : 0 < f) (hu : 0 < source.rate) (huf : source.rate ≤ f) :
    Cslib.LogSpaceEstimation.binNormCost 4 0 *
        (2 : ℝ) ^ (Real.logb 2 (r.source.rate / source.rate) / 4) *
        (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A
          (Cslib.LogSpaceEstimation.lastBudget M d c 0) (r.task.rank k) f r.source.rate) ≤
      (2 : ℝ) ^ (-Cslib.LogSpaceEstimation.precision (16 * c) A M
        ((projectedReward (i + 1)).rank k) f source.rate - A +
        (d : ℝ) / (16 * c) + 1 / 16) * Cslib.LogSpaceEstimation.scaleMajorant 0 := by
  have hrates : source.rate ≤ r.source.rate := by
    simp only [rewardRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · simpa only [hbroad] using huf
    · exact le_rfl
    · exact le_rfl
    · simpa only [hmid] using huf
  simpa only [Int.cast_zero] using
    scheduled_child_cost_le (k := k) (rewardRequest_mem_children hr) hA M d c hc 0
      hf hf hu hrates (by simp [ne_of_gt hf])

/-- Pilot values keep their existing types; stochastic rows have two seed coordinates. -/
abbrev Value (m : ℕ) (V κ Γ Ζ : Type u) : CorrectionRowTask → Type _
  | .pilot t => PilotRowTask.Value V κ Γ Ζ t
  | .preparation _ | .normalized _ => Γ × Ζ → Matrix V V ℝ
  | .previousReward | .reward _ => V → ℝ
  | .weights => Fin (m + 1) → V → ℝ
  | .projectedReward _ => Lex (V × Fin (m + 1)) → ℝ
  | _ => Matrix V V ℝ

end CorrectionRowTask

namespace CorrectionSampling

variable {q cπ Cπ Cpair Cvar : ℝ} {P : HierarchyParams q cπ Cπ Cpair Cvar}
  {V κ Γ Ζ : Type u} {ι : Type*} [Fintype V] [Fintype ι] [Fintype κ] [Fintype Γ] [Fintype Ζ]
  {X : ι → V → Prop} {Y : κ → V → Prop}
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {Xs : Γ → V → Prop} {Z Zt : Ζ → V → Prop}
  [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
  {f : ℝ} {C : Matrix V V ℝ} {i : ℕ}
  (A : P.CorrectionSampling X Y Xs Z Zt f C i)

/-- All incoming scores are computed from the child raw input on this draw, before ranking. -/
@[expose] noncomputable def preparationRecipe (input : Matrix V V ℝ)
    (σ : Γ × Ζ) : Matrix V V ℝ :=
  CorrectionRowRecipe.preparation A.I A.τ A.h A.ρ A.K A.Kc f Xs Z input σ

/-- Normalization reads the raw child, preparatory child and final pilot vector. Ranks and
products are evaluated on child functions before the conditional average is taken. -/
@[expose] noncomputable def normalizedRecipe (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : Γ × Ζ) (x y : V) : ℝ :=
  CorrectionRowRecipe.normalized A.I A.τ A.ρ P.atomCutoff P.γ A.K A.Kc f Xs Z Zt
    input prep maximum σ x y

/-- Every estimated child table gives values in the same fixed range. The preparatory
child and final-pilot child are arbitrary functions; no error hypothesis is required. -/
theorem normalizedRecipe_mem_Icc (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V) :
    A.normalizedRecipe input prep maximum σ x y ∈ Set.Icc 0 (2 * P.Q P.atomCap) := by
  exact CorrectionRowRecipe.normalized_mem_Icc A.I A.τ A.ρ P.atomCutoff P.γ
    A.K A.Kc f Xs Z Zt (P.Q_nonneg _) P.atomCutoff_nonneg P.atomCutoff_le
    A.ρ_nonneg A.ρ_le_one A.τ_nonneg A.τ_le_one P.γ_nonneg P.γ_le_one
    input prep maximum σ x y

/-- Usage masking is retained for arbitrary child substitutions and fixed channel suffixes. -/
theorem normalizedRecipe_eq_zero_of_not_usage (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V)
    (hy : ¬ Zt σ.2 y) : A.normalizedRecipe input prep maximum σ x y = 0 := by
  simp only [normalizedRecipe, CorrectionRowRecipe.normalized, ite_eq_right hy]

/-- Clipping cannot introduce support at nonpositive raw estimates. -/
theorem normalizedRecipe_eq_zero_of_nonpos (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V)
    (hd : input x y / f ≤ 0) : A.normalizedRecipe input prep maximum σ x y = 0 := by
  simp only [normalizedRecipe, CorrectionRowRecipe.normalized, P.atomCutoff_eq_zero hd,
    zero_mul, zero_div, ite_self]

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

variable (W : V → ℝ)

/-- Actual values of every constructor, using the existing pilot and actual-correction semantics.
The primitive gates are fixed throughout this local family; their sampling contract is needed
only at the iteration for which a mean theorem is requested. -/
@[expose] noncomputable def value (W : V → ℝ) (t : CorrectionRowTask) : t.Value P.m V κ Γ Ζ :=
  match t with
  | .pilot t => PilotRowRecipe.value P X Y f C A.preparationRecipe A.normalizedRecipe t
  | .correction j => P.correctionIter X Y f C j
  | .input j => P.correctionInput X Y f C j
  | .preparation j => A.preparationRecipe (P.correctionInput X Y f C j)
  | .normalized j => A.normalizedRecipe (P.correctionInput X Y f C j)
      (A.preparationRecipe (P.correctionInput X Y f C j))
      (PilotTask.value P X Y f C (.maximum P.k))
  | .previousReward => W
  | .weights => P.weight X Y f C
  | .reward j => W + P.correctionIter X Y f C j *ᵥ W
  | .projectedReward j => fun a =>
      P.weight X Y f C (ofLex a).2 (ofLex a).1 *
        (W + P.correctionIter X Y f C j *ᵥ W) (ofLex a).1

/-- The embedded pilot uses the shared expanded evaluator. When the same primitive
recipes satisfy the pilot laws, all its values agree with the standalone pilot family.
Only recipe equality is required, never an assumed mean or error. -/
theorem value_pilot (B : P.PilotSampling X Y Xs Z Zt f C i)
    (hprep : A.preparationRecipe = B.preparationRecipe)
    (hnorm : A.normalizedRecipe = B.normalizedRecipe) (t : PilotRowTask) :
    A.value W (.pilot t) = B.value t := by
  simp only [value, PilotSampling.value, hprep, hnorm]

/-- The expanded pilot correction's normalized child remains a semantic dependency when
embedded in the actual family. Its mean follows from the pilot's own primitive channel laws. -/
theorem value_pilot_correction_mean (B : P.PilotSampling X Y Xs Z Zt f C i)
    (hprep : A.preparationRecipe = B.preparationRecipe)
    (hnorm : A.normalizedRecipe = B.normalizedRecipe)
    (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (y : V) :
    A.value W (.pilot (.pilot (.correction (i + 1)))) x y =
      𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
        (f / B.π) * A.value W (.pilot (.normalized i)) σ x y := by
  simp_rw [A.value_pilot W B hprep hnorm]
  exact B.value_correction_mean hf hC hC1 hCf hi hx y

/-- Actual raw-input calls, including evaluation of the right child at the midpoint. -/
theorem value_input (j : ℕ) : A.value W (.input j) =
    CorrectionRowRecipe.input (A.value W (.pilot (.pilot .base))) (A.value W (.correction j))
      (A.value W (.pilot (.pilot .base))) := rfl

/-- The incoming-score and gate assembly reads precisely the earlier raw-input child. -/
theorem value_preparation (j : ℕ) : A.value W (.preparation j) =
    A.preparationRecipe (A.value W (.input j)) := rfl

/-- The normalized row reads precisely its earlier input, preparation and final pilot children. -/
theorem value_normalized (j : ℕ) : A.value W (.normalized j) =
    A.normalizedRecipe (A.value W (.input j)) (A.value W (.preparation j))
      (A.value W (.pilot (.pilot (.maximum P.k)))) := rfl

/-- The actual recursive-task client uses the bounded recipe at every iteration. -/
theorem value_normalized_mem_Icc (j : ℕ) (σ : Γ × Ζ) (x y : V) :
    A.value W (.normalized j) σ x y ∈ Set.Icc 0 (2 * P.Q P.atomCap) :=
  A.normalizedRecipe_mem_Icc _ _ _ σ x y

/-- Actual correction values use the final pilot, independently of the current iteration. -/
theorem value_correction_succ (j : ℕ) (x y : V) :
    A.value W (.correction (j + 1)) x y =
      f * P.Q (A.value W (.input j) x y / f) *
        P.γ (A.value W (.pilot (.pilot (.maximum P.k))) y) := by
  change P.correctionIter X Y f C (j + 1) x y = _
  simp only [value, PilotRowRecipe.value, P.correctionIter_succ_apply, PilotTask.value_maximum_last]

/-- The copy weight is computed from the earlier expanded pilot maximum, on the
whole parent vertex domain. Primary and nonprimary symbols use the existing hierarchy API. -/
theorem value_weights : A.value W .weights =
    detectorWeight P.κ (A.value W (.pilot (.pilot (.maximum P.k)))) := by
  simp only [value, PilotRowRecipe.value, PilotTask.value_maximum_last]
  exact P.weight_eq X Y f C

/-- The reward constructor reads precisely the inherited reward and actual correction. -/
theorem value_reward (j : ℕ) (W : V → ℝ) : A.value W (.reward j) =
    A.value W .previousReward + A.value W (.correction j) *ᵥ A.value W .previousReward := rfl

/-- Projected task values are the existing weighted copy projection, not a second hierarchy. -/
theorem value_projectedReward [DecidableEq V] (j : ℕ) (W : V → ℝ) :
    A.value W (.projectedReward j) = P.proj X Y f C *ᵥ A.value W (.reward j) := by
  ext a
  exact (P.proj_mulVec X Y f C _ a).symm

/-- The actual (7.5) recipe substitutes whole earlier normalized-row, reward and copy-weight
functions. The right reward call is evaluated at the midpoint, with the same fixed channels. -/
@[expose] noncomputable def projectedRewardRecipe (W : V → ℝ)
    (σ : Γ × Ζ) (a : Lex (V × Fin (P.m + 1))) : ℝ :=
  A.value W .weights (ofLex a).2 (ofLex a).1 * A.value W .previousReward (ofLex a).1 +
    A.value W .weights (ofLex a).2 (ofLex a).1 * (f / A.π) *
      ∑ z, A.value W (.normalized i) σ (ofLex a).1 z * A.value W .previousReward z

/-- The raw recipe uses the actual base and previous actual correction, in matrix units. -/
theorem inputRecipe_eq_input :
    CorrectionRowRecipe.input (PilotTask.value P X Y f C .base) (P.correctionIter X Y f C i)
      (PilotTask.value P X Y f C .base) =
      P.correctionInput X Y f C i := rfl

/-- Preparatory values from true child functions are exactly the sampler's normalizer. -/
theorem normalizerRecipe_eq (x y : V) :
    CorrectionRowRecipe.normalizer Xs Zt (A.preparationRecipe (P.correctionInput X Y f C i)) x y =
      correctionNormalizer A.I A.τ A.K A.Kc f (P.correctionInput X Y f C i)
        Xs Z Zt A.h A.ρ x y := rfl

/-- On actual hierarchy inputs in the bounded iteration range, the complete local recipe
agrees with the existing uncapped true atom. The entry bound is derived, not assumed of a child. -/
theorem normalizedRecipe_eq_atom (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k) (σ : Γ × Ζ) (x y : V) :
    A.normalizedRecipe (P.correctionInput X Y f C i)
      (A.preparationRecipe (P.correctionInput X Y f C i))
      (PilotTask.value P X Y f C (.maximum P.k)) σ x y = A.atom σ x y := by
  have hb := P.correctionInput_bounds (X := X) (Y := Y) hf hC hC1 hCf i
  have hd0 : 0 ≤ P.correctionInput X Y f C i x y / f := div_nonneg (hb.1 x y) hf.le
  have hdk : P.correctionInput X Y f C i x y / f ≤ (P.k : ℝ) + 1 := by
    apply (div_le_iff₀ hf).mpr
    exact (hb.2.2 x y).trans (mul_le_mul_of_nonneg_right
      (by exact_mod_cast Nat.add_le_add_right hi 1) hf.le)
  rw [PilotTask.value_maximum_last]
  simp only [normalizedRecipe, CorrectionRowRecipe.normalized, atom, correctionAtom,
    P.atomCutoff_eq hd0 hdk]
  rfl

/-- True child substitution identifies the task recipe with the existing reward sample. -/
theorem projectedRewardRecipe_eq_rewardSample (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    (W : V → ℝ) (σ : Γ × Ζ) (a : Lex (V × Fin (P.m + 1))) :
    A.projectedRewardRecipe W σ a =
      A.rewardSample (P.weight X Y f C (ofLex a).2 (ofLex a).1) W σ (ofLex a).1 := by
  simp only [projectedRewardRecipe, value]
  simp_rw [A.normalizedRecipe_eq_atom hf hC hC1 hCf hi]
  rfl

/-- Primitive gate/channel laws identify the semantic value of the unified projected-reward
constructor. Every function in this recipe is a strictly earlier task in the same order.
This is a true-mean identity, not an error recurrence for substituted estimates. -/
theorem expect_projectedRewardRecipe (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    (W : V → ℝ) (a : Lex (V × Fin (P.m + 1)))
    (hx : ({s | Xs s (ofLex a).1} : Finset Γ).Nonempty) :
    (𝔼 σ ∈ ({s | Xs s (ofLex a).1} : Finset Γ) ×ˢ (univ : Finset Ζ),
      A.projectedRewardRecipe W σ a) = A.value W (.projectedReward (i + 1)) a := by
  simp_rw [A.projectedRewardRecipe_eq_rewardSample hf hC hC1 hCf hi]
  exact A.expect_rewardSample hf hC hC1 hx _ W

/-- At the final actual iteration, the task client is exactly the hierarchy's copy/reward
update. It reuses `correctionIter_last` and `proj`, preserving their mathematical values. -/
theorem expect_projectedRewardRecipe_last [DecidableEq V]
    (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ f) (hi : i + 1 = P.k)
    (W : V → ℝ) (a : Lex (V × Fin (P.m + 1)))
    (hx : ({s | Xs s (ofLex a).1} : Finset Γ).Nonempty) :
    (𝔼 σ ∈ ({s | Xs s (ofLex a).1} : Finset Γ) ×ˢ (univ : Finset Ζ),
      A.projectedRewardRecipe W σ a) =
      (P.proj X Y f C *ᵥ (W + P.correction X Y f C *ᵥ W)) a := by
  rw [A.expect_projectedRewardRecipe hf hC hC1 hCf (by omega) W a hx, hi,
    A.value_projectedReward]
  simp only [value, P.correctionIter_last]

/-- The second channel has precisely its preparatory conditional mean, with the usage mask
and external scale. In particular it has no broad/narrow importance ratio. -/
theorem secondChannel_eq (ζ : ℝ) (σ : Γ × Ζ) (x y : V) :
    CorrectionRowRecipe.secondChannel Xs Zt ζ
      (A.preparationRecipe (P.correctionInput X Y f C i)) σ x y =
    (if Zt σ.2 y then ζ * correctionNormalizer A.I A.τ A.K A.Kc f
      (P.correctionInput X Y f C i) Xs Z Zt A.h A.ρ x y else 0) := rfl

/-- Gate and channel laws, rather than a supplied mean, identify the normalized row's target. -/
theorem expect_normalizedRecipe (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (y : V) :
    (𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
      (f / A.π) * A.normalizedRecipe (P.correctionInput X Y f C i)
        (A.preparationRecipe (P.correctionInput X Y f C i))
        (PilotTask.value P X Y f C (.maximum P.k)) σ x y) =
      P.correctionIter X Y f C (i + 1) x y := by
  simp_rw [A.normalizedRecipe_eq_atom hf hC hC1 hCf hi]
  exact A.expect_atom hf hC hC1 hx y

/-- The actual correction constructor is the true mean of its earlier normalized child
in the unified order, with the exact usage density. -/
theorem value_correction_mean (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y)
    (hC1 : C *ᵥ 1 ≤ 1) (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    {x : V} (hx : ({s | Xs s x} : Finset Γ).Nonempty) (y : V) :
    A.value W (.correction (i + 1)) x y =
      𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ (univ : Finset Ζ),
        (f / A.π) * A.value W (.normalized i) σ x y :=
  (A.expect_normalizedRecipe hf hC hC1 hCf hi hx y).symm

end CorrectionSampling

namespace CorrectionRowTask

/-- A role/rate/suffix instantiation of the real reward recipe, with every listed call
strictly earlier. The broad source and midpoint roles supply the hierarchy's pilot channels;
the correction retains the inherited source and the right reward resets to the midpoint.
The sampler contains primitive channel/gate laws, not the asserted reward mean. -/
theorem expect_rewardRequests
    {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
    {V Ω : Type u} [Fintype V] [Fintype Ω] {Role Suffix : Type*}
    (channels : Role → ℝ → Suffix → Ω → V → Prop)
    [∀ role rate suffix s v, Decidable (channels role rate suffix s v)]
    (source broadSource midpoint : Channel Role Suffix) {f : ℝ} {C : Matrix V V ℝ} {i : ℕ}
    (hbroad : broadSource.rate = f) (hmid : midpoint.rate = f) (huf : source.rate ≤ f)
    (A : P.CorrectionSampling (broadSource.retains channels) (midpoint.retains channels)
      (source.retains channels) (midpoint.retains channels) (midpoint.retains channels) f C i)
    (hf : 0 < f) (hC : ∀ x y, 0 ≤ C x y) (hC1 : C *ᵥ 1 ≤ 1)
    (hCf : ∀ x y, C x y ≤ f) (hi : i ≤ P.k)
    (W : V → ℝ) (a : Lex (V × Fin (P.m + 1)))
    (hx : ({s | source.retains channels s (ofLex a).1} : Finset Ω).Nonempty) :
    (𝔼 σ ∈ ({s | source.retains channels s (ofLex a).1} : Finset Ω) ×ˢ
      (univ : Finset Ω), A.projectedRewardRecipe W σ a) =
        A.value W (.projectedReward (i + 1)) a ∧
      ∀ r ∈ rewardRequests source broadSource midpoint i,
        r.task.rank P.k < (projectedReward (i + 1)).rank P.k ∧
          source.rate ≤ r.source.rate := by
  refine ⟨A.expect_projectedRewardRecipe hf hC hC1 hCf hi W a hx, fun r hr =>
    ⟨rank_lt_of_mem_children (rewardRequest_mem_children hr), ?_⟩⟩
  simp only [rewardRequests, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · simpa only [hbroad] using huf
  · exact le_rfl
  · exact le_rfl
  · simpa only [hmid] using huf

end CorrectionRowTask
end Matrix.HierarchyParams

namespace Matrix

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)
  {V : ℕ → Type u} [∀ l, Fintype (V l)] [∀ l, LinearOrder (V l)]
  (e : ∀ l, V (l + 1) ≃ Lex (V l × Fin (P.m + 1)))
  {ι κ : ℕ → Type u} [∀ l, Fintype (ι l)] [∀ l, Fintype (κ l)]
  (X : ∀ l, ι l → V l → Prop) (Y : ∀ l, κ l → V l → Prop)
  [∀ l s v, Decidable (X l s v)] [∀ l t v, Decidable (Y l t v)]
  (S : Matrix (V 0) (V 0) ℝ)

/-- The unified local task recipe realizes the next reward of `DetectedHierarchy` itself.
The hierarchy invariant discharges true input bounds; no aggregate mean/error is assumed.
The previous reward is a leaf of the local order: assembling its cross-stage calls is separate. -/
theorem expect_hierarchyTaskReward {Γ Ζ : Type u} [Fintype Γ] [Fintype Ζ]
    (l i : ℕ) (Xs : Γ → V l → Prop) (Z Zt : Ζ → V l → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
    (A : P.CorrectionSampling (X l) (Y l) Xs Z Zt (q⁻¹ ^ l) (hierarchy P e X Y S l) i)
    (hi : i + 1 = P.k) (he : ∀ j a b, e j a < e j b → a < b)
    (hq : 0 < q) (hCπ : 0 < Cπ) (hS : S.IsStrictUpperTriangular)
    (hS0 : ∀ x y, 0 ≤ S x y) (hS1 : S *ᵥ 1 ≤ 1) {π : ℕ → ℝ}
    (hch : ∀ j < l, Cslib.Probability.RetentionChannels
      (X j) (Y j) (q⁻¹ ^ j) (π j) cπ Cπ Cpair Cvar)
    (e₀ : V 0 → ℝ) (a : V (l + 1))
    (hx : ({s | Xs s (ofLex (e l a)).1} : Finset Γ).Nonempty) :
    (𝔼 σ ∈ ({s | Xs s (ofLex (e l a)).1} : Finset Γ) ×ˢ (univ : Finset Ζ),
      A.projectedRewardRecipe
        (rewardTransport (hierarchyProj P e X Y S) (hierarchyCorrection P e X Y S) l *ᵥ e₀)
        σ (e l a)) =
      (rewardTransport (hierarchyProj P e X Y S) (hierarchyCorrection P e X Y S) (l + 1) *ᵥ
        e₀) a := by
  have hinv := hierarchy_invariant (P := P) (e := e) (X := X) (Y := Y)
    he hq hCπ hS hS0 hS1 l hch
  have hf : 0 < q⁻¹ ^ l := by positivity
  simp_rw [A.projectedRewardRecipe_eq_rewardSample hf hinv.2.1 hinv.2.2.1
    hinv.2.2.2 (by omega)]
  exact expect_hierarchyRewardSample P e X Y S l i Xs Z Zt A hi he hq hCπ hS hS0 hS1
    hch e₀ a hx

end Matrix
