/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PilotTasks
public import Complexity.Foundations.Probability.HierarchySampling

/-!
# Preparatory and normalized actual-correction rows

This is the actual-correction family of [OpenAI2026LogSpace, Sections 5.3, 7.1–7.2], revision
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

This completes the local preparation/normalization recipe, not raw direct-bin recursion, the global
stage order, or the scheduled mean-prefix theorem. Primitive cutoffs retain the explicit contracts
of `CorrectionSampling`. Mean identities are exact finite identities, independent of the source's
eighth versus our fourth moments; no new real-valued rate schedule is asserted.

## Main definitions

* `Matrix.HierarchyParams.atomCap`, `Matrix.HierarchyParams.atomCutoff`: bounded source cutoff.
* `Matrix.HierarchyParams.CorrectionRowTask`: actual-correction constructor order.
* `Matrix.HierarchyParams.CorrectionSampling.preparationRecipe`: local incoming-gate assembly.
* `Matrix.HierarchyParams.CorrectionSampling.normalizedRecipe`: actual child-function recipe.

## Main results

* `Matrix.HierarchyParams.CorrectionRowTask.rank_lt_of_mem_children`: computed rank decrease.
* `Matrix.HierarchyParams.CorrectionSampling.normalizedRecipe_mem_Icc`: arbitrary-child range.
* `Matrix.HierarchyParams.CorrectionSampling.normalizedRecipe_eq_atom`: true-input agreement.
* `Matrix.HierarchyParams.CorrectionSampling.expect_normalizedRecipe`: channel-derived true mean.
-/

public section

universe u

open Finset
open scoped BigOperators

namespace Matrix.HierarchyParams

/-- Constructors at a fixed stage; the `pilot` leaf uses the existing deterministic pilot family. -/
inductive CorrectionRowTask where
  | pilot (t : PilotTask)
  | correction (i : ℕ)
  | input (i : ℕ)
  | preparation (i : ℕ)
  | normalized (i : ℕ)
  deriving DecidableEq

namespace CorrectionRowTask

/-- Actual inputs of a constructor. The final pilot is completed before actual corrections begin. -/
@[expose] def children (k : ℕ) : CorrectionRowTask → List CorrectionRowTask
  | .pilot t => t.children.map .pilot
  | .correction 0 => []
  | .correction (i + 1) => [.input i, .pilot (.maximum k)]
  | .input i => [.pilot .base, .correction i]
  | .preparation i => [.input i]
  | .normalized i => [.input i, .preparation i, .pilot (.maximum k)]

/-- Five slots per actual iteration, after the last pilot maximum. -/
@[expose] def rank (k : ℕ) : CorrectionRowTask → ℕ
  | .pilot t => t.rank
  | .correction i => 5 * k + 5 * i + 6
  | .input i => 5 * k + 5 * i + 7
  | .preparation i => 5 * k + 5 * i + 8
  | .normalized i => 5 * k + 5 * i + 9

/-- Every actual child is earlier, including preparation and the final pilot multiplier. -/
theorem rank_lt_of_mem_children {k : ℕ} {parent child : CorrectionRowTask}
    (h : child ∈ parent.children k) : child.rank k < parent.rank k := by
  cases parent with
  | pilot t =>
    obtain ⟨s, hs, rfl⟩ := List.mem_map.mp h
    exact PilotTask.rank_lt_of_mem_children hs
  | correction i =>
    cases i with
    | zero => simp [children] at h
    | succ i =>
      simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
      rcases h with rfl | rfl <;> simp only [rank, PilotTask.rank] <;> omega
  | input i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl <;> simp only [rank, PilotTask.rank] <;> omega
  | preparation i =>
    simp only [children, List.mem_singleton] at h
    subst child
    simp only [rank]
    omega
  | normalized i =>
    simp only [children, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> simp only [rank, PilotTask.rank] <;> omega

/-- Pilot values keep their existing types; stochastic rows have two seed coordinates. -/
abbrev Value (V κ Γ Ζ : Type u) : CorrectionRowTask → Type _
  | .pilot t => PilotTask.Value V κ t
  | .preparation _ | .normalized _ => Γ × Ζ → Matrix V V ℝ
  | _ => Matrix V V ℝ

end CorrectionRowTask

/-- Fixed source atom cap, strictly above the hierarchy input bound `k + 1` and `θ₂`.
This is `B_Q` of [OpenAI2026LogSpace, Section 5.3], not a cap on raw matrices. -/
@[expose] noncomputable def atomCap {q cπ Cπ Cpair Cvar : ℝ}
    (P : HierarchyParams q cπ Cπ Cpair Cvar) : ℝ :=
  max ((P.k : ℝ) + 1) P.θ₂ + 1

/-- The source's bounded scalar cutoff `Qat`. Ranks and incoming scores must continue to use
unclipped child entries [OpenAI2026LogSpace, Section 5.3, before (5.14)]. -/
@[expose] noncomputable def atomCutoff {q cπ Cπ Cpair Cvar : ℝ}
    (P : HierarchyParams q cπ Cπ Cpair Cvar) (d : ℝ) : ℝ :=
  P.Q (min P.atomCap (max 0 d))

variable {q cπ Cπ Cpair Cvar : ℝ} (P : HierarchyParams q cπ Cπ Cpair Cvar)

/-- The chosen atom cap exceeds both source lower bounds. -/
theorem atomCap_gt : max ((P.k : ℝ) + 1) P.θ₂ < P.atomCap := by
  unfold atomCap
  linarith

/-- The bounded extension is nonnegative for every real estimate. -/
theorem atomCutoff_nonneg (d : ℝ) : 0 ≤ P.atomCutoff d := P.Q_nonneg _

/-- Uniform bound on the scalar cutoff, independent of the child estimate. -/
theorem atomCutoff_le (d : ℝ) : P.atomCutoff d ≤ P.Q P.atomCap :=
  P.Q_mono (min_le_left _ _)

/-- The bounded extension agrees with the hierarchy cutoff on its nonnegative true range. -/
theorem atomCutoff_eq {d : ℝ} (hd : 0 ≤ d) (hdk : d ≤ (P.k : ℝ) + 1) :
    P.atomCutoff d = P.Q d := by
  have hcap : d ≤ P.atomCap := hdk.trans ((le_max_left _ _).trans P.atomCap_gt.le)
  simp only [atomCutoff, max_eq_right hd, min_eq_right hcap]

/-- Nonpositive estimates give zero, as required by the source extension. -/
theorem atomCutoff_eq_zero {d : ℝ} (hd : d ≤ 0) : P.atomCutoff d = 0 := by
  have hcap : 0 ≤ P.atomCap := by
    have hk : (0 : ℝ) ≤ P.k := Nat.cast_nonneg _
    have hm := le_max_left ((P.k : ℝ) + 1) P.θ₂
    have hg := P.atomCap_gt
    linarith
  have hQ : P.Q 0 = 0 := le_antisymm (by
    simpa only [zero_sub, max_eq_right (neg_nonpos.mpr P.θ_pos.le)] using P.Q_le 0)
    (P.Q_nonneg 0)
  simp only [atomCutoff, max_eq_left hd, min_eq_right hcap, hQ]

/-- The bounded extension does not introduce support absent from the original cutoff. -/
theorem atomCutoff_eq_zero_of_Q_eq_zero {d : ℝ} (hd : P.Q d = 0) :
    P.atomCutoff d = 0 := by
  by_cases hd0 : d ≤ 0
  · exact P.atomCutoff_eq_zero hd0
  · apply le_antisymm _ (P.atomCutoff_nonneg d)
    calc
      P.atomCutoff d ≤ P.Q d := P.Q_mono (by
        exact (min_le_right _ _).trans (by rw [max_eq_right (not_le.mp hd0).le]))
      _ = 0 := hd

namespace CorrectionSampling

variable {q cπ Cπ Cpair Cvar : ℝ} {P : HierarchyParams q cπ Cπ Cpair Cvar}
  {V κ Γ Ζ : Type u} {ι : Type*} [Fintype V] [Fintype ι] [Fintype κ] [Fintype Γ] [Fintype Ζ]
  {X : ι → V → Prop} {Y : κ → V → Prop}
  [∀ s v, Decidable (X s v)] [∀ t v, Decidable (Y t v)]
  {Xs : Γ → V → Prop} {Z Zt : Ζ → V → Prop}
  [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Z t v)] [∀ t v, Decidable (Zt t v)]
  {f : ℝ} {C : Matrix V V ℝ} {i : ℕ}
  (A : P.CorrectionSampling X Y Xs Z Zt f C i)

/-- Raw actual input recipe. The right child is a whole row function on the midpoint domain;
its source argument is the summation vertex, not the parent's old source. -/
@[expose] def inputRecipe (base correction : Matrix V V ℝ) : Matrix V V ℝ :=
  fun x y => base x y + ∑ z, correction x z * base z y

/-- All incoming scores are computed from the child raw input on this draw, before ranking. -/
@[expose] noncomputable def preparationRecipe (input : Matrix V V ℝ)
    (σ : Γ × Ζ) : Matrix V V ℝ :=
  correctionPrep A.I A.τ A.K A.Kc f input A.h A.ρ
    {w | Xs σ.1 w} {w | Z σ.2 w}

/-- The second raw channel calls the preparatory child on its own source/usage slice.
The optional external second-channel scale is applied after this mean. -/
@[expose] noncomputable def normalizerRecipe (Xs : Γ → V → Prop) (Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Zt t v)] (prep : Γ × Ζ → Matrix V V ℝ)
    (x y : V) : ℝ :=
  𝔼 σ ∈ ({s | Xs s x} : Finset Γ) ×ˢ ({t | Zt t y} : Finset Ζ), prep σ x y

/-- Scaled second raw channel on the narrower usage slice, extended by zero off that slice. -/
@[expose] noncomputable def secondChannelRecipe (Xs : Γ → V → Prop) (Zt : Ζ → V → Prop)
    [∀ s v, Decidable (Xs s v)] [∀ t v, Decidable (Zt t v)] (ζ : ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (σ : Γ × Ζ) (x y : V) : ℝ :=
  if Zt σ.2 y then ζ * normalizerRecipe Xs Zt prep x y else 0

/-- Normalization reads the raw child, preparatory child and final pilot vector. Ranks and
products are evaluated on child functions before the conditional average is taken. -/
@[expose] noncomputable def normalizedRecipe (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ)
    (σ : Γ × Ζ) (x y : V) : ℝ :=
  if Zt σ.2 y then
    P.atomCutoff (input x y / f) * (rowGate A.ρ A.K f input {w | Z σ.2 w} x *
      incomingGate A.I A.τ A.K A.Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y) /
      max (1 / 2) (min 1 (normalizerRecipe Xs Zt prep x y)) * P.γ (maximum y)
  else 0

/-- Every estimated child table gives values in the same fixed range. The preparatory
child and final-pilot child are arbitrary functions; no error hypothesis is required. -/
theorem normalizedRecipe_mem_Icc (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V) :
    A.normalizedRecipe input prep maximum σ x y ∈ Set.Icc 0 (2 * P.Q P.atomCap) := by
  have hQ0 := P.atomCutoff_nonneg (input x y / f)
  have hQ1 := P.atomCutoff_le (input x y / f)
  have hg0 : 0 ≤ rowGate A.ρ A.K f input {w | Z σ.2 w} x *
      incomingGate A.I A.τ A.K A.Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y :=
    mul_nonneg (A.ρ_nonneg _) (A.τ_nonneg _)
  have hg1 : rowGate A.ρ A.K f input {w | Z σ.2 w} x *
      incomingGate A.I A.τ A.K A.Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y ≤ 1 :=
    (mul_le_mul_of_nonneg_right (A.ρ_le_one _) (A.τ_nonneg _)).trans
      (by simpa only [one_mul] using A.τ_le_one _)
  have hc : (1 / 2 : ℝ) ≤ max (1 / 2)
      (min 1 (normalizerRecipe Xs Zt prep x y)) := le_max_left _ _
  have hc0 : 0 < max (1 / 2) (min 1 (normalizerRecipe Xs Zt prep x y)) := by linarith
  unfold normalizedRecipe
  split_ifs
  · have hn0 := div_nonneg (mul_nonneg hQ0 hg0) hc0.le
    have hn1 : P.atomCutoff (input x y / f) *
        (rowGate A.ρ A.K f input {w | Z σ.2 w} x *
          incomingGate A.I A.τ A.K A.Kc f input {w | Xs σ.1 w} {w | Z σ.2 w} y) /
        max (1 / 2) (min 1 (normalizerRecipe Xs Zt prep x y)) ≤ 2 * P.Q P.atomCap := by
      apply (div_le_iff₀ hc0).mpr
      calc
        _ ≤ P.atomCutoff (input x y / f) := mul_le_of_le_one_right hQ0 hg1
        _ ≤ P.Q P.atomCap := hQ1
        _ ≤ _ := by nlinarith [P.Q_nonneg P.atomCap]
    exact ⟨mul_nonneg hn0 (P.γ_nonneg _),
      (mul_le_of_le_one_right hn0 (P.γ_le_one _)).trans hn1⟩
  · exact ⟨le_rfl, mul_nonneg (by norm_num) (P.Q_nonneg _)⟩

/-- Usage masking is retained for arbitrary child substitutions and fixed channel suffixes. -/
theorem normalizedRecipe_eq_zero_of_not_usage (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V)
    (hy : ¬ Zt σ.2 y) : A.normalizedRecipe input prep maximum σ x y = 0 := by
  simp only [normalizedRecipe, ite_eq_right hy]

/-- Clipping cannot introduce support at nonpositive raw estimates. -/
theorem normalizedRecipe_eq_zero_of_nonpos (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x y : V)
    (hd : input x y / f ≤ 0) : A.normalizedRecipe input prep maximum σ x y = 0 := by
  simp only [normalizedRecipe, P.atomCutoff_eq_zero hd, zero_mul, zero_div, ite_self]

/-- Bounded estimated rows retain the original row-support guarantee. Preparation substitution
cannot create a nonzero entry when the cutoff or row gate vanishes. -/
theorem card_filter_normalizedRecipe_row_ne_zero_lt (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (x : V)
    (hK : 0 < A.K) {e g : ℝ} (he : 0 ≤ e)
    (hQ : ∀ d, d ≤ e → P.Q d = 0) (hg : g ≤ e)
    (hρ : ∀ r, g ≤ r → A.ρ r = 0) :
    #{y ∈ ({w | Z σ.2 w} : Finset V) |
      A.normalizedRecipe input prep maximum σ x y ≠ 0} < A.K := by
  refine lt_of_le_of_lt (card_le_card fun y hy => ?_)
    (card_filter_mul_rowGate_ne_zero_lt (G := input) (a := f) {w | Z σ.2 w} x hK he
      (fun d hd => P.atomCutoff_eq_zero_of_Q_eq_zero (hQ d hd)) hg hρ)
  rw [mem_filter] at hy ⊢
  refine ⟨hy.1, fun h0 => hy.2 ?_⟩
  unfold normalizedRecipe
  split_ifs
  · rw [← mul_assoc, h0, zero_mul, zero_div, zero_mul]
  · rfl

/-- The incoming support bound also survives arbitrary child substitutions. Scores and ranks
use the original raw table, and the cap cannot introduce new scalar support. -/
theorem card_filter_normalizedRecipe_col_ne_zero_lt (input : Matrix V V ℝ)
    (prep : Γ × Ζ → Matrix V V ℝ) (maximum : V → ℝ) (σ : Γ × Ζ) (y : V)
    (hKc : 0 < A.Kc) (hIQ : ∀ v r, P.Q v ≠ 0 → A.ρ r ≠ 0 → A.I v r = 1)
    {g : ℝ} (hg : g ≤ 1) (hτ : ∀ r, g ≤ r → A.τ r = 0) :
    #{x ∈ ({w | Xs σ.1 w} : Finset V) |
      A.normalizedRecipe input prep maximum σ x y ≠ 0} < A.Kc := by
  by_contra hle
  rw [not_lt] at hle
  have hgate : incomingGate A.I A.τ A.K A.Kc f input
      {w | Xs σ.1 w} {w | Z σ.2 w} y = 0 := by
    refine incomingGate_eq_zero hKc hg hτ (hle.trans (card_le_card fun x hx => ?_))
    rw [mem_filter] at hx ⊢
    refine ⟨hx.1, le_of_eq (hIQ _ _ (fun hQ => hx.2 ?_) (fun hρ => hx.2 ?_)).symm⟩
    · simp [normalizedRecipe, P.atomCutoff_eq_zero_of_Q_eq_zero hQ]
    · simp [normalizedRecipe, rowGate, hρ]
  obtain ⟨x, hx⟩ := card_pos.mp (hKc.trans_le hle)
  rw [mem_filter] at hx
  exact hx.2 (by simp [normalizedRecipe, hgate])

/-- Actual values of every constructor, using the existing pilot and actual-correction semantics.
The primitive gates are fixed throughout this local family; their sampling contract is needed
only at the iteration for which a mean theorem is requested. -/
@[expose] noncomputable def value : (t : CorrectionRowTask) → t.Value V κ Γ Ζ
  | .pilot t => PilotTask.value P X Y f C t
  | .correction j => P.correctionIter X Y f C j
  | .input j => P.correctionInput X Y f C j
  | .preparation j => A.preparationRecipe (P.correctionInput X Y f C j)
  | .normalized j => A.normalizedRecipe (P.correctionInput X Y f C j)
      (A.preparationRecipe (P.correctionInput X Y f C j))
      (PilotTask.value P X Y f C (.maximum P.k))

/-- Actual raw-input calls, including evaluation of the right child at the midpoint. -/
theorem value_input (j : ℕ) : A.value (.input j) =
    inputRecipe (A.value (.pilot .base)) (A.value (.correction j)) := rfl

/-- The incoming-score and gate assembly reads precisely the earlier raw-input child. -/
theorem value_preparation (j : ℕ) : A.value (.preparation j) =
    A.preparationRecipe (A.value (.input j)) := rfl

/-- The normalized row reads precisely its earlier input, preparation and final pilot children. -/
theorem value_normalized (j : ℕ) : A.value (.normalized j) =
    A.normalizedRecipe (A.value (.input j)) (A.value (.preparation j))
      (A.value (.pilot (.maximum P.k))) := rfl

/-- The actual recursive-task client uses the bounded recipe at every iteration. -/
theorem value_normalized_mem_Icc (j : ℕ) (σ : Γ × Ζ) (x y : V) :
    A.value (.normalized j) σ x y ∈ Set.Icc 0 (2 * P.Q P.atomCap) :=
  A.normalizedRecipe_mem_Icc _ _ _ σ x y

/-- Actual correction values use the final pilot, independently of the current iteration. -/
theorem value_correction_succ (j : ℕ) (x y : V) :
    A.value (.correction (j + 1)) x y =
      f * P.Q (A.value (.input j) x y / f) *
        P.γ (A.value (.pilot (.maximum P.k)) y) := by
  change P.correctionIter X Y f C (j + 1) x y = _
  simp only [value, P.correctionIter_succ_apply, PilotTask.value_maximum_last]

/-- The raw recipe uses the actual base and previous actual correction, in matrix units. -/
theorem inputRecipe_eq_input :
    inputRecipe (PilotTask.value P X Y f C .base) (P.correctionIter X Y f C i) =
      P.correctionInput X Y f C i := rfl

/-- Preparatory values from true child functions are exactly the sampler's normalizer. -/
theorem normalizerRecipe_eq (x y : V) :
    normalizerRecipe Xs Zt (A.preparationRecipe (P.correctionInput X Y f C i)) x y =
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
  simp only [normalizedRecipe, atom, correctionAtom, P.atomCutoff_eq hd0 hdk]
  rfl

/-- The second channel has precisely its preparatory conditional mean, with the usage mask
and external scale. In particular it has no broad/narrow importance ratio. -/
theorem secondChannel_eq (ζ : ℝ) (σ : Γ × Ζ) (x y : V) :
    secondChannelRecipe Xs Zt ζ
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

end CorrectionSampling
end Matrix.HierarchyParams
