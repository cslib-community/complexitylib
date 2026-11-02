/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.PilotTasks
public import Complexity.Foundations.Probability.HierarchySampling
public import Complexity.Foundations.Probability.HierarchyAtomCutoff

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
    CorrectionRowRecipe.input (A.value (.pilot .base)) (A.value (.correction j))
      (A.value (.pilot .base)) := rfl

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

end CorrectionSampling
end Matrix.HierarchyParams
