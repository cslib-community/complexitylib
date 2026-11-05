/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyDetector
public import Complexity.Foundations.Probability.HierarchyDenseChildren
public import Complexity.Foundations.Probability.EstimatorSchedule
public import Complexity.Foundations.Probability.HierarchyEstimatedInput
public import Complexity.Foundations.Probability.NormalizedAtomRows.Request
import Complexity.Foundations.Probability.RootMetric.FiniteError

/-!
# Statistical-budget evaluation of existing hierarchy requests

The structural parameter `HP.k` is fixed. Rows and vectors share one history, and every
child retains the entire original H4 environment. `finiteInput` is the unaveraged finite
assembly helper. The public RAW route assembles paired endpoint differences before one
common completion per dyadic slack group, using `LogSpaceEstimation.lastBudget` at both budgets.
The negative residual is one signed ray, outside the positive-bin sum. Initial pilot and
actual inputs share the same zero-correction assembly; their request precisions and walks
retain their own constructor ranks.

This is a partial mathematical evaluator, not the closed compressed estimator of
[OpenAI2026LogSpace, Sections 7.4–7.5]. Dense leaves are unavailable at budget zero.
Every raw task has a literal zero sample at budget zero; canonical
coarse-error bounds beyond the initial pilot remain explicit obligations. Inactive recursive calls,
invalid frames and unsupported constructors also return `none`. The exact base matrix and
literal iteration-zero constants remain available.

Allocation magnitudes are derived from certified primitive cutoff caps and explicit finite
bin/rate/density charges, not supplied per request. They are proved sufficient for every initial
pilot paired sample and the assembled initial group, with actual completion noise. Their validity
for later constructions, noise summation, post-average compression,
incoming support, the simultaneous row/vector canonical-accuracy invariant and cross-stage/reward
transport remain open. In particular, no
row sparsity of a conditional average is inferred from pointwise input sparsity.

The shared-history organization is inspired by `current`, `rolls`, `forecast`, and
`error_estimate` in OpenAI's `HierarchicalEstimator.lean`, revision
`4eaee87548250b2682affda7d05d947c05554bae`. This is an original implementation over
Complexitylib's existing requests, not a port of those declarations.

## Main definitions

* `BudgetValue`: whole row and vector outputs on the same environment.
* `BudgetData.evaluate`: partial stage-zero statistical-budget evaluation.

## Main results

* `BudgetData.evaluate_eq`: public recursive constructor equation.
* `BudgetData.complete_grid`: exact request-to-H4-graph identification.
* `BudgetData.completion_noise`: range-based centered-noise allocation.
* `BudgetData.pairedSample_initial_completion`: actual scheduled initial-ray noise payment.
* `BudgetData.completedGroup_initial_rays`: literal common-walk group aggregation.
* `BudgetData.completedGroup_initial_grid`: derived assembled-group noise payment.
* `BudgetData.evaluate_normalized_bounds`: actual normalized range, usage and row support.
* `BudgetData.evaluate_maximum_succ`: actual inductive maximum error payment.
-/

public section
noncomputable section

open Finset Cslib Cslib.Probability
open scoped BigOperators

namespace Matrix.HierarchyParams.H4RankEnvironment

attribute [local instance] Classical.propDecidable

/-- Whole outputs on one unchanged environment. A vector is not a frozen row of a matrix. -/
inductive BudgetValue (P : ℕ) where
  | row (value : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
  | vector (value : Environment P 3 → ZMod P → ℝ)

namespace BudgetValue

/-- Type-checked row access; a vector cannot silently serve as a row. -/
@[expose] def row? {P : ℕ} : BudgetValue P → Option
    (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
  | .row A => some A
  | .vector _ => none

/-- Type-checked vector access. -/
@[expose] def vector? {P : ℕ} : BudgetValue P → Option
    (Environment P 3 → ZMod P → ℝ)
  | .row _ => none
  | .vector v => some v

end BudgetValue

/-- Finite stage-zero inputs and primitive cutoff bounds. Allocation amplitudes are
derived from these bounds and the literal rate/density coefficients. -/
structure BudgetData (HP : FourthRootHierarchyParams 16 1 16 32 8) (P : ℕ) where
  /-- Existing affine copy-padding radix. -/
  padding : ZMod P
  /-- Actual stage-zero input matrix. -/
  base : Matrix (ZMod P) (ZMod P) ℝ
  /-- The finite positive bins assembled by every RAW call. -/
  bins : Finset ℕ
  /-- Each bin's rank rate, retained separately from the endpoint usage rate. -/
  binRate : ℕ → ℝ
  /-- Actual bounded bin numerator cutoffs. -/
  cutoff : ℕ → ℝ → ℝ
  /-- Dense preparatory cutoffs corresponding to the bin numerators. -/
  auxiliary : ℕ → ℝ → ℝ
  /-- Positive integer coefficient of the existing scale-slack schedule. -/
  slack : ℕ
  /-- Strict budget decrease requires a positive slack coefficient. -/
  slack_pos : 0 < slack
  /-- Structural-rank charge in the existing precision formula. -/
  rankCharge : ℝ
  /-- Uniform finite cap for the supplied bin numerators. -/
  binCap : ℝ
  /-- Primitive cap sign, fixed before recursive calls. -/
  binCap_nonneg : 0 ≤ binCap
  /-- Primitive numerator range, independent of recursive output accuracy. -/
  cutoff_bounds : ∀ i d, cutoff i d ∈ Set.Icc 0 binCap

namespace BudgetData

variable {HP : FourthRootHierarchyParams 16 1 16 32 8} {P : ℕ} [Fact P.Prime]
  (B : BudgetData HP P)

/-- Precision uses the existing structural rank and actual endpoint/source rates. -/
@[expose] def requestPrecision (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℝ :=
  LogSpaceEstimation.precision (16 * B.slack) B.rankCharge M r.task.rank
    r.terminal.rate r.source.rate

/-- The common next budget is the actual zero-scale slack schedule. -/
@[expose] def childBudget (M : ℕ) : ℕ :=
  LogSpaceEstimation.lastBudget M 1 B.slack 0

omit [Fact P.Prime] in
/-- Decrease is supplied by the schedule, rather than a separate rank certificate. -/
theorem childBudget_lt {M : ℕ} (hM : 0 < M) : B.childBudget M < M :=
  LogSpaceEstimation.lastBudget_lt hM B.slack_pos

/-- Each bin reserves its own logarithmic scale slack. -/
@[expose] def binBudget (M i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℕ :=
  LogSpaceEstimation.lastBudget M 1 B.slack
    ⌊Real.logb 2 (B.binRate i / r.terminal.rate)⌋

omit [Fact P.Prime] in
/-- Both coarse and fine bin requests are strictly below the parent budget. -/
theorem binBudget_lt {M : ℕ} (hM : 0 < M) (i : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : B.binBudget M i r < M :=
  LogSpaceEstimation.lastBudget_lt hM B.slack_pos

/-- The unused role among three distinct source and terminal coordinates. -/
@[expose] def midpointRole (s t : Fin 3) : Fin 3 :=
  if s ≠ 0 ∧ t ≠ 0 then 0 else if s ≠ 1 ∧ t ≠ 1 then 1 else 2

omit [Fact P.Prime] in
/-- The concrete three-role endpoint always has a distinct midpoint coordinate. -/
theorem midpointRole_distinct (s t : Fin 3) :
    s ≠ midpointRole s t ∧ midpointRole s t ≠ t := by
  fin_cases s <;> fin_cases t <;> decide

/-- A request's third role, with the terminal stage rate and no inherited copy suffix.
Source and terminal suffixes themselves remain in their respective child requests. -/
@[expose] def midpoint (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    CorrectionRowTask.Channel (Fin 3) (List (ZMod P)) :=
  ⟨midpointRole r.source.role r.terminal.role, r.terminal.rate, []⟩

/-- The normalized correction amplitude supplied by the hierarchy cutoffs. -/
@[expose] def atomCap (_B : BudgetData HP P) : ℝ := 2 * HP.Q HP.toHierarchyParams.atomCap

/-- Literal finite-bin envelope at an endpoint. No unknown recursive value occurs.
The conservative product charge uses the finite vertex width. -/
@[expose] def positiveCharge
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : ℕ) (y : ZMod P) : ℝ :=
  let R := HierarchyTask.rawRequests 0 i (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r)
    r.terminal (B.binRate i)
  |B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y| *
      (2 * B.binCap) +
    |B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal R.right y *
      (r.terminal.rate /
        (dens {τ | R.right.source.retains (channels B.padding) τ y} : ℝ))| *
      ((P : ℝ) * B.atomCap * (2 * B.binCap))

/-- Finite positive-bin allocation amplitude. It sums endpoint charges, rather than
transporting moments by the cardinality of the environment or its smallest atom. -/
@[expose] def positiveMagnitude
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : ℕ) : ℝ :=
  ∑ y, B.positiveCharge r i y

/-- The once-negative residual amplitude on its own rank and usage channels. -/
@[expose] def negativeMagnitude
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℝ :=
  let request : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
    ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
      r.terminal, { r.terminal with rate := min r.terminal.rate r.terminal.rate }⟩
  ∑ y, |r.terminal.rate *
    HierarchyTask.usageRatio (channels B.padding) r.terminal request y| * B.atomCap

/-- Derived common walk amplitude. Paired differences cost twice the ray amplitude;
preparation and normalized completion are covered by the first two summands. -/
@[expose] def magnitude (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℝ :=
  1 + B.atomCap + 2 * ((∑ i ∈ B.bins, B.positiveMagnitude r i) + B.negativeMagnitude r)

/-- Every displayed rate charge is nonnegative, even at an empty frame slice. -/
theorem positiveCharge_nonneg
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (i : ℕ) (y : ZMod P) :
    0 ≤ B.positiveCharge r i y := by
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hcap := B.binCap_nonneg
  unfold positiveCharge atomCap
  exact add_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (by norm_num) B.binCap_nonneg))
    (mul_nonneg (abs_nonneg _) (by positivity))

/-- The existing derived allocation covers bounded preparation inputs without a new budget. -/
theorem one_le_magnitude (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    1 ≤ B.magnitude r := by
  have hp : 0 ≤ ∑ i ∈ B.bins, B.positiveMagnitude r i := by
    apply sum_nonneg
    intro i _
    exact sum_nonneg fun y _ => B.positiveCharge_nonneg r i y
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hn : 0 ≤ B.negativeMagnitude r := by
    unfold negativeMagnitude atomCap
    exact sum_nonneg fun y _ => mul_nonneg (abs_nonneg _) (by positivity)
  have hcap : 0 ≤ B.atomCap := by unfold atomCap; positivity
  change 1 ≤ 1 + B.atomCap + 2 * _
  linarith

/-- The derived allocation is positive without a supplied per-request magnitude. -/
theorem magnitude_pos (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    0 < B.magnitude r := lt_of_lt_of_le zero_lt_one (B.one_le_magnitude r)

/-- Positive lengths are chosen from the derived finite rate/cutoff envelope before
the lower calls. Task-specific validity and noise summation remain proof obligations. -/
@[expose] def steps (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (slack : ℕ := 0) : ℕ :=
  max 1 (spectralWalkLength (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4))
    (32 * ((P : ℝ)^2 / (P * r.source.rate) * B.magnitude r ^ 4))
    ((2 : ℝ) ^ (-B.requestPrecision M r)) slack)

/-- The mathematical allocator never selects the zero-length walk. -/
theorem steps_pos (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (slack : ℕ := 0) :
    0 < B.steps M r slack := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

/-- Full-coordinate completion with explicit natural frame sides. Encapsulating the
dependent graph here keeps request-rate rewrites outside its subtype and instance arguments. -/
@[expose] def completeAt (s t : Fin 3) (Ls Lu : ℕ) (ss su : List (ZMod P))
    (steps : ℕ) (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :=
  if h : s ≠ t ∧ 0 < Ls ∧ Ls ≤ P ∧ 0 < Lu ∧ Lu ≤ P then
    letI : NeZero Ls := ⟨Nat.ne_of_gt h.2.1⟩
    letI : NeZero Lu := ⟨Nat.ne_of_gt h.2.2.2.1⟩
    some (conditionalWalk
      (X s Ls (CopyPadding.identifier B.padding ss))
      (Y t Lu (CopyPadding.identifier B.padding su))
      (graph s t h.1 Ls Lu h.2.2.1 h.2.2.2.2
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => steps) A)
  else none

/-- Complete on the actual full-coordinate source/usage graph. Invalid frame sides are
reported as unavailable, rather than clipped to a different channel. -/
@[expose] def complete (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (slack : ℕ := 0) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :=
  B.completeAt r.source.role r.usage.role
    (semanticSide P r.source.rate) (semanticSide P r.usage.rate)
    r.source.suffix r.usage.suffix (B.steps M r slack) A

/-- Grid requests use exactly the original H4 retained-pair graph, with the source
and usage suffixes intact. The frame guard cannot reject a grid call on distinct roles. -/
theorem complete_grid (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) (slack : ℕ := 0) :
    B.complete M r A slack = some (conditionalWalk
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ku) (CopyPadding.identifier B.padding su))
      (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r slack) A) := by
  unfold complete
  rw [hs, hu]
  simp only [gridChannel, semanticSide_grid]
  unfold completeAt
  rw [dite_eq_left ⟨hst, side_pos P ks (Fact.out : P.Prime).pos,
    side_le P ks, side_pos P ku (Fact.out : P.Prime).pos, side_le P ku⟩]
  rfl

/-- A uniform magnitude pays actual full-coordinate completion noise with group slack.
This is centered noise against the computed child's literal slice mean, not accuracy
against a supplied desired mean or a canonical hierarchy target. -/
theorem completion_noise (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hu : 0 < r.source.rate)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : ∀ σ x y, |A σ x y| ≤ B.magnitude r) (slack : ℕ := 0) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    rowNormPow 4 P r.source.rate Xs Yu (fun σ x y =>
      conditionalWalk Xs Yu
        (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
          (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
        (fun _ _ => B.steps M r slack) A σ x y - rowSliceMean Xs Yu A x y) ≤
      (((2 : ℝ) ^ (-B.requestPrecision M r)) * (64 : ℝ)⁻¹ ^ slack) ^ 4 := by
  intro Xs Yu
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hu.le
  have hbound := rowNormPow_fourth_le_expect_envelope hNu Xs Yu A
    (fun _ => B.magnitude r ^ 4) (fun _ => by positivity)
    (fun σ x y _ _ => pow_le_pow_left₀ (abs_nonneg _) (hA σ x y) 4)
  simp only [ZMod.card, Fintype.expect_const] at hbound
  have hr : 0 < 1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4) := by norm_num
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (show 0 ≤ 32 * ((P : ℝ)^2 / (P * r.source.rate) * B.magnitude r ^ 4) by positivity)
    (Real.rpow_pos_of_pos (by norm_num) _) slack (B.steps M r slack)
    (Nat.le_max_right _ _)
  have hn := noise s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
    hNu (B.steps M r slack) A
  exact hn.trans ((mul_le_mul_of_nonneg_left hbound (by positivity)).trans
    (by nlinarith only [hp]))

/-- Look up a completed row without coercing a vector answer. -/
@[expose] def row (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
    Option (BudgetValue P))
    (m : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) := (history m r).bind BudgetValue.row?

/-- Look up a completed vector without coercing a row answer. -/
@[expose] def vector (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
    Option (BudgetValue P))
    (m : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :=
  (history m r).bind BudgetValue.vector?

/-- One finite positive bin calls its three actual whole-function requests at the
supplied exact budget. Direct and right requests keep distinct source tuples. -/
@[expose] def positiveSample (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
    Option (BudgetValue P))
    (m i : ℕ) (t : HierarchyTask.RawTask HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let R := HierarchyTask.rawRequests 0 i t r.source (midpoint r) r.terminal (B.binRate i)
  let direct ← row history m R.direct
  let left ← row history m R.left
  let right ← row history m R.right
  pure fun σ x y =>
    B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y *
      direct σ x y +
    B.binRate i * HierarchyTask.usageRatio (channels B.padding) r.terminal R.right y *
      ((midpoint r).rate /
        (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ)) *
      ∑ z, left σ x z * right σ z y

/-- Unaveraged finite positive bins, followed by the residual's single negative request.
No negative term is placed inside the bin sum. -/
@[expose] def finiteInput (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
    Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let positives ← B.bins.toList.mapM fun i => B.positiveSample history (B.binBudget M i r) i t r
  let negative ← match t with
    | .pilotInput _ | .input _ => pure (0 : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    | .residual => do
      let request : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
        ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
          { r.terminal with rate := (midpoint r).rate },
          { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩
      let A ← row history (B.childBudget M) request
      pure fun σ x y => (midpoint r).rate *
        HierarchyTask.usageRatio (channels B.padding) r.terminal request y * A σ x y
  pure fun σ x y => (positives.map (fun A => A σ x y)).sum - negative σ x y

/-- The scale of a positive contribution, or of the single residual correction.
The latter is a separate ray; it is never repeated inside the positive-bin sum. -/
@[expose] def sampleScale (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (bin : Option ℕ) : ℤ :=
  ⌊Real.logb 2 ((bin.map B.binRate |>.getD (midpoint r).rate) / r.terminal.rate)⌋

/-- One unaveraged contribution at an exact statistical budget. Budget zero is the
literal zero approximation for every raw task, before any child call. This boundary does
not assert canonical accuracy; `initialSample_zero_error` records the initial coarse error. -/
@[expose] def sample
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Option (BudgetValue P))
    (m : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :=
  if m = 0 then some 0 else
    match bin with
    | some i => B.positiveSample history m i t r
    | none => match t with
      | .pilotInput _ | .input _ => some 0
      | .residual => do
        let request : HierarchyTask.Request HP.k (Fin 3) (ZMod P) :=
          ⟨HierarchyTask.correctionAtomTask 0 false (Fin.last HP.k), r.source,
            { r.terminal with rate := (midpoint r).rate },
            { r.terminal with rate := min r.terminal.rate (midpoint r).rate }⟩
        let A ← row history m request
        pure fun σ x y => -(midpoint r).rate *
          HierarchyTask.usageRatio (channels B.padding) r.terminal request y * A σ x y

/-- A dyadic slack group's two endpoint samples, on the same whole environment.
Both calls use their actual (possibly unequal) last budgets. Empty groups make no calls. -/
@[expose] def pairedSample
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :=
  let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)
  let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)
  if fine = coarse then some 0 else do
    let A ← B.sample history fine t r bin
    let C ← B.sample history coarse t r bin
    pure (A - C)

omit [Fact P.Prime] in
/-- Every nonempty paired group calls only earlier statistical budgets, independently
of structural HP.k and of the activity of either child. -/
theorem pairedSample_budgets_lt (M d : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ) :
    LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin) < M ∧
    LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin) < M :=
  ⟨LogSpaceEstimation.lastBudget_lt hM B.slack_pos,
    LogSpaceEstimation.lastBudget_lt hM B.slack_pos⟩

/-- Positive rays and the residual's one negative ray, in their assembly order. -/
@[expose] def rays (t : HierarchyTask.RawTask HP.k) : List (Option ℕ) :=
  B.bins.toList.map some ++ (match t with | .residual => [none] | _ => [])

/-- Assemble the actual paired children before the common group walk. Empty ray lists
retain their literal zero without introducing a frame-availability obligation. -/
@[expose] def completedGroup
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :=
  if (B.rays t).isEmpty then some 0 else do
    let inputs ← (B.rays t).mapM (B.pairedSample history M d t r)
    B.complete M r (fun σ x y => (inputs.map (fun A => A σ x y)).sum) d

/-- Scheduled RAW completes each assembled paired group once. All its rays share the
actual source/usage graph and length. Unsupported positive-budget children still propagate
`none`; the single residual negative ray remains outside the positive-bin list. -/
@[expose] def raw
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let groups ← (List.range (Nat.log2 M + 1)).mapM fun j =>
    B.completedGroup history M (Cslib.RowCompression.dyadicSlack (Nat.log2 M + 1) j) t r
  pure fun σ x y => (groups.map (fun A => A σ x y)).sum

set_option backward.isDefEq.respectTransparency false in
/-- One assembled group walk equals the sum of the literal completed rays, on a common
grid request. No independence, support, or canonical-error hypothesis is used. -/
theorem complete_grid_list_sum (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (inputs : List (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)) (d : ℕ) :
    B.complete M r (fun σ x y => (inputs.map (fun A => A σ x y)).sum) d =
      some (fun σ x y => (inputs.map (fun A => conditionalWalk
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ku) (CopyPadding.identifier B.padding su))
        (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
          (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
        (fun _ _ => B.steps M r d) A σ x y)).sum) := by
  rw [B.complete_grid M r s t hst ks ku ss su hs hu _ d]
  congr 1
  funext σ x y
  exact conditionalWalk_list_sum _ _ _ _ inputs σ x y

/-- Paired endpoint subtraction is exactly the existing schedule's telescoped group.
The equality retains both budgets and the zero boundary. It uses no independence. -/
theorem pairedSample_eq_group
    (T : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) → Option (BudgetValue P))
    (M d : ℕ) (t : HierarchyTask.RawTask HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : Option ℕ)
    (hf : B.sample history
      (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) t r bin =
      some (T (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin))))
    (hc : B.sample history
      (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) t r bin =
      some (T (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)))) :
    B.pairedSample history M d t r bin = some (fun σ x y =>
      ∑ m ∈ LogSpaceEstimation.slackGroup M d B.slack (B.sampleScale r bin),
        (T (m + 1) σ x y - T m σ x y)) := by
  have htel : (fun σ x y =>
      ∑ m ∈ LogSpaceEstimation.slackGroup M d B.slack (B.sampleScale r bin),
        (T (m + 1) σ x y - T m σ x y)) =
      T (LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r bin)) -
        T (LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r bin)) := by
    funext σ x y
    exact LogSpaceEstimation.sum_slackGroup_differences (fun m => T m σ x y) _ _ _ _
  rw [htel]
  unfold pairedSample
  dsimp only
  split_ifs with heq
  · rw [heq]
    simp only [sub_self]
    rfl
  · rw [hf, hc]
    rfl

/-- Shared normalized row assembly after three genuine lower-budget calls. -/
@[expose] def normalized
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (pilot : Bool) (i : Fin HP.k) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let A ← row history (B.childBudget M)
    { r with task := .row 0 (if pilot then .pilotInput i else .input i) }
  let prep ← row history (B.childBudget M)
    { r with task := .row 0 (if pilot then .pilotPreparation i else .preparation i) }
  let maximum ← vector history (B.childBudget M)
    { r with task := .row 0 (.maximum (if pilot then i.succ else Fin.last HP.k)) }
  pure (correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ)
    HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
    ⌈4 * (1 + 32 * HP.R)⌉₊ A prep maximum)

/-- A single constructor step. Exact base and literal iteration-zero constants are
available at every budget; dense leaves require positive budget.
Nonconstant inactive calls remain explicitly
unavailable pending their analytic zero-approximation theorem. -/
@[expose] def step (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
    Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (BudgetValue P) :=
  match r.task with
  | .row 0 .base => some (.row (fun _ => B.base))
  | .row 0 (.pilotCorrection i) | .row 0 (.correction i) =>
    if hi : i.val = 0 then some (.row 0)
    else if 0 < B.requestPrecision M r then do
      let j : Fin HP.k := ⟨i.val - 1, by omega⟩
      let task := match r.task with
        | .row _ (.pilotCorrection _) => HierarchyTask.row 0 (.pilotNormalized j)
        | _ => HierarchyTask.row 0 (.normalized j)
      let A ← row history (B.childBudget M) { r with task := task }
      let A ← B.complete M r A
      pure (.row (fun σ x y => r.terminal.rate * A σ x y))
    else none
  | .row 0 (.maximum i) =>
    if hi : i.val = 0 then some (.vector 0)
    else if 0 < B.requestPrecision M r then do
      let j : Fin HP.k := ⟨i.val - 1, by omega⟩
      let previous ← vector history (B.childBudget M)
        { r with task := .row 0 (.maximum j.castSucc) }
      let detector ← vector history (B.childBudget M) { r with task := .row 0 (.detector j) }
      pure (.vector (fun σ => PilotRowRecipe.maximum (previous σ) (detector σ)))
    else none
  | .basePreparation 0 i => if 0 < M then some (.row
      (densePreparation B.padding id r (B.auxiliary i) HP.ρ HP.K B.base)) else none
  | .baseNormalized 0 i => if 0 < M then some (.row
      (denseChild B.padding id r (B.cutoff i) (B.auxiliary i) HP.ρ HP.K B.base)) else none
  | .row 0 (.pilotInput i) | .row 0 (.input i) =>
    -- Both initial targets are C + 0*C. Reuse the proved initial history rather than
    -- duplicating a route through the equal literal-zero actual correction.
    if i.val = 0 then
      if 0 < B.requestPrecision M r then (B.raw history M (.pilotInput i) r).map .row else none
    else if 0 < B.requestPrecision M r then
      let t := match r.task with
        | .row _ (.pilotInput _) => HierarchyTask.RawTask.pilotInput i
        | _ => .input i
      (B.raw history M t r).map .row
    else none
  | .residual 0 =>
    if 0 < B.requestPrecision M r then (B.raw history M .residual r).map .row else none
  | .row 0 (.score i) => if 0 < B.requestPrecision M r then do
      let A ← row history (B.childBudget M) { r with task := .row 0 (.pilotInput i) }
      pure (.row (fun σ => PilotRowRecipe.score HP.toHierarchyParams
        (fun τ y => r.terminal.retains (channels B.padding) τ y) r.terminal.rate (A σ) σ))
    else none
  | .row 0 (.detector i) => if hr : Admissible r then
      if 0 < B.requestPrecision M r then do
        let A ← row history (B.childBudget M)
          { r with task := .row 0 (.score i), source := { r.source with rate := r.terminal.rate } }
        pure (.vector (fun _ => environmentDetector HP B.padding id r hr A))
      else none
    else none
  | .row 0 (.pilotPreparation i) | .row 0 (.preparation i) =>
    if 0 < B.requestPrecision M r then do
      let task := match r.task with
        | .row _ (.pilotPreparation _) => HierarchyTask.row 0 (.pilotInput i)
        | _ => HierarchyTask.row 0 (.input i)
      let A ← row history (B.childBudget M) { r with task := task }
      let prep := fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
        ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate (A σ) (polynomialPrepCutoff4 HP.θ) HP.ρ
        {x | r.source.retains (channels B.padding) σ x}
        {y | r.terminal.retains (channels B.padding) σ y}
      (B.complete M r prep).map .row
    else none
  | .row 0 (.pilotNormalized i) =>
    if 0 < B.requestPrecision M r then (B.normalized history M r true i).map .row else none
  | .row 0 (.normalized i) =>
    if 0 < B.requestPrecision M r then (B.normalized history M r false i).map .row else none
  | _ => none

/-- One recursive evaluator for both value shapes. Out-of-budget history access fails
explicitly; implemented scheduled calls satisfy the strict inequalities above. -/
def evaluate (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (BudgetValue P) :=
  B.step (fun m r => if _h : m < M then evaluate m r else none) M r
termination_by M

/-- Public constructor equation for the budget recursion. Clients need not unfold
the private unary function generated by well-founded recursion. -/
theorem evaluate_eq (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.evaluate M r = B.step
      (fun m r => if m < M then B.evaluate m r else none) M r := by
  rw [evaluate]
  apply congrArg (fun history => B.step history M r)
  funext m r
  split_ifs <;> rfl

/-- Original stage-zero base access is exact at every budget. -/
theorem evaluate_base (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 .base) :
    B.evaluate M r = some (.row (fun _ => B.base)) := by
  rw [evaluate, step, hr]
  rfl

/-- Dense leaves evaluate their genuine normalized row at positive statistical budgets. -/
theorem evaluate_dense (M i : ℕ) (hM : 0 < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .baseNormalized 0 i) :
    B.evaluate M r = some (.row
      (denseChild B.padding id r (B.cutoff i) (B.auxiliary i) HP.ρ HP.K B.base)) := by
  rw [evaluate, step, hr]
  simp only [hM, ↓reduceIte]

/-- The public dense evaluator consumes the supplied bin numerator and its corresponding
preparation. Its target is a dense normalized bin, with full terminal rank and the actual
source/usage conditional mean; it is not the fixed-HP atom decoder or a correction request. -/
theorem evaluate_dense_eq_output (M i : ℕ) (hM : 0 < M)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .baseNormalized 0 i) (ha : Admissible r)
    {ζ : ℝ} (hζ : 0 < ζ) :
    B.evaluate M r = some (.row (fun σ x y =>
      if r.usage.retains (channels B.padding) σ y then
        FourthRootHierarchyParams.NormalizedRow.output (B.cutoff i) HP.ρ ζ
          (requestSignals ζ B.padding id r (fun _ => B.base)
            (densePreparation B.padding id r (B.auxiliary i) HP.ρ HP.K B.base) σ x y 0)
          (requestSignals ζ B.padding id r (fun _ => B.base)
            (densePreparation B.padding id r (B.auxiliary i) HP.ρ HP.K B.base) σ x y 1)
          (Cslib.RowCompression.firstRank
            {z | r.terminal.retains (channels B.padding) σ z} HP.K 0
            (requestSignals ζ B.padding id r (fun _ => B.base)
              (densePreparation B.padding id r (B.auxiliary i) HP.ρ HP.K B.base) σ x))
      else 0)) := by
  rw [B.evaluate_dense M i hM r hr]
  congr 2
  funext σ x y
  exact normalizedRequest_eq_output (B.cutoff i) HP.ρ HP.K hζ B.padding id r ha
    (fun _ => B.base) (densePreparation B.padding id r (B.auxiliary i) HP.ρ HP.K B.base) σ x y

/-- The pilot's literal zero correction is available even at budget zero. -/
theorem evaluate_pilotCorrection_zero (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (.pilotCorrection 0)) :
    B.evaluate M r = some (.row 0) := by
  rw [evaluate, step, hr]
  rfl

/-- The actual correction has the same literal zero base. -/
theorem evaluate_correction_zero (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (.correction 0)) :
    B.evaluate M r = some (.row 0) := by
  rw [evaluate, step, hr]
  rfl

/-- The running maximum's base is a vector zero, not a row zero. -/
theorem evaluate_maximum_zero (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (.maximum 0)) :
    B.evaluate M r = some (.vector 0) := by
  rw [evaluate, step, hr]
  rfl

/-- The actual zero-correction positive-bin sample on the full original environment. -/
@[expose] def initialSample (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (bin : ℕ) : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  let R := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  fun σ x y => B.binRate bin *
    HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y *
    denseChild B.padding id R.direct (B.cutoff bin) (B.auxiliary bin)
      HP.ρ HP.K B.base σ x y

/-- Derived bound for the actual assembled initial sample, including all importance
ratios. In particular this certifies its budget-zero coarse approximation. -/
theorem initialSample_abs_le
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : ℕ)
    (σ : Environment P 3) (x y : ZMod P) :
    |B.initialSample r bin σ x y| ≤ B.positiveMagnitude r bin := by
  let R := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
    r.source (midpoint r) r.terminal (B.binRate bin)
  have hd := normalizedRequest_mem_Icc HP B.padding R.direct (B.cutoff bin)
    B.binCap_nonneg (B.cutoff_bounds bin) (fun _ => B.base)
    (densePreparation B.padding id R.direct (B.auxiliary bin) HP.ρ HP.K B.base) σ x y
  have hdabs : |denseChild B.padding id R.direct (B.cutoff bin) (B.auxiliary bin)
      HP.ρ HP.K B.base σ x y| ≤ 2 * B.binCap :=
    abs_le.mpr ⟨by change -(2 * B.binCap) ≤ normalizedRequest _ _ _ _ _ _ _ _ _ _ _
                   linarith [hd.1, B.binCap_nonneg], hd.2⟩
  have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
  have hcap := B.binCap_nonneg
  calc
    |B.initialSample r bin σ x y| ≤
        |B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y| *
          (2 * B.binCap) := by
      change |(_ : ℝ) * denseChild _ _ _ _ _ _ _ _ _ _ _| ≤ _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left hdabs (abs_nonneg _)
    _ ≤ B.positiveCharge r bin y := by
      unfold positiveCharge atomCap
      exact le_add_of_nonneg_right (by positivity)
    _ ≤ B.positiveMagnitude r bin :=
      single_le_sum (fun z _ => B.positiveCharge_nonneg r bin z) (mem_univ y)

/-- Zero-budget coarse errors against both the actual initial sample and its canonical
bin in matrix units. These finite amplitude bounds do not establish the global root-metric
precision payment. No dense request is evaluated at budget zero. -/
theorem initialSample_zero_error
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (bin : ℕ)
    (σ : Environment P 3) (x y : ZMod P) :
    |(0 : ℝ) - B.initialSample r bin σ x y| ≤ B.positiveMagnitude r bin ∧
      |(0 : ℝ) - B.binRate bin * B.cutoff bin (B.base x y / B.binRate bin)| ≤
        |B.binRate bin| * B.binCap := by
  refine ⟨?_, ?_⟩
  · simpa only [zero_sub, abs_neg] using B.initialSample_abs_le r bin σ x y
  · rw [zero_sub, abs_neg, abs_mul]
    apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
    rw [abs_of_nonneg (B.cutoff_bounds bin _).1]
    exact (B.cutoff_bounds bin _).2

/-- Initial RAW is a specialization of shared positive-bin evaluation: its actual
zero correction kills the product, and the direct dense child is computed locally.
This lemma covers every bin of the finite assembly, not a single-bin evaluator. -/
theorem positiveSample_initial (M m : ℕ) (hm : 0 < m) (hmM : m < M) (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    let R := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    B.positiveSample (fun m r => if m < M then B.evaluate m r else none)
      m bin (.pilotInput ⟨0, HP.k_pos⟩) r =
      some (fun σ x y => B.binRate bin *
        HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y *
        denseChild B.padding id R.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base σ x y) := by
  intro R
  have hd := B.evaluate_dense m bin hm R.direct rfl
  have hl := B.evaluate_pilotCorrection_zero m R.left rfl
  have hr := B.evaluate_dense m bin hm R.right rfl
  have hd' : row (fun m r => if m < M then B.evaluate m r else none) m R.direct =
      some (denseChild B.padding id R.direct (B.cutoff bin) (B.auxiliary bin)
        HP.ρ HP.K B.base) := by
    dsimp only [row]
    rw [ite_eq_left hmM, hd]
    rfl
  have hl' : row (fun m r => if m < M then B.evaluate m r else none) m R.left = some 0 := by
    dsimp only [row]
    rw [ite_eq_left hmM, hl]
    rfl
  have hr' : row (fun m r => if m < M then B.evaluate m r else none) m R.right =
      some (denseChild B.padding id R.right (B.cutoff bin) (B.auxiliary bin)
        HP.ρ HP.K B.base) := by
    dsimp only [row]
    rw [ite_eq_left hmM, hr]
    rfl
  change (do
    let direct ← row (fun m r => if m < M then B.evaluate m r else none) m R.direct
    let left ← row (fun m r => if m < M then B.evaluate m r else none) m R.left
    let right ← row (fun m r => if m < M then B.evaluate m r else none) m R.right
    pure (fun σ x y =>
      B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y *
        direct σ x y +
      B.binRate bin * HierarchyTask.usageRatio (channels B.padding) r.terminal R.right y *
        ((midpoint r).rate / (dens {τ | (midpoint r).retains (channels B.padding) τ y} : ℝ)) *
        ∑ z, left σ x z * right σ z y)) = _
  simp only [hd', hl', hr', bind, Option.bind, pure]
  congr 1
  funext σ x y
  simp

/-- Simultaneous positive-budget availability for every initial-bin request. The two
samples of a group use the very same history functions, at their own budgets. -/
theorem sample_initial (M m : ℕ) (hm : 0 < m) (hmM : m < M) (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    let R := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    B.sample (fun m r => if m < M then B.evaluate m r else none)
      m (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) =
      some (fun σ x y => B.binRate bin *
        HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y *
        denseChild B.padding id R.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base σ x y) := by
  unfold sample
  rw [ite_eq_right (Nat.ne_of_gt hm)]
  exact B.positiveSample_initial M m hm hmM bin r

/-- All lower budgets of an initial positive ray are available together. Budget zero
uses the proved coarse boundary, while every positive budget calls the actual evaluator. -/
theorem sample_initial_eq (M : ℕ) (_hM : 0 < M) (m : ℕ) (hmM : m < M) (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.sample (fun m r => if m < M then B.evaluate m r else none)
      m (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) =
      some (if m = 0 then 0 else B.initialSample r bin) := by
  by_cases hm : m = 0
  · subst m
    rfl
  · rw [ite_eq_right hm, B.sample_initial M m (by omega) hmM bin r]
    rfl

/-- Actual paired lower calls for the initial constructor, at both scheduled budgets.
This is an availability equation, not a supplied child family or error certificate. -/
theorem pairedSample_initial (M d : ℕ) (hM : 0 < M) (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    let fine := LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin))
    let coarse := LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
    B.pairedSample (fun m r => if m < M then B.evaluate m r else none)
      M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) =
      some ((if fine = 0 then 0 else B.initialSample r bin) -
        (if coarse = 0 then 0 else B.initialSample r bin)) := by
  dsimp only
  unfold pairedSample
  dsimp only
  by_cases heq : LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) =
      LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin))
  · rw [ite_eq_left heq, heq, sub_self]
  · rw [ite_eq_right heq, B.sample_initial_eq M hM _ (B.pairedSample_budgets_lt M d hM r _).1,
      B.sample_initial_eq M hM _ (B.pairedSample_budgets_lt M d hM r _).2]
    rfl

/-- Uniform magnitude of the actual paired initial contribution, including empty
and zero-budget groups. This is before completion; no walk sparsity is inferred. -/
theorem pairedSample_initial_bound (M d : ℕ) (hM : 0 < M) (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    ∃ A, B.pairedSample (fun m r => if m < M then B.evaluate m r else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      ∀ σ x y, |A σ x y| ≤ 2 * B.positiveMagnitude r bin := by
  rw [B.pairedSample_initial M d hM bin r]
  refine ⟨_, rfl, ?_⟩
  intro σ x y
  have hp : 0 ≤ B.positiveMagnitude r bin :=
    sum_nonneg fun y _ => B.positiveCharge_nonneg r bin y
  have ha := B.initialSample_abs_le r bin σ x y
  change |((if _ then 0 else B.initialSample r bin) σ x y) -
    ((if _ then 0 else B.initialSample r bin) σ x y)| ≤ _
  split_ifs <;> simp only [Pi.zero_apply, Matrix.zero_apply, zero_sub, sub_zero, sub_self, abs_neg,
      abs_zero] <;>
    linarith

/-- Every included positive ray's paired amplitude is paid by the allocation fixed
from primitive cutoffs and literal finite rate charges. -/
theorem positiveMagnitude_twice_le (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (bin : ℕ) (hbin : bin ∈ B.bins) :
    2 * B.positiveMagnitude r bin ≤ B.magnitude r := by
  have hp : B.positiveMagnitude r bin ≤ ∑ i ∈ B.bins, B.positiveMagnitude r i :=
    single_le_sum (fun i _ => sum_nonneg fun y _ => B.positiveCharge_nonneg r i y) hbin
  have hn : 0 ≤ B.negativeMagnitude r := by
    unfold negativeMagnitude atomCap
    have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
    exact sum_nonneg fun y _ => mul_nonneg (abs_nonneg _) (by positivity)
  have hC : 0 ≤ B.atomCap := mul_nonneg (by norm_num) (HP.Q_nonneg _)
  unfold magnitude
  linarith

/-- The actual history-based paired initial samples have certified walk amplitudes.
This covers every finite bin and all slack groups, rather than a hardcoded fixture. -/
theorem pairedSample_initial_certified (M d : ℕ) (hM : 0 < M) (bin : ℕ)
    (hbin : bin ∈ B.bins) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    ∃ A, B.pairedSample (fun m r => if m < M then B.evaluate m r else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      ∀ σ x y, |A σ x y| ≤ B.magnitude r := by
  obtain ⟨A, hA, hb⟩ := B.pairedSample_initial_bound M d hM bin r
  exact ⟨A, hA, fun σ x y => (hb σ x y).trans (B.positiveMagnitude_twice_le r bin hbin)⟩

/-- Actual initial slack-group completion and its centered-noise payment from the
same proved amplitude, on the original source/usage grid. No input bound is assumed. -/
theorem pairedSample_initial_completion (M d : ℕ) (hM : 0 < M) (bin : ℕ)
    (hbin : bin ∈ B.bins) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su) :
    ∃ A, B.pairedSample (fun m r => if m < M then B.evaluate m r else none)
        M d (.pilotInput ⟨0, HP.k_pos⟩) r (some bin) = some A ∧
      B.complete M r A d = some (conditionalWalk
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ku) (CopyPadding.identifier B.padding su))
        (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
          (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
        (fun _ _ => B.steps M r d) A) ∧
      rowNormPow 4 P r.source.rate
        (X s (side P ks) (CopyPadding.identifier B.padding ss))
        (Y t (side P ku) (CopyPadding.identifier B.padding su))
        (fun σ x y => conditionalWalk
          (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y t (side P ku) (CopyPadding.identifier B.padding su))
          (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
            (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
          (fun _ _ => B.steps M r d) A σ x y -
          rowSliceMean (X s (side P ks) (CopyPadding.identifier B.padding ss))
            (Y t (side P ku) (CopyPadding.identifier B.padding su)) A x y) ≤
        (((2 : ℝ) ^ (-B.requestPrecision M r)) * (64 : ℝ)⁻¹ ^ d) ^ 4 := by
  obtain ⟨A, hA, hbound⟩ := B.pairedSample_initial_certified M d hM bin hbin r
  have hsource : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
  exact ⟨A, hA, B.complete_grid M r s t hst ks ku ss su hs hu A d,
    B.completion_noise M r s t hst ks ku ss su hsource A hbound d⟩

/-- Literal assembled initial input at one paired group, before its common walk. All
bins use the same recursive history; their fine/coarse budgets retain their own scales. -/
@[expose] def initialGroupInput (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ x y => ∑ bin ∈ B.bins,
    ((if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0
      then 0 else B.initialSample r bin σ x y) -
    (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)) = 0
      then 0 else B.initialSample r bin σ x y))

/-- The allocation pays the amplitude of the assembled initial group, with every bin
included. This bound is derived from primitive cutoff caps, before the common walk. -/
theorem initialGroupInput_bound (M d : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) (σ : Environment P 3) (x y : ZMod P) :
    |B.initialGroupInput M d r σ x y| ≤ B.magnitude r := by
  have hb (bin : ℕ) :
      |((if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0
        then 0 else B.initialSample r bin σ x y) -
      (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)) = 0
        then 0 else B.initialSample r bin σ x y))| ≤ 2 * B.positiveMagnitude r bin := by
    have ha := B.initialSample_abs_le r bin σ x y
    have hp : 0 ≤ B.positiveMagnitude r bin :=
      sum_nonneg fun y _ => B.positiveCharge_nonneg r bin y
    split_ifs <;> simp only [zero_sub, sub_zero, sub_self, abs_neg, abs_zero] <;> linarith
  have hn : 0 ≤ B.negativeMagnitude r := by
    unfold negativeMagnitude atomCap
    have hQ := HP.Q_nonneg HP.toHierarchyParams.atomCap
    exact sum_nonneg fun y _ => mul_nonneg (abs_nonneg _) (by positivity)
  have hc : 0 ≤ B.atomCap := mul_nonneg (by norm_num) (HP.Q_nonneg _)
  calc
    _ ≤ ∑ bin ∈ B.bins, |((if LogSpaceEstimation.lastBudget M d B.slack
        (B.sampleScale r (some bin)) = 0 then 0 else B.initialSample r bin σ x y) -
        (if LogSpaceEstimation.lastBudget M (2 * d) B.slack
          (B.sampleScale r (some bin)) = 0 then 0 else B.initialSample r bin σ x y))| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ bin ∈ B.bins, 2 * B.positiveMagnitude r bin := sum_le_sum fun bin _ => hb bin
    _ ≤ B.magnitude r := by rw [← mul_sum]; unfold magnitude; linarith

set_option backward.isDefEq.respectTransparency false in
/-- The actual initial-group computation assembles its paired history children and
then completes that assembled input. Nonempty bins require the genuine frame guard. -/
theorem completedGroup_initial (M d : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    B.completedGroup (fun m r => if m < M then B.evaluate m r else none)
      M d (.pilotInput ⟨0, HP.k_pos⟩) r = B.complete M r (B.initialGroupInput M d r) d := by
  have he : (B.rays (.pilotInput ⟨0, HP.k_pos⟩)).isEmpty = false := by
    simp only [rays, List.append_nil, List.isEmpty_map]
    exact Bool.eq_false_iff.mpr hbins.not_empty_toList
  unfold completedGroup
  rw [he]
  simp only [Bool.false_eq_true, ↓reduceIte, rays, List.append_nil, List.mapM_map]
  simp_rw [Function.comp_def, B.pairedSample_initial M d hM]
  have hm (f : ℕ → Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
      B.bins.toList.mapM (fun i => some (f i)) = some (B.bins.toList.map f) := List.mapM_pure
  rw [hm]
  simp only [bind, Option.bind_some]
  congr 1
  funext σ x y
  simp only [List.map_map, Function.comp_def, Pi.sub_apply]
  rw [Finset.sum_map_toList]
  unfold initialGroupInput
  apply sum_congr rfl
  intro bin _
  split_ifs <;> rfl

set_option backward.isDefEq.respectTransparency false in
/-- The computed initial group is literally the sum of its completed paired rays.
Every term retains its own fine/coarse scale, but shares the request graph and length. -/
theorem completedGroup_initial_rays (M d : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su) :
    let T := fun bin =>
      (if LogSpaceEstimation.lastBudget M d B.slack (B.sampleScale r (some bin)) = 0
        then 0 else B.initialSample r bin) -
      (if LogSpaceEstimation.lastBudget M (2 * d) B.slack (B.sampleScale r (some bin)) = 0
        then 0 else B.initialSample r bin)
    B.completedGroup (fun m r => if m < M then B.evaluate m r else none)
      M d (.pilotInput ⟨0, HP.k_pos⟩) r = some (fun σ x y =>
        (B.bins.toList.map (fun bin => conditionalWalk
          (X s (side P ks) (CopyPadding.identifier B.padding ss))
          (Y t (side P ku) (CopyPadding.identifier B.padding su))
          (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
            (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
          (fun _ _ => B.steps M r d) (T bin) σ x y)).sum) := by
  intro T
  rw [B.completedGroup_initial M d hM hbins r]
  have hinput : B.initialGroupInput M d r =
      fun σ x y => ((B.bins.toList.map T).map (fun A => A σ x y)).sum := by
    funext σ x y
    simp only [List.map_map, Function.comp_def, Finset.sum_map_toList, initialGroupInput]
    apply sum_congr rfl
    intro bin _
    dsimp only [T]
    split_ifs <;> rfl
  rw [hinput]
  simpa only [List.map_map, Function.comp_def] using
    B.complete_grid_list_sum M r s t hst ks ku ss su hs hu (B.bins.toList.map T) d

/-- Actual assembled-group availability and centered noise on the unchanged H4 grid.
The same history children supply both the computed row and its proved allocation amplitude.
This is centered group noise, not canonical accuracy or a sum over all groups. -/
theorem completedGroup_initial_grid (M d : ℕ) (hM : 0 < M) (hbins : B.bins.Nonempty)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    let A := B.initialGroupInput M d r
    let F := conditionalWalk Xs Yu
      (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r d) A
    B.completedGroup (fun m r => if m < M then B.evaluate m r else none)
      M d (.pilotInput ⟨0, HP.k_pos⟩) r = some F ∧
    rowNormPow 4 P r.source.rate Xs Yu
      (fun σ x y => F σ x y - rowSliceMean Xs Yu A x y) ≤
        (((2 : ℝ) ^ (-B.requestPrecision M r)) * (64 : ℝ)⁻¹ ^ d) ^ 4 := by
  dsimp only
  constructor
  · rw [B.completedGroup_initial M d hM hbins r]
    exact B.complete_grid M r s t hst ks ku ss su hs hu _ d
  · have hsource : 0 < r.source.rate := by rw [hs]; exact rate_pos ks
    exact B.completion_noise M r s t hst ks ku ss su hsource _
      (B.initialGroupInput_bound M d r) d

/-- Every successful shared normalized call has the existing actual range, usage guard,
and rank-channel row sparsity, irrespective of lower-call errors. This is the safety
part of the intended simultaneous invariant; accuracy and incoming column support are
separate obligations. -/
theorem normalized_bounds
    (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
      Option (BudgetValue P))
    (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (pilot : Bool) (i : Fin HP.k)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.normalized history M r pilot i = some A) :
    (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap)) ∧
    (∀ σ x y, ¬ r.usage.retains (channels B.padding) σ y → A σ x y = 0) ∧
    ∀ σ x, #{y ∈ ({y | r.terminal.retains (channels B.padding) σ y} : Finset _) |
      A σ x y ≠ 0} ≤ HP.K := by
  unfold normalized at hA
  cases hraw : row history (B.childBudget M)
      { r with task := .row 0 (if pilot then .pilotInput i else .input i) } with
  | none => simp [hraw] at hA
  | some raw =>
    cases hprep : row history (B.childBudget M)
        { r with task := .row 0 (if pilot then .pilotPreparation i else .preparation i) } with
    | none => simp [hraw, hprep] at hA
    | some prep =>
      cases hmax : vector history (B.childBudget M)
          { r with task := .row 0 (.maximum (if pilot then i.succ else Fin.last HP.k)) } with
      | none => simp [hraw, hprep, hmax] at hA
      | some maximum =>
        simp only [hraw, hprep, hmax] at hA
        have heq : correctionRequest B.padding id r (polynomialAuxCutoff4 HP.θ)
            HP.incomingCutoff HP.ρ HP.toHierarchyParams.atomCutoff HP.γ HP.K
            ⌈4 * (1 + 32 * HP.R)⌉₊ raw prep maximum = A := Option.some.inj hA
        subst A
        refine ⟨?_, ?_, ?_⟩
        · exact fun σ x y => selectedRequest_mem_Icc HP B.padding id r _ raw prep maximum σ x y
        · exact fun σ x y hy => correctionRequest_eq_zero_of_not_usage
            B.padding id r _ _ _ _ _ _ _ raw prep maximum σ x y hy
        · exact fun σ x => selectedRequest_row_support HP
            (FourthRootHierarchyParams.NormalizedRow.rank_pos HP)
            B.padding id r _ raw prep maximum σ x

/-- Successful normalized rows share one range, usage and support law at every budget.
No errors or correctness certificate are inputs. Availability remains explicit. -/
theorem evaluate_normalized_bounds (M : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotNormalized i else .normalized i))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.evaluate M r = some (.row A)) :
    (∀ σ x y, A σ x y ∈ Set.Icc 0 (2 * HP.Q HP.toHierarchyParams.atomCap)) ∧
    (∀ σ x y, ¬ r.usage.retains (channels B.padding) σ y → A σ x y = 0) ∧
    ∀ σ x, #{y ∈ ({y | r.terminal.retains (channels B.padding) σ y} : Finset _) |
      A σ x y ≠ 0} ≤ HP.K := by
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
      exact B.normalized_bounds _ M _ _ i _ hn

/-- A genuine inductive vector case of the shared evaluator: the successful earlier
maximum and detector calls determine the new value, its range, and its fourth-moment
error against the corresponding reference maximum. The two lower errors remain on
the same parent masks; there is no final-accuracy hypothesis. -/
theorem evaluate_maximum_succ
    (M : ℕ) (hM : 0 < M) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (i : Fin HP.k) (hr : r.task = .row 0 (.maximum i.succ))
    (hactive : 0 < B.requestPrecision M r)
    (a b : Environment P 3 → ZMod P → ℝ)
    (ha : B.evaluate (B.childBudget M)
      { r with task := .row 0 (.maximum i.castSucc) } = some (.vector a))
    (hb : B.evaluate (B.childBudget M)
      { r with task := .row 0 (.detector i) } = some (.vector b)) :
    B.evaluate M r = some (.vector (fun σ => PilotRowRecipe.maximum (a σ) (b σ))) ∧
    (∀ σ y, PilotRowRecipe.maximum (a σ) (b σ) y ∈ Set.Icc 0 1) ∧
    ∀ (a' b' : Environment P 3 → ZMod P → ℝ) {N u : ℝ}, 0 ≤ N * u →
      rowNormPow 4 N u
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ _ y => PilotRowRecipe.maximum (a σ) (b σ) y -
          PilotRowRecipe.maximum (a' σ) (b' σ) y) ≤
      rowNormPow 4 N u
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ _ y => a σ y - a' σ y) +
      rowNormPow 4 N u
        (fun σ x => r.source.retains (channels B.padding) σ x)
        (fun σ y => r.terminal.retains (channels B.padding) σ y)
        (fun σ _ y => b σ y - b' σ y) := by
  refine ⟨?_, fun σ y => PilotRowRecipe.maximum_mem_Icc _ _ y, ?_⟩
  · rw [evaluate, step, hr]
    simp only [Fin.val_succ, Nat.add_eq_zero_iff, one_ne_zero, and_false, ↓reduceDIte,
      hactive, ↓reduceIte]
    have hi : (⟨i.val + 1 - 1, by omega⟩ : Fin HP.k) = i := by ext; simp
    simp only [hi, vector, B.childBudget_lt hM, ↓reduceDIte, ha, hb,
      Option.bind_some, BudgetValue.vector?]
    rfl
  · intro a' b' N u hNu
    exact PilotRowRecipe.maximum_row_moment _ _ a b a' b' hNu

end BudgetData
end Matrix.HierarchyParams.H4RankEnvironment
