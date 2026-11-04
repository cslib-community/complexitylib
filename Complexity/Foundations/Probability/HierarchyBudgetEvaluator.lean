/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyDetector
public import Complexity.Foundations.Probability.HierarchyDenseChildren
public import Complexity.Foundations.Probability.EstimatorSchedule
public import Complexity.Foundations.Probability.HierarchyEstimatedInput
import Complexity.Foundations.Probability.NormalizedAtomRows.Output
import Complexity.Foundations.Probability.RootMetric.FiniteError

/-!+# Statistical-budget evaluation of existing hierarchy requests

The structural parameter `HP.k` is fixed. Recursive calls use `lastBudget`, independently
of structural task ranks. Rows and vectors share one history, and every child retains the
entire original H4 environment. Finite RAW assembly sums positive bins and subtracts the
negative correction once. No child function or accuracy oracle is an input.

This is a partial mathematical evaluator, not the closed estimator of
[OpenAI2026LogSpace, Sections 7.4–7.5]. Exact base/dense leaves remain available at every
budget. `none` reports an inactive recursive request, an invalid frame, or an unsupported
constructor; it never substitutes zero for one.
The implemented domain is stage zero, including later finite correction iterations.
Cross-stage matrix/copy and reward transport and justified inactive approximations remain
open. The simultaneous analytic budget induction is not established here.

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
* `BudgetData.normalized_bounds`: actual normalized range, usage and row support.
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

/-- Finite stage-zero inputs and explicit allocation parameters. `magnitude` is a
preselected uniform bound used for allocation, not an input-dependent moment or an
accuracy certificate. Proving it bounds each assembled input is a separate obligation. -/
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
  /-- Preselected per-request magnitude for finite walk allocation. -/
  magnitude : HierarchyTask.Request HP.k (Fin 3) (ZMod P) → ℝ

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

/-- Positive lengths are chosen from an explicit width/rate/magnitude envelope before
the lower calls. This allocation alone does not certify that the supplied envelope suffices. -/
@[expose] def steps (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) : ℕ :=
  max 1 (spectralWalkLength (1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4))
    (32 * ((P : ℝ)^2 / (P * r.source.rate) * B.magnitude r ^ 4))
    ((2 : ℝ) ^ (-B.requestPrecision M r)) 0)

omit [Fact P.Prime] in
/-- The mathematical allocator never selects the zero-length walk. -/
theorem steps_pos (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    0 < B.steps M r := lt_of_lt_of_le Nat.zero_lt_one (Nat.le_max_left _ _)

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
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :=
  B.completeAt r.source.role r.usage.role
    (semanticSide P r.source.rate) (semanticSide P r.usage.rate)
    r.source.suffix r.usage.suffix (B.steps M r) A

/-- Grid requests use exactly the original H4 retained-pair graph, with the source
and usage suffixes intact. The frame guard cannot reject a grid call on distinct roles. -/
theorem complete_grid (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel t ku su)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    B.complete M r A = some (conditionalWalk
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y t (side P ku) (CopyPadding.identifier B.padding su))
      (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r) A) := by
  unfold complete
  rw [hs, hu]
  simp only [gridChannel, semanticSide_grid]
  unfold completeAt
  rw [dite_eq_left ⟨hst, side_pos P ks (Fact.out : P.Prime).pos,
    side_le P ks, side_pos P ku (Fact.out : P.Prime).pos, side_le P ku⟩]
  rfl

/-- The preselected uniform magnitude pays actual full-coordinate completion noise.
This is centered noise against the computed child's literal slice mean, not accuracy
against a supplied desired mean or a canonical hierarchy target. -/
theorem completion_noise (M : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s t : Fin 3) (hst : s ≠ t) (ks ku : ℕ) (ss su : List (ZMod P))
    (hu : 0 < r.source.rate)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : ∀ σ x y, |A σ x y| ≤ B.magnitude r) :
    let Xs := X s (side P ks) (CopyPadding.identifier B.padding ss)
    let Yu := Y t (side P ku) (CopyPadding.identifier B.padding su)
    rowNormPow 4 P r.source.rate Xs Yu (fun σ x y =>
      conditionalWalk Xs Yu
        (graph s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
          (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
        (fun _ _ => B.steps M r) A σ x y - rowSliceMean Xs Yu A x y) ≤
      ((2 : ℝ) ^ (-B.requestPrecision M r)) ^ 4 := by
  intro Xs Yu
  have hNu : 0 ≤ (P : ℝ) * r.source.rate := mul_nonneg (Nat.cast_nonneg _) hu.le
  have hbound := rowNormPow_fourth_le_expect_envelope hNu Xs Yu A
    (fun _ => B.magnitude r ^ 4) (fun _ => by positivity)
    (fun σ x y _ _ => pow_le_pow_left₀ (abs_nonneg _) (hA σ x y) 4)
  simp only [ZMod.card, Fintype.expect_const] at hbound
  have hr : 0 < 1 - 1 / (155648 * (3 + 1) * (4 : ℝ)^4) := by norm_num
  have hp := spectralWalkLength_payment hr (sub_lt_self _ (by positivity))
    (show 0 ≤ 32 * ((P : ℝ)^2 / (P * r.source.rate) * B.magnitude r ^ 4) by positivity)
    (Real.rpow_pos_of_pos (by norm_num) _) 0 (B.steps M r) (Nat.le_max_right _ _)
  simp only [pow_zero, mul_one] at hp
  have hn := noise s t hst (side P ks) (side P ku) (side_le P ks) (side_le P ku)
    (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su)
    hNu (B.steps M r) A
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
bin's scheduled lower budget. Direct and right requests keep distinct source tuples. -/
@[expose] def positiveBin (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
    Option (BudgetValue P))
    (M i : ℕ) (t : HierarchyTask.RawTask HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let R := HierarchyTask.rawRequests 0 i t r.source (midpoint r) r.terminal (B.binRate i)
  let m := B.binBudget M i r
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

/-- All finite positive bins, followed by the residual's single negative request.
No negative term is placed inside the bin sum. -/
@[expose] def raw (history : ℕ → HierarchyTask.Request HP.k (Fin 3) (ZMod P) →
    Option (BudgetValue P))
    (M : ℕ) (t : HierarchyTask.RawTask HP.k) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    Option (Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) := do
  let positives ← B.bins.toList.mapM fun i => B.positiveBin history M i t r
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
  B.complete M r (fun σ x y => (positives.map (fun A => A σ x y)).sum - negative σ x y)

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

/-- A single constructor step. Exact base/dense leaves and literal iteration-zero
constants are available at every budget. Nonconstant inactive calls remain explicitly
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
  | .basePreparation 0 i => some (.row
      (densePreparation B.padding id r (B.auxiliary i) HP.ρ HP.K B.base))
  | .baseNormalized 0 i => some (.row
      (denseChild B.padding id r (B.cutoff i) (B.auxiliary i) HP.ρ HP.K B.base))
  | .row 0 (.pilotInput i) =>
    if 0 < B.requestPrecision M r then (B.raw history M (.pilotInput i) r).map .row else none
  | .row 0 (.input i) =>
    if 0 < B.requestPrecision M r then (B.raw history M (.input i) r).map .row else none
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

/-- Dense leaves evaluate their genuine preparation at every statistical budget. -/
theorem evaluate_dense (M i : ℕ) (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .baseNormalized 0 i) :
    B.evaluate M r = some (.row
      (denseChild B.padding id r (B.cutoff i) (B.auxiliary i) HP.ρ HP.K B.base)) := by
  rw [evaluate, step, hr]
  rfl

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

/-- Initial RAW is a specialization of shared positive-bin evaluation: its actual
zero correction kills the product, and the direct dense child is computed locally.
This lemma covers every bin of the finite assembly, not a single-bin evaluator. -/
theorem positiveBin_initial (M : ℕ) (hM : 0 < M) (bin : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P)) :
    let R := HierarchyTask.rawRequests 0 bin (.pilotInput ⟨0, HP.k_pos⟩)
      r.source (midpoint r) r.terminal (B.binRate bin)
    B.positiveBin (fun m r => if m < M then B.evaluate m r else none)
      M bin (.pilotInput ⟨0, HP.k_pos⟩) r =
      some (fun σ x y => B.binRate bin *
        HierarchyTask.usageRatio (channels B.padding) r.terminal R.direct y *
        denseChild B.padding id R.direct (B.cutoff bin) (B.auxiliary bin)
          HP.ρ HP.K B.base σ x y) := by
  intro R
  let m := B.binBudget M bin r
  have hm : m < M := B.binBudget_lt hM bin r
  have hd := B.evaluate_dense m bin R.direct rfl
  have hl := B.evaluate_pilotCorrection_zero m R.left rfl
  have hr := B.evaluate_dense m bin R.right rfl
  have hd' : row (fun m r => if m < M then B.evaluate m r else none) m R.direct =
      some (denseChild B.padding id R.direct (B.cutoff bin) (B.auxiliary bin)
        HP.ρ HP.K B.base) := by
    dsimp only [row]
    rw [ite_eq_left hm, hd]
    rfl
  have hl' : row (fun m r => if m < M then B.evaluate m r else none) m R.left = some 0 := by
    dsimp only [row]
    rw [ite_eq_left hm, hl]
    rfl
  have hr' : row (fun m r => if m < M then B.evaluate m r else none) m R.right =
      some (denseChild B.padding id R.right (B.cutoff bin) (B.auxiliary bin)
        HP.ρ HP.K B.base) := by
    dsimp only [row]
    rw [ite_eq_left hm, hr]
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
