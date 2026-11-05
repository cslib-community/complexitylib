/-
Copyright (c) 2026 Christian Reitwiessner, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner, Samuel Schlesinger
-/
module
-- upstream: candidate

public import Complexity.Foundations.Probability.HierarchyBudgetEvaluator
public import Complexity.Foundations.Probability.RootMetric.Stationarity

/-!
# Execution and stationarity of the incoming PREP request

The production PREP constructor reads its corresponding completed input at `childBudget M`,
then applies the incoming-gated correction preparation and completes it with slack zero.
This is distinct from the dense selected-preparation list used by initial compression.
The identities below retain the original rank channel and all source/usage suffixes.
Positive-precision child success is an explicit premise, not recursive availability or accuracy.
These are original execution identities; no numerical incoming-bias payment is claimed.

## Main results

* `BudgetData.evaluate_preparation`: literal incoming PREP execution.
* `BudgetData.evaluate_preparation_grid`: the successful production H4 walk.
* `BudgetData.preparationWalk_mean`: its same-slice conditional mean is unchanged.
-/

public section
noncomputable section
namespace Matrix.HierarchyParams.H4RankEnvironment.BudgetData
open Finset Cslib Cslib.Probability
attribute [local instance] Classical.propDecidable
attribute [local implicit_reducible] Matrix
variable {P : ℕ} [Fact P.Prime] {HP : FourthRootHierarchyParams 16 1 16 32 8}
  (B : BudgetData HP P)

/-- Incoming preparation of a completed RAW child, with its original source and rank sets.
Unlike `binPreparation`, this includes the incoming column gate. -/
@[expose] def incomingPreparation (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ) :
    Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ :=
  fun σ => correctionPrep (polynomialAuxCutoff4 HP.θ) HP.incomingCutoff HP.K
    ⌈4 * (1 + 32 * HP.R)⌉₊ r.terminal.rate (A σ) (polynomialPrepCutoff4 HP.θ) HP.ρ
    {x | r.source.retains (channels B.padding) σ x}
    {y | r.terminal.retains (channels B.padding) σ y}

/-- Extract the literal successful RAW child. Completion uses the production default slack zero;
no selected-preparation list or changed-task accuracy is assumed. -/
theorem evaluate_preparation (M : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hp : 0 < B.requestPrecision M r) (hm : B.childBudget M < M)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.evaluate (B.childBudget M)
      { r with task := .row 0 (if pilot then .pilotInput i else .input i) } = some (.row A)) :
    B.evaluate M r = (B.complete M r (B.incomingPreparation r A)).map .row := by
  rw [evaluate_eq]
  cases pilot <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at hr hA
  all_goals
    simp only [step, hr, hp, ↓reduceIte, row, hm, hA, Option.bind_some,
      BudgetValue.row?]
    rfl

/-- Inactive PREP requests reject even if a RAW child could be supplied. -/
theorem evaluate_preparation_inactive (M : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hp : ¬ 0 < B.requestPrecision M r) : B.evaluate M r = none := by
  rw [evaluate_eq]
  cases pilot <;> simp only [Bool.false_eq_true, ↓reduceIte] at hr
  all_goals simp only [step, hr, hp, ↓reduceIte]

/-- Grid completion of the actual incoming preparation, including unequal rates and suffixes. -/
theorem evaluate_preparation_grid (M : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hp : 0 < B.requestPrecision M r) (hm : B.childBudget M < M)
    (A : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.evaluate (B.childBudget M)
      { r with task := .row 0 (if pilot then .pilotInput i else .input i) } = some (.row A))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su) :
    B.evaluate M r = some (.row (conditionalWalk
      (X s (side P ks) (CopyPadding.identifier B.padding ss))
      (Y u (side P ku) (CopyPadding.identifier B.padding su))
      (graph s u hsu (side P ks) (side P ku) (side_le P ks) (side_le P ku)
        (CopyPadding.identifier B.padding ss) (CopyPadding.identifier B.padding su))
      (fun _ _ => B.steps M r 0) (B.incomingPreparation r A))) := by
  rw [B.evaluate_preparation M pilot i r hr hp hm A hA,
    B.complete_grid M r s u hsu ks ku ss su hs hu]
  rfl

/-- Stationarity removes only the usage walk, retaining the incoming gate and the actual
completed child on the same source/usage slice. Empty slices obey the same identity. -/
theorem preparationWalk_mean (M : ℕ)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hW : B.complete M r (B.incomingPreparation r A) = some W) (x y : ZMod P) :
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y) W x y =
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y)
      (B.incomingPreparation r A) x y := by
  rw [B.complete_grid M r s u hsu ks ku ss su hs hu] at hW
  cases Option.some.inj hW
  have hx : (fun σ x => r.source.retains (channels B.padding) σ x) =
      X s (side P ks) (CopyPadding.identifier B.padding ss) := by
    rw [hs]
    funext σ x
    simp only [gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid]
    rfl
  have hy : (fun σ y => r.usage.retains (channels B.padding) σ y) =
      Y u (side P ku) (CopyPadding.identifier B.padding su) := by
    rw [hu]
    funext σ y
    simp only [gridChannel, CorrectionRowTask.Channel.retains, channels, semanticSide_grid]
    rfl
  simp only [hx, hy]
  exact rowSliceMean_conditionalWalk _ _ _ _ _ x y

/-- A successful production PREP result has the same source/usage normalizer as the incoming
preparation of its child. That input child must succeed at its own smaller budget. -/
theorem evaluate_preparation_mean (M : ℕ) (pilot : Bool) (i : Fin HP.k)
    (r : HierarchyTask.Request HP.k (Fin 3) (ZMod P))
    (hr : r.task = .row 0 (if pilot then .pilotPreparation i else .preparation i))
    (hp : 0 < B.requestPrecision M r) (hm : B.childBudget M < M)
    (A W : Environment P 3 → Matrix (ZMod P) (ZMod P) ℝ)
    (hA : B.evaluate (B.childBudget M)
      { r with task := .row 0 (if pilot then .pilotInput i else .input i) } = some (.row A))
    (hW : B.evaluate M r = some (.row W))
    (s u : Fin 3) (hsu : s ≠ u) (ks ku : ℕ) (ss su : List (ZMod P))
    (hs : r.source = gridChannel s ks ss) (hu : r.usage = gridChannel u ku su)
    (x y : ZMod P) :
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y) W x y =
    rowSliceMean (fun σ x => r.source.retains (channels B.padding) σ x)
      (fun σ y => r.usage.retains (channels B.padding) σ y)
      (B.incomingPreparation r A) x y := by
  rw [B.evaluate_preparation M pilot i r hr hp hm A hA] at hW
  have hc : B.complete M r (B.incomingPreparation r A) = some W := by
    cases h : B.complete M r (B.incomingPreparation r A) with
    | none => simp only [h, Option.map_none, reduceCtorEq] at hW
    | some V =>
      simp only [h, Option.map_some, Option.some.injEq, BudgetValue.row.injEq] at hW
      exact congrArg some hW
  exact B.preparationWalk_mean M r s u hsu ks ku ss su hs hu A W hc x y

end Matrix.HierarchyParams.H4RankEnvironment.BudgetData
