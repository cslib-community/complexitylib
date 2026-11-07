/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Matroid.Greedy
public import Complexity.Algorithms.Lean.Query.Matroid.IndepQuery
public import Cslib.Algorithms.Lean.Query.Bounds

/-!
# Matroid Greedy Selection as an Independence-Oracle Query Program

This module instantiates the monadic matroid greedy algorithms from
`Complexity.Algorithms.Lean.Matroid.Greedy` in `FreeM (IndepQuery α)`, separating independence
oracle queries (charged via `FreeM.countQueries` and `Cslib.Query.UpperBound`) from pure host-side
sorting and filtering.

## Main definitions

* `Cslib.Query.matroidGreedySelect`: greedy scan over `List α` using `IndepQuery.ask`.
* `Cslib.Query.matroidGreedyMaxBasis`: sort by nonincreasing weight `w` and run greedy selection.
* `Cslib.Query.matroidGreedyMinBasis`: sort by nondecreasing weight `w` (Kruskal order) and run
  greedy selection.
* `Cslib.Query.matroidGreedyMaxIndep`: filter `0 ≤ w x` and run `matroidGreedyMaxBasis`.

## Main results

* `eval_matroidGreedySelect`, `eval_matroidGreedyMaxBasis`, `eval_matroidGreedyMinBasis`,
  `eval_matroidGreedyMaxIndep`: `FreeM.eval` agrees with the pure reference implementations via
  `FreeM.isMonadHom_pure_eval`.
* `countQueries_matroidGreedySelect`, `countQueries_matroidGreedyMaxBasis`,
  `countQueries_matroidGreedyMinBasis`, `countQueries_matroidGreedyMaxIndep_le`: exact `n`-query
  counts (`≤ n` after nonnegative filtering) along any oracle path.
* `matroidGreedySelect_upperBound`, `matroidGreedyMaxBasis_upperBound`,
  `matroidGreedyMinBasis_upperBound`, `matroidGreedyMaxIndep_upperBound`: linear query upper bounds
  `UpperBound ... List.length id`.
* `eval_matroidGreedySelect_isBasis'`, `sum_le_eval_matroidGreedyMaxBasis`,
  `eval_matroidGreedyMinBasis_le_sum`, `sum_le_eval_matroidGreedyMaxBasis_of_indep`,
  `sum_le_eval_matroidGreedyMaxIndep`: end-to-end basis and weighted optimality under
  `IndepQuery.ImplementsMatroid oracle M`.
-/

public section

open Cslib
open Cslib.Algorithms.Lean.Matroid

namespace Cslib.Query

variable {α : Type} {β : Type*}

/-! ## Query-monadic matroid greedy programs -/

/-- Greedy matroid scan over `xs` making explicit independence queries via `IndepQuery.ask`. -/
@[expose] def matroidGreedySelect [DecidableEq α] (xs : List α) :
    FreeM (IndepQuery α) (Finset α) :=
  greedySelectM IndepQuery.ask xs

/-- Maximum-weight matroid basis selection in the independence-oracle query model. -/
@[expose] def matroidGreedyMaxBasis [DecidableEq α] [LinearOrder β]
    (w : α → β) (xs : List α) : FreeM (IndepQuery α) (Finset α) :=
  greedyMaxBasisM IndepQuery.ask w xs

/-- Minimum-weight matroid basis selection (Kruskal order) in the independence-oracle query
model. -/
@[expose] def matroidGreedyMinBasis [DecidableEq α] [LinearOrder β]
    (w : α → β) (xs : List α) : FreeM (IndepQuery α) (Finset α) :=
  greedyMinBasisM IndepQuery.ask w xs

/-- Maximum-weight independent-set selection under arbitrary signed weights in the
independence-oracle query model. -/
@[expose] def matroidGreedyMaxIndep [DecidableEq α] [Zero β] [LinearOrder β]
    (w : α → β) (xs : List α) : FreeM (IndepQuery α) (Finset α) :=
  greedyMaxIndepM IndepQuery.ask w xs

/-! ## Evaluation agreement with pure greedy algorithms -/

@[simp] theorem eval_matroidGreedySelect [DecidableEq α]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (xs : List α) :
    (matroidGreedySelect xs).eval oracle = greedySelect (fun S => oracle (.indep S)) xs :=
  Id.pure_injective <| by
    simpa [matroidGreedySelect] using
      (FreeM.isMonadHom_pure_eval oracle).map_greedySelectM IndepQuery.ask xs

@[simp] theorem eval_matroidGreedyMaxBasis [DecidableEq α] [LinearOrder β]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (w : α → β) (xs : List α) :
    (matroidGreedyMaxBasis w xs).eval oracle =
      greedyMaxBasis (fun S => oracle (.indep S)) w xs :=
  eval_matroidGreedySelect oracle (xs.mergeSort (fun a b => decide (w b ≤ w a)))

@[simp] theorem eval_matroidGreedyMinBasis [DecidableEq α] [LinearOrder β]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (w : α → β) (xs : List α) :
    (matroidGreedyMinBasis w xs).eval oracle =
      greedyMinBasis (fun S => oracle (.indep S)) w xs :=
  eval_matroidGreedySelect oracle (xs.mergeSort (fun a b => decide (w a ≤ w b)))

@[simp] theorem eval_matroidGreedyMaxIndep [DecidableEq α] [Zero β] [LinearOrder β]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (w : α → β) (xs : List α) :
    (matroidGreedyMaxIndep w xs).eval oracle =
      greedyMaxIndep (fun S => oracle (.indep S)) w xs :=
  eval_matroidGreedyMaxBasis oracle w (xs.filter (fun x => decide (0 ≤ w x)))

/-! ## Exact query counts and `Cslib.Query.UpperBound` certificates -/

private theorem countQueries_foldlM_greedyStepM [DecidableEq α]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (acc : Finset α) (xs : List α) :
    (xs.foldlM (greedyStepM IndepQuery.ask) acc).countQueries oracle = xs.length := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldlM_cons, greedyStepM, IndepQuery.ask, FreeM.countQueries_bind,
      FreeM.eval_bind, FreeM.countQueries_lift, FreeM.eval_lift, ih, List.length_cons]
    by_cases h : oracle (.indep (insert x acc)) = true <;> simp [h, Nat.add_comm]

@[simp] theorem countQueries_matroidGreedySelect [DecidableEq α]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (xs : List α) :
    (matroidGreedySelect xs).countQueries oracle = xs.length :=
  countQueries_foldlM_greedyStepM oracle ∅ xs

@[simp] theorem countQueries_matroidGreedyMaxBasis [DecidableEq α] [LinearOrder β]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (w : α → β) (xs : List α) :
    (matroidGreedyMaxBasis w xs).countQueries oracle = xs.length :=
  (countQueries_matroidGreedySelect oracle _).trans (List.length_mergeSort _)

@[simp] theorem countQueries_matroidGreedyMinBasis [DecidableEq α] [LinearOrder β]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (w : α → β) (xs : List α) :
    (matroidGreedyMinBasis w xs).countQueries oracle = xs.length :=
  (countQueries_matroidGreedySelect oracle _).trans (List.length_mergeSort _)

@[simp] theorem countQueries_matroidGreedyMaxIndep [DecidableEq α] [Zero β] [LinearOrder β]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (w : α → β) (xs : List α) :
    (matroidGreedyMaxIndep w xs).countQueries oracle =
      (xs.filter (fun x => decide (0 ≤ w x))).length :=
  countQueries_matroidGreedyMaxBasis oracle w (xs.filter (fun x => decide (0 ≤ w x)))

theorem countQueries_matroidGreedyMaxIndep_le [DecidableEq α] [Zero β] [LinearOrder β]
    (oracle : {ι : Type} → IndepQuery α ι → ι) (w : α → β) (xs : List α) :
    (matroidGreedyMaxIndep w xs).countQueries oracle ≤ xs.length := by
  rw [countQueries_matroidGreedyMaxIndep]
  exact List.length_filter_le _ xs

/-- `matroidGreedySelect` makes at most `n` independence queries on inputs of length at most `n`. -/
theorem matroidGreedySelect_upperBound [DecidableEq α] :
    UpperBound (matroidGreedySelect (α := α)) List.length id :=
  UpperBound.of_pointwise monotone_id fun oracle xs =>
    (countQueries_matroidGreedySelect oracle xs).le

/-- `matroidGreedyMaxBasis w` makes at most `n` independence queries on inputs of length at most
`n` (sorting uses only pure weight comparisons). -/
theorem matroidGreedyMaxBasis_upperBound [DecidableEq α] [LinearOrder β] (w : α → β) :
    UpperBound (matroidGreedyMaxBasis (α := α) w) List.length id :=
  UpperBound.of_pointwise monotone_id fun oracle xs =>
    (countQueries_matroidGreedyMaxBasis oracle w xs).le

/-- `matroidGreedyMinBasis w` makes at most `n` independence queries on inputs of length at most
`n`. -/
theorem matroidGreedyMinBasis_upperBound [DecidableEq α] [LinearOrder β] (w : α → β) :
    UpperBound (matroidGreedyMinBasis (α := α) w) List.length id :=
  UpperBound.of_pointwise monotone_id fun oracle xs =>
    (countQueries_matroidGreedyMinBasis oracle w xs).le

/-- `matroidGreedyMaxIndep w` makes at most `n` independence queries on inputs of length at most
`n`. -/
theorem matroidGreedyMaxIndep_upperBound [DecidableEq α] [Zero β] [LinearOrder β] (w : α → β) :
    UpperBound (matroidGreedyMaxIndep (α := α) w) List.length id :=
  UpperBound.of_pointwise monotone_id fun oracle xs =>
    countQueries_matroidGreedyMaxIndep_le oracle w xs

/-! ## End-to-end correctness and weighted optimality in the oracle model -/

theorem eval_matroidGreedySelect_isBasis' [DecidableEq α]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (xs : List α) :
    M.IsBasis' (((matroidGreedySelect xs).eval oracle : Finset α) : Set α) {x | x ∈ xs} := by
  rw [eval_matroidGreedySelect]
  exact greedySelect_isBasis' horacle xs

theorem eval_matroidGreedyMaxBasis_isBasis' [DecidableEq α] [LinearOrder β]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (w : α → β) (xs : List α) :
    M.IsBasis' (((matroidGreedyMaxBasis w xs).eval oracle : Finset α) : Set α) {x | x ∈ xs} := by
  rw [eval_matroidGreedyMaxBasis]
  exact greedyMaxBasis_isBasis' horacle w xs

theorem eval_matroidGreedyMinBasis_isBasis' [DecidableEq α] [LinearOrder β]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (w : α → β) (xs : List α) :
    M.IsBasis' (((matroidGreedyMinBasis w xs).eval oracle : Finset α) : Set α) {x | x ∈ xs} := by
  rw [eval_matroidGreedyMinBasis]
  exact greedyMinBasis_isBasis' horacle w xs

theorem sum_le_eval_matroidGreedyMaxBasis [DecidableEq α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (w : α → β) (xs : List α)
    {I : Finset α} (hI : M.IsBasis' (I : Set α) {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ (matroidGreedyMaxBasis w xs).eval oracle, w x := by
  rw [eval_matroidGreedyMaxBasis]
  exact sum_le_greedyMaxBasis horacle w xs hI

theorem eval_matroidGreedyMinBasis_le_sum [DecidableEq α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (w : α → β) (xs : List α)
    {I : Finset α} (hI : M.IsBasis' (I : Set α) {x | x ∈ xs}) :
    ∑ x ∈ (matroidGreedyMinBasis w xs).eval oracle, w x ≤ ∑ x ∈ I, w x := by
  rw [eval_matroidGreedyMinBasis]
  exact greedyMinBasis_le_sum horacle w xs hI

theorem sum_le_eval_matroidGreedyMaxBasis_of_indep [DecidableEq α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (w : α → β) (xs : List α)
    (hnonneg : ∀ x ∈ xs, 0 ≤ w x)
    {I : Finset α} (hI : M.Indep (I : Set α)) (hIsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ (matroidGreedyMaxBasis w xs).eval oracle, w x := by
  rw [eval_matroidGreedyMaxBasis]
  exact sum_le_greedyMaxBasis_of_indep horacle w xs hnonneg hI hIsub

theorem eval_matroidGreedyMaxIndep_indep [DecidableEq α] [Zero β] [LinearOrder β]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (w : α → β) (xs : List α) :
    M.Indep (((matroidGreedyMaxIndep w xs).eval oracle : Finset α) : Set α) := by
  rw [eval_matroidGreedyMaxIndep]
  exact greedyMaxIndep_indep horacle w xs

theorem sum_le_eval_matroidGreedyMaxIndep [DecidableEq α]
    [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {oracle : {ι : Type} → IndepQuery α ι → ι}
    (horacle : IndepQuery.ImplementsMatroid oracle M) (w : α → β) (xs : List α)
    {I : Finset α} (hI : M.Indep (I : Set α)) (hIsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ (matroidGreedyMaxIndep w xs).eval oracle, w x := by
  rw [eval_matroidGreedyMaxIndep]
  exact sum_le_greedyMaxIndep horacle w xs hI hIsub

end Cslib.Query
