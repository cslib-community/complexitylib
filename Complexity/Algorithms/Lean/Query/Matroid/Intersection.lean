/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.Matroid.Intersection.Solver
public import Complexity.Algorithms.Lean.Query.FreeM.FilterM
public import Complexity.Algorithms.Lean.Query.Matroid.IndepQuery
public import Cslib.Algorithms.Lean.Query.Bounds
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Order.Interval.Finset.Nat
import Complexity.Foundations.Data.List.EraseDups
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.LocallyFinite
import Mathlib.Tactic.Ring

/-!
# Matroid intersection in the independence-oracle model

This module runs the matroid intersection algorithm of
`Complexity.Algorithms.Lean.Matroid.Intersection.Solver` in `FreeM (IndepPairQuery α)`, the query
model with one independence oracle for each matroid, and counts the oracle calls with
`FreeM.countQueries`. Breadth-first search and list bookkeeping are host computation and are not
charged here; only the independence tests are.

On `n` distinct candidates, a phase from a common independent set `I` makes exactly
`2 * (n - |I|) * (1 + |I|)` tests: `n - |I|` for the sources, as many for the sinks, and one per
pair `(x, y) ∈ I × (E \ I)` for each matroid (`countQueries_exchTablesM_of_nodup`). For any
oracles, at most `n + 1` phases give at most `2n(n + 1)²` tests (`matroidIntersection_upperBound`).
When the oracles implement matroids, the phases run from `|I| = 0` to `|I| = ν`, the maximum size
of a common independent set, so the count is exactly `∑_{r = 0}^{ν} 2(n - r)(1 + r)`
(`countQueries_matroidIntersection`), at most `2n(ν + 1)²`
(`countQueries_matroidIntersection_le`).

The query bounds are for this implementation, which rebuilds the exchange digraph from scratch in
every phase. [Schrijver2017], Theorem 10.8 states only that the algorithm runs in polynomial time.

## Main definitions

* `Cslib.Query.IndepPairQuery`: independence queries to two matroids, `IndepQuery α` on each side.
* `Cslib.Query.IndepPairQuery.ask₁`, `ask₂`: the two queries.
* `Cslib.Query.IndepPairQuery.left`, `right`, `pair`: an oracle for the pair, seen as two
  `IndepQuery α` oracles, and conversely.
* `Cslib.Query.matroidIntersection`: the algorithm as a query program.

## Main results

* `Cslib.Query.eval_matroidIntersection`: evaluation agrees with the pure algorithm.
* `Cslib.Query.eval_matroidIntersection_spec`: for oracles implementing `M₁` and `M₂`, the
  output is a maximum common independent set with a separator.
* `Cslib.Query.countQueries_exchTablesM_of_nodup`: the exact number of tests in one phase.
* `Cslib.Query.matroidIntersection_upperBound`: `UpperBound` with bound `2n(n + 1)²`, for all
  oracles.
* `Cslib.Query.countQueries_matroidIntersection`,
  `Cslib.Query.countQueries_matroidIntersection_le`: the exact, output-sensitive count and its
  bound `2n(ν + 1)²` for oracles implementing matroids.

## References

* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], Section 10.5
-/

public section

open Cslib.Algorithms.Lean.Matroid
open Cslib.Reachability
open scoped symmDiff

namespace Cslib.Query

variable {α : Type}

/-! ### Two independence oracles -/

/-- Independence queries to two matroids: `.inl (.indep S)` asks whether `S` is independent in
the first, `.inr (.indep S)` whether it is independent in the second. -/
abbrev IndepPairQuery (α : Type) (ι : Type) : Type := IndepQuery α ι ⊕ IndepQuery α ι

namespace IndepPairQuery

/-- Ask whether `S` is independent in the first matroid. -/
abbrev ask₁ (S : Finset α) : FreeM (IndepPairQuery α) Bool := FreeM.lift (.inl (.indep S))

/-- Ask whether `S` is independent in the second matroid. -/
abbrev ask₂ (S : Finset α) : FreeM (IndepPairQuery α) Bool := FreeM.lift (.inr (.indep S))

/-- The first-matroid part of an oracle for the pair. -/
@[expose] def left (oracle : {ι : Type} → IndepPairQuery α ι → ι) :
    {ι : Type} → IndepQuery α ι → ι :=
  fun q => oracle (.inl q)

/-- The second-matroid part of an oracle for the pair. -/
@[expose] def right (oracle : {ι : Type} → IndepPairQuery α ι → ι) :
    {ι : Type} → IndepQuery α ι → ι :=
  fun q => oracle (.inr q)

/-- The oracle for the pair answering with `oracle₁` on the left and `oracle₂` on the right. -/
@[expose] def pair (oracle₁ oracle₂ : {ι : Type} → IndepQuery α ι → ι) :
    {ι : Type} → IndepPairQuery α ι → ι
  | _, .inl q => oracle₁ q
  | _, .inr q => oracle₂ q

@[simp] theorem left_pair (oracle₁ oracle₂ : {ι : Type} → IndepQuery α ι → ι) {ι : Type}
    (q : IndepQuery α ι) : left (pair oracle₁ oracle₂) q = oracle₁ q := rfl

@[simp] theorem right_pair (oracle₁ oracle₂ : {ι : Type} → IndepQuery α ι → ι) {ι : Type}
    (q : IndepQuery α ι) : right (pair oracle₁ oracle₂) q = oracle₂ q := rfl

end IndepPairQuery

open IndepPairQuery

/-! ### The query program -/

/-- **Matroid intersection** in the two-oracle query model: `maxCommonIndepM` with the
independence tests answered by the two oracles. -/
@[expose] def matroidIntersection [DecidableEq α] (es : List α) :
    FreeM (IndepPairQuery α) (Finset α × Finset α) :=
  maxCommonIndepM ask₁ ask₂ es

@[simp] theorem eval_exchTablesM [DecidableEq α] (oracle : {ι : Type} → IndepPairQuery α ι → ι)
    (V : List α) (I : Finset α) :
    (exchTablesM ask₁ ask₂ V I).eval oracle =
      exchTables (fun S => oracle (.inl (.indep S))) (fun S => oracle (.inr (.indep S))) V I :=
  Id.pure_injective <| by
    simpa using (FreeM.isMonadHom_pure_eval oracle).map_exchTablesM ask₁ ask₂ V I

/-- Evaluating the query program is running the pure algorithm with the oracles' answers. -/
@[simp] theorem eval_matroidIntersection [DecidableEq α]
    (oracle : {ι : Type} → IndepPairQuery α ι → ι) (es : List α) :
    (matroidIntersection es).eval oracle =
      maxCommonIndep (fun S => oracle (.inl (.indep S))) (fun S => oracle (.inr (.indep S))) es :=
  Id.pure_injective <| by
    simpa [matroidIntersection] using
      (FreeM.isMonadHom_pure_eval oracle).map_maxCommonIndepM ask₁ ask₂ es

/-- **Correctness in the oracle model**: if the two oracles implement `M₁` and `M₂`, the program
returns `(I, U)` with `I` a maximum common independent subset of `E = es.toFinset`, `U ⊆ E`, and
`I.card = M₁.eRk U + M₂.eRk (E \ U)`. -/
theorem eval_matroidIntersection_spec [DecidableEq α] {M₁ M₂ : Matroid α}
    {oracle : {ι : Type} → IndepPairQuery α ι → ι}
    (h₁ : IndepQuery.ImplementsMatroid (left oracle) M₁)
    (h₂ : IndepQuery.ImplementsMatroid (right oracle) M₂) (es : List α) :
    IsMaxCommonIndep M₁ M₂ es.toFinset ((matroidIntersection es).eval oracle).1 ∧
      ((matroidIntersection es).eval oracle).2 ⊆ es.toFinset ∧
      (((matroidIntersection es).eval oracle).1.card : ℕ∞) =
        M₁.eRk (((matroidIntersection es).eval oracle).2 : Set α) +
          M₂.eRk ((es.toFinset \ ((matroidIntersection es).eval oracle).2 : Finset α) :
            Set α) := by
  rw [eval_matroidIntersection]
  exact maxCommonIndep_spec h₁ h₂ es

/-! ### Query counts -/

/-- One phase from `I` makes `2 * |V \ I| * (1 + |V ∩ I|)` independence tests, whatever the
oracle answers. -/
theorem countQueries_exchTablesM [DecidableEq α] (oracle : {ι : Type} → IndepPairQuery α ι → ι)
    (V : List α) (I : Finset α) :
    (exchTablesM ask₁ ask₂ V I).countQueries oracle =
      2 * (V.filter (· ∉ I)).length * (1 + (V.filter (· ∈ I)).length) := by
  have hq₁ : ∀ S, (ask₁ (α := α) S).countQueries oracle = 1 := fun _ => rfl
  have hq₂ : ∀ S, (ask₂ (α := α) S).countQueries oracle = 1 := fun _ => rfl
  simp only [exchTablesM, FreeM.countQueries_bind, FreeM.countQueries_pure,
    FreeM.countQueries_filterM_of_eq_one oracle (fun _ => hq₁ _),
    FreeM.countQueries_filterM_of_eq_one oracle (fun _ => hq₂ _),
    length_exchPairs]
  ring

/-- **Exact cost of a phase**: on duplicate-free candidates `V` with `n` elements, a phase from
`I ⊆ V` makes `2 * (n - |I|) * (1 + |I|)` independence tests. -/
theorem countQueries_exchTablesM_of_nodup [DecidableEq α]
    (oracle : {ι : Type} → IndepPairQuery α ι → ι) {V : List α} (hV : V.Nodup) {I : Finset α}
    (hIV : I ⊆ V.toFinset) :
    (exchTablesM ask₁ ask₂ V I).countQueries oracle =
      2 * (V.length - I.card) * (1 + I.card) := by
  have hin : (V.filter (· ∈ I)).length = I.card := by
    rw [← List.toFinset_card_of_nodup (hV.filter _), List.toFinset_filter]
    congr 1
    ext x
    simp only [Finset.mem_filter, List.mem_toFinset, decide_eq_true_eq]
    exact ⟨fun h => h.2, fun h => ⟨List.mem_toFinset.mp (hIV h), h⟩⟩
  have hsplit := List.length_eq_length_filter_add (l := V) (fun x => decide (x ∈ I))
  have hout : (V.filter (· ∉ I)).length = V.length - I.card := by
    have : (V.filter (· ∉ I)) = V.filter (fun x => !decide (x ∈ I)) := by
      congr 1
    rw [this]
    omega
  rw [countQueries_exchTablesM, hin, hout]

private theorem countQueries_maxCommonIndepLoopM_le [DecidableEq α]
    (oracle : {ι : Type} → IndepPairQuery α ι → ι) (V : List α) :
    ∀ (fuel : ℕ) (I : Finset α), (maxCommonIndepLoopM ask₁ ask₂ V fuel I).countQueries oracle ≤
      fuel * (2 * V.length * (1 + V.length)) := by
  intro fuel
  induction fuel with
  | zero => intro I; simp [maxCommonIndepLoopM]
  | succ fuel ih =>
    intro I
    have hphase : (exchTablesM ask₁ ask₂ V I).countQueries oracle ≤
        2 * V.length * (1 + V.length) := by
      rw [countQueries_exchTablesM]
      have h₁ := (List.filter_sublist (p := fun x => decide (x ∉ I)) (l := V)).length_le
      have h₂ := (List.filter_sublist (p := fun x => decide (x ∈ I)) (l := V)).length_le
      gcongr
    simp only [maxCommonIndepLoopM, FreeM.countQueries_bind]
    split
    · next p _ =>
      have := ih (I ∆ p.toFinset)
      rw [Nat.succ_mul]
      omega
    · simp only [FreeM.countQueries_pure]
      rw [Nat.succ_mul]
      omega

/-- **Oracle-independent query bound**: on lists of length at most `n`, `matroidIntersection`
makes at most `2n(n + 1)²` independence queries, whatever the oracles answer. -/
theorem matroidIntersection_upperBound [DecidableEq α] :
    UpperBound (matroidIntersection (α := α)) List.length fun n => 2 * n * (n + 1) ^ 2 := by
  refine UpperBound.of_pointwise
    (fun a b hab => Nat.mul_le_mul (Nat.mul_le_mul_left 2 hab) (Nat.pow_le_pow_left (by omega) 2))
    fun oracle es => ?_
  have hle : es.eraseDups.length ≤ es.length := (List.eraseDups_sublist es).length_le
  calc (matroidIntersection es).countQueries oracle
      ≤ (es.eraseDups.length + 1) * (2 * es.eraseDups.length * (1 + es.eraseDups.length)) :=
        countQueries_maxCommonIndepLoopM_le oracle _ _ _
    _ ≤ (es.length + 1) * (2 * es.length * (1 + es.length)) := by gcongr
    _ = 2 * es.length * (es.length + 1) ^ 2 := by ring

private theorem countQueries_maxCommonIndepLoopM_eq [DecidableEq α] {M₁ M₂ : Matroid α}
    {oracle : {ι : Type} → IndepPairQuery α ι → ι}
    (h₁ : IndepQuery.ImplementsMatroid (left oracle) M₁)
    (h₂ : IndepQuery.ImplementsMatroid (right oracle) M₂) {V : List α} (hV : V.Nodup) :
    ∀ (fuel : ℕ) (I : Finset α), I ⊆ V.toFinset → IsCommonIndep M₁ M₂ I →
      V.toFinset.card - I.card < fuel →
      I.card ≤ ((maxCommonIndepLoopM ask₁ ask₂ V fuel I).eval oracle).1.card ∧
      (maxCommonIndepLoopM ask₁ ask₂ V fuel I).countQueries oracle =
        ∑ r ∈ Finset.Ico I.card
          (((maxCommonIndepLoopM ask₁ ask₂ V fuel I).eval oracle).1.card + 1),
          2 * (V.length - r) * (1 + r) := by
  intro fuel
  induction fuel with
  | zero => intro I _ _ h; omega
  | succ fuel ih =>
    intro I hIV hI hfuel
    have hphase := countQueries_exchTablesM_of_nodup oracle hV hIV
    have heval : ∀ fuel' I', (maxCommonIndepLoopM ask₁ ask₂ V fuel' I').eval oracle =
        maxCommonIndepLoop (fun S => oracle (.inl (.indep S))) (fun S => oracle (.inr (.indep S)))
          V fuel' I' := fun fuel' I' => Id.pure_injective <| by
      simpa using (FreeM.isMonadHom_pure_eval oracle).map_maxCommonIndepLoopM ask₁ ask₂ V fuel' I'
    simp only [heval] at ih ⊢
    simp only [maxCommonIndepLoopM, maxCommonIndepLoop, FreeM.countQueries_bind, eval_exchTablesM,
      hphase]
    rcases hs : exchSearch V
      (exchTables (fun S => oracle (.inl (.indep S))) (fun S => oracle (.inr (.indep S))) V I)
      with p | R
    · dsimp only
      obtain ⟨hI'V, hI', hcard⟩ := augment_of_exchSearch_eq_inl h₁ h₂ hIV hs
      have hle := Finset.card_le_card hI'V
      obtain ⟨hmono, hcount⟩ := ih _ hI'V hI' (by omega)
      refine ⟨by omega, ?_⟩
      rw [hcount, hcard, Finset.sum_eq_sum_Ico_succ_bot (a := I.card) (by omega)]
    · dsimp only
      simp only [FreeM.countQueries_pure, add_zero]
      refine ⟨le_rfl, ?_⟩
      rw [Nat.Ico_succ_singleton, Finset.sum_singleton]

/-- **Exact output-sensitive query count**: if the oracles implement `M₁` and `M₂` and `es` has
`n` distinct elements, `matroidIntersection es` makes exactly `∑_{r=0}^{ν} 2(n - r)(1 + r)`
independence queries, where `ν` is the size of the returned maximum common independent set. -/
theorem countQueries_matroidIntersection [DecidableEq α] {M₁ M₂ : Matroid α}
    {oracle : {ι : Type} → IndepPairQuery α ι → ι}
    (h₁ : IndepQuery.ImplementsMatroid (left oracle) M₁)
    (h₂ : IndepQuery.ImplementsMatroid (right oracle) M₂) (es : List α) :
    (matroidIntersection es).countQueries oracle =
      ∑ r ∈ Finset.range (((matroidIntersection es).eval oracle).1.card + 1),
        2 * (es.toFinset.card - r) * (1 + r) := by
  have h := (countQueries_maxCommonIndepLoopM_eq h₁ h₂ (List.nodup_eraseDups es)
    (es.eraseDups.length + 1) ∅ (Finset.empty_subset _) (isCommonIndep_empty M₁ M₂)
    (by rw [List.length_eraseDups, List.toFinset_eraseDups]; omega)).2
  rw [Finset.card_empty, ← Finset.range_eq_Ico] at h
  simp only [matroidIntersection, maxCommonIndepM]
  rw [List.length_eraseDups] at h ⊢
  exact h

/-- **Output-sensitive query bound**: if the oracles implement `M₁` and `M₂` and `es` has `n`
distinct elements, `matroidIntersection es` makes at most `2n(ν + 1)²` independence queries, where
`ν` is the maximum size of a common independent subset of `es`. -/
theorem countQueries_matroidIntersection_le [DecidableEq α] {M₁ M₂ : Matroid α}
    {oracle : {ι : Type} → IndepPairQuery α ι → ι}
    (h₁ : IndepQuery.ImplementsMatroid (left oracle) M₁)
    (h₂ : IndepQuery.ImplementsMatroid (right oracle) M₂) (es : List α) :
    (matroidIntersection es).countQueries oracle ≤
      2 * es.toFinset.card * (((matroidIntersection es).eval oracle).1.card + 1) ^ 2 := by
  rw [countQueries_matroidIntersection h₁ h₂]
  set ν := ((matroidIntersection es).eval oracle).1.card
  calc ∑ r ∈ Finset.range (ν + 1), 2 * (es.toFinset.card - r) * (1 + r)
      ≤ ∑ _r ∈ Finset.range (ν + 1), 2 * es.toFinset.card * (ν + 1) := by
        refine Finset.sum_le_sum fun r hr => ?_
        have hr : r < ν + 1 := Finset.mem_range.mp hr
        exact Nat.mul_le_mul (by omega) (by omega)
    _ = 2 * es.toFinset.card * (ν + 1) ^ 2 := by
        rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
        ring

end Cslib.Query
