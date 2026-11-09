/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import Complexity.Computability.Machines.Turing.MultiTape.BlockComputation.ScheduleReadWindow
public import Complexity.Computability.Machines.Turing.MultiTape.Probabilistic.ExplicitBlockNetwork.Table

/-!
# Streaming the last earlier provider interval

The search retains the binary schedule, target interval and port, a binary cursor and at most one
previous matching index. It visits earlier intervals in increasing order, replacing the saved
index on a match. Window membership is computed by streamed digit counts. No list of indices or
runtime power is allocated.
-/

public section

namespace Turing.MultiTapePTM.BlockComputation.ScheduleRead

/-- Actual schedule number, target interval and target port. -/
abbrev SearchArgs := ℕ × ℕ × ℕ

/-- Retained search arguments, next candidate interval and last matching interval. -/
abbrev SearchState := SearchArgs × ℕ × Option ℕ

/-- Check one candidate and advance the binary cursor, retaining the original arguments. -/
@[expose] def searchStep (k c : ℕ) : SearchState → SearchState :=
  fun (a, j, previous) =>
    let (σ, i, δ) := a
    (a, j + 1, if inWindow k c (σ, i, δ, j) then some j else previous)

/-- Search the earlier intervals without materializing their indices. -/
@[expose] def search (k c : ℕ) (a : SearchArgs) : Option ℕ :=
  let (_, i, _) := a
  let (_, _, previous) := (searchStep k c)^[i] (a, 0, none)
  previous

/-- Every iteration retains the original schedule and target. -/
theorem searchIterate_context (k c : ℕ) (a : SearchArgs) (j : ℕ) :
    ((searchStep k c)^[j] (a, 0, none)).1 = a := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa only [searchStep] using ih

/-- The search cursor equals the number of completed iterations. -/
theorem searchIterate_cursor (k c : ℕ) (a : SearchArgs) (j : ℕ) :
    ((searchStep k c)^[j] (a, 0, none)).2.1 = j := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    simpa only [searchStep] using congrArg Nat.succ ih

/-- The retained option is absent exactly before any match, and otherwise records a greatest
matching candidate among the intervals already visited. -/
theorem searchIterate_spec (k c σ i δ j : ℕ) :
    match ((searchStep k c)^[j] ((σ, i, δ), 0, none)).2.2 with
    | none => ∀ n, n < j → inWindow k c (σ, i, δ, n) = false
    | some n => n < j ∧ inWindow k c (σ, i, δ, n) = true ∧
        ∀ m, m < j → inWindow k c (σ, i, δ, m) = true → m ≤ n := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [Function.iterate_succ_apply']
    change (match (if inWindow k c
      (((searchStep k c)^[j] ((σ, i, δ), 0, none)).1.1,
       ((searchStep k c)^[j] ((σ, i, δ), 0, none)).1.2.1,
       ((searchStep k c)^[j] ((σ, i, δ), 0, none)).1.2.2,
       ((searchStep k c)^[j] ((σ, i, δ), 0, none)).2.1) then
        some (((searchStep k c)^[j] ((σ, i, δ), 0, none)).2.1) else
        ((searchStep k c)^[j] ((σ, i, δ), 0, none)).2.2) with
      | none => _
      | some n => _)
    rw [searchIterate_context, searchIterate_cursor]
    cases hp : inWindow k c (σ, i, δ, j) with
    | true =>
      simp only [hp, ↓reduceIte]
      exact ⟨by omega, trivial, fun m hm _ => by omega⟩
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      cases hl : ((searchStep k c)^[j] ((σ, i, δ), 0, none)).2.2 with
      | none =>
        simp only [hl] at ih ⊢
        intro m hm
        by_cases hmj : m < j
        · exact ih m hmj
        · have : m = j := by omega
          simpa only [this] using hp
      | some n =>
        simp only [hl] at ih ⊢
        refine ⟨by omega, ih.2.1, ?_⟩
        intro m hm hmatch
        by_cases hmj : m < j
        · exact ih.2.2 m hmj hmatch
        · have : m = j := by omega
          rw [this, hp] at hmatch
          contradiction

/-- A retained predecessor is always smaller than the number of visited intervals. -/
theorem searchIterate_latest_bound (k c : ℕ) (a : SearchArgs) (j n : ℕ)
    (h : ((searchStep k c)^[j] (a, 0, none)).2.2 = some n) : n < j := by
  rcases a with ⟨σ, i, δ⟩
  have hs := searchIterate_spec k c σ i δ j
  rw [h] at hs
  exact hs.1

/-- Streaming search computes the existing numeric last-provider operation. -/
theorem search_eq_lastBeforeNum (k c σ i δ : ℕ) :
    search k c (σ, i, δ) = lastBeforeNum k σ c i δ := by
  have hs := searchIterate_spec k c σ i δ i
  change ((searchStep k c)^[i] ((σ, i, δ), 0, none)).2.2 = _
  cases hl : ((searchStep k c)^[i] ((σ, i, δ), 0, none)).2.2 with
  | none =>
    simp only [hl] at hs
    symm
    simp only [lastBeforeNum, Option.map_eq_none_iff, List.find?_eq_none, List.mem_range]
    intro j hj hmatch
    rw [← inWindow_eq, hs (i - 1 - j) (by omega)] at hmatch
    contradiction
  | some n =>
    simp only [hl] at hs
    have hfind : ((List.range i).find? fun j =>
        inWindowNum k σ c i δ (i - 1 - j)) = some (i - 1 - n) := by
      rw [List.find?_range_eq_some]
      refine ⟨?_, List.mem_range.mpr (by omega), ?_⟩
      · rw [show i - 1 - (i - 1 - n) = n by omega, ← inWindow_eq]
        exact hs.2.1
      · intro j hj
        rw [Bool.not_eq_true', Bool.eq_false_iff]
        intro hmatch
        rw [← inWindow_eq] at hmatch
        have hm := hs.2.2 (i - 1 - j) (by omega) hmatch
        omega
    simp only [lastBeforeNum, hfind, Option.map_some]
    congr 1
    omega

/-- The native reader finds exactly the functional schedule's last earlier provider. -/
theorem search_eq_lastBefore {k q : ℕ} (σ : ℕ) (i : Fin q) (h : Fin k) (δ : Fin 3) :
    search k (h + 1) (σ, i, δ) =
      (lastBefore (InWindow (scheduleOfNat k q σ) h
        (portBlock (scheduleOfNat k q σ) i h δ)) i).map Fin.val := by
  rw [search_eq_lastBeforeNum, lastBeforeNum_eq]

end Turing.MultiTapePTM.BlockComputation.ScheduleRead
