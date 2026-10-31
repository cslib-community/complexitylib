/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Submodular.Basic
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Analysis.Complex.Exponential
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Greedy Cardinality-Constrained Submodular Maximization

This module formalizes the Nemhauser–Wolsey–Fisher greedy algorithm for maximizing a monotone
submodular set function `f : Finset α → β` over a finite ground list `xs : List α` subject to a
cardinality constraint `|S| ≤ k` ([NemhauserWolseyFisher1978], Section 4, Theorem 4.2), together
with its exact `1 - (1 - 1/k)^k` tightness family for every budget `k ≥ 1`
([NemhauserWolsey1978], Section 3; [NemhauserWolseyFisher1978], Section 4, Theorem 4.1(c) and
Theorem 4.2, pp. 280–283).

## Algorithm design

1. First-occurrence deduplication `dedupFirst xs` produces the ordered list `u` of distinct ground
   elements once upfront (`u.length = xs.toFinset.card`).
2. Each greedy round filters `u` to candidates `c ∉ S`. If none remain, `S` is returned unchanged
   with zero oracle evaluations. Otherwise, maximizing `marginalGain f S c = f (insert c S) - f S`
   for fixed `S` is equivalent to maximizing `f (insert c S)`, so the algorithm needs only
   `[DecidableEq α] [LinearOrder β]` (no subtraction in the algorithm itself) and breaks ties in
   favor of earlier candidates (`bestVal < v`).
3. Monadic (`submodularGreedyM`) and pure (`submodularGreedy`) presentations are connected by
   `@[simp]` `pure`/`Id.run` lemmas and `@[grind .] IsMonadHom` naturality bridges so the same
   correctness and approximation theorems transfer directly to the `FreeM (ValueQuery α β)` query
   tree.

## Main definitions

* `Cslib.Algorithms.Lean.Submodular.dedupFirst`: order-preserving first-occurrence deduplication.
* `Cslib.Algorithms.Lean.Submodular.submodularGreedyM`,
  `Cslib.Algorithms.Lean.Submodular.submodularGreedy`: monadic and pure `k`-step greedy algorithms.
* `Cslib.Algorithms.Lean.Submodular.tightCandidates`,
  `Cslib.Algorithms.Lean.Submodular.tightObjective`,
  `Cslib.Algorithms.Lean.Submodular.tightOpt`: the `2k`-element witness family showing exact
  tightness of `1 - (1 - 1/k)^k`.

## Main results

* `submodularGreedy_subset_toFinset`, `card_submodularGreedy_eq_min`, `card_submodularGreedy_le`:
  feasibility and exact output cardinality `min k xs.toFinset.card`.
* `one_sub_pow_mul_le_submodularGreedy_steps`, `one_sub_pow_mul_le_submodularGreedy`:
  `(1 - (1 - 1 / (k : β)) ^ m) * f OPT ≤ f (submodularGreedy f xs m)` over any
  `[Field β] [LinearOrder β] [IsStrictOrderedRing β]` (`ℚ`, `ℝ`, …).
* `one_sub_exp_neg_div_mul_le_submodularGreedy`, `one_sub_exp_neg_one_mul_le_submodularGreedy`:
  `(1 - Real.exp (-1)) * f OPT ≤ f (submodularGreedy f xs k)` over `ℝ` for every `k : ℕ`.
* `submodularGreedy_tightObjective_eq`, `exists_tight_submodularGreedy`: for every `k ≥ 1`, there
  exists a nonnegative monotone submodular objective on `2k` elements with `f ∅ = 0`, `f OPT = 1`
  (`|OPT| = k`), and `f (submodularGreedy f xs k) = 1 - (1 - 1 / (k : β)) ^ k`.

## References

* [NemhauserWolseyFisher1978] George L. Nemhauser, Laurence A. Wolsey, and Marshall L. Fisher,
  *An Analysis of Approximations for Maximizing Submodular Set Functions—I*, 1978.
* [NemhauserWolsey1978] George L. Nemhauser and Laurence A. Wolsey,
  *Best Algorithms for Approximating the Maximum of a Submodular Set Function*, 1978.
-/

public section

open Cslib (IsMonadHom)

namespace Cslib.Algorithms.Lean.Submodular

/-! ## First-occurrence deduplication -/

/-- Keep the first occurrence of each distinct element in `xs`, preserving left-to-right order
(structurally recursive `[DecidableEq α]` counterpart of `List.eraseDups`). -/
@[expose] def dedupFirst {α : Type*} [DecidableEq α] : List α → List α
  | [] => []
  | x :: xs => x :: (dedupFirst xs).filter (· ≠ x)

@[simp] theorem dedupFirst_nil {α : Type*} [DecidableEq α] :
    dedupFirst ([] : List α) = [] := rfl

@[simp] theorem dedupFirst_cons {α : Type*} [DecidableEq α] (x : α) (xs : List α) :
    dedupFirst (x :: xs) = x :: (dedupFirst xs).filter (· ≠ x) := rfl

@[simp] theorem mem_dedupFirst {α : Type*} [DecidableEq α] {xs : List α} {a : α} :
    a ∈ dedupFirst xs ↔ a ∈ xs := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    simp only [dedupFirst_cons, List.mem_cons, List.mem_filter, ne_eq, ih]
    by_cases hax : a = x <;> simp [hax]

theorem nodup_dedupFirst {α : Type*} [DecidableEq α] (xs : List α) :
    (dedupFirst xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    rw [dedupFirst_cons, List.nodup_cons]
    exact ⟨by simp, ih.filter _⟩

theorem dedupFirst_eq_self {α : Type*} [DecidableEq α] {xs : List α} (h : xs.Nodup) :
    dedupFirst xs = xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rcases List.nodup_cons.mp h with ⟨hx, hxs⟩
    rw [dedupFirst_cons, ih hxs]
    congr 1
    refine List.filter_eq_self.mpr fun y hy => decide_eq_true ?_
    rintro rfl
    exact hx hy

@[simp] theorem toFinset_dedupFirst {α : Type*} [DecidableEq α] (xs : List α) :
    (dedupFirst xs).toFinset = xs.toFinset := by
  ext a
  simp

theorem length_dedupFirst {α : Type*} [DecidableEq α] (xs : List α) :
    (dedupFirst xs).length = xs.toFinset.card := by
  rw [← toFinset_dedupFirst xs, List.toFinset_card_of_nodup (nodup_dedupFirst xs)]

theorem length_dedupFirst_le {α : Type*} [DecidableEq α] (xs : List α) :
    (dedupFirst xs).length ≤ xs.length := by
  rw [length_dedupFirst]
  exact List.toFinset_card_le xs

/-! ## Monadic and pure greedy algorithm -/

section Algorithm

/-- Pure left-to-right scan selecting the first candidate achieving the maximum of
`f (insert c S)`. -/
@[expose] def scanCandidates {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (f : Finset α → β) (S : Finset α) (best : α) (bestVal : β) : List α → α × β
  | [] => (best, bestVal)
  | c :: cs =>
    let v := f (insert c S)
    if bestVal < v then
      scanCandidates f S c v cs
    else
      scanCandidates f S best bestVal cs

/-- One pure greedy round over distinct ground list `u`: inserts the remaining element `c ∉ S`
maximizing `f (insert c S)` (breaking ties toward earlier elements of `u`), or returns `S` if no
candidate remains. -/
@[expose] def submodularGreedyStep {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (f : Finset α → β) (u : List α) (S : Finset α) : Finset α :=
  match u.filter (· ∉ S) with
  | [] => S
  | c₀ :: cs => insert (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 S

/-- Tail-recursive `k`-step pure greedy loop over deduplicated ground list `u`. -/
@[expose] def submodularGreedyLoop {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (f : Finset α → β) (u : List α) : ℕ → Finset α → Finset α
  | 0, S => S
  | k + 1, S => submodularGreedyLoop f u k (submodularGreedyStep f u S)

/-- Pure `k`-step Nemhauser–Wolsey–Fisher greedy algorithm on ground list `xs`. -/
@[expose] def submodularGreedy {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (f : Finset α → β) (xs : List α) (k : ℕ) : Finset α :=
  submodularGreedyLoop f (dedupFirst xs) k ∅

/-- Monadic left-to-right scan evaluating `evalSet (insert c S)` once per candidate in `cs`. -/
@[expose] def scanCandidatesM {α : Type} {β : Type} {m : Type → Type*} [Monad m]
    [DecidableEq α] [LinearOrder β]
    (evalSet : Finset α → m β) (S : Finset α) (best : α) (bestVal : β) : List α → m (α × β)
  | [] => return (best, bestVal)
  | c :: cs => do
    let v ← evalSet (insert c S)
    if bestVal < v then
      scanCandidatesM evalSet S c v cs
    else
      scanCandidatesM evalSet S best bestVal cs

/-- One monadic greedy round over deduplicated ground list `u`. -/
@[expose] def submodularGreedyStepM {α : Type} {β : Type} {m : Type → Type*} [Monad m]
    [DecidableEq α] [LinearOrder β]
    (evalSet : Finset α → m β) (u : List α) (S : Finset α) : m (Finset α) :=
  match u.filter (· ∉ S) with
  | [] => return S
  | c₀ :: cs => do
    let v₀ ← evalSet (insert c₀ S)
    let p ← scanCandidatesM evalSet S c₀ v₀ cs
    return insert p.1 S

/-- Monadic `k`-step greedy loop over deduplicated ground list `u`. -/
@[expose] def submodularGreedyLoopM {α : Type} {β : Type} {m : Type → Type*} [Monad m]
    [DecidableEq α] [LinearOrder β]
    (evalSet : Finset α → m β) (u : List α) : ℕ → Finset α → m (Finset α)
  | 0, S => return S
  | k + 1, S => do
    let S' ← submodularGreedyStepM evalSet u S
    submodularGreedyLoopM evalSet u k S'

/-- Monadic `k`-step Nemhauser–Wolsey–Fisher greedy algorithm with value-oracle callback
`evalSet : Finset α → m β`. -/
@[expose] def submodularGreedyM {α : Type} {β : Type} {m : Type → Type*} [Monad m]
    [DecidableEq α] [LinearOrder β]
    (evalSet : Finset α → m β) (xs : List α) (k : ℕ) : m (Finset α) :=
  submodularGreedyLoopM evalSet (dedupFirst xs) k ∅

/-! ### Monad homomorphism and `pure`/`Id.run` bridges -/

section Bridges

variable {α : Type} {β : Type} [DecidableEq α] [LinearOrder β]
  {m : Type → Type*} {n : Type → Type*} [Monad m] [Monad n]

@[simp] theorem scanCandidatesM_pure [LawfulMonad m]
    (f : Finset α → β) (S : Finset α) (best : α) (bestVal : β) (cs : List α) :
    scanCandidatesM (fun T => (pure (f T) : m β)) S best bestVal cs =
      pure (scanCandidates f S best bestVal cs) := by
  induction cs generalizing best bestVal with
  | nil => rfl
  | cons c cs ih =>
    simp only [scanCandidatesM, scanCandidates, pure_bind]
    split_ifs <;> exact ih _ _

@[simp] theorem submodularGreedyStepM_pure [LawfulMonad m]
    (f : Finset α → β) (u : List α) (S : Finset α) :
    submodularGreedyStepM (fun T => (pure (f T) : m β)) u S =
      pure (submodularGreedyStep f u S) := by
  unfold submodularGreedyStepM submodularGreedyStep
  cases u.filter (· ∉ S) with
  | nil => rfl
  | cons c₀ cs => simp [scanCandidatesM_pure]

@[simp] theorem submodularGreedyLoopM_pure [LawfulMonad m]
    (f : Finset α → β) (u : List α) (k : ℕ) (S : Finset α) :
    submodularGreedyLoopM (fun T => (pure (f T) : m β)) u k S =
      pure (submodularGreedyLoop f u k S) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp [submodularGreedyLoopM, submodularGreedyLoop, submodularGreedyStepM_pure, ih]

@[simp] theorem submodularGreedyM_pure [LawfulMonad m]
    (f : Finset α → β) (xs : List α) (k : ℕ) :
    submodularGreedyM (fun T => (pure (f T) : m β)) xs k =
      pure (submodularGreedy f xs k) :=
  submodularGreedyLoopM_pure f (dedupFirst xs) k ∅

@[simp] theorem idRun_submodularGreedyM
    (evalSet : Finset α → Id β) (xs : List α) (k : ℕ) :
    Id.run (submodularGreedyM evalSet xs k) =
      submodularGreedy (fun T => Id.run (evalSet T)) xs k :=
  submodularGreedyM_pure (m := Id) (fun T => Id.run (evalSet T)) xs k

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_scanCandidatesM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (evalSet : Finset α → m β) (S : Finset α) (best : α) (bestVal : β) (cs : List α) :
    φ (scanCandidatesM evalSet S best bestVal cs) =
      scanCandidatesM (fun T => φ (evalSet T)) S best bestVal cs := by
  induction cs generalizing best bestVal with
  | nil => simp [scanCandidatesM, hφ.map_pure]
  | cons c cs ih =>
    simp only [scanCandidatesM, hφ.map_bind]
    congr 1
    funext v
    split_ifs <;> exact ih _ _

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_submodularGreedyStepM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (evalSet : Finset α → m β) (u : List α) (S : Finset α) :
    φ (submodularGreedyStepM evalSet u S) =
      submodularGreedyStepM (fun T => φ (evalSet T)) u S := by
  unfold submodularGreedyStepM
  cases u.filter (· ∉ S) with
  | nil => simp [hφ.map_pure]
  | cons c₀ cs =>
    simp only [hφ.map_bind]
    congr 1
    funext v₀
    rw [hφ.map_scanCandidatesM]
    congr 1
    funext p
    exact hφ.map_pure _

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_submodularGreedyLoopM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (evalSet : Finset α → m β) (u : List α) (k : ℕ) (S : Finset α) :
    φ (submodularGreedyLoopM evalSet u k S) =
      submodularGreedyLoopM (fun T => φ (evalSet T)) u k S := by
  induction k generalizing S with
  | zero => simp [submodularGreedyLoopM, hφ.map_pure]
  | succ k ih =>
    simp only [submodularGreedyLoopM, hφ.map_bind, hφ.map_submodularGreedyStepM]
    congr 1
    funext S'
    exact ih S'

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_submodularGreedyM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (evalSet : Finset α → m β) (xs : List α) (k : ℕ) :
    φ (submodularGreedyM evalSet xs k) =
      submodularGreedyM (fun T => φ (evalSet T)) xs k :=
  hφ.map_submodularGreedyLoopM evalSet (dedupFirst xs) k ∅

end Bridges

end Algorithm

/-! ## Scan invariants, feasibility, and exact output cardinality -/

section Feasibility

variable {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]

theorem scanCandidates_snd_eq (f : Finset α → β) (S : Finset α)
    {best : α} {bestVal : β} (hval : bestVal = f (insert best S)) (cs : List α) :
    (scanCandidates f S best bestVal cs).2 =
      f (insert (scanCandidates f S best bestVal cs).1 S) := by
  induction cs generalizing best bestVal with
  | nil => exact hval
  | cons c cs ih =>
    simp only [scanCandidates]
    split_ifs with hlt
    · exact ih rfl
    · exact ih hval

theorem scanCandidates_fst_mem (f : Finset α → β) (S : Finset α)
    (best : α) (bestVal : β) (cs : List α) :
    (scanCandidates f S best bestVal cs).1 ∈ best :: cs := by
  induction cs generalizing best bestVal with
  | nil => simp [scanCandidates]
  | cons c cs ih =>
    simp only [scanCandidates]
    split_ifs with hlt
    · exact List.mem_cons_of_mem best (ih c (f (insert c S)))
    · rcases List.mem_cons.mp (ih best bestVal) with h | h
      · exact List.mem_cons.mpr (Or.inl h)
      · exact List.mem_cons_of_mem best (List.mem_cons_of_mem c h)

theorem le_scanCandidates_snd (f : Finset α → β) (S : Finset α)
    (best : α) (bestVal : β) (cs : List α) :
    bestVal ≤ (scanCandidates f S best bestVal cs).2 := by
  induction cs generalizing best bestVal with
  | nil => exact le_rfl
  | cons c cs ih =>
    simp only [scanCandidates]
    split_ifs with hlt
    · exact hlt.le.trans (ih c (f (insert c S)))
    · exact ih best bestVal

theorem forall_le_scanCandidates_snd (f : Finset α → β) (S : Finset α)
    (best : α) (bestVal : β) (cs : List α) :
    ∀ x ∈ cs, f (insert x S) ≤ (scanCandidates f S best bestVal cs).2 := by
  induction cs generalizing best bestVal with
  | nil => intro _ hx; cases hx
  | cons c cs ih =>
    intro x hx
    simp only [scanCandidates]
    rcases List.mem_cons.mp hx with rfl | hx_cs
    · split_ifs with hlt
      · exact le_scanCandidates_snd f S x (f (insert x S)) cs
      · exact (not_lt.mp hlt).trans (le_scanCandidates_snd f S best bestVal cs)
    · split_ifs with hlt
      · exact ih c (f (insert c S)) x hx_cs
      · exact ih best bestVal x hx_cs

theorem scanCandidates_eq_of_forall_le (f : Finset α → β) (S : Finset α)
    (best : α) (bestVal : β) {cs : List α}
    (h : ∀ c ∈ cs, f (insert c S) ≤ bestVal) :
    scanCandidates f S best bestVal cs = (best, bestVal) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    have hc : ¬ bestVal < f (insert c S) := not_lt.mpr (h c List.mem_cons_self)
    simp only [scanCandidates, hc, ↓reduceIte]
    exact ih fun y hy => h y (List.mem_cons_of_mem c hy)

@[simp] theorem submodularGreedyLoop_zero (f : Finset α → β) (u : List α) (S : Finset α) :
    submodularGreedyLoop f u 0 S = S := rfl

theorem submodularGreedyLoop_succ_right (f : Finset α → β) (u : List α) (m : ℕ) (S : Finset α) :
    submodularGreedyLoop f u (m + 1) S =
      submodularGreedyStep f u (submodularGreedyLoop f u m S) := by
  induction m generalizing S with
  | zero => rfl
  | succ m ih =>
    simp only [submodularGreedyLoop]
    exact ih (submodularGreedyStep f u S)

@[simp] theorem submodularGreedy_zero (f : Finset α → β) (xs : List α) :
    submodularGreedy f xs 0 = ∅ := rfl

theorem submodularGreedy_succ (f : Finset α → β) (xs : List α) (m : ℕ) :
    submodularGreedy f xs (m + 1) =
      submodularGreedyStep f (dedupFirst xs) (submodularGreedy f xs m) :=
  submodularGreedyLoop_succ_right f (dedupFirst xs) m ∅

theorem subset_submodularGreedyStep (f : Finset α → β) (u : List α) (S : Finset α) :
    S ⊆ submodularGreedyStep f u S := by
  unfold submodularGreedyStep
  cases u.filter (· ∉ S) with
  | nil => exact Finset.Subset.refl S
  | cons c₀ cs => exact Finset.subset_insert _ S

theorem submodularGreedyStep_subset_toFinset (f : Finset α → β) {u : List α} {S : Finset α}
    (hS : S ⊆ u.toFinset) :
    submodularGreedyStep f u S ⊆ u.toFinset := by
  unfold submodularGreedyStep
  cases hfilt : u.filter (· ∉ S) with
  | nil => exact hS
  | cons c₀ cs =>
    have hmem : (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 ∈ c₀ :: cs :=
      scanCandidates_fst_mem f S c₀ (f (insert c₀ S)) cs
    rw [← hfilt] at hmem
    have hu : (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 ∈ u.toFinset :=
      List.mem_toFinset.mpr (List.mem_of_mem_filter hmem)
    exact Finset.insert_subset hu hS

theorem submodularGreedyStep_max (f : Finset α → β) (u : List α) (S : Finset α)
    {x : α} (hxu : x ∈ u) (hxS : x ∉ S) :
    f (insert x S) ≤ f (submodularGreedyStep f u S) := by
  have hx_filt : x ∈ u.filter (· ∉ S) :=
    List.mem_filter.mpr ⟨hxu, decide_eq_true hxS⟩
  unfold submodularGreedyStep
  cases hfilt : u.filter (· ∉ S) with
  | nil =>
    rw [hfilt] at hx_filt
    cases hx_filt
  | cons c₀ cs =>
    rw [hfilt] at hx_filt
    have hsnd : (scanCandidates f S c₀ (f (insert c₀ S)) cs).2 =
        f (insert (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 S) :=
      scanCandidates_snd_eq f S rfl cs
    rw [← hsnd]
    rcases List.mem_cons.mp hx_filt with rfl | hx_cs
    · exact le_scanCandidates_snd f S x (f (insert x S)) cs
    · exact forall_le_scanCandidates_snd f S c₀ (f (insert c₀ S)) cs x hx_cs

theorem submodularGreedy_subset_toFinset (f : Finset α → β) (xs : List α) (k : ℕ) :
    submodularGreedy f xs k ⊆ xs.toFinset := by
  rw [← toFinset_dedupFirst xs]
  induction k with
  | zero => simp
  | succ m ih =>
    rw [submodularGreedy_succ]
    exact submodularGreedyStep_subset_toFinset f ih

theorem mem_of_mem_submodularGreedy {f : Finset α → β} {xs : List α} {k : ℕ} {x : α}
    (hx : x ∈ submodularGreedy f xs k) : x ∈ xs :=
  List.mem_toFinset.mp (submodularGreedy_subset_toFinset f xs k hx)

theorem card_submodularGreedy_eq_min (f : Finset α → β) (xs : List α) (k : ℕ) :
    (submodularGreedy f xs k).card = min k xs.toFinset.card := by
  rw [← toFinset_dedupFirst xs]
  set u := dedupFirst xs
  induction k with
  | zero => simp
  | succ m ih =>
    rw [submodularGreedy_succ]
    set S := submodularGreedy f xs m
    have hS_sub : S ⊆ u.toFinset := by
      simpa [u, S, toFinset_dedupFirst] using submodularGreedy_subset_toFinset f xs m
    by_cases hm : m < u.toFinset.card
    · have hScard : S.card = m := by omega
      cases hfilt : u.filter (· ∉ S) with
      | nil =>
        exfalso
        have hu_sub : u.toFinset ⊆ S := by
          intro a ha
          have ha_u : a ∈ u := List.mem_toFinset.mp ha
          by_contra haS
          have hmem : a ∈ u.filter (· ∉ S) := List.mem_filter.mpr ⟨ha_u, decide_eq_true haS⟩
          rw [hfilt] at hmem
          cases hmem
        have hle : u.toFinset.card ≤ S.card := Finset.card_le_card hu_sub
        omega
      | cons c₀ cs =>
        unfold submodularGreedyStep
        rw [hfilt]
        have hmem : (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 ∈ c₀ :: cs :=
          scanCandidates_fst_mem f S c₀ (f (insert c₀ S)) cs
        rw [← hfilt] at hmem
        have hnotS : (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 ∉ S :=
          of_decide_eq_true (List.mem_filter.mp hmem).2
        rw [Finset.card_insert_of_notMem hnotS, hScard]
        omega
    · have hScard : S.card = u.toFinset.card := by omega
      have hSeq : S = u.toFinset := Finset.eq_of_subset_of_card_le hS_sub hScard.ge
      have hfilt : u.filter (· ∉ S) = [] := by
        rw [List.filter_eq_nil_iff]
        intro a ha
        simp [hSeq, ha]
      unfold submodularGreedyStep
      rw [hfilt, hScard]
      omega

theorem card_submodularGreedy_le (f : Finset α → β) (xs : List α) (k : ℕ) :
    (submodularGreedy f xs k).card ≤ k := by
  rw [card_submodularGreedy_eq_min]
  exact min_le_left k xs.toFinset.card

end Feasibility

/-! ## Nemhauser–Wolsey–Fisher `(1 - 1/e)` approximation guarantee -/

section Approximation

variable {α : Type*} {β : Type*} [DecidableEq α]
  [Field β] [LinearOrder β] [IsStrictOrderedRing β]

/-- Single-step residual contraction ([NemhauserWolseyFisher1978], Section 4): for any set `OPT` of
at most `k ≥ 1` elements drawn from `u`, one greedy step shrinks `f OPT - f S` by at least a factor
of `1 - 1 / (k : β)`. -/
theorem sub_submodularGreedyStep_le
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    {u : List α} {k : ℕ} (hk : 0 < k)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ u.toFinset) (hOPT_card : OPT.card ≤ k)
    (S : Finset α) :
    f OPT - f (submodularGreedyStep f u S) ≤ (1 - 1 / (k : β)) * (f OPT - f S) := by
  have hk_pos : (0 : β) < (k : β) := Nat.cast_pos.mpr hk
  have hk_ne : (k : β) ≠ 0 := hk_pos.ne'
  have hS_le : f S ≤ f (submodularGreedyStep f u S) := hmono (subset_submodularGreedyStep f u S)
  by_cases hgap : f OPT - f S ≤ 0
  · have hdiv_nonneg : (0 : β) ≤ 1 / (k : β) := div_nonneg zero_le_one hk_pos.le
    have hmul_nonpos : (1 / (k : β)) * (f OPT - f S) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hdiv_nonneg hgap
    linarith
  · push Not at hgap
    have hgain_each : ∀ x ∈ OPT \ S,
        marginalGain f S x ≤ f (submodularGreedyStep f u S) - f S := by
      intro x hx
      rcases Finset.mem_sdiff.mp hx with ⟨hxOPT, hxS⟩
      have hxu : x ∈ u := List.mem_toFinset.mp (hOPT_sub hxOPT)
      exact sub_le_sub_right (submodularGreedyStep_max f u S hxu hxS) (f S)
    have hsum_le : f OPT - f S ≤ (k : β) * (f (submodularGreedyStep f u S) - f S) := by
      have h1 : f OPT - f S ≤ ∑ x ∈ OPT \ S, marginalGain f S x :=
        hf.sub_le_sum_marginalGain_of_monotone hmono S OPT
      have h2 : ∑ x ∈ OPT \ S, marginalGain f S x ≤
          ∑ _x ∈ OPT \ S, (f (submodularGreedyStep f u S) - f S) :=
        Finset.sum_le_sum hgain_each
      have hcard_le : ((OPT \ S).card : β) ≤ (k : β) :=
        Nat.cast_le.mpr ((Finset.card_le_card Finset.sdiff_subset).trans hOPT_card)
      have hstep_nonneg : 0 ≤ f (submodularGreedyStep f u S) - f S := sub_nonneg.mpr hS_le
      calc
        f OPT - f S ≤ ∑ _x ∈ OPT \ S, (f (submodularGreedyStep f u S) - f S) := h1.trans h2
        _ = ((OPT \ S).card : β) * (f (submodularGreedyStep f u S) - f S) := by
          rw [Finset.sum_const, nsmul_eq_mul]
        _ ≤ (k : β) * (f (submodularGreedyStep f u S) - f S) :=
          mul_le_mul_of_nonneg_right hcard_le hstep_nonneg
    have hmul_target : (k : β) * (f OPT - f (submodularGreedyStep f u S)) ≤
        (k : β) * ((1 - 1 / (k : β)) * (f OPT - f S)) := by
      have hid : (k : β) * (1 - 1 / (k : β)) = (k : β) - 1 := by
        rw [mul_sub, mul_one, mul_one_div_cancel hk_ne]
      calc
        (k : β) * (f OPT - f (submodularGreedyStep f u S))
            = (k : β) * (f OPT - f S) - (k : β) * (f (submodularGreedyStep f u S) - f S) := by ring
        _ ≤ (k : β) * (f OPT - f S) - (f OPT - f S) := by linarith
        _ = ((k : β) - 1) * (f OPT - f S) := by ring
        _ = ((k : β) * (1 - 1 / (k : β))) * (f OPT - f S) := by rw [hid]
        _ = (k : β) * ((1 - 1 / (k : β)) * (f OPT - f S)) := by ring
    exact le_of_mul_le_mul_left hmul_target hk_pos

/-- Residual gap bound after `m` greedy steps against any cardinality-`k` benchmark `OPT` (`k ≥ 1`):
`f OPT - f (submodularGreedy f xs m) ≤ (1 - 1 / (k : β)) ^ m * (f OPT - f ∅)`. -/
theorem sub_submodularGreedy_le_pow_mul
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    {xs : List α} {k : ℕ} (hk : 0 < k) (m : ℕ)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    f OPT - f (submodularGreedy f xs m) ≤
      (1 - 1 / (k : β)) ^ m * (f OPT - f ∅) := by
  have hk_one : (1 : β) ≤ (k : β) := Nat.one_le_cast.mpr hk
  have hk_pos : (0 : β) < (k : β) := Nat.cast_pos.mpr hk
  have hfactor_nonneg : (0 : β) ≤ 1 - 1 / (k : β) := by
    have hdiv_le : 1 / (k : β) ≤ 1 := div_le_one_of_le₀ hk_one hk_pos.le
    linarith
  have hOPT_u : OPT ⊆ (dedupFirst xs).toFinset := by
    rwa [toFinset_dedupFirst]
  induction m with
  | zero => simp
  | succ m ih =>
    rw [submodularGreedy_succ, pow_succ', mul_assoc]
    exact (sub_submodularGreedyStep_le hf hmono hk hOPT_u hOPT_card _).trans
      (mul_le_mul_of_nonneg_left ih hfactor_nonneg)

/-- **Nemhauser–Wolsey–Fisher `m`-Step Approximation Guarantee** ([NemhauserWolseyFisher1978],
Section 4, Theorem 4.2): for monotone submodular `f` with `0 ≤ f ∅`, running `m` greedy steps
achieves at least `1 - (1 - 1 / (k : β)) ^ m` of any subset `OPT ⊆ xs.toFinset` with
`OPT.card ≤ k` (`0 < k`). -/
theorem one_sub_pow_mul_le_submodularGreedy_steps
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    {xs : List α} {k : ℕ} (hk : 0 < k) (m : ℕ)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - (1 - 1 / (k : β)) ^ m) * f OPT ≤ f (submodularGreedy f xs m) := by
  have hk_one : (1 : β) ≤ (k : β) := Nat.one_le_cast.mpr hk
  have hk_pos : (0 : β) < (k : β) := Nat.cast_pos.mpr hk
  have hfactor_nonneg : (0 : β) ≤ 1 - 1 / (k : β) := by
    have hdiv_le : 1 / (k : β) ≤ 1 := div_le_one_of_le₀ hk_one hk_pos.le
    linarith
  have hpow_nonneg : (0 : β) ≤ (1 - 1 / (k : β)) ^ m := pow_nonneg hfactor_nonneg m
  have hrec := sub_submodularGreedy_le_pow_mul hf hmono hk m hOPT_sub hOPT_card
  have hdrop : (1 - 1 / (k : β)) ^ m * (f OPT - f ∅) ≤ (1 - 1 / (k : β)) ^ m * f OPT :=
    mul_le_mul_of_nonneg_left (sub_le_self (f OPT) hf0) hpow_nonneg
  linarith

/-- **Nemhauser–Wolsey–Fisher Exact Algebraic Bound** ([NemhauserWolseyFisher1978], Theorem 4.2):
after `k ≥ 1` greedy steps, `(1 - (1 - 1 / (k : β)) ^ k) * f OPT ≤ f (submodularGreedy f xs k)`
for every `OPT ⊆ xs.toFinset` with `OPT.card ≤ k`. -/
theorem one_sub_pow_mul_le_submodularGreedy
    {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    {xs : List α} {k : ℕ} (hk : 0 < k)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - (1 - 1 / (k : β)) ^ k) * f OPT ≤ f (submodularGreedy f xs k) :=
  one_sub_pow_mul_le_submodularGreedy_steps hf hmono hf0 hk k hOPT_sub hOPT_card

end Approximation

section RealApproximation

variable {α : Type*} [DecidableEq α]

/-- Real `m`-step exponential approximation bound: running `m` greedy steps achieves at least
`(1 - Real.exp (-(m : ℝ) / (k : ℝ))) * f OPT` against any `OPT ⊆ xs.toFinset` with
`OPT.card ≤ k` (`0 < k`). -/
theorem one_sub_exp_neg_div_mul_le_submodularGreedy
    {f : Finset α → ℝ} (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    {xs : List α} {k : ℕ} (hk : 0 < k) (m : ℕ)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-(m : ℝ) / (k : ℝ))) * f OPT ≤ f (submodularGreedy f xs m) := by
  have hk_one : (1 : ℝ) ≤ (k : ℝ) := Nat.one_le_cast.mpr hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := Nat.cast_pos.mpr hk
  have hfactor_nonneg : (0 : ℝ) ≤ 1 - 1 / (k : ℝ) := by
    have hdiv_le : 1 / (k : ℝ) ≤ 1 := div_le_one_of_le₀ hk_one hk_pos.le
    linarith
  have hexp : (1 - 1 / (k : ℝ)) ^ m ≤ Real.exp (-(m : ℝ) / (k : ℝ)) := by
    calc
      (1 - 1 / (k : ℝ)) ^ m ≤ (Real.exp (-(1 / (k : ℝ)))) ^ m :=
        pow_le_pow_left₀ hfactor_nonneg (Real.one_sub_le_exp_neg (1 / (k : ℝ))) m
      _ = Real.exp ((m : ℝ) * (-(1 / (k : ℝ)))) := (Real.exp_nat_mul _ m).symm
      _ = Real.exp (-(m : ℝ) / (k : ℝ)) := by ring_nf
  have hOPT_nonneg : 0 ≤ f OPT := nonneg_of_empty_nonneg_of_monotone hf0 hmono OPT
  have hcoef : 1 - Real.exp (-(m : ℝ) / (k : ℝ)) ≤ 1 - (1 - 1 / (k : ℝ)) ^ m := by linarith
  exact (mul_le_mul_of_nonneg_right hcoef hOPT_nonneg).trans
    (one_sub_pow_mul_le_submodularGreedy_steps hf hmono hf0 hk m hOPT_sub hOPT_card)

/-- **Nemhauser–Wolsey–Fisher `(1 - 1/e)` Theorem** ([NemhauserWolseyFisher1978], Section 4,
Theorem 4.2): for every nonnegative monotone submodular function `f : Finset α → ℝ` (`0 ≤ f ∅`),
ground list `xs : List α`, budget `k : ℕ`, and feasible set `OPT ⊆ xs.toFinset` with
`OPT.card ≤ k`,
`(1 - Real.exp (-1)) * f OPT ≤ f (submodularGreedy f xs k)`. -/
theorem one_sub_exp_neg_one_mul_le_submodularGreedy
    {f : Finset α → ℝ} (hf : IsSubmodular f) (hmono : Monotone f) (hf0 : 0 ≤ f ∅)
    (xs : List α) (k : ℕ)
    {OPT : Finset α} (hOPT_sub : OPT ⊆ xs.toFinset) (hOPT_card : OPT.card ≤ k) :
    (1 - Real.exp (-1)) * f OPT ≤ f (submodularGreedy f xs k) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · have hOPT_empty : OPT = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hOPT_card)
    rw [hOPT_empty, submodularGreedy_zero]
    have hexp_pos : 0 ≤ Real.exp (-1) := (Real.exp_pos (-1)).le
    have hcoef_le : 1 - Real.exp (-1) ≤ 1 := by linarith
    calc
      (1 - Real.exp (-1)) * f ∅ ≤ 1 * f ∅ := mul_le_mul_of_nonneg_right hcoef_le hf0
      _ = f ∅ := one_mul (f ∅)
  · have h := one_sub_exp_neg_div_mul_le_submodularGreedy hf hmono hf0 hk k hOPT_sub hOPT_card
    have hk_ne : (k : ℝ) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
    have hdiv : -(k : ℝ) / (k : ℝ) = -1 := by
      rw [neg_div, div_self hk_ne]
    rwa [hdiv] at h

end RealApproximation

/-! ## Exact `1 - (1 - 1/k)^k` tightness family for every `k ≥ 1` -/

section Tightness

/-- Number of left-half elements `Sum.inl i` belonging to `S`. -/
def leftCount (k : ℕ) (S : Finset (Fin k ⊕ Fin k)) : ℕ :=
  (Finset.univ.filter fun i : Fin k => Sum.inl i ∈ S).card

private theorem leftCount_empty (k : ℕ) : leftCount k ∅ = 0 := by
  simp [leftCount]

private theorem leftCount_mono (k : ℕ) : Monotone (leftCount k) := by
  intro A B hAB
  exact Finset.card_le_card fun i hi => by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hAB hi

private theorem leftCount_insert_inr (k : ℕ) (j : Fin k) (S : Finset (Fin k ⊕ Fin k)) :
    leftCount k (insert (Sum.inr j) S) = leftCount k S := by
  simp [leftCount]

private theorem leftCount_insert_inl_of_notMem (k : ℕ) (i : Fin k)
    {S : Finset (Fin k ⊕ Fin k)} (hi : Sum.inl i ∉ S) :
    leftCount k (insert (Sum.inl i) S) = leftCount k S + 1 := by
  unfold leftCount
  have hfilt : (Finset.univ.filter fun t : Fin k => Sum.inl t ∈ insert (Sum.inl i) S) =
      insert i (Finset.univ.filter fun t : Fin k => Sum.inl t ∈ S) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert, Sum.inl.injEq]
  have hi_not : i ∉ Finset.univ.filter (fun t : Fin k => Sum.inl t ∈ S) := by
    simp [hi]
  rw [hfilt, Finset.card_insert_of_notMem hi_not]

/-- Component `j` of the Nemhauser–Wolsey tight instance on `Fin k ⊕ Fin k`: saturates at `1/k`
once `Sum.inr j ∈ S`, and otherwise grows geometrically with `leftCount k S`. -/
def tightComponent {β : Type*} [Field β] (k : ℕ) (j : Fin k)
    (S : Finset (Fin k ⊕ Fin k)) : β :=
  if Sum.inr j ∈ S then
    1 / (k : β)
  else
    (1 / (k : β)) * (1 - (1 - 1 / (k : β)) ^ leftCount k S)

/-- Tight monotone submodular objective `∑ j : Fin k, tightComponent k j S` on `Fin k ⊕ Fin k`
([NemhauserWolsey1978], Section 3; [NemhauserWolseyFisher1978], Section 4, Theorem 4.1(c) and
Theorem 4.2, pp. 280–283).

At each step `t < k` from `{Sum.inl 0, …, Sum.inl (t - 1)}`, every remaining `Sum.inl i` and
`Sum.inr j` has the exact same marginal gain `(1 / k) * (1 - 1 / k) ^ t`; ordering `Sum.inl`
before `Sum.inr` in `tightCandidates k` lets `submodularGreedy`'s deterministic left-to-right
tie-breaking attain `1 - (1 - 1 / k) ^ k` exactly without an `ε > 0` perturbation. -/
def tightObjective {β : Type*} [Field β] (k : ℕ)
    (S : Finset (Fin k ⊕ Fin k)) : β :=
  ∑ j : Fin k, tightComponent k j S

/-- Ordered ground list of `2k` candidates: all `Sum.inl i` followed by all `Sum.inr j`. -/
def tightCandidates (k : ℕ) : List (Fin k ⊕ Fin k) :=
  (List.finRange k).map Sum.inl ++ (List.finRange k).map Sum.inr

/-- Optimal cardinality-`k` subset `{Sum.inr 0, …, Sum.inr (k - 1)}`. -/
def tightOpt (k : ℕ) : Finset (Fin k ⊕ Fin k) :=
  Finset.univ.map ⟨Sum.inr, Sum.inr_injective⟩

@[simp] theorem tightComponent_empty {β : Type*} [Field β] (k : ℕ) (j : Fin k) :
    tightComponent (β := β) k j ∅ = 0 := by
  simp [tightComponent, leftCount_empty]

@[simp] theorem tightObjective_empty {β : Type*} [Field β] (k : ℕ) :
    tightObjective (β := β) k ∅ = 0 := by
  simp [tightObjective]

private theorem marginalGain_tightComponent_inl {β : Type*} [Field β] (k : ℕ) (j i : Fin k)
    {S : Finset (Fin k ⊕ Fin k)} (hi : Sum.inl i ∉ S) :
    marginalGain (tightComponent (β := β) k j) S (Sum.inl i) =
      if Sum.inr j ∈ S then 0
      else (1 / (k : β)) * (1 - 1 / (k : β)) ^ leftCount k S * (1 / (k : β)) := by
  unfold marginalGain tightComponent
  have hinr : (Sum.inr j ∈ insert (Sum.inl i) S) ↔ Sum.inr j ∈ S := by simp
  simp only [hinr]
  split_ifs with hj
  · exact sub_self _
  · rw [leftCount_insert_inl_of_notMem k i hi, pow_succ]
    ring

private theorem marginalGain_tightComponent_inr_self {β : Type*} [Field β] (k : ℕ) (j : Fin k)
    {S : Finset (Fin k ⊕ Fin k)} (hj : Sum.inr j ∉ S) :
    marginalGain (tightComponent (β := β) k j) S (Sum.inr j) =
      (1 / (k : β)) * (1 - 1 / (k : β)) ^ leftCount k S := by
  unfold marginalGain tightComponent
  simp only [Finset.mem_insert_self, ↓reduceIte, hj]
  ring

private theorem marginalGain_tightComponent_inr_ne {β : Type*} [Field β]
    (k : ℕ) {j j' : Fin k} (hne : j' ≠ j) (S : Finset (Fin k ⊕ Fin k)) :
    marginalGain (tightComponent (β := β) k j) S (Sum.inr j') = 0 := by
  unfold marginalGain tightComponent
  have hinr : (Sum.inr j ∈ insert (Sum.inr j') S) ↔ Sum.inr j ∈ S := by
    simp [hne.symm]
  simp [hinr, leftCount_insert_inr]

theorem nodup_tightCandidates (k : ℕ) : (tightCandidates k).Nodup := by
  unfold tightCandidates
  rw [List.nodup_append]
  refine ⟨(List.nodup_finRange k).map Sum.inl_injective,
    (List.nodup_finRange k).map Sum.inr_injective, ?_⟩
  intro a ha b hb hab
  rcases List.mem_map.mp ha with ⟨i, _, rfl⟩
  rcases List.mem_map.mp hb with ⟨j, _, rfl⟩
  cases hab

@[simp] theorem mem_tightCandidates (k : ℕ) (x : Fin k ⊕ Fin k) :
    x ∈ tightCandidates k := by
  unfold tightCandidates
  cases x with
  | inl i => exact List.mem_append_left _ (List.mem_map_of_mem (List.mem_finRange i))
  | inr j => exact List.mem_append_right _ (List.mem_map_of_mem (List.mem_finRange j))

theorem tightOpt_subset_toFinset (k : ℕ) :
    tightOpt k ⊆ (tightCandidates k).toFinset := by
  intro x _
  exact List.mem_toFinset.mpr (mem_tightCandidates k x)

@[simp] theorem card_tightOpt (k : ℕ) : (tightOpt k).card = k := by
  simp [tightOpt]

/-- Prefix `{Sum.inl 0, …, Sum.inl (t - 1)}` selected after `t` greedy steps on the tight
instance. -/
private def leftPrefix (k t : ℕ) : Finset (Fin k ⊕ Fin k) :=
  (Finset.univ.filter fun i : Fin k => i.val < t).map ⟨Sum.inl, Sum.inl_injective⟩

private theorem mem_leftPrefix {k t : ℕ} {x : Fin k ⊕ Fin k} :
    x ∈ leftPrefix k t ↔ ∃ i : Fin k, i.val < t ∧ x = Sum.inl i := by
  simp [leftPrefix, eq_comm]

private theorem leftPrefix_zero (k : ℕ) : leftPrefix k 0 = ∅ := by
  ext x
  simp [mem_leftPrefix]

private theorem leftCount_leftPrefix {k t : ℕ} (ht : t ≤ k) :
    leftCount k (leftPrefix k t) = t := by
  unfold leftCount
  have hfilt : (Finset.univ.filter fun i : Fin k => Sum.inl i ∈ leftPrefix k t) =
      Finset.univ.filter (fun i : Fin k => i.val < t) := by
    ext i
    simp [mem_leftPrefix]
  rw [hfilt]
  have hbij : (Finset.univ.filter fun i : Fin k => i.val < t).card = (Finset.range t).card := by
    refine Finset.card_bij (fun i _ => i.val) ?_ ?_ ?_
    · intro i hi
      exact Finset.mem_range.mpr (Finset.mem_filter.mp hi).2
    · intro i₁ _ i₂ _ hval
      exact Fin.ext hval
    · intro m hm
      have hmt : m < t := Finset.mem_range.mp hm
      exact ⟨⟨m, hmt.trans_le ht⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hmt⟩, rfl⟩
  rw [hbij, Finset.card_range]

private theorem filter_tightCandidates_leftPrefix {k t : ℕ} (ht : t < k) :
    ∃ cs, (tightCandidates k).filter (· ∉ leftPrefix k t) = Sum.inl ⟨t, ht⟩ :: cs := by
  have hsplit : List.finRange k =
      (List.finRange k).take t ++ ⟨t, ht⟩ :: (List.finRange k).drop (t + 1) := by
    have hlen : t < (List.finRange k).length := by simp [ht]
    have hdrop : (List.finRange k).drop t =
        (List.finRange k)[t] :: (List.finRange k).drop (t + 1) :=
      List.drop_eq_getElem_cons hlen
    have hget : (List.finRange k)[t] = ⟨t, ht⟩ := by simp
    calc
      List.finRange k = (List.finRange k).take t ++ (List.finRange k).drop t :=
        (List.take_append_drop t (List.finRange k)).symm
      _ = (List.finRange k).take t ++ ⟨t, ht⟩ :: (List.finRange k).drop (t + 1) := by
        rw [hdrop, hget]
  unfold tightCandidates
  rw [hsplit, List.map_append, List.map_cons, List.append_assoc, List.filter_append]
  have htake_nil :
      (((List.finRange k).take t).map Sum.inl).filter (· ∉ leftPrefix k t) = [] := by
    rw [List.filter_eq_nil_iff]
    intro x hx
    rcases List.mem_map.mp hx with ⟨i, hi_take, rfl⟩
    have hi_lt : i.val < t := by
      rcases List.mem_iff_getElem.mp hi_take with ⟨idx, hidx, hget⟩
      have hidx_lt : idx < t := by
        rw [List.length_take] at hidx
        exact lt_of_lt_of_le hidx (Nat.min_le_left t _)
      have hval : ((List.finRange k).take t)[idx].val = idx := by simp
      rw [← hget, hval]
      exact hidx_lt
    have hmem : Sum.inl i ∈ leftPrefix k t := mem_leftPrefix.mpr ⟨i, hi_lt, rfl⟩
    simp [hmem]
  have ht_notMem : Sum.inl (⟨t, ht⟩ : Fin k) ∉ leftPrefix k t := by
    intro hmem
    rcases mem_leftPrefix.mp hmem with ⟨i, hi_lt, hinj⟩
    cases hinj
    exact Nat.lt_irrefl t hi_lt
  rw [htake_nil, List.nil_append, List.cons_append]
  simp [ht_notMem]

section OrderedTightness

variable {β : Type*} [Field β] [LinearOrder β] [IsStrictOrderedRing β]

theorem monotone_tightComponent {k : ℕ} (hk : 0 < k) (j : Fin k) :
    Monotone (tightComponent (β := β) k j) := by
  have hk_pos : (0 : β) < (k : β) := Nat.cast_pos.mpr hk
  have hk_one : (1 : β) ≤ (k : β) := Nat.one_le_cast.mpr hk
  have hdiv_nonneg : (0 : β) ≤ 1 / (k : β) := div_nonneg zero_le_one hk_pos.le
  have hq_nonneg : (0 : β) ≤ 1 - 1 / (k : β) := by
    have hdiv_le : 1 / (k : β) ≤ 1 := div_le_one_of_le₀ hk_one hk_pos.le
    linarith
  have hq_le_one : 1 - 1 / (k : β) ≤ 1 := by linarith
  intro A B hAB
  unfold tightComponent
  split_ifs with hA hB hB
  · exact le_rfl
  · exact absurd (hAB hA) hB
  · have hpow_nonneg : (0 : β) ≤ (1 - 1 / (k : β)) ^ leftCount k A :=
      pow_nonneg hq_nonneg _
    have h1 : 1 - (1 - 1 / (k : β)) ^ leftCount k A ≤ 1 := by linarith
    calc
      (1 / (k : β)) * (1 - (1 - 1 / (k : β)) ^ leftCount k A)
          ≤ (1 / (k : β)) * 1 := mul_le_mul_of_nonneg_left h1 hdiv_nonneg
      _ = 1 / (k : β) := mul_one _
  · have hpow : (1 - 1 / (k : β)) ^ leftCount k B ≤ (1 - 1 / (k : β)) ^ leftCount k A :=
      pow_le_pow_of_le_one hq_nonneg hq_le_one (leftCount_mono k hAB)
    exact mul_le_mul_of_nonneg_left (by linarith) hdiv_nonneg

theorem isSubmodular_tightComponent {k : ℕ} (hk : 0 < k) (j : Fin k) :
    IsSubmodular (tightComponent (β := β) k j) := by
  rw [isSubmodular_iff_marginalGain_le]
  have hk_pos : (0 : β) < (k : β) := Nat.cast_pos.mpr hk
  have hk_one : (1 : β) ≤ (k : β) := Nat.one_le_cast.mpr hk
  have hdiv_nonneg : (0 : β) ≤ 1 / (k : β) := div_nonneg zero_le_one hk_pos.le
  have hq_nonneg : (0 : β) ≤ 1 - 1 / (k : β) := by
    have hdiv_le : 1 / (k : β) ≤ 1 := div_le_one_of_le₀ hk_one hk_pos.le
    linarith
  have hq_le_one : 1 - 1 / (k : β) ≤ 1 := by linarith
  intro A B x hAB hxB
  have hxA : x ∉ A := fun h => hxB (hAB h)
  cases x with
  | inl i =>
    rw [marginalGain_tightComponent_inl k j i hxB, marginalGain_tightComponent_inl k j i hxA]
    split_ifs with hB hA hA
    · exact le_rfl
    · exact mul_nonneg
        (mul_nonneg hdiv_nonneg (pow_nonneg hq_nonneg _)) hdiv_nonneg
    · exact absurd (hAB hA) hB
    · have hpow : (1 - 1 / (k : β)) ^ leftCount k B ≤ (1 - 1 / (k : β)) ^ leftCount k A :=
        pow_le_pow_of_le_one hq_nonneg hq_le_one (leftCount_mono k hAB)
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hpow hdiv_nonneg) hdiv_nonneg
  | inr j' =>
    by_cases hjj : j' = j
    · subst hjj
      rw [marginalGain_tightComponent_inr_self k j' hxB,
        marginalGain_tightComponent_inr_self k j' hxA]
      have hpow : (1 - 1 / (k : β)) ^ leftCount k B ≤ (1 - 1 / (k : β)) ^ leftCount k A :=
        pow_le_pow_of_le_one hq_nonneg hq_le_one (leftCount_mono k hAB)
      exact mul_le_mul_of_nonneg_left hpow hdiv_nonneg
    · rw [marginalGain_tightComponent_inr_ne k hjj B,
        marginalGain_tightComponent_inr_ne k hjj A]

theorem monotone_tightObjective {k : ℕ} (hk : 0 < k) :
    Monotone (tightObjective (β := β) k) := by
  intro A B hAB
  exact Finset.sum_le_sum fun j _ => monotone_tightComponent hk j hAB

theorem isSubmodular_tightObjective {k : ℕ} (hk : 0 < k) :
    IsSubmodular (tightObjective (β := β) k) :=
  isSubmodular_sum Finset.univ fun j _ => isSubmodular_tightComponent hk j

theorem tightObjective_tightOpt {k : ℕ} (hk : 0 < k) :
    tightObjective (β := β) k (tightOpt k) = 1 := by
  have hk_ne : (k : β) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  have hmem : ∀ j : Fin k, Sum.inr j ∈ tightOpt k := by
    intro j
    simp [tightOpt]
  simp [tightObjective, tightComponent, hmem, Finset.sum_const, nsmul_eq_mul, hk_ne]

private theorem tightObjective_leftPrefix {k t : ℕ} (hk : 0 < k) (ht : t ≤ k) :
    tightObjective (β := β) k (leftPrefix k t) = 1 - (1 - 1 / (k : β)) ^ t := by
  have hk_ne : (k : β) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  have hnot_inr : ∀ j : Fin k, Sum.inr j ∉ leftPrefix k t := by
    intro j hj
    rcases mem_leftPrefix.mp hj with ⟨i, _, h⟩
    cases h
  simp only [tightObjective, tightComponent, hnot_inr, ↓reduceIte, leftCount_leftPrefix ht,
    Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← mul_assoc, mul_one_div_cancel hk_ne, one_mul]

private theorem tightObjective_insert_leftPrefix_eq {k t : ℕ} (hk : 0 < k) (ht : t < k)
    {x : Fin k ⊕ Fin k} (hx : x ∉ leftPrefix k t) :
    tightObjective (β := β) k (insert x (leftPrefix k t)) =
      1 - (1 - 1 / (k : β)) ^ (t + 1) := by
  have hk_ne : (k : β) ≠ 0 := (Nat.cast_pos.mpr hk).ne'
  have hnot_inr : ∀ j : Fin k, Sum.inr j ∉ leftPrefix k t := by
    intro j hj
    rcases mem_leftPrefix.mp hj with ⟨i, _, h⟩
    cases h
  have hdiff : tightObjective (β := β) k (insert x (leftPrefix k t)) -
      tightObjective (β := β) k (leftPrefix k t) =
      (1 / (k : β)) * (1 - 1 / (k : β)) ^ t := by
    have hsum_sub : tightObjective (β := β) k (insert x (leftPrefix k t)) -
        tightObjective (β := β) k (leftPrefix k t) =
        ∑ j : Fin k, marginalGain (tightComponent (β := β) k j) (leftPrefix k t) x := by
      simp [tightObjective, marginalGain, Finset.sum_sub_distrib]
    rw [hsum_sub]
    cases x with
    | inl i =>
      have hterm : ∀ j : Fin k,
          marginalGain (tightComponent (β := β) k j) (leftPrefix k t) (Sum.inl i) =
            (1 / (k : β)) * (1 - 1 / (k : β)) ^ t * (1 / (k : β)) := by
        intro j
        rw [marginalGain_tightComponent_inl k j i hx, leftCount_leftPrefix ht.le]
        simp [hnot_inr j]
      simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        (k : β) * ((1 / (k : β)) * (1 - 1 / (k : β)) ^ t * (1 / (k : β)))
            = ((k : β) * (1 / (k : β))) * ((1 / (k : β)) * (1 - 1 / (k : β)) ^ t) := by ring
        _ = 1 * ((1 / (k : β)) * (1 - 1 / (k : β)) ^ t) := by rw [mul_one_div_cancel hk_ne]
        _ = (1 / (k : β)) * (1 - 1 / (k : β)) ^ t := one_mul _
    | inr j₀ =>
      have hterm : ∀ j : Fin k,
          marginalGain (tightComponent (β := β) k j) (leftPrefix k t) (Sum.inr j₀) =
            if j = j₀ then (1 / (k : β)) * (1 - 1 / (k : β)) ^ t else 0 := by
        intro j
        by_cases hjj : j = j₀
        · subst hjj
          simp [marginalGain_tightComponent_inr_self k j hx, leftCount_leftPrefix ht.le]
        · have hne : j₀ ≠ j := fun h => hjj h.symm
          simp [hjj, marginalGain_tightComponent_inr_ne k hne]
      simp [hterm]
  have hbase := tightObjective_leftPrefix (β := β) hk ht.le
  calc
    tightObjective (β := β) k (insert x (leftPrefix k t))
        = tightObjective (β := β) k (leftPrefix k t) +
            (tightObjective (β := β) k (insert x (leftPrefix k t)) -
              tightObjective (β := β) k (leftPrefix k t)) := by ring
    _ = (1 - (1 - 1 / (k : β)) ^ t) + (1 / (k : β)) * (1 - 1 / (k : β)) ^ t := by
        rw [hdiff, hbase]
    _ = 1 - (1 - 1 / (k : β)) ^ (t + 1) := by
        rw [pow_succ]
        ring

private theorem submodularGreedy_tightObjective_steps {k : ℕ} (hk : 0 < k) :
    ∀ t ≤ k,
      submodularGreedy (tightObjective (β := β) k) (tightCandidates k) t = leftPrefix k t := by
  intro t ht
  induction t with
  | zero => simp [leftPrefix_zero]
  | succ t ih =>
    have ht_lt : t < k := Nat.lt_of_succ_le ht
    rw [submodularGreedy_succ, ih ht_lt.le, dedupFirst_eq_self (nodup_tightCandidates k)]
    rcases filter_tightCandidates_leftPrefix ht_lt with ⟨cs, hfilt⟩
    unfold submodularGreedyStep
    rw [hfilt]
    dsimp only
    have ht_notMem : Sum.inl (⟨t, ht_lt⟩ : Fin k) ∉ leftPrefix k t := by
      have hmem : Sum.inl (⟨t, ht_lt⟩ : Fin k) ∈
          (tightCandidates k).filter (· ∉ leftPrefix k t) := by
        rw [hfilt]
        exact List.mem_cons_self
      exact of_decide_eq_true (List.mem_filter.mp hmem).2
    have hall_le : ∀ c ∈ cs,
        tightObjective (β := β) k (insert c (leftPrefix k t)) ≤
          tightObjective (β := β) k (insert (Sum.inl ⟨t, ht_lt⟩) (leftPrefix k t)) := by
      intro c hc
      have hc_filt : c ∈ (tightCandidates k).filter (· ∉ leftPrefix k t) := by
        rw [hfilt]
        exact List.mem_cons_of_mem _ hc
      have hc_notMem : c ∉ leftPrefix k t := of_decide_eq_true (List.mem_filter.mp hc_filt).2
      rw [tightObjective_insert_leftPrefix_eq hk ht_lt hc_notMem,
        tightObjective_insert_leftPrefix_eq hk ht_lt ht_notMem]
    rw [scanCandidates_eq_of_forall_le _ _ _ _ hall_le]
    ext x
    simp only [Finset.mem_insert, mem_leftPrefix]
    constructor
    · rintro (rfl | ⟨i, hi_lt, rfl⟩)
      · exact ⟨⟨t, ht_lt⟩, Nat.lt_succ_self t, rfl⟩
      · exact ⟨i, Nat.lt_succ_of_lt hi_lt, rfl⟩
    · rintro ⟨i, hi_lt, rfl⟩
      rcases Nat.lt_succ_iff_lt_or_eq.mp hi_lt with hlt | heq
      · exact Or.inr ⟨i, hlt, rfl⟩
      · left
        congr
        exact Fin.ext heq

/-- **Exact Tightness of `1 - (1 - 1/k)^k`** ([NemhauserWolsey1978], Section 3;
[NemhauserWolseyFisher1978], Section 4, Theorem 4.1(c) and Theorem 4.2, pp. 280–283): for every
budget `k ≥ 1`, running `submodularGreedy` on `tightObjective k` and `tightCandidates k` (under
left-to-right tie-breaking across tied marginal gains `(1 / k) * (1 - 1 / k) ^ t`) returns a set
of exact value `1 - (1 - 1 / (k : β)) ^ k`, whereas `tightOpt k` has cardinality `k` and value
`1`. -/
theorem submodularGreedy_tightObjective_eq {k : ℕ} (hk : 0 < k) :
    tightObjective (β := β) k (submodularGreedy (tightObjective (β := β) k) (tightCandidates k) k) =
      1 - (1 - 1 / (k : β)) ^ k := by
  rw [submodularGreedy_tightObjective_steps hk k le_rfl, tightObjective_leftPrefix hk le_rfl]

/-- Existential summary: for every `k ≥ 1`, no constant strictly larger than `1 - (1 - 1/k)^k`
can lower-bound the approximation ratio of `submodularGreedy` on `2k`-element nonnegative monotone
submodular instances. -/
theorem exists_tight_submodularGreedy {k : ℕ} (hk : 0 < k) :
    ∃ (f : Finset (Fin k ⊕ Fin k) → β) (xs : List (Fin k ⊕ Fin k)) (OPT : Finset (Fin k ⊕ Fin k)),
      IsSubmodular f ∧ Monotone f ∧ f ∅ = 0 ∧
      xs.length = 2 * k ∧ OPT ⊆ xs.toFinset ∧ OPT.card = k ∧ f OPT = 1 ∧
      f (submodularGreedy f xs k) = (1 - (1 - 1 / (k : β)) ^ k) * f OPT := by
  refine ⟨tightObjective k, tightCandidates k, tightOpt k,
    isSubmodular_tightObjective hk, monotone_tightObjective hk, tightObjective_empty k,
    ?_, tightOpt_subset_toFinset k, card_tightOpt k, tightObjective_tightOpt hk, ?_⟩
  · simp [tightCandidates, two_mul]
  · rw [tightObjective_tightOpt hk, mul_one, submodularGreedy_tightObjective_eq hk]

end OrderedTightness

end Tightness

end Cslib.Algorithms.Lean.Submodular
