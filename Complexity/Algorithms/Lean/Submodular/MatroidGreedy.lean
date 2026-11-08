/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.Matroid.PSystem
public import Complexity.Algorithms.Lean.Submodular.Greedy
public import Cslib.Foundations.Control.Monad.IsMonadHom
import Complexity.Foundations.Data.List.EraseDups
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Max
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Data.Fintype.Fin

/-!
# Greedy Submodular Maximization over Matroids and `p`-Systems

This module formalizes the greedy algorithm of Fisher, Nemhauser, and Wolsey for maximizing a
monotone submodular set function `f : Finset α → β` subject to a matroid constraint, or more
generally a `p`-system constraint ([FisherNemhauserWolsey1978];
[CalinescuChekuriPalVondrak2011], Appendix B). Starting from `S = ∅`, each round inserts a
feasible element `c ∉ S` with `indep (insert c S)` maximizing `f (insert c S)`, and the algorithm
stops when no feasible element remains.

## Algorithm design

1. First-occurrence deduplication `xs.eraseDups` produces the ordered ground list `u`.
2. Each round first tests every remaining element `c ∉ S` of `u` for feasibility
   (`indep (insert c S)`, one independence query each), then scans the feasible candidates,
   evaluating `f (insert c S)` once per candidate and breaking ties toward earlier candidates.
   If no candidate is feasible, the round returns `none` and the algorithm stops.
3. The loop runs at most `u.length` rounds, which suffices because every successful round grows
   the current set inside `u.toFinset`.
4. Monadic (`submodularMatroidGreedyM`) and pure (`submodularMatroidGreedy`) presentations are
   connected by `@[simp]` `pure`/`Id.run` lemmas and `@[grind .] IsMonadHom` naturality bridges, as
   for the cardinality-constrained `submodularGreedy`.

## Main definitions

* `Cslib.Algorithms.Lean.Submodular.feasibleCandidates`: elements `c ∉ S` of `u` with
  `indep (insert c S)`, in order.
* `Cslib.Algorithms.Lean.Submodular.submodularMatroidGreedyM`,
  `Cslib.Algorithms.Lean.Submodular.submodularMatroidGreedy`: the monadic and pure greedy
  algorithms.
* `Cslib.Algorithms.Lean.Submodular.submodularMatroidGreedyChain`: the chain `S₀ = ∅ ⊆ S₁ ⊆ ⋯` of
  greedy prefixes, which stabilizes once no feasible element remains.

## Main results

* `submodularMatroidGreedy_subset_toFinset`, `indep_submodularMatroidGreedy`,
  `not_indep_insert_submodularMatroidGreedy`: the output is a maximal independent subset of the
  ground list.
* `add_nsmul_le_succ_nsmul_submodularMatroidGreedy`: for a monotone submodular `f`, a `p`-system
  `indep` and any independent `O ⊆ xs.toFinset`, `f O + p • f ∅ ≤ (p + 1) • f G`
  ([FisherNemhauserWolsey1978]; [CalinescuChekuriPalVondrak2011], Appendix B).
* `div_succ_le_submodularMatroidGreedy`: `f O / (p + 1) ≤ f G` over ordered fields when
  `0 ≤ f ∅`.
* `add_le_two_nsmul_submodularMatroidGreedy_of_matroid`,
  `half_le_submodularMatroidGreedy_of_matroid`: the `1/2` bound for a Mathlib `Matroid`.
* `div_card_succ_le_submodularMatroidGreedy_of_iInter_matroid`: the `1/(k+1)` bound for the
  intersection of `k ≥ 1` matroids.
* `sum_le_nsmul_sum_submodularMatroidGreedy`, `sum_le_sum_submodularMatroidGreedy_of_matroid`: for
  nonnegative modular objectives, `∑ O w ≤ p • ∑ G w` ([Jenkyns1976]); for `p = 1` (matroids) the
  greedy output is optimal.
* `exists_tight_submodularMatroidGreedy`: the `1/2` bound is attained exactly.

## References

* [FisherNemhauserWolsey1978] Marshall L. Fisher, George L. Nemhauser, and Laurence A. Wolsey,
  *An Analysis of Approximations for Maximizing Submodular Set Functions—II*, 1978. Attributed via
  [CalinescuChekuriPalVondrak2011], Section 1 and Appendix B; not inspected (paywalled).
* [CalinescuChekuriPalVondrak2011] Gruia Calinescu, Chandra Chekuri, Martin Pál, and Jan Vondrák,
  *Maximizing a Monotone Submodular Function Subject to a Matroid Constraint*, 2011.
* [Jenkyns1976] Thomas A. Jenkyns, *The Efficacy of the "Greedy" Algorithm*, 1976.
-/

public section

open Cslib (IsMonadHom)
open Cslib.Algorithms.Lean.Matroid (IsPSystem isPSystem_matroid isPSystem_iInter_matroid)

namespace Cslib.Algorithms.Lean.Submodular

/-! ## Monadic and pure greedy algorithm -/

section Algorithm

/-- Feasible candidates of one greedy round: the elements `c ∉ S` of `u` with
`indep (insert c S) = true`, in order. -/
@[expose] def feasibleCandidates {α : Type*} [DecidableEq α]
    (indep : Finset α → Bool) (u : List α) (S : Finset α) : List α :=
  (u.filter (· ∉ S)).filter fun c => indep (insert c S)

/-- One pure greedy round over the deduplicated ground list `u`: returns `some (insert c S)` for the
feasible candidate `c` maximizing `f (insert c S)` (ties broken toward earlier elements of `u`), or
`none` when no candidate is feasible. -/
@[expose] def submodularMatroidGreedyStep {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (f : Finset α → β) (indep : Finset α → Bool) (u : List α) (S : Finset α) :
    Option (Finset α) :=
  match feasibleCandidates indep u S with
  | [] => none
  | c₀ :: cs => some (insert (scanCandidates f S c₀ (f (insert c₀ S)) cs).1 S)

/-- Pure greedy loop with fuel `k`, stopping at the first round without a feasible candidate. -/
@[expose] def submodularMatroidGreedyLoop {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (f : Finset α → β) (indep : Finset α → Bool) (u : List α) : ℕ → Finset α → Finset α
  | 0, S => S
  | k + 1, S =>
    match submodularMatroidGreedyStep f indep u S with
    | none => S
    | some S' => submodularMatroidGreedyLoop f indep u k S'

/-- Pure Fisher–Nemhauser–Wolsey greedy algorithm for maximizing `f` over the independent subsets
of the ground list `xs`. -/
@[expose] def submodularMatroidGreedy {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (f : Finset α → β) (indep : Finset α → Bool) (xs : List α) : Finset α :=
  submodularMatroidGreedyLoop f indep xs.eraseDups xs.eraseDups.length ∅

/-- Monadic feasibility filter making one `indepM` call per element of the input list. -/
@[expose] def filterIndepM {α : Type} {m : Type → Type*} [Monad m] [DecidableEq α]
    (indepM : Finset α → m Bool) (S : Finset α) : List α → m (List α)
  | [] => return []
  | c :: cs => do
    let b ← indepM (insert c S)
    let rest ← filterIndepM indepM S cs
    return if b then c :: rest else rest

/-- One monadic greedy round: one `indepM` call per element `c ∉ S` of `u`, then one `evalSet` call
per feasible candidate. -/
@[expose] def submodularMatroidGreedyStepM {α : Type} {β : Type} {m : Type → Type*} [Monad m]
    [DecidableEq α] [LinearOrder β]
    (evalSet : Finset α → m β) (indepM : Finset α → m Bool) (u : List α) (S : Finset α) :
    m (Option (Finset α)) := do
  let cands ← filterIndepM indepM S (u.filter (· ∉ S))
  match cands with
  | [] => return none
  | c₀ :: cs => do
    let v₀ ← evalSet (insert c₀ S)
    let p ← scanCandidatesM evalSet S c₀ v₀ cs
    return some (insert p.1 S)

/-- Monadic greedy loop with fuel `k`, stopping at the first round without a feasible candidate. -/
@[expose] def submodularMatroidGreedyLoopM {α : Type} {β : Type} {m : Type → Type*} [Monad m]
    [DecidableEq α] [LinearOrder β]
    (evalSet : Finset α → m β) (indepM : Finset α → m Bool) (u : List α) :
    ℕ → Finset α → m (Finset α)
  | 0, S => return S
  | k + 1, S => do
    match ← submodularMatroidGreedyStepM evalSet indepM u S with
    | none => return S
    | some S' => submodularMatroidGreedyLoopM evalSet indepM u k S'

/-- Monadic Fisher–Nemhauser–Wolsey greedy algorithm with value-oracle callback `evalSet` and
independence-oracle callback `indepM`. -/
@[expose] def submodularMatroidGreedyM {α : Type} {β : Type} {m : Type → Type*} [Monad m]
    [DecidableEq α] [LinearOrder β]
    (evalSet : Finset α → m β) (indepM : Finset α → m Bool) (xs : List α) : m (Finset α) :=
  submodularMatroidGreedyLoopM evalSet indepM xs.eraseDups xs.eraseDups.length ∅

/-! ### Monad homomorphism and `pure`/`Id.run` bridges -/

section Bridges

variable {α : Type} {β : Type} [DecidableEq α] [LinearOrder β]
  {m : Type → Type*} {n : Type → Type*} [Monad m] [Monad n]

@[simp] theorem filterIndepM_pure [LawfulMonad m]
    (indep : Finset α → Bool) (S : Finset α) (cs : List α) :
    filterIndepM (fun T => (pure (indep T) : m Bool)) S cs =
      pure (cs.filter fun c => indep (insert c S)) := by
  induction cs with
  | nil => rfl
  | cons c cs ih =>
    simp only [filterIndepM, pure_bind, ih, List.filter_cons]

@[simp] theorem submodularMatroidGreedyStepM_pure [LawfulMonad m]
    (f : Finset α → β) (indep : Finset α → Bool) (u : List α) (S : Finset α) :
    submodularMatroidGreedyStepM (fun T => (pure (f T) : m β)) (fun T => pure (indep T)) u S =
      pure (submodularMatroidGreedyStep f indep u S) := by
  simp only [submodularMatroidGreedyStepM, submodularMatroidGreedyStep, filterIndepM_pure,
    pure_bind]
  rw [← feasibleCandidates]
  cases feasibleCandidates indep u S with
  | nil => rfl
  | cons c₀ cs => simp [scanCandidatesM_pure]

@[simp] theorem submodularMatroidGreedyLoopM_pure [LawfulMonad m]
    (f : Finset α → β) (indep : Finset α → Bool) (u : List α) (k : ℕ) (S : Finset α) :
    submodularMatroidGreedyLoopM (fun T => (pure (f T) : m β)) (fun T => pure (indep T)) u k S =
      pure (submodularMatroidGreedyLoop f indep u k S) := by
  induction k generalizing S with
  | zero => rfl
  | succ k ih =>
    simp only [submodularMatroidGreedyLoopM, submodularMatroidGreedyLoop,
      submodularMatroidGreedyStepM_pure, pure_bind]
    cases submodularMatroidGreedyStep f indep u S with
    | none => rfl
    | some S' => exact ih S'

@[simp] theorem submodularMatroidGreedyM_pure [LawfulMonad m]
    (f : Finset α → β) (indep : Finset α → Bool) (xs : List α) :
    submodularMatroidGreedyM (fun T => (pure (f T) : m β)) (fun T => pure (indep T)) xs =
      pure (submodularMatroidGreedy f indep xs) :=
  submodularMatroidGreedyLoopM_pure f indep xs.eraseDups _ ∅

@[simp] theorem idRun_submodularMatroidGreedyM
    (evalSet : Finset α → Id β) (indepM : Finset α → Id Bool) (xs : List α) :
    Id.run (submodularMatroidGreedyM evalSet indepM xs) =
      submodularMatroidGreedy (fun T => Id.run (evalSet T)) (fun T => Id.run (indepM T)) xs :=
  submodularMatroidGreedyM_pure (m := Id) (fun T => Id.run (evalSet T))
    (fun T => Id.run (indepM T)) xs

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_filterIndepM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (indepM : Finset α → m Bool) (S : Finset α) (cs : List α) :
    φ (filterIndepM indepM S cs) = filterIndepM (fun T => φ (indepM T)) S cs := by
  induction cs with
  | nil => simp [filterIndepM, hφ.map_pure]
  | cons c cs ih =>
    simp only [filterIndepM, hφ.map_bind, hφ.map_pure, ih]

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_submodularMatroidGreedyStepM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (evalSet : Finset α → m β) (indepM : Finset α → m Bool) (u : List α) (S : Finset α) :
    φ (submodularMatroidGreedyStepM evalSet indepM u S) =
      submodularMatroidGreedyStepM (fun T => φ (evalSet T)) (fun T => φ (indepM T)) u S := by
  simp only [submodularMatroidGreedyStepM, hφ.map_bind, hφ.map_filterIndepM]
  congr 1
  funext cands
  cases cands with
  | nil => exact hφ.map_pure _
  | cons c₀ cs =>
    simp only [hφ.map_bind, hφ.map_scanCandidatesM, hφ.map_pure]

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_submodularMatroidGreedyLoopM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (evalSet : Finset α → m β) (indepM : Finset α → m Bool) (u : List α) (k : ℕ) (S : Finset α) :
    φ (submodularMatroidGreedyLoopM evalSet indepM u k S) =
      submodularMatroidGreedyLoopM (fun T => φ (evalSet T)) (fun T => φ (indepM T)) u k S := by
  induction k generalizing S with
  | zero => exact hφ.map_pure _
  | succ k ih =>
    simp only [submodularMatroidGreedyLoopM, hφ.map_bind, hφ.map_submodularMatroidGreedyStepM]
    congr 1
    funext o
    cases o with
    | none => exact hφ.map_pure _
    | some S' => exact ih S'

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_submodularMatroidGreedyM
    {φ : {γ : Type} → m γ → n γ} (hφ : IsMonadHom m n φ)
    (evalSet : Finset α → m β) (indepM : Finset α → m Bool) (xs : List α) :
    φ (submodularMatroidGreedyM evalSet indepM xs) =
      submodularMatroidGreedyM (fun T => φ (evalSet T)) (fun T => φ (indepM T)) xs :=
  hφ.map_submodularMatroidGreedyLoopM evalSet indepM xs.eraseDups _ ∅

end Bridges

end Algorithm

/-! ## The greedy chain, feasibility, and maximality -/

section Chain

variable {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]

/-- The chain `S₀ = ∅ ⊆ S₁ ⊆ ⋯` of greedy prefixes over the ground list `u`: `S (t + 1)` is the next
greedy prefix, or `S t` once no feasible candidate remains. -/
@[expose] def submodularMatroidGreedyChain (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) : ℕ → Finset α
  | 0 => ∅
  | t + 1 =>
    (submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)).getD
      (submodularMatroidGreedyChain f indep u t)

theorem mem_feasibleCandidates {indep : Finset α → Bool} {u : List α} {S : Finset α} {c : α} :
    c ∈ feasibleCandidates indep u S ↔ c ∈ u ∧ c ∉ S ∧ indep (insert c S) = true := by
  simp only [feasibleCandidates, List.mem_filter, decide_eq_true_eq, and_assoc]

/-- A successful greedy round inserts a feasible candidate `c` maximizing `f (insert c S)` over all
feasible candidates. -/
theorem exists_of_submodularMatroidGreedyStep_eq_some {f : Finset α → β} {indep : Finset α → Bool}
    {u : List α} {S S' : Finset α} (h : submodularMatroidGreedyStep f indep u S = some S') :
    ∃ c ∈ feasibleCandidates indep u S, S' = insert c S ∧
      ∀ x ∈ feasibleCandidates indep u S, f (insert x S) ≤ f S' := by
  unfold submodularMatroidGreedyStep at h
  rcases hc : feasibleCandidates indep u S with _ | ⟨c₀, cs⟩
  · simp only [hc, reduceCtorEq] at h
  · simp only [hc, Option.some.injEq] at h
    subst h
    set r := scanCandidates f S c₀ (f (insert c₀ S)) cs
    have hval : r.2 = f (insert r.1 S) := scanCandidates_snd_eq f S rfl cs
    refine ⟨r.1, scanCandidates_fst_mem f S c₀ _ cs, rfl, fun x hx => ?_⟩
    rw [← hval]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_scanCandidates_snd f S x _ cs
    · exact forall_le_scanCandidates_snd f S c₀ _ cs x hx

theorem submodularMatroidGreedyStep_eq_none_iff {f : Finset α → β} {indep : Finset α → Bool}
    {u : List α} {S : Finset α} :
    submodularMatroidGreedyStep f indep u S = none ↔ feasibleCandidates indep u S = [] := by
  unfold submodularMatroidGreedyStep
  rcases feasibleCandidates indep u S with _ | ⟨c₀, cs⟩ <;> simp

@[simp] theorem submodularMatroidGreedyChain_zero (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) : submodularMatroidGreedyChain f indep u 0 = ∅ := rfl

theorem submodularMatroidGreedyChain_succ (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) (t : ℕ) :
    submodularMatroidGreedyChain f indep u (t + 1) =
      (submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)).getD
        (submodularMatroidGreedyChain f indep u t) := rfl

/-- Once a round finds no feasible candidate, the greedy chain is constant. -/
theorem submodularMatroidGreedyChain_add_of_step_eq_none {f : Finset α → β}
    {indep : Finset α → Bool} {u : List α} {t : ℕ}
    (h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t) = none)
    (k : ℕ) :
    submodularMatroidGreedyChain f indep u (t + k) = submodularMatroidGreedyChain f indep u t := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [← Nat.add_assoc, submodularMatroidGreedyChain_succ, ih, h, Option.getD_none]

private theorem submodularMatroidGreedyLoop_chain (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) (k t : ℕ) :
    submodularMatroidGreedyLoop f indep u k (submodularMatroidGreedyChain f indep u t) =
      submodularMatroidGreedyChain f indep u (t + k) := by
  induction k generalizing t with
  | zero => rfl
  | succ k ih =>
    simp only [submodularMatroidGreedyLoop]
    rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
      with _ | S'
    · exact (submodularMatroidGreedyChain_add_of_step_eq_none h (k + 1)).symm
    · have hS' : S' = submodularMatroidGreedyChain f indep u (t + 1) := by
        rw [submodularMatroidGreedyChain_succ, h, Option.getD_some]
      dsimp only
      rw [hS', ih (t + 1), Nat.add_right_comm, Nat.add_assoc]

/-- The greedy output is the prefix `S n` of the greedy chain, `n = xs.eraseDups.length`. -/
theorem submodularMatroidGreedy_eq_chain (f : Finset α → β) (indep : Finset α → Bool)
    (xs : List α) :
    submodularMatroidGreedy f indep xs =
      submodularMatroidGreedyChain f indep xs.eraseDups xs.eraseDups.length := by
  have h := submodularMatroidGreedyLoop_chain f indep xs.eraseDups xs.eraseDups.length 0
  rw [Nat.zero_add] at h
  exact h

/-- The greedy loop only adds elements. -/
theorem subset_submodularMatroidGreedyLoop (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) (k : ℕ) (S : Finset α) : S ⊆ submodularMatroidGreedyLoop f indep u k S := by
  induction k generalizing S with
  | zero => exact Finset.Subset.refl S
  | succ k ih =>
    simp only [submodularMatroidGreedyLoop]
    rcases h : submodularMatroidGreedyStep f indep u S with _ | S'
    · exact Finset.Subset.refl S
    · obtain ⟨c, -, rfl, -⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
      exact (Finset.subset_insert c S).trans (ih _)

theorem submodularMatroidGreedyChain_subset_succ (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) (t : ℕ) :
    submodularMatroidGreedyChain f indep u t ⊆ submodularMatroidGreedyChain f indep u (t + 1) := by
  rw [submodularMatroidGreedyChain_succ]
  rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
    with _ | S'
  · exact Finset.Subset.refl _
  · obtain ⟨c, -, rfl, -⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
    exact Finset.subset_insert c _

theorem monotone_submodularMatroidGreedyChain (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) : Monotone (submodularMatroidGreedyChain f indep u) :=
  monotone_nat_of_le_succ (submodularMatroidGreedyChain_subset_succ f indep u)

theorem submodularMatroidGreedyChain_subset_toFinset (f : Finset α → β)
    (indep : Finset α → Bool) (u : List α) (t : ℕ) :
    submodularMatroidGreedyChain f indep u t ⊆ u.toFinset := by
  induction t with
  | zero => exact Finset.empty_subset _
  | succ t ih =>
    rw [submodularMatroidGreedyChain_succ]
    rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
      with _ | S'
    · exact ih
    · obtain ⟨c, hc, rfl, -⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
      exact Finset.insert_subset (List.mem_toFinset.mpr (mem_feasibleCandidates.mp hc).1) ih

theorem indep_submodularMatroidGreedyChain {f : Finset α → β} {indep : Finset α → Bool}
    (h0 : indep ∅ = true) (u : List α) (t : ℕ) :
    indep (submodularMatroidGreedyChain f indep u t) = true := by
  induction t with
  | zero => exact h0
  | succ t ih =>
    rw [submodularMatroidGreedyChain_succ]
    rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
      with _ | S'
    · exact ih
    · obtain ⟨c, hc, rfl, -⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
      exact (mem_feasibleCandidates.mp hc).2.2

theorem card_submodularMatroidGreedyChain_le (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) (t : ℕ) : (submodularMatroidGreedyChain f indep u t).card ≤ t := by
  induction t with
  | zero => simp
  | succ t ih =>
    rw [submodularMatroidGreedyChain_succ]
    rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
      with _ | S'
    · exact ih.trans (Nat.le_succ t)
    · obtain ⟨c, -, rfl, -⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
      exact (Finset.card_insert_le c _).trans (Nat.succ_le_succ ih)

/-- Each prefix either has exactly `t` elements or the algorithm has already run out of feasible
candidates. -/
private theorem card_eq_or_feasibleCandidates_eq_nil (f : Finset α → β) (indep : Finset α → Bool)
    (u : List α) (t : ℕ) :
    (submodularMatroidGreedyChain f indep u t).card = t ∨
      feasibleCandidates indep u (submodularMatroidGreedyChain f indep u t) = [] := by
  induction t with
  | zero => exact Or.inl rfl
  | succ t ih =>
    rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
      with _ | S'
    · right
      rw [submodularMatroidGreedyChain_succ, h, Option.getD_none]
      exact submodularMatroidGreedyStep_eq_none_iff.mp h
    · rcases ih with hcard | hnil
      · left
        obtain ⟨c, hc, hS', -⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
        rw [submodularMatroidGreedyChain_succ, h, Option.getD_some, hS',
          Finset.card_insert_of_notMem (mem_feasibleCandidates.mp hc).2.1, hcard]
      · cases h.symm.trans (submodularMatroidGreedyStep_eq_none_iff.mpr hnil)

/-- After `u.toFinset.card` rounds no feasible candidate remains. -/
theorem feasibleCandidates_submodularMatroidGreedyChain_card_eq_nil (f : Finset α → β)
    (indep : Finset α → Bool) (u : List α) :
    feasibleCandidates indep u (submodularMatroidGreedyChain f indep u u.toFinset.card) = [] := by
  rcases card_eq_or_feasibleCandidates_eq_nil f indep u u.toFinset.card with hcard | hnil
  · have hall : submodularMatroidGreedyChain f indep u u.toFinset.card = u.toFinset :=
      Finset.eq_of_subset_of_card_le (submodularMatroidGreedyChain_subset_toFinset f indep u _)
        hcard.ge
    refine List.eq_nil_iff_forall_not_mem.mpr fun c hc => ?_
    have hc' := mem_feasibleCandidates.mp hc
    have hmem : c ∈ submodularMatroidGreedyChain f indep u u.toFinset.card := by
      rw [hall]
      exact List.mem_toFinset.mpr hc'.1
    exact hc'.2.1 hmem
  · exact hnil

/-- The greedy output is a subset of the ground list. -/
theorem submodularMatroidGreedy_subset_toFinset (f : Finset α → β) (indep : Finset α → Bool)
    (xs : List α) : submodularMatroidGreedy f indep xs ⊆ xs.toFinset := by
  rw [submodularMatroidGreedy_eq_chain]
  simpa using submodularMatroidGreedyChain_subset_toFinset f indep xs.eraseDups _

/-- The greedy output is independent whenever `∅` is. -/
theorem indep_submodularMatroidGreedy {f : Finset α → β} {indep : Finset α → Bool}
    (h0 : indep ∅ = true) (xs : List α) : indep (submodularMatroidGreedy f indep xs) = true := by
  rw [submodularMatroidGreedy_eq_chain]
  exact indep_submodularMatroidGreedyChain h0 _ _

/-- The greedy output is maximal: no element of the ground list can be added to it while
preserving independence. -/
theorem not_indep_insert_submodularMatroidGreedy (f : Finset α → β) (indep : Finset α → Bool)
    {xs : List α} {x : α} (hx : x ∈ xs) (hxG : x ∉ submodularMatroidGreedy f indep xs) :
    indep (insert x (submodularMatroidGreedy f indep xs)) = false := by
  have hnil := feasibleCandidates_submodularMatroidGreedyChain_card_eq_nil f indep xs.eraseDups
  rw [List.toFinset_eraseDups, ← List.length_eraseDups] at hnil
  rw [submodularMatroidGreedy_eq_chain] at hxG ⊢
  by_contra hind
  exact List.eq_nil_iff_forall_not_mem.mp hnil x
    (mem_feasibleCandidates.mpr ⟨List.mem_eraseDups.mpr hx, hxG, by simpa using hind⟩)

/-- Under an independence test implementing `M : Matroid α`, the greedy output is a basis of the
ground list, `M.IsBasis' G {x | x ∈ xs}`. -/
theorem submodularMatroidGreedy_isBasis' {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (f : Finset α → β)
    (xs : List α) :
    M.IsBasis' ((submodularMatroidGreedy f indep xs : Finset α) : Set α) {x | x ∈ xs} := by
  have h0 : indep ∅ = true := (hM ∅).mpr (by simp)
  refine ⟨⟨(hM _).mp (indep_submodularMatroidGreedy h0 xs), fun x hx =>
    List.mem_toFinset.mp (submodularMatroidGreedy_subset_toFinset f indep xs hx)⟩, ?_⟩
  intro J ⟨hJ_ind, hJ_sub⟩ hsub e heJ
  by_contra heG
  have hfalse := not_indep_insert_submodularMatroidGreedy f indep (hJ_sub heJ) heG
  have hind : M.Indep ((insert e (submodularMatroidGreedy f indep xs) : Finset α) : Set α) := by
    rw [Finset.coe_insert]
    exact hJ_ind.subset (Set.insert_subset heJ hsub)
  rw [← hM] at hind
  simp [hind] at hfalse

end Chain

/-! ## The charging argument -/

section Charging

variable {ι : Type*} {β : Type*}
  [AddCommGroup β] [PartialOrder β] [IsOrderedAddMonoid β]

/-- Sorted charging: if each `o ∈ O` costs at most `d s` for every stage `s < σ o`, and at most
`p * t` elements have `σ o ≤ t`, then `∑ O c ≤ ∑ j < |O|, d (j / p)`. -/
private theorem sum_le_sum_range_card_div {O : Finset ι} {σ : ι → ℕ} {c : ι → β} {d : ℕ → β}
    {p : ℕ} (hc : ∀ o ∈ O, ∀ s < σ o, c o ≤ d s)
    (hcount : ∀ t, (O.filter fun o => σ o ≤ t).card ≤ p * t) :
    ∑ o ∈ O, c o ≤ ∑ j ∈ Finset.range O.card, d (j / p) := by
  classical
  induction O using Finset.induction_on_max_value σ with
  | empty => simp
  | insert a s has hmax ih =>
    have hc' : ∀ o ∈ s, ∀ t < σ o, c o ≤ d t :=
      fun o ho => hc o (Finset.mem_insert_of_mem ho)
    have hcount' : ∀ t, (s.filter fun o => σ o ≤ t).card ≤ p * t := fun t =>
      (Finset.card_le_card (Finset.filter_subset_filter _ (Finset.subset_insert a s))).trans
        (hcount t)
    rw [Finset.sum_insert has, Finset.card_insert_of_notMem has, Finset.sum_range_succ,
      add_comm (c a)]
    refine add_le_add (ih hc' hcount') (hc a (Finset.mem_insert_self a s) _ ?_)
    by_contra hge
    have hall : (insert a s).filter (fun o => σ o ≤ s.card / p) = insert a s :=
      Finset.filter_true_of_mem fun o ho => by
        rcases Finset.mem_insert.mp ho with rfl | ho
        · omega
        · exact (hmax o ho).trans (by omega)
    have h1 := hcount (s.card / p)
    rw [hall, Finset.card_insert_of_notMem has] at h1
    have h2 := Nat.mul_div_le s.card p
    omega

omit [PartialOrder β] [IsOrderedAddMonoid β] in
/-- Block decomposition `∑ j < p * N, d (j / p) = p • ∑ s < N, d s`. -/
private theorem sum_range_mul_div (d : ℕ → β) (p N : ℕ) (hp : 0 < p) :
    ∑ j ∈ Finset.range (p * N), d (j / p) = p • ∑ s ∈ Finset.range N, d s := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [mul_add_one, Finset.sum_range_add, ih, Finset.sum_range_succ (fun s => d s), smul_add]
    congr 1
    have hblock : ∀ j ∈ Finset.range p, d ((p * N + j) / p) = d N := by
      intro j hj
      congr 1
      rw [Nat.mul_comm, Nat.add_comm, Nat.add_mul_div_right _ _ hp,
        Nat.div_eq_of_lt (Finset.mem_range.mp hj), Nat.zero_add]
    rw [Finset.sum_congr rfl hblock, Finset.sum_const, Finset.card_range]

/-- Charging with stages bounded by `N`: `∑ O c ≤ p • ∑ s < N, d s` for nonnegative `d`. -/
private theorem sum_le_nsmul_sum_range {O : Finset ι} {σ : ι → ℕ} {c : ι → β} {d : ℕ → β}
    {p N : ℕ} (hd : ∀ s, 0 ≤ d s) (hσ : ∀ o ∈ O, σ o ≤ N)
    (hc : ∀ o ∈ O, ∀ s < σ o, c o ≤ d s)
    (hcount : ∀ t, (O.filter fun o => σ o ≤ t).card ≤ p * t) :
    ∑ o ∈ O, c o ≤ p • ∑ s ∈ Finset.range N, d s := by
  have hON : O.card ≤ p * N := by
    have h := hcount N
    rwa [Finset.filter_true_of_mem hσ] at h
  rcases Nat.eq_zero_or_pos p with rfl | hp
  · have hO : O = ∅ := Finset.card_eq_zero.mp (by simpa using hON)
    simp [hO]
  calc ∑ o ∈ O, c o ≤ ∑ j ∈ Finset.range O.card, d (j / p) := sum_le_sum_range_card_div hc hcount
    _ ≤ ∑ j ∈ Finset.range (p * N), d (j / p) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hON) fun j _ _ => hd _
    _ = p • ∑ s ∈ Finset.range N, d s := sum_range_mul_div d p N hp

end Charging

/-! ## Approximation guarantees -/

section Approximation

variable {α : Type*} {β : Type*} [DecidableEq α]
  [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β]

omit [AddCommGroup β] [IsOrderedAddMonoid β] in
/-- A feasible element `o ∉ S t` of `u` cannot gain more over `S t` than the greedy round did. -/
theorem le_submodularMatroidGreedyChain_succ {f : Finset α → β} {indep : Finset α → Bool}
    {u : List α} {t : ℕ} {o : α} (hou : o ∈ u) (hoS : o ∉ submodularMatroidGreedyChain f indep u t)
    (hind : indep (insert o (submodularMatroidGreedyChain f indep u t)) = true) :
    f (insert o (submodularMatroidGreedyChain f indep u t)) ≤
      f (submodularMatroidGreedyChain f indep u (t + 1)) := by
  have hfeas : o ∈ feasibleCandidates indep u (submodularMatroidGreedyChain f indep u t) :=
    mem_feasibleCandidates.mpr ⟨hou, hoS, hind⟩
  rcases h : submodularMatroidGreedyStep f indep u (submodularMatroidGreedyChain f indep u t)
    with _ | S'
  · rw [submodularMatroidGreedyStep_eq_none_iff] at h
    simp [h] at hfeas
  · obtain ⟨c, -, -, hmax⟩ := exists_of_submodularMatroidGreedyStep_eq_some h
    rw [submodularMatroidGreedyChain_succ, h, Option.getD_some]
    exact hmax o hfeas

/-- **Chain-level charging** ([CalinescuChekuriPalVondrak2011], Appendix B). Let `indep` be a
`p`-system, `O ⊆ u.toFinset` independent, and `f` monotone. If each `o ∈ O` costs at most the gain
`f S (t + 1) - f S t` of every greedy round `t < n` in which `o` is still feasible, then
`∑ O c ≤ p • (f S n - f ∅)`, where `n = u.toFinset.card`. -/
theorem sum_le_nsmul_sub_of_submodularMatroidGreedyChain {f : Finset α → β}
    {indep : Finset α → Bool} {p : ℕ} (hmono : Monotone f)
    (hsys : IsPSystem (fun S => indep S = true) p) {u : List α} {O : Finset α}
    (hO : indep O = true) (hOu : O ⊆ u.toFinset) {c : α → β}
    (hc : ∀ o ∈ O, ∀ t < u.toFinset.card, o ∉ submodularMatroidGreedyChain f indep u t →
      indep (insert o (submodularMatroidGreedyChain f indep u t)) = true →
      c o ≤ f (submodularMatroidGreedyChain f indep u (t + 1)) -
        f (submodularMatroidGreedyChain f indep u t)) :
    ∑ o ∈ O, c o ≤
      p • (f (submodularMatroidGreedyChain f indep u u.toFinset.card) - f ∅) := by
  classical
  set S := submodularMatroidGreedyChain f indep u with hS
  set n := u.toFinset.card
  -- `P o t`: by round `t`, `o` has been selected or has become infeasible.
  let P : α → ℕ → Prop := fun o t => o ∈ S t ∨ indep (insert o (S t)) = false
  have hPn : ∀ o ∈ O, P o n := by
    intro o ho
    by_cases hoS : o ∈ S n
    · exact Or.inl hoS
    · right
      by_contra hind
      have hnil := feasibleCandidates_submodularMatroidGreedyChain_card_eq_nil f indep u
      exact List.eq_nil_iff_forall_not_mem.mp hnil o (mem_feasibleCandidates.mpr
        ⟨List.mem_toFinset.mp (hOu ho), hoS, by simpa using hind⟩)
  have hPmono : ∀ o s t, s ≤ t → P o s → P o t := by
    intro o s t hst hPs
    have hsub : S s ⊆ S t := monotone_submodularMatroidGreedyChain f indep u hst
    by_cases hot : o ∈ S t
    · exact Or.inl hot
    · right
      rcases hPs with hos | hind
      · exact absurd (hsub hos) hot
      · by_contra hind'
        have h' : indep (insert o (S t)) = true := by simpa using hind'
        have := hsys.indep_of_subset h' (Finset.insert_subset_insert o hsub)
        simp [hind] at this
  -- `σ o`: the first round by which `o ∈ O` is selected or infeasible.
  have hex : ∀ o, ∃ t, o ∈ O → P o t := fun o => ⟨n, hPn o⟩
  let σ : α → ℕ := fun o => Nat.find (hex o)
  have hσspec : ∀ o ∈ O, σ o ≤ n ∧ P o (σ o) ∧ ∀ s < σ o, ¬ P o s := fun o ho =>
    ⟨Nat.find_min' (hex o) (hPn o), Nat.find_spec (hex o) ho,
      fun s hs hPs => Nat.find_min (hex o) hs fun _ => hPs⟩
  have hd : ∀ s, 0 ≤ f (S (s + 1)) - f (S s) := fun s =>
    sub_nonneg.mpr (hmono (submodularMatroidGreedyChain_subset_succ f indep u s))
  have key := sum_le_nsmul_sum_range (O := O) (σ := σ) (c := c) (p := p) (N := n)
    (d := fun s => f (S (s + 1)) - f (S s)) hd (fun o ho => (hσspec o ho).1)
    (fun o ho s hs => by
      have hnot := (hσspec o ho).2.2 s hs
      simp only [P, not_or, Bool.not_eq_false] at hnot
      exact hc o ho s (lt_of_lt_of_le hs (hσspec o ho).1) hnot.1 hnot.2)
    (fun t => by
      have hT : ((O.filter fun o => σ o ≤ t).card) ≤ p * (S t).card := by
        refine hsys.card_le_mul_card_of_blocked (indep_submodularMatroidGreedyChain
          hsys.indep_empty u t) (hsys.indep_of_subset hO (Finset.filter_subset _ O)) ?_
        intro o ho hoS hind
        obtain ⟨hoO, hσt⟩ := Finset.mem_filter.mp ho
        rcases hPmono o (σ o) t hσt (hσspec o hoO).2.1 with h | h
        · exact hoS h
        · simp [h] at hind
      exact hT.trans (Nat.mul_le_mul_left p (card_submodularMatroidGreedyChain_le f indep u t)))
  rw [Finset.sum_range_sub (fun s => f (S s))] at key
  exact key

/-- **Fisher–Nemhauser–Wolsey greedy bound** ([FisherNemhauserWolsey1978];
[CalinescuChekuriPalVondrak2011], Appendix B). For a monotone submodular `f`, a `p`-system
`indep` and every independent `O ⊆ xs.toFinset`, the greedy output `G` satisfies
`f O + p • f ∅ ≤ (p + 1) • f G`, i.e. `f O - f ∅ ≤ (p + 1) • (f G - f ∅)`. -/
theorem add_nsmul_le_succ_nsmul_submodularMatroidGreedy {f : Finset α → β}
    (hf : IsSubmodular f) (hmono : Monotone f) {indep : Finset α → Bool} {p : ℕ}
    (hsys : IsPSystem (fun S => indep S = true) p) {xs : List α} {O : Finset α}
    (hO : indep O = true) (hOxs : O ⊆ xs.toFinset) :
    f O + p • f ∅ ≤ (p + 1) • f (submodularMatroidGreedy f indep xs) := by
  set u := xs.eraseDups
  have hn : u.length = u.toFinset.card := by
    simp only [u, List.length_eraseDups, List.toFinset_eraseDups]
  have hG : submodularMatroidGreedy f indep xs =
      submodularMatroidGreedyChain f indep u u.toFinset.card := by
    rw [submodularMatroidGreedy_eq_chain, ← hn]
  rw [hG]
  set G := submodularMatroidGreedyChain f indep u u.toFinset.card
  have hOu : O \ G ⊆ u.toFinset := by
    simpa only [u, List.toFinset_eraseDups] using Finset.sdiff_subset.trans hOxs
  have hcharge := sum_le_nsmul_sub_of_submodularMatroidGreedyChain (c := marginalGain f G) hmono
    hsys (hsys.indep_of_subset hO Finset.sdiff_subset) hOu
    (fun o ho t ht hoS hind => by
      have hsub : submodularMatroidGreedyChain f indep u t ⊆ G :=
        monotone_submodularMatroidGreedyChain f indep u ht.le
      have hou : o ∈ u := List.mem_toFinset.mp (hOu ho)
      calc marginalGain f G o
          ≤ marginalGain f (submodularMatroidGreedyChain f indep u t) o :=
            hf.marginalGain_le_of_monotone hmono o hsub
        _ ≤ _ := sub_le_sub_right (le_submodularMatroidGreedyChain_succ hou hoS hind) _)
  have hsum := hf.sub_le_sum_marginalGain_of_monotone hmono G O
  have hmain : f O - f G ≤ p • (f G - f ∅) := hsum.trans hcharge
  rw [nsmul_sub, sub_le_iff_le_add] at hmain
  calc f O + p • f ∅ ≤ p • f G - p • f ∅ + f G + p • f ∅ := add_le_add_left hmain _
    _ = (p + 1) • f G := by rw [succ_nsmul]; abel

end Approximation

/-! ## Corollaries: ordered fields, matroids, matroid intersections, modular objectives -/

section Corollaries

variable {α : Type*} [DecidableEq α]

/-- Ordered-field form of the greedy bound: `f O / (p + 1) ≤ f G` when `0 ≤ f ∅`. -/
theorem div_succ_le_submodularMatroidGreedy {β : Type*} [Field β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    (hf0 : 0 ≤ f ∅) {indep : Finset α → Bool} {p : ℕ}
    (hsys : IsPSystem (fun S => indep S = true) p) {xs : List α} {O : Finset α}
    (hO : indep O = true) (hOxs : O ⊆ xs.toFinset) :
    f O / (p + 1) ≤ f (submodularMatroidGreedy f indep xs) := by
  have h := add_nsmul_le_succ_nsmul_submodularMatroidGreedy hf hmono hsys hO hOxs
  rw [nsmul_eq_mul, nsmul_eq_mul] at h
  push_cast at h
  have hp : (0 : β) < (p : β) + 1 := by positivity
  rw [div_le_iff₀ hp]
  nlinarith [mul_nonneg (Nat.cast_nonneg (α := β) p) hf0]

omit [DecidableEq α] in
private theorem isPSystem_of_matroid {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) :
    IsPSystem (fun S => indep S = true) 1 :=
  (isPSystem_matroid M).of_iff hM

omit [DecidableEq α] in
private theorem isPSystem_of_iInter_matroid {ι : Type*} [Fintype ι] [Nonempty ι]
    {M : ι → Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ ∀ i, (M i).Indep (S : Set α)) :
    IsPSystem (fun S => indep S = true) (Fintype.card ι) :=
  (isPSystem_iInter_matroid M).of_iff hM

/-- **`1/2`-approximation over a matroid** ([FisherNemhauserWolsey1978];
[CalinescuChekuriPalVondrak2011], Section 1, the case `p = 1`): under an independence test
implementing `M : Matroid α`, `f O + f ∅ ≤ 2 • f G` for every independent `O ⊆ xs.toFinset`. -/
theorem add_le_two_nsmul_submodularMatroidGreedy_of_matroid {β : Type*} [AddCommGroup β]
    [LinearOrder β] [IsOrderedAddMonoid β] {f : Finset α → β} (hf : IsSubmodular f)
    (hmono : Monotone f) {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) {xs : List α} {O : Finset α}
    (hO : M.Indep (O : Set α)) (hOxs : O ⊆ xs.toFinset) :
    f O + f ∅ ≤ 2 • f (submodularMatroidGreedy f indep xs) := by
  simpa using add_nsmul_le_succ_nsmul_submodularMatroidGreedy hf hmono
    (isPSystem_of_matroid hM) ((hM O).mpr hO) hOxs

/-- **`1/2`-approximation over a matroid**, ordered-field form: `f O / 2 ≤ f G` when
`0 ≤ f ∅`. -/
theorem half_le_submodularMatroidGreedy_of_matroid {β : Type*} [Field β] [LinearOrder β]
    [IsStrictOrderedRing β] {f : Finset α → β} (hf : IsSubmodular f) (hmono : Monotone f)
    (hf0 : 0 ≤ f ∅) {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) {xs : List α} {O : Finset α}
    (hO : M.Indep (O : Set α)) (hOxs : O ⊆ xs.toFinset) :
    f O / 2 ≤ f (submodularMatroidGreedy f indep xs) := by
  have h := div_succ_le_submodularMatroidGreedy hf hmono hf0 (isPSystem_of_matroid hM)
    ((hM O).mpr hO) hOxs
  rwa [Nat.cast_one, one_add_one_eq_two] at h

/-- **`1/(k+1)`-approximation over an intersection of `k ≥ 1` matroids**
([FisherNemhauserWolsey1978]; [CalinescuChekuriPalVondrak2011], Section 1), ordered-group form:
`f O + k • f ∅ ≤ (k + 1) • f G` with `k = Fintype.card ι`. -/
theorem add_card_nsmul_le_submodularMatroidGreedy_of_iInter_matroid {β : Type*}
    [AddCommGroup β] [LinearOrder β] [IsOrderedAddMonoid β] {f : Finset α → β}
    (hf : IsSubmodular f) (hmono : Monotone f) {ι : Type*} [Fintype ι] [Nonempty ι]
    {M : ι → Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ ∀ i, (M i).Indep (S : Set α)) {xs : List α}
    {O : Finset α} (hO : ∀ i, (M i).Indep (O : Set α)) (hOxs : O ⊆ xs.toFinset) :
    f O + Fintype.card ι • f ∅ ≤
      (Fintype.card ι + 1) • f (submodularMatroidGreedy f indep xs) :=
  add_nsmul_le_succ_nsmul_submodularMatroidGreedy hf hmono (isPSystem_of_iInter_matroid hM)
    ((hM O).mpr hO) hOxs

/-- **`1/(k+1)`-approximation over an intersection of `k ≥ 1` matroids**
([FisherNemhauserWolsey1978]; [CalinescuChekuriPalVondrak2011], Section 1), ordered-field form:
`f O / (k + 1) ≤ f G` when `0 ≤ f ∅`. -/
theorem div_card_succ_le_submodularMatroidGreedy_of_iInter_matroid {β : Type*} [Field β]
    [LinearOrder β] [IsStrictOrderedRing β] {f : Finset α → β} (hf : IsSubmodular f)
    (hmono : Monotone f) (hf0 : 0 ≤ f ∅) {ι : Type*} [Fintype ι] [Nonempty ι]
    {M : ι → Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ ∀ i, (M i).Indep (S : Set α)) {xs : List α}
    {O : Finset α} (hO : ∀ i, (M i).Indep (O : Set α)) (hOxs : O ⊆ xs.toFinset) :
    f O / (Fintype.card ι + 1) ≤ f (submodularMatroidGreedy f indep xs) :=
  div_succ_le_submodularMatroidGreedy hf hmono hf0 (isPSystem_of_iInter_matroid hM)
    ((hM O).mpr hO) hOxs

/-- **Modular objectives on `p`-systems** ([Jenkyns1976]; [CalinescuChekuriPalVondrak2011],
Section 1): for nonnegative weights `w`, the greedy algorithm run on `modularSum w` satisfies
`∑ O w ≤ p • ∑ G w` for every independent `O ⊆ xs.toFinset`. -/
theorem sum_le_nsmul_sum_submodularMatroidGreedy {β : Type*} [AddCommGroup β] [LinearOrder β]
    [IsOrderedAddMonoid β] {w : α → β} (hw : ∀ x, 0 ≤ w x) {indep : Finset α → Bool} {p : ℕ}
    (hsys : IsPSystem (fun S => indep S = true) p) {xs : List α} {O : Finset α}
    (hO : indep O = true) (hOxs : O ⊆ xs.toFinset) :
    ∑ x ∈ O, w x ≤ p • ∑ x ∈ submodularMatroidGreedy (modularSum w) indep xs, w x := by
  set u := xs.eraseDups
  have hn : u.length = u.toFinset.card := by
    simp only [u, List.length_eraseDups, List.toFinset_eraseDups]
  have hG : submodularMatroidGreedy (modularSum w) indep xs =
      submodularMatroidGreedyChain (modularSum w) indep u u.toFinset.card := by
    rw [submodularMatroidGreedy_eq_chain, ← hn]
  have hOu : O ⊆ u.toFinset := by simpa only [u, List.toFinset_eraseDups] using hOxs
  have h := sum_le_nsmul_sub_of_submodularMatroidGreedyChain (c := w) (monotone_modularSum hw)
    hsys hO hOu (fun o ho t _ hoS hind => by
      have hle := le_submodularMatroidGreedyChain_succ (List.mem_toFinset.mp (hOu ho)) hoS hind
      rw [modularSum, Finset.sum_insert hoS] at hle
      exact le_sub_iff_add_le.mpr hle)
  rw [modularSum_empty, sub_zero] at h
  rw [hG]
  exact h

/-- **Greedy is optimal for nonnegative modular objectives on a matroid** (the `p = 1` case of
`sum_le_nsmul_sum_submodularMatroidGreedy`): `∑ O w ≤ ∑ G w` for every independent
`O ⊆ xs.toFinset`. Compare the Rado–Edmonds weight-sorted greedy
`Cslib.Algorithms.Lean.Matroid.sum_le_greedyMaxBasis_of_indep`, which reaches the same optimum by
scanning elements in decreasing weight order instead of re-evaluating marginal gains. -/
theorem sum_le_sum_submodularMatroidGreedy_of_matroid {β : Type*} [AddCommGroup β]
    [LinearOrder β] [IsOrderedAddMonoid β] {w : α → β} (hw : ∀ x, 0 ≤ w x) {M : Matroid α}
    {indep : Finset α → Bool} (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    {xs : List α} {O : Finset α} (hO : M.Indep (O : Set α)) (hOxs : O ⊆ xs.toFinset) :
    ∑ x ∈ O, w x ≤ ∑ x ∈ submodularMatroidGreedy (modularSum w) indep xs, w x := by
  simpa using sum_le_nsmul_sum_submodularMatroidGreedy hw (isPSystem_of_matroid hM)
    ((hM O).mpr hO) hOxs

end Corollaries

/-! ## Tightness of the `1/2` bound -/

section Tightness

/-- Independence test of the partition matroid on `Fin 3` with blocks `{0, 1}` and `{2}`, each of
capacity one: a set is independent unless it contains both `0` and `1`. -/
@[expose] def matroidTightIndep (S : Finset (Fin 3)) : Bool :=
  !(decide ((0 : Fin 3) ∈ S) && decide ((1 : Fin 3) ∈ S))

private theorem matroidTightIndep_empty : matroidTightIndep ∅ = true := by decide

private theorem matroidTightIndep_subset :
    ∀ ⦃A B : Finset (Fin 3)⦄, matroidTightIndep B = true → A ⊆ B →
      matroidTightIndep A = true := by
  decide

private theorem matroidTightIndep_augment :
    ∀ ⦃I J : Finset (Fin 3)⦄, matroidTightIndep I = true → matroidTightIndep J = true →
      I.card < J.card → ∃ e ∈ J, e ∉ I ∧ matroidTightIndep (insert e I) = true := by
  decide

/-- The partition matroid on `Fin 3` decided by `matroidTightIndep`. -/
noncomputable def matroidTightMatroid : Matroid (Fin 3) :=
  (IndepMatroid.ofFinset Set.univ (fun S => matroidTightIndep S = true) matroidTightIndep_empty
    matroidTightIndep_subset matroidTightIndep_augment (fun _ _ => Set.subset_univ _)).matroid

theorem matroidTightIndep_iff (S : Finset (Fin 3)) :
    matroidTightIndep S = true ↔ matroidTightMatroid.Indep (S : Set (Fin 3)) := by
  simp [matroidTightMatroid]

/-- Coverage sets of the tight instance: `0` and `2` both cover item `0`, and `1` covers item
`1`. -/
@[expose] def matroidTightCover : Fin 3 → Finset (Fin 2)
  | 0 => {0}
  | 1 => {1}
  | 2 => {0}

/-- Unit-weight coverage objective `S ↦ |⋃ s ∈ S, matroidTightCover s|` of the tight instance. -/
@[expose] def matroidTightObjective : Finset (Fin 3) → ℤ :=
  weightedCoverage matroidTightCover fun _ => 1

theorem isSubmodular_matroidTightObjective : IsSubmodular matroidTightObjective :=
  isSubmodular_weightedCoverage _ fun _ => zero_le_one

theorem monotone_matroidTightObjective : Monotone matroidTightObjective :=
  monotone_weightedCoverage _ fun _ => zero_le_one

/-- On the tight instance, greedy first picks `0` (all singletons have value `1`, and ties go to
the earliest candidate), then `2` (`1` is blocked by `0`), and stops at `{0, 2}`. -/
theorem submodularMatroidGreedy_matroidTight :
    submodularMatroidGreedy matroidTightObjective matroidTightIndep [0, 1, 2] = {0, 2} := by
  decide

/-- **Tightness of the `1/2` bound** ([FisherNemhauserWolsey1978];
[CalinescuChekuriPalVondrak2011], Section 1, which states that the greedy ratios are tight for
all `p`): a monotone submodular
coverage objective with `f ∅ = 0` and a partition matroid on three elements for which the greedy
value is exactly half the value of an independent set. -/
theorem exists_tight_submodularMatroidGreedy :
    ∃ (M : Matroid (Fin 3)) (indep : Finset (Fin 3) → Bool) (f : Finset (Fin 3) → ℤ)
      (xs : List (Fin 3)) (O : Finset (Fin 3)),
      (∀ S : Finset (Fin 3), indep S = true ↔ M.Indep (S : Set (Fin 3))) ∧
      IsSubmodular f ∧ Monotone f ∧ f ∅ = 0 ∧ M.Indep (O : Set (Fin 3)) ∧ O ⊆ xs.toFinset ∧
      0 < f O ∧ f O = 2 * f (submodularMatroidGreedy f indep xs) := by
  refine ⟨matroidTightMatroid, matroidTightIndep, matroidTightObjective, [0, 1, 2], {1, 2},
    matroidTightIndep_iff, isSubmodular_matroidTightObjective, monotone_matroidTightObjective,
    by decide, (matroidTightIndep_iff _).mp (by decide), by decide, by decide, ?_⟩
  rw [submodularMatroidGreedy_matroidTight]
  decide

end Tightness

end Cslib.Algorithms.Lean.Submodular
