/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Cslib.Foundations.Control.Monad.IsMonadHom
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.Algebra.Order.Monoid.Defs
public import Mathlib.Combinatorics.Matroid.Basic
public import Mathlib.Data.List.Sort
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.Order.BigOperators.Group.List
import Mathlib.Combinatorics.Matroid.IndepAxioms
import Mathlib.Combinatorics.Matroid.Minor.Restrict
import Mathlib.Data.Finset.Card

/-!
# Matroid Greedy Algorithm and Weighted Optimality

This module defines the greedy matroid algorithm (both monadically over an arbitrary effectful
independence test `Finset α → m Bool` and purely over `Finset α → Bool`) and proves its structural
and weighted optimality guarantees against `Mathlib.Combinatorics.Matroid`.

The monadic formulation `greedySelectM` instantiates with `Id` to recover the pure algorithm
`greedySelect`, with `TimeM` for step-annotated analyses, and with `FreeM (IndepQuery α)` in
`Complexity.Algorithms.Lean.Query.Matroid.Greedy` to count independence-oracle queries explicitly.

## Main definitions

* `Cslib.Algorithms.Lean.Matroid.greedyStepM`, `greedySelectM`: monadic greedy scan over a list of
  candidate elements, augmenting the current independent `Finset α` whenever the oracle accepts.
* `Cslib.Algorithms.Lean.Matroid.greedyStep`, `greedySelect`: pure specializations.
* `Cslib.Algorithms.Lean.Matroid.greedyMaxBasisM`, `greedyMaxBasis`: sort candidates by
  nonincreasing weight `w` via `List.mergeSort` and run greedy selection.
* `Cslib.Algorithms.Lean.Matroid.greedyMinBasisM`, `greedyMinBasis`: sort candidates by
  nondecreasing weight `w` (Kruskal order) and run greedy selection.
* `Cslib.Algorithms.Lean.Matroid.greedyMaxIndepM`, `greedyMaxIndep`: filter candidates with
  `0 ≤ w x` before running `greedyMaxBasis`, handling arbitrary signed weights.

## Main results

* `greedyMaxBasis_eq_insertionSort`, `greedyMinBasis_eq_insertionSort`: stability bridge showing
  that `List.mergeSort`-based weighted selection agrees with `List.insertionSort`, enabling direct
  kernel `decide` reduction on concrete inputs even when weights have ties.
* `greedySelect_isBasis'`, `greedySelect_isBasis`, `greedySelect_isBase`: for any `Matroid α` and
  candidate list `xs : List α` (possibly containing duplicates), `greedySelect` computes a basis of
  `{x | x ∈ xs}`.
* `gale_dominance_nodup`: Gale's pointwise dominance theorem ([Gale1968], Theorem, p. 177): when
  `xs` is duplicate-free and sorted with respect to a reflexive relation `R`, the `j`-th greedy
  element dominates the `j`-th element of any independent subset `I` of `xs` under `R`.
* `sum_le_greedySelect_of_isBasis'`, `greedySelect_le_sum_of_isBasis'`, `sum_le_greedyMaxBasis`,
  `greedyMinBasis_le_sum`: Rado–Edmonds weighted basis optimality ([Rado1957]; [Edmonds1971],
  Section 2) for both maximum-weight and minimum-weight bases under arbitrary weights in an ordered
  commutative additive monoid (including unsigned `ℕ` weights for minimum-weight bases without
  negation).
* `sum_le_greedySelect_of_indep`, `sum_le_greedyMaxBasis_of_indep`: maximum-weight independent
  subset optimality for nonnegative weights (generalizing [CLRS2009], Section 16.4, Theorem 16.11
  from strictly positive to nonnegative weights).
* `sum_le_greedyMaxIndep`: maximum-weight independent subset optimality for arbitrary signed
  weights via nonnegative pre-filtering ([Edmonds1971], Section 2).
* `augment_of_forall_sum_le_greedyMaxBasis`, `exists_matroid_iff_forall_sum_le_greedyMaxBasis`,
  `exists_matroid_finset_iff_forall_sum_le_greedyMaxBasis`: converse and full Rado–Edmonds
  characterization ([Rado1957]; [Edmonds1971], Section 2): a finite hereditary system is a matroid
  if and only if `greedyMaxBasis` is optimal for all `ℕ`-valued weight functions.

## References

* [Rado1957] Richard Rado, *Note on Independence Functions*, 1957.
* [Gale1968] David Gale, *Optimal Assignments in an Ordered Set: An Application of Matroid Theory*,
  1968.
* [Edmonds1971] Jack Edmonds, *Matroids and the Greedy Algorithm*, 1971.
* [CLRS2009] Cormen, Leiserson, Rivest, and Stein, *Introduction to Algorithms* (3rd ed.),
  Section 16.4, Theorem 16.11.
-/

public section

open Cslib (IsMonadHom)

namespace Cslib.Algorithms.Lean.Matroid

/-! ## Monadic and pure greedy definitions -/

/-- One monadic step of the greedy matroid scan: query whether `insert x acc` is independent and
retain `x` when the test succeeds. -/
@[expose] def greedyStepM {α : Type} [DecidableEq α] {m : Type → Type*} [Monad m]
    (indep : Finset α → m Bool) (acc : Finset α) (x : α) : m (Finset α) := do
  if ← indep (insert x acc) then return insert x acc else return acc

/-- Monadic greedy matroid scan over a candidate list `xs`, starting from `∅`. -/
@[expose] def greedySelectM {α : Type} [DecidableEq α] {m : Type → Type*} [Monad m]
    (indep : Finset α → m Bool) (xs : List α) : m (Finset α) :=
  xs.foldlM (greedyStepM indep) ∅

/-- Pure greedy step over a Boolean independence test `indep : Finset α → Bool`. -/
@[expose] def greedyStep {α : Type*} [DecidableEq α]
    (indep : Finset α → Bool) (acc : Finset α) (x : α) : Finset α :=
  if indep (insert x acc) then insert x acc else acc

/-- Pure greedy selection over a candidate list `xs`, starting from `∅`. -/
@[expose] def greedySelect {α : Type*} [DecidableEq α]
    (indep : Finset α → Bool) (xs : List α) : Finset α :=
  xs.foldl (greedyStep indep) ∅

/-- Monadic maximum-weight basis selection: sort `xs` by nonincreasing weight `w` and run
`greedySelectM`. -/
@[expose] def greedyMaxBasisM {α : Type} {β : Type*} [DecidableEq α] [LinearOrder β]
    {m : Type → Type*} [Monad m]
    (indep : Finset α → m Bool) (w : α → β) (xs : List α) : m (Finset α) :=
  greedySelectM indep (xs.mergeSort (fun a b => decide (w b ≤ w a)))

/-- Pure maximum-weight basis selection: sort `xs` by nonincreasing weight `w` and run
`greedySelect`. -/
@[expose] def greedyMaxBasis {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) : Finset α :=
  greedySelect indep (xs.mergeSort (fun a b => decide (w b ≤ w a)))

/-- Monadic minimum-weight basis selection (Kruskal order): sort `xs` by nondecreasing weight `w`
and run `greedySelectM`. -/
@[expose] def greedyMinBasisM {α : Type} {β : Type*} [DecidableEq α] [LinearOrder β]
    {m : Type → Type*} [Monad m]
    (indep : Finset α → m Bool) (w : α → β) (xs : List α) : m (Finset α) :=
  greedySelectM indep (xs.mergeSort (fun a b => decide (w a ≤ w b)))

/-- Pure minimum-weight basis selection (Kruskal order): sort `xs` by nondecreasing weight `w` and
run `greedySelect`. -/
@[expose] def greedyMinBasis {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) : Finset α :=
  greedySelect indep (xs.mergeSort (fun a b => decide (w a ≤ w b)))

/-- Monadic maximum-weight independent-set selection under arbitrary signed weights: discard
negative-weight elements (`¬ 0 ≤ w x`) before running `greedyMaxBasisM`. -/
@[expose] def greedyMaxIndepM {α : Type} {β : Type*} [DecidableEq α] [Zero β] [LinearOrder β]
    {m : Type → Type*} [Monad m]
    (indep : Finset α → m Bool) (w : α → β) (xs : List α) : m (Finset α) :=
  greedyMaxBasisM indep w (xs.filter (fun x => decide (0 ≤ w x)))

/-- Pure maximum-weight independent-set selection under arbitrary signed weights: discard
negative-weight elements (`¬ 0 ≤ w x`) before running `greedyMaxBasis`. -/
@[expose] def greedyMaxIndep {α : Type*} {β : Type*} [DecidableEq α] [Zero β] [LinearOrder β]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) : Finset α :=
  greedyMaxBasis indep w (xs.filter (fun x => decide (0 ≤ w x)))

/-! ## Monad homomorphism laws -/

@[simp] theorem greedySelect_nil {α : Type*} [DecidableEq α] (indep : Finset α → Bool) :
    greedySelect indep [] = ∅ := rfl

@[simp] theorem greedySelectM_nil {α : Type} [DecidableEq α] {m : Type → Type*} [Monad m]
    (indep : Finset α → m Bool) :
    greedySelectM indep [] = pure ∅ := rfl

private theorem foldlM_greedyStepM_pure {α : Type} [DecidableEq α]
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (indep : Finset α → Bool) (acc : Finset α) (xs : List α) :
    xs.foldlM (greedyStepM (fun S => (pure (indep S) : m Bool))) acc =
      pure (xs.foldl (greedyStep indep) acc) := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
    simp only [List.foldlM_cons, List.foldl_cons, greedyStepM, greedyStep]
    cases indep (insert x acc) <;> simp [ih]

@[simp] theorem greedySelectM_pure {α : Type} [DecidableEq α]
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (indep : Finset α → Bool) (xs : List α) :
    greedySelectM (fun S => (pure (indep S) : m Bool)) xs = pure (greedySelect indep xs) :=
  foldlM_greedyStepM_pure indep ∅ xs

@[simp] theorem idRun_greedySelectM {α : Type} [DecidableEq α]
    (indep : Finset α → Id Bool) (xs : List α) :
    Id.run (greedySelectM indep xs) = greedySelect (fun S => Id.run (indep S)) xs :=
  greedySelectM_pure (m := Id) (fun S => Id.run (indep S)) xs

@[simp] theorem greedyMaxBasisM_pure {α : Type} {β : Type*} [DecidableEq α] [LinearOrder β]
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) :
    greedyMaxBasisM (fun S => (pure (indep S) : m Bool)) w xs =
      pure (greedyMaxBasis indep w xs) :=
  greedySelectM_pure indep _

@[simp] theorem idRun_greedyMaxBasisM {α : Type} {β : Type*} [DecidableEq α] [LinearOrder β]
    (indep : Finset α → Id Bool) (w : α → β) (xs : List α) :
    Id.run (greedyMaxBasisM indep w xs) = greedyMaxBasis (fun S => Id.run (indep S)) w xs :=
  greedyMaxBasisM_pure (m := Id) (fun S => Id.run (indep S)) w xs

@[simp] theorem greedyMinBasisM_pure {α : Type} {β : Type*} [DecidableEq α] [LinearOrder β]
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) :
    greedyMinBasisM (fun S => (pure (indep S) : m Bool)) w xs =
      pure (greedyMinBasis indep w xs) :=
  greedySelectM_pure indep _

@[simp] theorem idRun_greedyMinBasisM {α : Type} {β : Type*} [DecidableEq α] [LinearOrder β]
    (indep : Finset α → Id Bool) (w : α → β) (xs : List α) :
    Id.run (greedyMinBasisM indep w xs) = greedyMinBasis (fun S => Id.run (indep S)) w xs :=
  greedyMinBasisM_pure (m := Id) (fun S => Id.run (indep S)) w xs

@[simp] theorem greedyMaxIndepM_pure {α : Type} {β : Type*} [DecidableEq α] [Zero β] [LinearOrder β]
    {m : Type → Type*} [Monad m] [LawfulMonad m]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) :
    greedyMaxIndepM (fun S => (pure (indep S) : m Bool)) w xs =
      pure (greedyMaxIndep indep w xs) :=
  greedyMaxBasisM_pure indep w _

@[simp] theorem idRun_greedyMaxIndepM {α : Type} {β : Type*} [DecidableEq α] [Zero β]
    [LinearOrder β] (indep : Finset α → Id Bool) (w : α → β) (xs : List α) :
    Id.run (greedyMaxIndepM indep w xs) = greedyMaxIndep (fun S => Id.run (indep S)) w xs :=
  greedyMaxIndepM_pure (m := Id) (fun S => Id.run (indep S)) w xs

private theorem map_greedyStepM {α : Type} [DecidableEq α]
    {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f)
    (indep : Finset α → m Bool) (acc : Finset α) (x : α) :
    f (greedyStepM indep acc x) = greedyStepM (fun S => f (indep S)) acc x := by
  simp only [greedyStepM, hf.map_bind]
  congr 1
  funext b
  cases b <;> simp [hf.map_pure]

private theorem map_foldlM_greedyStepM {α : Type} [DecidableEq α]
    {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f)
    (indep : Finset α → m Bool) (acc : Finset α) (xs : List α) :
    f (xs.foldlM (greedyStepM indep) acc) =
      xs.foldlM (greedyStepM (fun S => f (indep S))) acc := by
  induction xs generalizing acc with
  | nil => simp [hf.map_pure]
  | cons x rest ih =>
    simp only [List.foldlM_cons, hf.map_bind, map_greedyStepM hf]
    congr 1
    funext acc'
    exact ih acc'

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_greedySelectM {α : Type} [DecidableEq α]
    {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f)
    (indep : Finset α → m Bool) (xs : List α) :
    f (greedySelectM indep xs) = greedySelectM (fun S => f (indep S)) xs :=
  map_foldlM_greedyStepM hf indep ∅ xs

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_greedyMaxBasisM {α : Type} {β : Type*} [DecidableEq α]
    [LinearOrder β] {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f)
    (indep : Finset α → m Bool) (w : α → β) (xs : List α) :
    f (greedyMaxBasisM indep w xs) = greedyMaxBasisM (fun S => f (indep S)) w xs :=
  hf.map_greedySelectM indep (xs.mergeSort (fun a b => decide (w b ≤ w a)))

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_greedyMinBasisM {α : Type} {β : Type*} [DecidableEq α]
    [LinearOrder β] {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f)
    (indep : Finset α → m Bool) (w : α → β) (xs : List α) :
    f (greedyMinBasisM indep w xs) = greedyMinBasisM (fun S => f (indep S)) w xs :=
  hf.map_greedySelectM indep (xs.mergeSort (fun a b => decide (w a ≤ w b)))

@[grind .]
theorem _root_.Cslib.IsMonadHom.map_greedyMaxIndepM {α : Type} {β : Type*} [DecidableEq α]
    [Zero β] [LinearOrder β] {m n : Type → Type*} [Monad m] [Monad n]
    {f : {γ : Type} → m γ → n γ} (hf : IsMonadHom m n f)
    (indep : Finset α → m Bool) (w : α → β) (xs : List α) :
    f (greedyMaxIndepM indep w xs) = greedyMaxIndepM (fun S => f (indep S)) w xs :=
  hf.map_greedyMaxBasisM indep w (xs.filter (fun x => decide (0 ≤ w x)))

/-! ### Stability bridge to `List.insertionSort` for symbolic proof reduction -/

private theorem orderedInsert_append_eq {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (a : α) : ∀ (l₁ l₂ : List α),
      (∀ b ∈ l₁, ¬ r a b) → (∀ c ∈ l₂, r a c) →
      List.orderedInsert r a (l₁ ++ l₂) = l₁ ++ a :: l₂
  | [], [], _, _ => by simp
  | [], c :: l₂, _, hl₂ => by
    simp [hl₂ c List.mem_cons_self]
  | b :: l₁, l₂, hl₁, hl₂ => by
    have hnb : ¬ r a b := hl₁ b List.mem_cons_self
    simp [hnb, orderedInsert_append_eq r a l₁ l₂ (fun x hx => hl₁ x (List.mem_cons_of_mem b hx))
      hl₂]

private theorem mergeSort_decide_eq_insertionSort {α : Type*} (r : α → α → Prop) [DecidableRel r]
    (htrans : ∀ a b c, r a b → r b c → r a c)
    (htotal : ∀ a b, r a b ∨ r b a) :
    ∀ xs : List α, xs.mergeSort (fun a b => decide (r a b)) = xs.insertionSort r
  | [] => by simp
  | a :: l => by
    have tr : ∀ x y z, decide (r x y) = true → decide (r y z) = true → decide (r x z) = true := by
      intro x y z h1 h2
      exact decide_eq_true (htrans x y z (of_decide_eq_true h1) (of_decide_eq_true h2))
    have tot : ∀ x y, (decide (r x y) || decide (r y x)) = true := by
      intro x y
      rcases htotal x y with h | h <;> simp [h]
    obtain ⟨l₁, l₂, hcons, hl, hnot⟩ := List.mergeSort_cons tr tot a l
    have hpw : (l₁ ++ a :: l₂).Pairwise (fun x y => decide (r x y) = true) :=
      hcons ▸ List.pairwise_mergeSort tr tot (a :: l)
    have hl₂ : ∀ c ∈ l₂, r a c := fun c hc =>
      of_decide_eq_true ((List.pairwise_cons.mp (List.pairwise_append.mp hpw).2.1).1 c hc)
    have hl₁ : ∀ b ∈ l₁, ¬ r a b := fun b hb hrab => by
      have hnb := hnot b hb
      simp [hrab] at hnb
    rw [hcons, List.insertionSort_cons, ← mergeSort_decide_eq_insertionSort r htrans htotal l, hl]
    exact (orderedInsert_append_eq r a l₁ l₂ hl₁ hl₂).symm

/-- `List.mergeSort` and `List.insertionSort` are both stable, so `greedyMaxBasis` equals
`greedySelect` over `xs.insertionSort (fun a b => w b ≤ w a)` even when distinct elements share a
weight. This allows `simp` to evaluate `greedyMaxBasis` symbolically on concrete lists without
exposing `List.mergeSort`'s internal splitter. -/
theorem greedyMaxBasis_eq_insertionSort {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) :
    greedyMaxBasis indep w xs = greedySelect indep (xs.insertionSort (fun a b => w b ≤ w a)) := by
  rw [greedyMaxBasis,
    mergeSort_decide_eq_insertionSort (fun a b => w b ≤ w a)
      (fun _ _ _ h1 h2 => h2.trans h1) (fun a b => le_total (w b) (w a))]

/-- `List.insertionSort` rewriting form of `greedyMinBasis`, preserving ties by stability. -/
theorem greedyMinBasis_eq_insertionSort {α : Type*} {β : Type*} [DecidableEq α] [LinearOrder β]
    (indep : Finset α → Bool) (w : α → β) (xs : List α) :
    greedyMinBasis indep w xs = greedySelect indep (xs.insertionSort (fun a b => w a ≤ w b)) := by
  rw [greedyMinBasis,
    mergeSort_decide_eq_insertionSort (fun a b => w a ≤ w b)
      (fun _ _ _ h1 h2 => h1.trans h2) (fun a b => le_total (w a) (w b))]

/-! ## Structural properties of the greedy scan -/

section Structural

variable {α : Type*} [DecidableEq α]

private theorem subset_greedyStep (indep : Finset α → Bool) (acc : Finset α) (x : α) :
    acc ⊆ greedyStep indep acc x := by
  simp only [greedyStep]
  split <;> simp [Finset.subset_insert]

private theorem subset_foldl_greedyStep (indep : Finset α → Bool) (acc : Finset α) (xs : List α) :
    acc ⊆ xs.foldl (greedyStep indep) acc := by
  induction xs generalizing acc with
  | nil => exact Finset.Subset.refl _
  | cons x rest ih => exact (subset_greedyStep indep acc x).trans (ih _)

private theorem foldl_greedyStep_subset (indep : Finset α → Bool) (acc : Finset α) (xs : List α) :
    xs.foldl (greedyStep indep) acc ⊆ acc ∪ xs.toFinset := by
  induction xs generalizing acc with
  | nil => simp
  | cons x rest ih =>
    refine (ih (greedyStep indep acc x)).trans ?_
    intro y hy
    simp only [Finset.mem_union, List.toFinset_cons, Finset.mem_insert] at hy ⊢
    rcases hy with hy | hy
    · simp only [greedyStep] at hy
      split at hy
      · rcases Finset.mem_insert.mp hy with rfl | hacc
        · exact Or.inr (Or.inl rfl)
        · exact Or.inl hacc
      · exact Or.inl hy
    · exact Or.inr (Or.inr hy)

/-- Every element chosen by `greedySelect` belongs to `xs.toFinset` (for any Boolean test). -/
theorem greedySelect_subset_toFinset (indep : Finset α → Bool) (xs : List α) :
    greedySelect indep xs ⊆ xs.toFinset := by
  simpa [greedySelect] using foldl_greedyStep_subset indep ∅ xs

/-- Every element chosen by `greedySelect` appears in `xs`. -/
theorem mem_of_mem_greedySelect {indep : Finset α → Bool} {xs : List α} {x : α}
    (hx : x ∈ greedySelect indep xs) : x ∈ xs :=
  List.mem_toFinset.mp (greedySelect_subset_toFinset indep xs hx)

/-- Every element chosen by `greedyMaxBasis` appears in `xs`. -/
theorem mem_of_mem_greedyMaxBasis {β : Type*} [LinearOrder β]
    {indep : Finset α → Bool} {w : α → β} {xs : List α} {x : α}
    (hx : x ∈ greedyMaxBasis indep w xs) : x ∈ xs :=
  (List.mergeSort_perm xs _).subset (mem_of_mem_greedySelect hx)

/-- Every element chosen by `greedyMinBasis` appears in `xs`. -/
theorem mem_of_mem_greedyMinBasis {β : Type*} [LinearOrder β]
    {indep : Finset α → Bool} {w : α → β} {xs : List α} {x : α}
    (hx : x ∈ greedyMinBasis indep w xs) : x ∈ xs :=
  (List.mergeSort_perm xs _).subset (mem_of_mem_greedySelect hx)

/-- Every element chosen by `greedyMaxIndep` appears in `xs` and has nonnegative weight. -/
theorem mem_and_nonneg_of_mem_greedyMaxIndep {β : Type*} [Zero β] [LinearOrder β]
    {indep : Finset α → Bool} {w : α → β} {xs : List α} {x : α}
    (hx : x ∈ greedyMaxIndep indep w xs) : x ∈ xs ∧ 0 ≤ w x := by
  have hmem := mem_of_mem_greedyMaxBasis hx
  simpa using List.mem_filter.mp hmem

private theorem indep_foldl_greedyStep {indep : Finset α → Bool} {acc : Finset α}
    (hacc : indep acc = true) (xs : List α) :
    indep (xs.foldl (greedyStep indep) acc) = true := by
  induction xs generalizing acc with
  | nil => exact hacc
  | cons x rest ih =>
    refine ih ?_
    simp only [greedyStep]
    cases h : indep (insert x acc) <;> simp [h, hacc]

/-- Whenever `indep ∅ = true`, `greedySelect indep xs` satisfies `indep` (even for arbitrary
non-matroid predicates). -/
theorem indep_greedySelect {indep : Finset α → Bool} (hempty : indep ∅ = true) (xs : List α) :
    indep (greedySelect indep xs) = true :=
  indep_foldl_greedyStep hempty xs

/-! ## Matroid independence and basis theorems -/

private theorem foldl_greedyStep_indep_and_max {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    {acc : Finset α} (hacc : M.Indep (acc : Set α)) (xs : List α) :
    M.Indep ((xs.foldl (greedyStep indep) acc : Finset α) : Set α) ∧
      ∀ e ∈ xs, e ∉ xs.foldl (greedyStep indep) acc →
        ¬ M.Indep (insert e ((xs.foldl (greedyStep indep) acc : Finset α) : Set α)) := by
  induction xs generalizing acc with
  | nil => exact ⟨hacc, by simp⟩
  | cons x rest ih =>
    simp only [List.foldl_cons]
    have hstep_indep : M.Indep ((greedyStep indep acc x : Finset α) : Set α) := by
      simp only [greedyStep]
      split
      · rename_i htrue
        exact (hM _).mp htrue
      · exact hacc
    obtain ⟨hind, hmax⟩ := ih hstep_indep
    refine ⟨hind, fun e he he_not_mem => ?_⟩
    rcases List.mem_cons.mp he with rfl | he_rest
    · have hx_false : indep (insert e acc) = false := by
        cases hbool : indep (insert e acc)
        · rfl
        · exfalso
          have hx_in : e ∈ greedyStep indep acc e := by simp [greedyStep, hbool]
          exact he_not_mem (subset_foldl_greedyStep indep _ rest hx_in)
      have hnot : ¬ M.Indep ((insert e acc : Finset α) : Set α) := by
        rw [← hM]
        simp [hx_false]
      intro hind_final
      apply hnot
      refine hind_final.subset ?_
      rw [Finset.coe_insert]
      exact Set.insert_subset_insert (Finset.coe_subset.mpr
        ((subset_greedyStep indep acc e).trans
          (subset_foldl_greedyStep indep (greedyStep indep acc e) rest)))
    · exact hmax e he_rest he_not_mem

/-- Under an independence test implementing `M : Matroid α`, `greedySelect` returns an independent
set. -/
theorem greedySelect_indep {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α) :
    M.Indep ((greedySelect indep xs : Finset α) : Set α) :=
  (foldl_greedyStep_indep_and_max hM (by simp) xs).1

/-- Any candidate `e ∈ xs` rejected by `greedySelect` cannot be added to the greedy output while
preserving independence in `M`. -/
theorem greedySelect_insert_not_indep {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α)
    {e : α} (he : e ∈ xs) (hne : e ∉ greedySelect indep xs) :
    ¬ M.Indep (insert e ((greedySelect indep xs : Finset α) : Set α)) :=
  (foldl_greedyStep_indep_and_max hM (by simp) xs).2 e he hne

/-- `greedySelect` computes a basis (`Matroid.IsBasis'`) of `{x | x ∈ xs}` in `M`, without
requiring `xs` to be duplicate-free or contained in `M.E`. -/
theorem greedySelect_isBasis' {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α) :
    M.IsBasis' ((greedySelect indep xs : Finset α) : Set α) {x | x ∈ xs} := by
  refine ⟨⟨greedySelect_indep hM xs, fun x hx => mem_of_mem_greedySelect hx⟩, ?_⟩
  intro J ⟨hJ_ind, hJ_sub⟩ hsub e heJ
  by_contra heG
  exact greedySelect_insert_not_indep hM xs (hJ_sub heJ) heG
    (hJ_ind.subset (Set.insert_subset heJ hsub))

/-- When all elements of `xs` lie in `M.E`, `greedySelect` computes a `Matroid.IsBasis` of
`{x | x ∈ xs}`. -/
theorem greedySelect_isBasis {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α)
    (hE : {x | x ∈ xs} ⊆ M.E) :
    M.IsBasis ((greedySelect indep xs : Finset α) : Set α) {x | x ∈ xs} :=
  (greedySelect_isBasis' hM xs).isBasis hE

/-- When `xs` enumerates the entire ground set `M.E`, `greedySelect` computes a base
(`Matroid.IsBase`) of `M`. -/
theorem greedySelect_isBase {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α)
    (hE : {x | x ∈ xs} = M.E) :
    M.IsBase ((greedySelect indep xs : Finset α) : Set α) := by
  rw [← Matroid.isBasis_ground_iff, ← hE]
  exact greedySelect_isBasis hM xs hE.subset

/-- Every independent finite subset `I` of `{x | x ∈ xs}` has cardinality at most
`(greedySelect indep xs).card`. -/
theorem card_le_greedySelect_card {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α)
    {I : Finset α} (hI : M.Indep (I : Set α)) (hIsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    I.card ≤ (greedySelect indep xs).card := by
  by_contra hlt
  push Not at hlt
  obtain ⟨e, heI, heG, hind⟩ := (greedySelect_indep hM xs).augment_finset hI hlt
  exact (greedySelect_isBasis' hM xs).insert_not_indep ⟨hIsub heI, heG⟩ hind

/-- Every basis `I` of `{x | x ∈ xs}` has the same cardinality as `greedySelect indep xs`. -/
theorem card_eq_greedySelect_card_of_isBasis' {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α)
    {I : Finset α} (hI : M.IsBasis' (I : Set α) {x | x ∈ xs}) :
    I.card = (greedySelect indep xs).card := by
  refine Nat.le_antisymm (card_le_greedySelect_card hM xs hI.indep hI.subset) ?_
  by_contra hlt
  push Not at hlt
  obtain ⟨e, heG, heI, hind⟩ := hI.indep.augment_finset (greedySelect_indep hM xs) hlt
  exact hI.insert_not_indep ⟨mem_of_mem_greedySelect heG, heI⟩ hind

/-! ## Deduplication invariance (retaining first occurrences) -/

/-- Keep the first occurrence of each element of `xs`, preserving left-to-right order. -/
private def dedupFirst : List α → List α
  | [] => []
  | x :: xs => x :: (dedupFirst xs).filter (· ≠ x)

private theorem mem_dedupFirst {xs : List α} {y : α} : y ∈ dedupFirst xs ↔ y ∈ xs := by
  induction xs with
  | nil => rfl
  | cons x rest ih =>
    simp only [dedupFirst, List.mem_cons, List.mem_filter, ih]
    by_cases hyx : y = x <;> simp [hyx]

private theorem dedupFirst_sublist (xs : List α) : (dedupFirst xs).Sublist xs := by
  induction xs with
  | nil => exact .slnil
  | cons x rest ih => exact .cons_cons x (List.filter_sublist.trans ih)

private theorem nodup_dedupFirst (xs : List α) : (dedupFirst xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x rest ih =>
    rw [dedupFirst, List.nodup_cons]
    exact ⟨by simp, ih.filter _⟩

private theorem foldl_greedyStep_filter_ne {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (x : α) (ys : List α) (acc : Finset α)
    (hx : x ∈ acc ∨ ¬ M.Indep ((insert x acc : Finset α) : Set α)) :
    ys.foldl (greedyStep indep) acc = (ys.filter (· ≠ x)).foldl (greedyStep indep) acc := by
  induction ys generalizing acc with
  | nil => rfl
  | cons y rest ih =>
    by_cases hyx : y = x
    · subst hyx
      have hstep : greedyStep indep acc y = acc := by
        rcases hx with hmem | hdep
        · simp [greedyStep, Finset.insert_eq_of_mem hmem]
        · have hfalse : indep (insert y acc) = false := by
            cases hbool : indep (insert y acc)
            · rfl
            · exact absurd ((hM _).mp hbool) hdep
          simp [greedyStep, hfalse]
      simp [List.foldl_cons, hstep, ih acc hx]
    · have hkeep : (y :: rest).filter (· ≠ x) = y :: rest.filter (· ≠ x) := by
        simp [hyx]
      rw [hkeep, List.foldl_cons, List.foldl_cons]
      refine ih (greedyStep indep acc y) ?_
      rcases hx with hmem | hdep
      · exact Or.inl (subset_greedyStep indep acc y hmem)
      · refine Or.inr (fun hind => hdep (hind.subset ?_))
        rw [Finset.coe_insert, Finset.coe_insert]
        exact Set.insert_subset_insert (Finset.coe_subset.mpr (subset_greedyStep indep acc y))

private theorem foldl_greedyStep_dedupFirst {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (xs : List α) (acc : Finset α) :
    xs.foldl (greedyStep indep) acc = (dedupFirst xs).foldl (greedyStep indep) acc := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x rest ih =>
    simp only [dedupFirst, List.foldl_cons]
    rw [ih (greedyStep indep acc x)]
    refine foldl_greedyStep_filter_ne hM x (dedupFirst rest) (greedyStep indep acc x) ?_
    cases hbool : indep (insert x acc)
    · right
      simp only [greedyStep, hbool]
      intro hind
      have htrue := (hM (insert x acc)).mpr hind
      simp [hbool] at htrue
    · left
      simp [greedyStep, hbool]

/-- Under a matroid independence test, duplicate elements in `xs` do not affect `greedySelect`. -/
private theorem greedySelect_eq_dedupFirst {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (xs : List α) :
    greedySelect indep xs = greedySelect indep (dedupFirst xs) :=
  foldl_greedyStep_dedupFirst hM xs ∅

/-! ## Gale's pointwise dominance theorem -/

omit [DecidableEq α] in
private theorem exists_split_getElem_filter {xs : List α} (p : α → Bool)
    {j : ℕ} (hj : j < (xs.filter p).length) :
    ∃ P S : List α, xs = P ++ (xs.filter p)[j] :: S ∧ (P.filter p).length = j := by
  induction xs generalizing j with
  | nil => simp at hj
  | cons a rest ih =>
    cases hpa : p a
    · simp only [List.filter_cons, hpa, Bool.false_eq_true, ↓reduceIte] at hj ⊢
      obtain ⟨P, S, hsplit, hlen⟩ := ih hj
      refine ⟨a :: P, S, congrArg (a :: ·) hsplit, ?_⟩
      simp [hpa, hlen]
    · simp only [List.filter_cons, hpa, ↓reduceIte] at hj ⊢
      cases j with
      | zero => exact ⟨[], rest, rfl, rfl⟩
      | succ j' =>
        have hj' : j' < (rest.filter p).length := Nat.lt_of_succ_lt_succ hj
        obtain ⟨P, S, hsplit, hlen⟩ := ih hj'
        refine ⟨a :: P, S, congrArg (a :: ·) hsplit, ?_⟩
        simp [hpa, hlen]

omit [DecidableEq α] in
private theorem prefix_split_cases :
    ∀ {P₁ : List α} {x₁ : α} {S₁ P₂ : List α} {x₂ : α} {S₂ : List α},
      P₁ ++ x₁ :: S₁ = P₂ ++ x₂ :: S₂ →
      (P₁ = P₂ ∧ x₁ = x₂ ∧ S₁ = S₂) ∨
      (∃ M, P₂ = P₁ ++ x₁ :: M ∧ S₁ = M ++ x₂ :: S₂) ∨
      (∃ M, P₁ = P₂ ++ x₂ :: M ∧ S₂ = M ++ x₁ :: S₁)
  | [], x₁, S₁, [], x₂, S₂, h => by
    simp only [List.nil_append, List.cons.injEq] at h
    exact Or.inl ⟨rfl, h.1, h.2⟩
  | [], x₁, S₁, p₂ :: P₂, x₂, S₂, h => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
    exact Or.inr (Or.inl ⟨P₂, by simp [h.1], h.2⟩)
  | p₁ :: P₁, x₁, S₁, [], x₂, S₂, h => by
    simp only [List.cons_append, List.nil_append, List.cons.injEq] at h
    exact Or.inr (Or.inr ⟨P₁, by simp [h.1], h.2.symm⟩)
  | p₁ :: P₁, x₁, S₁, p₂ :: P₂, x₂, S₂, h => by
    simp only [List.cons_append, List.cons.injEq] at h
    rcases h with ⟨rfl, htail⟩
    rcases prefix_split_cases htail with ⟨rfl, rfl, rfl⟩ | ⟨M, hP, hS⟩ | ⟨M, hP, hS⟩
    · exact Or.inl ⟨rfl, rfl, rfl⟩
    · exact Or.inr (Or.inl ⟨M, by simp [hP], hS⟩)
    · exact Or.inr (Or.inr ⟨M, by simp [hP], hS⟩)

private theorem mem_foldl_greedyStep_of_disjoint (indep : Finset α → Bool)
    {P S : List α} (hdisj : List.Disjoint P S) (acc : Finset α) {z : α} (hz : z ∈ P) :
    z ∈ S.foldl (greedyStep indep) acc ↔ z ∈ acc := by
  refine ⟨fun hmem => ?_, fun hmem => subset_foldl_greedyStep indep acc S hmem⟩
  have hsub := foldl_greedyStep_subset indep acc S hmem
  rcases Finset.mem_union.mp hsub with hacc | hS
  · exact hacc
  · exact absurd (List.mem_toFinset.mp hS) (hdisj hz)

private theorem toFinset_filter_mem {xs : List α} {I : Finset α}
    (hsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    (xs.filter (· ∈ I)).toFinset = I := by
  ext x
  simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
  exact ⟨fun h => h.2, fun hx => ⟨hsub hx, hx⟩⟩

/-- **Gale's Pointwise Dominance Theorem** ([Gale1968], Theorem, p. 177):
Let `xs` be a duplicate-free list sorted with respect to a reflexive relation `R`, and let
`G := greedySelect indep xs` be the greedy output for `M : Matroid α`. For every independent set
`I : Finset α` contained in `{x | x ∈ xs}`, listing `G` and `I` in the order of `xs` as
`G_list := xs.filter (· ∈ G)` and `I_list := xs.filter (· ∈ I)` yields:
1. `I_list.length ≤ G_list.length`, and
2. for every index `j < I_list.length`, `R G_list[j] I_list[j]`. -/
theorem gale_dominance_nodup {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    {R : α → α → Prop} [Std.Refl R] {xs : List α} (hnodup : xs.Nodup) (hsorted : xs.Pairwise R)
    {I : Finset α} (hI : M.Indep (I : Set α)) (hIsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    let G := greedySelect indep xs
    let G_list := xs.filter (· ∈ G)
    let I_list := xs.filter (· ∈ I)
    ∃ hlen : I_list.length ≤ G_list.length,
      ∀ (j : ℕ) (hj : j < I_list.length),
        R (G_list[j]'(Nat.lt_of_lt_of_le hj hlen)) (I_list[j]'hj) := by
  dsimp only
  set G := greedySelect indep xs
  set G_list := xs.filter (· ∈ G)
  set I_list := xs.filter (· ∈ I)
  have hGsub : (G : Set α) ⊆ {x | x ∈ xs} := fun x hx => mem_of_mem_greedySelect hx
  have hG_len : G_list.length = G.card := by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _), toFinset_filter_mem hGsub]
  have hI_len : I_list.length = I.card := by
    rw [← List.toFinset_card_of_nodup (hnodup.filter _), toFinset_filter_mem hIsub]
  have hlen : I_list.length ≤ G_list.length := by
    rw [hI_len, hG_len]
    exact card_le_greedySelect_card hM xs hI hIsub
  refine ⟨hlen, fun j hj => ?_⟩
  have hjG : j < G_list.length := Nat.lt_of_lt_of_le hj hlen
  obtain ⟨P_G, S_G, hxs_G, hPG_len⟩ := exists_split_getElem_filter (· ∈ G) hjG
  obtain ⟨P_I, S_I, hxs_I, hPI_len⟩ := exists_split_getElem_filter (· ∈ I) hj
  set g := G_list[j]
  set y := I_list[j]
  have hsplit : P_G ++ g :: S_G = P_I ++ y :: S_I := hxs_G.symm.trans hxs_I
  rcases prefix_split_cases hsplit with ⟨_, hgy, _⟩ | ⟨M_mid, _, hSG⟩ | ⟨M_mid, hPG_eq, _⟩
  · exact hgy ▸ refl g
  · have hsorted' : (P_G ++ g :: (M_mid ++ y :: S_I)).Pairwise R := by
      rwa [← hSG, ← hxs_G]
    have htail : (g :: (M_mid ++ y :: S_I)).Pairwise R :=
      (List.pairwise_append.mp hsorted').2.1
    exact (List.pairwise_cons.mp htail).1 y (by simp)
  · exfalso
    set A_P := greedySelect indep P_G
    have hnodup_G : (P_G ++ g :: S_G).Nodup := hxs_G ▸ hnodup
    have hdisj : List.Disjoint P_G (g :: S_G) := fun z hz1 hz2 =>
      (List.nodup_append.mp hnodup_G).2.2 z hz1 z hz2 rfl
    have hG_eq : G = (g :: S_G).foldl (greedyStep indep) A_P := by
      simp [G, A_P, greedySelect, hxs_G, List.foldl_append]
    have hfilter_eq : P_G.filter (· ∈ A_P) = P_G.filter (· ∈ G) := by
      refine List.filter_congr fun z hz => ?_
      rw [hG_eq]
      simp only [decide_eq_decide]
      exact (mem_foldl_greedyStep_of_disjoint indep hdisj A_P hz).symm
    have hAP_sub : (A_P : Set α) ⊆ {z | z ∈ P_G} := fun z hz => mem_of_mem_greedySelect hz
    have hAP_card : A_P.card = j := by
      rw [← toFinset_filter_mem hAP_sub,
        List.toFinset_card_of_nodup ((List.nodup_append.mp hnodup_G).1.filter _),
        hfilter_eq, hPG_len]
    have hy_mem_I : y ∈ I := by
      have hy_in : y ∈ I_list := List.getElem_mem hj
      exact (List.mem_filter.mp hy_in).2 |> decide_eq_true_eq.mp
    set L_J := (P_I ++ [y]).filter (· ∈ I)
    set J := L_J.toFinset
    have hPG_nodup : P_G.Nodup := (List.nodup_append.mp hnodup_G).1
    have hPIy_sub_PG : ∀ z ∈ P_I ++ [y], z ∈ P_G := by
      intro z hz
      rw [hPG_eq]
      rcases List.mem_append.mp hz with hzI | hzy
      · exact List.mem_append_left _ hzI
      · simp only [List.mem_singleton] at hzy
        subst hzy
        exact List.mem_append_right _ (List.mem_cons_self ..)
    have hPIy_nodup : (P_I ++ [y]).Nodup := by
      have hpg' : ((P_I ++ [y]) ++ M_mid).Nodup := by simpa [hPG_eq] using hPG_nodup
      exact (List.nodup_append.mp hpg').1
    have hJ_card : J.card = j + 1 := by
      rw [List.toFinset_card_of_nodup (hPIy_nodup.filter _)]
      simp [List.filter_append, hy_mem_I, hPI_len]
    have hJ_sub_I : J ⊆ I := by
      intro z hz
      have hz' := List.mem_filter.mp (List.mem_toFinset.mp hz)
      exact decide_eq_true_eq.mp hz'.2
    have hJ_indep : M.Indep (J : Set α) := hI.subset (Finset.coe_subset.mpr hJ_sub_I)
    have hlt_card : A_P.card < J.card := by omega
    obtain ⟨e, heJ, heAP, hind_ins⟩ :=
      (greedySelect_indep hM P_G).augment_finset hJ_indep hlt_card
    have he_in_PG : e ∈ P_G := by
      have he_LJ : e ∈ L_J := List.mem_toFinset.mp heJ
      exact hPIy_sub_PG e (List.mem_filter.mp he_LJ).1
    exact (greedySelect_isBasis' hM P_G).insert_not_indep ⟨he_in_PG, heAP⟩ hind_ins

end Structural

/-! ## Rado–Edmonds and CLRS weighted optimality theorems -/

section Weighted

variable {α : Type*} {β : Type*} [DecidableEq α]

omit [DecidableEq α] in
private theorem list_sum_le_sum_of_getElem [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β] :
    ∀ {xs ys : List α} (w : α → β) (hlen : xs.length = ys.length),
      (∀ (j : ℕ) (hj : j < xs.length), w (xs[j]'hj) ≤ w (ys[j]'(hlen ▸ hj))) →
      (xs.map w).sum ≤ (ys.map w).sum
  | [], [], _, _, _ => le_rfl
  | x :: xs, y :: ys, w, hlen, hle => by
    simp only [List.length_cons, Nat.succ.injEq] at hlen
    simp only [List.map_cons, List.sum_cons]
    refine add_le_add (hle 0 (Nat.zero_lt_succ _)) ?_
    exact list_sum_le_sum_of_getElem w hlen fun j hj => hle (j + 1) (Nat.succ_lt_succ hj)

private theorem finset_sum_eq_filter_map_sum [AddCommMonoid β] {xs : List α} (hnodup : xs.Nodup)
    {S : Finset α} (hS : (S : Set α) ⊆ {x | x ∈ xs}) (w : α → β) :
    ∑ x ∈ S, w x = ((xs.filter (· ∈ S)).map w).sum := by
  have hto : (xs.filter (· ∈ S)).toFinset = S := toFinset_filter_mem hS
  conv_lhs => rw [← hto]
  exact List.sum_toFinset w (hnodup.filter _)

/-- **Rado–Edmonds Maximum-Weight Basis Theorem** (pre-sorted candidate list, [Rado1957];
[Edmonds1971], Section 2): if `xs` is ordered by nonincreasing weight `w b ≤ w a`, then
`greedySelect indep xs` maximizes total weight `∑ x ∈ I, w x` among all bases `I` of
`{x | x ∈ xs}` in `M` (under arbitrary signed or unsigned weights). -/
theorem sum_le_greedySelect_of_isBasis' [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (w : α → β) {xs : List α} (hsorted : xs.Pairwise (fun a b => w b ≤ w a))
    {I : Finset α} (hI : M.IsBasis' (I : Set α) {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ greedySelect indep xs, w x := by
  rw [greedySelect_eq_dedupFirst hM xs]
  set ys := dedupFirst xs
  have hys_nodup : ys.Nodup := nodup_dedupFirst xs
  have hys_sorted : ys.Pairwise (fun a b => w b ≤ w a) := hsorted.sublist (dedupFirst_sublist xs)
  have hset_eq : {x | x ∈ ys} = {x | x ∈ xs} := by
    ext x; exact mem_dedupFirst
  have hI' : M.IsBasis' (I : Set α) {x | x ∈ ys} := hset_eq.symm ▸ hI
  set G := greedySelect indep ys
  have hGsub : (G : Set α) ⊆ {x | x ∈ ys} := fun x hx => mem_of_mem_greedySelect hx
  have : Std.Refl (fun a b : α => w b ≤ w a) := ⟨fun _ => le_rfl⟩
  obtain ⟨hlen_le, hdom⟩ :=
    gale_dominance_nodup hM hys_nodup hys_sorted hI'.indep hI'.subset
  have hcard_eq : I.card = G.card := card_eq_greedySelect_card_of_isBasis' hM ys hI'
  have hlen_I : (ys.filter (· ∈ I)).length = I.card := by
    rw [← List.toFinset_card_of_nodup (hys_nodup.filter _), toFinset_filter_mem hI'.subset]
  have hlen_G : (ys.filter (· ∈ G)).length = G.card := by
    rw [← List.toFinset_card_of_nodup (hys_nodup.filter _), toFinset_filter_mem hGsub]
  have hlen_eq : (ys.filter (· ∈ I)).length = (ys.filter (· ∈ G)).length := by omega
  rw [finset_sum_eq_filter_map_sum hys_nodup hI'.subset w,
    finset_sum_eq_filter_map_sum hys_nodup hGsub w]
  exact list_sum_le_sum_of_getElem w hlen_eq fun j hj => hdom j hj

/-- **Rado–Edmonds Minimum-Weight Basis Theorem** (pre-sorted candidate list, Kruskal order):
if `xs` is ordered by nondecreasing weight `w a ≤ w b`, then `greedySelect indep xs` minimizes
total weight `∑ x ∈ I, w x` among all bases `I` of `{x | x ∈ xs}` in `M` (valid even over `ℕ`
without negation or subtraction). -/
theorem greedySelect_le_sum_of_isBasis' [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (w : α → β) {xs : List α} (hsorted : xs.Pairwise (fun a b => w a ≤ w b))
    {I : Finset α} (hI : M.IsBasis' (I : Set α) {x | x ∈ xs}) :
    ∑ x ∈ greedySelect indep xs, w x ≤ ∑ x ∈ I, w x :=
  sum_le_greedySelect_of_isBasis' (β := βᵒᵈ) hM w hsorted hI

/-- **Weighted Independent-Set Optimality** for pre-sorted nonnegative weights (generalizing
[CLRS2009], Section 16.4, Theorem 16.11 from strictly positive to nonnegative weights): if `xs` is
ordered by nonincreasing weight `w b ≤ w a` and `0 ≤ w x` for every `x ∈ xs`, then
`greedySelect indep xs` maximizes `∑ x ∈ I, w x` over **all** independent finite subsets `I` of
`{x | x ∈ xs}`. -/
theorem sum_le_greedySelect_of_indep [AddCommMonoid β] [Preorder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (w : α → β) {xs : List α} (hsorted : xs.Pairwise (fun a b => w b ≤ w a))
    (hnonneg : ∀ x ∈ xs, 0 ≤ w x)
    {I : Finset α} (hI : M.Indep (I : Set α)) (hIsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ greedySelect indep xs, w x := by
  rw [greedySelect_eq_dedupFirst hM xs]
  set ys := dedupFirst xs
  have hys_nodup : ys.Nodup := nodup_dedupFirst xs
  have hys_sorted : ys.Pairwise (fun a b => w b ≤ w a) := hsorted.sublist (dedupFirst_sublist xs)
  have hset_eq : {x | x ∈ ys} = {x | x ∈ xs} := by
    ext x; exact mem_dedupFirst
  have hIsub' : (I : Set α) ⊆ {x | x ∈ ys} := hset_eq.symm ▸ hIsub
  set G := greedySelect indep ys
  have hGsub : (G : Set α) ⊆ {x | x ∈ ys} := fun x hx => mem_of_mem_greedySelect hx
  have : Std.Refl (fun a b : α => w b ≤ w a) := ⟨fun _ => le_rfl⟩
  obtain ⟨hlen_le, hdom⟩ := gale_dominance_nodup hM hys_nodup hys_sorted hI hIsub'
  rw [finset_sum_eq_filter_map_sum hys_nodup hIsub' w,
    finset_sum_eq_filter_map_sum hys_nodup hGsub w]
  set G_list := ys.filter (· ∈ G)
  set I_list := ys.filter (· ∈ I)
  have hsplit : G_list = G_list.take I_list.length ++ G_list.drop I_list.length :=
    (List.take_append_drop I_list.length G_list).symm
  conv_rhs => rw [hsplit, List.map_append, List.sum_append]
  have htake_len : I_list.length = (G_list.take I_list.length).length := by
    simp [hlen_le]
  have hle_prefix : (I_list.map w).sum ≤ ((G_list.take I_list.length).map w).sum := by
    refine list_sum_le_sum_of_getElem w htake_len fun j hj => ?_
    simpa [List.getElem_take] using hdom j hj
  have hdrop_nonneg : 0 ≤ ((G_list.drop I_list.length).map w).sum := by
    refine List.sum_nonneg ?_
    intro v hv
    obtain ⟨x, hx_drop, rfl⟩ := List.mem_map.mp hv
    have hx_G : x ∈ G_list := List.mem_of_mem_drop hx_drop
    have hx_ys : x ∈ ys := (List.mem_filter.mp hx_G).1
    exact hnonneg x (mem_dedupFirst.mp hx_ys)
  exact le_add_of_le_of_nonneg hle_prefix hdrop_nonneg

/-! ### Unsorted weighted entrypoints (`greedyMaxBasis`, `greedyMinBasis`, `greedyMaxIndep`) -/

omit [DecidableEq α] in
private theorem pairwise_mergeSort_ge [LinearOrder β] (w : α → β) (xs : List α) :
    (xs.mergeSort (fun a b => decide (w b ≤ w a))).Pairwise (fun a b => w b ≤ w a) := by
  simpa using List.pairwise_mergeSort (le := fun a b => decide (w b ≤ w a))
    (fun a b c h₁ h₂ => decide_eq_true (le_trans (of_decide_eq_true h₂) (of_decide_eq_true h₁)))
    (fun a b => by rcases le_total (w b) (w a) with h | h <;> simp [h])
    xs

omit [DecidableEq α] in
private theorem pairwise_mergeSort_le [LinearOrder β] (w : α → β) (xs : List α) :
    (xs.mergeSort (fun a b => decide (w a ≤ w b))).Pairwise (fun a b => w a ≤ w b) :=
  pairwise_mergeSort_ge (β := βᵒᵈ) w xs

/-- `greedyMaxBasis` always returns a basis (`Matroid.IsBasis'`) of `{x | x ∈ xs}`. -/
theorem greedyMaxBasis_isBasis' [LinearOrder β] {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (w : α → β) (xs : List α) :
    M.IsBasis' ((greedyMaxBasis indep w xs : Finset α) : Set α) {x | x ∈ xs} := by
  have hset : {x | x ∈ xs.mergeSort (fun a b => decide (w b ≤ w a))} = {x | x ∈ xs} := by
    ext x; exact (List.mergeSort_perm xs _).mem_iff
  rw [greedyMaxBasis, ← hset]
  exact greedySelect_isBasis' hM _

/-- `greedyMinBasis` always returns a basis (`Matroid.IsBasis'`) of `{x | x ∈ xs}`. -/
theorem greedyMinBasis_isBasis' [LinearOrder β] {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (w : α → β) (xs : List α) :
    M.IsBasis' ((greedyMinBasis indep w xs : Finset α) : Set α) {x | x ∈ xs} := by
  have hset : {x | x ∈ xs.mergeSort (fun a b => decide (w a ≤ w b))} = {x | x ∈ xs} := by
    ext x; exact (List.mergeSort_perm xs _).mem_iff
  rw [greedyMinBasis, ← hset]
  exact greedySelect_isBasis' hM _

/-- **Maximum-Weight Basis Optimality** ([Edmonds1971], Section 2): `greedyMaxBasis indep w xs`
maximizes `∑ x ∈ I, w x` among all bases `I` of `{x | x ∈ xs}`, under arbitrary weights. -/
theorem sum_le_greedyMaxBasis [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (w : α → β) (xs : List α)
    {I : Finset α} (hI : M.IsBasis' (I : Set α) {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ greedyMaxBasis indep w xs, w x := by
  have hset : {x | x ∈ xs.mergeSort (fun a b => decide (w b ≤ w a))} = {x | x ∈ xs} := by
    ext x; exact (List.mergeSort_perm xs _).mem_iff
  exact sum_le_greedySelect_of_isBasis' hM w (pairwise_mergeSort_ge w xs) (hset.symm ▸ hI)

/-- **Minimum-Weight Basis Optimality** (Kruskal order): `greedyMinBasis indep w xs` minimizes
`∑ x ∈ I, w x` among all bases `I` of `{x | x ∈ xs}` (including over `ℕ`). -/
theorem greedyMinBasis_le_sum [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (w : α → β) (xs : List α)
    {I : Finset α} (hI : M.IsBasis' (I : Set α) {x | x ∈ xs}) :
    ∑ x ∈ greedyMinBasis indep w xs, w x ≤ ∑ x ∈ I, w x := by
  have hset : {x | x ∈ xs.mergeSort (fun a b => decide (w a ≤ w b))} = {x | x ∈ xs} := by
    ext x; exact (List.mergeSort_perm xs _).mem_iff
  exact greedySelect_le_sum_of_isBasis' hM w (pairwise_mergeSort_le w xs) (hset.symm ▸ hI)

/-- **Maximum-Weight Independent-Set Optimality** for nonnegative weights (generalizing [CLRS2009],
Section 16.4, Theorem 16.11 from strictly positive to nonnegative weights): when `0 ≤ w x` for all
`x ∈ xs`, `greedyMaxBasis indep w xs` maximizes `∑ x ∈ I, w x` over all independent finite subsets
`I` of `{x | x ∈ xs}`. -/
theorem sum_le_greedyMaxBasis_of_indep [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (w : α → β) (xs : List α) (hnonneg : ∀ x ∈ xs, 0 ≤ w x)
    {I : Finset α} (hI : M.Indep (I : Set α)) (hIsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ greedyMaxBasis indep w xs, w x := by
  set ys := xs.mergeSort (fun a b => decide (w b ≤ w a))
  have hperm : ys.Perm xs := List.mergeSort_perm xs _
  have hset : {x | x ∈ ys} = {x | x ∈ xs} := by ext x; exact hperm.mem_iff
  exact sum_le_greedySelect_of_indep hM w (pairwise_mergeSort_ge w xs)
    (fun x hx => hnonneg x (hperm.subset hx)) hI (hset.symm ▸ hIsub)

/-- `greedyMaxIndep` returns an independent subset of `{x | x ∈ xs}`. -/
theorem greedyMaxIndep_indep [Zero β] [LinearOrder β] {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) (w : α → β) (xs : List α) :
    M.Indep ((greedyMaxIndep indep w xs : Finset α) : Set α) :=
  greedySelect_indep hM _

/-- **Maximum-Weight Independent-Set Optimality** for arbitrary signed weights ([Edmonds1971],
Section 2): `greedyMaxIndep indep w xs` maximizes `∑ x ∈ I, w x` over all independent finite
subsets `I` of `{x | x ∈ xs}` without any nonnegativity restriction on `w`. -/
theorem sum_le_greedyMaxIndep [AddCommMonoid β] [LinearOrder β] [IsOrderedAddMonoid β]
    {M : Matroid α} {indep : Finset α → Bool}
    (hM : ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α))
    (w : α → β) (xs : List α)
    {I : Finset α} (hI : M.Indep (I : Set α)) (hIsub : (I : Set α) ⊆ {x | x ∈ xs}) :
    ∑ x ∈ I, w x ≤ ∑ x ∈ greedyMaxIndep indep w xs, w x := by
  set xsPos := xs.filter (fun x => decide (0 ≤ w x))
  set IPos := I.filter (fun x => 0 ≤ w x)
  have hle_pos : ∑ x ∈ I, w x ≤ ∑ x ∈ IPos, w x := by
    rw [← Finset.sum_filter_add_sum_filter_not I (fun x => 0 ≤ w x)]
    have hneg : ∑ x ∈ I.filter (fun x => ¬ 0 ≤ w x), w x ≤ 0 := by
      refine Finset.sum_nonpos fun x hx => ?_
      exact le_of_not_ge (Finset.mem_filter.mp hx).2
    simpa [IPos] using add_le_of_nonpos_right hneg
  have hIPos_indep : M.Indep (IPos : Set α) :=
    hI.subset (Finset.coe_subset.mpr (Finset.filter_subset _ _))
  have hIPos_sub : (IPos : Set α) ⊆ {x | x ∈ xsPos} := by
    intro x hx
    have hx' := Finset.mem_filter.mp hx
    exact List.mem_filter.mpr ⟨hIsub hx'.1, decide_eq_true hx'.2⟩
  have hxsPos_nonneg : ∀ x ∈ xsPos, 0 ≤ w x := fun x hx =>
    of_decide_eq_true (List.mem_filter.mp hx).2
  exact hle_pos.trans
    (sum_le_greedyMaxBasis_of_indep hM w xsPos hxsPos_nonneg hIPos_indep hIPos_sub)

/-! ## Converse and full Rado–Edmonds matroid characterization -/

private theorem rado_edmonds_converse_inv
    {indep : Finset α → Bool}
    (hhered : ∀ ⦃A B : Finset α⦄, indep B = true → A ⊆ B → indep A = true)
    {I J : Finset α} (hI : indep I = true)
    (hno_aug : ∀ e ∈ J, e ∉ I → indep (insert e I) = false) :
    let k := I.card
    let w : α → ℕ := fun x => if x ∈ I then k + 2 else if x ∈ J then k + 1 else 0
    ∀ (seen rest : List α) (acc : Finset α),
      (seen ++ rest).Pairwise (fun a b => w b ≤ w a) →
      (∀ x ∈ I, x ∈ seen ++ rest) →
      acc ⊆ seen.toFinset →
      (∀ u ∈ acc, u ∈ I ∨ w u = 0) →
      (∀ x ∈ I, x ∈ seen → x ∈ acc) →
      ∀ u ∈ rest.foldl (greedyStep indep) acc, u ∈ I ∨ w u = 0 := by
  intro k w seen rest
  induction rest generalizing seen with
  | nil =>
    intro acc _ _ _ hacc _
    exact hacc
  | cons y tail ih =>
    intro acc hpw hI_mem hacc_seen hacc_I0 hI_seen
    have hpw' : ((seen ++ [y]) ++ tail).Pairwise (fun a b => w b ≤ w a) := by
      simpa [List.append_assoc] using hpw
    have hI_mem' : ∀ x ∈ I, x ∈ (seen ++ [y]) ++ tail := by
      simpa [List.append_assoc] using hI_mem
    have hseen_ge_y : ∀ u ∈ seen, w y ≤ w u := by
      intro u hu
      have hpair := List.pairwise_append.mp hpw
      exact hpair.2.2 u hu y (List.mem_cons_self ..)
    have hy_ge_tail : ∀ z ∈ tail, w z ≤ w y := by
      have hpair := (List.pairwise_append.mp hpw).2.1
      exact (List.pairwise_cons.mp hpair).1
    set acc' := greedyStep indep acc y
    have hacc'_seen : acc' ⊆ (seen ++ [y]).toFinset := by
      intro u hu
      simp only [List.toFinset_append, List.toFinset_cons, List.toFinset_nil,
        Finset.insert_empty, Finset.mem_union, Finset.mem_singleton]
      simp only [acc', greedyStep] at hu
      split at hu
      · rcases Finset.mem_insert.mp hu with rfl | hmem
        · exact Or.inr rfl
        · exact Or.inl (hacc_seen hmem)
      · exact Or.inl (hacc_seen hu)
    by_cases hyI : y ∈ I
    · have hwy : w y = k + 2 := by simp [w, hyI]
      have hacc_sub_I : acc ⊆ I := by
        intro u hu
        rcases hacc_I0 u hu with huI | hwu0
        · exact huI
        · exfalso
          have hle := hseen_ge_y u (List.mem_toFinset.mp (hacc_seen hu))
          omega
      have hins_ind : indep (insert y acc) = true :=
        hhered hI (Finset.insert_subset hyI hacc_sub_I)
      have hacc'_eq : acc' = insert y acc := by simp [acc', greedyStep, hins_ind]
      refine ih (seen ++ [y]) acc' hpw' hI_mem' hacc'_seen ?_ ?_
      · intro u hu
        rw [hacc'_eq] at hu
        rcases Finset.mem_insert.mp hu with rfl | hmem
        · exact Or.inl hyI
        · exact hacc_I0 u hmem
      · intro x hxI hx_sy
        rw [hacc'_eq]
        rcases List.mem_append.mp hx_sy with hx_s | hx_y
        · exact Finset.mem_insert_of_mem (hI_seen x hxI hx_s)
        · simp only [List.mem_singleton] at hx_y
          exact hx_y ▸ Finset.mem_insert_self y acc
    · by_cases hyJ : y ∈ J
      · have hwy : w y = k + 1 := by simp [w, hyI, hyJ]
        have hacc_sub_I : acc ⊆ I := by
          intro u hu
          rcases hacc_I0 u hu with huI | hwu0
          · exact huI
          · exfalso
            have hle := hseen_ge_y u (List.mem_toFinset.mp (hacc_seen hu))
            omega
        have hI_sub_acc : I ⊆ acc := by
          intro x hxI
          have hmem := hI_mem x hxI
          rcases List.mem_append.mp hmem with hx_s | hx_yt
          · exact hI_seen x hxI hx_s
          · exfalso
            rcases List.mem_cons.mp hx_yt with rfl | hx_t
            · exact hyI hxI
            · have hwx : w x = k + 2 := by simp [w, hxI]
              have hle := hy_ge_tail x hx_t
              omega
        have hacc_eq_I : acc = I := Finset.Subset.antisymm hacc_sub_I hI_sub_acc
        have hins_false : indep (insert y acc) = false := by
          rw [hacc_eq_I]
          exact hno_aug y hyJ hyI
        have hacc'_eq : acc' = acc := by simp [acc', greedyStep, hins_false]
        refine ih (seen ++ [y]) acc' hpw' hI_mem' hacc'_seen (hacc'_eq ▸ hacc_I0) ?_
        intro x hxI hx_sy
        rw [hacc'_eq]
        rcases List.mem_append.mp hx_sy with hx_s | hx_y
        · exact hI_seen x hxI hx_s
        · simp only [List.mem_singleton] at hx_y
          exact absurd (hx_y ▸ hxI) hyI
      · have hwy : w y = 0 := by simp [w, hyI, hyJ]
        refine ih (seen ++ [y]) acc' hpw' hI_mem' hacc'_seen ?_ ?_
        · intro u hu
          simp only [acc', greedyStep] at hu
          split at hu
          · rcases Finset.mem_insert.mp hu with rfl | hmem
            · exact Or.inr hwy
            · exact hacc_I0 u hmem
          · exact hacc_I0 u hu
        · intro x hxI hx_sy
          rcases List.mem_append.mp hx_sy with hx_s | hx_y
          · exact subset_greedyStep indep acc y (hI_seen x hxI hx_s)
          · simp only [List.mem_singleton] at hx_y
            exact absurd (hx_y ▸ hxI) hyI

/-- **Converse of Rado–Edmonds** ([Rado1957]; [Edmonds1971], Section 2): if `indep` is hereditary
and supported on `{x | x ∈ xs}`, and `greedyMaxBasis indep w xs` achieves weight at least
`∑ x ∈ J, w x` for every `ℕ`-valued weight function `w` and every `indep`-set `J`, then `indep`
satisfies the matroid augmentation axiom. -/
theorem augment_of_forall_sum_le_greedyMaxBasis
    {xs : List α} {indep : Finset α → Bool}
    (hhered : ∀ ⦃A B : Finset α⦄, indep B = true → A ⊆ B → indep A = true)
    (hsupp : ∀ ⦃A : Finset α⦄, indep A = true → ∀ x ∈ A, x ∈ xs)
    (hopt : ∀ (w : α → ℕ) (J : Finset α),
      indep J = true → ∑ x ∈ J, w x ≤ ∑ x ∈ greedyMaxBasis indep w xs, w x)
    ⦃I J : Finset α⦄ (hI : indep I = true) (hJ : indep J = true) (hlt : I.card < J.card) :
    ∃ e ∈ J, e ∉ I ∧ indep (insert e I) = true := by
  by_contra hno
  push Not at hno
  have hno_aug : ∀ e ∈ J, e ∉ I → indep (insert e I) = false := by
    intro e heJ heI
    cases hb : indep (insert e I)
    · rfl
    · exact absurd hb (hno e heJ heI)
  set k := I.card
  let w : α → ℕ := fun x => if x ∈ I then k + 2 else if x ∈ J then k + 1 else 0
  set ys := xs.mergeSort (fun a b => decide (w b ≤ w a))
  have hperm : ys.Perm xs := List.mergeSort_perm xs _
  have hI_mem_ys : ∀ x ∈ I, x ∈ ys := fun x hx =>
    hperm.mem_iff.mpr (hsupp hI x hx)
  have hpw : ([] ++ ys).Pairwise (fun a b => w b ≤ w a) := by
    simpa using pairwise_mergeSort_ge w xs
  have hG_inv := rado_edmonds_converse_inv hhered hI hno_aug [] ys ∅ hpw hI_mem_ys
    (by simp) (by simp) (by simp)
  set G := greedyMaxBasis indep w xs
  have hG_le : ∑ u ∈ G, w u ≤ k * (k + 2) := by
    have hsplit_G : ∑ u ∈ G, w u =
        ∑ u ∈ G.filter (· ∈ I), w u + ∑ u ∈ G.filter (· ∉ I), w u :=
      (Finset.sum_filter_add_sum_filter_not G (· ∈ I) w).symm
    have hzero : ∑ u ∈ G.filter (· ∉ I), w u = 0 := by
      refine Finset.sum_eq_zero fun u hu => ?_
      have hu' := Finset.mem_filter.mp hu
      rcases hG_inv u hu'.1 with huI | hwu0
      · exact absurd huI hu'.2
      · exact hwu0
    have hsub_I : G.filter (· ∈ I) ⊆ I := fun u hu => (Finset.mem_filter.mp hu).2
    have hle_I : ∑ u ∈ G.filter (· ∈ I), w u ≤ ∑ u ∈ I, w u :=
      Finset.sum_le_sum_of_subset hsub_I
    have hsum_I : ∑ u ∈ I, w u = k * (k + 2) := by
      have hcongr : ∑ u ∈ I, w u = ∑ _u ∈ I, (k + 2) :=
        Finset.sum_congr rfl fun u hu => by simp [w, hu]
      simpa [k] using hcongr
    omega
  have hJ_ge : (k + 1) * (k + 1) ≤ ∑ u ∈ J, w u := by
    have h1 : J.card * (k + 1) ≤ ∑ u ∈ J, w u := by
      have hsum : ∑ _u ∈ J, (k + 1) ≤ ∑ u ∈ J, w u := by
        refine Finset.sum_le_sum fun u hu => ?_
        by_cases huI : u ∈ I <;> simp [w, huI, hu]
      simpa using hsum
    exact (Nat.mul_le_mul_right (k + 1) hlt).trans h1
  have hopt_J : ∑ u ∈ J, w u ≤ ∑ u ∈ G, w u := hopt w J hJ
  have hcontra : (k + 1) * (k + 1) ≤ k * (k + 2) := hJ_ge.trans (hopt_J.trans hG_le)
  have hexpand : (k + 1) * (k + 1) = k * (k + 2) + 1 := by
    simp only [Nat.add_mul, Nat.mul_add]
    omega
  omega

/-- **Rado–Edmonds Characterization of Matroids** ([Rado1957]; [Edmonds1971], Section 2):
Let `xs : List α` enumerate a finite ground set and let `indep : Finset α → Bool` be a nonempty
hereditary Boolean predicate supported on `{x | x ∈ xs}`. Then `indep` is the finite-set
independence predicate of a matroid `M : Matroid α` with ground set `M.E = {x | x ∈ xs}` **if and
only if** for every nonnegative integer weight function `w : α → ℕ` and every `indep`-set `J`,
`greedyMaxBasis indep w xs` returns a set of weight at least `∑ x ∈ J, w x`. -/
theorem exists_matroid_iff_forall_sum_le_greedyMaxBasis
    (xs : List α) (indep : Finset α → Bool)
    (hempty : indep ∅ = true)
    (hhered : ∀ ⦃A B : Finset α⦄, indep B = true → A ⊆ B → indep A = true)
    (hsupp : ∀ ⦃A : Finset α⦄, indep A = true → ∀ x ∈ A, x ∈ xs) :
    (∃ M : Matroid α,
      M.E = {x | x ∈ xs} ∧ ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) ↔
      ∀ (w : α → ℕ) (J : Finset α),
        indep J = true → ∑ x ∈ J, w x ≤ ∑ x ∈ greedyMaxBasis indep w xs, w x := by
  refine ⟨?_, fun hopt => ?_⟩
  · rintro ⟨M, _, hM⟩ w J hJ
    have hJ_ind : M.Indep (J : Set α) := (hM J).mp hJ
    have hJ_sub : (J : Set α) ⊆ {x | x ∈ xs} := fun x hx => hsupp hJ x hx
    exact sum_le_greedyMaxBasis_of_indep hM w xs (fun _ _ => Nat.zero_le _) hJ_ind hJ_sub
  · have haug := augment_of_forall_sum_le_greedyMaxBasis hhered hsupp hopt
    let IM := IndepMatroid.ofFinset {x | x ∈ xs} (fun S => indep S = true) hempty hhered haug
      (fun ⦃I⦄ hI x hx => hsupp hI x hx)
    exact ⟨IM.matroid, rfl,
      fun S => (IM.matroid_indep_iff.trans (IndepMatroid.ofFinset_indep _ _ _ _ _ _)).symm⟩

/-- `Finset`-ground-set form of the **Rado–Edmonds Characterization**
(`exists_matroid_iff_forall_sum_le_greedyMaxBasis` instantiated at `E.toList`). -/
theorem exists_matroid_finset_iff_forall_sum_le_greedyMaxBasis
    (E : Finset α) (indep : Finset α → Bool)
    (hempty : indep ∅ = true)
    (hhered : ∀ ⦃A B : Finset α⦄, indep B = true → A ⊆ B → indep A = true)
    (hsupp : ∀ ⦃A : Finset α⦄, indep A = true → A ⊆ E) :
    (∃ M : Matroid α, M.E = (E : Set α) ∧ ∀ S : Finset α, indep S = true ↔ M.Indep (S : Set α)) ↔
      ∀ (w : α → ℕ) (J : Finset α),
        indep J = true → ∑ x ∈ J, w x ≤ ∑ x ∈ greedyMaxBasis indep w E.toList, w x := by
  have hset : ({x | x ∈ E.toList} : Set α) = (E : Set α) := by
    ext x
    simp
  rw [← hset]
  exact exists_matroid_iff_forall_sum_le_greedyMaxBasis E.toList indep hempty hhered
    (fun A hA x hx => Finset.mem_toList.mpr (hsupp hA hx))

end Weighted

end Cslib.Algorithms.Lean.Matroid
