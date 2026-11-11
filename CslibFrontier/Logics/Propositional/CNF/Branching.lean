/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.Foundations.Data.BranchingVector
public import CslibFrontier.Logics.Propositional.CNF.ModelCount.Declared
import CslibFrontier.Logics.Propositional.CNF.Eval
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.Fintype.Card

/-!
# Explicit SAT branching rules: covering vs. partitioning and sub-`2 ^ n` search trees

Branching SAT algorithms split a CNF formula `φ` into child formulas. Depending on the rule, child
branches either **cover** satisfying assignments (`CNF.CoversModels`: `φ.eval σ = true` iff some
branch evaluates to `true`, sufficient for decision and giving a subadditive model-count bound) or
**partition** them (`CNF.PartitionsModels`: every model of `φ` satisfies a unique branch and every
non-model satisfies none, conserving `modelCountOn` exactly across branches).

We package formula-level branching rules with their declared disposition (`CNF.BranchMode`,
`CNF.BranchRule`) and prove the exact disposition of three standard SAT rules:
* **Binary variable split** (`CNF.varSplitBranches v φ`): branching vector `[1, 1]`, partitions
  satisfying assignments (`CNF.partitionsModels_varSplitBranches`).
* **Naive clause literal cover** (`CNF.clauseCoverBranches c φ` for `c ∈ φ`): branching vector
  `[1, …, 1]`, covers satisfying assignments (`CNF.coversModels_clauseCoverBranches`), and fails to
  partition them whenever `c` has two literals on distinct variables
  (`CNF.not_partitionsModels_clauseCoverBranches_two`).
* **Disjoint prefix `k`-clause branching** (`CNF.clausePrefixBranches c φ` for `c ∈ φ`, fixing
  `[l₁]`, `[¬l₁, l₂]`, …, `[¬l₁, …, ¬l_{b-1}, l_b]`): partitions satisfying assignments
  (`CNF.partitionsModels_clausePrefixBranches`).

Eliminating assigned variables along disjoint prefix branches gives a terminating
`BranchingVector.BranchingTree` (`CNF.clausePrefixTree k` on `CNF.ClauseBranchState V`) with step
vector `prefixSteps b` (`b ≤ k`), conserving `modelCountOn`, deciding `Satisfiable` at its leaves,
and bounding the search tree by `(2 - (1 / 2) ^ k) ^ n` leaves (`< 2 ^ n` for `k ≥ 1`, `n ≥ 1`) and
`goldenBranchFactor ^ n` leaves for `2`-CNF.

## Main definitions

* `Cslib.Logic.PL.CNF.CoversModels`, `Cslib.Logic.PL.CNF.PartitionsModels`: covering and
  partitioning semantics for lists of child CNF formulas.
* `Cslib.Logic.PL.CNF.BranchMode`, `Cslib.Logic.PL.CNF.BranchRule`: branching rule specification
  recording covering vs. partitioning disposition.
* `Cslib.Logic.PL.CNF.varSplitBranches`, `Cslib.Logic.PL.CNF.clauseCoverBranches`,
  `Cslib.Logic.PL.CNF.clausePrefixBranches`: explicit SAT branching rules.
* `Cslib.Logic.PL.CNF.ClauseBranchState`, `Cslib.Logic.PL.CNF.clausePrefixTree`:
  variable-eliminating disjoint prefix `k`-clause `BranchingTree`.

## Main results

* `Cslib.Logic.PL.CNF.CoversModels.satisfiable_iff`,
  `Cslib.Logic.PL.CNF.CoversModels.modelCountOn_le_sum`,
  `Cslib.Logic.PL.CNF.PartitionsModels.modelCountOn_eq_sum`: decision equivalence, subadditivity,
  and exact count additivity.
* `Cslib.Logic.PL.CNF.partitionsModels_varSplitBranches`,
  `Cslib.Logic.PL.CNF.coversModels_clauseCoverBranches`,
  `Cslib.Logic.PL.CNF.not_partitionsModels_clauseCoverBranches_two`,
  `Cslib.Logic.PL.CNF.partitionsModels_clausePrefixBranches`: disposition of the three rules.
* `Cslib.Logic.PL.CNF.modelCountOn_eq_sum_clausePrefixTree_leaves`,
  `Cslib.Logic.PL.CNF.satisfiable_iff_exists_clausePrefixTree_leaf`,
  `Cslib.Logic.PL.CNF.leafCount_clausePrefixTree_le`,
  `Cslib.Logic.PL.CNF.leafCount_clausePrefixTree_two_le`: exact leaf count conservation,
  satisfiability equivalence, sub-`2 ^ n` `(2 - (1 / 2) ^ k) ^ n` bound, and golden-ratio `2`-CNF
  bound.

## References

* [F. V. Fomin, D. Kratsch, *Exact Exponential Algorithms*][FominKratsch2010]
-/

public section

namespace Cslib.Logic.PL.CNF

open Cslib.BranchingVector

variable {V : Type*}

/-! ### Covering vs. partitioning branch semantics -/

/-- `branches` **covers** the satisfying assignments of `φ`: an assignment satisfies `φ` if and only
if it satisfies at least one child formula in `branches`. -/
@[expose] def CoversModels (φ : CNF V) (branches : List (CNF V)) : Prop :=
  ∀ σ : V → Bool, φ.eval σ = true ↔ ∃ ψ ∈ branches, ψ.eval σ = true

/-- `branches` **partitions** the satisfying assignments of `φ`: every satisfying assignment of `φ`
satisfies a unique child formula in `branches`, and every non-satisfying assignment satisfies no
child formula. -/
@[expose] def PartitionsModels (φ : CNF V) (branches : List (CNF V)) : Prop :=
  ∀ σ : V → Bool, (branches.countP fun ψ : CNF V => ψ.eval σ) = if φ.eval σ then 1 else 0

/-- Whether a branching rule merely covers satisfying assignments or partitions them into pairwise
disjoint branches. -/
inductive BranchMode where
  /-- Every model of the parent satisfies at least one child, and every child model satisfies the
  parent (`CoversModels`). -/
  | covering
  /-- Every model of the parent satisfies a unique child, and non-models satisfy none
  (`PartitionsModels`). -/
  | partitioning
  deriving DecidableEq, Repr

/-- Formula-level SAT branching rule bundled with its declared `BranchMode` and soundness proof. -/
structure BranchRule (V : Type*) where
  /-- Declared solution-set disposition (`covering` or `partitioning`). -/
  mode : BranchMode
  /-- Domain of formulas on which the rule applies. -/
  valid : CNF V → Prop
  /-- Child formulas produced from an input formula. -/
  apply : CNF V → List (CNF V)
  /-- Verification of the declared disposition on `valid` formulas. -/
  sound : ∀ φ, valid φ →
    match mode with
    | .covering => CoversModels φ (apply φ)
    | .partitioning => PartitionsModels φ (apply φ)

/-- Every partitioning branching rule is in particular a covering branching rule. -/
theorem PartitionsModels.coversModels {φ : CNF V} {branches : List (CNF V)}
    (h : PartitionsModels φ branches) : CoversModels φ branches := by
  intro σ
  have hcount := h σ
  cases heval : φ.eval σ
  · simp only [heval, Bool.false_eq_true, ↓reduceIte] at hcount
    simp only [Bool.false_eq_true, false_iff, not_exists, not_and]
    exact fun ψ hψ => (List.countP_eq_zero.mp hcount) ψ hψ
  · simp only [heval, ↓reduceIte] at hcount
    simp only [true_iff]
    exact List.countP_pos_iff.mp (hcount ▸ Nat.zero_lt_one)

/-- A covering branching rule preserves satisfiability (`φ.Satisfiable` iff some branch is
satisfiable). -/
theorem CoversModels.satisfiable_iff {φ : CNF V} {branches : List (CNF V)}
    (h : CoversModels φ branches) :
    φ.Satisfiable ↔ ∃ ψ ∈ branches, ψ.Satisfiable := by
  constructor
  · rintro ⟨σ, hσ⟩
    obtain ⟨ψ, hψ, hψσ⟩ := (h σ).mp hσ
    exact ⟨ψ, hψ, σ, hψσ⟩
  · rintro ⟨ψ, hψ, σ, hψσ⟩
    exact ⟨σ, (h σ).mpr ⟨ψ, hψ, hψσ⟩⟩

/-- A partitioning branching rule preserves satisfiability. -/
theorem PartitionsModels.satisfiable_iff {φ : CNF V} {branches : List (CNF V)}
    (h : PartitionsModels φ branches) :
    φ.Satisfiable ↔ ∃ ψ ∈ branches, ψ.Satisfiable :=
  h.coversModels.satisfiable_iff

private def extDeclared [DecidableEq V] (declared : Finset V) (σ : declared → Bool) (v : V) :
    Bool :=
  if hv : v ∈ declared then σ ⟨v, hv⟩ else false

private theorem modelCountOn_eq_sum_ite [DecidableEq V] (φ : CNF V) (declared : Finset V) :
    φ.modelCountOn declared =
      ∑ σ : declared → Bool, if φ.eval (extDeclared declared σ) then 1 else 0 := by
  simp only [modelCountOn, Finset.card_filter]
  rfl

/-- **Subadditivity of covering rules.** If `CoversModels φ branches`, then
`φ.modelCountOn declared` is at most the sum of `ψ.modelCountOn declared` over `ψ ∈ branches`. -/
theorem CoversModels.modelCountOn_le_sum [DecidableEq V] {φ : CNF V} {branches : List (CNF V)}
    (h : CoversModels φ branches) (declared : Finset V) :
    φ.modelCountOn declared ≤ (branches.map fun ψ => ψ.modelCountOn declared).sum := by
  rw [modelCountOn_eq_sum_ite]
  have hpoint : ∀ σ : declared → Bool,
      (if φ.eval (extDeclared declared σ) then 1 else 0) ≤
        (branches.map fun ψ : CNF V => if ψ.eval (extDeclared declared σ) then 1 else 0).sum := by
    intro σ
    rw [← List.length_filter_eq_sum branches (fun ψ : CNF V => ψ.eval (extDeclared declared σ)),
      ← List.countP_eq_length_filter]
    cases heval : φ.eval (extDeclared declared σ)
    · simp only [Bool.false_eq_true, ↓reduceIte, Nat.zero_le]
    · simp only [↓reduceIte]
      exact Nat.succ_le_of_lt (List.countP_pos_iff.mpr ((h _).mp heval))
  refine (Finset.sum_le_sum fun σ _ => hpoint σ).trans ?_
  rw [Finset.sum_list_sum_comm]
  simp only [← modelCountOn_eq_sum_ite, le_refl]

/-- **Additivity of partitioning rules.** If `PartitionsModels φ branches`, then
`φ.modelCountOn declared` equals the sum of `ψ.modelCountOn declared` over `ψ ∈ branches`. -/
theorem PartitionsModels.modelCountOn_eq_sum [DecidableEq V] {φ : CNF V} {branches : List (CNF V)}
    (h : PartitionsModels φ branches) (declared : Finset V) :
    φ.modelCountOn declared = (branches.map fun ψ => ψ.modelCountOn declared).sum := by
  rw [modelCountOn_eq_sum_ite]
  have hpoint : ∀ σ : declared → Bool,
      (if φ.eval (extDeclared declared σ) then 1 else 0) =
        (branches.map fun ψ : CNF V => if ψ.eval (extDeclared declared σ) then 1 else 0).sum := by
    intro σ
    rw [← List.length_filter_eq_sum branches (fun ψ : CNF V => ψ.eval (extDeclared declared σ)),
      ← List.countP_eq_length_filter]
    exact (h _).symm
  calc
    ∑ σ : declared → Bool, (if φ.eval (extDeclared declared σ) then 1 else 0)
        = ∑ σ : declared → Bool, (branches.map fun ψ : CNF V =>
            if ψ.eval (extDeclared declared σ) then 1 else 0).sum :=
      Finset.sum_congr rfl fun σ _ => hpoint σ
    _ = (branches.map fun ψ => ψ.modelCountOn declared).sum := by
      rw [Finset.sum_list_sum_comm]
      simp only [← modelCountOn_eq_sum_ite]

/-! ### Explicit formula-level SAT branching rules -/

/-- **Binary variable split** on `v`: add the unit clause `[(v, true)]` or `[(v, false)]`. -/
@[expose] def varSplitBranches (v : V) (φ : CNF V) : List (CNF V) :=
  [[(v, true)] :: φ, [(v, false)] :: φ]

/-- Binary variable splitting partitions satisfying assignments on every formula. -/
theorem partitionsModels_varSplitBranches (v : V) (φ : CNF V) :
    PartitionsModels φ (varSplitBranches v φ) := by
  intro σ
  simp only [varSplitBranches, List.countP_cons, List.countP_nil, eval_cons, Clause.eval_cons,
    Clause.eval_nil, Bool.or_false, Literal.eval_mk]
  cases σ v <;> cases φ.eval σ <;> rfl

/-- Packaged `BranchRule` for binary variable splitting (`mode = .partitioning`). -/
@[expose] def varSplitRule (v : V) : BranchRule V where
  mode := .partitioning
  valid _ := True
  apply := varSplitBranches v
  sound φ _ := partitionsModels_varSplitBranches v φ

/-- **Naive clause literal cover** on `c`: one branch `[l] :: φ` per literal occurrence `l ∈ c`. -/
@[expose] def clauseCoverBranches (c : Clause V) (φ : CNF V) : List (CNF V) :=
  c.map fun l => [l] :: φ

/-- Naive clause literal branching covers satisfying assignments whenever `c ∈ φ`. -/
theorem coversModels_clauseCoverBranches {c : Clause V} {φ : CNF V} (hc : c ∈ φ) :
    CoversModels φ (clauseCoverBranches c φ) := by
  intro σ
  simp only [clauseCoverBranches, List.mem_map, exists_exists_and_eq_and, eval_cons,
    Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.and_eq_true]
  constructor
  · intro hφ
    have hc_true : c.eval σ = true := (CNF.eval_eq_true_iff σ φ).mp hφ c hc
    obtain ⟨l, hl, hσl⟩ := (Clause.eval_eq_true_iff σ c).mp hc_true
    exact ⟨l, hl, (Literal.eval_eq_true_iff σ l).mpr hσl, hφ⟩
  · rintro ⟨_, _, _, hφ⟩
    exact hφ

/-- Packaged `BranchRule` for naive clause literal branching (`mode = .covering`). -/
@[expose] def clauseCoverRule (c : Clause V) : BranchRule V where
  mode := .covering
  valid φ := c ∈ φ
  apply := clauseCoverBranches c
  sound _ hc := coversModels_clauseCoverBranches hc

/-- **Naive clause literal branching does not partition models.** On `[ [l₁, l₂] ]` with distinct
variables `l₁.1 ≠ l₂.1`, setting both literals `true` satisfies both branches simultaneously. -/
theorem not_partitionsModels_clauseCoverBranches_two {l₁ l₂ : Literal V}
    (hne : l₁.1 ≠ l₂.1) :
    ¬ PartitionsModels [[l₁, l₂]] (clauseCoverBranches [l₁, l₂] [[l₁, l₂]]) := by
  classical
  intro hpart
  let σ : V → Bool := Function.update (Function.update (fun _ => false) l₁.1 l₁.2) l₂.1 l₂.2
  have hl₁ : Literal.eval σ l₁ = true := by
    rw [Literal.eval_eq_true_iff]
    simp only [σ, Function.update_of_ne hne, Function.update_self]
  have hl₂ : Literal.eval σ l₂ = true := by
    rw [Literal.eval_eq_true_iff]
    simp only [σ, Function.update_self]
  have hspec := hpart σ
  simp only [clauseCoverBranches, List.map_cons, List.map_nil, List.countP_cons, List.countP_nil,
    eval_cons, eval_nil, Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.and_true,
    hl₁, hl₂, Bool.true_or, ↓reduceIte] at hspec
  omega

/-- Disjoint literal prefixes `[l₁]`, `[¬l₁, l₂]`, …, `[¬l₁, …, ¬l_{b-1}, l_b]` of a clause `c`. -/
@[expose] def clausePrefixLitsList : Clause V → List (List (Literal V))
  | [] => []
  | l :: ls => [l] :: (clausePrefixLitsList ls).map (Std.Sat.Literal.negate l :: ·)

@[simp] theorem length_clausePrefixLitsList (c : Clause V) :
    (clausePrefixLitsList c).length = c.length := by
  induction c with
  | nil => rfl
  | cons _ ls ih => simp only [clausePrefixLitsList, List.length_cons, List.length_map, ih]

private theorem map_succ_range' (a n : ℕ) :
    (List.range' a n).map (· + 1) = List.range' (a + 1) n := by
  induction n generalizing a with
  | zero => rfl
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons]
    rw [ih (a + 1)]

/-- The prefix lengths of `clausePrefixLitsList c` form the branching vector `prefixSteps c.length`
(`[1, 2, …, c.length]`). -/
theorem map_length_clausePrefixLitsList (c : Clause V) :
    (clausePrefixLitsList c).map List.length = prefixSteps c.length := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    rw [clausePrefixLitsList, List.map_cons, List.length_singleton, List.map_map,
      List.length_cons, prefixSteps, List.range'_succ]
    congr 1
    have hcomp : (List.length ∘ fun xs => Std.Sat.Literal.negate l :: xs) =
        ((· + 1) ∘ List.length) := rfl
    rw [hcomp, ← List.map_map, ih, prefixSteps, map_succ_range']

/-- For any assignment `σ`, the number of prefixes in `clausePrefixLitsList c` satisfied by `σ` is
`1` when `c.eval σ = true` and `0` when `c.eval σ = false`. -/
theorem countP_all_clausePrefixLitsList (c : Clause V) (σ : V → Bool) :
    ((clausePrefixLitsList c).countP fun lits => lits.all (Literal.eval σ)) =
      if c.eval σ then 1 else 0 := by
  induction c with
  | nil => rfl
  | cons l ls ih =>
    rw [clausePrefixLitsList, List.countP_cons, List.all_cons, List.all_nil, Bool.and_true,
      Clause.eval_cons]
    cases hl : Literal.eval σ l
    · simp only [Bool.false_eq_true, ↓reduceIte, Bool.false_or, Nat.add_zero, List.countP_map]
      have hcongr : ((fun lits => lits.all (Literal.eval σ)) ∘
          fun xs => Std.Sat.Literal.negate l :: xs) = fun xs => xs.all (Literal.eval σ) := by
        funext xs
        simp only [Function.comp_def, List.all_cons, Literal.eval_negate, hl, Bool.not_false,
          Bool.true_and]
      rw [hcongr, ih]
    · simp only [↓reduceIte, Bool.true_or]
      have hzero : ((clausePrefixLitsList ls).countP
          ((fun lits => lits.all (Literal.eval σ)) ∘
            fun xs => Std.Sat.Literal.negate l :: xs)) = 0 := by
        rw [List.countP_eq_zero]
        intro xs _
        simp only [Function.comp_def, List.all_cons, Literal.eval_negate, hl, Bool.not_true,
          Bool.false_and, Bool.false_eq_true, not_false_eq_true]
      rw [List.countP_map, hzero]

/-- **Disjoint prefix clause branching** (`[l₁]`, `[¬l₁, l₂]`, …) as formula-level unit-clause
extensions of `φ`. -/
@[expose] def clausePrefixBranches (c : Clause V) (φ : CNF V) : List (CNF V) :=
  (clausePrefixLitsList c).map fun lits => (lits.map (fun l => ([l] : Clause V)) ++ φ : CNF V)

private theorem eval_map_singleton_append (lits : List (Literal V)) (φ : CNF V) (σ : V → Bool) :
    CNF.eval σ (lits.map (fun l => ([l] : Clause V)) ++ φ) =
      (lits.all (Literal.eval σ) && φ.eval σ) := by
  rw [CNF.eval_append]
  congr 1
  induction lits with
  | nil => rfl
  | cons l rest ih =>
    simp only [List.map_cons, CNF.eval_cons, Clause.eval_cons, Clause.eval_nil, Bool.or_false,
      List.all_cons, ih]

private theorem map_fst_sublist_of_mem_clausePrefixLitsList {c : Clause V}
    {lits : List (Literal V)} (hlits : lits ∈ clausePrefixLitsList c) :
    List.Sublist (lits.map Prod.fst) (c.map Prod.fst) := by
  induction c generalizing lits with
  | nil => nomatch hlits
  | cons l ls ih =>
    rw [clausePrefixLitsList, List.mem_cons] at hlits
    rcases hlits with rfl | htail
    · simp only [List.map_cons]
      exact List.Sublist.cons_cons l.1 (List.nil_sublist _)
    · obtain ⟨rest, hrest, rfl⟩ := List.mem_map.mp htail
      have hneg_fst : (Std.Sat.Literal.negate l).1 = l.1 := by
        cases l.2 <;> rfl
      simp only [List.map_cons, hneg_fst]
      exact List.Sublist.cons_cons l.1 (ih hrest)

/-- Whenever `c` holds on every model of `φ` (`∀ σ, φ.eval σ = true → c.eval σ = true`),
`clausePrefixBranches c φ` partitions the models of `φ`. -/
theorem partitionsModels_clausePrefixBranches_of_imp {c : Clause V} {φ : CNF V}
    (himp : ∀ σ : V → Bool, φ.eval σ = true → Clause.eval σ c = true) :
    PartitionsModels φ (clausePrefixBranches c φ) := by
  intro σ
  rw [clausePrefixBranches, List.countP_map]
  cases hφ : φ.eval σ
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [List.countP_eq_zero]
    intro lits _
    simp only [Function.comp_def, eval_map_singleton_append, hφ, Bool.and_false,
      Bool.false_eq_true, not_false_eq_true]
  · have hc_true : Clause.eval σ c = true := himp σ hφ
    have hcomp : ((fun ψ : CNF V => ψ.eval σ) ∘ fun lits : List (Literal V) =>
        (lits.map (fun l => ([l] : Clause V)) ++ φ : CNF V)) =
        fun lits => lits.all (Literal.eval σ) := by
      funext lits
      simp only [Function.comp_def, eval_map_singleton_append, hφ, Bool.and_true]
    rw [hcomp, countP_all_clausePrefixLitsList, hc_true]

/-- **Disjoint prefix clause branching partitions models** whenever `c ∈ φ`. -/
theorem partitionsModels_clausePrefixBranches {c : Clause V} {φ : CNF V} (hc : c ∈ φ) :
    PartitionsModels φ (clausePrefixBranches c φ) :=
  partitionsModels_clausePrefixBranches_of_imp fun σ hφ => (CNF.eval_eq_true_iff σ φ).mp hφ c hc

/-- Packaged `BranchRule` for disjoint prefix clause branching (`mode = .partitioning`). -/
@[expose] def clausePrefixRule (c : Clause V) : BranchRule V where
  mode := .partitioning
  valid φ := c ∈ φ
  apply := clausePrefixBranches c
  sound _ hc := partitionsModels_clausePrefixBranches hc

/-! ### Variable-eliminating disjoint prefix `k`-clause search tree -/

section Elimination

variable [DecidableEq V]

/-- Substitute a fixed literal `l = (v, b)` into `φ`: drop clauses containing `l` and delete `¬l`
from all remaining clauses. -/
@[expose] def substLit (l : Literal V) (φ : CNF V) : CNF V :=
  φ.filterMap fun c => if l ∈ c then none else some (c.filter (· ≠ Std.Sat.Literal.negate l))

/-- Evaluating `substLit l φ` at `σ` agrees with evaluating `φ` at `Function.update σ l.1 l.2`. -/
theorem eval_substLit (l : Literal V) (φ : CNF V) (σ : V → Bool) :
    (substLit l φ).eval σ = φ.eval (Function.update σ l.1 l.2) := by
  induction φ with
  | nil => rfl
  | cons c rest ih =>
    rw [substLit, List.filterMap_cons, CNF.eval_cons]
    by_cases hmem : l ∈ c
    · simp only [hmem, ↓reduceIte]
      have hc_true : c.eval (Function.update σ l.1 l.2) = true := by
        rw [Clause.eval_eq_true_iff]
        exact ⟨l, hmem, Function.update_self l.1 l.2 σ⟩
      rw [hc_true, Bool.true_and]
      exact ih
    · simp only [hmem, ↓reduceIte, CNF.eval_cons]
      rw [← substLit, ih]
      congr 1
      rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
      constructor
      · rintro ⟨l', hl', hσ'⟩
        obtain ⟨hl'_c, hne_neg⟩ := List.mem_filter.mp hl'
        refine ⟨l', hl'_c, ?_⟩
        by_cases hv : l'.1 = l.1
        · exfalso
          obtain ⟨v, b⟩ := l
          obtain ⟨v', b'⟩ := l'
          dsimp only at hv
          subst hv
          cases b <;> cases b'
          · exact hmem hl'_c
          · exact (of_decide_eq_true hne_neg) rfl
          · exact (of_decide_eq_true hne_neg) rfl
          · exact hmem hl'_c
        · simpa only [Function.update_of_ne hv] using hσ'
      · rintro ⟨l', hl'_c, hupd⟩
        by_cases hv : l'.1 = l.1
        · exfalso
          obtain ⟨v, b⟩ := l
          obtain ⟨v', b'⟩ := l'
          dsimp only at hv hupd
          subst hv
          rw [Function.update_self] at hupd
          subst hupd
          exact hmem hl'_c
        · rw [Function.update_of_ne hv] at hupd
          refine ⟨l', List.mem_filter.mpr ⟨hl'_c, decide_eq_true fun hneg => hv ?_⟩, hupd⟩
          have hfst : (Std.Sat.Literal.negate l).1 = l.1 := by cases l.2 <;> rfl
          exact (congrArg Prod.fst hneg).trans hfst

/-- `substLit l φ` eliminates every occurrence of `l.1`. -/
theorem notMem_vars_substLit (l : Literal V) (φ : CNF V) : l.1 ∉ (substLit l φ).vars := by
  rw [CNF.mem_vars]
  rintro ⟨c', hc', b', hb'⟩
  rw [substLit, List.mem_filterMap] at hc'
  obtain ⟨c, _, hopt⟩ := hc'
  by_cases hmem : l ∈ c
  · simp only [hmem, ↓reduceIte, reduceCtorEq] at hopt
  · simp only [hmem, ↓reduceIte, Option.some.injEq] at hopt
    subst hopt
    obtain ⟨hb'_c, hne_neg⟩ := List.mem_filter.mp hb'
    obtain ⟨v, b⟩ := l
    dsimp only at hb'_c hne_neg
    cases b <;> cases b'
    · exact hmem hb'_c
    · exact (of_decide_eq_true hne_neg) rfl
    · exact (of_decide_eq_true hne_neg) rfl
    · exact hmem hb'_c

/-- Every variable occurring in `substLit l φ` belonged to `φ.vars.toFinset.erase l.1`. -/
theorem vars_substLit_subset (l : Literal V) (φ : CNF V) :
    (substLit l φ).vars.toFinset ⊆ φ.vars.toFinset.erase l.1 := by
  intro w hw
  rw [List.mem_toFinset] at hw
  refine Finset.mem_erase.mpr ⟨fun h => notMem_vars_substLit l φ (h ▸ hw), ?_⟩
  rw [List.mem_toFinset, CNF.mem_vars]
  obtain ⟨c', hc', b', hb'⟩ := CNF.mem_vars.mp hw
  rw [substLit, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hopt⟩ := hc'
  by_cases hmem : l ∈ c
  · simp only [hmem, ↓reduceIte, reduceCtorEq] at hopt
  · simp only [hmem, ↓reduceIte, Option.some.injEq] at hopt
    subst hopt
    exact ⟨c, hc, b', (List.mem_filter.mp hb').1⟩

/-- `substLit` never increases maximum clause length. -/
theorem length_le_of_mem_substLit {l : Literal V} {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) {c' : Clause V} (hc' : c' ∈ substLit l φ) :
    c'.length ≤ k := by
  rw [substLit, List.mem_filterMap] at hc'
  obtain ⟨c, hc, hopt⟩ := hc'
  by_cases hmem : l ∈ c
  · simp only [hmem, ↓reduceIte, reduceCtorEq] at hopt
  · simp only [hmem, ↓reduceIte, Option.some.injEq] at hopt
    subst hopt
    exact (List.length_filter_le _ c).trans (hk c hc)

/-- Adding `[l]` to `φ` on `U` (`l.1 ∈ U`) has the same model count as `substLit l φ` on
`U.erase l.1`. -/
theorem modelCountOn_cons_unit_eq_substLit {l : Literal V} {φ : CNF V} {U : Finset V}
    (hl : l.1 ∈ U) :
    CNF.modelCountOn (([l] : Clause V) :: φ) U = (substLit l φ).modelCountOn (U.erase l.1) := by
  let extU (σ : U → Bool) (v : V) : Bool := if hv : v ∈ U then σ ⟨v, hv⟩ else false
  let extE (τ : U.erase l.1 → Bool) (v : V) : Bool :=
    if hv : v ∈ U.erase l.1 then τ ⟨v, hv⟩ else false
  let ins (τ : U.erase l.1 → Bool) (u : U) : Bool :=
    if h : u.1 = l.1 then l.2 else τ ⟨u.1, Finset.mem_erase.mpr ⟨h, u.2⟩⟩
  have heval_ins (τ : U.erase l.1 → Bool) :
      Function.update (extE τ) l.1 l.2 = extU (ins τ) := by
    funext v
    by_cases hv : v = l.1
    · subst hv
      simp only [Function.update_self, extU, hl, ↓reduceDIte, ins]
    · rw [Function.update_of_ne hv]
      by_cases hvU : v ∈ U
      · have hvE : v ∈ U.erase l.1 := Finset.mem_erase.mpr ⟨hv, hvU⟩
        simp only [extE, hvE, ↓reduceDIte, extU, hvU, ins, hv]
      · have hvE : v ∉ U.erase l.1 := fun h => hvU (Finset.mem_of_mem_erase h)
        simp only [extE, hvE, ↓reduceDIte, extU, hvU]
  let e : {σ : U → Bool // CNF.eval (extU σ) (([l] : Clause V) :: φ) = true} ≃
      {τ : U.erase l.1 → Bool // (substLit l φ).eval (extE τ) = true} :=
    { toFun := fun ⟨σ, hσ⟩ =>
        ⟨fun u => σ ⟨u.1, Finset.mem_of_mem_erase u.2⟩, by
          rw [CNF.eval_cons, Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.and_eq_true,
            Literal.eval_eq_true_iff] at hσ
          have hl_eq : σ ⟨l.1, hl⟩ = l.2 := by simpa only [extU, hl, ↓reduceDIte] using hσ.1
          have hins : ins (fun u => σ ⟨u.1, Finset.mem_of_mem_erase u.2⟩) = σ := by
            funext ⟨v, hv⟩
            by_cases hvl : v = l.1
            · subst hvl
              simpa only [ins, ↓reduceDIte] using hl_eq.symm
            · simp only [ins, hvl, ↓reduceDIte]
          rw [eval_substLit, heval_ins (fun u => σ ⟨u.1, Finset.mem_of_mem_erase u.2⟩), hins]
          exact hσ.2⟩
      invFun := fun ⟨τ, hτ⟩ =>
        ⟨ins τ, by
          rw [CNF.eval_cons, Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.and_eq_true,
            Literal.eval_eq_true_iff]
          refine ⟨by simp only [extU, hl, ↓reduceDIte, ins], ?_⟩
          rwa [eval_substLit, heval_ins] at hτ⟩
      left_inv := fun ⟨σ, hσ⟩ => by
        apply Subtype.ext
        funext ⟨v, hv⟩
        rw [CNF.eval_cons, Clause.eval_cons, Clause.eval_nil, Bool.or_false, Bool.and_eq_true,
          Literal.eval_eq_true_iff] at hσ
        have hl_eq : σ ⟨l.1, hl⟩ = l.2 := by simpa only [extU, hl, ↓reduceDIte] using hσ.1
        by_cases hvl : v = l.1
        · subst hvl
          simpa only [ins, ↓reduceDIte] using hl_eq.symm
        · simp only [ins, hvl, ↓reduceDIte]
      right_inv := fun ⟨τ, _⟩ => by
        apply Subtype.ext
        funext ⟨v, hv⟩
        have hne : v ≠ l.1 := (Finset.mem_erase.mp hv).1
        simp only [ins, hne, ↓reduceDIte] }
  simpa only [modelCountOn, Fintype.card_subtype] using Fintype.card_congr e

/-- Sequentially substitute a list of literals into `φ`. -/
@[expose] def substLits (lits : List (Literal V)) (φ : CNF V) : CNF V :=
  lits.foldl (fun ψ l => substLit l ψ) φ

/-- Sequentially erase the variables of `lits` from `U`. -/
@[expose] def eraseLits (lits : List (Literal V)) (U : Finset V) : Finset V :=
  lits.foldl (fun S l => S.erase l.1) U

/-- Erasing `lits` with distinct variables contained in `U` decreases `U.card` by `lits.length`. -/
theorem card_eraseLits_add {lits : List (Literal V)} {U : Finset V}
    (hnodup : (lits.map Prod.fst).Nodup) (hsub : ∀ l ∈ lits, l.1 ∈ U) :
    (eraseLits lits U).card + lits.length = U.card := by
  induction lits generalizing U with
  | nil => simp only [eraseLits, List.foldl_nil, List.length_nil, Nat.add_zero]
  | cons l rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    have hlU : l.1 ∈ U := hsub l List.mem_cons_self
    have hrest : ∀ l' ∈ rest, l'.1 ∈ U.erase l.1 := by
      intro l' hl'
      refine Finset.mem_erase.mpr ⟨fun heq => hnodup.1 ?_, hsub l' (List.mem_cons_of_mem _ hl')⟩
      exact List.mem_map.mpr ⟨l', hl', heq⟩
    have hstep := ih hnodup.2 hrest
    have herase : (U.erase l.1).card + 1 = U.card := Finset.card_erase_add_one hlU
    simp only [eraseLits, List.foldl_cons, List.length_cons] at hstep ⊢
    omega

/-- `substLits` preserves `vars.toFinset ⊆ eraseLits lits U` when `φ.vars.toFinset ⊆ U`. -/
theorem vars_substLits_subset {lits : List (Literal V)} {φ : CNF V} {U : Finset V}
    (hvars : φ.vars.toFinset ⊆ U) :
    (substLits lits φ).vars.toFinset ⊆ eraseLits lits U := by
  induction lits generalizing φ U with
  | nil => exact hvars
  | cons l rest ih =>
    refine ih ((vars_substLit_subset l φ).trans ?_)
    exact Finset.erase_subset_erase l.1 hvars

/-- `substLits` preserves clause-width bounds. -/
theorem length_le_of_mem_substLits {lits : List (Literal V)} {φ : CNF V} {k : ℕ}
    (hk : ∀ c ∈ φ, c.length ≤ k) :
    ∀ c' ∈ substLits lits φ, c'.length ≤ k := by
  induction lits generalizing φ with
  | nil => exact hk
  | cons l rest ih => exact ih fun _ hc' => length_le_of_mem_substLit hk hc'

private theorem substLit_map_units (l : Literal V) (rest : List (Literal V))
    (hnodup : l.1 ∉ rest.map Prod.fst) :
    substLit l (rest.map fun x => ([x] : Clause V)) = rest.map fun x => ([x] : Clause V) := by
  induction rest with
  | nil => rfl
  | cons l' rs ihr =>
    have hne_var : l'.1 ≠ l.1 := fun heq =>
      hnodup (List.mem_map.mpr ⟨l', List.mem_cons_self, heq⟩)
    have hne1 : l ≠ l' := fun h => hne_var (congrArg Prod.fst h).symm
    have hne2 : decide (l' ≠ Std.Sat.Literal.negate l) = true := by
      refine decide_eq_true fun h => hne_var ?_
      rw [h]
      cases l.2 <;> rfl
    have htail : l.1 ∉ rs.map Prod.fst := fun h => hnodup (List.mem_cons_of_mem _ h)
    rw [List.map_cons, substLit, List.filterMap_cons]
    simp only [List.mem_singleton, hne1, ↓reduceIte, List.filter_cons, hne2, List.filter_nil]
    exact congrArg ([l'] :: ·) (ihr htail)

/-- Conjoining unit clauses `[l]` for `l ∈ lits` with distinct variables in `U` has the same model
count on `U` as `substLits lits φ` on `eraseLits lits U`. -/
theorem modelCountOn_append_units_eq_substLits {lits : List (Literal V)} {φ : CNF V} {U : Finset V}
    (hnodup : (lits.map Prod.fst).Nodup) (hsub : ∀ l ∈ lits, l.1 ∈ U) :
    CNF.modelCountOn (lits.map (fun l => ([l] : Clause V)) ++ φ) U =
      (substLits lits φ).modelCountOn (eraseLits lits U) := by
  induction lits generalizing φ U with
  | nil => rfl
  | cons l rest ih =>
    rw [List.map_cons, List.nodup_cons] at hnodup
    have hlU : l.1 ∈ U := hsub l List.mem_cons_self
    have hrest : ∀ l' ∈ rest, l'.1 ∈ U.erase l.1 := by
      intro l' hl'
      refine Finset.mem_erase.mpr ⟨fun heq => hnodup.1 ?_, hsub l' (List.mem_cons_of_mem _ hl')⟩
      exact List.mem_map.mpr ⟨l', hl', heq⟩
    have hcomm :=
      modelCountOn_cons_unit_eq_substLit (φ := rest.map (fun x => ([x] : Clause V)) ++ φ) hlU
    have hsubst_units : substLit l (rest.map (fun x => ([x] : Clause V)) ++ φ) =
        rest.map (fun x => ([x] : Clause V)) ++ substLit l φ := by
      rw [substLit, List.filterMap_append, ← substLit, ← substLit,
        substLit_map_units l rest hnodup.1]
    rw [List.map_cons, List.cons_append, hcomm, hsubst_units]
    exact ih hnodup.2 hrest

/-- Whether a clause contains complementary literals `l` and `¬l` (making it a tautology). -/
@[expose] def isTautClause (c : Clause V) : Bool :=
  c.any fun l => decide (Std.Sat.Literal.negate l ∈ c)

/-- A tautological clause evaluates to `true` under every assignment. -/
theorem eval_eq_true_of_isTautClause {c : Clause V} (ht : isTautClause c = true) (σ : V → Bool) :
    c.eval σ = true := by
  simp only [isTautClause, List.any_eq_true, decide_eq_true_eq] at ht
  obtain ⟨l, hl, hneg⟩ := ht
  rw [Clause.eval_eq_true_iff]
  by_cases h : σ l.1 = l.2
  · exact ⟨l, hl, h⟩
  · refine ⟨Std.Sat.Literal.negate l, hneg, ?_⟩
    obtain ⟨v, b⟩ := l
    cases b <;> cases hσ : σ v <;> simp_all [Std.Sat.Literal.negate]

/-- Deduplicating a non-tautological clause produces distinct variables. -/
theorem nodup_map_fst_dedup_of_not_isTautClause {c : Clause V} (ht : isTautClause c = false) :
    (c.dedup.map Prod.fst).Nodup := by
  have hnt : ∀ l ∈ c, Std.Sat.Literal.negate l ∉ c := by
    intro l hl hneg
    have : isTautClause c = true := by
      simp only [isTautClause, List.any_eq_true, decide_eq_true_eq]
      exact ⟨l, hl, hneg⟩
    rw [ht] at this
    exact Bool.noConfusion this
  have hinj : Set.InjOn (Prod.fst : Literal V → V) {l | l ∈ c.dedup} := by
    rintro ⟨v₁, b₁⟩ h₁ ⟨v₂, b₂⟩ h₂ hv
    dsimp only at hv
    subst hv
    rw [Set.mem_ofPred_eq, List.mem_dedup] at h₁ h₂
    cases b₁ <;> cases b₂
    · rfl
    · exact absurd h₂ (hnt (v₁, false) h₁)
    · exact absurd h₂ (hnt (v₁, true) h₁)
    · rfl
  exact c.nodup_dedup.map_on hinj

/-- Deduplicating a clause preserves its evaluation under every assignment. -/
theorem eval_dedup_clause (c : Clause V) (σ : V → Bool) :
    Clause.eval σ c.dedup = Clause.eval σ c := by
  rw [Bool.eq_iff_iff, Clause.eval_eq_true_iff, Clause.eval_eq_true_iff]
  simp only [List.mem_dedup]

/-- Search-tree state for variable-eliminating CNF branching: remaining `unassigned` variables and
residual `formula`. -/
structure ClauseBranchState (V : Type*) where
  /-- Variables not yet fixed along the current branch. -/
  unassigned : Finset V
  /-- Residual CNF formula over `unassigned`. -/
  formula : CNF V

/-- Predicate selecting a non-tautological clause supported in `U` with deduplicated width in
`[1, k]`. -/
@[expose] def isPivotClause (k : ℕ) (U : Finset V) (c : Clause V) : Bool :=
  !isTautClause c && c.all (fun l => decide (l.1 ∈ U)) &&
    decide (1 ≤ c.dedup.length ∧ c.dedup.length ≤ k)

/-- First pivot clause of `s.formula`, if `[] ∉ s.formula`. -/
@[expose] def pivotClause (k : ℕ) (s : ClauseBranchState V) : Option (Clause V) :=
  if [] ∈ s.formula then none else s.formula.find? (isPivotClause k s.unassigned)

private theorem mem_and_isPivotClause_of_pivotClause_eq_some {k : ℕ} {s : ClauseBranchState V}
    {c : Clause V} (hpiv : pivotClause k s = some c) :
    c ∈ s.formula ∧ isPivotClause k s.unassigned c = true := by
  unfold pivotClause at hpiv
  split_ifs at hpiv
  exact ⟨List.mem_of_find?_eq_some hpiv, List.find?_some hpiv⟩

/-- **Disjoint prefix `k`-clause `BranchingTree`** on `ClauseBranchState V`, measured by
`s.unassigned.card` with branching vector `prefixSteps k = [1, 2, …, k]`. -/
@[expose] def clausePrefixTree (k : ℕ) : BranchingTree (ClauseBranchState V) where
  isLeaf s := (pivotClause k s).isNone
  children s :=
    match pivotClause k s with
    | none => []
    | some c =>
      (clausePrefixLitsList c.dedup).map fun lits =>
        { unassigned := eraseLits lits s.unassigned
          formula := substLits lits s.formula }
  measure s := s.unassigned.card
  steps := prefixSteps k
  steps_pos _ hd := prefixSteps_pos hd
  children_steps s hleaf := by
    cases hpiv : pivotClause k s with
    | none =>
      simp only [hpiv, Option.isNone_none, Bool.true_eq_false] at hleaf
    | some c =>
      obtain ⟨_, hpred⟩ := mem_and_isPivotClause_of_pivotClause_eq_some hpiv
      simp only [isPivotClause, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
        decide_eq_true_eq] at hpred
      obtain ⟨⟨htaut, hallU⟩, _, hlenk⟩ := hpred
      have hnodup_c : (c.dedup.map Prod.fst).Nodup := nodup_map_fst_dedup_of_not_isTautClause htaut
      refine ⟨prefixSteps c.dedup.length, prefixSteps_sublist hlenk, ?_⟩
      rw [← map_length_clausePrefixLitsList c.dedup]
      have hsame : List.Forall₂
          (fun lits => fun d =>
            (eraseLits lits s.unassigned).card + d ≤ s.unassigned.card)
          (clausePrefixLitsList c.dedup) ((clausePrefixLitsList c.dedup).map List.length) := by
        refine List.forall₂_map_right_iff.mpr (List.forall₂_same.mpr fun lits hlits => ?_)
        have hsub_fst := map_fst_sublist_of_mem_clausePrefixLitsList hlits
        have hnodup_lits : (lits.map Prod.fst).Nodup := hsub_fst.nodup hnodup_c
        have hU_lits : ∀ l ∈ lits, l.1 ∈ s.unassigned := by
          intro l hl
          have hf_mem : l.1 ∈ c.dedup.map Prod.fst :=
            hsub_fst.subset (List.mem_map_of_mem hl)
          obtain ⟨l', hl', heq⟩ := List.mem_map.mp hf_mem
          exact heq ▸ hallU l' (List.mem_dedup.mp hl')
        exact (card_eraseLits_add hnodup_lits hU_lits).le
      exact List.forall₂_map_left_iff.mpr hsame

private theorem valid_preserved {k : ℕ} {u child : ClauseBranchState V}
    (hleaf : (clausePrefixTree k).isLeaf u = false)
    (hchild : child ∈ (clausePrefixTree k).children u)
    (hwid : ∀ c ∈ u.formula, c.length ≤ k)
    (hvars : u.formula.vars.toFinset ⊆ u.unassigned) :
    (∀ c ∈ child.formula, c.length ≤ k) ∧ child.formula.vars.toFinset ⊆ child.unassigned := by
  dsimp only [clausePrefixTree] at hleaf hchild
  cases hpiv : pivotClause k u with
  | none => simp only [hpiv, Option.isNone_none, Bool.true_eq_false] at hleaf
  | some c =>
    simp only [hpiv, List.mem_map] at hchild
    obtain ⟨lits, _, rfl⟩ := hchild
    exact ⟨length_le_of_mem_substLits hwid, vars_substLits_subset hvars⟩

private theorem reachable_valid {k : ℕ} {s₀ u : ClauseBranchState V}
    (hreach : (clausePrefixTree k).Reachable s₀ u)
    (hwid₀ : ∀ c ∈ s₀.formula, c.length ≤ k)
    (hvars₀ : s₀.formula.vars.toFinset ⊆ s₀.unassigned) :
    (∀ c ∈ u.formula, c.length ≤ k) ∧ u.formula.vars.toFinset ⊆ u.unassigned := by
  induction hreach with
  | refl => exact ⟨hwid₀, hvars₀⟩
  | snoc _ hleaf hchild ih => exact valid_preserved hleaf hchild ih.1 ih.2

private theorem leaf_modelCountOn_eq {k : ℕ} {u : ClauseBranchState V}
    (hleaf : (clausePrefixTree k).isLeaf u = true)
    (hwid : ∀ c ∈ u.formula, c.length ≤ k)
    (hvars : u.formula.vars.toFinset ⊆ u.unassigned) :
    u.formula.modelCountOn u.unassigned =
      if [] ∈ u.formula then 0 else 2 ^ u.unassigned.card := by
  by_cases hnil : [] ∈ u.formula
  · simp only [hnil, ↓reduceIte, modelCountOn_eq_zero_of_nil_mem hnil]
  · simp only [hnil, ↓reduceIte]
    have hpiv : pivotClause k u = none := Option.isNone_iff_eq_none.mp hleaf
    simp only [pivotClause, hnil, ↓reduceIte, List.find?_eq_none] at hpiv
    have hall_taut : ∀ c ∈ u.formula, isTautClause c = true := by
      intro c hc
      by_contra hnt
      have htaut_f : isTautClause c = false := Bool.eq_false_iff.mpr hnt
      have hc_ne : c ≠ [] := fun he => hnil (he ▸ hc)
      have hdedup_ne : c.dedup ≠ [] := by
        obtain ⟨l, hl⟩ := List.exists_mem_of_ne_nil c hc_ne
        exact List.ne_nil_of_mem (List.mem_dedup.mpr hl)
      have h1 : 1 ≤ c.dedup.length := Nat.succ_le_of_lt (List.length_pos_of_ne_nil hdedup_ne)
      have hk_c : c.dedup.length ≤ k := c.dedup_sublist.length_le.trans (hwid c hc)
      have hallU : ∀ l ∈ c, l.1 ∈ u.unassigned := fun l hl =>
        hvars (List.mem_toFinset.mpr (CNF.mem_vars.mpr ⟨c, hc, l.2, hl⟩))
      apply hpiv c hc
      simp only [isPivotClause, htaut_f, Bool.not_false, Bool.true_and, Bool.and_eq_true,
        List.all_eq_true, decide_eq_true_eq]
      exact ⟨hallU, h1, hk_c⟩
    have heval_true : ∀ σ : V → Bool, u.formula.eval σ = true := fun σ =>
      (CNF.eval_eq_true_iff σ u.formula).mpr fun c hc =>
        eval_eq_true_of_isTautClause (hall_taut c hc) σ
    rw [modelCountOn, Finset.filter_true_of_mem fun σ _ => heval_true _, Finset.card_univ,
      Fintype.card_fun, Fintype.card_bool, Fintype.card_coe]

/-- **Exact model-count conservation across `clausePrefixTree k`.** On any width-`≤ k` formula `φ`
whose variables lie in `declared`, `φ.modelCountOn declared` equals the sum of leaf counts
`if [] ∈ l.formula then 0 else 2 ^ l.unassigned.card` over the leaves of `clausePrefixTree k`. -/
theorem modelCountOn_eq_sum_clausePrefixTree_leaves {k : ℕ} {φ : CNF V} {declared : Finset V}
    (hwid : ∀ c ∈ φ, c.length ≤ k) (hvars : φ.vars.toFinset ⊆ declared) :
    φ.modelCountOn declared =
      (((clausePrefixTree k).leaves { unassigned := declared, formula := φ }).map
        fun l => if [] ∈ l.formula then 0 else 2 ^ l.unassigned.card).sum := by
  let s₀ : ClauseBranchState V := { unassigned := declared, formula := φ }
  have hsum := (clausePrefixTree k).sum_leaves_eq (s := s₀)
    (w := fun u => u.formula.modelCountOn u.unassigned) fun u _ hleaf => by
      dsimp only [clausePrefixTree] at hleaf ⊢
      cases hpiv : pivotClause k u with
      | none => simp only [hpiv, Option.isNone_none, Bool.true_eq_false] at hleaf
      | some c =>
        obtain ⟨hc_mem, hpred⟩ := mem_and_isPivotClause_of_pivotClause_eq_some hpiv
        simp only [isPivotClause, Bool.and_eq_true, Bool.not_eq_true', List.all_eq_true,
          decide_eq_true_eq] at hpred
        obtain ⟨⟨htaut, hallU⟩, _, _⟩ := hpred
        have hnodup_c : (c.dedup.map Prod.fst).Nodup :=
          nodup_map_fst_dedup_of_not_isTautClause htaut
        have hpart_dedup : PartitionsModels u.formula (clausePrefixBranches c.dedup u.formula) :=
          partitionsModels_clausePrefixBranches_of_imp fun σ hφ => by
            rw [eval_dedup_clause]
            exact (CNF.eval_eq_true_iff σ u.formula).mp hφ c hc_mem
        rw [hpart_dedup.modelCountOn_eq_sum u.unassigned, clausePrefixBranches, List.map_map,
          List.map_map]
        congr 1
        refine List.map_congr_left fun lits hlits => ?_
        dsimp only [Function.comp_def]
        have hsub_fst := map_fst_sublist_of_mem_clausePrefixLitsList hlits
        have hnodup_lits : (lits.map Prod.fst).Nodup := hsub_fst.nodup hnodup_c
        have hU_lits : ∀ l ∈ lits, l.1 ∈ u.unassigned := by
          intro l hl
          obtain ⟨l', hl', heq⟩ :=
            List.mem_map.mp (hsub_fst.subset (List.mem_map_of_mem hl))
          exact heq ▸ hallU l' (List.mem_dedup.mp hl')
        exact modelCountOn_append_units_eq_substLits hnodup_lits hU_lits
  change s₀.formula.modelCountOn s₀.unassigned = _
  rw [← hsum]
  congr 1
  refine List.map_congr_left fun l hl => ?_
  have hreach := (clausePrefixTree k).reachable_of_mem_leaves hl
  have hleaf := (clausePrefixTree k).isLeaf_of_mem_leaves hl
  obtain ⟨hwid_l, hvars_l⟩ := reachable_valid hreach hwid hvars
  exact leaf_modelCountOn_eq hleaf hwid_l hvars_l

/-- **Satisfiability equivalence across `clausePrefixTree k`.** A width-`≤ k` formula `φ` with
variables in `declared` is satisfiable if and only if some leaf of `clausePrefixTree k` contains no
empty clause. -/
theorem satisfiable_iff_exists_clausePrefixTree_leaf {k : ℕ} {φ : CNF V} {declared : Finset V}
    (hwid : ∀ c ∈ φ, c.length ≤ k) (hvars : φ.vars.toFinset ⊆ declared) :
    φ.Satisfiable ↔
      ∃ l ∈ (clausePrefixTree k).leaves { unassigned := declared, formula := φ },
        [] ∉ l.formula := by
  rw [← modelCount_pos_iff]
  have hmul : φ.modelCountOn declared = 2 ^ (declared.card - φ.numVars) * φ.modelCount :=
    modelCountOn_eq_mul_modelCount φ declared hvars
  have hpos_iff : 0 < φ.modelCount ↔ 0 < φ.modelCountOn declared := by
    rw [hmul]
    have hpow : 0 < 2 ^ (declared.card - φ.numVars) := by positivity
    exact ⟨fun h => Nat.mul_pos hpow h, fun h => Nat.pos_of_mul_pos_left h⟩
  rw [hpos_iff, modelCountOn_eq_sum_clausePrefixTree_leaves hwid hvars, Nat.pos_iff_ne_zero,
    ne_eq, List.sum_eq_zero_iff]
  constructor
  · intro hne
    by_contra! hall
    apply hne
    rintro x hx
    obtain ⟨l, hl, rfl⟩ := List.mem_map.mp hx
    have hnil : [] ∈ l.formula := hall l hl
    simp only [hnil, ↓reduceIte]
  · rintro ⟨l, hl, hnil⟩ hzero
    have hx := hzero (if [] ∈ l.formula then 0 else 2 ^ l.unassigned.card)
      (List.mem_map_of_mem hl)
    simp only [hnil, ↓reduceIte] at hx
    exact (by positivity : (0 : ℕ) < 2 ^ l.unassigned.card).ne' hx

/-- **Sub-`2 ^ n` `k`-SAT branching-tree leaf bound.** For `k ≥ 1`, `clausePrefixTree k` expands any
state on `n = declared.card` unassigned variables into at most `(2 - (1 / 2) ^ k) ^ n` leaves. -/
theorem leafCount_clausePrefixTree_le {k : ℕ} (hk : 1 ≤ k) (s : ClauseBranchState V) :
    ((clausePrefixTree k).leafCount s : ℝ) ≤ (prefixBranchFactor k) ^ s.unassigned.card :=
  (clausePrefixTree k).leafCount_le_pow (one_lt_prefixBranchFactor hk).le
    (charSum_prefixSteps_le_one hk) s

/-- **Node-count bound for `clausePrefixTree k`.** For `k ≥ 1`, `clausePrefixTree k` visits at most
`(n + 1) * (2 - (1 / 2) ^ k) ^ n` total nodes on `n = s.unassigned.card` variables. -/
theorem nodeCount_clausePrefixTree_le {k : ℕ} (hk : 1 ≤ k) (s : ClauseBranchState V) :
    ((clausePrefixTree k).nodeCount s : ℝ) ≤
      (s.unassigned.card + 1 : ℝ) * (prefixBranchFactor k) ^ s.unassigned.card :=
  (clausePrefixTree k).nodeCount_le_mul_pow (one_lt_prefixBranchFactor hk).le
    (charSum_prefixSteps_le_one hk) s

/-- **Golden-ratio `2`-CNF branching-tree leaf bound.** For `k = 2`, `clausePrefixTree 2` expands
into at most `((1 + √5) / 2) ^ n` leaves (`goldenBranchFactor ^ s.unassigned.card`). -/
theorem leafCount_clausePrefixTree_two_le (s : ClauseBranchState V) :
    ((clausePrefixTree 2).leafCount s : ℝ) ≤ goldenBranchFactor ^ s.unassigned.card := by
  have hchar : charSum (prefixSteps 2) goldenBranchFactor ≤ 1 := by
    change charSum [1, 2] goldenBranchFactor ≤ 1
    exact charSum_fibonacci.le
  exact (clausePrefixTree 2).leafCount_le_pow one_lt_goldenBranchFactor.le hchar s

end Elimination

end Cslib.Logic.PL.CNF
