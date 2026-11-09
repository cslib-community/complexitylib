/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Cslib.Init
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Card
public import Mathlib.Logic.Function.Const
public import Mathlib.Order.Lattice.Nat

/-!
# Decision trees

A decision tree over Boolean variables indexed by `ι` queries a variable at each internal node
and follows the branch for its value; the leaf it reaches is the output (`DecisionTree.eval`). Its
depth is the longest structural root-to-leaf path, an upper bound on the number of queries on
any input. Repeated variables can make a longest path unreachable. The variables queried on the
way to the leaf of an input `x` determine the output: every input that agrees with `x` on them
reaches the same leaf (`DecisionTree.eval_eq_of_forall_mem_queries`) along the same path, so with
the same queries (`DecisionTree.queries_eq_of_forall_mem_queries`).

Querying every variable in turn computes any function, so over finitely many variables every
function has a decision tree of depth at most the number of variables (`exists_computes`). The
*decision tree complexity* `DecisionTree.complexity f` of `f` is the least depth of a tree computing
it [Jukna, Chapter 14][Jukna2012].

## Main definitions

* `Cslib.DecisionTree`: decision trees.
* `Cslib.DecisionTree.eval`, `Cslib.DecisionTree.depth`, `Cslib.DecisionTree.queries`.
* `Cslib.DecisionTree.mapQueries`: relabel queries without changing the tree shape.
* `Cslib.DecisionTree.map`: relabel the leaves of a decision tree.
* `Cslib.DecisionTree.complexity`: the decision tree complexity of a function.

## Main results

* `Cslib.DecisionTree.eval_eq_of_forall_mem_queries`: the queried variables certify the output.
* `Cslib.DecisionTree.queries_eq_of_forall_mem_queries`: the queried variables determine the
  queries.
* `Cslib.DecisionTree.complexity_le_card`: decision tree complexity is at most the number of
  variables.

## References

* [S. Jukna, *Boolean Function Complexity: Advances and Frontiers*][Jukna2012]
-/

@[expose] public section

namespace Cslib

/-- A decision tree over Boolean variables indexed by `ι`, with outputs in `β`: a leaf, or a query
of a variable with a subtree for each of its values. -/
inductive DecisionTree (ι : Type*) (β : Type*) where
  /-- Output `b`. -/
  | leaf (b : β)
  /-- Query variable `i`, then continue with `ifFalse` or `ifTrue`. -/
  | node (i : ι) (ifFalse ifTrue : DecisionTree ι β)

namespace DecisionTree

variable {ι β : Type*}

/-- The output of a decision tree on an input. -/
def eval : DecisionTree ι β → (ι → Bool) → β
  | leaf b, _ => b
  | node i t₀ t₁, x => cond (x i) (t₁.eval x) (t₀.eval x)

/-- The longest structural root-to-leaf path, bounding the queries executed on any input.
Repeated variables can make a longest path unreachable. -/
def depth : DecisionTree ι β → ℕ
  | leaf _ => 0
  | node _ t₀ t₁ => max t₀.depth t₁.depth + 1

/-- A decision tree computes `f` when it agrees with `f` on every input. -/
def Computes (t : DecisionTree ι β) (f : (ι → Bool) → β) : Prop :=
  ∀ x, t.eval x = f x

theorem computes_iff {t : DecisionTree ι β} {f : (ι → Bool) → β} : t.Computes f ↔ t.eval = f :=
  funext_iff.symm

@[simp] theorem eval_leaf (b : β) (x : ι → Bool) : (leaf b).eval x = b :=
  rfl

@[simp] theorem eval_node (i : ι) (t₀ t₁ : DecisionTree ι β) (x : ι → Bool) :
    (node i t₀ t₁).eval x = cond (x i) (t₁.eval x) (t₀.eval x) :=
  rfl

@[simp] theorem depth_leaf (b : β) : (leaf b : DecisionTree ι β).depth = 0 :=
  rfl

@[simp] theorem depth_node (i : ι) (t₀ t₁ : DecisionTree ι β) :
    (node i t₀ t₁).depth = max t₀.depth t₁.depth + 1 :=
  rfl

/-- Relabel the queries while preserving every branch and leaf, even when `f` is not injective. -/
def mapQueries {κ : Type*} (f : ι → κ) : DecisionTree ι β → DecisionTree κ β
  | leaf b => leaf b
  | node i left right => node (f i) (left.mapQueries f) (right.mapQueries f)

@[simp]
theorem eval_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) (x : κ → Bool) :
    (t.mapQueries f).eval x = t.eval (x ∘ f) := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, ihl, ihr]

@[simp]
theorem depth_mapQueries {κ : Type*} (f : ι → κ) (t : DecisionTree ι β) :
    (t.mapQueries f).depth = t.depth := by
  induction t with
  | leaf => rfl
  | node i left right ihl ihr => simp [mapQueries, ihl, ihr]

/-- Relabel the leaves of a decision tree. -/
def map {γ : Type*} (f : β → γ) : DecisionTree ι β → DecisionTree ι γ
  | leaf b => leaf (f b)
  | node i t₀ t₁ => node i (t₀.map f) (t₁.map f)

@[simp] theorem eval_map {γ : Type*} (f : β → γ) (t : DecisionTree ι β) (x : ι → Bool) :
    (t.map f).eval x = f (t.eval x) := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ => cases h : x i <;> simp [map, h, ih₀, ih₁]

@[simp] theorem depth_map {γ : Type*} (f : β → γ) (t : DecisionTree ι β) :
    (t.map f).depth = t.depth := by
  induction t with
  | leaf b => rfl
  | node i t₀ t₁ ih₀ ih₁ => simp [map, ih₀, ih₁]

section Queries

variable [DecidableEq ι]

/-- The variables queried on the way to the leaf of `x`. -/
def queries : DecisionTree ι β → (ι → Bool) → Finset ι
  | leaf _, _ => ∅
  | node i t₀ t₁, x => insert i (cond (x i) (t₁.queries x) (t₀.queries x))

@[simp] theorem queries_leaf (b : β) (x : ι → Bool) : (leaf b : DecisionTree ι β).queries x = ∅ :=
  rfl

@[simp] theorem queries_node (i : ι) (t₀ t₁ : DecisionTree ι β) (x : ι → Bool) :
    (node i t₀ t₁).queries x = insert i (cond (x i) (t₁.queries x) (t₀.queries x)) :=
  rfl

/-- At most `depth` variables are queried on any input. -/
theorem card_queries_le_depth (t : DecisionTree ι β) (x : ι → Bool) :
    (t.queries x).card ≤ t.depth := by
  induction t with
  | leaf => simp [queries]
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [queries, depth_node]
    refine (Finset.card_insert_le _ _).trans ?_
    cases x i
    · exact Nat.add_le_add_right (ih₀.trans (le_max_left _ _)) 1
    · exact Nat.add_le_add_right (ih₁.trans (le_max_right _ _)) 1

/-- Inputs that agree on the variables queried for `x` reach the same leaf. -/
theorem eval_eq_of_forall_mem_queries (t : DecisionTree ι β) {x y : ι → Bool}
    (h : ∀ i ∈ t.queries x, y i = x i) : t.eval y = t.eval x := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [queries, Finset.mem_insert, forall_eq_or_imp] at h
    obtain ⟨hi, h⟩ := h
    simp only [eval_node, hi]
    cases hx : x i
    · rw [hx] at h
      exact ih₀ h
    · rw [hx] at h
      exact ih₁ h

/-- Inputs that agree on the variables queried for `x` make the same queries. -/
theorem queries_eq_of_forall_mem_queries (t : DecisionTree ι β) {x y : ι → Bool}
    (h : ∀ i ∈ t.queries x, y i = x i) : t.queries y = t.queries x := by
  induction t with
  | leaf => rfl
  | node i t₀ t₁ ih₀ ih₁ =>
    simp only [queries, Finset.mem_insert, forall_eq_or_imp] at h
    obtain ⟨hi, h⟩ := h
    simp only [queries_node, hi]
    cases hx : x i
    · rw [hx] at h
      simp only [Bool.cond_false]
      rw [ih₀ h]
    · rw [hx] at h
      simp only [Bool.cond_true]
      rw [ih₁ h]

end Queries

section Complexity

section Graft

variable [DecidableEq ι]

/-- Query the variables of `l` in turn, starting from the assignment `a`, and continue with the
tree `k a'` for the assignment `a'` reached. -/
def graft : List ι → ((ι → Bool) → DecisionTree ι β) → (ι → Bool) → DecisionTree ι β
  | [], k, a => k a
  | i :: l, k, a => node i (graft l k (Function.update a i false))
      (graft l k (Function.update a i true))

@[simp] theorem graft_nil (k : (ι → Bool) → DecisionTree ι β) (a : ι → Bool) :
    graft [] k a = k a :=
  rfl

@[simp] theorem graft_cons (i : ι) (l : List ι) (k : (ι → Bool) → DecisionTree ι β)
    (a : ι → Bool) :
    graft (i :: l) k a =
      node i (graft l k (Function.update a i false)) (graft l k (Function.update a i true)) :=
  rfl

theorem eval_graft (l : List ι) (k : (ι → Bool) → DecisionTree ι β) (a x : ι → Bool) :
    (graft l k a).eval x = (k fun j => if j ∈ l then x j else a j).eval x := by
  induction l generalizing a with
  | nil => simp [graft]
  | cons i l ih =>
    have : (graft (i :: l) k a).eval x = (graft l k (Function.update a i (x i))).eval x := by
      cases hx : x i <;> simp [graft, hx]
    rw [this, ih]
    congr 2
    funext j
    by_cases hj : j ∈ l
    · simp [hj]
    · by_cases hji : j = i
      · subst hji
        simp
      · simp [hj, hji]

/-- Grafting adds at most the number of queried variables to the depth. -/
theorem depth_graft_le (l : List ι) (k : (ι → Bool) → DecisionTree ι β) (a : ι → Bool) {d : ℕ}
    (hk : ∀ b, (k b).depth ≤ d) : (graft l k a).depth ≤ l.length + d := by
  induction l generalizing a with
  | nil => simpa [graft] using hk a
  | cons i l ih =>
    simp only [graft, depth_node, List.length_cons]
    have := ih (Function.update a i false)
    have := ih (Function.update a i true)
    omega

/-- Query the variables of `l` in turn, starting from the assignment `a`, and output `f` of the
assignment reached. -/
def queryAll (f : (ι → Bool) → β) (l : List ι) (a : ι → Bool) : DecisionTree ι β :=
  graft l (fun b => leaf (f b)) a

theorem eval_queryAll (f : (ι → Bool) → β) (l : List ι) (a x : ι → Bool) :
    (queryAll f l a).eval x = f fun j => if j ∈ l then x j else a j :=
  eval_graft l _ a x

theorem depth_queryAll_le (f : (ι → Bool) → β) (l : List ι) (a : ι → Bool) :
    (queryAll f l a).depth ≤ l.length := by
  simpa [queryAll] using depth_graft_le l (fun b => leaf (f b)) a (d := 0) fun _ => le_rfl

end Graft

/-- Over finitely many variables, every function has a decision tree that queries each variable
once. -/
theorem exists_computes [Fintype ι] (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, t.Computes f ∧ t.depth ≤ Fintype.card ι := by
  classical
  exact ⟨queryAll f Finset.univ.toList fun _ => false, fun x => by simp [eval_queryAll],
    (depth_queryAll_le f _ _).trans_eq (by simp)⟩

/-- The decision tree complexity of `f`: the least depth of a decision tree computing it. It is
`0` when no decision tree computes `f`, which can only happen over infinitely many variables. -/
noncomputable def complexity (f : (ι → Bool) → β) : ℕ :=
  sInf {d | ∃ t : DecisionTree ι β, t.Computes f ∧ t.depth ≤ d}

theorem complexity_le_depth {f : (ι → Bool) → β} {t : DecisionTree ι β} (ht : t.Computes f) :
    complexity f ≤ t.depth :=
  Nat.sInf_le ⟨t, ht, le_rfl⟩

variable [Finite ι]

/-- Some decision tree computing `f` has depth exactly its decision tree complexity. -/
theorem exists_computes_depth_eq_complexity (f : (ι → Bool) → β) :
    ∃ t : DecisionTree ι β, t.Computes f ∧ t.depth = complexity f := by
  have := Fintype.ofFinite ι
  obtain ⟨t, ht, hd⟩ := exists_computes f
  obtain ⟨t', ht', hd'⟩ := Nat.sInf_mem (s := {d | ∃ t : DecisionTree ι β, t.Computes f ∧
    t.depth ≤ d}) ⟨_, t, ht, hd⟩
  exact ⟨t', ht', le_antisymm hd' (complexity_le_depth ht')⟩

theorem complexity_le_iff {f : (ι → Bool) → β} {d : ℕ} :
    complexity f ≤ d ↔ ∃ t : DecisionTree ι β, t.Computes f ∧ t.depth ≤ d := by
  refine ⟨fun h => ?_, fun ⟨t, ht, hd⟩ => (complexity_le_depth ht).trans hd⟩
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact ⟨t, ht, hd.trans_le h⟩

/-- Lower bounds on decision tree complexity are lower bounds on the depth of every tree. -/
theorem le_complexity_iff {f : (ι → Bool) → β} {d : ℕ} :
    d ≤ complexity f ↔ ∀ t : DecisionTree ι β, t.Computes f → d ≤ t.depth := by
  refine ⟨fun h t ht => h.trans (complexity_le_depth ht), fun h => ?_⟩
  obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
  exact (h t ht).trans hd.le

/-- A function has decision tree complexity zero exactly when it is constant. -/
theorem complexity_eq_zero_iff {f : (ι → Bool) → β} : complexity f = 0 ↔ Function.IsConst f := by
  constructor
  · intro h
    obtain ⟨t, ht, hd⟩ := exists_computes_depth_eq_complexity f
    cases t with
    | leaf b => exact fun x y => (ht x).symm.trans (ht y)
    | node i t₀ t₁ => simp [h] at hd
  · intro h
    exact Nat.le_zero.1 (complexity_le_depth (t := leaf (f fun _ => false))
      fun x => h (fun _ => false) x)

omit [Finite ι] in
/-- Decision tree complexity is at most the number of variables. -/
theorem complexity_le_card [Fintype ι] (f : (ι → Bool) → β) : complexity f ≤ Fintype.card ι := by
  obtain ⟨t, ht, hd⟩ := exists_computes f
  exact (complexity_le_depth ht).trans hd

end Complexity

end DecisionTree

end Cslib
