/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Init
public import Complexity.Algorithms.Lean.SearchTree.Cost
public import Complexity.Foundations.Data.OrderedSet

/-!
# Self-Adjusting Splay Trees

This module formalizes annotation-free bottom-up splay trees over Mathlib's `BinaryTree α`,
reusing the finite-set abstraction `Cslib.Algorithms.Lean.SearchTree.elements` and strict
binary-search-tree invariant `Cslib.Algorithms.Lean.SearchTree.Ordered` ([SleatorTarjan1985b],
Sections 2–3, pp. 654–662).

Unlike height- or weight-balanced search trees, splay nodes store no auxiliary balance metadata.
Each operation descends a search path, saves the ancestor chain in an explicit stack (`Frame`),
and restructures the tree bottom-up from the target node (or the last non-empty node visited on an
unsuccessful search) to the root using `zig` (single terminal rotation at the root), `zig-zig`
(parent-grandparent rotation followed by node-parent rotation), and `zig-zag` (double rotation)
steps ([SleatorTarjan1985b], Section 2, pp. 655–656, Figure 3; Section 3, pp. 660–661, Figure 6;
Section 4, p. 665).

## Design notes and cost conventions

* **Set-idempotent updates**: Sleator and Tarjan ([SleatorTarjan1985b], Section 3, p. 661) specify
  `insert(i, t)` under the precondition `i ∉ t` and `delete(i, t)` under `i ∈ t`. To realize
  `Cslib.OrderedSet.spec α` directly, `insert` and `erase` are total and set-idempotent: inserting
  a present key splays that key to the root without duplicating it, and erasing an absent key
  splays the last visited node along the failed search path while leaving `elements` unchanged.
* **Rotation counts vs. node visits**: Each `SplayResult`, `SplitResult`, and `QueryResult`
  records the exact number of binary-tree edge rotations executed (`0` on `.nil` or when the
  target is already at the root, `1` for `zig`, and `2` per `zig-zig` or `zig-zag` step). On any
  non-empty tree, `(splay x t).rotations + 1 = SearchTree.searchVisits x t` and
  `(splayMin t).rotations + 1 = SearchTree.minimumVisits t`. Ancestor-stack allocation, tree-node
  allocation, and key-comparison costs are not charged separately.

## Main definitions

* `SplayResult`, `SplitResult`, `QueryResult`: named output records bundling restructured trees,
  query answers, and exact edge-rotation counts.
* `Frame`, `plug`, `Focus`, `splayUp`: upward ancestor zipper and bottom-up splaying loop.
* `splay`, `splayMin`, `splayMax`: splay at a searched key (or last visited node), leftmost key,
  or rightmost key.
* `contains`, `split`, `join`, `insert`, `erase`, `minimum`, `successor`: self-adjusting
  dictionary and split/join operations.

## Main results

* `elements_splay`, `ordered_splay`, `rootKey_splay_of_mem`, `splay_split_lt`, `splay_split_ge`:
  `splay` preserves `elements` and `Ordered`, moves present keys to the root, and partitions keys
  across the splayed root when `x` is absent.
* `rotations_splay_add_one_eq_searchVisits`, `rotations_splayMin_add_one_eq_minimumVisits`: exact
  correspondence between rotation counts and `SearchTree` downward path visits.
* `contains_answer_eq`, `elements_split_left`, `elements_split_right`, `elements_join`,
  `ordered_join`, `elements_insert`, `ordered_insert`, `elements_erase`, `ordered_erase`,
  `minimum_spec`, `successor_spec`: semantic correctness and `Ordered` preservation for all
  operations.

## References

* [SleatorTarjan1985b] Daniel Dominic Sleator and Robert Endre Tarjan,
  *Self-Adjusting Binary Search Trees*, Journal of the ACM 32(3), Sections 2–4, pp. 654–667, 1985.
-/

public section

namespace Cslib.Algorithms.Lean.SplayTree

open Cslib.OrderedSet
open Cslib.Algorithms.Lean.SearchTree (elements Ordered mem_elements_node
  searchVisits minimumVisits)

section Shape

variable {α β : Type*}

/-- Key stored at the root of a `BinaryTree α`, or `none` if empty. -/
@[expose] def rootKey : BinaryTree α → Option α
  | .nil => none
  | .node a _ _ => some a

@[simp] theorem rootKey_nil : rootKey (.nil : BinaryTree α) = none := rfl

@[simp] theorem rootKey_node (a : α) (l r : BinaryTree α) :
    rootKey (.node a l r) = some a := rfl

/-- Output of a tree-restructuring splay or update operation (`splay`, `splayMin`, `splayMax`,
`join`, `insert`, `erase`). -/
@[ext]
structure SplayResult (α : Type*) where
  /-- Restructured binary search tree. -/
  tree : BinaryTree α
  /-- Exact number of edge rotations executed (`0` if empty or already at the root). -/
  rotations : ℕ
  deriving DecidableEq, Repr

/-- Output of `split`: left tree (`≤ x`), right tree (`> x`), and edge-rotation count. -/
@[ext]
structure SplitResult (α : Type*) where
  /-- Subtree containing all keys `≤ x`. -/
  left : BinaryTree α
  /-- Subtree containing all keys `> x`. -/
  right : BinaryTree α
  /-- Exact number of edge rotations executed during `split`. -/
  rotations : ℕ
  deriving DecidableEq, Repr

/-- Output of a self-adjusting query (`contains`, `minimum`, `successor`). -/
@[ext]
structure QueryResult (α : Type*) (β : Type*) where
  /-- Query answer. -/
  answer : β
  /-- Restructured binary search tree after splaying. -/
  tree : BinaryTree α
  /-- Exact number of edge rotations executed. -/
  rotations : ℕ
  deriving DecidableEq, Repr

/-- One ancestor frame along a downward search path in a `BinaryTree α`. -/
inductive Frame (α : Type*) : Type _
  /-- Current subtree is the left child of `node key · rightSub`. -/
  | left (key : α) (rightSub : BinaryTree α)
  /-- Current subtree is the right child of `node key leftSub ·`. -/
  | right (leftSub : BinaryTree α) (key : α)
  deriving DecidableEq, Repr

/-- Reconstruct a `BinaryTree α` by plugging `t` upward through an ancestor stack `ctx`
(ordered from parent to original root). -/
@[expose] def plug (t : BinaryTree α) : List (Frame α) → BinaryTree α
  | [] => t
  | .left p r :: ctx => plug (.node p t r) ctx
  | .right l p :: ctx => plug (.node p l t) ctx

@[simp] theorem plug_nil (t : BinaryTree α) : plug t [] = t := rfl

@[simp] theorem plug_left (t : BinaryTree α) (p : α) (r : BinaryTree α) (ctx : List (Frame α)) :
    plug t (.left p r :: ctx) = plug (.node p t r) ctx := rfl

@[simp] theorem plug_right (t : BinaryTree α) (l : BinaryTree α) (p : α) (ctx : List (Frame α)) :
    plug t (.right l p :: ctx) = plug (.node p l t) ctx := rfl

@[simp] theorem plug_append (t : BinaryTree α) (ctx₁ ctx₂ : List (Frame α)) :
    plug t (ctx₁ ++ ctx₂) = plug (plug t ctx₁) ctx₂ := by
  induction ctx₁ generalizing t with
  | nil => rfl
  | cons f ctx₁ ih =>
    cases f <;> exact ih _

theorem plug_ne_nil_of_ne_nil {t : BinaryTree α} (ht : t ≠ .nil) (ctx : List (Frame α)) :
    plug t ctx ≠ .nil := by
  induction ctx generalizing t with
  | nil => exact ht
  | cons f ctx ih =>
    cases f <;> exact ih (by simp)

/-- Focused non-empty node `.node key leftSub rightSub` together with its upward ancestor stack. -/
structure Focus (α : Type*) where
  /-- Key at the focused node. -/
  key : α
  /-- Left subtree of the focused node. -/
  leftSub : BinaryTree α
  /-- Right subtree of the focused node. -/
  rightSub : BinaryTree α
  /-- Ancestor stack from parent to root. -/
  ctx : List (Frame α)
  deriving DecidableEq, Repr

/-- The subtree rooted at the focused node, ignoring its ancestors. -/
@[expose] def Focus.sub (f : Focus α) : BinaryTree α :=
  .node f.key f.leftSub f.rightSub

/-- Reconstruct the full tree represented by `f`. -/
@[expose] def Focus.toTree (f : Focus α) : BinaryTree α :=
  plug f.sub f.ctx

/-- Bottom-up splaying loop ([SleatorTarjan1985b], Section 2, pp. 655–656, Figure 3):
rotates the focused node `(x, l, r)` to the root through its upward ancestor stack `ctx` via
`zig-zig` and `zig-zag` pairs and at most one terminal `zig` step. -/
@[expose] def splayUp (x : α) (l r : BinaryTree α) : List (Frame α) → SplayResult α
  | [] => ⟨.node x l r, 0⟩
  | [.left p c] => ⟨.node x l (.node p r c), 1⟩
  | [.right c p] => ⟨.node x (.node p c l) r, 1⟩
  | .left p c :: .left g d :: ctx =>
      let res := splayUp x l (.node p r (.node g c d)) ctx
      ⟨res.tree, res.rotations + 2⟩
  | .right c p :: .right d g :: ctx =>
      let res := splayUp x (.node p (.node g d c) l) r ctx
      ⟨res.tree, res.rotations + 2⟩
  | .right a p :: .left g d :: ctx =>
      let res := splayUp x (.node p a l) (.node g r d) ctx
      ⟨res.tree, res.rotations + 2⟩
  | .left p c :: .right d g :: ctx =>
      let res := splayUp x (.node g d l) (.node p r c) ctx
      ⟨res.tree, res.rotations + 2⟩

/-- Bottom-up splaying performs exactly one edge rotation per ancestor in `ctx`. -/
@[simp] theorem rotations_splayUp (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    (splayUp x l r ctx).rotations = ctx.length := by
  induction l, r, ctx using splayUp.induct x with
  | case1 => rfl
  | case2 => rfl
  | case3 => rfl
  | case4 l r p c g d ctx ih => simp [splayUp, ih]
  | case5 l r c p d g ctx ih => simp [splayUp, ih]
  | case6 l r a p g d ctx ih => simp [splayUp, ih]
  | case7 l r p c d g ctx ih => simp [splayUp, ih]

/-- `splayUp x l r ctx` always roots the resulting tree at `x`. -/
theorem exists_node_splayUp (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    ∃ l' r', (splayUp x l r ctx).tree = .node x l' r' := by
  induction l, r, ctx using splayUp.induct x with
  | case1 => exact ⟨_, _, rfl⟩
  | case2 => exact ⟨_, _, rfl⟩
  | case3 => exact ⟨_, _, rfl⟩
  | case4 _ _ _ _ _ _ _ ih => simpa only [splayUp] using ih
  | case5 _ _ _ _ _ _ _ ih => simpa only [splayUp] using ih
  | case6 _ _ _ _ _ _ _ ih => simpa only [splayUp] using ih
  | case7 _ _ _ _ _ _ _ ih => simpa only [splayUp] using ih

@[simp] theorem rootKey_splayUp (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    rootKey (splayUp x l r ctx).tree = some x := by
  obtain ⟨l', r', h⟩ := exists_node_splayUp x l r ctx
  simp [h]

theorem tree_splayUp_ne_nil (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    (splayUp x l r ctx).tree ≠ .nil := by
  obtain ⟨l', r', h⟩ := exists_node_splayUp x l r ctx
  simp [h]

/-- Focus on the leftmost node of `t`, accumulating upward left-child frames onto `ctx`. -/
@[expose] def focusMin : BinaryTree α → List (Frame α) → Option (Focus α)
  | .nil, _ => none
  | .node a l r, ctx => (focusMin l (.left a r :: ctx)).or (some ⟨a, l, r, ctx⟩)

/-- Focus on the rightmost node of `t`, accumulating upward right-child frames onto `ctx`. -/
@[expose] def focusMax : BinaryTree α → List (Frame α) → Option (Focus α)
  | .nil, _ => none
  | .node a l r, ctx => (focusMax r (.right l a :: ctx)).or (some ⟨a, l, r, ctx⟩)

@[simp] theorem focusMin_eq_none_iff (t : BinaryTree α) (ctx : List (Frame α)) :
    focusMin t ctx = none ↔ t = .nil := by
  cases t with
  | nil => simp [focusMin]
  | node a l r =>
    simp only [focusMin, reduceCtorEq, iff_false]
    cases focusMin l (.left a r :: ctx) <;> simp

@[simp] theorem focusMax_eq_none_iff (t : BinaryTree α) (ctx : List (Frame α)) :
    focusMax t ctx = none ↔ t = .nil := by
  cases t with
  | nil => simp [focusMax]
  | node a l r =>
    simp only [focusMax, reduceCtorEq, iff_false]
    cases focusMax r (.right l a :: ctx) <;> simp

theorem focusMin_spec {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (hf : focusMin t ctx = some f) :
    f.toTree = plug t ctx ∧ f.leftSub = .nil := by
  induction t generalizing ctx with
  | nil => simp [focusMin] at hf
  | node a l r ihl _ =>
    simp only [focusMin] at hf
    cases hl : focusMin l (.left a r :: ctx) with
    | none =>
      have hnil : l = .nil := (focusMin_eq_none_iff l _).mp hl
      subst hnil
      simp only [hl, Option.none_or, Option.some.injEq] at hf
      subst hf
      exact ⟨rfl, rfl⟩
    | some f' =>
      simp only [hl, Option.some_or, Option.some.injEq] at hf
      subst hf
      exact ihl hl

theorem focusMax_spec {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (hf : focusMax t ctx = some f) :
    f.toTree = plug t ctx ∧ f.rightSub = .nil := by
  induction t generalizing ctx with
  | nil => simp [focusMax] at hf
  | node a l r _ ihr =>
    simp only [focusMax] at hf
    cases hr : focusMax r (.right l a :: ctx) with
    | none =>
      have hnil : r = .nil := (focusMax_eq_none_iff r _).mp hr
      subst hnil
      simp only [hr, Option.none_or, Option.some.injEq] at hf
      subst hf
      exact ⟨rfl, rfl⟩
    | some f' =>
      simp only [hr, Option.some_or, Option.some.injEq] at hf
      subst hf
      exact ihr hr

/-- Splay the leftmost (minimum) node of `t` to the root. -/
@[expose] def splayMin (t : BinaryTree α) : SplayResult α :=
  match focusMin t [] with
  | none => ⟨.nil, 0⟩
  | some f => splayUp f.key f.leftSub f.rightSub f.ctx

/-- Splay the rightmost (maximum) node of `t` to the root. -/
@[expose] def splayMax (t : BinaryTree α) : SplayResult α :=
  match focusMax t [] with
  | none => ⟨.nil, 0⟩
  | some f => splayUp f.key f.leftSub f.rightSub f.ctx

@[simp] theorem splayMin_nil : splayMin (.nil : BinaryTree α) = ⟨.nil, 0⟩ := rfl

@[simp] theorem splayMax_nil : splayMax (.nil : BinaryTree α) = ⟨.nil, 0⟩ := rfl

@[simp] theorem tree_splayMin_eq_nil_iff (t : BinaryTree α) :
    (splayMin t).tree = .nil ↔ t = .nil := by
  simp only [splayMin]
  cases hf : focusMin t [] with
  | none => simp [(focusMin_eq_none_iff t []).mp hf]
  | some f =>
    have hne : t ≠ .nil := by intro h; subst h; simp [focusMin] at hf
    simp [tree_splayUp_ne_nil, hne]

@[simp] theorem tree_splayMax_eq_nil_iff (t : BinaryTree α) :
    (splayMax t).tree = .nil ↔ t = .nil := by
  simp only [splayMax]
  cases hf : focusMax t [] with
  | none => simp [(focusMax_eq_none_iff t []).mp hf]
  | some f =>
    have hne : t ≠ .nil := by intro h; subst h; simp [focusMax] at hf
    simp [tree_splayUp_ne_nil, hne]

/-- Predicate asserting that every ancestor frame in `ctx` is a left-child frame. -/
private def AllLeft : List (Frame α) → Prop
  | [] => True
  | .left _ _ :: ctx => AllLeft ctx
  | .right _ _ :: _ => False

private theorem allLeft_focusMin {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (hctx : AllLeft ctx) (hf : focusMin t ctx = some f) : AllLeft f.ctx := by
  induction t generalizing ctx with
  | nil => simp [focusMin] at hf
  | node a l r ihl _ =>
    simp only [focusMin] at hf
    cases hl : focusMin l (.left a r :: ctx) with
    | none =>
      simp only [hl, Option.none_or, Option.some.injEq] at hf
      subst hf
      exact hctx
    | some f' =>
      simp only [hl, Option.some_or, Option.some.injEq] at hf
      subst hf
      exact ihl (show AllLeft (.left a r :: ctx) from hctx) hl

private theorem left_nil_splayUp (x : α) (r : BinaryTree α) :
    ∀ ctx : List (Frame α), AllLeft ctx →
      ∃ r', (splayUp x .nil r ctx).tree = .node x .nil r'
  | [], _ => ⟨r, rfl⟩
  | [.left p c], _ => ⟨.node p r c, rfl⟩
  | [.right _ _], h => h.elim
  | .right _ _ :: _ :: _, h => h.elim
  | .left _ _ :: .right _ _ :: _, h => h.elim
  | .left p c :: .left g d :: ctx, h =>
      left_nil_splayUp x (.node p r (.node g c d)) ctx h

/-- On any non-empty tree `t`, `(splayMin t).tree` has `.nil` as its left child. -/
theorem exists_node_nil_left_splayMin {t : BinaryTree α} (ht : t ≠ .nil) :
    ∃ m r, (splayMin t).tree = .node m .nil r := by
  simp only [splayMin]
  cases hf : focusMin t [] with
  | none => exact (ht ((focusMin_eq_none_iff t []).mp hf)).elim
  | some f =>
    simp only
    have hleft := (focusMin_spec hf).2
    have hall := allLeft_focusMin (ctx := []) trivial hf
    rw [hleft]
    obtain ⟨r', hr'⟩ := left_nil_splayUp f.key f.rightSub f.ctx hall
    exact ⟨f.key, r', hr'⟩

private def AllRight : List (Frame α) → Prop
  | [] => True
  | .left _ _ :: _ => False
  | .right _ _ :: ctx => AllRight ctx

private theorem allRight_focusMax {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (hctx : AllRight ctx) (hf : focusMax t ctx = some f) : AllRight f.ctx := by
  induction t generalizing ctx with
  | nil => simp [focusMax] at hf
  | node a l r _ ihr =>
    simp only [focusMax] at hf
    cases hr : focusMax r (.right l a :: ctx) with
    | none =>
      simp only [hr, Option.none_or, Option.some.injEq] at hf
      subst hf
      exact hctx
    | some f' =>
      simp only [hr, Option.some_or, Option.some.injEq] at hf
      subst hf
      exact ihr (show AllRight (.right l a :: ctx) from hctx) hr

private theorem right_nil_splayUp (x : α) (l : BinaryTree α) :
    ∀ ctx : List (Frame α), AllRight ctx →
      ∃ l', (splayUp x l .nil ctx).tree = .node x l' .nil
  | [], _ => ⟨l, rfl⟩
  | [.right c p], _ => ⟨.node p c l, rfl⟩
  | [.left _ _], h => h.elim
  | .left _ _ :: _ :: _, h => h.elim
  | .right _ _ :: .left _ _ :: _, h => h.elim
  | .right c p :: .right d g :: ctx, h =>
      right_nil_splayUp x (.node p (.node g d c) l) ctx h

/-- On any non-empty tree `t`, `(splayMax t).tree` has `.nil` as its right child. -/
theorem exists_node_nil_right_splayMax {t : BinaryTree α} (ht : t ≠ .nil) :
    ∃ m l, (splayMax t).tree = .node m l .nil := by
  simp only [splayMax]
  cases hf : focusMax t [] with
  | none => exact (ht ((focusMax_eq_none_iff t []).mp hf)).elim
  | some f =>
    simp only
    have hright := (focusMax_spec hf).2
    have hall := allRight_focusMax (ctx := []) trivial hf
    rw [hright]
    obtain ⟨l', hl'⟩ := right_nil_splayUp f.key f.leftSub f.ctx hall
    exact ⟨f.key, l', hl'⟩

end Shape

section Ordered

variable {α : Type*} [LinearOrder α]

@[simp] private theorem elements_nil_eq : elements (.nil : BinaryTree α) = ∅ := rfl

omit [LinearOrder α] in
theorem focusMin_ctx_length {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (hf : focusMin t ctx = some f) :
    f.ctx.length + 1 = ctx.length + minimumVisits t := by
  induction t generalizing ctx with
  | nil => simp [focusMin] at hf
  | node a l r ihl _ =>
    simp only [focusMin] at hf
    cases hl : focusMin l (.left a r :: ctx) with
    | none =>
      have hnil : l = .nil := (focusMin_eq_none_iff l _).mp hl
      subst hnil
      simp only [hl, Option.none_or, Option.some.injEq] at hf
      subst hf
      simp [minimumVisits]
    | some f' =>
      simp only [hl, Option.some_or, Option.some.injEq] at hf
      subst hf
      have hlen := ihl hl
      simp only [List.length_cons, minimumVisits] at hlen ⊢
      omega

theorem elements_plug_congr {t₁ t₂ : BinaryTree α} (ctx : List (Frame α))
    (he : elements t₁ = elements t₂) :
    elements (plug t₁ ctx) = elements (plug t₂ ctx) := by
  induction ctx generalizing t₁ t₂ with
  | nil => exact he
  | cons f ctx ih =>
    cases f with
    | left p r => exact ih (by simp [elements, he])
    | right l p => exact ih (by simp [elements, he])

theorem ordered_of_ordered_plug {t : BinaryTree α} {ctx : List (Frame α)}
    (h : Ordered (plug t ctx)) : Ordered t := by
  induction ctx generalizing t with
  | nil => exact h
  | cons f ctx ih =>
    cases f with
    | left p r => exact (ih h).1
    | right l p => exact (ih h).2.1

theorem ordered_plug_congr {t₁ t₂ : BinaryTree α} (ctx : List (Frame α))
    (he : elements t₁ = elements t₂) (ho : Ordered t₁ → Ordered t₂)
    (h : Ordered (plug t₁ ctx)) : Ordered (plug t₂ ctx) := by
  induction ctx generalizing t₁ t₂ with
  | nil => exact ho h
  | cons f ctx ih =>
    cases f with
    | left p r =>
      refine ih (by simp [elements, he]) ?_ h
      rintro ⟨ht₁, hr, hlt, hgt⟩
      exact ⟨ho ht₁, hr, he ▸ hlt, hgt⟩
    | right l p =>
      refine ih (by simp [elements, he]) ?_ h
      rintro ⟨hl, ht₁, hlt, hgt⟩
      exact ⟨hl, ho ht₁, hlt, he ▸ hgt⟩

/-- Every rotation step in `splayUp` preserves the represented finite set of keys. -/
theorem elements_splayUp (x : α) (l r : BinaryTree α) (ctx : List (Frame α)) :
    elements (splayUp x l r ctx).tree = elements (plug (.node x l r) ctx) := by
  induction l, r, ctx using splayUp.induct x with
  | case1 => rfl
  | case2 l r p c =>
    ext y
    simp only [splayUp, plug, mem_elements_node]
    tauto
  | case3 l r c p =>
    ext y
    simp only [splayUp, plug, mem_elements_node]
    tauto
  | case4 l r p c g d ctx ih =>
    simp only [splayUp, plug_left]
    rw [ih]
    apply elements_plug_congr
    ext y
    simp only [mem_elements_node]
    tauto
  | case5 l r c p d g ctx ih =>
    simp only [splayUp, plug_right]
    rw [ih]
    apply elements_plug_congr
    ext y
    simp only [mem_elements_node]
    tauto
  | case6 l r a p g d ctx ih =>
    simp only [splayUp, plug_right, plug_left]
    rw [ih]
    apply elements_plug_congr
    ext y
    simp only [mem_elements_node]
    tauto
  | case7 l r p c d g ctx ih =>
    simp only [splayUp, plug_left, plug_right]
    rw [ih]
    apply elements_plug_congr
    ext y
    simp only [mem_elements_node]
    tauto

private theorem ordered_zig_left {x p : α} {a b c : BinaryTree α}
    (h : Ordered (.node p (.node x a b) c)) :
    Ordered (.node x a (.node p b c)) := by
  obtain ⟨⟨ha, hb, hax, hxb⟩, hc, hxp, hpc⟩ := h
  have hxp' : x < p := hxp x (by simp)
  refine ⟨ha, ⟨hb, hc, fun y hy => hxp y (by simp [hy]), hpc⟩, hax, ?_⟩
  intro y hy
  rcases mem_elements_node.mp hy with rfl | hy | hy
  · exact hxp'
  · exact hxb y hy
  · exact lt_trans hxp' (hpc y hy)

private theorem ordered_zig_right {x p : α} {a b c : BinaryTree α}
    (h : Ordered (.node p a (.node x b c))) :
    Ordered (.node x (.node p a b) c) := by
  obtain ⟨ha, ⟨hb, hc, hbx, hxc⟩, hap, hpx⟩ := h
  have hpx' : p < x := hpx x (by simp)
  refine ⟨⟨ha, hb, hap, fun y hy => hpx y (by simp [hy])⟩, hc, ?_, hxc⟩
  intro y hy
  rcases mem_elements_node.mp hy with rfl | hy | hy
  · exact hpx'
  · exact lt_trans (hap y hy) hpx'
  · exact hbx y hy

private theorem ordered_zig_zig_left {x p g : α} {a b c d : BinaryTree α}
    (h : Ordered (.node g (.node p (.node x a b) c) d)) :
    Ordered (.node x a (.node p b (.node g c d))) :=
  ordered_zig_left (ordered_zig_left h)

private theorem ordered_zig_zig_right {x p g : α} {a b c d : BinaryTree α}
    (h : Ordered (.node g d (.node p c (.node x a b)))) :
    Ordered (.node x (.node p (.node g d c) a) b) :=
  ordered_zig_right (ordered_zig_right h)

private theorem ordered_zig_zag_lr {x p g : α} {a b c d : BinaryTree α}
    (h : Ordered (.node g (.node p a (.node x b c)) d)) :
    Ordered (.node x (.node p a b) (.node g c d)) := by
  obtain ⟨hp, hd, hpg, hgd⟩ := h
  have hrot : Ordered (.node g (.node x (.node p a b) c) d) :=
    ⟨ordered_zig_right hp, hd, fun y hy => hpg y (by
      simp only [mem_elements_node] at hy ⊢; tauto), hgd⟩
  exact ordered_zig_left hrot

private theorem ordered_zig_zag_rl {x p g : α} {a b c d : BinaryTree α}
    (h : Ordered (.node g d (.node p (.node x a b) c))) :
    Ordered (.node x (.node g d a) (.node p b c)) := by
  obtain ⟨hd, hp, hdg, hgp⟩ := h
  have hrot : Ordered (.node g d (.node x a (.node p b c))) :=
    ⟨hd, ordered_zig_left hp, hdg, fun y hy => hgp y (by
      simp only [mem_elements_node] at hy ⊢; tauto)⟩
  exact ordered_zig_right hrot

/-- `splayUp` preserves `Ordered` whenever the reconstructed initial tree is `Ordered`. -/
theorem ordered_splayUp {x : α} {l r : BinaryTree α} {ctx : List (Frame α)}
    (h : Ordered (plug (.node x l r) ctx)) :
    Ordered (splayUp x l r ctx).tree := by
  induction l, r, ctx using splayUp.induct x with
  | case1 => exact h
  | case2 => exact ordered_zig_left h
  | case3 => exact ordered_zig_right h
  | case4 l r p c g d ctx ih =>
    apply ih
    refine ordered_plug_congr ctx ?_ ordered_zig_zig_left h
    ext y; simp only [mem_elements_node]; tauto
  | case5 l r c p d g ctx ih =>
    apply ih
    refine ordered_plug_congr ctx ?_ ordered_zig_zig_right h
    ext y; simp only [mem_elements_node]; tauto
  | case6 l r a p g d ctx ih =>
    apply ih
    refine ordered_plug_congr ctx ?_ ordered_zig_zag_lr h
    ext y; simp only [mem_elements_node]; tauto
  | case7 l r p c d g ctx ih =>
    apply ih
    refine ordered_plug_congr ctx ?_ ordered_zig_zag_rl h
    ext y; simp only [mem_elements_node]; tauto

/-- Descend the search path for `x` in `t`, returning the node containing `x` if present or the
last non-empty node visited before an empty child ([SleatorTarjan1985b], Section 3, pp. 660–661,
Figure 6). -/
@[expose] def focusSearch (x : α) : BinaryTree α → List (Frame α) → Option (Focus α)
  | .nil, _ => none
  | .node a l r, ctx =>
      if x < a then
        (focusSearch x l (.left a r :: ctx)).or (some ⟨a, l, r, ctx⟩)
      else if a < x then
        (focusSearch x r (.right l a :: ctx)).or (some ⟨a, l, r, ctx⟩)
      else
        some ⟨a, l, r, ctx⟩

@[simp] theorem focusSearch_eq_none_iff (x : α) (t : BinaryTree α) (ctx : List (Frame α)) :
    focusSearch x t ctx = none ↔ t = .nil := by
  cases t with
  | nil => simp [focusSearch]
  | node a l r =>
    simp only [focusSearch, reduceCtorEq, iff_false]
    split
    · cases focusSearch x l (.left a r :: ctx) <;> simp
    · split
      · cases focusSearch x r (.right l a :: ctx) <;> simp
      · simp

theorem focusSearch_toTree_and_length {x : α} {t : BinaryTree α} {ctx : List (Frame α)}
    {f : Focus α} (hf : focusSearch x t ctx = some f) :
    f.toTree = plug t ctx ∧ f.ctx.length + 1 = ctx.length + searchVisits x t := by
  induction t generalizing ctx with
  | nil => simp [focusSearch] at hf
  | node a l r ihl ihr =>
    simp only [focusSearch] at hf
    split at hf <;> rename_i hxa
    · cases hl : focusSearch x l (.left a r :: ctx) with
      | none =>
        have hlnil : l = .nil := (focusSearch_eq_none_iff x l _).mp hl
        subst hlnil
        simp only [hl, Option.none_or, Option.some.injEq] at hf
        subst hf
        simp [Focus.toTree, Focus.sub, searchVisits, hxa]
      | some f' =>
        simp only [hl, Option.some_or, Option.some.injEq] at hf
        subst hf
        obtain ⟨htree, hlen⟩ := ihl hl
        refine ⟨htree, ?_⟩
        simp only [List.length_cons, searchVisits, hxa, ↓reduceIte] at hlen ⊢
        omega
    · split at hf <;> rename_i hax
      · cases hr : focusSearch x r (.right l a :: ctx) with
        | none =>
          have hrnil : r = .nil := (focusSearch_eq_none_iff x r _).mp hr
          subst hrnil
          simp only [hr, Option.none_or, Option.some.injEq] at hf
          subst hf
          simp [Focus.toTree, Focus.sub, searchVisits, hxa, hax]
        | some f' =>
          simp only [hr, Option.some_or, Option.some.injEq] at hf
          subst hf
          obtain ⟨htree, hlen⟩ := ihr hr
          refine ⟨htree, ?_⟩
          simp only [List.length_cons, searchVisits, hxa, hax, ↓reduceIte] at hlen ⊢
          omega
      · simp only [Option.some.injEq] at hf
        subst hf
        simp [Focus.toTree, Focus.sub, searchVisits, hxa, hax]

/-- Key separation invariant of `focusSearch`: in an `Ordered` tree `t`, `f.key ∈ elements t`,
`f.key = x` whenever `x ∈ elements t`, and no key of `t` lies strictly between `x` and `f.key`. -/
theorem focusSearch_ordered_spec {x : α} {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (ht : Ordered t) (hf : focusSearch x t ctx = some f) :
    f.key ∈ elements t ∧
      (x ∈ elements t → f.key = x) ∧
      (∀ y ∈ elements t, ¬ (x < y ∧ y < f.key) ∧ ¬ (f.key < y ∧ y < x)) := by
  induction t generalizing ctx with
  | nil => simp [focusSearch] at hf
  | node a l r ihl ihr =>
    obtain ⟨hl, hr, hla, har⟩ := ht
    simp only [focusSearch] at hf
    split at hf <;> rename_i hxa
    · cases hfl : focusSearch x l (.left a r :: ctx) with
      | none =>
        have hlnil : l = .nil := (focusSearch_eq_none_iff x l _).mp hfl
        subst hlnil
        simp only [hfl, Option.none_or, Option.some.injEq] at hf
        subst hf
        refine ⟨by simp, ?_, ?_⟩
        · intro hx
          rcases mem_elements_node.mp hx with rfl | hx | hx
          · exact (lt_irrefl x hxa).elim
          · simp [elements] at hx
          · exact (lt_asymm hxa (har x hx)).elim
        · intro y hy
          rcases mem_elements_node.mp hy with rfl | hy | hy
          · exact ⟨fun h => lt_irrefl y h.2, fun h => lt_irrefl y h.1⟩
          · simp [elements] at hy
          · have hay := har y hy
            exact ⟨fun h => lt_asymm hay h.2, fun h => lt_asymm hxa (lt_trans hay h.2)⟩
      | some f' =>
        simp only [hfl, Option.some_or, Option.some.injEq] at hf
        subst hf
        obtain ⟨hmem, hxeq, hbet⟩ := ihl hl hfl
        have hfk_lt_a : f'.key < a := hla f'.key hmem
        refine ⟨by simp [hmem], ?_, ?_⟩
        · intro hx
          rcases mem_elements_node.mp hx with rfl | hx | hx
          · exact (lt_irrefl x hxa).elim
          · exact hxeq hx
          · exact (lt_asymm hxa (har x hx)).elim
        · intro y hy
          rcases mem_elements_node.mp hy with rfl | hy | hy
          · exact ⟨fun h => lt_asymm hfk_lt_a h.2, fun h => lt_asymm hxa h.2⟩
          · exact hbet y hy
          · have hay := har y hy
            exact ⟨fun h => lt_asymm (lt_trans hfk_lt_a hay) h.2,
              fun h => lt_asymm hxa (lt_trans hay h.2)⟩
    · split at hf <;> rename_i hax
      · cases hfr : focusSearch x r (.right l a :: ctx) with
        | none =>
          have hrnil : r = .nil := (focusSearch_eq_none_iff x r _).mp hfr
          subst hrnil
          simp only [hfr, Option.none_or, Option.some.injEq] at hf
          subst hf
          refine ⟨by simp, ?_, ?_⟩
          · intro hx
            rcases mem_elements_node.mp hx with rfl | hx | hx
            · exact (lt_irrefl x hax).elim
            · exact (lt_asymm hax (hla x hx)).elim
            · simp [elements] at hx
          · intro y hy
            rcases mem_elements_node.mp hy with rfl | hy | hy
            · exact ⟨fun h => lt_irrefl y h.2, fun h => lt_irrefl y h.1⟩
            · have hya := hla y hy
              exact ⟨fun h => lt_asymm hax (lt_trans h.1 hya), fun h => lt_asymm hya h.1⟩
            · simp [elements] at hy
        | some f' =>
          simp only [hfr, Option.some_or, Option.some.injEq] at hf
          subst hf
          obtain ⟨hmem, hxeq, hbet⟩ := ihr hr hfr
          have ha_lt_fk : a < f'.key := har f'.key hmem
          refine ⟨by simp [hmem], ?_, ?_⟩
          · intro hx
            rcases mem_elements_node.mp hx with rfl | hx | hx
            · exact (lt_irrefl x hax).elim
            · exact (lt_asymm hax (hla x hx)).elim
            · exact hxeq hx
          · intro y hy
            rcases mem_elements_node.mp hy with rfl | hy | hy
            · exact ⟨fun h => lt_asymm hax h.1, fun h => lt_asymm ha_lt_fk h.1⟩
            · have hya := hla y hy
              exact ⟨fun h => lt_asymm hax (lt_trans h.1 hya),
                fun h => lt_asymm (lt_trans hya ha_lt_fk) h.1⟩
            · exact hbet y hy
      · simp only [Option.some.injEq] at hf
        subst hf
        have hxeqa : x = a := le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa)
        subst hxeqa
        refine ⟨by simp, fun _ => rfl, fun y _ => ?_⟩
        exact ⟨fun h => lt_irrefl x (lt_trans h.1 h.2), fun h => lt_irrefl x (lt_trans h.1 h.2)⟩

/-! ### Core Splaying Operations -/

/-- Splay `t` at `x`: if `t` is empty, return `(.nil, 0)`; otherwise splay the node reached by
`focusSearch x t []` to the root ([SleatorTarjan1985b], Section 2, pp. 655–656, and Section 3,
pp. 660–661, Figure 6). -/
@[expose] def splay (x : α) (t : BinaryTree α) : SplayResult α :=
  match focusSearch x t [] with
  | none => ⟨.nil, 0⟩
  | some f => splayUp f.key f.leftSub f.rightSub f.ctx

@[simp] theorem splay_nil (x : α) : splay x (.nil : BinaryTree α) = ⟨.nil, 0⟩ := rfl

@[simp] theorem tree_splay_eq_nil_iff (x : α) (t : BinaryTree α) :
    (splay x t).tree = .nil ↔ t = .nil := by
  simp only [splay]
  cases hf : focusSearch x t [] with
  | none =>
    simp [(focusSearch_eq_none_iff x t []).mp hf]
  | some f =>
    have hne : t ≠ .nil := by
      intro h; subst h; simp [focusSearch] at hf
    simp [tree_splayUp_ne_nil, hne]

/-- `splay` preserves the represented finite set of keys on any tree. -/
@[simp] theorem elements_splay (x : α) (t : BinaryTree α) :
    elements (splay x t).tree = elements t := by
  simp only [splay]
  cases hf : focusSearch x t [] with
  | none => simp [(focusSearch_eq_none_iff x t []).mp hf]
  | some f =>
    have htree := (focusSearch_toTree_and_length hf).1
    rw [elements_splayUp]
    simpa only [Focus.toTree, Focus.sub, plug_nil] using congrArg elements htree

/-- `splay` preserves the strict binary-search-tree invariant. -/
theorem ordered_splay {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (splay x t).tree := by
  simp only [splay]
  cases hf : focusSearch x t [] with
  | none => trivial
  | some f =>
    have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := by
      simpa only [Focus.toTree, Focus.sub, plug_nil] using (focusSearch_toTree_and_length hf).1
    apply ordered_splayUp
    rwa [htree]

/-- On any non-empty tree, the rotation count of `splay x t` plus one equals `searchVisits x t`. -/
theorem rotations_splay_add_one_eq_searchVisits {t : BinaryTree α} (ht : t ≠ .nil) (x : α) :
    (splay x t).rotations + 1 = searchVisits x t := by
  simp only [splay]
  cases hf : focusSearch x t [] with
  | none => exact (ht ((focusSearch_eq_none_iff x t []).mp hf)).elim
  | some f =>
    have hlen := (focusSearch_toTree_and_length hf).2
    simpa only [rotations_splayUp, List.length_nil, zero_add] using hlen

/-- If `x ∈ elements t` in an `Ordered` tree `t`, `splay x t` places `x` at the root. -/
theorem rootKey_splay_of_mem {t : BinaryTree α} (ht : Ordered t) {x : α} (hx : x ∈ elements t) :
    rootKey (splay x t).tree = some x := by
  simp only [splay]
  cases hf : focusSearch x t [] with
  | none =>
    have hnil := (focusSearch_eq_none_iff x t []).mp hf
    subst hnil
    simp [elements] at hx
  | some f =>
    have hkey := (focusSearch_ordered_spec ht hf).2.1 hx
    simp [hkey]

/-- Split separation on the left: if `(splay x t).tree = .node r L R` and `x < r`, then every key
in `L` is strictly less than `x`. -/
theorem splay_split_lt {t L R : BinaryTree α} {x r : α} (ht : Ordered t)
    (hs : (splay x t).tree = .node r L R) (hxr : x < r) :
    ∀ y ∈ elements L, y < x := by
  have hord : Ordered (.node r L R) := hs ▸ ordered_splay ht x
  have helem : elements (.node r L R) = elements t := hs ▸ elements_splay x t
  simp only [splay] at hs
  cases hf : focusSearch x t [] with
  | none => simp [hf] at hs
  | some f =>
    simp only [hf] at hs
    have hr_eq : f.key = r := by
      have hroot := rootKey_splayUp f.key f.leftSub f.rightSub f.ctx
      rw [hs] at hroot
      exact Option.some.inj hroot.symm
    obtain ⟨_, hxeq, hbet⟩ := focusSearch_ordered_spec ht hf
    intro y hyL
    have hy_lt_r : y < r := hord.2.2.1 y hyL
    have hy_mem : y ∈ elements t := helem ▸ (by simp [hyL])
    have hy_ne_x : y ≠ x := by
      intro hyx
      subst hyx
      exact ne_of_lt hxr (hr_eq ▸ hxeq hy_mem).symm
    rcases lt_trichotomy y x with hyx | rfl | hxy
    · exact hyx
    · exact (hy_ne_x rfl).elim
    · exact ((hbet y hy_mem).1 ⟨hxy, hr_eq ▸ hy_lt_r⟩).elim

/-- Split separation on the right: if `(splay x t).tree = .node r L R` and `r ≤ x`, then every key
in `R` is strictly greater than `x`. -/
theorem splay_split_ge {t L R : BinaryTree α} {x r : α} (ht : Ordered t)
    (hs : (splay x t).tree = .node r L R) (hrx : r ≤ x) :
    ∀ y ∈ elements R, x < y := by
  have hord : Ordered (.node r L R) := hs ▸ ordered_splay ht x
  rcases eq_or_lt_of_le hrx with rfl | hrltx
  · exact hord.2.2.2
  · have helem : elements (.node r L R) = elements t := hs ▸ elements_splay x t
    simp only [splay] at hs
    cases hf : focusSearch x t [] with
    | none => simp [hf] at hs
    | some f =>
      simp only [hf] at hs
      have hr_eq : f.key = r := by
        have hroot := rootKey_splayUp f.key f.leftSub f.rightSub f.ctx
        rw [hs] at hroot
        exact Option.some.inj hroot.symm
      obtain ⟨_, hxeq, hbet⟩ := focusSearch_ordered_spec ht hf
      intro y hyR
      have hr_lt_y : r < y := hord.2.2.2 y hyR
      have hy_mem : y ∈ elements t := helem ▸ (by simp [hyR])
      have hy_ne_x : y ≠ x := by
        intro hyx
        subst hyx
        exact ne_of_lt hrltx (hr_eq ▸ hxeq hy_mem)
      rcases lt_trichotomy x y with hxy | rfl | hyx
      · exact hxy
      · exact (hy_ne_x rfl).elim
      · exact ((hbet y hy_mem).2 ⟨hr_eq.symm ▸ hr_lt_y, hyx⟩).elim

@[simp] theorem elements_splayMin (t : BinaryTree α) :
    elements (splayMin t).tree = elements t := by
  simp only [splayMin]
  cases hf : focusMin t [] with
  | none => simp [(focusMin_eq_none_iff t []).mp hf]
  | some f =>
    have htree := (focusMin_spec hf).1
    rw [elements_splayUp]
    simpa only [Focus.toTree, Focus.sub, plug_nil] using congrArg elements htree

theorem ordered_splayMin {t : BinaryTree α} (ht : Ordered t) :
    Ordered (splayMin t).tree := by
  simp only [splayMin]
  cases hf : focusMin t [] with
  | none => trivial
  | some f =>
    have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := by
      simpa only [Focus.toTree, Focus.sub, plug_nil] using (focusMin_spec hf).1
    apply ordered_splayUp
    rwa [htree]

omit [LinearOrder α] in
theorem rotations_splayMin_add_one_eq_minimumVisits {t : BinaryTree α} (ht : t ≠ .nil) :
    (splayMin t).rotations + 1 = minimumVisits t := by
  simp only [splayMin]
  cases hf : focusMin t [] with
  | none => exact (ht ((focusMin_eq_none_iff t []).mp hf)).elim
  | some f =>
    have hlen := focusMin_ctx_length hf
    simpa only [rotations_splayUp, List.length_nil, zero_add] using hlen

@[simp] theorem elements_splayMax (t : BinaryTree α) :
    elements (splayMax t).tree = elements t := by
  simp only [splayMax]
  cases hf : focusMax t [] with
  | none => simp [(focusMax_eq_none_iff t []).mp hf]
  | some f =>
    have htree := (focusMax_spec hf).1
    rw [elements_splayUp]
    simpa only [Focus.toTree, Focus.sub, plug_nil] using congrArg elements htree

theorem ordered_splayMax {t : BinaryTree α} (ht : Ordered t) :
    Ordered (splayMax t).tree := by
  simp only [splayMax]
  cases hf : focusMax t [] with
  | none => trivial
  | some f =>
    have htree : plug (.node f.key f.leftSub f.rightSub) f.ctx = t := by
      simpa only [Focus.toTree, Focus.sub, plug_nil] using (focusMax_spec hf).1
    apply ordered_splayUp
    rwa [htree]

/-! ### Self-Adjusting Dictionary and Split/Join Operations -/

/-- Self-adjusting membership test (`access(x, t)` in [SleatorTarjan1985b], Section 3,
pp. 660–661): splays `t` at `x` and checks whether the new root equals `x`. -/
@[expose] def contains (x : α) (t : BinaryTree α) : QueryResult α Bool :=
  let res := splay x t
  match res.tree with
  | .nil => ⟨false, .nil, 0⟩
  | .node r l R => ⟨decide (x = r), .node r l R, res.rotations⟩

/-- Split `t` at `x` into `(left, right)` with keys `≤ x` and `> x` ([SleatorTarjan1985b],
Section 3, pp. 661–662, Figure 7(b)). -/
@[expose] def split (x : α) (t : BinaryTree α) : SplitResult α :=
  let res := splay x t
  match res.tree with
  | .nil => ⟨.nil, .nil, 0⟩
  | .node r l R =>
      if x < r then ⟨l, .node r .nil R, res.rotations⟩
      else ⟨.node r l .nil, R, res.rotations⟩

/-- Concatenate two trees `t₁` and `t₂` whose keys satisfy `∀ x ∈ t₁, ∀ y ∈ t₂, x < y`, by
splaying the maximum element of `t₁` to its root and attaching `t₂` as its right subtree
([SleatorTarjan1985b], Section 3, pp. 661–662, Figure 7(a)). -/
@[expose] def join (t₁ t₂ : BinaryTree α) : SplayResult α :=
  match t₁ with
  | .nil => ⟨t₂, 0⟩
  | .node _ _ _ =>
      let res := splayMax t₁
      match res.tree with
      | .nil => ⟨t₂, res.rotations⟩
      | .node m l _ => ⟨.node m l t₂, res.rotations⟩

/-- Self-adjusting set-idempotent insertion ([SleatorTarjan1985b], Section 3, p. 662,
Figure 8(a)): splays `t` at `x`; if `x` is already at the root, leaves the splayed tree unchanged,
and otherwise inserts `x` as the new root above the split subtrees. -/
@[expose] def insert (x : α) (t : BinaryTree α) : SplayResult α :=
  match t with
  | .nil => ⟨.node x .nil .nil, 0⟩
  | .node _ _ _ =>
      let res := splay x t
      match res.tree with
      | .nil => ⟨.node x .nil .nil, res.rotations⟩
      | .node r l R =>
          if x < r then ⟨.node x l (.node r .nil R), res.rotations⟩
          else if r < x then ⟨.node x (.node r l .nil) R, res.rotations⟩
          else ⟨.node r l R, res.rotations⟩

/-- Self-adjusting set-idempotent deletion ([SleatorTarjan1985b], Section 3, p. 662,
Figure 8(b)): splays `t` at `x`, and if `x` is at the new root replaces the tree by `join` of its
left and right subtrees. -/
@[expose] def erase (x : α) (t : BinaryTree α) : SplayResult α :=
  match t with
  | .nil => ⟨.nil, 0⟩
  | .node _ _ _ =>
      let res := splay x t
      match res.tree with
      | .nil => ⟨.nil, res.rotations⟩
      | .node r l R =>
          if x = r then
            let j := join l R
            ⟨j.tree, res.rotations + j.rotations⟩
          else
            ⟨.node r l R, res.rotations⟩

/-- Self-adjusting minimum query: splays the leftmost node to the root and returns its key. -/
@[expose] def minimum (t : BinaryTree α) : QueryResult α (Option α) :=
  let res := splayMin t
  match res.tree with
  | .nil => ⟨none, .nil, 0⟩
  | .node m l R => ⟨some m, .node m l R, res.rotations⟩

/-- Self-adjusting strict successor query: splays `t` at `x`; if the splayed root `r` satisfies
`x < r`, `r` is already the least key `> x`; otherwise splays the minimum of the right subtree `R`
and rotates it to the root. -/
@[expose] def successor (x : α) (t : BinaryTree α) : QueryResult α (Option α) :=
  let res := splay x t
  match res.tree with
  | .nil => ⟨none, .nil, 0⟩
  | .node r l R =>
      if x < r then
        ⟨some r, .node r l R, res.rotations⟩
      else
        match R with
        | .nil => ⟨none, .node r l .nil, res.rotations⟩
        | .node _ _ _ =>
            let mres := splayMin R
            match mres.tree with
            | .nil => ⟨none, .node r l .nil, res.rotations + mres.rotations⟩
            | .node m mL mR =>
                ⟨some m, .node m (.node r l mL) mR, res.rotations + mres.rotations + 1⟩

/-! ### Correctness and Invariant Preservation of Operations -/

@[simp] theorem elements_contains (x : α) (t : BinaryTree α) :
    elements (contains x t).tree = elements t := by
  simp only [contains]
  cases hs : (splay x t).tree <;> simp [← elements_splay x t, hs]

theorem ordered_contains {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (contains x t).tree := by
  simp only [contains]
  have ho := ordered_splay ht x
  cases hs : (splay x t).tree <;> simpa [hs] using ho

theorem contains_answer_eq_true {t : BinaryTree α} (ht : Ordered t) (x : α) :
    (contains x t).answer = true ↔ x ∈ elements t := by
  simp only [contains]
  cases hs : (splay x t).tree with
  | nil =>
    have hnil := (tree_splay_eq_nil_iff x t).mp hs
    subst hnil
    simp [elements]
  | node r l R =>
    simp only [decide_eq_true_eq]
    constructor
    · rintro rfl
      have he := elements_splay x t
      rw [hs] at he
      exact he ▸ (by simp)
    · intro hx
      have hroot := rootKey_splay_of_mem ht hx
      rw [hs] at hroot
      exact (Option.some.inj hroot).symm

theorem contains_answer_eq {t : BinaryTree α} (ht : Ordered t) (x : α) :
    (contains x t).answer = SearchTree.contains x t := by
  rw [Bool.eq_iff_iff, contains_answer_eq_true ht x, SearchTree.contains_eq_true ht x]

theorem ordered_split {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (split x t).left ∧ Ordered (split x t).right := by
  simp only [split]
  have ho := ordered_splay ht x
  cases hs : (splay x t).tree with
  | nil => simp [Ordered]
  | node r l R =>
    dsimp only
    rw [hs] at ho
    obtain ⟨hl, hR, hlr, hrR⟩ := ho
    split <;> dsimp only
    · exact ⟨hl, ⟨trivial, hR, by simp, hrR⟩⟩
    · exact ⟨⟨hl, trivial, hlr, by simp⟩, hR⟩

theorem elements_split_left {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (split x t).left = (elements t).filter (· ≤ x) := by
  simp only [split]
  have ho := ordered_splay ht x
  have he := elements_splay x t
  cases hs : (splay x t).tree with
  | nil =>
    have hnil := (tree_splay_eq_nil_iff x t).mp hs
    subst hnil; simp
  | node r l R =>
    dsimp only
    rw [hs] at ho he
    obtain ⟨_, _, hlr, hrR⟩ := ho
    split <;> rename_i hxr <;> dsimp only
    · have hlt := splay_split_lt ht hs hxr
      ext y
      simp only [Finset.mem_filter, ← he, mem_elements_node]
      constructor
      · intro hy
        exact ⟨Or.inr (Or.inl hy), (hlt y hy).le⟩
      · rintro ⟨rfl | hy | hy, hyx⟩
        · exact (not_lt_of_ge hyx hxr).elim
        · exact hy
        · exact (not_lt_of_ge hyx (lt_trans hxr (hrR y hy))).elim
    · have hrx : r ≤ x := le_of_not_gt hxr
      have hgt := splay_split_ge ht hs hrx
      ext y
      simp only [Finset.mem_filter, ← he, mem_elements_node, elements_nil_eq,
        Finset.notMem_empty, or_false]
      constructor
      · rintro (rfl | hy)
        · exact ⟨Or.inl rfl, hrx⟩
        · exact ⟨Or.inr (Or.inl hy), (lt_of_lt_of_le (hlr y hy) hrx).le⟩
      · rintro ⟨rfl | hy | hy, hyx⟩
        · exact Or.inl rfl
        · exact Or.inr hy
        · exact (not_lt_of_ge hyx (hgt y hy)).elim

theorem elements_split_right {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (split x t).right = (elements t).filter (x < ·) := by
  simp only [split]
  have ho := ordered_splay ht x
  have he := elements_splay x t
  cases hs : (splay x t).tree with
  | nil =>
    have hnil := (tree_splay_eq_nil_iff x t).mp hs
    subst hnil; simp
  | node r l R =>
    dsimp only
    rw [hs] at ho he
    obtain ⟨_, _, hlr, hrR⟩ := ho
    split <;> rename_i hxr <;> dsimp only
    · have hlt := splay_split_lt ht hs hxr
      ext y
      simp only [Finset.mem_filter, ← he, mem_elements_node, elements_nil_eq,
        Finset.notMem_empty, false_or]
      constructor
      · rintro (rfl | hy)
        · exact ⟨Or.inl rfl, hxr⟩
        · exact ⟨Or.inr (Or.inr hy), lt_trans hxr (hrR y hy)⟩
      · rintro ⟨rfl | hy | hy, hxy⟩
        · exact Or.inl rfl
        · exact (lt_asymm hxy (hlt y hy)).elim
        · exact Or.inr hy
    · have hrx : r ≤ x := le_of_not_gt hxr
      have hgt := splay_split_ge ht hs hrx
      ext y
      simp only [Finset.mem_filter, ← he, mem_elements_node]
      constructor
      · intro hy
        exact ⟨Or.inr (Or.inr hy), hgt y hy⟩
      · rintro ⟨rfl | hy | hy, hxy⟩
        · exact (not_lt_of_ge hrx hxy).elim
        · exact (not_lt_of_ge (le_trans (hlr y hy).le hrx) hxy).elim
        · exact hy

theorem elements_join (t₁ t₂ : BinaryTree α) :
    elements (join t₁ t₂).tree = elements t₁ ∪ elements t₂ := by
  cases t₁ with
  | nil => simp [join]
  | node a l r =>
    obtain ⟨m, lm, hm⟩ := exists_node_nil_right_splayMax (t := .node a l r) (by simp)
    have he := elements_splayMax (.node a l r)
    rw [hm] at he
    simp only [join, hm]
    ext y
    simp only [mem_elements_node, Finset.mem_union, ← he, elements_nil_eq, Finset.notMem_empty,
      or_false]
    tauto

theorem ordered_join {t₁ t₂ : BinaryTree α} (h₁ : Ordered t₁) (h₂ : Ordered t₂)
    (hsep : ∀ x ∈ elements t₁, ∀ y ∈ elements t₂, x < y) :
    Ordered (join t₁ t₂).tree := by
  cases t₁ with
  | nil => simpa [join] using h₂
  | node a l r =>
    obtain ⟨m, lm, hm⟩ := exists_node_nil_right_splayMax (t := .node a l r) (by simp)
    have ho := ordered_splayMax h₁
    have he := elements_splayMax (.node a l r)
    rw [hm] at ho he
    obtain ⟨hlm, _, hlt, _⟩ := ho
    simp only [join, hm]
    refine ⟨hlm, h₂, hlt, ?_⟩
    intro y hy
    exact hsep m (he ▸ by simp) y hy

@[simp] theorem elements_insert (x : α) (t : BinaryTree α) :
    elements (insert x t).tree = Insert.insert x (elements t) := by
  cases t with
  | nil => simp [insert, elements]
  | node a l r =>
    simp only [insert]
    have he := elements_splay x (.node a l r)
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have hnil := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at hnil
    | node r' l' R' =>
      dsimp only
      rw [hs] at he
      rw [← he]
      split <;> rename_i hxr
      · dsimp only
        ext y
        simp only [mem_elements_node, elements_nil_eq, Finset.notMem_empty, Finset.mem_insert]
        tauto
      · split <;> rename_i hrx <;> dsimp only
        · ext y
          simp only [mem_elements_node, elements_nil_eq, Finset.notMem_empty, Finset.mem_insert]
          tauto
        · have hxeqr : x = r' := le_antisymm (le_of_not_gt hrx) (le_of_not_gt hxr)
          subst hxeqr
          ext y
          simp only [mem_elements_node, Finset.mem_insert]
          tauto

theorem ordered_insert {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (insert x t).tree := by
  cases t with
  | nil => simp [insert, Ordered]
  | node a l r =>
    simp only [insert]
    have ho := ordered_splay ht x
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have hnil := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at hnil
    | node r' l' R' =>
      dsimp only
      have ho' : Ordered (.node r' l' R') := hs ▸ ho
      obtain ⟨hl', hR', hlr', hrR'⟩ := id ho'
      split <;> rename_i hxr
      · dsimp only
        have hlt := splay_split_lt ht hs hxr
        refine ⟨hl', ⟨trivial, hR', by simp, hrR'⟩, hlt, ?_⟩
        intro y hy
        rcases mem_elements_node.mp hy with rfl | hy | hy
        · exact hxr
        · simp at hy
        · exact lt_trans hxr (hrR' y hy)
      · split <;> rename_i hrx <;> dsimp only
        · have hgt := splay_split_ge ht hs hrx.le
          refine ⟨⟨hl', trivial, hlr', by simp⟩, hR', ?_, hgt⟩
          intro y hy
          rcases mem_elements_node.mp hy with rfl | hy | hy
          · exact hrx
          · exact lt_trans (hlr' y hy) hrx
          · simp at hy
        · exact ho'

@[simp] theorem rootKey_insert (x : α) (t : BinaryTree α) :
    rootKey (insert x t).tree = some x := by
  cases t with
  | nil => rfl
  | node a l r =>
    simp only [insert]
    cases hs : (splay x (.node a l r)).tree with
    | nil => simp
    | node r' l' R' =>
      dsimp only
      split
      · rfl
      · split
        · rfl
        · rename_i hxr hrx
          simp [le_antisymm (le_of_not_gt hrx) (le_of_not_gt hxr)]

theorem elements_erase {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (erase x t).tree = (elements t).erase x := by
  cases t with
  | nil => simp [erase]
  | node a l r =>
    simp only [erase]
    have ho := ordered_splay ht x
    have he := elements_splay x (.node a l r)
    cases hs : (splay x (.node a l r)).tree with
    | nil =>
      have hnil := (tree_splay_eq_nil_iff x (.node a l r)).mp hs
      simp at hnil
    | node r' l' R' =>
      dsimp only
      have ho' : Ordered (.node r' l' R') := hs ▸ ho
      obtain ⟨_, _, hlr', hrR'⟩ := id ho'
      rw [hs] at he
      split <;> rename_i hxr <;> dsimp only
      · subst hxr
        rw [elements_join]
        have hnotMem : x ∉ elements l' ∪ elements R' := by
          intro hmem
          rcases Finset.mem_union.mp hmem with hmem | hmem
          · exact lt_irrefl x (hlr' x hmem)
          · exact lt_irrefl x (hrR' x hmem)
        rw [← he, elements, Finset.erase_insert hnotMem]
      · have hxnot : x ∉ elements (.node a l r) := by
          intro hxmem
          have hroot := rootKey_splay_of_mem ht hxmem
          rw [hs] at hroot
          exact hxr (Option.some.inj hroot).symm
        rw [he, Finset.erase_eq_of_notMem hxnot]

theorem ordered_erase {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (erase x t).tree := by
  cases t with
  | nil => trivial
  | node a l r =>
    simp only [erase]
    have ho := ordered_splay ht x
    cases hs : (splay x (.node a l r)).tree with
    | nil => simp [Ordered]
    | node r' l' R' =>
      dsimp only
      have ho' : Ordered (.node r' l' R') := hs ▸ ho
      obtain ⟨hl', hR', hlr', hrR'⟩ := id ho'
      split <;> dsimp only
      · exact ordered_join hl' hR' (fun y hy z hz => lt_trans (hlr' y hy) (hrR' z hz))
      · exact ho'

@[simp] theorem elements_minimum (t : BinaryTree α) :
    elements (minimum t).tree = elements t := by
  simp only [minimum]
  cases hs : (splayMin t).tree <;> simp [← elements_splayMin t, hs]

theorem ordered_minimum {t : BinaryTree α} (ht : Ordered t) :
    Ordered (minimum t).tree := by
  simp only [minimum]
  have ho := ordered_splayMin ht
  cases hs : (splayMin t).tree <;> simpa [hs] using ho

theorem minimum_spec {t : BinaryTree α} (ht : Ordered t) :
    LeastResult (elements t) (minimum t).answer := by
  cases t with
  | nil => rfl
  | node a l r =>
    obtain ⟨m, rm, hm⟩ := exists_node_nil_left_splayMin (t := .node a l r) (by simp)
    have ho : Ordered (.node m .nil rm) := hm ▸ ordered_splayMin ht
    have he : elements (.node m .nil rm) = elements (.node a l r) := hm ▸ elements_splayMin _
    simp only [minimum, hm, LeastResult, ← he]
    refine ⟨by simp, ?_⟩
    intro y hy
    rcases mem_elements_node.mp hy with rfl | hy | hy
    · exact le_rfl
    · simp at hy
    · exact (ho.2.2.2 y hy).le

theorem minimum_answer_eq {t : BinaryTree α} (ht : Ordered t) :
    (minimum t).answer = SearchTree.minimum t :=
  (minimum_spec ht).eq_least.trans (SearchTree.minimum_spec ht).eq_least.symm

@[simp] theorem elements_successor (x : α) (t : BinaryTree α) :
    elements (successor x t).tree = elements t := by
  simp only [successor]
  have he := elements_splay x t
  cases hs : (splay x t).tree with
  | nil => simpa [hs] using he
  | node r l R =>
    dsimp only
    rw [hs] at he
    split
    · exact he
    · cases R with
      | nil => exact he
      | node b rl rr =>
        dsimp only
        have heR := elements_splayMin (.node b rl rr)
        cases hm : (splayMin (.node b rl rr)).tree with
        | nil =>
          have hnil := (tree_splayMin_eq_nil_iff (.node b rl rr)).mp hm
          simp at hnil
        | node m mL mR =>
          dsimp only
          rw [hm] at heR
          ext y
          simp only [← he, mem_elements_node, ← heR]
          tauto

theorem ordered_successor {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (successor x t).tree := by
  simp only [successor]
  have ho := ordered_splay ht x
  cases hs : (splay x t).tree with
  | nil => simp [Ordered]
  | node r l R =>
    dsimp only
    have ho' : Ordered (.node r l R) := hs ▸ ho
    obtain ⟨hl, hR, hlr, hrR⟩ := id ho'
    split
    · exact ho'
    · cases R with
      | nil => exact ho'
      | node b rl rr =>
        dsimp only
        have hoR := ordered_splayMin hR
        have heR := elements_splayMin (.node b rl rr)
        cases hm : (splayMin (.node b rl rr)).tree with
        | nil =>
          have hnil := (tree_splayMin_eq_nil_iff (.node b rl rr)).mp hm
          simp at hnil
        | node m mL mR =>
          dsimp only
          rw [hm] at hoR heR
          have hrot : Ordered (.node r l (.node m mL mR)) :=
            ⟨hl, hoR, hlr, heR.symm ▸ hrR⟩
          exact ordered_zig_right hrot

theorem successor_spec {t : BinaryTree α} (ht : Ordered t) (x : α) :
    LeastResult ((elements t).filter (x < ·)) (successor x t).answer := by
  simp only [successor]
  have ho := ordered_splay ht x
  have he := elements_splay x t
  cases hs : (splay x t).tree with
  | nil =>
    have hnil := (tree_splay_eq_nil_iff x t).mp hs
    subst hnil
    simp [LeastResult]
  | node r l R =>
    dsimp only
    have ho' : Ordered (.node r l R) := hs ▸ ho
    obtain ⟨_, hR, hlr, hrR⟩ := id ho'
    rw [hs] at he
    by_cases hxr : x < r
    · have hlt := splay_split_lt ht hs hxr
      simp only [hxr, ↓reduceIte, LeastResult]
      refine ⟨Finset.mem_filter.mpr ⟨he ▸ by simp, hxr⟩, ?_⟩
      intro y hy
      rw [Finset.mem_filter, ← he, mem_elements_node] at hy
      rcases hy with ⟨rfl | hy | hy, hxy⟩
      · exact le_rfl
      · exact (lt_asymm hxy (hlt y hy)).elim
      · exact (hrR y hy).le
    · simp only [hxr, ↓reduceIte]
      have hrx : r ≤ x := le_of_not_gt hxr
      have hgt := splay_split_ge ht hs hrx
      have hfilter_eq : (elements t).filter (x < ·) = elements R := by
        ext y
        simp only [Finset.mem_filter, ← he, mem_elements_node]
        constructor
        · rintro ⟨rfl | hy | hy, hxy⟩
          · exact (not_lt_of_ge hrx hxy).elim
          · exact (not_lt_of_ge (le_trans (hlr y hy).le hrx) hxy).elim
          · exact hy
        · intro hy
          exact ⟨Or.inr (Or.inr hy), hgt y hy⟩
      rw [hfilter_eq]
      cases R with
      | nil => simp [LeastResult]
      | node b rl rr =>
        dsimp only
        obtain ⟨m, rm, hm⟩ := exists_node_nil_left_splayMin (t := .node b rl rr) (by simp)
        have hoR : Ordered (.node m .nil rm) := hm ▸ ordered_splayMin hR
        have heR : elements (.node m .nil rm) = elements (.node b rl rr) :=
          hm ▸ elements_splayMin _
        simp only [hm, LeastResult, ← heR]
        refine ⟨by simp, ?_⟩
        intro y hy
        rcases mem_elements_node.mp hy with rfl | hy | hy
        · exact le_rfl
        · simp at hy
        · exact (hoR.2.2.2 y hy).le

theorem successor_answer_eq {t : BinaryTree α} (ht : Ordered t) (x : α) :
    (successor x t).answer = SearchTree.successor x t :=
  (successor_spec ht x).eq_least.trans (SearchTree.successor_spec ht x).eq_least.symm

end Ordered

end Cslib.Algorithms.Lean.SplayTree
