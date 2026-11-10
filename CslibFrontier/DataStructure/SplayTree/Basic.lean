/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import CslibFrontier.DataStructure.SearchTree.Cost
public import CslibFrontier.DataStructure.OrderedSet.Basic

/-!
# Self-Adjusting Splay Trees

This module formalizes annotation-free bottom-up splay trees over Mathlib's `BinaryTree α`,
reusing the finite-set abstraction `Cslib.DataStructure.SearchTree.elements` and strict
binary-search-tree invariant `Cslib.DataStructure.SearchTree.Ordered` ([SleatorTarjan1985b],
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
  `Cslib.DataStructure.OrderedSet.spec α` directly, `insert` and `erase` are total and
  set-idempotent: inserting
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

namespace Cslib.DataStructure.SplayTree

open Cslib.DataStructure.OrderedSet
open Cslib.DataStructure.SearchTree (elements Ordered mem_elements_node
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

/-- One step of `focusMin`: it either finds the focus in the left child, or the left child is empty
and the focus is the node itself. -/
private theorem focusMin_node_eq_some {a : α} {l r : BinaryTree α} {ctx : List (Frame α)}
    {f : Focus α} (hf : focusMin (.node a l r) ctx = some f) :
    focusMin l (.left a r :: ctx) = some f ∨ l = .nil ∧ f = ⟨a, l, r, ctx⟩ := by
  rcases Option.or_eq_some_iff.mp hf with hl | ⟨hl, hf⟩
  · exact .inl hl
  · exact .inr ⟨(focusMin_eq_none_iff l _).mp hl, (Option.some.inj hf).symm⟩

/-- One step of `focusMax`, mirroring `focusMin_node_eq_some`. -/
private theorem focusMax_node_eq_some {a : α} {l r : BinaryTree α} {ctx : List (Frame α)}
    {f : Focus α} (hf : focusMax (.node a l r) ctx = some f) :
    focusMax r (.right l a :: ctx) = some f ∨ r = .nil ∧ f = ⟨a, l, r, ctx⟩ := by
  rcases Option.or_eq_some_iff.mp hf with hr | ⟨hr, hf⟩
  · exact .inl hr
  · exact .inr ⟨(focusMax_eq_none_iff r _).mp hr, (Option.some.inj hf).symm⟩

theorem focusMin_spec {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (hf : focusMin t ctx = some f) :
    f.toTree = plug t ctx ∧ f.leftSub = .nil := by
  induction t generalizing ctx with
  | nil => simp [focusMin] at hf
  | node a l r ihl _ =>
    rcases focusMin_node_eq_some hf with hl | ⟨rfl, rfl⟩
    · exact ihl hl
    · exact ⟨rfl, rfl⟩

theorem focusMax_spec {t : BinaryTree α} {ctx : List (Frame α)} {f : Focus α}
    (hf : focusMax t ctx = some f) :
    f.toTree = plug t ctx ∧ f.rightSub = .nil := by
  induction t generalizing ctx with
  | nil => simp [focusMax] at hf
  | node a l r _ ihr =>
    rcases focusMax_node_eq_some hf with hr | ⟨rfl, rfl⟩
    · exact ihr hr
    · exact ⟨rfl, rfl⟩

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
    rcases focusMin_node_eq_some hf with hl | ⟨_, rfl⟩
    · exact ihl (show AllLeft (.left a r :: ctx) from hctx) hl
    · exact hctx

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
    rcases focusMax_node_eq_some hf with hr | ⟨_, rfl⟩
    · exact ihr (show AllRight (.right l a :: ctx) from hctx) hr
    · exact hctx

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
    rcases focusMin_node_eq_some hf with hl | ⟨rfl, rfl⟩
    · have hlen := ihl hl
      simp only [List.length_cons, minimumVisits] at hlen ⊢
      omega
    · simp [minimumVisits]

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

/-- One step of `focusSearch`: it descends into the child on `x`'s side, falling back to the node
itself when that child is empty, or stops at a node whose key is `x`. -/
private theorem focusSearch_node_eq_some {x a : α} {l r : BinaryTree α} {ctx : List (Frame α)}
    {f : Focus α} (hf : focusSearch x (.node a l r) ctx = some f) :
    x < a ∧ (focusSearch x l (.left a r :: ctx) = some f ∨ l = .nil ∧ f = ⟨a, l, r, ctx⟩) ∨
      a < x ∧ (focusSearch x r (.right l a :: ctx) = some f ∨ r = .nil ∧ f = ⟨a, l, r, ctx⟩) ∨
      x = a ∧ f = ⟨a, l, r, ctx⟩ := by
  simp only [focusSearch] at hf
  split_ifs at hf with hxa hax
  · rcases Option.or_eq_some_iff.mp hf with hl | ⟨hl, hf⟩
    · exact .inl ⟨hxa, .inl hl⟩
    · exact .inl ⟨hxa, .inr ⟨(focusSearch_eq_none_iff x l _).mp hl, (Option.some.inj hf).symm⟩⟩
  · rcases Option.or_eq_some_iff.mp hf with hr | ⟨hr, hf⟩
    · exact .inr (.inl ⟨hax, .inl hr⟩)
    · exact .inr (.inl ⟨hax, .inr ⟨(focusSearch_eq_none_iff x r _).mp hr,
        (Option.some.inj hf).symm⟩⟩)
  · exact .inr (.inr ⟨le_antisymm (le_of_not_gt hax) (le_of_not_gt hxa), (Option.some.inj hf).symm⟩)

theorem focusSearch_toTree_and_length {x : α} {t : BinaryTree α} {ctx : List (Frame α)}
    {f : Focus α} (hf : focusSearch x t ctx = some f) :
    f.toTree = plug t ctx ∧ f.ctx.length + 1 = ctx.length + searchVisits x t := by
  induction t generalizing ctx with
  | nil => simp [focusSearch] at hf
  | node a l r ihl ihr =>
    rcases focusSearch_node_eq_some hf with
      ⟨hxa, hl | ⟨rfl, rfl⟩⟩ | ⟨hax, hr | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩
    · obtain ⟨htree, hlen⟩ := ihl hl
      refine ⟨htree, ?_⟩
      simp only [List.length_cons, searchVisits, hxa, ↓reduceIte] at hlen ⊢
      omega
    · simp [Focus.toTree, Focus.sub, searchVisits, hxa]
    · obtain ⟨htree, hlen⟩ := ihr hr
      refine ⟨htree, ?_⟩
      simp only [List.length_cons, searchVisits, lt_asymm hax, hax, ↓reduceIte] at hlen ⊢
      omega
    · simp [Focus.toTree, Focus.sub, searchVisits, lt_asymm hax, hax]
    · simp [Focus.toTree, Focus.sub, searchVisits]

/-- Search step to the left of `a` for `focusSearch_ordered_spec`: if the search continues left of
`a` and returns a key `k ≤ a` satisfying the invariant on `l` (vacuously when `l` is empty and
`k = a`), then `k` satisfies the invariant on `.node a l r`. -/
private theorem focusSearch_spec_left {x a k : α} {l r : BinaryTree α}
    (hxa : x < a) (har : ∀ y ∈ elements r, a < y) (hka : k ≤ a) (hk : k = a ∨ k ∈ elements l)
    (hxeq : x ∈ elements l → k = x)
    (hbet : ∀ y ∈ elements l, ¬ (x < y ∧ y < k) ∧ ¬ (k < y ∧ y < x)) :
    k ∈ elements (.node a l r) ∧ (x ∈ elements (.node a l r) → k = x) ∧
      (∀ y ∈ elements (.node a l r), ¬ (x < y ∧ y < k) ∧ ¬ (k < y ∧ y < x)) := by
  refine ⟨mem_elements_node.mpr (hk.imp_right .inl), fun hx => ?_, fun y hy => ?_⟩
  · rcases mem_elements_node.mp hx with rfl | hx | hx
    · exact (lt_irrefl x hxa).elim
    · exact hxeq hx
    · exact (lt_asymm hxa (har x hx)).elim
  · rcases mem_elements_node.mp hy with rfl | hy | hy
    · exact ⟨fun h => not_le_of_gt h.2 hka, fun h => lt_asymm hxa h.2⟩
    · exact hbet y hy
    · have hay := har y hy
      exact ⟨fun h => not_le_of_gt (lt_of_le_of_lt hka hay) h.2.le,
        fun h => lt_asymm hxa (lt_trans hay h.2)⟩

/-- Search step to the right of `a`, mirroring `focusSearch_spec_left`. -/
private theorem focusSearch_spec_right {x a k : α} {l r : BinaryTree α}
    (hax : a < x) (hla : ∀ y ∈ elements l, y < a) (hak : a ≤ k) (hk : k = a ∨ k ∈ elements r)
    (hxeq : x ∈ elements r → k = x)
    (hbet : ∀ y ∈ elements r, ¬ (x < y ∧ y < k) ∧ ¬ (k < y ∧ y < x)) :
    k ∈ elements (.node a l r) ∧ (x ∈ elements (.node a l r) → k = x) ∧
      (∀ y ∈ elements (.node a l r), ¬ (x < y ∧ y < k) ∧ ¬ (k < y ∧ y < x)) := by
  refine ⟨mem_elements_node.mpr (hk.imp_right .inr), fun hx => ?_, fun y hy => ?_⟩
  · rcases mem_elements_node.mp hx with rfl | hx | hx
    · exact (lt_irrefl x hax).elim
    · exact (lt_asymm hax (hla x hx)).elim
    · exact hxeq hx
  · rcases mem_elements_node.mp hy with rfl | hy | hy
    · exact ⟨fun h => lt_asymm hax h.1, fun h => not_le_of_gt h.1 hak⟩
    · have hya := hla y hy
      exact ⟨fun h => lt_asymm hax (lt_trans h.1 hya),
        fun h => not_le_of_gt (lt_of_lt_of_le hya hak) h.1.le⟩
    · exact hbet y hy

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
    rcases focusSearch_node_eq_some hf with
      ⟨hxa, hfl | ⟨rfl, rfl⟩⟩ | ⟨hax, hfr | ⟨rfl, rfl⟩⟩ | ⟨rfl, rfl⟩
    · obtain ⟨hmem, hxeq, hbet⟩ := ihl hl hfl
      exact focusSearch_spec_left hxa har (hla _ hmem).le (.inr hmem) hxeq hbet
    · exact focusSearch_spec_left hxa har le_rfl (.inl rfl) (by simp) (by simp)
    · obtain ⟨hmem, hxeq, hbet⟩ := ihr hr hfr
      exact focusSearch_spec_right hax hla (har _ hmem).le (.inr hmem) hxeq hbet
    · exact focusSearch_spec_right hax hla le_rfl (.inl rfl) (by simp) (by simp)
    · refine ⟨by simp, fun _ => rfl, fun y _ => ?_⟩
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

/-- Root of a splayed tree: if `(splay x t).tree = .node r L R` with `t` ordered, the splayed tree
is ordered with the same keys, `r = x` when `x` is present, and no key lies strictly between `x`
and `r`. -/
private theorem splay_root_spec {t L R : BinaryTree α} {x r : α} (ht : Ordered t)
    (hs : (splay x t).tree = .node r L R) :
    Ordered (.node r L R) ∧ elements (.node r L R) = elements t ∧ (x ∈ elements t → r = x) ∧
      ∀ y ∈ elements t, ¬ (x < y ∧ y < r) ∧ ¬ (r < y ∧ y < x) := by
  refine ⟨hs ▸ ordered_splay ht x, hs ▸ elements_splay x t, ?_⟩
  simp only [splay] at hs
  cases hf : focusSearch x t [] with
  | none => simp [hf] at hs
  | some f =>
    simp only [hf] at hs
    have hr_eq : r = f.key := by
      simpa only [hs, rootKey_node, Option.some.injEq] using
        rootKey_splayUp f.key f.leftSub f.rightSub f.ctx
    exact hr_eq ▸ (focusSearch_ordered_spec ht hf).2

/-- Split separation on the left: if `(splay x t).tree = .node r L R` and `x < r`, then every key
in `L` is strictly less than `x`. -/
theorem splay_split_lt {t L R : BinaryTree α} {x r : α} (ht : Ordered t)
    (hs : (splay x t).tree = .node r L R) (hxr : x < r) :
    ∀ y ∈ elements L, y < x := by
  obtain ⟨hord, helem, hxeq, hbet⟩ := splay_root_spec ht hs
  intro y hyL
  have hyr : y < r := hord.2.2.1 y hyL
  have hy : y ∈ elements t := helem ▸ mem_elements_node.mpr (.inr (.inl hyL))
  rcases lt_trichotomy y x with hyx | rfl | hxy
  · exact hyx
  · exact (hxr.ne' (hxeq hy)).elim
  · exact ((hbet y hy).1 ⟨hxy, hyr⟩).elim

/-- Split separation on the right: if `(splay x t).tree = .node r L R` and `r ≤ x`, then every key
in `R` is strictly greater than `x`. -/
theorem splay_split_ge {t L R : BinaryTree α} {x r : α} (ht : Ordered t)
    (hs : (splay x t).tree = .node r L R) (hrx : r ≤ x) :
    ∀ y ∈ elements R, x < y := by
  obtain ⟨hord, helem, hxeq, hbet⟩ := splay_root_spec ht hs
  rcases eq_or_lt_of_le hrx with rfl | hrx
  · exact hord.2.2.2
  intro y hyR
  have hry : r < y := hord.2.2.2 y hyR
  have hy : y ∈ elements t := helem ▸ mem_elements_node.mpr (.inr (.inr hyR))
  rcases lt_trichotomy x y with hxy | rfl | hyx
  · exact hxy
  · exact (hrx.ne (hxeq hy)).elim
  · exact ((hbet y hy).2 ⟨hry, hyx⟩).elim

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

/-- `split x t` partitions the keys of an ordered `t` into those `≤ x` and those `> x`. -/
private theorem split_partition {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (split x t).left ∪ elements (split x t).right = elements t ∧
      (∀ y ∈ elements (split x t).left, y ≤ x) ∧ ∀ y ∈ elements (split x t).right, x < y := by
  simp only [split]
  have he := elements_splay x t
  cases hs : (splay x t).tree with
  | nil =>
    rw [hs] at he
    simp [← he]
  | node r l R =>
    obtain ⟨⟨_, _, hlr, hrR⟩, he, -, -⟩ := splay_root_spec ht hs
    dsimp only
    split <;> rename_i hxr <;> dsimp only <;> refine ⟨?_, fun y hy => ?_, fun y hy => ?_⟩
    · ext y; simp only [Finset.mem_union, ← he, mem_elements_node, elements_nil_eq,
        Finset.notMem_empty, false_or]; tauto
    · exact (splay_split_lt ht hs hxr y hy).le
    · rcases mem_elements_node.mp hy with rfl | hy | hy
      · exact hxr
      · simp at hy
      · exact lt_trans hxr (hrR y hy)
    · ext y; simp only [Finset.mem_union, ← he, mem_elements_node, elements_nil_eq,
        Finset.notMem_empty, or_false]; tauto
    · have hrx : r ≤ x := le_of_not_gt hxr
      rcases mem_elements_node.mp hy with rfl | hy | hy
      · exact hrx
      · exact (hlr y hy).le.trans hrx
      · simp at hy
    · exact splay_split_ge ht hs (le_of_not_gt hxr) y hy

theorem elements_split_left {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (split x t).left = (elements t).filter (· ≤ x) := by
  obtain ⟨hunion, hle, hgt⟩ := split_partition ht x
  rw [← hunion, Finset.filter_union, Finset.filter_true_of_mem hle,
    Finset.filter_false_of_mem fun y hy => not_le_of_gt (hgt y hy), Finset.union_empty]

theorem elements_split_right {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (split x t).right = (elements t).filter (x < ·) := by
  obtain ⟨hunion, hle, hgt⟩ := split_partition ht x
  rw [← hunion, Finset.filter_union, Finset.filter_false_of_mem fun y hy => not_lt_of_ge (hle y hy),
    Finset.filter_true_of_mem hgt, Finset.empty_union]

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

/-- Splaying a nonempty tree yields a node. -/
private theorem exists_splay_eq_node {t : BinaryTree α} (ht : t ≠ .nil) (x : α) :
    ∃ r L R, (splay x t).tree = .node r L R := by
  cases hs : (splay x t).tree with
  | nil => exact absurd ((tree_splay_eq_nil_iff x t).mp hs) ht
  | node r L R => exact ⟨r, L, R, rfl⟩

@[simp] theorem elements_insert (x : α) (t : BinaryTree α) :
    elements (insert x t).tree = Insert.insert x (elements t) := by
  cases t with
  | nil => simp [insert, elements]
  | node a l r =>
    obtain ⟨r', l', R', hs⟩ := exists_splay_eq_node (t := .node a l r) (by simp) x
    have he := elements_splay x (.node a l r)
    rw [hs] at he
    simp only [insert, hs, ← he]
    split_ifs with hxr hrx
    on_goal 3 =>
      rw [le_antisymm (le_of_not_gt hrx) (le_of_not_gt hxr), elements, Finset.insert_idem]
    all_goals
      ext y
      simp only [mem_elements_node, elements_nil_eq, Finset.notMem_empty, Finset.mem_insert]
      tauto

theorem ordered_insert {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (insert x t).tree := by
  cases t with
  | nil => simp [insert, Ordered]
  | node a l r =>
    obtain ⟨r', l', R', hs⟩ := exists_splay_eq_node (t := .node a l r) (by simp) x
    have ho := (splay_root_spec ht hs).1
    obtain ⟨-, -, hlr', -⟩ := id ho
    obtain ⟨hleft, hright⟩ := ordered_split ht x
    obtain ⟨-, -, hgt⟩ := split_partition ht x
    simp only [split, hs] at hleft hright hgt
    simp only [insert, hs]
    split_ifs at hleft hright hgt ⊢ with hxr hrx
    · exact ⟨hleft, hright, splay_split_lt ht hs hxr, hgt⟩
    · refine ⟨hleft, hright, fun y hy => ?_, hgt⟩
      rcases mem_elements_node.mp hy with rfl | hy | hy
      exacts [hrx, (hlr' y hy).trans hrx, by simp at hy]
    · exact ho

@[simp] theorem rootKey_insert (x : α) (t : BinaryTree α) :
    rootKey (insert x t).tree = some x := by
  cases t with
  | nil => rfl
  | node a l r =>
    obtain ⟨r', l', R', hs⟩ := exists_splay_eq_node (t := .node a l r) (by simp) x
    simp only [insert, hs]
    split_ifs with hxr hrx
    · rfl
    · rfl
    · simp [le_antisymm (le_of_not_gt hrx) (le_of_not_gt hxr)]

theorem elements_erase {t : BinaryTree α} (ht : Ordered t) (x : α) :
    elements (erase x t).tree = (elements t).erase x := by
  cases t with
  | nil => simp [erase]
  | node a l r =>
    obtain ⟨r', l', R', hs⟩ := exists_splay_eq_node (t := .node a l r) (by simp) x
    obtain ⟨ho, he, hmem, -⟩ := splay_root_spec ht hs
    simp only [erase, hs]
    split_ifs with hxr
    · subst hxr
      rw [elements_join, ← he, elements, Finset.erase_insert ho.notMem_elements_union]
    · rw [he, Finset.erase_eq_of_notMem fun hx => hxr (hmem hx).symm]

theorem ordered_erase {t : BinaryTree α} (ht : Ordered t) (x : α) :
    Ordered (erase x t).tree := by
  cases t with
  | nil => trivial
  | node a l r =>
    obtain ⟨r', l', R', hs⟩ := exists_splay_eq_node (t := .node a l r) (by simp) x
    have ho := (splay_root_spec ht hs).1
    obtain ⟨hl', hR', hlr', hrR'⟩ := id ho
    simp only [erase, hs]
    split_ifs
    · exact ordered_join hl' hR' (fun y hy z hz => lt_trans (hlr' y hy) (hrR' z hz))
    · exact ho

@[simp] theorem elements_minimum (t : BinaryTree α) :
    elements (minimum t).tree = elements t := by
  simp only [minimum]
  cases hs : (splayMin t).tree <;> simp [← elements_splayMin t, hs]

theorem ordered_minimum {t : BinaryTree α} (ht : Ordered t) :
    Ordered (minimum t).tree := by
  simp only [minimum]
  have ho := ordered_splayMin ht
  cases hs : (splayMin t).tree <;> simpa [hs] using ho

/-- The root of an ordered tree with empty left subtree is its least key. -/
private theorem leastResult_node_nil {m : α} {R : BinaryTree α} (ho : Ordered (.node m .nil R)) :
    LeastResult (elements (.node m .nil R)) (some m) := by
  simp only [LeastResult]
  refine ⟨by simp, fun y hy => ?_⟩
  rcases mem_elements_node.mp hy with rfl | hy | hy
  · exact le_rfl
  · simp at hy
  · exact (ho.2.2.2 y hy).le

/-- `splayMin` of a nonempty ordered tree brings its least key to a root with empty left
subtree. -/
private theorem leastResult_splayMin {t : BinaryTree α} (ht : Ordered t) (hne : t ≠ .nil) :
    ∃ m R, (splayMin t).tree = .node m .nil R ∧ LeastResult (elements t) (some m) := by
  obtain ⟨m, R, hm⟩ := exists_node_nil_left_splayMin hne
  refine ⟨m, R, hm, ?_⟩
  rw [← elements_splayMin t, hm]
  exact leastResult_node_nil (hm ▸ ordered_splayMin ht)

theorem minimum_spec {t : BinaryTree α} (ht : Ordered t) :
    LeastResult (elements t) (minimum t).answer := by
  cases t with
  | nil => rfl
  | node a l r =>
    obtain ⟨m, R, hm, hlm⟩ := leastResult_splayMin ht (by simp)
    simpa only [minimum, hm] using hlm

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
  have hright := elements_split_right ht x
  simp only [successor]
  simp only [split] at hright
  cases hs : (splay x t).tree with
  | nil =>
    rw [hs] at hright
    simp [LeastResult, ← hright]
  | node r l R =>
    obtain ⟨⟨-, hR, -, hrR⟩, -, -, -⟩ := splay_root_spec ht hs
    rw [hs] at hright
    dsimp only at hright ⊢
    split_ifs at hright ⊢ with hxr <;> rw [← hright]
    · exact leastResult_node_nil ⟨trivial, hR, by simp, hrR⟩
    · cases R with
      | nil => simp [LeastResult]
      | node b rl rr =>
        obtain ⟨m, R', hm, hlm⟩ := leastResult_splayMin hR (by simp)
        simpa only [hm] using hlm

theorem successor_answer_eq {t : BinaryTree α} (ht : Ordered t) (x : α) :
    (successor x t).answer = SearchTree.successor x t :=
  (successor_spec ht x).eq_least.trans (SearchTree.successor_spec ht x).eq_least.symm

end Ordered

end Cslib.DataStructure.SplayTree
