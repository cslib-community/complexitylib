/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/Digraph/Arborescence.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Logic.Relation

/-!
# Spanning in-arborescences and parent functions

A digraph `T` on `V` is a *spanning in-arborescence rooted at `r`* (`Digraph.IsInArborescence`)
if the root has no outgoing arc, every other vertex has exactly one outgoing arc, and every vertex
reaches `r` along arcs. Its arcs point towards the root.

An in-arborescence is determined by its *parent function*, which sends each vertex `v ≠ r` to the
head of its unique outgoing arc. Conversely, a function `p : V → V` gives the digraph
`Digraph.parentDigraph r p` with arcs `v → p v` for `v ≠ r`. This module proves that this digraph
is a spanning in-arborescence exactly when iterating `p` leads from every vertex to `r`
(`Digraph.isInArborescence_parentDigraph_iff`), and that every spanning in-arborescence arises this
way (`Digraph.IsInArborescence.exists_parentDigraph_eq`).

## Main definitions

* `Digraph.IsInArborescence`: spanning in-arborescences rooted at a vertex.
* `Digraph.parentDigraph`: the digraph of a parent function.

## Main results

* `Digraph.isInArborescence_parentDigraph_iff`: `parentDigraph r p` is a spanning in-arborescence
  rooted at `r` iff every vertex reaches `r` by iterating `p`.
* `Digraph.IsInArborescence.exists_parentDigraph_eq`: every spanning in-arborescence is the digraph
  of a parent function fixing the root.

The directed matrix-tree theorem (`Complexity.Foundations.Combinatorics.Digraph.MatrixTree`) counts
these arborescences, and the Chu–Liu/Edmonds algorithm
(`Complexity.Algorithms.Lean.Arborescence.ChuLiuEdmonds`) optimizes over them.
-/

public section

namespace Digraph

variable {V : Type*}

/-- `T` is a **spanning in-arborescence rooted at `r`**, an oriented spanning tree with every arc
directed towards `r`: the root has no outgoing arc, every other vertex has exactly one outgoing
arc, and every vertex reaches `r` along arcs. -/
structure IsInArborescence (T : Digraph V) (r : V) : Prop where
  /-- The root has no outgoing arc. -/
  not_adj_root : ∀ w, ¬ T.Adj r w
  /-- Every vertex other than the root has exactly one outgoing arc. -/
  existsUnique_adj : ∀ v, v ≠ r → ∃! w, T.Adj v w
  /-- Every vertex reaches the root along arcs. -/
  reachable : ∀ v, Relation.ReflTransGen T.Adj v r

/-- The digraph of a parent function `p`: the arcs `v → p v` for `v ≠ r`. -/
@[expose] def parentDigraph (r : V) (p : V → V) : Digraph V where
  Adj v w := v ≠ r ∧ p v = w

instance [DecidableEq V] (r : V) (p : V → V) : DecidableRel (parentDigraph r p).Adj :=
  fun v w => inferInstanceAs (Decidable (v ≠ r ∧ p v = w))

@[simp]
theorem parentDigraph_adj {r : V} {p : V → V} {v w : V} :
    (parentDigraph r p).Adj v w ↔ v ≠ r ∧ p v = w := Iff.rfl

/-- If iterating `p` leads from `v` to `r`, then `v` reaches `r` in `parentDigraph r p`. -/
theorem reflTransGen_parentDigraph_of_iterate_eq {r : V} {p : V → V} :
    ∀ {n : ℕ} {v : V}, p^[n] v = r → Relation.ReflTransGen (parentDigraph r p).Adj v r
  | 0, v, h => by
    rw [Function.iterate_zero_apply] at h
    rw [h]
  | n + 1, v, h => by
    by_cases hv : v = r
    · rw [hv]
    · rw [Function.iterate_succ_apply] at h
      exact Relation.ReflTransGen.head ⟨hv, rfl⟩ (reflTransGen_parentDigraph_of_iterate_eq h)

/-- If `v` reaches `r` in `parentDigraph r p`, then iterating `p` leads from `v` to `r`. -/
theorem exists_iterate_eq_of_reflTransGen_parentDigraph {r : V} {p : V → V} {v : V}
    (h : Relation.ReflTransGen (parentDigraph r p).Adj v r) : ∃ n, p^[n] v = r := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact ⟨0, rfl⟩
  | head hab _ ih =>
    obtain ⟨n, hn⟩ := ih
    obtain ⟨-, rfl⟩ := hab
    exact ⟨n + 1, by rw [Function.iterate_succ_apply, hn]⟩

/-- The digraph of a parent function is a spanning in-arborescence rooted at `r` iff iterating
the parent function leads from every vertex to `r`. -/
theorem isInArborescence_parentDigraph_iff {r : V} {p : V → V} :
    (parentDigraph r p).IsInArborescence r ↔ ∀ v, ∃ n, p^[n] v = r := by
  refine ⟨fun h v => exists_iterate_eq_of_reflTransGen_parentDigraph (h.reachable v), fun h => ?_⟩
  refine ⟨fun w hw => hw.1 rfl, fun v hv => ⟨p v, ⟨hv, rfl⟩, fun w hw => hw.2.symm⟩, fun v => ?_⟩
  obtain ⟨n, hn⟩ := h v
  exact reflTransGen_parentDigraph_of_iterate_eq hn

/-- Every spanning in-arborescence rooted at `r` is the digraph of a parent function fixing `r`. -/
theorem IsInArborescence.exists_parentDigraph_eq {T : Digraph V} {r : V}
    (hT : T.IsInArborescence r) : ∃ p : V → V, p r = r ∧ parentDigraph r p = T := by
  classical
  let p : V → V := fun v => if hv : v = r then r else (hT.existsUnique_adj v hv).choose
  have hp : ∀ v (hv : v ≠ r), T.Adj v (p v) := fun v hv => by
    simp only [p, dite_eq_right hv]
    exact (hT.existsUnique_adj v hv).choose_spec.1
  refine ⟨p, by simp [p], ?_⟩
  ext v w
  constructor
  · rintro ⟨hv, rfl⟩
    exact hp v hv
  · intro hvw
    have hv : v ≠ r := fun h => hT.not_adj_root w (h ▸ hvw)
    exact ⟨hv, (hT.existsUnique_adj v hv).unique (hp v hv) hvw⟩

end Digraph
