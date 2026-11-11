/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Separator.lean`)

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Combinatorics.SimpleGraph.Walk.Basic
import Mathlib.Combinatorics.SimpleGraph.Walk.Maps
import Mathlib.Combinatorics.SimpleGraph.Walk.Operations

/-!
# Separating vertex sets

A set `Y` of vertices *separates* `A` from `B` in a simple graph `G` (`SimpleGraph.IsSeparator`)
when every walk from a vertex of `A` to a vertex of `B` visits a vertex of `Y`. This is the
`A`–`B` separator of graph theory; `Y` may meet `A` and `B`, and a vertex of `A ∩ B` must lie in
`Y` (the trivial walk). A walk avoiding `Y` contains a path avoiding `Y` with the same endpoints,
so quantifying over walks or over paths gives the same notion
(`SimpleGraph.isSeparator_iff_forall_isPath`). For single terminals `A = {u}`, `B = {v}` with
`u, v ∉ Y`, this is the `u`–`v` vertex separator `SimpleGraph.IsVertexSeparator` of Menger's
theorem ([Diestel2025], §1.4; related by `SimpleGraph.isVertexSeparator_iff_isSeparator`).

`SimpleGraph.reachAvoiding G A Y` is the set of vertices reached from `A` by walks avoiding `Y`.
`Y` separates `A` from `B` exactly when no vertex of `B` is reached
(`SimpleGraph.isSeparator_iff_forall_notMem_reachAvoiding`). A Boolean labelling that is
constant along edges outside `Y`, true on `A \ Y` and false on `B \ Y`, certifies that `Y`
separates `A` from `B` (`SimpleGraph.isSeparator_of_forall_adj`). This is the form in which a
minimum cut of a flow network certifies a vertex separator.

## Main definitions

* `SimpleGraph.IsSeparator`: `Y` separates `A` from `B` in `G`.
* `SimpleGraph.IsVertexSeparator`: finite `u`–`v` vertex separator avoiding `u` and `v`.
* `SimpleGraph.reachAvoiding`: the vertices reached from `A` by walks avoiding `Y`.

## Main results

* `SimpleGraph.isVertexSeparator_iff_isSeparator`: single-terminal vertex separators in terms of
  `IsSeparator`.
* `SimpleGraph.isVertexSeparator_iff_not_reachable_induce`: `u`–`v` separation in terms of
  reachability in `G.induce (T : Set V)ᶜ`.
* `SimpleGraph.isVertexSeparator_of_forall_adj`: closed-set certificate for `IsVertexSeparator`.
* `SimpleGraph.isSeparator_iff_forall_notMem_reachAvoiding`: separation in terms of
  `reachAvoiding`.
* `SimpleGraph.mem_reachAvoiding_of_mem`, `SimpleGraph.mem_reachAvoiding_of_adj`,
  `SimpleGraph.notMem_of_mem_reachAvoiding`: closure properties of `reachAvoiding`.
* `SimpleGraph.isSeparator_of_forall_adj`: a labelling certificate for separation.
* `SimpleGraph.isSeparator_iff_forall_isPath`: it suffices to check paths.
* `SimpleGraph.IsSeparator.mono`: enlarging the separator.
* `SimpleGraph.isSeparator_of_subset_left`: a separator containing `A`.
-/

public section

namespace SimpleGraph

variable {V : Type*} (G : SimpleGraph V)

/-- `Y` separates `A` from `B` in `G`: every walk from a vertex of `A` to a vertex of `B` visits a
vertex of `Y`. A vertex of `A ∩ B` must lie in `Y`, because of its trivial walk. -/
def IsSeparator (A B Y : Set V) : Prop :=
  ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → ∀ p : G.Walk a b, ∃ x ∈ p.support, x ∈ Y

/-- The vertices reached from `A` by walks of `G` that avoid `Y`. -/
def reachAvoiding (A Y : Set V) : Set V :=
  {v | ∃ a ∈ A, ∃ p : G.Walk a v, ∀ x ∈ p.support, x ∉ Y}

variable {G} {A B Y Y' : Set V}

theorem IsSeparator.exists_mem_support (h : G.IsSeparator A B Y) {a b : V} (ha : a ∈ A)
    (hb : b ∈ B) (p : G.Walk a b) : ∃ x ∈ p.support, x ∈ Y :=
  h ha hb p

theorem IsSeparator.mono (h : G.IsSeparator A B Y) (hY : Y ⊆ Y') : G.IsSeparator A B Y' :=
  fun _ ha _ hb p => (h ha hb p).imp fun _ hx => ⟨hx.1, hY hx.2⟩

/-- A set containing `A` separates `A` from any `B`: every walk starts in `A`. -/
theorem isSeparator_of_subset_left (h : A ⊆ Y) : G.IsSeparator A B Y :=
  fun a ha _ _ p => ⟨a, p.start_mem_support, h ha⟩

theorem mem_reachAvoiding_of_mem {v : V} (hA : v ∈ A) (hY : v ∉ Y) : v ∈ G.reachAvoiding A Y :=
  ⟨v, hA, Walk.nil, by simpa using hY⟩

theorem notMem_of_mem_reachAvoiding {v : V} (h : v ∈ G.reachAvoiding A Y) : v ∉ Y := by
  obtain ⟨_, _, p, hp⟩ := h
  exact hp v p.end_mem_support

/-- `reachAvoiding` is closed under edges to vertices outside `Y`. -/
theorem mem_reachAvoiding_of_adj {u v : V} (hu : u ∈ G.reachAvoiding A Y) (huv : G.Adj u v)
    (hv : v ∉ Y) : v ∈ G.reachAvoiding A Y := by
  obtain ⟨a, ha, p, hp⟩ := hu
  refine ⟨a, ha, p.concat huv, fun x hx => ?_⟩
  rw [Walk.support_concat, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact hp x hx
  · exact hv

/-- It suffices to check paths: a walk avoiding `Y` contains a path (`Walk.bypass`) with the same
endpoints and fewer vertices. -/
theorem isSeparator_iff_forall_isPath :
    G.IsSeparator A B Y ↔
      ∀ ⦃a⦄, a ∈ A → ∀ ⦃b⦄, b ∈ B → ∀ p : G.Walk a b, p.IsPath → ∃ x ∈ p.support, x ∈ Y := by
  classical
  refine ⟨fun h a ha b hb p _ => h ha hb p, fun h a ha b hb p => ?_⟩
  obtain ⟨x, hx, hxY⟩ := h ha hb p.bypass p.bypass_isPath
  exact ⟨x, p.support_bypass_subset_support hx, hxY⟩

/-- `Y` separates `A` from `B` exactly when no vertex of `B` is reached from `A` avoiding `Y`. -/
theorem isSeparator_iff_forall_notMem_reachAvoiding :
    G.IsSeparator A B Y ↔ ∀ b ∈ B, b ∉ G.reachAvoiding A Y := by
  constructor
  · rintro h b hb ⟨a, ha, p, hp⟩
    obtain ⟨x, hx, hxY⟩ := h ha hb p
    exact hp x hx hxY
  · intro h a ha b hb p
    by_contra hp
    push Not at hp
    exact h b hb ⟨a, ha, p, hp⟩

/-- A labelling `f` that is constant along walks avoiding `Y` takes the same value at both
endpoints. -/
private theorem apply_eq_of_forall_adj {f : V → Bool}
    (hf : ∀ ⦃u v⦄, G.Adj u v → u ∉ Y → v ∉ Y → f u = f v) {a b : V} (p : G.Walk a b)
    (hp : ∀ x ∈ p.support, x ∉ Y) : f a = f b := by
  induction p with
  | nil => rfl
  | cons h q ih =>
    rw [Walk.support_cons] at hp
    exact (hf h (hp _ List.mem_cons_self) (hp _ (List.mem_cons_of_mem _ q.start_mem_support))).trans
      (ih fun x hx => hp x (List.mem_cons_of_mem _ hx))

/-- **Labelling certificate.** If `f` is constant along edges outside `Y`, true on `A \ Y` and
false on `B \ Y`, then `Y` separates `A` from `B`. -/
theorem isSeparator_of_forall_adj (f : V → Bool)
    (hf : ∀ ⦃u v⦄, G.Adj u v → u ∉ Y → v ∉ Y → f u = f v)
    (hA : ∀ a ∈ A, a ∉ Y → f a = true) (hB : ∀ b ∈ B, b ∉ Y → f b = false) :
    G.IsSeparator A B Y := by
  intro a ha b hb p
  by_contra hp
  push Not at hp
  have hab := apply_eq_of_forall_adj hf p hp
  rw [hA a ha (hp a p.start_mem_support), hB b hb (hp b p.end_mem_support)] at hab
  exact Bool.noConfusion hab

/-- `T` separates `u` from `v` in `G` ([Diestel2025], §1.4): `u, v ∉ T` and every `u`–`v` path of
`G` visits a vertex of `T`. -/
@[expose] def IsVertexSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  u ∉ T ∧ v ∉ T ∧ ∀ w : G.Walk u v, w.IsPath → ∃ x ∈ w.support, x ∈ T

/-- `T` is a `u`–`v` vertex separator iff `u, v ∉ T` and `T` separates `{u}` from `{v}` in the
`SimpleGraph.IsSeparator` sense. -/
theorem isVertexSeparator_iff_isSeparator {u v : V} {T : Finset V} :
    G.IsVertexSeparator u v T ↔ u ∉ T ∧ v ∉ T ∧ G.IsSeparator {u} {v} ↑T := by
  simp only [IsVertexSeparator, isSeparator_iff_forall_isPath, Set.mem_singleton_iff,
    forall_eq, Finset.mem_coe]

/-- A finite `u`–`v` separator avoids `u` and `v` and meets every `u`–`v` walk. -/
theorem isVertexSeparator_iff_forall_walk {u v : V} {T : Finset V} :
    G.IsVertexSeparator u v T ↔ u ∉ T ∧ v ∉ T ∧ ∀ w : G.Walk u v, ∃ x ∈ w.support, x ∈ T := by
  simp only [isVertexSeparator_iff_isSeparator, IsSeparator, Set.mem_singleton_iff,
    forall_eq, Finset.mem_coe]

/-- `T` is a `u`–`v` vertex separator iff `u, v ∉ T` and `u`, `v` are unreachable in `G - T`. -/
theorem isVertexSeparator_iff_not_reachable_induce {u v : V} {T : Finset V} :
    G.IsVertexSeparator u v T ↔
      ∃ (hu : u ∉ T) (hv : v ∉ T), ¬ (G.induce (T : Set V)ᶜ).Reachable ⟨u, hu⟩ ⟨v, hv⟩ := by
  rw [isVertexSeparator_iff_forall_walk]
  constructor
  · rintro ⟨hu, hv, h⟩
    refine ⟨hu, hv, fun ⟨w⟩ => ?_⟩
    obtain ⟨x, hx, hxT⟩ := h (w.map ⟨Subtype.val, id⟩)
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
    exact hy hxT
  · rintro ⟨hu, hv, h⟩
    refine ⟨hu, hv, fun w => ?_⟩
    by_contra hp
    push Not at hp
    exact h ⟨w.induce (T : Set V)ᶜ fun x hx => hp x hx⟩

/-- Closed-set certificate for a vertex separator: if `u ∈ S`, `v ∉ S`, `T` avoids `u` and `v`,
and every edge leaving `S` ends in `T`, then `T` separates `u` from `v`. -/
theorem isVertexSeparator_of_forall_adj {u v : V} {S T : Finset V} (hu : u ∈ S) (hv : v ∉ S)
    (huT : u ∉ T) (hvT : v ∉ T) (hST : ∀ x ∈ S, ∀ y, G.Adj x y → y ∉ S → y ∈ T) :
    G.IsVertexSeparator u v T := by
  classical
  refine isVertexSeparator_iff_isSeparator.mpr ⟨huT, hvT, isSeparator_of_forall_adj
    (fun x => decide (x ∈ S)) (fun a b hab ha hb => ?_) (fun a ha _ => ?_) (fun b hb _ => ?_)⟩
  · by_contra hne
    rcases Bool.eq_false_or_eq_true (decide (a ∈ S)) with h | h <;>
        rcases Bool.eq_false_or_eq_true (decide (b ∈ S)) with h' | h'
    · exact hne (h.trans h'.symm)
    · simp only [decide_eq_true_eq] at h
      simp only [decide_eq_false_iff_not] at h'
      exact hb (Finset.mem_coe.mpr (hST a h b hab h'))
    · simp only [decide_eq_false_iff_not] at h
      simp only [decide_eq_true_eq] at h'
      exact ha (Finset.mem_coe.mpr (hST b h' a hab.symm h))
    · exact hne (h.trans h'.symm)
  · simp only [Set.mem_singleton_iff] at ha
    simp [ha, hu]
  · simp only [Set.mem_singleton_iff] at hb
    simp [hb, hv]

end SimpleGraph
