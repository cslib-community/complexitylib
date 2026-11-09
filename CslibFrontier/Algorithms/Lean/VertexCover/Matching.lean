/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Init
public import Mathlib.Combinatorics.SimpleGraph.VertexCover
import Mathlib.Data.Set.Card

/-!
# The maximal-matching 2-approximation for vertex cover

This module formalizes the classical 2-approximation for minimum vertex cover: greedily build a
maximal matching and return both endpoints of every matching edge ([CLRS2009], Section 35.1,
`APPROX-VERTEX-COVER` and Theorem 35.1).

## Model

The graph is `SimpleGraph.fromRel (fun u v => (u, v) ∈ es)` for a list `es : List (V × V)` of edges
over a type with decidable equality: two distinct vertices are adjacent when some listed edge joins
them in either direction. Self-loops and repeated edges may occur in `es`; the graph ignores them.
Covers and the optimum are Mathlib's `SimpleGraph.IsVertexCover` and
`SimpleGraph.vertexCoverNum`.

## Algorithm and source mapping

`greedyMatching es` scans `es` once, keeping an edge `(u, v)` when `u ≠ v` and neither endpoint is
already matched; `matchingCover es` lists the endpoints of the kept edges. [CLRS2009]'s
`APPROX-VERTEX-COVER` repeatedly picks an arbitrary remaining edge, adds both endpoints to the
cover and deletes the edges incident to them; the scan makes the same choices with "arbitrary"
read as "first remaining edge in list order", since an edge is still present exactly when neither
endpoint has been matched. The analysis is the source's: the kept edges form a matching
(`nodup_matchingCover`), every vertex cover contains a distinct endpoint of each of them
(`length_le_encard_of_isVertexCover`), and the returned cover has exactly two vertices per kept
edge (`length_endpoints`).

## Limitations

The algorithm is a pure Lean function; a machine-level running time for the `Graph` encoding is
in `CslibFrontier.Computability.Complexity.Problems.VertexCover.Approximation`.

## Main definitions

* `Cslib.Algorithms.Lean.VertexCover.endpoints`: the endpoints of a list of edges.
* `Cslib.Algorithms.Lean.VertexCover.greedyMatching`: the greedy maximal matching.
* `Cslib.Algorithms.Lean.VertexCover.matchingCover`: its endpoints, the returned cover.
* `Cslib.Algorithms.Lean.VertexCover.coverStep`: the scan step tracking only matched vertices.

## Main results

* `isVertexCover_matchingCover`: the returned vertices cover every edge.
* `nodup_matchingCover`, `mem_matchingCover`: the returned vertices are distinct endpoints of
  listed edges.
* `matchingCover_eq_foldl_coverStep`: the cover is a single scan tracking only matched vertices.
* `length_le_encard_of_isVertexCover`: a matching has at most as many edges as any vertex cover
  has vertices.
* `length_matchingCover_le_two_mul_encard`, `length_matchingCover_le_two_mul_card`,
  `length_matchingCover_le_two_mul_vertexCoverNum`: the returned cover has at most twice as many
  vertices as any vertex cover, in particular a minimum one.

## References

* [T. H. Cormen, C. E. Leiserson, R. L. Rivest and C. Stein, *Introduction to
  Algorithms*][CLRS2009], Section 35.1.
-/

public section

namespace Cslib.Algorithms.Lean.VertexCover

variable {V : Type*}

/-! ### The algorithm -/

/-- The endpoints of a list of edges, in order: `[u₁, v₁, u₂, v₂, …]`. -/
@[expose] def endpoints : List (V × V) → List V
  | [] => []
  | e :: M => e.1 :: e.2 :: endpoints M

section Endpoints

/-- A vertex is an endpoint of `M` when it is an endpoint of some edge of `M`. -/
theorem mem_endpoints {M : List (V × V)} {v : V} :
    v ∈ endpoints M ↔ ∃ e ∈ M, v = e.1 ∨ v = e.2 := by
  induction M with
  | nil => simp [endpoints]
  | cons e M ih =>
    simp only [endpoints, List.mem_cons, ih, exists_eq_or_imp, or_assoc]

/-- Each edge contributes two endpoints. -/
theorem length_endpoints (M : List (V × V)) : (endpoints M).length = 2 * M.length := by
  induction M with
  | nil => rfl
  | cons e M ih =>
    simp only [endpoints, List.length_cons, ih]
    omega

/-- `endpoints` distributes over concatenation. -/
theorem endpoints_append (M N : List (V × V)) :
    endpoints (M ++ N) = endpoints M ++ endpoints N := by
  induction M with
  | nil => rfl
  | cons e M ih => simp only [List.cons_append, endpoints, ih]

/-- `endpoints` is monotone for list containment. -/
theorem endpoints_subset_of_subset {M N : List (V × V)} (h : M ⊆ N) :
    endpoints M ⊆ endpoints N := fun v hv => by
  obtain ⟨e, he, hv⟩ := mem_endpoints.1 hv
  exact mem_endpoints.2 ⟨e, h he, hv⟩

end Endpoints

variable [DecidableEq V]

/-- One step of the greedy matching: keep the edge `e` when its endpoints are distinct and both
unmatched by `M`. Kept edges are appended, so the matching lists them in scan order. -/
@[expose] def matchingStep (M : List (V × V)) (e : V × V) : List (V × V) :=
  if e.1 ≠ e.2 ∧ e.1 ∉ endpoints M ∧ e.2 ∉ endpoints M then M ++ [e] else M

/-- **Greedy maximal matching**: scan the edges once, keeping each edge whose endpoints are
distinct and not yet matched. -/
@[expose] def greedyMatching (es : List (V × V)) : List (V × V) :=
  es.foldl matchingStep []

/-- **The matching cover**: both endpoints of every edge of the greedy maximal matching. -/
@[expose] def matchingCover (es : List (V × V)) : List V :=
  endpoints (greedyMatching es)

/-- One step of the scan that tracks only the matched vertices `C`: add both endpoints of `e` when
they are distinct and unmatched. -/
@[expose] def coverStep (C : List V) (e : V × V) : List V :=
  if e.1 ≠ e.2 ∧ e.1 ∉ C ∧ e.2 ∉ C then C ++ [e.1, e.2] else C

/-! ### Invariants of the greedy scan -/

/-- The scan only adds edges: the initial matching is contained in the final one. -/
theorem subset_foldl_matchingStep (es : List (V × V)) (M : List (V × V)) :
    M ⊆ es.foldl matchingStep M := by
  induction es generalizing M with
  | nil => exact List.Subset.refl M
  | cons e es ih =>
    refine List.Subset.trans ?_ (ih _)
    unfold matchingStep
    split_ifs
    · exact List.subset_append_left M [e]
    · exact List.Subset.refl M

/-- The scan keeps the endpoints of the matching distinct. -/
theorem nodup_endpoints_foldl_matchingStep (es : List (V × V)) {M : List (V × V)}
    (hM : (endpoints M).Nodup) : (endpoints (es.foldl matchingStep M)).Nodup := by
  induction es generalizing M with
  | nil => exact hM
  | cons e es ih =>
    refine ih ?_
    unfold matchingStep
    split_ifs with h
    · obtain ⟨hne, h1, h2⟩ := h
      rw [endpoints_append, List.perm_append_comm.nodup_iff]
      simp only [endpoints, List.cons_append, List.nil_append, List.nodup_cons, List.mem_cons,
        not_or]
      exact ⟨⟨hne, h1⟩, h2, hM⟩
    · exact hM

/-- Every edge of the final matching is in the initial matching or is a listed edge with distinct
endpoints. -/
theorem mem_foldl_matchingStep (es : List (V × V)) {M : List (V × V)} {e : V × V}
    (he : e ∈ es.foldl matchingStep M) : e ∈ M ∨ (e ∈ es ∧ e.1 ≠ e.2) := by
  induction es generalizing M with
  | nil => exact Or.inl he
  | cons f es ih =>
    rcases ih he with h | h
    · unfold matchingStep at h
      split_ifs at h with hf
      · rcases List.mem_append.1 h with h | h
        · exact Or.inl h
        · rw [List.mem_singleton.1 h]
          exact Or.inr ⟨List.mem_cons_self, hf.1⟩
      · exact Or.inl h
    · exact Or.inr ⟨List.mem_cons_of_mem _ h.1, h.2⟩

/-- **Maximality.** Every listed edge with distinct endpoints meets the final matching. -/
theorem exists_endpoint_mem_foldl_matchingStep (es : List (V × V)) (M : List (V × V))
    {e : V × V} (he : e ∈ es) (hne : e.1 ≠ e.2) :
    e.1 ∈ endpoints (es.foldl matchingStep M) ∨ e.2 ∈ endpoints (es.foldl matchingStep M) := by
  induction es generalizing M with
  | nil => simp at he
  | cons f es ih =>
    rcases List.mem_cons.1 he with rfl | he
    · have hsub := endpoints_subset_of_subset (subset_foldl_matchingStep es (matchingStep M e))
      simp only [List.foldl_cons]
      by_cases h : e.1 ∈ endpoints M ∨ e.2 ∈ endpoints M
      · have hstep : endpoints M ⊆ endpoints (matchingStep M e) := by grind [matchingStep]
        exact h.imp (fun h => hsub (hstep h)) (fun h => hsub (hstep h))
      · rw [not_or] at h
        have : matchingStep M e = M ++ [e] := ite_eq_left ⟨hne, h.1, h.2⟩
        left
        apply hsub
        rw [this, endpoints_append]
        exact List.mem_append_right _ List.mem_cons_self
    · exact ih _ he

/-- Scanning with `matchingStep` and taking endpoints is scanning with `coverStep`. -/
theorem endpoints_foldl_matchingStep (es : List (V × V)) (M : List (V × V)) :
    endpoints (es.foldl matchingStep M) = es.foldl coverStep (endpoints M) := by
  induction es generalizing M with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons]
    rw [ih]
    congr 1
    unfold matchingStep coverStep
    split_ifs <;> simp only [endpoints_append, endpoints]

/-- The matching cover is computed by the scan that tracks only the matched vertices. -/
theorem matchingCover_eq_foldl_coverStep (es : List (V × V)) :
    matchingCover es = es.foldl coverStep [] :=
  endpoints_foldl_matchingStep es []

/-- The returned vertices are distinct, so the returned list has the cover's size. -/
theorem nodup_matchingCover (es : List (V × V)) : (matchingCover es).Nodup :=
  nodup_endpoints_foldl_matchingStep es List.nodup_nil

/-- The greedy matching consists of listed edges with distinct endpoints. -/
theorem mem_greedyMatching {es : List (V × V)} {e : V × V} (he : e ∈ greedyMatching es) :
    e ∈ es ∧ e.1 ≠ e.2 :=
  (mem_foldl_matchingStep es he).resolve_left List.not_mem_nil

/-- The returned vertices are endpoints of listed edges. -/
theorem mem_matchingCover {es : List (V × V)} {v : V} (hv : v ∈ matchingCover es) :
    ∃ e ∈ es, v = e.1 ∨ v = e.2 := by
  obtain ⟨e, he, hv⟩ := mem_endpoints.1 hv
  exact ⟨e, (mem_greedyMatching he).1, hv⟩

/-! ### Correctness and the factor 2 -/

/-- **Feasibility.** The matching cover is a vertex cover. -/
theorem isVertexCover_matchingCover (es : List (V × V)) :
    (SimpleGraph.fromRel fun u v => (u, v) ∈ es).IsVertexCover
      {v | v ∈ matchingCover es} := by
  intro u v huv
  rw [SimpleGraph.fromRel_adj] at huv
  obtain ⟨hne, he | he⟩ := huv
  · exact exists_endpoint_mem_foldl_matchingStep es [] he hne
  · exact (exists_endpoint_mem_foldl_matchingStep es [] he hne.symm).symm

omit [DecidableEq V] in
/-- **The matching lower bound.** A list of edges of `G` with pairwise distinct endpoints has at
most as many edges as any vertex cover of `G` has vertices: each edge has an endpoint in the cover,
and distinct edges have distinct endpoints. -/
theorem length_le_encard_of_isVertexCover {G : SimpleGraph V} {M : List (V × V)}
    (hM : (endpoints M).Nodup) (hadj : ∀ e ∈ M, G.Adj e.1 e.2) {c : Set V}
    (hc : G.IsVertexCover c) : (M.length : ℕ∞) ≤ c.encard := by
  suffices h : (M.length : ℕ∞) ≤ (c ∩ {v | v ∈ endpoints M}).encard from
    h.trans (Set.encard_le_encard Set.inter_subset_left)
  induction M with
  | nil => simp
  | cons e M ih =>
    simp only [endpoints, List.nodup_cons, List.mem_cons, not_or] at hM
    obtain ⟨⟨-, h1⟩, h2, hM⟩ := hM
    have ih := ih hM fun f hf => hadj f (List.mem_cons_of_mem _ hf)
    obtain ⟨x, hxc, hx, hxM⟩ : ∃ x ∈ c, (x = e.1 ∨ x = e.2) ∧ x ∉ endpoints M := by
      rcases hc (hadj e List.mem_cons_self) with h | h
      · exact ⟨e.1, h, Or.inl rfl, h1⟩
      · exact ⟨e.2, h, Or.inr rfl, h2⟩
    have hsub : insert x (c ∩ {v | v ∈ endpoints M}) ⊆ c ∩ {v | v ∈ endpoints (e :: M)} := by
      intro v hv
      rcases hv with rfl | ⟨hvc, hvM⟩
      · refine ⟨hxc, ?_⟩
        simp only [endpoints, Set.mem_ofPred_eq, List.mem_cons]
        tauto
      · refine ⟨hvc, ?_⟩
        simp only [endpoints, Set.mem_ofPred_eq, List.mem_cons]
        exact Or.inr (Or.inr hvM)
    calc ((e :: M).length : ℕ∞) = (M.length : ℕ∞) + 1 := by simp
      _ ≤ (c ∩ {v | v ∈ endpoints M}).encard + 1 := by gcongr
      _ = (insert x (c ∩ {v | v ∈ endpoints M})).encard :=
          (Set.encard_insert_of_notMem fun h : x ∈ c ∩ {v | v ∈ endpoints M} => hxM h.2).symm
      _ ≤ (c ∩ {v | v ∈ endpoints (e :: M)}).encard := Set.encard_le_encard hsub

/-- **The factor 2 against any cover.** The matching cover has at most twice as many vertices as
any vertex cover. -/
theorem length_matchingCover_le_two_mul_encard (es : List (V × V)) {c : Set V}
    (hc : (SimpleGraph.fromRel fun u v => (u, v) ∈ es).IsVertexCover c) :
    ((matchingCover es).length : ℕ∞) ≤ 2 * c.encard := by
  have hM := length_le_encard_of_isVertexCover (nodup_matchingCover es)
    (fun e he => by
      obtain ⟨he, hne⟩ := mem_greedyMatching he
      rw [SimpleGraph.fromRel_adj]
      exact ⟨hne, Or.inl he⟩) hc
  rw [matchingCover, length_endpoints, Nat.cast_mul, Nat.cast_ofNat]
  exact mul_le_mul_right hM 2

/-- **The factor 2 against any finite cover.** -/
theorem length_matchingCover_le_two_mul_card (es : List (V × V)) {c : Finset V}
    (hc : (SimpleGraph.fromRel fun u v => (u, v) ∈ es).IsVertexCover c) :
    (matchingCover es).length ≤ 2 * c.card := by
  have h := length_matchingCover_le_two_mul_encard es hc
  rw [Set.encard_coe_eq_coe_finsetCard] at h
  exact_mod_cast h

/-- **The maximal-matching 2-approximation**: the matching cover has at most twice the minimum
number of vertices in a vertex cover. -/
theorem length_matchingCover_le_two_mul_vertexCoverNum (es : List (V × V)) :
    ((matchingCover es).length : ℕ∞) ≤
      2 * (SimpleGraph.fromRel fun u v => (u, v) ∈ es).vertexCoverNum := by
  obtain ⟨c, hcard, hc⟩ := (SimpleGraph.fromRel fun u v => (u, v) ∈ es).vertexCoverNum_exists
  rw [← hcard]
  exact length_matchingCover_le_two_mul_encard es hc

end Cslib.Algorithms.Lean.VertexCover
