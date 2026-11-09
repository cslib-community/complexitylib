/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate (Mathlib, dominating sets and private neighbors)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.Order.Minimal

/-!
# Inclusion-minimal dominating sets and private-neighbor markings

A dominating set is inclusion-minimal exactly when each of its vertices has a private closed
neighbor. Valid private-neighbor markings may mark several private neighbors of the same selected
vertex; these markings are not unique certificates. This is the interpretation of
[ChenJiangZhu2027], Proposition 7.6 / Appendix D.3 (PDF pp. 27, 34–35).

## Main results

* `SimpleGraph.minimal_dominatingSet_iff`: private-neighbor characterization of inclusion
  minimality.
* `SimpleGraph.exists_privateMarking_iff`: markings decide minimal domination, without asserting
  one marking per original set.
-/

public section

namespace SimpleGraph

variable {V : Type*}

/-- Adjacency in the closed neighborhood, including the vertex itself. -/
@[expose] def ClosedAdj (G : SimpleGraph V) (w u : V) : Prop := w = u ∨ G.Adj w u

instance (G : SimpleGraph V) [DecidableEq V] [DecidableRel G.Adj] : DecidableRel G.ClosedAdj :=
  fun w u => inferInstanceAs (Decidable (w = u ∨ G.Adj w u))

/-- Closed neighborhood membership is symmetric in an undirected graph. -/
theorem ClosedAdj.symm {G : SimpleGraph V} {u v : V} (h : G.ClosedAdj u v) : G.ClosedAdj v u :=
  h.imp Eq.symm (fun h => h.symm)

/-- Every vertex has a selected closed neighbor. -/
@[expose] def IsDominatingSet (G : SimpleGraph V) (S : Set V) : Prop :=
  ∀ w, ∃ u ∈ S, G.ClosedAdj w u

/-- The selected vertex is the unique selected member of a closed neighborhood. -/
@[expose] def IsPrivateNeighbor (G : SimpleGraph V) (S : Set V) (w u : V) : Prop :=
  u ∈ S ∧ G.ClosedAdj w u ∧ ∀ v ∈ S, G.ClosedAdj w v → v = u

open Classical in
/-- Minimality is inclusion minimality among dominating sets, not minimum cardinality. -/
theorem minimal_dominatingSet_iff (G : SimpleGraph V) (S : Set V) :
    Minimal G.IsDominatingSet S ↔ G.IsDominatingSet S ∧
      ∀ u ∈ S, ∃ w, G.IsPrivateNeighbor S w u := by
  constructor
  · intro hm
    refine ⟨hm.1, ?_⟩
    intro u hu
    by_contra hnone
    have hd : G.IsDominatingSet (S \ {u}) := by
      intro w
      obtain ⟨v, hv, hwv⟩ := hm.1 w
      by_cases hne : v ≠ u
      · exact ⟨v, ⟨hv, hne⟩, hwv⟩
      · have hvu : v = u := by tauto
        subst v
        have hex : ∃ v ∈ S, G.ClosedAdj w v ∧ v ≠ u := by
          by_contra hn
          apply hnone
          refine ⟨w, hu, hwv, ?_⟩
          intro v hv hw
          by_contra hne
          exact hn ⟨v, hv, hw, hne⟩
        obtain ⟨v, hv, hw, hne⟩ := hex
        exact ⟨v, ⟨hv, hne⟩, hw⟩
    have hh := hm.2 hd (Set.sdiff_subset : S \ {u} ⊆ S) hu
    exact hh.2 (Set.mem_singleton u)
  · rintro ⟨hd, hp⟩
    refine ⟨hd, ?_⟩
    intro T hT hTS u hu
    obtain ⟨w, _, hwu, huniq⟩ := hp u hu
    obtain ⟨v, hv, hwv⟩ := hT w
    have he := huniq v (hTS hv) hwv
    simpa only [he] using hv

/-- Source set–marking pairs: domination, at most one selected closed neighbor per mark, and a
marked private-neighbor candidate for every selected vertex. No owner labels are counted. -/
@[expose] def IsPrivateMarking (G : SimpleGraph V) (S W : Set V) : Prop :=
  G.IsDominatingSet S ∧
    (∀ w ∈ W, ∀ u ∈ S, ∀ v ∈ S, G.ClosedAdj w u → G.ClosedAdj w v → u = v) ∧
    ∀ u ∈ S, ∃ w ∈ W, G.ClosedAdj u w

open Classical in
/-- A valid marking exists exactly for an inclusion-minimal dominating set. The canonical
existence proof marks all private neighbors, while the encoded count allows other valid markings. -/
theorem exists_privateMarking_iff (G : SimpleGraph V) (S : Set V) :
    (∃ W, G.IsPrivateMarking S W) ↔ Minimal G.IsDominatingSet S := by
  rw [minimal_dominatingSet_iff]
  constructor
  · rintro ⟨W, hd, hupper, hcover⟩
    refine ⟨hd, ?_⟩
    intro u hu
    obtain ⟨w, hw, huw⟩ := hcover u hu
    exact ⟨w, hu, huw.symm, fun v hv hwv => (hupper w hw u hu v hv huw.symm hwv).symm⟩
  · rintro ⟨hd, hp⟩
    let W := {w | ∃ u, G.IsPrivateNeighbor S w u}
    refine ⟨W, hd, ?_, ?_⟩
    · rintro w ⟨owner, _, _, huniq⟩ u hu v hv hwu hwv
      exact (huniq u hu hwu).trans (huniq v hv hwv).symm
    · intro u hu
      obtain ⟨w, hw⟩ := hp u hu
      exact ⟨w, ⟨u, hw⟩, hw.2.1.symm⟩

end SimpleGraph
