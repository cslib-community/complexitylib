/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Algorithms.Lean.MaxFlow.Decomposition
public import CslibFrontier.Foundations.Combinatorics.Digraph.Connectivity
public import CslibFrontier.Foundations.Combinatorics.Multidigraph.Connectivity
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import CslibFrontier.Foundations.Combinatorics.SimpleGraph.Connectivity.VertexConnectivity
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators

/-!
# Menger's Theorem via Integral Max-Flow/Min-Cut

Derives finite forms of **Menger's theorem** ([Menger1927]) from the integral max-flow/min-cut
theorem `Cslib.Algorithms.Lean.MaxFlow.Network.exists_maxFlow_eq_minCut` and flow path
decomposition (`Cslib.Algorithms.Lean.MaxFlow.Network.Flow.exists_flowPaths`). Pure graph
notions (`Digraph.IsDipath`, `Digraph.ArcDisjoint`, `Digraph.InternallyDisjoint`,
`Digraph.IsArcCut`, `Digraph.IsVertexCut`, `Digraph.outArcs`, `Cslib.Multidigraph.IsDipath`,
`Cslib.Multidigraph.IsArcCut`, `Cslib.Multidigraph.outArcs`, `SimpleGraph.IsVertexSeparator`,
`SimpleGraph.InternallyDisjoint`, `SimpleGraph.IsVertexConnected`) live in
`CslibFrontier.Foundations.Combinatorics`.

## Main results

* **Integral-capacity path packing & directed multidigraphs:**
  `exists_arcCap_eq_cutCapacity`, `exists_arcCap_iff_forall_isCut`,
  `exists_multidigraph_arcDisjoint_eq_outArcs`,
  `exists_multidigraph_arcDisjoint_iff_forall_isArcCut` ([Schrijver2017], §4.1, Corollary 4.1b
  for directed multigraphs and Theorem 4.2 remark for integer capacities).
* **Two-terminal directed forms** ([Schrijver2017], §4.1, Corollaries 4.1b and 4.1a):
  `exists_arcDisjoint_iff_forall_isArcCut`, `exists_arcDisjoint_eq_outArcs`,
  `exists_internallyDisjoint_iff_forall_isVertexCut`, `exists_internallyDisjoint_eq_isVertexCut`.
* **Two-terminal undirected forms** ([Diestel2025], Corollary 3.3.5):
  `isEdgeReachable_iff_exists_edgeDisjoint`, `exists_edgeDisjoint_eq_not_reachable`,
  `exists_internallyDisjoint_iff_forall_isVertexSeparator`,
  `exists_internallyDisjoint_eq_isVertexSeparator`.
* **Set-to-set `A`–`B` vertex Menger** ([Schrijver2017], §4.1, Theorem 4.1; [Diestel2025],
  Theorem 3.3.1): `exists_vertexDisjoint_eq_isSeparator`,
  `exists_vertexDisjoint_iff_forall_isSeparator` (directed), and
  `exists_disjoint_walk_eq_isSeparator`, `exists_disjoint_walk_iff_forall_isSeparator`
  (undirected).
* **Global `k`-connectivity forms** ([Diestel2025], Theorem 3.3.6 and `κ ≤ λ`):
  `isVertexConnected_iff_forall_exists_injective_internallyDisjoint`,
  `isVertexConnected_iff_of_nontrivial`, `isVertexConnected_iff_forall_exists_finset`,
  `isEdgeConnected_iff_forall_exists_edgeDisjoint`,
  `isEdgeConnected_iff_forall_ne_exists_injective_edgeDisjoint`, and
  `isEdgeConnected_of_isVertexConnected`.

## Scope

Finite graphs, finite multidigraphs, and integral capacities only. Infinite graphs (Erdős–Menger)
and `TimeM` connectivity solvers are not covered here.

## References

* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017], §4.1
* [R. Diestel, *Graph Theory*][Diestel2025], §1.4 and §3.3
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

section PathLemmas

variable {V : Type*}

private theorem pathArcs_eq_zip_tail : ∀ p : List V, pathArcs p = p.zip p.tail
  | [] => rfl
  | [_] => rfl
  | u :: v :: rest => by
    rw [pathArcs_cons_cons, List.tail_cons, List.zip_cons_cons, pathArcs_eq_zip_tail (v :: rest),
      List.tail_cons]

/-- If every list in a family avoids `v` as its head and every arc `(u, v)` lies on at most
`c u v` of the lists, then at most `∑ u, c u v` of the lists visit `v`. -/
private theorem card_filter_mem_le_sum [Fintype V] [DecidableEq V] {k : ℕ} (P : Fin k → List V)
    (v : V) (hhead : ∀ i, (P i).head? ≠ some v) (c : V → V → ℕ)
    (hc : ∀ u, (Finset.univ.filter fun i => (u, v) ∈ pathArcs (P i)).card ≤ c u v) :
    (Finset.univ.filter fun i => v ∈ P i).card ≤ ∑ u, c u v := by
  calc (Finset.univ.filter fun i => v ∈ P i).card
      ≤ (Finset.univ.biUnion fun u =>
          Finset.univ.filter fun i => (u, v) ∈ pathArcs (P i)).card := by
        refine Finset.card_le_card fun i hi => ?_
        rw [Finset.mem_filter] at hi
        obtain ⟨u, hu⟩ := exists_mem_pathArcs_snd_eq hi.2 (hhead i)
        exact Finset.mem_biUnion.mpr ⟨u, Finset.mem_univ _, by simp [hu]⟩
    _ ≤ ∑ u, (Finset.univ.filter fun i => (u, v) ∈ pathArcs (P i)).card :=
        Finset.card_biUnion_le
    _ ≤ ∑ u, c u v := Finset.sum_le_sum fun u _ => hc u

end PathLemmas

/-! ### Integral-capacity path packing and directed Menger -/

section Directed

variable {V : Type*}

/-- The support digraph of a network: arcs of positive capacity. -/
@[expose] def Network.posCapDigraph (N : Network V) : Digraph V where
  Adj u v := 0 < N.cap u v

instance instDecidableRelPosCapDigraph (N : Network V) : DecidableRel N.posCapDigraph.Adj :=
  fun u v => inferInstanceAs (Decidable (0 < N.cap u v))

section CapAndArc

variable [Fintype V] [DecidableEq V]

/-- Integral max-flow/min-cut packaged as capacity-respecting simple paths without antiparallel
overlap. -/
private theorem exists_cap_flowPaths (N : Network V) (hst : N.s ≠ N.t) :
    ∃ S : Finset V, N.IsCut S ∧
      ∃ P : Fin (N.cutCapacity S) → List V,
        (∀ i, N.posCapDigraph.IsDipath N.s N.t (P i)) ∧
        (∀ u v,
          (Finset.univ.filter fun i => (u, v) ∈ (P i).zip (P i).tail).card ≤ N.cap u v) ∧
        ∀ i j a b, (a, b) ∈ (P i).zip (P i).tail → (b, a) ∉ (P j).zip (P j).tail := by
  obtain ⟨f₀, S, -, hScut, hval⟩ := Network.exists_maxFlow_eq_minCut (N := N) hst
  have hval' : f₀.cancel.value = (N.cutCapacity S : ℤ) := by
    rw [Network.Flow.value_cancel, hval]
  obtain ⟨P, hP, hcount⟩ := f₀.cancel.exists_flowPaths
  have hk : f₀.cancel.value.toNat = N.cutCapacity S := by omega
  have hcap : ∀ u v, f₀.cancel u v ≤ N.cap u v := fun u v => f₀.cancel.le_cap u v
  refine ⟨S, hScut.1, fun i => P (Fin.cast hk.symm i), fun i => ?_, fun u v => ?_, fun i j a b =>
      ?_⟩
  · obtain ⟨hnd, hs, ht, hpos⟩ := hP (Fin.cast hk.symm i)
    refine ⟨hnd, hs, ht, Digraph.isChain_iff_forall_mem_zip_tail.mpr fun e he => ?_⟩
    rw [← pathArcs_eq_zip_tail] at he
    exact lt_of_lt_of_le (hpos e he) (hcap e.1 e.2)
  · have hle : (Finset.univ.filter fun i : Fin (N.cutCapacity S) =>
        (u, v) ∈ (P (Fin.cast hk.symm i)).zip (P (Fin.cast hk.symm i)).tail).card ≤
        (Finset.univ.filter fun l => (u, v) ∈ pathArcs (P l)).card := by
      refine Finset.card_le_card_of_injOn (Fin.cast hk.symm) (fun i hi => ?_)
        fun i _ j _ h => Fin.cast_injective _ h
      rw [Finset.mem_coe, Finset.mem_filter] at hi ⊢
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [pathArcs_eq_zip_tail]
      exact hi.2
    exact hle.trans ((hcount u v).trans (hcap u v))
  · intro hab hba
    rw [← pathArcs_eq_zip_tail] at hab hba
    have h1 := (hP (Fin.cast hk.symm i)).2.2.2 _ hab
    have h2 := (hP (Fin.cast hk.symm j)).2.2.2 _ hba
    rcases f₀.cancel_eq_zero_or a b with h | h
    · simp only at h1; omega
    · simp only at h2; omega

omit [Fintype V] [DecidableEq V] in
/-- **Weak duality for capacity-constrained paths**: if `k` simple `s`–`t` paths use each arc
`(u, v)` at most `N.cap u v` times, then `k` is at most the capacity of any `s`–`t` cut `S`. -/
theorem card_le_cutCapacity_of_cap [Fintype V] [DecidableEq V] {N : Network V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, N.posCapDigraph.IsDipath N.s N.t (P i))
    (hcap : ∀ u v,
      (Finset.univ.filter fun i => (u, v) ∈ (P i).zip (P i).tail).card ≤ N.cap u v)
    {S : Finset V} (hS : N.IsCut S) : k ≤ N.cutCapacity S := by
  have hbd : ∀ i, ∃ e ∈ (P i).zip (P i).tail, e.1 ∈ S ∧ e.2 ∉ S := by
    intro i
    obtain ⟨_, hps, hpt, _⟩ := hP i
    obtain ⟨e, he, heS, heS'⟩ := exists_mem_pathArcs_boundary (· ∈ S) hps hpt hS.1 hS.2
    exact ⟨e, pathArcs_eq_zip_tail (P i) ▸ he, heS, heS'⟩
  choose e he heS heS' using hbd
  calc k = (Finset.univ : Finset (Fin k)).card := (Finset.card_fin k).symm
    _ ≤ (S.biUnion fun u => (Finset.univ \ S).biUnion fun v =>
          Finset.univ.filter fun i => (u, v) ∈ (P i).zip (P i).tail).card := by
        refine Finset.card_le_card fun i _ => ?_
        refine Finset.mem_biUnion.mpr ⟨(e i).1, heS i, ?_⟩
        refine Finset.mem_biUnion.mpr ⟨(e i).2, Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, heS' i⟩,
          ?_⟩
        simpa using he i
    _ ≤ ∑ u ∈ S, ∑ v ∈ Finset.univ \ S,
          (Finset.univ.filter fun i => (u, v) ∈ (P i).zip (P i).tail).card :=
        Finset.card_biUnion_le.trans (Finset.sum_le_sum fun _ _ => Finset.card_biUnion_le)
    _ ≤ ∑ u ∈ S, ∑ v ∈ Finset.univ \ S, N.cap u v :=
        Finset.sum_le_sum fun u _ => Finset.sum_le_sum fun v _ => hcap u v
    _ = N.cutCapacity S := rfl

/-- **Integral-capacity path packing** ([Schrijver2017], §4.1/Theorem 4.2 remark): for `N.s ≠ N.t`,
there exist an `s`–`t` cut `S` and `N.cutCapacity S` simple `s`–`t` paths along positive-capacity
arcs using each arc `(u, v)` at most `N.cap u v` times. -/
theorem exists_arcCap_eq_cutCapacity (N : Network V) (hst : N.s ≠ N.t) :
    ∃ S : Finset V, N.IsCut S ∧
      ∃ P : Fin (N.cutCapacity S) → List V,
        (∀ i, N.posCapDigraph.IsDipath N.s N.t (P i)) ∧
        ∀ u v,
          (Finset.univ.filter fun i => (u, v) ∈ (P i).zip (P i).tail).card ≤ N.cap u v := by
  obtain ⟨S, hS, P, hP, hcap, -⟩ := exists_cap_flowPaths N hst
  exact ⟨S, hS, P, hP, hcap⟩

/-- **Integral-capacity Menger / path-packing characterization**: there exist `k` simple `s`–`t`
paths in `N` using each arc `(u, v)` at most `N.cap u v` times if and only if every `s`–`t` cut
has capacity at least `k`. -/
theorem exists_arcCap_iff_forall_isCut (N : Network V) (k : ℕ) :
    (∃ P : Fin k → List V, (∀ i, N.posCapDigraph.IsDipath N.s N.t (P i)) ∧
      ∀ u v, (Finset.univ.filter fun i => (u, v) ∈ (P i).zip (P i).tail).card ≤ N.cap u v) ↔
      ∀ S : Finset V, N.IsCut S → k ≤ N.cutCapacity S := by
  constructor
  · rintro ⟨P, hP, hcap⟩ S hS
    exact card_le_cutCapacity_of_cap hP hcap hS
  · intro h
    by_cases hst : N.s = N.t
    · refine ⟨fun _ => [N.s], fun _ =>
          ⟨List.nodup_singleton _, rfl, by simp [hst], List.isChain_singleton _⟩, fun u v => ?_⟩
      simp
    · obtain ⟨S, hS, P, hP, hcap⟩ := exists_arcCap_eq_cutCapacity N hst
      have hk : k ≤ N.cutCapacity S := h S hS
      refine ⟨fun i => P (Fin.castLE hk i), fun i => hP _, fun u v => ?_⟩
      have hsub : (Finset.univ.filter fun i : Fin k =>
          (u, v) ∈ (P (Fin.castLE hk i)).zip (P (Fin.castLE hk i)).tail).card ≤
          (Finset.univ.filter fun j : Fin (N.cutCapacity S) =>
          (u, v) ∈ (P j).zip (P j).tail).card := by
        refine Finset.card_le_card_of_injOn (Fin.castLE hk) (fun i hi => ?_)
          fun _ _ _ _ h' => Fin.castLE_injective hk h'
        rw [Finset.mem_coe, Finset.mem_filter] at hi ⊢
        exact ⟨Finset.mem_univ _, hi.2⟩
      exact hsub.trans (hcap u v)

/-- The unit-capacity network of `G` with source `s` and sink `t`. -/
private def unitNetwork (G : Digraph V) [DecidableRel G.Adj] (s t : V) : Network V where
  cap u v := if G.Adj u v then 1 else 0
  s := s
  t := t

private theorem cutCapacity_unitNetwork (G : Digraph V) [DecidableRel G.Adj] (s t : V)
    (S : Finset V) : (unitNetwork G s t).cutCapacity S = (G.outArcs S).card := by
  rw [Digraph.outArcs, Finset.card_filter, Finset.sum_product]
  rfl

/-- Unit-capacity max-flow/min-cut packaged for Menger: arc-disjoint `s`–`t` paths, as many as
the arcs leaving some `s`–`t` cut, with no arc used in both directions. -/
private theorem exists_unit_flowPaths (G : Digraph V) [DecidableRel G.Adj] {s t : V}
    (hst : s ≠ t) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ ∃ P : Fin (G.outArcs S).card → List V,
      (∀ i, G.IsDipath s t (P i)) ∧ Digraph.ArcDisjoint P ∧
      ∀ i j a b, (a, b) ∈ (P i).zip (P i).tail → (b, a) ∉ (P j).zip (P j).tail := by
  obtain ⟨S, hScut, P, hP, hcap, hanti⟩ := exists_cap_flowPaths (unitNetwork G s t) hst
  have hk : (unitNetwork G s t).cutCapacity S = (G.outArcs S).card :=
    cutCapacity_unitNetwork G s t S
  refine ⟨S, hScut.1, hScut.2, fun i => P (Fin.cast hk.symm i), fun i => ?_, ?_, ?_⟩
  · obtain ⟨hnd, hs, ht, hchain⟩ := hP (Fin.cast hk.symm i)
    refine ⟨hnd, hs, ht, ?_⟩
    rw [Digraph.isChain_iff_forall_mem_zip_tail] at hchain ⊢
    intro e he
    have := hchain e he
    change 0 < (unitNetwork G s t).cap e.1 e.2 at this
    simp only [unitNetwork] at this
    split_ifs at this with hadj
    · exact hadj
    · omega
  · intro i j hij e hei hej
    have hne : Fin.cast hk.symm i ≠ Fin.cast hk.symm j := fun h => hij (Fin.cast_injective _ h)
    have hc := hcap e.1 e.2
    have hadj : G.Adj e.1 e.2 := by
      have hchain := (hP (Fin.cast hk.symm i)).2.2.2
      rw [Digraph.isChain_iff_forall_mem_zip_tail] at hchain
      have hpos := hchain e hei
      change 0 < (unitNetwork G s t).cap e.1 e.2 at hpos
      simp only [unitNetwork] at hpos
      split_ifs at hpos with hadj
      · exact hadj
      · omega
    have h2 : 1 < (Finset.univ.filter fun l =>
        (e.1, e.2) ∈ (P l).zip (P l).tail).card :=
      Finset.one_lt_card.mpr ⟨_, by simpa using hei, _, by simpa using hej, hne⟩
    have h1 : (unitNetwork G s t).cap e.1 e.2 = 1 := by simp [unitNetwork, hadj]
    omega
  · intro i j a b hab hba
    exact hanti _ _ a b hab hba

/-- **Menger's theorem, directed arc-disjoint form, with a matching cut** ([Menger1927];
[Schrijver2017], §4.1, Corollary 4.1b): for distinct `s`, `t` there are `(G.outArcs S).card`
pairwise arc-disjoint directed `s`–`t` paths for some `S` with `s ∈ S`, `t ∉ S`. -/
theorem exists_arcDisjoint_eq_outArcs (G : Digraph V) [DecidableRel G.Adj] {s t : V}
    (hst : s ≠ t) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ ∃ P : Fin (G.outArcs S).card → List V,
      (∀ i, G.IsDipath s t (P i)) ∧ Digraph.ArcDisjoint P := by
  obtain ⟨S, hs, ht, P, hP, hdisj, -⟩ := exists_unit_flowPaths G hst
  exact ⟨S, hs, ht, P, hP, hdisj⟩

omit [Fintype V] [DecidableEq V] in
/-- **Menger's theorem, directed arc-disjoint form** ([Menger1927]; [Schrijver2017], §4.1,
Corollary 4.1b): in a finite digraph there are `k` pairwise arc-disjoint directed `s`–`t` paths
if and only if every `s`–`t` arc cut has at least `k` arcs. -/
theorem exists_arcDisjoint_iff_forall_isArcCut [Finite V] (G : Digraph V) (s t : V) (k : ℕ) :
    (∃ P : Fin k → List V, (∀ i, G.IsDipath s t (P i)) ∧ Digraph.ArcDisjoint P) ↔
      ∀ C : Finset (V × V), G.IsArcCut s t C → k ≤ C.card := by
  classical
  have := Fintype.ofFinite V
  constructor
  · rintro ⟨P, hP, hdisj⟩ C hC
    exact Digraph.card_le_card_of_arcDisjoint_of_isArcCut hP hdisj hC
  · intro h
    by_cases hst : s = t
    · subst hst
      refine ⟨fun _ => [s], fun _ => ⟨List.nodup_singleton s, rfl, rfl,
          List.isChain_singleton s⟩, ?_⟩
      intro i j _ e he
      simp at he
    · obtain ⟨S, hs, ht, P, hP, hdisj⟩ := exists_arcDisjoint_eq_outArcs G hst
      have hk : k ≤ (G.outArcs S).card := h _ (Digraph.isArcCut_outArcs G hs ht)
      refine ⟨fun i => P (Fin.castLE hk i), fun i => hP _, fun i j hij => ?_⟩
      exact hdisj fun h' => hij (Fin.castLE_injective hk h')

end CapAndArc

/-- Vertex splitting of `G`: arcs `(u, true) → (v, false)` of capacity `2` for the arcs of `G`, and
splitting arcs `(v, false) → (v, true)` of capacity `1` for `v ≠ s, t`. -/
private def splitNetwork [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj]
    (s t : V) : Network (V × Bool) where
  cap x y :=
    if x.2 = true ∧ y.2 = false ∧ G.Adj x.1 y.1 then 2
    else if x.2 = false ∧ y.2 = true ∧ x.1 = y.1 ∧ x.1 ≠ s ∧ x.1 ≠ t then 1
    else 0
  s := (s, true)
  t := (t, false)

section Split

variable [DecidableEq V] {G : Digraph V} [DecidableRel G.Adj] {s t : V}

private theorem splitNetwork_s : (splitNetwork G s t).s = (s, true) := rfl

private theorem splitNetwork_t : (splitNetwork G s t).t = (t, false) := rfl

private theorem splitNetwork_cap_tf (u v : V) :
    (splitNetwork G s t).cap (u, true) (v, false) = if G.Adj u v then 2 else 0 := by
  simp [splitNetwork]

private theorem splitNetwork_cap_ft (u v : V) :
    (splitNetwork G s t).cap (u, false) (v, true) =
      if u = v ∧ u ≠ s ∧ u ≠ t then 1 else 0 := by
  simp [splitNetwork]

variable [Fintype V]

private theorem split_flow_eq_zero (f : (splitNetwork G s t).Flow) {x y : V × Bool}
    (h : (splitNetwork G s t).cap x y = 0) : f x y = 0 :=
  Nat.eq_zero_of_le_zero (h ▸ f.le_cap x y)

private theorem split_flow_same (f : (splitNetwork G s t).Flow) (u v : V) (b : Bool) :
    f (u, b) (v, b) = 0 :=
  split_flow_eq_zero f (by cases b <;> simp [splitNetwork])

private theorem split_flow_ft_le (f : (splitNetwork G s t).Flow) (v : V) :
    f (v, false) (v, true) ≤ 1 := by
  have := f.le_cap (v, false) (v, true)
  rw [splitNetwork_cap_ft] at this
  split_ifs at this <;> omega

private theorem split_flow_ft_ne (f : (splitNetwork G s t).Flow) {u v : V}
    (h : ¬ (u = v ∧ u ≠ s ∧ u ≠ t)) :
    f (u, false) (v, true) = 0 :=
  split_flow_eq_zero f (by simp [splitNetwork_cap_ft, h])

private theorem split_flow_tf_zero (f : (splitNetwork G s t).Flow) {u v : V} (h : ¬ G.Adj u v) :
    f (u, true) (v, false) = 0 :=
  split_flow_eq_zero f (by simp [splitNetwork_cap_tf, h])

omit [DecidableEq V] in
private theorem sum_split {M : Type*} [AddCommMonoid M] (g : V × Bool → M) :
    ∑ x, g x = ∑ w, g (w, true) + ∑ w, g (w, false) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => Fintype.sum_bool _

private theorem split_conserve (f : (splitNetwork G s t).Flow) (v : V) (b : Bool)
    (hs : (v, b) ≠ (s, true)) (ht : (v, b) ≠ (t, false)) :
    ∑ w, f (w, !b) (v, b) = ∑ w, f (v, b) (w, !b) := by
  have hc := f.conserve (v, b) hs ht
  change ∑ x, f x (v, b) = ∑ y, f (v, b) y at hc
  rw [sum_split, sum_split (fun y => f (v, b) y)] at hc
  cases b <;> simp only [Bool.not_false, Bool.not_true, split_flow_same,
    Finset.sum_const_zero, add_zero, zero_add] at hc ⊢ <;> exact hc

/-- Flow entering the tail copy `(v, false)` all comes from head copies and leaves through the
splitting arc. -/
private theorem split_inflow (f : (splitNetwork G s t).Flow) {v : V} (hvt : v ≠ t) :
    ∑ u, f (u, true) (v, false) = f (v, false) (v, true) := by
  have hc : ∑ u, f (u, true) (v, false) = ∑ w, f (v, false) (w, true) := by
    simpa using split_conserve f v false (by simp) (by simp [hvt])
  rw [hc]
  exact Finset.sum_eq_single v (fun w _ hw => split_flow_ft_ne f fun h => hw h.1.symm) (by simp)

/-- Flow leaving the head copy `(u, true)` all goes to tail copies and enters through the
splitting arc. -/
private theorem split_outflow (f : (splitNetwork G s t).Flow) {u : V} (hus : u ≠ s) :
    ∑ v, f (u, true) (v, false) = f (u, false) (u, true) := by
  have hc : ∑ w, f (w, false) (u, true) = ∑ v, f (u, true) (v, false) := by
    simpa using split_conserve f u true (by simp [hus]) (by simp)
  rw [← hc]
  exact Finset.sum_eq_single u (fun w _ hw => split_flow_ft_ne f fun h => hw h.1) (by simp)

/-- Each arc of `G` carries at most one unit, except possibly a direct arc `s → t`. -/
private theorem split_thru (f : (splitNetwork G s t).Flow) (hadj : ¬ G.Adj s t) (u v : V) :
    f (u, true) (v, false) ≤ 1 := by
  by_cases hvt : v = t
  · by_cases hus : u = s
    · rw [hvt, hus, split_flow_tf_zero f hadj]
      exact Nat.zero_le 1
    · exact (Finset.single_le_sum (f := fun w => f (u, true) (w, false))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ v)).trans
        ((split_outflow f hus).le.trans (split_flow_ft_le f u))
  · exact (Finset.single_le_sum (f := fun w => f (w, true) (v, false))
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ u)).trans
      ((split_inflow f hvt).le.trans (split_flow_ft_le f v))

end Split

/-- **Menger's theorem, directed vertex form, with a matching cut** ([Menger1927];
[Schrijver2017], §4.1, Corollary 4.1a): for distinct `s`, `t` with `¬ G.Adj s t`, there are `m`
pairwise internally disjoint directed `s`–`t` paths and an `s`–`t` vertex cut with `m`
vertices. -/
theorem exists_internallyDisjoint_eq_isVertexCut [Finite V] (G : Digraph V) {s t : V}
    (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ (m : ℕ) (P : Fin m → List V), (∀ i, G.IsDipath s t (P i)) ∧
      Digraph.InternallyDisjoint s t P ∧ ∃ T : Finset V, G.IsVertexCut s t T ∧ T.card = m := by
  classical
  have := Fintype.ofFinite V
  have hst' : (splitNetwork G s t).s ≠ (splitNetwork G s t).t := by
    simp [splitNetwork_s, splitNetwork_t]
  obtain ⟨f, -, hf, -, -⟩ := Network.exists_maxFlow_eq_minCut (splitNetwork G s t) hst'
  have hno := (f.isMaxFlow_iff_not_exists_augmentingPath hst').mp hf
  have hRcut := f.reachableCut_isCut hno
  have hsR : (s, true) ∈ f.reachableCut := hRcut.1
  have htR : (t, false) ∉ f.reachableCut := hRcut.2
  have hval := f.value_eq_cutCapacity_reachableCut hno
  have hprop : ∀ u v, G.Adj u v → (u, true) ∈ f.reachableCut → (v, false) ∈ f.reachableCut := by
    intro u v huv hu
    rw [Network.Flow.mem_reachableCut_iff] at hu ⊢
    refine hu.tail ?_
    have h1 := split_thru f hadj u v
    change 0 < ((splitNetwork G s t).cap (u, true) (v, false) - f (u, true) (v, false)) +
      f (v, false) (u, true)
    simp only [splitNetwork_cap_tf, huv, ↓reduceIte]
    omega
  obtain ⟨T, hT⟩ : ∃ T : Finset V, ∀ v, v ∈ T ↔
      (v, false) ∈ f.reachableCut ∧ (v, true) ∉ f.reachableCut :=
    ⟨Finset.univ.filter fun v => (v, false) ∈ f.reachableCut ∧ (v, true) ∉ f.reachableCut,
      fun v => by simp⟩
  have hsT : s ∉ T := fun h => ((hT s).mp h).2 hsR
  have htT : t ∉ T := fun h => htR ((hT t).mp h).1
  have hTcut : G.IsVertexCut s t T := by
    refine ⟨hsT, htT, fun p ⟨_, hps, hpt, hchain⟩ => ?_⟩
    rw [Digraph.isChain_iff_forall_mem_zip_tail, ← pathArcs_eq_zip_tail] at hchain
    obtain ⟨e, he, hSe, hSe'⟩ := exists_mem_pathArcs_boundary
      (fun v => (v, false) ∈ f.reachableCut ∨ v = s) hps hpt (Or.inr rfl)
      (by rintro (h | h); exacts [htR h, hst h.symm])
    have hna : (e.1, true) ∉ f.reachableCut := fun h => hSe' (Or.inl (hprop _ _ (hchain e he) h))
    refine ⟨e.1, fst_mem_of_mem_pathArcs he, (hT _).mpr ⟨?_, hna⟩⟩
    exact hSe.elim id fun h => absurd (h ▸ hsR) hna
  have hTcap : T.card ≤ (splitNetwork G s t).cutCapacity f.reachableCut := by
    have hsub : T.image (fun v => ((v, false), (v, true))) ⊆
        f.reachableCut ×ˢ (Finset.univ \ f.reachableCut) := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      simpa using (hT v).mp hv
    have hone : ∀ v ∈ T, (splitNetwork G s t).cap (v, false) (v, true) = 1 := by
      grind [splitNetwork_cap_ft]
    calc T.card = ∑ v ∈ T, (splitNetwork G s t).cap (v, false) (v, true) := by
          rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ x ∈ T.image (fun v => ((v, false), (v, true))),
            (splitNetwork G s t).cap x.1 x.2 := by
          rw [Finset.sum_image]
          intro _ _ _ _ h
          simpa using h
      _ ≤ ∑ x ∈ f.reachableCut ×ˢ (Finset.univ \ f.reachableCut),
            (splitNetwork G s t).cap x.1 x.2 :=
          Finset.sum_le_sum_of_subset hsub
      _ = (splitNetwork G s t).cutCapacity f.reachableCut := by
          rw [Finset.sum_product]; rfl
  let g : (unitNetwork G s t).Flow :=
    { toFun := fun u v => f (u, true) (v, false)
      le_cap := fun u v => by
        change f (u, true) (v, false) ≤ if G.Adj u v then 1 else 0
        split_ifs with huv
        · exact split_thru f hadj u v
        · exact (split_flow_tf_zero f huv).le
      conserve := fun v hvs hvt => by
        show ∑ u, f (u, true) (v, false) = ∑ w, f (v, true) (w, false)
        rw [split_inflow f hvt, split_outflow f hvs] }
  have hgval : g.value = f.value := by
    have hout : ∑ y, (f (s, true) y : ℤ) = ∑ w, (f (s, true) (w, false) : ℤ) := by
      rw [sum_split]; simp [split_flow_same]
    have hin : ∑ x, (f x (s, true) : ℤ) = 0 := by
      refine Finset.sum_eq_zero fun ⟨w, b⟩ _ => ?_
      cases b
      · simp [split_flow_ft_ne f (fun h => h.2.1 h.1)]
      · simp [split_flow_same]
    have hin' : ∑ u, (f (u, true) (s, false) : ℤ) = 0 := by
      have h := split_inflow f hst
      rw [split_flow_ft_ne f (fun h => h.2.1 rfl)] at h
      exact_mod_cast h
    change (∑ w, (f (s, true) (w, false) : ℤ)) - ∑ u, (f (u, true) (s, false) : ℤ) =
      (∑ y, (f (s, true) y : ℤ)) - ∑ x, (f x (s, true) : ℤ)
    rw [hout, hin, hin']
  obtain ⟨P, hP, hcount⟩ := g.exists_flowPaths
  have hPdi : ∀ i, G.IsDipath s t (P i) := fun i =>
    ⟨(hP i).1, (hP i).2.1, (hP i).2.2.1, Digraph.isChain_iff_forall_mem_zip_tail.mpr fun e he => by
      rw [← pathArcs_eq_zip_tail] at he
      by_contra hne
      have h1 := (hP i).2.2.2 e he
      change 0 < f (e.1, true) (e.2, false) at h1
      rw [split_flow_tf_zero f hne] at h1
      exact absurd h1 (lt_irrefl 0)⟩
  have hPdisj : Digraph.InternallyDisjoint s t P := by
    intro i j hij v hvi hvj
    by_contra hv
    rw [not_or] at hv
    have hhead : ∀ l, (P l).head? ≠ some v := fun l h =>
      hv.1 (Option.some.inj (h.symm.trans (hP l).2.1))
    have hle := card_filter_mem_le_sum P v hhead (fun u w => g u w) (fun u => hcount u v)
    have h1 : ∑ u, g u v = f (v, false) (v, true) := split_inflow f hv.2
    have h2 := split_flow_ft_le f v
    have h3 : 1 < (Finset.univ.filter fun l => v ∈ P l).card :=
      Finset.one_lt_card.mpr ⟨i, by simpa using hvi, j, by simpa using hvj, hij⟩
    omega
  have hle := Digraph.card_le_card_of_internallyDisjoint_of_isVertexCut hPdi hPdisj hTcut
  refine ⟨g.value.toNat, P, hPdi, hPdisj, T, hTcut, ?_⟩
  omega

/-- **Menger's theorem, directed vertex form** ([Menger1927]; [Schrijver2017], §4.1,
Corollary 4.1a): in a finite digraph there are `k` pairwise internally disjoint directed `s`–`t`
paths if and only if every `s`–`t` vertex cut has at least `k` vertices. -/
theorem exists_internallyDisjoint_iff_forall_isVertexCut [Finite V] (G : Digraph V) (s t : V)
    (k : ℕ) :
    (∃ P : Fin k → List V, (∀ i, G.IsDipath s t (P i)) ∧ Digraph.InternallyDisjoint s t P) ↔
      ∀ T : Finset V, G.IsVertexCut s t T → k ≤ T.card := by
  classical
  have := Fintype.ofFinite V
  constructor
  · rintro ⟨P, hP, hdisj⟩ T hT
    exact Digraph.card_le_card_of_internallyDisjoint_of_isVertexCut hP hdisj hT
  · intro h
    by_cases hst : s = t
    · subst hst
      refine ⟨fun _ => [s], fun _ => ⟨List.nodup_singleton s, rfl, rfl,
          List.isChain_singleton s⟩, ?_⟩
      intro i j _ v hv _
      exact Or.inl (List.mem_singleton.mp hv)
    by_cases hadj : G.Adj s t
    · refine ⟨fun _ => [s, t], fun _ => ⟨by simp [hst], rfl, rfl, by simp [hadj]⟩, ?_⟩
      intro i j _ v hv _
      simpa using hv
    obtain ⟨m, P, hP, hdisj, T, hT, hTm⟩ := exists_internallyDisjoint_eq_isVertexCut G hst hadj
    have hk : k ≤ m := hTm ▸ h T hT
    refine ⟨fun i => P (Fin.castLE hk i), fun i => hP _, fun i j hij => ?_⟩
    exact hdisj fun h' => hij (Fin.castLE_injective hk h')

/-! ### Set-to-set `A`–`B` Menger (directed) -/

/-- Auxiliary supersource/supersink digraph on `Bool ⊕ V`: `inl true` reaches `inr a` (`a ∈ A`),
`inr b` reaches `inl false` (`b ∈ B`), and `inr u` reaches `inr v` along arcs of `G`. -/
private def extDigraph (G : Digraph V) (A B : Set V) : Digraph (Bool ⊕ V) where
  Adj x y := match x, y with
    | .inl true, .inr a => a ∈ A
    | .inr b, .inl false => b ∈ B
    | .inr u, .inr v => G.Adj u v
    | _, _ => False

private theorem isChain_extDigraph_append {G : Digraph V} {A B : Set V} :
    ∀ {p : List V} {b : V}, p ≠ [] → p.getLast? = some b → p.IsChain G.Adj → b ∈ B →
      (p.map Sum.inr ++ [Sum.inl false]).IsChain (extDigraph G A B).Adj
  | [], _, hne, _, _, _ => absurd rfl hne
  | [x], b, _, hlast, _, hb => by
    simp only [List.getLast?_singleton, Option.some.injEq] at hlast
    subst hlast
    simp [extDigraph, hb]
  | x :: y :: rest, b, _, hlast, hchain, hb => by
    rw [List.isChain_cons_cons] at hchain
    have hrec := isChain_extDigraph_append (A := A) (p := y :: rest) (List.cons_ne_nil y rest)
      (by simpa using hlast) hchain.2 hb
    simpa [List.map_cons, extDigraph, hchain.1] using hrec

private theorem unwrap_extDigraph_mid {G : Digraph V} {A B : Set V} :
    ∀ {r : List (Bool ⊕ V)}, r.Nodup → r.getLast? = some (Sum.inl false) →
      r.IsChain (extDigraph G A B).Adj → ∀ {u : V}, r.head? = some (Sum.inr u) →
      ∃ Q : List V, r = Q.map Sum.inr ++ [Sum.inl false] ∧ Q.Nodup ∧ Q.head? = some u ∧
        (∃ b ∈ B, Q.getLast? = some b) ∧ Q.IsChain G.Adj
  | [], _, _, _, _, hhead => by simp at hhead
  | [Sum.inr u], _, hlast, _, _, _ => by simp at hlast
  | [Sum.inl _], _, _, _, _, hhead => by simp at hhead
  | Sum.inl _ :: _, _, _, _, _, hhead => by simp at hhead
  | Sum.inr u :: Sum.inl c :: rest, hnd, hlast, hchain, w, hhead => by
    simp only [List.head?_cons, Option.some.injEq, Sum.inr.injEq] at hhead
    rw [hhead] at hnd hlast hchain ⊢
    rw [List.isChain_cons_cons] at hchain
    rcases c with _ | _
    · have hc := hchain.1
      change w ∈ B at hc
      cases rest with
      | nil =>
        exact ⟨[w], rfl, List.nodup_singleton _, rfl, ⟨w, hc, rfl⟩, List.isChain_singleton _⟩
      | cons z zs =>
        have hstep := (List.isChain_cons_cons.mp hchain.2).1
        exact (by simp [extDigraph] at hstep : False).elim
    · exact (by simp [extDigraph] at hchain : False).elim
  | Sum.inr u :: Sum.inr v :: rest, hnd, hlast, hchain, w, hhead => by
    simp only [List.head?_cons, Option.some.injEq, Sum.inr.injEq] at hhead
    rw [hhead] at hnd hlast hchain ⊢
    rw [List.isChain_cons_cons] at hchain
    have hnd' := (List.nodup_cons.mp hnd).2
    obtain ⟨Q, hQeq, hQnd, hQhead, ⟨b, hbB, hQlast⟩, hQchain⟩ :=
      unwrap_extDigraph_mid hnd' (by simpa using hlast) hchain.2 rfl
    have hwQ : w ∉ Q := by
      intro hmem
      have h1 := (List.nodup_cons.mp hnd).1
      have hmem' : Sum.inr w ∈ Sum.inr v :: rest := by
        rw [hQeq, List.mem_append, List.mem_map]
        exact Or.inl ⟨w, hmem, rfl⟩
      exact h1 hmem'
    refine ⟨w :: Q, by simp [hQeq], List.nodup_cons.mpr ⟨hwQ, hQnd⟩, rfl, ⟨b, hbB, ?_⟩, ?_⟩
    · have hQne : Q ≠ [] := fun h => by rw [h] at hQhead; simp at hQhead
      rwa [List.getLast?_cons_of_ne_nil hQne]
    · rcases Q with _ | ⟨q₀, qs⟩
      · simp at hQhead
      · simp only [List.head?_cons, Option.some.injEq] at hQhead
        subst hQhead
        exact List.isChain_cons_cons.mpr ⟨hchain.1, hQchain⟩

private theorem unwrap_extDigraph_dipath {G : Digraph V} {A B : Set V} {p : List (Bool ⊕ V)}
    (hp : (extDigraph G A B).IsDipath (Sum.inl true) (Sum.inl false) p) :
    ∃ Q : List V, p = Sum.inl true :: (Q.map Sum.inr ++ [Sum.inl false]) ∧
      ∃ a ∈ A, ∃ b ∈ B, G.IsDipath a b Q := by
  obtain ⟨hnd, hhead, hlast, hchain⟩ := hp
  rcases p with _ | ⟨x, r⟩
  · simp at hhead
  · simp only [List.head?_cons, Option.some.injEq] at hhead
    subst hhead
    rcases r with _ | ⟨y, r'⟩
    · simp at hlast
    · rw [List.isChain_cons_cons] at hchain
      rcases y with b | a
      · exact (by cases b <;> simp [extDigraph] at hchain : False).elim
      · have ha : a ∈ A := hchain.1
        obtain ⟨Q, hQeq, hQnd, hQhead, ⟨b, hbB, hQlast⟩, hQchain⟩ :=
          unwrap_extDigraph_mid (List.nodup_cons.mp hnd).2 (by simpa using hlast) hchain.2 rfl
        exact ⟨Q, by simp [hQeq], a, ha, b, hbB, hQnd, hQhead, hQlast, hQchain⟩

/-- **Menger's theorem, directed `A`–`B` vertex-disjoint form, with a matching separator**
([Menger1927]; [Schrijver2017], §4.1, Theorem 4.1): in a finite digraph, for any vertex sets
`A, B : Set V`, there exist `m` pairwise vertex-disjoint simple directed `A`–`B` paths and an
`A`–`B` separator `Y : Finset V` of size `m`. -/
theorem exists_vertexDisjoint_eq_isSeparator [Finite V] (G : Digraph V) (A B : Set V) :
    ∃ (m : ℕ) (P : Fin m → List V),
      (∀ i, ∃ a ∈ A, ∃ b ∈ B, G.IsDipath a b (P i)) ∧
      Pairwise (fun i j => (P i).Disjoint (P j)) ∧
      ∃ Y : Finset V, G.IsSeparator A B ↑Y ∧ Y.card = m := by
  classical
  have := Fintype.ofFinite V
  have hst : (Sum.inl true : Bool ⊕ V) ≠ Sum.inl false := by simp
  have hadj : ¬ (extDigraph G A B).Adj (Sum.inl true) (Sum.inl false) := by simp [extDigraph]
  obtain ⟨m, P₀, hP₀, hdisj₀, T, hTcut, hTm⟩ :=
    exists_internallyDisjoint_eq_isVertexCut (extDigraph G A B) hst hadj
  choose Q hQeq a ha b hb hQ using fun i => unwrap_extDigraph_dipath (hP₀ i)
  let Y : Finset V := Finset.univ.filter fun v => (Sum.inr v : Bool ⊕ V) ∈ T
  have hYcard : Y.card = m := by
    have hmap : Y.map ⟨Sum.inr, Sum.inr_injective⟩ = T := by
      ext x
      rcases x with c | v
      · simp only [Finset.mem_map, Function.Embedding.coeFn_mk, reduceCtorEq, and_false,
          exists_false, false_iff]
        cases c
        · exact hTcut.2.1
        · exact hTcut.1
      · simp [Y]
    rw [← Finset.card_map ⟨Sum.inr, Sum.inr_injective⟩, hmap, hTm]
  have hYsep : G.IsSeparator A B ↑Y := by
    intro u hu v hv p ⟨hpnd, hps, hpt, hpchain⟩
    let p' : List (Bool ⊕ V) := Sum.inl true :: (p.map Sum.inr ++ [Sum.inl false])
    have hpne : p ≠ [] := fun h => by rw [h] at hps; simp at hps
    have hp'nd : p'.Nodup := by
      refine List.nodup_cons.mpr ⟨?_, ?_⟩
      · simp only [List.mem_append, List.mem_map, List.mem_singleton, reduceCtorEq, and_false,
          exists_false, or_false, Sum.inl.injEq, Bool.true_eq_false, not_false_eq_true]
      · refine List.nodup_append.mpr ⟨hpnd.map Sum.inr_injective, List.nodup_singleton _, ?_⟩
        intro z hz1 z' hz2
        rw [List.mem_singleton] at hz2
        rw [List.mem_map] at hz1
        obtain ⟨_, _, rfl⟩ := hz1
        simp [hz2]
    have hp'chain : p'.IsChain (extDigraph G A B).Adj := by
      have htail := isChain_extDigraph_append (G := G) (A := A) hpne hpt hpchain hv
      rcases p with _ | ⟨x, xs⟩
      · exact absurd rfl hpne
      · simp only [List.head?_cons, Option.some.injEq] at hps
        subst hps
        exact List.isChain_cons_cons.mpr ⟨hu, htail⟩
    have hp'last : p'.getLast? = some (Sum.inl false) := by
      change (Sum.inl true :: (p.map Sum.inr ++ [Sum.inl false])).getLast? = some (Sum.inl false)
      rw [List.getLast?_cons_of_ne_nil (by simp), List.getLast?_append]
      simp
    obtain ⟨z, hz, hzT⟩ := hTcut.2.2 p' ⟨hp'nd, rfl, hp'last, hp'chain⟩
    rcases List.mem_cons.mp hz with rfl | hz'
    · exact absurd hzT hTcut.1
    · rcases List.mem_append.mp hz' with hzmap | hzlast
      · obtain ⟨w, hwp, rfl⟩ := List.mem_map.mp hzmap
        exact ⟨w, hwp, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hzT⟩)⟩
      · rw [List.mem_singleton] at hzlast
        subst hzlast
        exact absurd hzT hTcut.2.1
  refine ⟨m, Q, fun i => ⟨a i, ha i, b i, hb i, hQ i⟩, fun i j hij v hvi hvj => ?_,
      Y, hYsep, hYcard⟩
  have hvi' : (Sum.inr v : Bool ⊕ V) ∈ P₀ i := by
    rw [hQeq i]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hvi))
  have hvj' : (Sum.inr v : Bool ⊕ V) ∈ P₀ j := by
    rw [hQeq j]
    exact List.mem_cons_of_mem _ (List.mem_append_left _ (List.mem_map_of_mem hvj))
  rcases hdisj₀ hij (Sum.inr v) hvi' hvj' with h | h <;> simp at h

/-- **Menger's theorem, directed `A`–`B` vertex-disjoint form** ([Menger1927]; [Schrijver2017],
§4.1, Theorem 4.1): in a finite digraph, there are `k` pairwise vertex-disjoint directed `A`–`B`
paths iff every `A`–`B` separator has at least `k` vertices. -/
theorem exists_vertexDisjoint_iff_forall_isSeparator [Finite V] (G : Digraph V)
    (A B : Set V) (k : ℕ) :
    (∃ P : Fin k → List V,
      (∀ i, ∃ a ∈ A, ∃ b ∈ B, G.IsDipath a b (P i)) ∧
      Pairwise fun i j => (P i).Disjoint (P j)) ↔
      ∀ Y : Finset V, G.IsSeparator A B ↑Y → k ≤ Y.card := by
  constructor
  · rintro ⟨P, hP, hdisj⟩ Y hY
    exact Digraph.card_le_card_of_disjoint_of_isSeparator hP hdisj hY
  · intro h
    obtain ⟨m, P, hP, hdisj, Y, hY, hYm⟩ := exists_vertexDisjoint_eq_isSeparator G A B
    have hk : k ≤ m := hYm ▸ h Y hY
    refine ⟨fun i => P (Fin.castLE hk i), fun i => hP _, fun i j hij => ?_⟩
    exact hdisj fun h' => hij (Fin.castLE_injective hk h')

end Directed

/-! ### Multidigraph arc-disjoint Menger -/

section Multidigraph

variable {V E : Type*} (src tgt : E → V)

private noncomputable def multiNetwork [DecidableEq V] [Fintype E]
    (s t : V) : Network V where
  cap u v := (Finset.univ.filter fun e => src e = u ∧ tgt e = v).card
  s := s
  t := t

private theorem cutCapacity_multiNetwork [Fintype V] [DecidableEq V] [Fintype E] (s t : V)
    (S : Finset V) :
    (multiNetwork src tgt s t).cutCapacity S = (Multidigraph.outArcs src tgt S).card := by
  classical
  have hunion : Multidigraph.outArcs src tgt S =
      S.biUnion fun u => (Finset.univ \ S).biUnion fun v =>
        Finset.univ.filter fun e => src e = u ∧ tgt e = v := by
    ext e
    simp only [Multidigraph.mem_outArcs, Finset.mem_biUnion, Finset.mem_sdiff, Finset.mem_univ,
      true_and, Finset.mem_filter]
    exact ⟨fun ⟨hs, ht⟩ => ⟨src e, hs, tgt e, ht, rfl, rfl⟩,
      fun ⟨_, hu, _, hv, h1, h2⟩ => ⟨h1 ▸ hu, h2 ▸ hv⟩⟩
  rw [hunion, Finset.card_biUnion]
  · simp only [Network.cutCapacity, multiNetwork]
    refine Finset.sum_congr rfl fun u _ => (Finset.card_biUnion fun v _ v' _ hne => ?_).symm
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    simp only [Finset.mem_filter] at he he'
    exact hne (he.2.2.symm.trans he'.2.2)
  · intro u _ u' _ hne
    refine Finset.disjoint_left.mpr fun e he he' => ?_
    simp only [Finset.mem_biUnion, Finset.mem_filter] at he he'
    obtain ⟨_, _, _, heu, _⟩ := he
    obtain ⟨_, _, _, heu', _⟩ := he'
    exact hne (heu.symm.trans heu')

private theorem pmap_zip_isDipath_aux {S : V × V → Prop}
    (f : ∀ e, S e → E) (hf : ∀ e (he : S e), src (f e he) = e.1 ∧ tgt (f e he) = e.2) :
    ∀ {p : List V}, p.Nodup →
      ∀ {s t : V}, p.head? = some s → p.getLast? = some t →
      ∀ (hS : ∀ e ∈ p.zip p.tail, S e),
      let q := (p.zip p.tail).pmap f hS
      q.IsChain (fun a b => tgt a = src b) ∧
      (s :: q.map tgt) = p ∧
      (∀ e ∈ q.head?, src e = s) ∧
      (q = [] → s = t) ∧
      (∀ e ∈ q.getLast?, tgt e = t)
  | [], _, s, _, hs, _, _ => by
    simp only [List.head?_nil, reduceCtorEq] at hs
  | [x], _, s, t, hs, ht, hS => by
    simp only [List.head?_cons, Option.some.injEq] at hs
    simp only [List.getLast?_singleton, Option.some.injEq] at ht
    subst hs ht
    refine ⟨List.isChain_nil, rfl, (fun _ h => by cases h), (fun _ => rfl),
      (fun _ h => by cases h)⟩
  | x :: y :: rest', hp, s, t, hs, ht, hS => by
    simp only [List.head?_cons, Option.some.injEq] at hs
    subst hs
    have hnd' := (List.nodup_cons.mp hp).2
    have he0 : (x, y) ∈ (x :: y :: rest').zip (x :: y :: rest').tail := by
      simp only [List.tail_cons, List.zip_cons_cons, List.mem_cons, true_or]
    have he0_eq := hf (x, y) (hS (x, y) he0)
    rcases rest' with _ | ⟨z, zs⟩
    · simp only [List.getLast?_cons_cons, List.getLast?_singleton, Option.some.injEq] at ht
      subst ht
      refine ⟨?_, ?_, ?_, (fun hq => by cases hq), ?_⟩
      · exact List.isChain_singleton _
      · exact congrArg (x :: ·) (congrArg (· :: []) he0_eq.2)
      · intro e he
        change some (f (x, y) _) = some e at he
        cases he
        exact he0_eq.1
      · intro e he
        change some (f (x, y) _) = some e at he
        cases he
        exact he0_eq.2
    · have hlast : (y :: z :: zs).getLast? = some t := by
        simpa only [List.getLast?_cons_cons] using ht
      let hS' : ∀ e ∈ (y :: z :: zs).zip (y :: z :: zs).tail, S e := fun e he =>
        hS e (List.mem_cons_of_mem (x, y) he)
      obtain ⟨hchain', hmap', hhd', _, hlt'⟩ :=
        pmap_zip_isDipath_aux f hf hnd' rfl hlast hS'
      refine ⟨?_, ?_, ?_, (fun hq => by cases hq), ?_⟩
      · have h1 := hhd' (f (y, z) (hS' (y, z) (by simp))) rfl
        exact List.isChain_cons_cons.mpr ⟨he0_eq.2.trans h1.symm, hchain'⟩
      · change x :: tgt (f (x, y) _) ::
          List.map tgt (((y :: z :: zs).zip (y :: z :: zs).tail).pmap f hS') = x :: y :: z :: zs
        rw [he0_eq.2]
        exact congrArg (x :: ·) hmap'
      · intro e he
        change some (f (x, y) _) = some e at he
        cases he
        exact he0_eq.1
      · intro e he
        exact hlt' e he

/-- **Menger's theorem, directed multidigraph arc-disjoint form, with a matching cut**
([Menger1927]; [Schrijver2017], §4.1, Corollary 4.1b for directed multigraphs): for distinct
`s`, `t` in a finite multidigraph `src tgt : E → V`, there are `(outArcs src tgt S).card`
pairwise arc-disjoint simple directed `s`–`t` paths for some `S` with `s ∈ S`, `t ∉ S`. -/
theorem exists_multidigraph_arcDisjoint_eq_outArcs [Finite V] [DecidableEq V] [Fintype E]
    {s t : V} (hst : s ≠ t) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧
      ∃ Q : Fin (Multidigraph.outArcs src tgt S).card → List E,
        (∀ i, Multidigraph.IsDipath src tgt s t (Q i)) ∧
        Pairwise fun i j => (Q i).Disjoint (Q j) := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨S, hS, P, hP, hcap⟩ := exists_arcCap_eq_cutCapacity (multiNetwork src tgt s t) hst
  have hcard : (multiNetwork src tgt s t).cutCapacity S =
      (Multidigraph.outArcs src tgt S).card :=
    cutCapacity_multiNetwork src tgt s t S
  let I : V → V → Finset (Fin ((multiNetwork src tgt s t).cutCapacity S)) := fun u v =>
    Finset.univ.filter fun i => (u, v) ∈ (P i).zip (P i).tail
  let A : V → V → Finset E := fun u v =>
    Finset.univ.filter fun e => src e = u ∧ tgt e = v
  let pick : ∀ u v, ∀ i ∈ I u v, E := fun u v i hi =>
    let eI := (I u v).equivFin
    let eA := (A u v).equivFin.symm
    have hle : (I u v).card ≤ (A u v).card := hcap u v
    (eA (Fin.castLE hle (eI ⟨i, hi⟩))).1
  have hpick_st : ∀ u v i (hi : i ∈ I u v), src (pick u v i hi) = u ∧ tgt (pick u v i hi) = v :=
    fun u v i hi => by
      have hm := ((A u v).equivFin.symm (Fin.castLE (hcap u v) ((I u v).equivFin ⟨i, hi⟩))).2
      simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hm
      exact hm
  have hpick_inj : ∀ u₁ v₁ i₁ hi₁ u₂ v₂ i₂ hi₂,
      pick u₁ v₁ i₁ hi₁ = pick u₂ v₂ i₂ hi₂ → i₁ = i₂ := by
    intro u₁ v₁ i₁ hi₁ u₂ v₂ i₂ hi₂ heq
    have hs₁ := (hpick_st u₁ v₁ i₁ hi₁).1
    have ht₁ := (hpick_st u₁ v₁ i₁ hi₁).2
    have hs₂ := (hpick_st u₂ v₂ i₂ hi₂).1
    have ht₂ := (hpick_st u₂ v₂ i₂ hi₂).2
    have hu : u₁ = u₂ := hs₁.symm.trans (heq ▸ hs₂)
    have hv : v₁ = v₂ := ht₁.symm.trans (heq ▸ ht₂)
    subst hu hv
    have hinj := ((A u₁ v₁).equivFin.symm.injective.comp
      (Fin.castLE_injective (hcap u₁ v₁))).comp (I u₁ v₁).equivFin.injective
    exact congrArg Subtype.val (hinj (Subtype.ext heq))
  let Q₀ : Fin ((multiNetwork src tgt s t).cutCapacity S) → List E := fun i =>
    ((P i).zip (P i).tail).pmap
      (fun e he => pick e.1 e.2 i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩))
      (fun _ he => he)
  refine ⟨S, hS.1, hS.2, fun i => Q₀ (Fin.cast hcard.symm i), fun i => ?_, fun i j hij => ?_⟩
  · obtain ⟨hnd, hps, hpt, _⟩ := hP (Fin.cast hcard.symm i)
    obtain ⟨hc, hm, hhd, hnil, hlt⟩ := pmap_zip_isDipath_aux src tgt
      (fun e (he : e ∈ (P (Fin.cast hcard.symm i)).zip (P (Fin.cast hcard.symm i)).tail) =>
        pick e.1 e.2 (Fin.cast hcard.symm i) (Finset.mem_filter.mpr ⟨Finset.mem_univ _, he⟩))
      (fun e he => hpick_st e.1 e.2 _ _) hnd hps hpt (fun _ he => he)
    exact ⟨hc, hm ▸ hnd, hhd, hnil, hlt⟩
  · intro e hei hej
    simp only [Q₀, List.mem_pmap] at hei hej
    obtain ⟨p₁, hp₁, rfl⟩ := hei
    obtain ⟨p₂, hp₂, heq⟩ := hej
    have hcast := hpick_inj _ _ _ _ _ _ _ _ heq
    exact hij (Fin.cast_injective _ hcast.symm)

/-- **Menger's theorem, directed multidigraph arc-disjoint form** ([Menger1927];
[Schrijver2017], §4.1, Corollary 4.1b for directed multigraphs): in a finite multidigraph
`src tgt : E → V`, there are `k` pairwise arc-disjoint simple directed `s`–`t` paths if and only
if every `s`–`t` arc cut has at least `k` arcs. -/
theorem exists_multidigraph_arcDisjoint_iff_forall_isArcCut [Finite V] [Finite E]
    (s t : V) (k : ℕ) :
    (∃ Q : Fin k → List E, (∀ i, Multidigraph.IsDipath src tgt s t (Q i)) ∧
      Pairwise fun i j => (Q i).Disjoint (Q j)) ↔
      ∀ C : Finset E, Multidigraph.IsArcCut src tgt s t C → k ≤ C.card := by
  classical
  have := Fintype.ofFinite V
  have := Fintype.ofFinite E
  constructor
  · rintro ⟨Q, hQ, hdisj⟩ C hC
    exact Multidigraph.card_le_card_of_disjoint_of_isArcCut src tgt hQ hdisj hC
  · intro h
    by_cases hst : s = t
    · subst hst
      refine ⟨fun _ => [], fun _ => ⟨List.isChain_nil, List.nodup_singleton s,
          fun _ h => by simp at h, fun _ => rfl, fun _ h => by simp at h⟩,
        fun i j _ e he => by simp at he⟩
    · obtain ⟨S, hs, ht, Q, hQ, hdisj⟩ :=
        exists_multidigraph_arcDisjoint_eq_outArcs src tgt hst
      have hk : k ≤ (Multidigraph.outArcs src tgt S).card :=
        h _ (Multidigraph.isArcCut_outArcs src tgt hs ht)
      refine ⟨fun i => Q (Fin.castLE hk i), fun i => hQ _, fun i j hij => ?_⟩
      exact hdisj fun h' => hij (Fin.castLE_injective hk h')

end Multidigraph

/-! ### Undirected Menger, set-to-set and global `k`-connectivity -/

section Undirected

open SimpleGraph

variable {V : Type*}

/-- The symmetric digraph of a simple graph: each edge becomes two opposite arcs. -/
private def toDigraph (G : SimpleGraph V) : Digraph V := ⟨G.Adj⟩

private theorem isDipath_support {G : SimpleGraph V} {u v : V} {w : G.Walk u v}
    (hw : w.IsPath) : (toDigraph G).IsDipath u v w.support := by
  refine ⟨hw.support_nodup, ?_, ?_, w.isChain_adj_support⟩
  · rw [List.head?_eq_some_head (Walk.support_ne_nil w), Walk.head_support]
  · rw [List.getLast?_eq_some_getLast (Walk.support_ne_nil w), Walk.getLast_support]

private theorem exists_walk_of_isDipath {G : SimpleGraph V} {u v : V} {p : List V}
    (hp : (toDigraph G).IsDipath u v p) : ∃ w : G.Walk u v, w.IsPath ∧ w.support = p := by
  obtain ⟨hnd, hu, hv, hchain⟩ := hp
  have hchain' : p.IsChain G.Adj := hchain
  have hne : p ≠ [] := by grind
  have hu' : p.head hne = u := by
    rw [List.head?_eq_some_head hne] at hu
    exact Option.some.inj hu
  have hv' : p.getLast hne = v := by
    rw [List.getLast?_eq_some_getLast hne] at hv
    exact Option.some.inj hv
  refine ⟨(Walk.ofSupport p hne hchain').copy hu' hv', ?_, ?_⟩
  · rw [Walk.isPath_copy]
    exact Walk.IsPath.mk' (by rw [Walk.support_ofSupport]; exact hnd)
  · rw [Walk.support_copy, Walk.support_ofSupport]

/-- **Menger's theorem, undirected edge form, with a matching cut** ([Menger1927];
[Diestel2025], Corollary 3.3.5 (ii)): for distinct `u`, `v` there are `m` pairwise edge-disjoint
`u`–`v` paths and a set of `m` edges whose deletion disconnects `u` from `v`. -/
theorem exists_edgeDisjoint_eq_not_reachable [Finite V] (G : SimpleGraph V) {u v : V}
    (huv : u ≠ v) :
    ∃ (m : ℕ) (W : Fin m → G.Walk u v), (∀ i, (W i).IsPath) ∧
      (Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges) ∧
      ∃ C : Finset (Sym2 V), C.card = m ∧ ¬ (G.deleteEdges ↑C).Reachable u v := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨S, hu, hv, P, hP, hdisj, hanti⟩ := exists_unit_flowPaths (toDigraph G) huv
  choose W hW hWs using fun i => exists_walk_of_isDipath (hP i)
  have hedges : ∀ {x y : V} (w : G.Walk x y),
      w.edges = (w.support.zip w.support.tail).map fun e => s(e.1, e.2) := by
    intro x y w
    induction w with
    | nil => simp
    | cons h p ih =>
      cases p with
      | nil => simp
      | cons h' q =>
        rw [Walk.edges_cons, ih]
        simp [Walk.support_cons]
  have hWdisj : Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges := by
    intro i j hij e hei hej
    rw [hedges, hWs i] at hei
    rw [hedges, hWs j] at hej
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hei
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hej
    rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hba : b = a := Prod.ext h1 h2
      exact hdisj hij a ha (by rw [← hba]; exact hb)
    · have hba : b = (a.2, a.1) := Prod.ext h1 h2
      exact hanti i j a.1 a.2 ha (by rw [← hba]; exact hb)
  obtain ⟨C, hC⟩ : ∃ C : Finset (Sym2 V),
      C = ((toDigraph G).outArcs S).image fun e => s(e.1, e.2) := ⟨_, rfl⟩
  have hCreach : ¬ (G.deleteEdges ↑C).Reachable u v := by
    refine not_reachable_deleteEdges_of_forall_adj (S := ↑S) hu hv fun x hx y hxy hy => ?_
    rw [hC, Finset.mem_coe]
    exact Finset.mem_image.mpr ⟨(x, y), Digraph.mem_outArcs.mpr ⟨hx, hy, hxy⟩, rfl⟩
  have hle := le_encard_of_edgeDisjoint_of_not_reachable W hWdisj hCreach
  rw [Set.encard_coe_eq_coe_finsetCard] at hle
  have hle' : ((toDigraph G).outArcs S).card ≤ C.card := by exact_mod_cast hle
  have hCle : C.card ≤ ((toDigraph G).outArcs S).card := by grind
  exact ⟨_, W, hW, hWdisj, C, le_antisymm hCle hle', hCreach⟩

/-- **Menger's theorem, undirected edge form** ([Menger1927]; [Diestel2025],
Corollary 3.3.5 (ii)): in a finite simple graph, `u` and `v` are `k`-edge-reachable if and only
if there are `k` pairwise edge-disjoint `u`–`v` paths. -/
theorem isEdgeReachable_iff_exists_edgeDisjoint [Finite V] (G : SimpleGraph V) (u v : V)
    (k : ℕ) :
    G.IsEdgeReachable k u v ↔ ∃ W : Fin k → G.Walk u v, (∀ i, (W i).IsPath) ∧
      Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges := by
  constructor
  · intro h
    by_cases huv : u = v
    · subst huv
      refine ⟨fun _ => Walk.nil, fun _ => Walk.IsPath.nil, fun i j _ e he => ?_⟩
      simp at he
    · obtain ⟨m, W, hW, hdisj, C, hCm, hC⟩ := exists_edgeDisjoint_eq_not_reachable G huv
      have hk : k ≤ m := by
        by_contra hlt
        apply hC
        apply h
        rw [Set.encard_coe_eq_coe_finsetCard, hCm]
        exact_mod_cast not_le.mp hlt
      refine ⟨fun i => W (Fin.castLE hk i), fun i => hW _, fun i j hij => ?_⟩
      exact hdisj fun h' => hij (Fin.castLE_injective hk h')
  · rintro ⟨W, -, hdisj⟩ s hs
    by_contra hreach
    exact absurd hs (not_lt.mpr (le_encard_of_edgeDisjoint_of_not_reachable W hdisj hreach))

private theorem isVertexSeparator_iff_isVertexCut {G : SimpleGraph V} {u v : V} {T : Finset V} :
    G.IsVertexSeparator u v T ↔ (toDigraph G).IsVertexCut u v T := by
  constructor
  · rintro ⟨hu, hv, h⟩
    refine ⟨hu, hv, fun p hp => ?_⟩
    obtain ⟨w, hw, rfl⟩ := exists_walk_of_isDipath hp
    exact h w hw
  · rintro ⟨hu, hv, h⟩
    exact ⟨hu, hv, fun w hw => h _ (isDipath_support hw)⟩

/-- **Menger's theorem, undirected vertex form, with a matching separator** ([Menger1927];
[Diestel2025], Corollary 3.3.5 (i)): for distinct, non-adjacent `u`, `v` there are `m` pairwise
internally disjoint `u`–`v` paths and a `u`–`v` separator with `m` vertices. -/
theorem exists_internallyDisjoint_eq_isVertexSeparator [Finite V] (G : SimpleGraph V)
    {u v : V} (huv : u ≠ v) (hadj : ¬ G.Adj u v) :
    ∃ (m : ℕ) (W : Fin m → G.Walk u v), (∀ i, (W i).IsPath) ∧
      SimpleGraph.InternallyDisjoint W ∧ ∃ T : Finset V, G.IsVertexSeparator u v T ∧ T.card = m :=
  by
  obtain ⟨m, P, hP, hdisj, T, hT, hTm⟩ :=
    exists_internallyDisjoint_eq_isVertexCut (toDigraph G) huv hadj
  choose W hW hWs using fun i => exists_walk_of_isDipath (hP i)
  refine ⟨m, W, hW, fun i j hij x hxi hxj => hdisj hij x ?_ ?_, T,
    isVertexSeparator_iff_isVertexCut.mpr hT, hTm⟩
  · rw [← hWs i]; exact hxi
  · rw [← hWs j]; exact hxj

/-- **Menger's theorem, undirected vertex form** ([Menger1927]; [Diestel2025],
Corollary 3.3.5 (i)): in a finite simple graph there are `k` pairwise internally disjoint
`u`–`v` paths if and only if every `u`–`v` separator has at least `k` vertices. -/
theorem exists_internallyDisjoint_iff_forall_isVertexSeparator [Finite V] (G : SimpleGraph V)
    (u v : V) (k : ℕ) :
    (∃ W : Fin k → G.Walk u v, (∀ i, (W i).IsPath) ∧ SimpleGraph.InternallyDisjoint W) ↔
      ∀ T : Finset V, G.IsVertexSeparator u v T → k ≤ T.card := by
  constructor
  · rintro ⟨W, _, hdisj⟩ T hT
    exact card_le_card_of_internallyDisjoint_of_isVertexSeparator hdisj hT
  · intro h
    obtain ⟨P, hP, hdisj⟩ := (exists_internallyDisjoint_iff_forall_isVertexCut _ u v k).mpr
      fun T hT => h T (isVertexSeparator_iff_isVertexCut.mpr hT)
    choose W hW hWs using fun i => exists_walk_of_isDipath (hP i)
    refine ⟨W, hW, fun i j hij x hxi hxj => hdisj hij x ?_ ?_⟩
    · rw [← hWs i]; exact hxi
    · rw [← hWs j]; exact hxj

/-! ### Undirected `A`–`B` Menger -/

private theorem isSeparator_simpleGraph_iff_toDigraph {G : SimpleGraph V} {A B Y : Set V} :
    G.IsSeparator A B Y ↔ (toDigraph G).IsSeparator A B Y := by
  rw [SimpleGraph.isSeparator_iff_forall_isPath]
  constructor
  · intro h a ha b hb p hp
    obtain ⟨w, hw, rfl⟩ := exists_walk_of_isDipath hp
    exact h ha hb w hw
  · intro h a ha b hb w hw
    exact h ha hb w.support (isDipath_support hw)

/-- **Menger's theorem, undirected `A`–`B` set form, with a matching separator** ([Menger1927];
[Diestel2025], Theorem 3.3.1): in a finite simple graph, for any `A, B : Set V`, there exist `m`
pairwise vertex-disjoint `A`–`B` paths and an `A`–`B` separator `Y : Finset V` of size `m`.

An `A`–`B` path here starts in `A`, ends in `B` and may pass through further vertices of `A` or
`B` (the endpoint convention of [Schrijver2017], Section 4.1), whereas [Diestel2025], Section 1.3,
lets `A`–`B` paths meet `A` and `B` only at their ends. Single-vertex paths at vertices of `A ∩ B`
are allowed, so every separator meets `A ∩ B`, but such vertices need not appear as single-vertex
paths in the family. -/
theorem exists_disjoint_walk_eq_isSeparator [Finite V] (G : SimpleGraph V) (A B : Set V) :
    ∃ (m : ℕ) (a b : Fin m → V) (W : ∀ i, G.Walk (a i) (b i)),
      (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (W i).IsPath) ∧
      (Pairwise fun i j => (W i).support.Disjoint (W j).support) ∧
      ∃ Y : Finset V, G.IsSeparator A B ↑Y ∧ Y.card = m := by
  obtain ⟨m, P, hP, hdisj, Y, hY, hYm⟩ :=
    exists_vertexDisjoint_eq_isSeparator (toDigraph G) A B
  choose a ha b hb hPi using hP
  choose W hW hWs using fun i => exists_walk_of_isDipath (hPi i)
  refine ⟨m, a, b, W, ha, hb, hW, fun i j hij x hxi hxj =>
    hdisj hij (hWs i ▸ hxi) (hWs j ▸ hxj), Y,
    isSeparator_simpleGraph_iff_toDigraph.mpr hY, hYm⟩

/-- **Menger's theorem, undirected `A`–`B` set form** ([Menger1927]; [Diestel2025],
Theorem 3.3.1): in a finite simple graph, there exist `k` pairwise vertex-disjoint `A`–`B` paths
if and only if every `A`–`B` separator has at least `k` vertices. The paths follow the endpoint
convention of `exists_disjoint_walk_eq_isSeparator`, not Diestel's: they may pass through further
vertices of `A` or `B`. -/
theorem exists_disjoint_walk_iff_forall_isSeparator [Finite V] (G : SimpleGraph V)
    (A B : Set V) (k : ℕ) :
    (∃ (a b : Fin k → V) (W : ∀ i, G.Walk (a i) (b i)),
        (∀ i, a i ∈ A) ∧ (∀ i, b i ∈ B) ∧ (∀ i, (W i).IsPath) ∧
        Pairwise fun i j => (W i).support.Disjoint (W j).support) ↔
      ∀ Y : Finset V, G.IsSeparator A B ↑Y → k ≤ Y.card := by
  constructor
  · rintro ⟨a, b, W, ha, hb, -, hdisj⟩ Y hY
    exact card_le_card_of_disjoint_of_isSeparator ha hb W hdisj hY
  · intro h
    obtain ⟨m, a, b, W, ha, hb, hW, hdisj, Y, hY, hYm⟩ :=
      exists_disjoint_walk_eq_isSeparator G A B
    have hk : k ≤ m := hYm ▸ h Y hY
    refine ⟨fun i => a (Fin.castLE hk i), fun i => b (Fin.castLE hk i),
      fun i => W (Fin.castLE hk i), fun i => ha _, fun i => hb _, fun i => hW _,
      fun i j hij => ?_⟩
    exact hdisj fun h' => hij (Fin.castLE_injective hk h')

/-! ### Global `k`-connectivity Menger -/

/-- **Menger's theorem, global edge-connectivity form** ([Diestel2025], Theorem 3.3.6 (ii)): a
finite simple graph is `k`-edge-connected iff every pair of vertices is joined by `k` pairwise
edge-disjoint paths.

`k`-edge-connectivity is Mathlib's `SimpleGraph.IsEdgeConnected`, which extends the convention of
[Diestel2025], Section 1.4: Diestel requires more than one vertex, whereas `IsEdgeConnected k`
holds for every `k` on empty and one-vertex types. Pairs `u = v` are included, and are joined by
`k` copies of the trivial walk. -/
theorem isEdgeConnected_iff_forall_exists_edgeDisjoint [Finite V] (G : SimpleGraph V) (k : ℕ) :
    G.IsEdgeConnected k ↔
      ∀ u v : V, ∃ W : Fin k → G.Walk u v, (∀ i, (W i).IsPath) ∧
        Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges := by
  simp only [IsEdgeConnected, isEdgeReachable_iff_exists_edgeDisjoint]

/-- **Menger's theorem, global edge-connectivity form on distinct vertices**: a finite simple
graph is `k`-edge-connected iff every pair of distinct vertices is joined by `k` distinct
pairwise edge-disjoint paths. -/
theorem isEdgeConnected_iff_forall_ne_exists_injective_edgeDisjoint [Finite V]
    (G : SimpleGraph V) (k : ℕ) :
    G.IsEdgeConnected k ↔
      ∀ ⦃u v : V⦄, u ≠ v → ∃ W : Fin k → G.Walk u v,
        Function.Injective W ∧ (∀ i, (W i).IsPath) ∧
        Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges := by
  constructor
  · intro h u v huv
    obtain ⟨W, hW, hdisj⟩ := (isEdgeReachable_iff_exists_edgeDisjoint G u v k).mp (h u v)
    exact ⟨W, injective_of_edgeDisjoint huv hdisj, hW, hdisj⟩
  · intro h
    exact isEdgeConnected_of_forall_exists_edgeDisjoint fun u v huv =>
      let ⟨W, _, _, hdisj⟩ := h huv; ⟨W, hdisj⟩

/-- Helper for Diestel's edge-deletion argument in Theorem 3.3.6 (i): if `w ∉ T ∪ {a, b}` is not
reachable from `a` in `(G.deleteEdges {s(a, b)}) - T`, then `insert b T` separates `a` from `w` in
`G`. -/
private theorem isVertexSeparator_insert_of_not_reachable [DecidableEq V] {G : SimpleGraph V}
    {a b w : V} {T : Finset V} (hab : a ≠ b) (hbw : b ≠ w) (haT : a ∉ T) (hwT : w ∉ T)
    (hnr : ¬ ((G.deleteEdges {s(a, b)}).induce (T : Set V)ᶜ).Reachable ⟨a, haT⟩ ⟨w, hwT⟩) :
    G.IsVertexSeparator a w (insert b T) := by
  rw [isVertexSeparator_iff_not_reachable_induce]
  have ha' : a ∉ insert b T := by simp [hab, haT]
  have hw' : w ∉ insert b T := by simp [hbw.symm, hwT]
  refine ⟨ha', hw', fun ⟨p⟩ => hnr ?_⟩
  let q : G.Walk a w := p.map ⟨Subtype.val, id⟩
  have hqsupp : ∀ x ∈ q.support, x ∉ ((insert b T : Finset V) : Set V) := by
    intro x hx
    rw [Walk.support_map, List.mem_map] at hx
    obtain ⟨⟨y, hy⟩, _, rfl⟩ := hx
    exact hy
  have hqedge : s(a, b) ∉ q.edges := by
    intro he
    have hb : b ∈ q.support := Walk.snd_mem_support_of_mem_edges q he
    exact hqsupp b hb (Finset.mem_coe.mpr (Finset.mem_insert_self b T))
  have hqsuppT : ∀ x ∈ q.support, x ∉ (T : Set V) := fun x hx h =>
    hqsupp x hx (Finset.mem_coe.mpr (Finset.mem_insert_of_mem (Finset.mem_coe.mp h)))
  exact ⟨(q.toDeleteEdge s(a, b) hqedge).induce (T : Set V)ᶜ fun x hx =>
    hqsuppT x (by simpa using hx)⟩

/-- **Menger's theorem, global vertex-connectivity form** ([Menger1927]; [Diestel2025],
Theorem 3.3.6 (i)): a finite simple graph is `k`-vertex-connected iff `|V| > k` and every pair of
distinct vertices is joined by `k` distinct pairwise internally disjoint paths. (The injectivity
condition prevents repeating the single-edge path `[u, v]` when `u` and `v` are adjacent.) -/
theorem isVertexConnected_iff_forall_exists_injective_internallyDisjoint [Finite V]
    (G : SimpleGraph V) (k : ℕ) :
    G.IsVertexConnected k ↔
      (k : ℕ∞) < ENat.card V ∧
        ∀ ⦃u v : V⦄, u ≠ v → ∃ W : Fin k → G.Walk u v,
          Function.Injective W ∧ (∀ i, (W i).IsPath) ∧ SimpleGraph.InternallyDisjoint W := by
  classical
  have := Fintype.ofFinite V
  constructor
  · intro hconn
    refine ⟨hconn.card_gt, fun u v huv => ?_⟩
    rcases k with _ | _ | k'
    · exact ⟨Fin.elim0, fun i => i.elim0, fun i => i.elim0, fun i => i.elim0⟩
    · obtain ⟨w, hw⟩ := ((hconn.connected le_rfl).preconnected u v).exists_isPath
      exact ⟨fun _ => w, fun i j _ => Fin.ext (by omega), fun _ => hw,
        fun i j hij => absurd (Fin.ext (by omega)) hij⟩
    · set k := k' + 2
      by_cases hadj : G.Adj u v
      · let G₀ := G.deleteEdges {s(u, v)}
        have hadj₀ : ¬ G₀.Adj u v := by simp [G₀]
        have hsep₀ : ∀ T : Finset V, G₀.IsVertexSeparator u v T → k - 1 ≤ T.card := by
          intro T hT
          by_contra! hTlt
          have hcardV : k < Fintype.card V := by
            have := hconn.card_gt
            rw [ENat.card_eq_coe_fintype_card] at this
            exact_mod_cast this
          have hins : (insert u (insert v T)).card ≤ k :=
            (Finset.card_insert_le _ _).trans
              (Nat.succ_le_of_lt (lt_of_le_of_lt (Finset.card_insert_le _ _) (by omega)))
          have hne : (insert u (insert v T) : Finset V) ≠ Finset.univ := by
            intro heq
            rw [heq, Finset.card_univ] at hins
            omega
          obtain ⟨w, -, hwins⟩ := Finset.exists_of_ssubset (Finset.ssubset_univ_iff.mpr hne)
          simp only [Finset.mem_insert, not_or] at hwins
          obtain ⟨hwu, hwv, hwT⟩ := hwins
          have huw : u ≠ w := fun h => hwu h.symm
          have hvw : v ≠ w := fun h => hwv h.symm
          rw [isVertexSeparator_iff_not_reachable_induce] at hT
          obtain ⟨huT, hvT, huvnr⟩ := hT
          have hnotboth :
              ¬ (G₀.induce (T : Set V)ᶜ).Reachable ⟨u, huT⟩ ⟨w, hwT⟩ ∨
              ¬ (G₀.induce (T : Set V)ᶜ).Reachable ⟨v, hvT⟩ ⟨w, hwT⟩ := by
            by_contra hboth
            push Not at hboth
            exact huvnr (hboth.1.trans hboth.2.symm)
          rcases hnotboth with hnr | hnr
          · have hsep := isVertexSeparator_insert_of_not_reachable huv hvw huT hwT hnr
            have hkT := (isVertexConnected_iff_forall_isVertexSeparator.mp hconn).2 huw
              (insert v T) hsep
            have hle := Finset.card_insert_le v T
            omega
          · have hG₀ : G₀ = G.deleteEdges {s(v, u)} := by rw [Sym2.eq_swap]
            rw [hG₀] at hnr
            have hsep := isVertexSeparator_insert_of_not_reachable huv.symm huw hvT hwT hnr
            have hkT := (isVertexConnected_iff_forall_isVertexSeparator.mp hconn).2 hvw
              (insert u T) hsep
            have hle := Finset.card_insert_le u T
            omega
        obtain ⟨W₀, hW₀, hdisj₀⟩ :=
          (exists_internallyDisjoint_iff_forall_isVertexSeparator G₀ u v (k - 1)).mpr hsep₀
        have hG₀le : G₀ ≤ G := G.deleteEdges_le _
        let W : Fin k → G.Walk u v := fun i =>
          if h : i.1 < k - 1 then (W₀ ⟨i.1, h⟩).mapLe hG₀le
          else hadj.toWalk
        have hWpath : ∀ i, (W i).IsPath := fun i => by
          dsimp only [W]
          split_ifs with h
          · exact Walk.IsPath.mk' (by
              rw [Walk.support_mapLe_eq_support]
              exact (hW₀ ⟨i.1, h⟩).support_nodup)
          · exact hadj.isPath_toWalk
        have hWdisj : SimpleGraph.InternallyDisjoint W := by
          intro i j hij x hxi hxj
          dsimp only [W] at hxi hxj
          by_cases hi : i.1 < k - 1 <;> by_cases hj : j.1 < k - 1
          · simp only [hi, ↓reduceDIte] at hxi
            simp only [hj, ↓reduceDIte] at hxj
            rw [Walk.support_mapLe_eq_support] at hxi hxj
            exact hdisj₀ (fun h => hij (Fin.ext (congrArg (@Fin.val (k - 1)) h))) x hxi hxj
          · simp only [hj, ↓reduceDIte, Adj.toWalk, Walk.support_cons, Walk.support_nil] at hxj
            simpa using hxj
          · simp only [hi, ↓reduceDIte, Adj.toWalk, Walk.support_cons, Walk.support_nil] at hxi
            simpa using hxi
          · exact absurd (Fin.ext (by omega)) hij
        have hWinj : Function.Injective W := by
          have hinj₀ := injective_of_internallyDisjoint_of_not_adj huv hadj₀ hW₀ hdisj₀
          have hlen₀ : ∀ i : Fin (k - 1), 2 ≤ (W₀ i).length := fun i => by
            cases hw : W₀ i with
            | nil => exact absurd rfl huv
            | @cons _ w₁ _ h₁ p =>
              cases p with
              | nil => exact absurd h₁ hadj₀
              | cons _ _ => simp [Walk.length_cons]
          intro i j hij
          dsimp only [W] at hij
          by_cases hi : i.1 < k - 1 <;> by_cases hj : j.1 < k - 1
          · simp only [hi, hj, ↓reduceDIte] at hij
            have hsup : (W₀ ⟨i.1, hi⟩).support = (W₀ ⟨j.1, hj⟩).support := by
              simpa [Walk.support_mapLe_eq_support] using congrArg Walk.support hij
            exact Fin.ext (congrArg (@Fin.val (k - 1)) (hinj₀ (Walk.ext_support hsup)))
          · simp only [hi, hj, ↓reduceDIte] at hij
            have h1 := congrArg Walk.length hij
            rw [Walk.length_mapLe, hadj.length_toWalk] at h1
            have := hlen₀ ⟨i.1, hi⟩
            omega
          · simp only [hi, hj, ↓reduceDIte] at hij
            have h1 := congrArg Walk.length hij
            rw [Walk.length_mapLe, hadj.length_toWalk] at h1
            have := hlen₀ ⟨j.1, hj⟩
            omega
          · exact Fin.ext (by omega)
        exact ⟨W, hWinj, hWpath, hWdisj⟩
      · have hsep := (isVertexConnected_iff_forall_isVertexSeparator.mp hconn).2 huv
        obtain ⟨W, hW, hdisj⟩ :=
          (exists_internallyDisjoint_iff_forall_isVertexSeparator G u v k).mpr hsep
        exact ⟨W, injective_of_internallyDisjoint_of_not_adj huv hadj hW hdisj, hW, hdisj⟩
  · rintro ⟨hcard, hpaths⟩
    exact isVertexConnected_of_forall_exists_internallyDisjoint hcard fun u v huv =>
      let ⟨W, _, hW, hdisj⟩ := hpaths huv; ⟨W, hW, hdisj⟩

/-- **Menger's theorem, global vertex-connectivity form for nontrivial graphs**: on a finite
vertex type with at least two vertices, `G` is `k`-vertex-connected iff every pair of distinct
vertices is joined by `k` distinct pairwise internally disjoint paths. -/
theorem isVertexConnected_iff_of_nontrivial [Finite V] [Nontrivial V] (G : SimpleGraph V)
    (k : ℕ) :
    G.IsVertexConnected k ↔
      ∀ ⦃u v : V⦄, u ≠ v → ∃ W : Fin k → G.Walk u v,
        Function.Injective W ∧ (∀ i, (W i).IsPath) ∧ SimpleGraph.InternallyDisjoint W := by
  refine ⟨fun h => (isVertexConnected_iff_forall_exists_injective_internallyDisjoint G k).mp h |>.2,
    fun h => isVertexConnected_of_nontrivial_of_forall_exists_injective_internallyDisjoint h⟩

/-- **Menger's theorem, global vertex-connectivity form with `Finset` path families**: a finite
simple graph is `k`-vertex-connected iff `|V| > k` and every pair of distinct vertices has a
`k`-element `Finset` of pairwise internally disjoint paths. -/
theorem isVertexConnected_iff_forall_exists_finset [Finite V] (G : SimpleGraph V) (k : ℕ) :
    G.IsVertexConnected k ↔
      (k : ℕ∞) < ENat.card V ∧
        ∀ ⦃u v : V⦄, u ≠ v → ∃ P : Finset (G.Walk u v), P.card = k ∧
          (∀ w ∈ P, w.IsPath) ∧ (P : Set (G.Walk u v)).Pairwise
            (fun w₁ w₂ => ∀ x ∈ w₁.support, x ∈ w₂.support → x = u ∨ x = v) := by
  rw [isVertexConnected_iff_forall_exists_injective_internallyDisjoint]
  simp only [exists_injective_internallyDisjoint_iff_exists_finset]

/-- Every finite `k`-vertex-connected simple graph is `k`-edge-connected (`κ(G) ≤ λ(G)`,
[Diestel2025], Proposition 1.4.2). -/
theorem isEdgeConnected_of_isVertexConnected [Finite V] {G : SimpleGraph V} {k : ℕ}
    (h : G.IsVertexConnected k) : G.IsEdgeConnected k := by
  rw [isEdgeConnected_iff_forall_ne_exists_injective_edgeDisjoint]
  obtain ⟨-, hpaths⟩ :=
    (isVertexConnected_iff_forall_exists_injective_internallyDisjoint G k).mp h
  intro u v huv
  obtain ⟨W, hinj, hW, hdisj⟩ := hpaths huv
  exact ⟨W, hinj, hW, edgeDisjoint_of_injective_internallyDisjoint hinj hW hdisj⟩

end Undirected

end Cslib.Algorithms.Lean.MaxFlow
