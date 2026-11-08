/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Algorithms.Lean.MaxFlow.Decomposition
public import Mathlib.Combinatorics.Digraph.Basic
public import Mathlib.Combinatorics.SimpleGraph.Connectivity.EdgeConnectivity
public import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.BigOperators

/-!
# Menger's Theorem via Integral Max-Flow/Min-Cut

Derives **Menger's theorem** ([Menger1927]) for finite graphs from the integral max-flow/min-cut
theorem `Cslib.Algorithms.Lean.MaxFlow.Network.exists_maxFlow_eq_minCut`, in four forms: directed
arc-disjoint and internally vertex-disjoint ([Schrijver2017], §4.1, Corollaries 4.1b and 4.1a),
and undirected edge-disjoint and internally vertex-disjoint ([Diestel2025], Corollary 3.3.5).

## Model and source mapping

* **Directed graphs:** Mathlib `Digraph V` on a finite vertex type. A directed `s`-`t` path
  (`IsDipath`) is a duplicate-free vertex list from `s` to `t` whose consecutive pairs
  (`pathArcs`) are arcs.
* **Arc form** ([Schrijver2017], Corollary 4.1b): `ArcDisjoint`, and `IsArcCut` (a set of arcs
  meeting every `s`-`t` path). Schrijver's `s`-`t` cuts `δ^out(U)` are `outArcs G U`. The proof
  sends one unit of flow per arc of `G` (`unitNetwork`), decomposes an integral maximum flow into
  paths (`Network.Flow.exists_flowPaths`) and reads the cut off a minimum cut.
* **Vertex form** ([Schrijver2017], Corollary 4.1a): `InternallyDisjoint` (sharing only `s` and
  `t`) and `IsVertexCut` (`s, t ∉ T` and `T` meets every `s`-`t` path). The proof splits each
  vertex `v ≠ s, t` into a tail copy `(v, false)` and a head copy `(v, true)` joined by an arc of
  capacity `1`, as in the derivation after [Schrijver2017], Corollary 4.1b.
* **Undirected graphs:** Mathlib `SimpleGraph V` with `Walk.IsPath`, through the symmetric
  digraph. The edge form is stated with Mathlib's `SimpleGraph.IsEdgeReachable` (connected after
  deleting fewer than `k` edges); antiparallel flow is cancelled (`Network.Flow.cancel`) so that
  the paths are edge-disjoint and not merely arc-disjoint. The vertex form uses
  `IsVertexSeparator` ([Diestel2025], §1.4).

## Scope

Finite graphs and two terminals only. Not covered: the set version for `A`-`B` paths
([Schrijver2017], Theorem 4.1; [Diestel2025], Theorem 3.3.1), the global `k`-connectivity form
([Diestel2025], Theorem 3.3.6), infinite graphs, and any running-time bound. The proofs are
existence proofs with no algorithm attached.

## Main definitions

* `Cslib.Algorithms.Lean.MaxFlow.IsDipath`, `ArcDisjoint`, `InternallyDisjoint`, `IsArcCut`,
  `IsVertexCut`, `outArcs`: directed paths, disjointness and cuts.
* `Cslib.Algorithms.Lean.MaxFlow.IsVertexSeparator`: vertex separators in a `SimpleGraph`.

## Main results

* `Cslib.Algorithms.Lean.MaxFlow.exists_arcDisjoint_iff_forall_isArcCut` and
  `exists_arcDisjoint_eq_outArcs`: directed arc form.
* `Cslib.Algorithms.Lean.MaxFlow.exists_internallyDisjoint_iff_forall_isVertexCut` and
  `exists_internallyDisjoint_eq_isVertexCut`: directed vertex form.
* `Cslib.Algorithms.Lean.MaxFlow.isEdgeReachable_iff_exists_edgeDisjoint` and
  `exists_edgeDisjoint_eq_not_reachable`: undirected edge form.
* `Cslib.Algorithms.Lean.MaxFlow.exists_internallyDisjoint_iff_forall_isVertexSeparator` and
  `exists_internallyDisjoint_eq_isVertexSeparator`: undirected vertex form.
* Weak duality (`card_le_card_of_arcDisjoint_of_isArcCut`,
  `card_le_card_of_internallyDisjoint_of_isVertexCut`,
  `le_encard_of_edgeDisjoint_of_not_reachable`,
  `card_le_card_of_internallyDisjoint_of_isVertexSeparator`) and closed-set certificates
  (`isArcCut_outArcs`, `isVertexCut_of_forall_adj`, `not_reachable_deleteEdges_of_forall_adj`,
  `isVertexSeparator_of_forall_adj`).

## References

* [K. Menger, *Zur allgemeinen Kurventheorie*][Menger1927]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017]
* [R. Diestel, *Graph Theory*][Diestel2025]
-/

public section

namespace Cslib.Algorithms.Lean.MaxFlow

section PathLemmas

variable {V : Type*}

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

/-! ### Directed Menger -/

section Directed

variable {V : Type*}

/-- `p` is a simple directed `s`-`t` path in `G`: a duplicate-free vertex list from `s` to `t`
whose consecutive pairs are arcs of `G`. -/
@[expose] def IsDipath (G : Digraph V) (s t : V) (p : List V) : Prop :=
  p.Nodup ∧ p.head? = some s ∧ p.getLast? = some t ∧ ∀ e ∈ pathArcs p, G.Adj e.1 e.2

instance instDecidableIsDipath [DecidableEq V] (G : Digraph V) [DecidableRel G.Adj] (s t : V)
    (p : List V) : Decidable (IsDipath G s t p) := by
  unfold IsDipath
  infer_instance

/-- `C` is an `s`-`t` arc cut of `G`: every directed `s`-`t` path of `G` uses an arc of `C`. -/
@[expose] def IsArcCut (G : Digraph V) (s t : V) (C : Finset (V × V)) : Prop :=
  ∀ p, IsDipath G s t p → ∃ e ∈ pathArcs p, e ∈ C

/-- The vertex lists `P i` are pairwise arc-disjoint. -/
@[expose] def ArcDisjoint {ι : Type*} (P : ι → List V) : Prop :=
  Pairwise fun i j => ∀ e ∈ pathArcs (P i), e ∉ pathArcs (P j)

/-- The vertex lists `P i` are pairwise internally disjoint with respect to the ends `s` and
`t`: two distinct lists share no vertex other than `s` and `t`. -/
@[expose] def InternallyDisjoint {ι : Type*} (s t : V) (P : ι → List V) : Prop :=
  Pairwise fun i j => ∀ v ∈ P i, v ∈ P j → v = s ∨ v = t

/-- `T` is an `s`-`t` vertex cut of `G`: it avoids `s` and `t`, and every directed `s`-`t` path
of `G` visits a vertex of `T`. -/
@[expose] def IsVertexCut (G : Digraph V) (s t : V) (T : Finset V) : Prop :=
  s ∉ T ∧ t ∉ T ∧ ∀ p, IsDipath G s t p → ∃ v ∈ p, v ∈ T

variable [Fintype V] [DecidableEq V]

/-- The arcs of `G` leaving a vertex set `S` (Schrijver's `δ^out(S)`). -/
@[expose] def outArcs (G : Digraph V) [DecidableRel G.Adj] (S : Finset V) : Finset (V × V) :=
  (S ×ˢ (Finset.univ \ S)).filter fun e => G.Adj e.1 e.2

theorem mem_outArcs {G : Digraph V} [DecidableRel G.Adj] {S : Finset V} {e : V × V} :
    e ∈ outArcs G S ↔ e.1 ∈ S ∧ e.2 ∉ S ∧ G.Adj e.1 e.2 := by
  simp only [outArcs, Finset.mem_filter, Finset.mem_product, Finset.mem_sdiff, Finset.mem_univ,
    true_and, and_assoc]

/-- The unit-capacity network of `G` with source `s` and sink `t`. -/
private def unitNetwork (G : Digraph V) [DecidableRel G.Adj] (s t : V) : Network V where
  cap u v := if G.Adj u v then 1 else 0
  s := s
  t := t

private theorem cutCapacity_unitNetwork (G : Digraph V) [DecidableRel G.Adj] (s t : V)
    (S : Finset V) : (unitNetwork G s t).cutCapacity S = (outArcs G S).card := by
  rw [outArcs, Finset.card_filter, Finset.sum_product]
  rfl

/-- `outArcs G S` is an `s`-`t` arc cut whenever `s ∈ S` and `t ∉ S`. -/
theorem isArcCut_outArcs (G : Digraph V) [DecidableRel G.Adj] {s t : V} {S : Finset V}
    (hs : s ∈ S) (ht : t ∉ S) : IsArcCut G s t (outArcs G S) := by
  rintro p ⟨-, hps, hpt, hadj⟩
  obtain ⟨e, he, heS, heS'⟩ := exists_mem_pathArcs_boundary (· ∈ S) hps hpt hs ht
  exact ⟨e, he, mem_outArcs.mpr ⟨heS, heS', hadj e he⟩⟩

omit [Fintype V] [DecidableEq V] in
/-- **Weak duality for arc-disjoint paths**: `k` pairwise arc-disjoint `s`-`t` paths need at
least `k` arcs in every `s`-`t` arc cut. -/
theorem card_le_card_of_arcDisjoint_of_isArcCut {G : Digraph V} {s t : V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, IsDipath G s t (P i)) (hdisj : ArcDisjoint P)
    {C : Finset (V × V)} (hC : IsArcCut G s t C) : k ≤ C.card := by
  choose e he heC using fun i => hC (P i) (hP i)
  have hinj : Function.Injective fun i => (⟨e i, heC i⟩ : C) := by
    intro i j hij
    by_contra hne
    have heq : e i = e j := congrArg Subtype.val hij
    exact hdisj hne (e i) (he i) (heq ▸ he j)
  simpa using Fintype.card_le_of_injective _ hinj

/-- Unit-capacity max-flow/min-cut packaged for Menger: arc-disjoint `s`-`t` paths, as many as
the arcs leaving some `s`-`t` cut, with no arc used in both directions. -/
private theorem exists_unit_flowPaths (G : Digraph V) [DecidableRel G.Adj] {s t : V}
    (hst : s ≠ t) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ ∃ P : Fin (outArcs G S).card → List V,
      (∀ i, IsDipath G s t (P i)) ∧ ArcDisjoint P ∧
      ∀ i j a b, (a, b) ∈ pathArcs (P i) → (b, a) ∉ pathArcs (P j) := by
  obtain ⟨f₀, S, -, ⟨hScut, -⟩, hval⟩ :=
    Network.exists_maxFlow_eq_minCut (N := unitNetwork G s t) hst
  have hval' : f₀.cancel.value = ((outArcs G S).card : ℤ) := by
    rw [Network.Flow.value_cancel, hval, cutCapacity_unitNetwork]
  obtain ⟨P, hP, hcount⟩ := f₀.cancel.exists_flowPaths hst
  have hk : f₀.cancel.value.toNat = (outArcs G S).card := by omega
  have hcap : ∀ u v, f₀.cancel u v ≤ if G.Adj u v then 1 else 0 :=
    fun u v => f₀.cancel.le_cap u v
  refine ⟨S, hScut.1, hScut.2, fun i => P (Fin.cast hk.symm i), fun i => ?_, ?_, ?_⟩
  · obtain ⟨hnd, hs, ht, hpos⟩ := hP (Fin.cast hk.symm i)
    refine ⟨hnd, hs, ht, fun e he => ?_⟩
    by_contra hne
    have h1 := hcap e.1 e.2
    have h2 := hpos e he
    simp only [hne, ↓reduceIte] at h1
    omega
  · intro i j hij e hei hej
    have hne : Fin.cast hk.symm i ≠ Fin.cast hk.symm j := fun h => hij (Fin.cast_injective _ h)
    have hc := hcount e.1 e.2
    have h1 := hcap e.1 e.2
    have h2 : 1 < (Finset.univ.filter fun l => (e.1, e.2) ∈ pathArcs (P l)).card :=
      Finset.one_lt_card.mpr ⟨_, by simpa using hei, _, by simpa using hej, hne⟩
    split_ifs at h1 <;> omega
  · intro i j a b hab hba
    have h1 := (hP (Fin.cast hk.symm i)).2.2.2 _ hab
    have h2 := (hP (Fin.cast hk.symm j)).2.2.2 _ hba
    rcases f₀.cancel_eq_zero_or a b with h | h
    · simp only at h1; omega
    · simp only at h2; omega

/-- **Menger's theorem, directed arc-disjoint form, with a matching cut** ([Menger1927];
[Schrijver2017], §4.1, Corollary 4.1b): for distinct `s`, `t`
there are `(outArcs G S).card` pairwise arc-disjoint directed `s`-`t` paths for some `S` with
`s ∈ S`, `t ∉ S`. With `card_le_card_of_arcDisjoint_of_isArcCut` this says that the maximum
number of arc-disjoint `s`-`t` paths equals the minimum size of an `s`-`t` arc cut. -/
theorem exists_arcDisjoint_eq_outArcs (G : Digraph V) [DecidableRel G.Adj] {s t : V}
    (hst : s ≠ t) :
    ∃ S : Finset V, s ∈ S ∧ t ∉ S ∧ ∃ P : Fin (outArcs G S).card → List V,
      (∀ i, IsDipath G s t (P i)) ∧ ArcDisjoint P := by
  obtain ⟨S, hs, ht, P, hP, hdisj, -⟩ := exists_unit_flowPaths G hst
  exact ⟨S, hs, ht, P, hP, hdisj⟩

omit [Fintype V] [DecidableEq V] in
/-- **Menger's theorem, directed arc-disjoint form** ([Menger1927]; [Schrijver2017], §4.1,
Corollary 4.1b; [Diestel2025], Corollary 3.3.5 (ii) for the undirected analogue): in a finite
digraph there are `k` pairwise arc-disjoint directed `s`-`t` paths if and only if every `s`-`t`
arc cut has at least `k` arcs. (For `s = t` both sides hold trivially.) -/
theorem exists_arcDisjoint_iff_forall_isArcCut [Finite V] (G : Digraph V) (s t : V) (k : ℕ) :
    (∃ P : Fin k → List V, (∀ i, IsDipath G s t (P i)) ∧ ArcDisjoint P) ↔
      ∀ C : Finset (V × V), IsArcCut G s t C → k ≤ C.card := by
  classical
  have := Fintype.ofFinite V
  constructor
  · rintro ⟨P, hP, hdisj⟩ C hC
    exact card_le_card_of_arcDisjoint_of_isArcCut hP hdisj hC
  · intro h
    by_cases hst : s = t
    · subst hst
      refine ⟨fun _ => [s], fun _ => ⟨List.nodup_singleton s, rfl, rfl, by simp⟩, ?_⟩
      intro i j _ e he
      simp at he
    · obtain ⟨S, hs, ht, P, hP, hdisj⟩ := exists_arcDisjoint_eq_outArcs G hst
      have hk : k ≤ (outArcs G S).card := h _ (isArcCut_outArcs G hs ht)
      refine ⟨fun i => P (Fin.castLE hk i), fun i => hP _, fun i j hij => ?_⟩
      exact hdisj fun h => hij (Fin.castLE_injective hk h)

omit [Fintype V] [DecidableEq V] in
/-- **Weak duality for internally disjoint paths**: `k` pairwise internally disjoint `s`-`t`
paths need at least `k` vertices in every `s`-`t` vertex cut. -/
theorem card_le_card_of_internallyDisjoint_of_isVertexCut {G : Digraph V} {s t : V} {k : ℕ}
    {P : Fin k → List V} (hP : ∀ i, IsDipath G s t (P i)) (hdisj : InternallyDisjoint s t P)
    {T : Finset V} (hT : IsVertexCut G s t T) : k ≤ T.card := by
  choose v hv hvT using fun i => hT.2.2 (P i) (hP i)
  have hinj : Function.Injective fun i => (⟨v i, hvT i⟩ : T) := by
    intro i j hij
    by_contra hne
    have heq : v i = v j := congrArg Subtype.val hij
    rcases hdisj hne (v i) (hv i) (heq ▸ hv j) with h | h
    · exact hT.1 (h ▸ hvT i)
    · exact hT.2.1 (h ▸ hvT i)
  simpa using Fintype.card_le_of_injective _ hinj

/-- Vertex splitting of `G`: arcs `(u, true) → (v, false)` of capacity `2` for the arcs of `G`, and
splitting arcs `(v, false) → (v, true)` of capacity `1` for `v ≠ s, t`. -/
private def splitNetwork (G : Digraph V) [DecidableRel G.Adj] (s t : V) : Network (V × Bool) where
  cap x y :=
    if x.2 = true ∧ y.2 = false ∧ G.Adj x.1 y.1 then 2
    else if x.2 = false ∧ y.2 = true ∧ x.1 = y.1 ∧ x.1 ≠ s ∧ x.1 ≠ t then 1
    else 0
  s := (s, true)
  t := (t, false)

section Split

variable {G : Digraph V} [DecidableRel G.Adj] {s t : V}

omit [Fintype V] in
private theorem splitNetwork_s : (splitNetwork G s t).s = (s, true) := rfl

omit [Fintype V] in
private theorem splitNetwork_t : (splitNetwork G s t).t = (t, false) := rfl

omit [Fintype V] in
private theorem splitNetwork_cap_tf (u v : V) :
    (splitNetwork G s t).cap (u, true) (v, false) = if G.Adj u v then 2 else 0 := by
  simp [splitNetwork]

omit [Fintype V] in
private theorem splitNetwork_cap_ft (u v : V) :
    (splitNetwork G s t).cap (u, false) (v, true) = if u = v ∧ u ≠ s ∧ u ≠ t then 1 else 0 := by
  simp [splitNetwork]

omit [Fintype V] in
private theorem splitNetwork_cap_tt (u v : V) :
    (splitNetwork G s t).cap (u, true) (v, true) = 0 := by
  simp [splitNetwork]

omit [Fintype V] in
private theorem splitNetwork_cap_ff (u v : V) :
    (splitNetwork G s t).cap (u, false) (v, false) = 0 := by
  simp [splitNetwork]


private theorem split_flow_tt (f : (splitNetwork G s t).Flow) (u v : V) :
    f (u, true) (v, true) = 0 := by
  have := f.le_cap (u, true) (v, true)
  rw [splitNetwork_cap_tt] at this
  omega

private theorem split_flow_ff (f : (splitNetwork G s t).Flow) (u v : V) :
    f (u, false) (v, false) = 0 := by
  have := f.le_cap (u, false) (v, false)
  rw [splitNetwork_cap_ff] at this
  omega

private theorem split_flow_ft_le (f : (splitNetwork G s t).Flow) (v : V) :
    f (v, false) (v, true) ≤ 1 := by
  have := f.le_cap (v, false) (v, true)
  rw [splitNetwork_cap_ft] at this
  split_ifs at this <;> omega

private theorem split_flow_ft_ne (f : (splitNetwork G s t).Flow) {u v : V}
    (h : ¬ (u = v ∧ u ≠ s ∧ u ≠ t)) :
    f (u, false) (v, true) = 0 := by
  have := f.le_cap (u, false) (v, true)
  simp only [splitNetwork_cap_ft, h, ↓reduceIte] at this
  omega

private theorem split_flow_tf_zero (f : (splitNetwork G s t).Flow) {u v : V} (h : ¬ G.Adj u v) :
    f (u, true) (v, false) = 0 := by
  have := f.le_cap (u, true) (v, false)
  simp only [splitNetwork_cap_tf, h, ↓reduceIte] at this
  omega

omit [DecidableEq V] in
private theorem sum_split {M : Type*} [AddCommMonoid M] (g : V × Bool → M) :
    ∑ x, g x = ∑ w, g (w, true) + ∑ w, g (w, false) := by
  rw [Fintype.sum_prod_type, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun w _ => Fintype.sum_bool _

/-- Flow entering the tail copy `(v, false)` all comes from head copies and leaves through the
splitting arc. -/
private theorem split_inflow (f : (splitNetwork G s t).Flow) {v : V} (hvt : v ≠ t) :
    ∑ u, f (u, true) (v, false) = f (v, false) (v, true) := by
  have hc := f.conserve (v, false) (by simp [splitNetwork_s]) (by simp [splitNetwork_t, hvt])
  have h1 : ∑ x, f x (v, false) = ∑ u, f (u, true) (v, false) + ∑ u, f (u, false) (v, false) :=
    sum_split _
  have h2 : ∑ y, f (v, false) y = ∑ w, f (v, false) (w, true) + ∑ w, f (v, false) (w, false) :=
    sum_split _
  have h3 : ∑ u, f (u, false) (v, false) = 0 :=
    Finset.sum_eq_zero fun u _ => split_flow_ff f u v
  have h4 : ∑ w, f (v, false) (w, false) = 0 :=
    Finset.sum_eq_zero fun w _ => split_flow_ff f v w
  have h5 : ∑ w, f (v, false) (w, true) = f (v, false) (v, true) := by
    refine Finset.sum_eq_single v (fun w _ hw => split_flow_ft_ne f ?_) (by simp)
    exact fun h => hw h.1.symm
  change ∑ x, f x (v, false) = ∑ y, f (v, false) y at hc
  omega

/-- Flow leaving the head copy `(u, true)` all goes to tail copies and enters through the
splitting arc. -/
private theorem split_outflow (f : (splitNetwork G s t).Flow) {u : V} (hus : u ≠ s) :
    ∑ v, f (u, true) (v, false) = f (u, false) (u, true) := by
  have hc := f.conserve (u, true) (by simp [splitNetwork_s, hus]) (by simp [splitNetwork_t])
  have h1 : ∑ x, f x (u, true) = ∑ w, f (w, true) (u, true) + ∑ w, f (w, false) (u, true) :=
    sum_split _
  have h2 : ∑ y, f (u, true) y = ∑ v, f (u, true) (v, true) + ∑ v, f (u, true) (v, false) :=
    sum_split _
  have h3 : ∑ w, f (w, true) (u, true) = 0 :=
    Finset.sum_eq_zero fun w _ => split_flow_tt f w u
  have h4 : ∑ v, f (u, true) (v, true) = 0 :=
    Finset.sum_eq_zero fun v _ => split_flow_tt f u v
  have h5 : ∑ w, f (w, false) (u, true) = f (u, false) (u, true) := by
    refine Finset.sum_eq_single u (fun w _ hw => split_flow_ft_ne f ?_) (by simp)
    exact fun h => hw h.1
  change ∑ x, f x (u, true) = ∑ y, f (u, true) y at hc
  omega

/-- Each arc of `G` carries at most one unit, except possibly a direct arc `s → t`. -/
private theorem split_thru (f : (splitNetwork G s t).Flow) (hadj : ¬ G.Adj s t) (u v : V) :
    f (u, true) (v, false) ≤ 1 := by
  by_cases hvt : v = t
  · by_cases hus : u = s
    · have := split_flow_tf_zero f hadj
      rw [hvt, hus]
      omega
    · have hle : f (u, true) (v, false) ≤ ∑ w, f (u, true) (w, false) :=
        Finset.single_le_sum (f := fun w => f (u, true) (w, false)) (fun _ _ => Nat.zero_le _)
          (Finset.mem_univ v)
      have := split_outflow f hus
      have := split_flow_ft_le f u
      omega
  · have hle : f (u, true) (v, false) ≤ ∑ w, f (w, true) (v, false) :=
      Finset.single_le_sum (f := fun w => f (w, true) (v, false)) (fun _ _ => Nat.zero_le _)
        (Finset.mem_univ u)
    have := split_inflow f hvt
    have := split_flow_ft_le f v
    omega

end Split

omit [Fintype V] [DecidableEq V] in
/-- **Menger's theorem, directed vertex form, with a matching cut** ([Menger1927];
[Schrijver2017], §4.1, Corollary 4.1a): for distinct,
non-adjacent `s`, `t` there are `m` pairwise internally disjoint directed `s`-`t` paths and an
`s`-`t` vertex cut with `m` vertices. With
`card_le_card_of_internallyDisjoint_of_isVertexCut` this says that the maximum number of
internally disjoint `s`-`t` paths equals the minimum size of an `s`-`t` vertex cut. -/
theorem exists_internallyDisjoint_eq_isVertexCut [Finite V] (G : Digraph V) {s t : V}
    (hst : s ≠ t) (hadj : ¬ G.Adj s t) :
    ∃ (m : ℕ) (P : Fin m → List V), (∀ i, IsDipath G s t (P i)) ∧ InternallyDisjoint s t P ∧
      ∃ T : Finset V, IsVertexCut G s t T ∧ T.card = m := by
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
  -- Arcs of `G` never leave the reachable cut from a head copy.
  have hprop : ∀ u v, G.Adj u v → (u, true) ∈ f.reachableCut → (v, false) ∈ f.reachableCut := by
    intro u v huv hu
    rw [Network.Flow.mem_reachableCut_iff] at hu ⊢
    refine hu.tail ?_
    have h1 := split_thru f hadj u v
    have h2 : (splitNetwork G s t).cap (u, true) (v, false) = 2 := by
      simp only [splitNetwork_cap_tf, huv, ↓reduceIte]
    change 0 < ((splitNetwork G s t).cap (u, true) (v, false) - f (u, true) (v, false)) +
      f (v, false) (u, true)
    omega
  obtain ⟨T, hT⟩ : ∃ T : Finset V, ∀ v, v ∈ T ↔
      (v, false) ∈ f.reachableCut ∧ (v, true) ∉ f.reachableCut :=
    ⟨Finset.univ.filter fun v => (v, false) ∈ f.reachableCut ∧ (v, true) ∉ f.reachableCut,
      fun v => by simp⟩
  have hsT : s ∉ T := fun h => ((hT s).mp h).2 hsR
  have htT : t ∉ T := fun h => htR ((hT t).mp h).1
  have hTcut : IsVertexCut G s t T := by
    refine ⟨hsT, htT, fun p ⟨_, hps, hpt, hadjp⟩ => ?_⟩
    obtain ⟨e, he, hSe, hSe'⟩ := exists_mem_pathArcs_boundary
      (fun v => (v, false) ∈ f.reachableCut ∨ v = s) hps hpt (Or.inr rfl)
      (by rintro (h | h); exacts [htR h, hst h.symm])
    have hnb : (e.2, false) ∉ f.reachableCut := fun h => hSe' (Or.inl h)
    have hna : (e.1, true) ∉ f.reachableCut := fun h => hnb (hprop _ _ (hadjp e he) h)
    refine ⟨e.1, fst_mem_of_mem_pathArcs he, (hT _).mpr ⟨?_, hna⟩⟩
    rcases hSe with h | h
    · exact h
    · exact absurd (h ▸ hsR) hna
  -- `|T|` is bounded by the capacity of the reachable cut.
  have hTcap : T.card ≤ (splitNetwork G s t).cutCapacity f.reachableCut := by
    have hsub : T.image (fun v => ((v, false), (v, true))) ⊆
        f.reachableCut ×ˢ (Finset.univ \ f.reachableCut) := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
      have := (hT v).mp hv
      simp [this.1, this.2]
    have hone : ∀ v ∈ T, (splitNetwork G s t).cap (v, false) (v, true) = 1 := by
      intro v hv
      have hvs : v ≠ s := fun h => hsT (h ▸ hv)
      have hvt : v ≠ t := fun h => htT (h ▸ hv)
      simp [splitNetwork_cap_ft, hvs, hvt]
    calc T.card = ∑ v ∈ T, (splitNetwork G s t).cap (v, false) (v, true) := by
          rw [Finset.sum_congr rfl hone, Finset.sum_const, smul_eq_mul, mul_one]
      _ = ∑ x ∈ T.image (fun v => ((v, false), (v, true))),
            (splitNetwork G s t).cap x.1 x.2 := by
          rw [Finset.sum_image]
          intro x _ y _ hxy
          simpa using hxy
      _ ≤ ∑ x ∈ f.reachableCut ×ˢ (Finset.univ \ f.reachableCut),
            (splitNetwork G s t).cap x.1 x.2 :=
          Finset.sum_le_sum_of_subset hsub
      _ = (splitNetwork G s t).cutCapacity f.reachableCut := by
          rw [Finset.sum_product]
          rfl
  -- Project `f` to a flow on the unit network of `G`.
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
  have hg : ∀ u v, g u v = f (u, true) (v, false) := fun _ _ => rfl
  have hgval : g.value = f.value := by
    have hout : ∑ y, (f (s, true) y : ℤ) = ∑ w, (f (s, true) (w, false) : ℤ) := by
      rw [sum_split]
      simp [split_flow_tt]
    have hin : ∑ x, (f x (s, true) : ℤ) = 0 := by
      rw [sum_split]
      refine (add_eq_zero_iff_of_nonneg (Finset.sum_nonneg fun _ _ => by omega)
        (Finset.sum_nonneg fun _ _ => by omega)).mpr ⟨?_, ?_⟩
      · exact Finset.sum_eq_zero fun w _ => by simp [split_flow_tt]
      · refine Finset.sum_eq_zero fun w _ => ?_
        rw [split_flow_ft_ne f (fun h => h.2.1 h.1)]
        simp
    have hin' : ∑ u, (f (u, true) (s, false) : ℤ) = 0 := by
      have h := split_inflow f hst
      rw [split_flow_ft_ne f (fun h => h.2.1 rfl)] at h
      exact_mod_cast h
    change (∑ w, (f (s, true) (w, false) : ℤ)) - ∑ u, (f (u, true) (s, false) : ℤ) =
      (∑ y, (f (s, true) y : ℤ)) - ∑ x, (f x (s, true) : ℤ)
    rw [hout, hin, hin']
  have hst'' : (unitNetwork G s t).s ≠ (unitNetwork G s t).t := hst
  obtain ⟨P, hP, hcount⟩ := g.exists_flowPaths hst''
  have hPdi : ∀ i, IsDipath G s t (P i) := by
    intro i
    obtain ⟨hnd, hs, ht, hpos⟩ := hP i
    refine ⟨hnd, hs, ht, fun e he => ?_⟩
    by_contra hne
    have h1 := hpos e he
    rw [hg, split_flow_tf_zero f hne] at h1
    exact absurd h1 (lt_irrefl 0)
  have hPdisj : InternallyDisjoint s t P := by
    intro i j hij v hvi hvj
    by_contra hv
    rw [not_or] at hv
    have hhead : ∀ l, (P l).head? ≠ some v := fun l h => hv.1 (by
      have := (hP l).2.1
      rw [h] at this
      exact Option.some.inj this)
    have hle := card_filter_mem_le_sum P v hhead (fun u w => g u w) (fun u => hcount u v)
    have h1 : ∑ u, g u v = f (v, false) (v, true) := split_inflow f hv.2
    have h2 := split_flow_ft_le f v
    have h3 : 1 < (Finset.univ.filter fun l => v ∈ P l).card :=
      Finset.one_lt_card.mpr ⟨i, by simpa using hvi, j, by simpa using hvj, hij⟩
    omega
  have hle := card_le_card_of_internallyDisjoint_of_isVertexCut hPdi hPdisj hTcut
  refine ⟨g.value.toNat, P, hPdi, hPdisj, T, hTcut, ?_⟩
  omega

omit [Fintype V] [DecidableEq V] in
/-- **Menger's theorem, directed vertex form** ([Menger1927]; [Schrijver2017], §4.1,
Corollary 4.1a; [Diestel2025], Corollary 3.3.5 (i) for the undirected analogue): in a finite
digraph there are `k` pairwise internally disjoint directed `s`-`t` paths if and only if every
`s`-`t` vertex cut has at least `k` vertices. (If `s = t` or `s → t` is an arc, there is no
`s`-`t` vertex cut and both sides hold for every `k`.) -/
theorem exists_internallyDisjoint_iff_forall_isVertexCut [Finite V] (G : Digraph V) (s t : V)
    (k : ℕ) :
    (∃ P : Fin k → List V, (∀ i, IsDipath G s t (P i)) ∧ InternallyDisjoint s t P) ↔
      ∀ T : Finset V, IsVertexCut G s t T → k ≤ T.card := by
  classical
  have := Fintype.ofFinite V
  constructor
  · rintro ⟨P, hP, hdisj⟩ T hT
    exact card_le_card_of_internallyDisjoint_of_isVertexCut hP hdisj hT
  · intro h
    by_cases hst : s = t
    · subst hst
      refine ⟨fun _ => [s], fun _ => ⟨List.nodup_singleton s, rfl, rfl, by simp⟩, ?_⟩
      intro i j _ v hv _
      exact Or.inl (List.mem_singleton.mp hv)
    by_cases hadj : G.Adj s t
    · refine ⟨fun _ => [s, t], fun _ => ⟨by simp [hst], rfl, rfl, by simp [hadj]⟩, ?_⟩
      intro i j _ v hv _
      simpa using hv
    obtain ⟨m, P, hP, hdisj, T, hT, hTm⟩ := exists_internallyDisjoint_eq_isVertexCut G hst hadj
    have hk : k ≤ m := hTm ▸ h T hT
    refine ⟨fun i => P (Fin.castLE hk i), fun i => hP _, fun i j hij => ?_⟩
    exact hdisj fun h => hij (Fin.castLE_injective hk h)

omit [Fintype V] [DecidableEq V] in
/-- Closed-set certificate for a vertex cut: if `s ∈ S`, `t ∉ S`, `T` avoids `s` and `t`, and
every arc leaving `S` ends in `T`, then `T` is an `s`-`t` vertex cut. -/
theorem isVertexCut_of_forall_adj {G : Digraph V} {s t : V} {S T : Finset V} (hs : s ∈ S)
    (ht : t ∉ S) (hsT : s ∉ T) (htT : t ∉ T) (hST : ∀ u ∈ S, ∀ v, G.Adj u v → v ∉ S → v ∈ T) :
    IsVertexCut G s t T := by
  refine ⟨hsT, htT, fun p ⟨_, hps, hpt, hadj⟩ => ?_⟩
  obtain ⟨e, he, heS, heS'⟩ := exists_mem_pathArcs_boundary (· ∈ S) hps hpt hs ht
  exact ⟨e.2, snd_mem_of_mem_pathArcs he, hST _ heS _ (hadj e he) heS'⟩

end Directed

/-! ### Undirected Menger -/

section Undirected

open SimpleGraph

variable {V : Type*}

/-- The symmetric digraph of a simple graph: each edge becomes two opposite arcs. -/
private def toDigraph (G : SimpleGraph V) : Digraph V := ⟨G.Adj⟩

private theorem forall_mem_pathArcs_of_isChain {r : V → V → Prop} :
    ∀ {l : List V}, l.IsChain r → ∀ e ∈ pathArcs l, r e.1 e.2
  | [], _, e, he => by simp at he
  | [_], _, e, he => by simp at he
  | x :: y :: rest, h, e, he => by
    rw [List.isChain_cons_cons] at h
    rw [pathArcs_cons_cons, List.mem_cons] at he
    rcases he with rfl | he
    · exact h.1
    · exact forall_mem_pathArcs_of_isChain h.2 e he

private theorem isChain_of_forall_mem_pathArcs {r : V → V → Prop} :
    ∀ {l : List V}, (∀ e ∈ pathArcs l, r e.1 e.2) → l.IsChain r
  | [], _ => List.IsChain.nil
  | [x], _ => List.IsChain.singleton x
  | x :: y :: rest, h =>
    List.IsChain.cons_cons (h (x, y) (by simp))
      (isChain_of_forall_mem_pathArcs fun e he => h e (by simp [he]))

private theorem edges_eq_map_pathArcs {G : SimpleGraph V} {u v : V} (w : G.Walk u v) :
    w.edges = (pathArcs w.support).map fun e => s(e.1, e.2) := by
  induction w with
  | nil => simp
  | cons h p ih =>
    cases p with
    | nil => simp
    | cons h' q =>
      rw [Walk.edges_cons, ih]
      simp

private theorem isDipath_support {G : SimpleGraph V} {u v : V} {w : G.Walk u v}
    (hw : w.IsPath) : IsDipath (toDigraph G) u v w.support := by
  refine ⟨hw.support_nodup, ?_, ?_, forall_mem_pathArcs_of_isChain w.isChain_adj_support⟩
  · rw [List.head?_eq_some_head (Walk.support_ne_nil w), Walk.head_support]
  · rw [List.getLast?_eq_some_getLast (Walk.support_ne_nil w), Walk.getLast_support]

private theorem exists_walk_of_isDipath {G : SimpleGraph V} {u v : V} {p : List V}
    (hp : IsDipath (toDigraph G) u v p) : ∃ w : G.Walk u v, w.IsPath ∧ w.support = p := by
  obtain ⟨hnd, hu, hv, hadj⟩ := hp
  have hne : p ≠ [] := by
    rintro rfl
    simp at hu
  have hchain : p.IsChain G.Adj := isChain_of_forall_mem_pathArcs (r := G.Adj) hadj
  have hu' : p.head hne = u := by
    rw [List.head?_eq_some_head hne] at hu
    exact Option.some.inj hu
  have hv' : p.getLast hne = v := by
    rw [List.getLast?_eq_some_getLast hne] at hv
    exact Option.some.inj hv
  refine ⟨(Walk.ofSupport p hne hchain).copy hu' hv', ?_, ?_⟩
  · rw [Walk.isPath_copy]
    exact Walk.IsPath.mk' (by rw [Walk.support_ofSupport]; exact hnd)
  · rw [Walk.support_copy, Walk.support_ofSupport]

/-- Closed-set certificate for disconnection: if `u ∈ S`, `v ∉ S` and every edge leaving `S` lies
in `C`, then `u` and `v` are disconnected in `G.deleteEdges C`. -/
theorem not_reachable_deleteEdges_of_forall_adj {G : SimpleGraph V} {u v : V} {S : Set V}
    {C : Set (Sym2 V)} (hu : u ∈ S) (hv : v ∉ S)
    (hC : ∀ x ∈ S, ∀ y, G.Adj x y → y ∉ S → s(x, y) ∈ C) :
    ¬ (G.deleteEdges C).Reachable u v := by
  rintro ⟨p⟩
  obtain ⟨d, -, hdS, hdS'⟩ := p.exists_boundary_dart S hu hv
  have hadj := d.adj
  rw [deleteEdges_adj] at hadj
  exact hadj.2 (hC _ hdS _ hadj.1 hdS')

/-- **Weak duality, undirected edge form**: `k` pairwise edge-disjoint `u`-`v` walks force every
edge set disconnecting `u` from `v` to have at least `k` edges. -/
theorem le_encard_of_edgeDisjoint_of_not_reachable {G : SimpleGraph V} {u v : V} {k : ℕ}
    (W : Fin k → G.Walk u v) (hdisj : Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges)
    {C : Set (Sym2 V)} (hC : ¬ (G.deleteEdges C).Reachable u v) : (k : ℕ∞) ≤ C.encard := by
  classical
  have hmem : ∀ i, ∃ e ∈ (W i).edges, e ∈ C := by
    intro i
    by_contra h
    simp only [not_exists, not_and] at h
    exact hC ⟨(W i).toDeleteEdges C h⟩
  choose e he heC using hmem
  have hinj : Function.Injective e := by
    intro i j hij
    by_contra hne
    exact hdisj hne (e i) (he i) (by rw [hij]; exact he j)
  have hsub : ((Finset.univ.image e : Finset (Sym2 V)) : Set (Sym2 V)) ⊆ C := by
    intro x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
    exact heC i
  calc (k : ℕ∞) = ((Finset.univ.image e : Finset (Sym2 V)) : Set (Sym2 V)).encard := by
        rw [Set.encard_coe_eq_coe_finsetCard, Finset.card_image_of_injective _ hinj,
          Finset.card_univ, Fintype.card_fin]
    _ ≤ C.encard := Set.encard_le_encard hsub

/-- **Menger's theorem, undirected edge form, with a matching cut** ([Menger1927];
[Diestel2025], Corollary 3.3.5 (ii); [Schrijver2017], §4.1, remark after Corollary 4.1b): for
distinct `u`, `v` there are `m` pairwise edge-disjoint `u`-`v` paths and a set of `m` edges whose
deletion disconnects `u` from `v`. With `le_encard_of_edgeDisjoint_of_not_reachable` this says
that the maximum number of edge-disjoint `u`-`v` paths equals the minimum number of edges
separating `u` from `v`. -/
theorem exists_edgeDisjoint_eq_not_reachable [Finite V] (G : SimpleGraph V) {u v : V}
    (huv : u ≠ v) :
    ∃ (m : ℕ) (W : Fin m → G.Walk u v), (∀ i, (W i).IsPath) ∧
      (Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges) ∧
      ∃ C : Finset (Sym2 V), C.card = m ∧ ¬ (G.deleteEdges ↑C).Reachable u v := by
  classical
  have := Fintype.ofFinite V
  obtain ⟨S, hu, hv, P, hP, hdisj, hanti⟩ := exists_unit_flowPaths (toDigraph G) huv
  choose W hW hWs using fun i => exists_walk_of_isDipath (hP i)
  have hWdisj : Pairwise fun i j => ∀ e ∈ (W i).edges, e ∉ (W j).edges := by
    intro i j hij e hei hej
    rw [edges_eq_map_pathArcs, hWs i] at hei
    rw [edges_eq_map_pathArcs, hWs j] at hej
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hei
    obtain ⟨b, hb, hab⟩ := List.mem_map.mp hej
    rcases Sym2.eq_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · have hba : b = a := Prod.ext h1 h2
      exact hdisj hij a ha (by rw [← hba]; exact hb)
    · have hba : b = (a.2, a.1) := Prod.ext h1 h2
      exact hanti i j a.1 a.2 ha (by rw [← hba]; exact hb)
  obtain ⟨C, hC⟩ : ∃ C : Finset (Sym2 V),
      C = (outArcs (toDigraph G) S).image fun e => s(e.1, e.2) := ⟨_, rfl⟩
  have hCreach : ¬ (G.deleteEdges ↑C).Reachable u v := by
    refine not_reachable_deleteEdges_of_forall_adj (S := ↑S) hu hv fun x hx y hxy hy => ?_
    rw [hC, Finset.mem_coe]
    exact Finset.mem_image.mpr ⟨(x, y), mem_outArcs.mpr ⟨hx, hy, hxy⟩, rfl⟩
  have hle := le_encard_of_edgeDisjoint_of_not_reachable W hWdisj hCreach
  rw [Set.encard_coe_eq_coe_finsetCard] at hle
  have hle' : (outArcs (toDigraph G) S).card ≤ C.card := by exact_mod_cast hle
  have hCle : C.card ≤ (outArcs (toDigraph G) S).card := by
    rw [hC]
    exact Finset.card_image_le
  exact ⟨_, W, hW, hWdisj, C, le_antisymm hCle hle', hCreach⟩

/-- **Menger's theorem, undirected edge form** ([Menger1927]; [Diestel2025],
Corollary 3.3.5 (ii)): in a finite simple graph, `u` and `v` are `k`-edge-reachable (they stay
connected after deleting any fewer than `k` edges) if and only if there are `k` pairwise
edge-disjoint `u`-`v` paths. -/
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
      exact hdisj fun h => hij (Fin.castLE_injective hk h)
  · rintro ⟨W, -, hdisj⟩ s hs
    by_contra hreach
    exact absurd hs (not_lt.mpr (le_encard_of_edgeDisjoint_of_not_reachable W hdisj hreach))

/-- `T` separates `u` from `v` in `G` ([Diestel2025], §1.4): `u, v ∉ T` and every `u`-`v` path of
`G` visits a vertex of `T`. -/
@[expose] def IsVertexSeparator (G : SimpleGraph V) (u v : V) (T : Finset V) : Prop :=
  u ∉ T ∧ v ∉ T ∧ ∀ w : G.Walk u v, w.IsPath → ∃ x ∈ w.support, x ∈ T

private theorem isVertexSeparator_iff_isVertexCut {G : SimpleGraph V} {u v : V} {T : Finset V} :
    IsVertexSeparator G u v T ↔ IsVertexCut (toDigraph G) u v T := by
  constructor
  · rintro ⟨hu, hv, h⟩
    refine ⟨hu, hv, fun p hp => ?_⟩
    obtain ⟨w, hw, rfl⟩ := exists_walk_of_isDipath hp
    exact h w hw
  · rintro ⟨hu, hv, h⟩
    exact ⟨hu, hv, fun w hw => h _ (isDipath_support hw)⟩

/-- Closed-set certificate for a vertex separator: if `u ∈ S`, `v ∉ S`, `T` avoids `u` and `v`,
and every edge leaving `S` ends in `T`, then `T` separates `u` from `v`. -/
theorem isVertexSeparator_of_forall_adj {G : SimpleGraph V} {u v : V} {S T : Finset V}
    (hu : u ∈ S) (hv : v ∉ S) (huT : u ∉ T) (hvT : v ∉ T)
    (hST : ∀ x ∈ S, ∀ y, G.Adj x y → y ∉ S → y ∈ T) : IsVertexSeparator G u v T :=
  isVertexSeparator_iff_isVertexCut.mpr (isVertexCut_of_forall_adj hu hv huT hvT hST)

/-- **Weak duality, undirected vertex form**: `k` pairwise internally disjoint `u`-`v` paths
force every `u`-`v` separator to have at least `k` vertices. -/
theorem card_le_card_of_internallyDisjoint_of_isVertexSeparator {G : SimpleGraph V} {u v : V}
    {k : ℕ} {W : Fin k → G.Walk u v} (hW : ∀ i, (W i).IsPath)
    (hdisj : InternallyDisjoint u v fun i => (W i).support) {T : Finset V}
    (hT : IsVertexSeparator G u v T) : k ≤ T.card :=
  card_le_card_of_internallyDisjoint_of_isVertexCut (fun i => isDipath_support (hW i)) hdisj
    (isVertexSeparator_iff_isVertexCut.mp hT)

/-- **Menger's theorem, undirected vertex form, with a matching separator** ([Menger1927];
[Diestel2025], Corollary 3.3.5 (i)): for distinct, non-adjacent `u`, `v` there are `m` pairwise
internally disjoint `u`-`v` paths and a `u`-`v` separator with `m` vertices. -/
theorem exists_internallyDisjoint_eq_isVertexSeparator [Finite V] (G : SimpleGraph V)
    {u v : V} (huv : u ≠ v) (hadj : ¬ G.Adj u v) :
    ∃ (m : ℕ) (W : Fin m → G.Walk u v), (∀ i, (W i).IsPath) ∧
      InternallyDisjoint u v (fun i => (W i).support) ∧
      ∃ T : Finset V, IsVertexSeparator G u v T ∧ T.card = m := by
  obtain ⟨m, P, hP, hdisj, T, hT, hTm⟩ :=
    exists_internallyDisjoint_eq_isVertexCut (toDigraph G) huv hadj
  choose W hW hWs using fun i => exists_walk_of_isDipath (hP i)
  refine ⟨m, W, hW, fun i j hij x hxi hxj => hdisj hij x ?_ ?_, T,
    isVertexSeparator_iff_isVertexCut.mpr hT, hTm⟩
  · rw [← hWs i]; exact hxi
  · rw [← hWs j]; exact hxj

/-- **Menger's theorem, undirected vertex form** ([Menger1927]; [Diestel2025],
Corollary 3.3.5 (i)): in a finite simple graph there are `k` pairwise internally disjoint
`u`-`v` paths if and only if every `u`-`v` separator has at least `k` vertices. (If `u = v` or
`u` and `v` are adjacent, there is no separator and both sides hold for every `k`.) -/
theorem exists_internallyDisjoint_iff_forall_isVertexSeparator [Finite V] (G : SimpleGraph V)
    (u v : V) (k : ℕ) :
    (∃ W : Fin k → G.Walk u v, (∀ i, (W i).IsPath) ∧
        InternallyDisjoint u v fun i => (W i).support) ↔
      ∀ T : Finset V, IsVertexSeparator G u v T → k ≤ T.card := by
  constructor
  · rintro ⟨W, hW, hdisj⟩ T hT
    exact card_le_card_of_internallyDisjoint_of_isVertexSeparator hW hdisj hT
  · intro h
    obtain ⟨P, hP, hdisj⟩ := (exists_internallyDisjoint_iff_forall_isVertexCut _ u v k).mpr
      fun T hT => h T (isVertexSeparator_iff_isVertexCut.mpr hT)
    choose W hW hWs using fun i => exists_walk_of_isDipath (hP i)
    refine ⟨W, hW, fun i j hij x hxi hxj => hdisj hij x ?_ ?_⟩
    · rw [← hWs i]; exact hxi
    · rw [← hWs j]; exact hxj

end Undirected

end Cslib.Algorithms.Lean.MaxFlow
