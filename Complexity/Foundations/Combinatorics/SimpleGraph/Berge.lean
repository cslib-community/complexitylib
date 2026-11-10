/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/Matching.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Matching
public import Mathlib.Combinatorics.SimpleGraph.Paths
public import Mathlib.Data.Set.Card
import Complexity.Foundations.Combinatorics.SimpleGraph.SymmDiff
import Mathlib.Combinatorics.SimpleGraph.DegreeSum

/-!
# Berge's lemma

A matching `M` of a graph is *maximum* when no matching has more edges. An *`M`-augmenting path*
is a path between two distinct vertices not covered by `M` whose edges alternate between edges
outside and inside `M`. Exchanging the edges of `M` along such a path gives a matching covering two
more vertices. Berge's lemma states the converse for finite graphs: a matching with no augmenting
path is maximum. The proof is the standard one ([Schrijver2017], Theorem 3.2). If a matching `M'`
covers more vertices than `M`, then in `M ∆ M'` every vertex has degree at most two. The component
of a vertex covered by `M'` only has a second odd-degree vertex. That vertex is covered by `M`
only, since otherwise the path between them would be `M`-augmenting. So `M'` covers at most as many
vertices as `M`.

Matchings are Mathlib's `SimpleGraph.Subgraph.IsMatching` and alternation is Mathlib's
`SimpleGraph.IsAlternating`.

The results about maximum matchings assume a finite vertex type, as in the source.

## Main definitions

* `SimpleGraph.Subgraph.IsAugmentingPath M p`: `p` is an `M`-augmenting path.
* `SimpleGraph.Subgraph.augment M p`: the symmetric difference of `M` and the edges of `p`.
* `SimpleGraph.Subgraph.IsMaximumMatching M`: `M` is a matching with at least as many edges as
  every matching.

## Main results

* `SimpleGraph.Subgraph.IsAugmentingPath.isMatching_augment`,
  `SimpleGraph.Subgraph.IsAugmentingPath.ncard_verts_augment`: augmenting along an augmenting path
  gives a matching covering two more vertices.
* `SimpleGraph.Subgraph.IsMatching.exists_isAugmentingPath_of_ncard_lt`: if a matching covers more
  vertices than `M`, there is an `M`-augmenting path.
* `SimpleGraph.Subgraph.IsMatching.isMaximumMatching_iff_forall_not_isAugmentingPath`: **Berge's
  lemma**. A matching of a finite graph is maximum iff it has no augmenting path.
* `SimpleGraph.exists_isMaximumMatching`: every finite graph has a maximum matching.

## References

* [C. Berge, *Two Theorems in Graph Theory*][Berge1957]
* [A. Schrijver, *A Course in Combinatorial Optimization*][Schrijver2017]
-/

public section

open scoped symmDiff

namespace SimpleGraph

variable {V : Type*} {G : SimpleGraph V}

/-- A vertex of a path other than its two ends has two distinct neighbours on the path. -/
theorem Walk.IsPath.exists_ne_adj_toSubgraph {u v x a : V} {p : G.Walk u v}
    (hp : p.IsPath) (hxu : x ≠ u) (hxv : x ≠ v) (ha : p.toSubgraph.Adj x a) :
    ∃ b, b ≠ a ∧ p.toSubgraph.Adj x b := by
  have hx : x ∈ p.support := p.mem_support_of_adj_toSubgraph ha
  obtain ⟨i, rfl, hi⟩ := p.mem_support_iff_exists_getVert.mp hx
  have hi0 : i ≠ 0 := by rintro rfl; exact hxu p.getVert_zero
  have hil : i < p.length := by
    rcases hi.lt_or_eq with h | h
    · exact h
    · subst h; exact absurd p.getVert_length hxv
  have hN := hp.neighborSet_toSubgraph_internal hi0 hil
  have hne : p.getVert (i - 1) ≠ p.getVert (i + 1) := by
    intro h
    have := hp.getVert_injOn (by rw [Set.mem_ofPred_eq]; omega)
      (by rw [Set.mem_ofPred_eq]; omega) h
    omega
  have hmem : ∀ b, b ∈ ({p.getVert (i - 1), p.getVert (i + 1)} : Set V) →
      p.toSubgraph.Adj (p.getVert i) b := fun b hb => by
    rw [← hN] at hb; exact hb
  have ha' : a ∈ p.toSubgraph.neighborSet (p.getVert i) := ha
  rw [hN] at ha'
  rcases ha' with rfl | rfl
  · exact ⟨p.getVert (i + 1), hne.symm, hmem _ (by simp)⟩
  · exact ⟨p.getVert (i - 1), hne, hmem _ (by simp)⟩

namespace Subgraph

variable {M M' : G.Subgraph}

/-- `p` is an `M`-augmenting path: a path between two distinct vertices not covered by `M` whose
edges alternate between edges outside and inside `M` ([Berge1957]; [Schrijver2017], Section 3.2).
Alternation is Mathlib's `SimpleGraph.IsAlternating`: of two distinct edges of `p` at a vertex,
exactly one lies in `M`. Since both ends are uncovered, the first and last edges lie outside `M`
and the path has odd length. -/
structure IsAugmentingPath (M : G.Subgraph) {u v : V} (p : G.Walk u v) : Prop where
  isPath : p.IsPath
  ne : u ≠ v
  start_notMem : u ∉ M.verts
  end_notMem : v ∉ M.verts
  isAlternating : p.toSubgraph.spanningCoe.IsAlternating M.spanningCoe

/-- The matching `M ∆ E(p)` obtained by augmenting `M` along the walk `p`: an edge belongs to it
when it belongs to exactly one of `M` and `p`. Its vertices are those of `M` and of `p`. -/
def augment (M : G.Subgraph) {u v : V} (p : G.Walk u v) : G.Subgraph where
  verts := M.verts ∪ {x | x ∈ p.support}
  Adj x y := (M.Adj x y ∧ ¬p.toSubgraph.Adj x y) ∨ (p.toSubgraph.Adj x y ∧ ¬M.Adj x y)
  adj_sub := by
    rintro x y (⟨h, -⟩ | ⟨h, -⟩)
    · exact M.adj_sub h
    · exact p.toSubgraph.adj_sub h
  edge_vert := by
    rintro x y (⟨h, -⟩ | ⟨h, -⟩)
    · exact Or.inl (M.edge_vert h)
    · exact Or.inr (p.mem_support_of_adj_toSubgraph h)
  symm.symm x y := by
    rintro (⟨h, h'⟩ | ⟨h, h'⟩)
    · exact Or.inl ⟨h.symm, fun h'' => h' h''.symm⟩
    · exact Or.inr ⟨h.symm, fun h'' => h' h''.symm⟩

theorem augment_adj {u v x y : V} {p : G.Walk u v} :
    (M.augment p).Adj x y ↔
      (M.Adj x y ∧ ¬p.toSubgraph.Adj x y) ∨ (p.toSubgraph.Adj x y ∧ ¬M.Adj x y) :=
  Iff.rfl

theorem verts_augment {u v : V} {p : G.Walk u v} :
    (M.augment p).verts = M.verts ∪ {x | x ∈ p.support} :=
  Set.ext fun _ => Iff.rfl

namespace IsAugmentingPath

variable {u v : V} {p : G.Walk u v}

theorem not_nil (hp : M.IsAugmentingPath p) : ¬p.Nil := fun h => hp.ne h.eq

/-- An inner vertex of an augmenting path is covered by `M`. -/
theorem mem_verts_of_mem_support (hp : M.IsAugmentingPath p) {x : V} (hx : x ∈ p.support)
    (hxu : x ≠ u) (hxv : x ≠ v) : x ∈ M.verts := by
  obtain ⟨e, he, hxe⟩ :=
    (p.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mp hx
  induction e using Sym2.ind with
  | _ a b =>
  have hab : p.toSubgraph.Adj a b := p.adj_toSubgraph_iff_mem_edges.mpr he
  obtain ⟨a', ha'⟩ : ∃ a', p.toSubgraph.Adj x a' := by
    rcases Sym2.mem_iff.mp hxe with rfl | rfl
    · exact ⟨b, hab⟩
    · exact ⟨a, hab.symm⟩
  obtain ⟨b', hb'a', hb'⟩ := hp.isPath.exists_ne_adj_toSubgraph hxu hxv ha'
  by_cases hM : M.Adj x a'
  · exact M.edge_vert hM
  · have := (hp.isAlternating hb'a' hb' ha').mpr hM
    exact M.edge_vert this

/-- Augmenting a matching along an augmenting path gives a matching. -/
theorem isMatching_augment (hM : M.IsMatching) (hp : M.IsAugmentingPath p) :
    (M.augment p).IsMatching := by
  intro x hx
  by_cases hxp : x ∈ p.support
  · -- `x` has an edge `xa` on `p`
    obtain ⟨e, he, hxe⟩ :=
      (p.mem_support_iff_exists_mem_edges_of_not_nil hp.not_nil).mp hxp
    induction e using Sym2.ind with
    | _ c d =>
    have hcd : p.toSubgraph.Adj c d := p.adj_toSubgraph_iff_mem_edges.mpr he
    obtain ⟨a, ha⟩ : ∃ a, p.toSubgraph.Adj x a := by
      rcases Sym2.mem_iff.mp hxe with rfl | rfl
      · exact ⟨d, hcd⟩
      · exact ⟨c, hcd.symm⟩
    -- the `p`-edge at `x` outside `M`
    obtain ⟨b, hb, hbM⟩ : ∃ b, p.toSubgraph.Adj x b ∧ ¬M.Adj x b := by
      by_cases hxa : M.Adj x a
      · have hxu : x ≠ u := by rintro rfl; exact hp.start_notMem (M.edge_vert hxa)
        have hxv : x ≠ v := by rintro rfl; exact hp.end_notMem (M.edge_vert hxa)
        obtain ⟨b, hba, hb⟩ := hp.isPath.exists_ne_adj_toSubgraph hxu hxv ha
        exact ⟨b, hb, fun hxb => ((hp.isAlternating hba hb ha).mp hxb) hxa⟩
      · exact ⟨a, ha, hxa⟩
    refine ⟨b, Or.inr ⟨hb, hbM⟩, ?_⟩
    rintro y (⟨hy, hyp⟩ | ⟨hy, hyM⟩)
    · -- `xy ∈ M \ p`: then `x` is inner, and its two `p`-edges are `xb ∉ M` and one in `M`
      exfalso
      have hxu : x ≠ u := by rintro rfl; exact hp.start_notMem (M.edge_vert hy)
      have hxv : x ≠ v := by rintro rfl; exact hp.end_notMem (M.edge_vert hy)
      obtain ⟨c, hcb, hc⟩ := hp.isPath.exists_ne_adj_toSubgraph hxu hxv hb
      have hxc : M.Adj x c := (hp.isAlternating hcb hc hb).mpr hbM
      exact hyp (hM.eq_of_adj_left hxc hy ▸ hc)
    · by_contra hyb
      exact hyM ((hp.isAlternating hyb hy hb).mpr hbM)
  · -- `x` is off the path, so its edges in `M.augment p` are its edges in `M`
    have hxM : x ∈ M.verts := hx.resolve_right hxp
    have hnp : ∀ y, ¬p.toSubgraph.Adj x y := fun y h => hxp (p.mem_support_of_adj_toSubgraph h)
    obtain ⟨y, hy, hy'⟩ := hM hxM
    refine ⟨y, Or.inl ⟨hy, hnp y⟩, ?_⟩
    rintro z (⟨hz, -⟩ | ⟨hz, -⟩)
    · exact hy' z hz
    · exact absurd hz (hnp z)

theorem verts_augment_eq (hp : M.IsAugmentingPath p) :
    (M.augment p).verts = insert u (insert v M.verts) := by
  ext x
  simp only [verts_augment, Set.mem_union, Set.mem_ofPred_eq, Set.mem_insert_iff]
  constructor
  · rintro (h | h)
    · exact Or.inr (Or.inr h)
    · by_cases hxu : x = u
      · exact Or.inl hxu
      by_cases hxv : x = v
      · exact Or.inr (Or.inl hxv)
      exact Or.inr (Or.inr (hp.mem_verts_of_mem_support h hxu hxv))
  · rintro (rfl | rfl | h)
    · exact Or.inr p.start_mem_support
    · exact Or.inr p.end_mem_support
    · exact Or.inl h

theorem ncard_verts_augment [Finite V] (hp : M.IsAugmentingPath p) :
    (M.augment p).verts.ncard = M.verts.ncard + 2 := by
  rw [hp.verts_augment_eq, Set.ncard_insert_of_notMem, Set.ncard_insert_of_notMem hp.end_notMem]
  rw [Set.mem_insert_iff, not_or]
  exact ⟨hp.ne, hp.start_notMem⟩

end IsAugmentingPath

/-! ### The symmetric difference of two matchings -/

/-- The symmetric difference of two matchings alternates with respect to the first one. For two
matchings of the same graph, this generalizes Mathlib's
`Subgraph.IsPerfectMatching.isAlternating_symmDiff_left` from perfect matchings to arbitrary
matchings (Mathlib's lemma allows the second matching to live in a different graph). -/
theorem IsMatching.isAlternating_symmDiff (hM : M.IsMatching) (hM' : M'.IsMatching) :
    (M.spanningCoe ∆ M'.spanningCoe).IsAlternating M.spanningCoe := by
  intro v w w' hww' hvw hvw'
  rw [SimpleGraph.symmDiff_adj] at hvw hvw'
  simp only [spanningCoe_adj] at hvw hvw' ⊢
  constructor
  · intro h h'
    exact hww' (hM.eq_of_adj_left h h')
  · intro h'
    rcases hvw with hl | hr
    · exact hl.1
    · rcases hvw' with hl' | hr'
      · exact absurd hl'.1 h'
      · exact absurd (hM'.eq_of_adj_left hr.1 hr'.1) hww'

/-- A vertex covered by `M'` but not by `M` has exactly one neighbour in `M ∆ M'`, its partner
in `M'`. -/
theorem IsMatching.exists_neighborSet_symmDiff_eq_singleton (hM' : M'.IsMatching) {x : V}
    (hx : x ∉ M.verts) (hx' : x ∈ M'.verts) :
    ∃ b, (M.spanningCoe ∆ M'.spanningCoe).neighborSet x = {b} := by
  obtain ⟨b, hb, hb'⟩ := hM' hx'
  refine ⟨b, Set.ext fun y => ?_⟩
  rw [SimpleGraph.mem_neighborSet, SimpleGraph.symmDiff_adj, Set.mem_singleton_iff]
  simp only [spanningCoe_adj]
  constructor
  · rintro (⟨h, -⟩ | ⟨h, -⟩)
    · exact absurd (M.edge_vert h) hx
    · exact hb' y h
  · rintro rfl
    exact Or.inr ⟨hb, fun h => hx (M.edge_vert h)⟩

/-- A vertex has an odd number of neighbours in `M ∆ M'` only if exactly one of `M` and `M'`
covers it. -/
theorem IsMatching.xor_of_odd_ncard_neighborSet_symmDiff (hM : M.IsMatching)
    (hM' : M'.IsMatching) {x : V}
    (hodd : Odd ((M.spanningCoe ∆ M'.spanningCoe).neighborSet x).ncard) :
    Xor (x ∈ M.verts) (x ∈ M'.verts) := by
  classical
  by_cases hx : x ∈ M.verts <;> by_cases hx' : x ∈ M'.verts
  · exfalso
    obtain ⟨a, ha, ha'⟩ := hM hx
    obtain ⟨b, hb, hb'⟩ := hM' hx'
    have hN : (M.spanningCoe ∆ M'.spanningCoe).neighborSet x =
        if a = b then ∅ else {a, b} := by
      ext y
      rw [SimpleGraph.mem_neighborSet, SimpleGraph.symmDiff_adj]
      simp only [spanningCoe_adj]
      split_ifs with hab
      · subst hab
        simp only [Set.mem_empty_iff_false, iff_false]
        rintro (⟨h, h'⟩ | ⟨h, h'⟩)
        · exact h' (ha' y h ▸ hb)
        · exact h' (hb' y h ▸ ha)
      · simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
        constructor
        · rintro (⟨h, -⟩ | ⟨h, -⟩)
          · exact Or.inl (ha' y h)
          · exact Or.inr (hb' y h)
        · rintro (rfl | rfl)
          · exact Or.inl ⟨ha, fun h => hab (hb' y h)⟩
          · exact Or.inr ⟨hb, fun h => hab (ha' y h).symm⟩
    rw [hN] at hodd
    split_ifs at hodd with hab
    · simp at hodd
    · rw [Set.ncard_pair hab] at hodd
      exact absurd hodd (by decide)
  · exact Or.inl ⟨hx, hx'⟩
  · exact Or.inr ⟨hx', hx⟩
  · exfalso
    have hN : (M.spanningCoe ∆ M'.spanningCoe).neighborSet x = ∅ := by
      ext y
      rw [SimpleGraph.mem_neighborSet, SimpleGraph.symmDiff_adj]
      simp only [spanningCoe_adj, Set.mem_empty_iff_false, iff_false]
      rintro (⟨h, -⟩ | ⟨h, -⟩)
      · exact hx (M.edge_vert h)
      · exact hx' (M'.edge_vert h)
    rw [hN, Set.ncard_empty] at hodd
    exact absurd hodd (by decide)

/-- **Berge's lemma**, hard direction ([Berge1957], Theorem 1; [Schrijver2017], Theorem 3.2): if
a matching `M'` covers more vertices than a matching `M`, then there is an `M`-augmenting path. -/
theorem IsMatching.exists_isAugmentingPath_of_ncard_lt [Finite V] (hM : M.IsMatching)
    (hM' : M'.IsMatching) (hlt : M.verts.ncard < M'.verts.ncard) :
    ∃ (u v : V) (p : G.Walk u v), M.IsAugmentingPath p := by
  classical
  have := Fintype.ofFinite V
  by_contra! hno
  set H := M.spanningCoe ∆ M'.spanningCoe with hH
  have hHG : H ≤ G :=
    symmDiff_le_sup.trans (sup_le M.spanningCoe_le M'.spanningCoe_le)
  -- two distinct vertices not covered by `M` are not joined in `H`
  have key : ∀ d w, d ≠ w → d ∉ M.verts → w ∉ M.verts → ¬H.Reachable d w := by
    intro d w hdw hd hw hr
    obtain ⟨q, hq⟩ := hr.exists_isPath
    refine hno d w (q.mapLe hHG) ⟨hq.mapLe hHG, hdw, hd, hw, ?_⟩
    refine (hM.isAlternating_symmDiff hM').mono fun x y hxy => ?_
    rw [Subgraph.spanningCoe_adj, Walk.adj_toSubgraph_mapLe] at hxy
    exact hxy.adj_sub
  -- every vertex covered by `M'` only is joined in `H` to a vertex covered by `M` only
  have reach : ∀ d, d ∉ M.verts → d ∈ M'.verts →
      ∃ w, w ∈ M.verts ∧ w ∉ M'.verts ∧ H.Reachable d w := by
    intro d hd hd'
    set c := H.connectedComponentMk d
    set K := c.toSimpleGraph.spanningCoe
    have hK : ∀ x, x ∈ c.supp → K.neighborSet x = H.neighborSet x := fun x hx => by
      ext y
      rw [SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet, c.adj_spanningCoe_toSimpleGraph]
      exact ⟨fun h => h.2, fun h => ⟨hx, h⟩⟩
    have hK' : ∀ x, x ∉ c.supp → K.neighborSet x = ∅ := fun x hx => by
      ext y
      rw [SimpleGraph.mem_neighborSet, c.adj_spanningCoe_toSimpleGraph]
      simp [hx]
    obtain ⟨b, hb⟩ := hM'.exists_neighborSet_symmDiff_eq_singleton hd hd'
    have hdeg : Odd (K.degree d) := by
      rw [← ncard_neighborSet, hK d rfl, hb, Set.ncard_singleton]
      exact odd_one
    obtain ⟨w, hwd, hw⟩ := K.exists_ne_odd_degree_of_exists_odd_degree d hdeg
    rw [← ncard_neighborSet] at hw
    have hwc : w ∈ c.supp := by
      by_contra hwc
      rw [hK' w hwc, Set.ncard_empty] at hw
      exact absurd hw (by decide)
    rw [hK w hwc] at hw
    have hdw : H.Reachable d w := (ConnectedComponent.exact hwc).symm
    rcases hM.xor_of_odd_ncard_neighborSet_symmDiff hM' hw with h | h
    · exact ⟨w, h.1, h.2, hdw⟩
    · exact absurd hdw (key d w (Ne.symm hwd) hd h.2)
  -- hence `M'`-only vertices inject into `M`-only vertices
  have hle : (M'.verts \ M.verts).ncard ≤ (M.verts \ M'.verts).ncard := by
    have : Nonempty V := ⟨(Set.nonempty_of_ncard_ne_zero (by omega : M'.verts.ncard ≠ 0)).some⟩
    choose! f hf₁ hf₂ hf₃ using reach
    refine Set.ncard_le_ncard_of_injOn f (fun d hd => ⟨hf₁ d hd.2 hd.1, hf₂ d hd.2 hd.1⟩) ?_
    intro d₁ hd₁ d₂ hd₂ heq
    by_contra hne
    refine key d₁ d₂ hne hd₁.2 hd₂.2 ((hf₃ d₁ hd₁.2 hd₁.1).trans ?_)
    rw [heq]
    exact (hf₃ d₂ hd₂.2 hd₂.1).symm
  have h₁ := Set.ncard_inter_add_ncard_sdiff_eq_ncard M.verts M'.verts
  have h₂ := Set.ncard_inter_add_ncard_sdiff_eq_ncard M'.verts M.verts
  rw [Set.inter_comm] at h₂
  omega

/-! ### Maximum matchings and Berge's lemma -/

/-- `M` is a maximum matching of `G`: a matching with at least as many edges as every matching of
`G`. Edges are counted with `Set.encard`. The definition needs no finiteness hypothesis, but it
is coarse on infinite graphs, where every matching with infinitely many edges is maximum. The
results below assume `[Finite V]`. -/
structure IsMaximumMatching (M : G.Subgraph) : Prop where
  isMatching : M.IsMatching
  maximum : ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.encard ≤ M.edgeSet.encard

/-- A matching of a finite graph covers twice as many vertices as it has edges. -/
theorem IsMatching.ncard_verts_eq_two_mul [Finite V] (hM : M.IsMatching) :
    M.verts.ncard = 2 * M.edgeSet.ncard := by
  classical
  have := Fintype.ofFinite V
  have h1 : ∀ v : M.verts, M.coe.degree v = 1 := fun v => by
    rw [coe_degree, degree_eq_one_iff_existsUnique_adj]
    exact hM v.2
  have hsum := M.coe.sum_degrees_eq_twice_card_edges
  rw [Finset.sum_congr rfl fun v _ => by convert h1 v, Finset.sum_const, smul_eq_mul, mul_one,
    Finset.card_univ] at hsum
  rw [← Set.ncard_coe_finset, coe_edgeFinset] at hsum
  rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card, hsum, ← image_coe_edgeSet_coe M,
    Set.ncard_image_of_injective _ (Sym2.map.injective Subtype.val_injective)]

/-- In a finite graph, maximality of a matching may be tested by comparing edge counts with
`Set.ncard`. -/
theorem isMaximumMatching_iff_ncard [Finite V] :
    M.IsMaximumMatching ↔
      M.IsMatching ∧ ∀ M' : G.Subgraph, M'.IsMatching → M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
  have h (M' : G.Subgraph) : M'.edgeSet.encard ≤ M.edgeSet.encard ↔
      M'.edgeSet.ncard ≤ M.edgeSet.ncard := by
    rw [← (Set.toFinite M'.edgeSet).cast_ncard_eq, ← (Set.toFinite M.edgeSet).cast_ncard_eq,
      Nat.cast_le]
  exact ⟨fun hM => ⟨hM.1, fun M' hM' => (h M').mp (hM.2 M' hM')⟩,
    fun hM => ⟨hM.1, fun M' hM' => (h M').mpr (hM.2 M' hM')⟩⟩

/-- In a finite graph a matching is maximum iff it covers at least as many vertices as every
matching. -/
theorem IsMatching.isMaximumMatching_iff_ncard_verts [Finite V] (hM : M.IsMatching) :
    M.IsMaximumMatching ↔ ∀ M' : G.Subgraph, M'.IsMatching → M'.verts.ncard ≤ M.verts.ncard := by
  rw [isMaximumMatching_iff_ncard, and_iff_right hM]
  refine forall₂_congr fun M' hM' => ?_
  rw [hM.ncard_verts_eq_two_mul, hM'.ncard_verts_eq_two_mul]
  omega

/-- A perfect matching of a finite graph is maximum. -/
theorem IsPerfectMatching.isMaximumMatching [Finite V] (hM : M.IsPerfectMatching) :
    M.IsMaximumMatching := by
  refine hM.1.isMaximumMatching_iff_ncard_verts.mpr fun M' _ => ?_
  rw [hM.2.verts_eq_univ]
  exact Set.ncard_le_ncard (Set.subset_univ _)

/-- A finite graph has a maximum matching. -/
theorem _root_.SimpleGraph.exists_isMaximumMatching [Finite V] (G : SimpleGraph V) :
    ∃ M : G.Subgraph, M.IsMaximumMatching := by
  classical
  have := Fintype.ofFinite G.Subgraph
  obtain ⟨M, hM, hmax⟩ := Finset.exists_max_image
    (Finset.univ.filter fun M : G.Subgraph => M.IsMatching) (fun M => M.edgeSet.ncard)
    ⟨⊥, Finset.mem_filter.mpr ⟨Finset.mem_univ _, fun v hv => absurd hv (Set.notMem_empty v)⟩⟩
  exact ⟨M, isMaximumMatching_iff_ncard.mpr ⟨(Finset.mem_filter.mp hM).2,
    fun M' hM' => hmax M' (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hM'⟩)⟩⟩

/-- **Berge's lemma** ([Berge1957], Theorem 1; [Schrijver2017], Theorem 3.2): a matching of a
finite graph is maximum iff there is no augmenting path. -/
theorem IsMatching.isMaximumMatching_iff_forall_not_isAugmentingPath [Finite V]
    (hM : M.IsMatching) :
    M.IsMaximumMatching ↔ ∀ (u v : V) (p : G.Walk u v), ¬M.IsAugmentingPath p := by
  rw [hM.isMaximumMatching_iff_ncard_verts]
  constructor
  · intro hmax u v p hp
    have := hmax _ (hp.isMatching_augment hM)
    rw [hp.ncard_verts_augment] at this
    omega
  · intro hno M' hM'
    by_contra! hlt
    obtain ⟨u, v, p, hp⟩ := hM.exists_isAugmentingPath_of_ncard_lt hM' hlt
    exact hno u v p hp

end Subgraph

end SimpleGraph
