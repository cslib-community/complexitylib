/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate (Mathlib, `Mathlib/Combinatorics/SimpleGraph/TreeDecomposition/Basic.lean`)

public import Complexity.Init
public import Mathlib.Combinatorics.SimpleGraph.Acyclic
public import Mathlib.Data.ENat.Lattice

/-!
# Tree decompositions and treewidth

A *tree decomposition* of a graph `G` on `V` is a tree `T` on an index type `ι` together with a
finite *bag* `bag t ⊆ V` for every node `t`, such that

1. every vertex lies in some bag;
2. both endpoints of every edge lie in a common bag;
3. for every vertex `v`, the nodes whose bags contain `v` induce a connected subtree of `T`.

The *width* of a decomposition with finitely many nodes is the largest bag size minus one. The
*treewidth* of `G` is the least width of a decomposition with finitely many nodes.

We work with finite bags and finite index trees throughout. `SimpleGraph.etreewidth` takes values
in `ℕ∞` and is `⊤` exactly when `G` has no such decomposition. Finitely many finite bags cover
only finitely many vertices, so this happens if and only if `V` is infinite, whatever the edges of
`G` (`SimpleGraph.etreewidth_eq_top_iff`). In particular `⊤` carries no graph information, and
`etreewidth` is not the treewidth of infinite graphs, which allows decompositions over infinite
trees. `SimpleGraph.treewidth` is the truncation to `ℕ`. It is the textbook treewidth for finite
`V`, where the single-bag decomposition shows `treewidth G ≤ card V - 1`. A graph on an empty
vertex type has treewidth `0`.

Condition 3 is stated as preconnectedness of the induced subgraph, so a vertex lying in no bag
would satisfy it vacuously; condition 1 rules that out.

## Relation to open Mathlib pull requests

Justin Lai's open pull request mathlib4#38334 defines the same structure, `TreeDecomp`, with the
same three axioms; mathlib4#39864 (the Helly property for subtrees) and mathlib4#39939 (complete
graphs and the clique bound) build on it. Here the index type is a
universe-polymorphic parameter `ι` rather than `W : Type`, and `width` is `ℕ`-valued on a
`Fintype` index. `etreewidth` minimizes over `Fin n`-indexed decompositions, so it is `⊤` exactly
for infinite `V`, whereas #38334 minimizes over all index types, giving the edgeless graph on `ℕ`
extended treewidth `0`. The two agree for finite `V`. The rooted parent-array form
(`TreeDecomposition/Rooted`, `SimpleGraph.parentTree`, `IsTree.parent`), `minDegree_le_treewidth`,
`treewidth_le_one_iff` and `treewidth_cycleGraph` are additions on top of that work; the
topmost-node proof that a clique lies in a bag is an alternative to the Helly argument.
Upstreaming should follow that work rather than compete with it.

## Main definitions

* `SimpleGraph.TreeDecomposition G ι`: a tree decomposition of `G` indexed by a tree on `ι`.
* `SimpleGraph.TreeDecomposition.width`: the largest bag size minus one.
* `SimpleGraph.etreewidth`, `SimpleGraph.treewidth`: extended and truncated treewidth.

## Main results

* `SimpleGraph.etreewidth_le_of_hom`, `SimpleGraph.treewidth_le_of_hom`: treewidth does not
  increase along injective homomorphisms, in particular under taking subgraphs
  (`SimpleGraph.treewidth_mono`).
* `SimpleGraph.Iso.treewidth_eq`: treewidth is an isomorphism invariant.
* `SimpleGraph.treewidth_le_card`: `treewidth G ≤ card V - 1`.
* `SimpleGraph.etreewidth_eq_top_iff`: `etreewidth G = ⊤ ↔ Infinite V`.
* `SimpleGraph.exists_width_eq_treewidth`, `SimpleGraph.le_treewidth_iff`,
  `SimpleGraph.treewidth_le_iff`: treewidth is attained, and its order characterizations.

## References

* [N. Robertson and P. D. Seymour, *Graph Minors. II. Algorithmic Aspects of
  Tree-Width*][RobertsonSeymour1986]
* [M. Cygan et al., *Parameterized Algorithms*, Section 7.2][CyganEtAl2015]
-/

public section

namespace SimpleGraph

universe uV uW uι uκ

variable {V : Type uV} {W : Type uW} {ι : Type uι} {κ : Type uκ}

/-- A tree decomposition of `G` indexed by a tree on `ι`: finite bags of vertices at the nodes of
a tree, covering every vertex and every edge, such that the nodes whose bags contain a given vertex
induce a connected subtree. -/
structure TreeDecomposition (G : SimpleGraph V) (ι : Type uι) where
  /-- The index tree. -/
  tree : SimpleGraph ι
  /-- The index graph is a tree. -/
  isTree : tree.IsTree
  /-- The bag of vertices at each node. -/
  bag : ι → Finset V
  /-- Every vertex lies in some bag. -/
  exists_mem_bag (v : V) : ∃ t, v ∈ bag t
  /-- Both endpoints of every edge lie in a common bag. -/
  exists_adj_mem_bag ⦃u v : V⦄ : G.Adj u v → ∃ t, u ∈ bag t ∧ v ∈ bag t
  /-- The nodes whose bags contain a given vertex induce a connected subtree. -/
  preconnected_bag (v : V) : (tree.induce {t | v ∈ bag t}).Preconnected

namespace TreeDecomposition

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- The width of a tree decomposition with finitely many nodes: the largest bag size minus one. -/
def width [Fintype ι] (D : G.TreeDecomposition ι) : ℕ :=
  (Finset.univ.sup fun t => (D.bag t).card) - 1

theorem width_le_iff [Fintype ι] (D : G.TreeDecomposition ι) {k : ℕ} :
    D.width ≤ k ↔ ∀ t, (D.bag t).card ≤ k + 1 := by
  rw [width, Nat.sub_le_iff_le_add, Finset.sup_le_iff]
  simp only [Finset.mem_univ, true_implies]

theorem card_bag_le [Fintype ι] (D : G.TreeDecomposition ι) (t : ι) :
    (D.bag t).card ≤ D.width + 1 :=
  D.width_le_iff.1 le_rfl t

theorem le_width_of_le_card [Fintype ι] (D : G.TreeDecomposition ι) {k : ℕ} {t : ι}
    (h : k + 1 ≤ (D.bag t).card) : k ≤ D.width := by
  have := D.card_bag_le t
  omega

/-- Finitely many finite bags cover the vertices, so a graph with a tree decomposition with
finitely many nodes has a finite vertex type. -/
theorem finite [Finite ι] (D : G.TreeDecomposition ι) : Finite V := by
  refine Set.finite_univ_iff.1 ((Set.finite_iUnion fun t => (D.bag t).finite_toSet).subset
    fun v _ => ?_)
  obtain ⟨t, ht⟩ := D.exists_mem_bag v
  exact Set.mem_iUnion.2 ⟨t, ht⟩

/-- Transport a tree decomposition along an equivalence of index types. -/
def reindex (D : G.TreeDecomposition ι) (e : ι ≃ κ) : G.TreeDecomposition κ where
  tree := D.tree.comap e.symm
  isTree := (Iso.comap e.symm D.tree).symm.isTree_iff.1 D.isTree
  bag := D.bag ∘ e.symm
  exists_mem_bag v := let ⟨t, ht⟩ := D.exists_mem_bag v; ⟨e t, by simpa using ht⟩
  exists_adj_mem_bag u v huv :=
    let ⟨t, ht⟩ := D.exists_adj_mem_bag huv; ⟨e t, by simpa using ht⟩
  preconnected_bag v := by
    let f : D.tree.induce {t | v ∈ D.bag t} →g
        (D.tree.comap e.symm).induce {a | v ∈ (D.bag ∘ e.symm) a} :=
      { toFun := fun t => ⟨e t, by
          simp only [Set.mem_ofPred_eq, Function.comp_apply, Equiv.symm_apply_apply]
          exact t.2⟩
        map_rel' := fun {a b} h => by simpa [comap_adj] using h }
    refine (D.preconnected_bag v).map f ?_
    rintro ⟨a, ha⟩
    exact ⟨⟨e.symm a, ha⟩, Subtype.ext (e.apply_symm_apply a)⟩

@[simp] theorem reindex_bag (D : G.TreeDecomposition ι) (e : ι ≃ κ) (a : κ) :
    (D.reindex e).bag a = D.bag (e.symm a) := by
  unfold reindex
  rfl

@[simp] theorem width_reindex [Fintype ι] [Fintype κ] (D : G.TreeDecomposition ι) (e : ι ≃ κ) :
    (D.reindex e).width = D.width := by
  refine le_antisymm ((D.reindex e).width_le_iff.2 fun a => D.card_bag_le _) ?_
  refine D.width_le_iff.2 fun t => ?_
  have := (D.reindex e).card_bag_le (e t)
  rwa [reindex_bag, Equiv.symm_apply_apply] at this

/-- Pull a tree decomposition of `G` back along an injective homomorphism `H →g G`: the bags are
the preimages of the bags. -/
noncomputable def comap (D : G.TreeDecomposition ι) (f : H →g G) (hf : Function.Injective f) :
    H.TreeDecomposition ι where
  tree := D.tree
  isTree := D.isTree
  bag t := (D.bag t).preimage f hf.injOn
  exists_mem_bag v := let ⟨t, ht⟩ := D.exists_mem_bag (f v); ⟨t, by simpa using ht⟩
  exists_adj_mem_bag u v huv :=
    let ⟨t, ht⟩ := D.exists_adj_mem_bag (f.map_rel huv); ⟨t, by simpa using ht⟩
  preconnected_bag v := by
    have : {t | v ∈ (D.bag t).preimage f hf.injOn} = {t | f v ∈ D.bag t} := by
      ext t
      simp only [Set.mem_ofPred_eq, Finset.mem_preimage]
    rw [this]
    exact D.preconnected_bag (f v)

@[simp] theorem mem_comap_bag (D : G.TreeDecomposition ι) (f : H →g G)
    (hf : Function.Injective f) {t : ι} {v : W} : v ∈ (D.comap f hf).bag t ↔ f v ∈ D.bag t := by
  simp only [comap, Finset.mem_preimage]

theorem width_comap_le [Fintype ι] (D : G.TreeDecomposition ι) (f : H →g G)
    (hf : Function.Injective f) : (D.comap f hf).width ≤ D.width :=
  (D.comap f hf).width_le_iff.2 fun t =>
    (Finset.card_le_card_of_injOn f (fun _ hx => (D.mem_comap_bag f hf).1 hx)
      hf.injOn).trans (D.card_bag_le t)

/-- The decomposition of a graph on a finite vertex type with a single bag containing every
vertex. -/
def singleBag [Fintype V] (G : SimpleGraph V) : G.TreeDecomposition (Fin 1) where
  tree := ⊥
  isTree := IsTree.of_subsingleton
  bag _ := Finset.univ
  exists_mem_bag _ := ⟨0, Finset.mem_univ _⟩
  exists_adj_mem_bag _ _ _ := ⟨0, Finset.mem_univ _, Finset.mem_univ _⟩
  preconnected_bag _ a b := by
    rw [Subsingleton.elim a b]

theorem width_singleBag [Fintype V] (G : SimpleGraph V) :
    (singleBag G).width = Fintype.card V - 1 := by
  simp [width, singleBag]

end TreeDecomposition

/-! ### Treewidth -/

open TreeDecomposition

variable {G : SimpleGraph V} {H : SimpleGraph W}

/-- The extended treewidth of `G`: the least width of a tree decomposition of `G` with finitely
many nodes, or `⊤` if there is none. Nodes are indexed by `Fin n`, which loses no generality
(`SimpleGraph.etreewidth_le_width`).

Since finitely many finite bags cover only finitely many vertices, `etreewidth G = ⊤` if and only
if `V` is infinite (`SimpleGraph.etreewidth_eq_top_iff`). So `⊤` carries no information about
the edges of `G`, and this is not the treewidth of infinite graphs, which allows decompositions
over infinite trees. -/
noncomputable def etreewidth (G : SimpleGraph V) : ℕ∞ :=
  ⨅ D : (Σ n : ℕ, G.TreeDecomposition (Fin n)), (D.2.width : ℕ∞)

theorem etreewidth_le_width [Fintype ι] (D : G.TreeDecomposition ι) :
    G.etreewidth ≤ D.width := by
  refine (iInf_le _ ⟨_, D.reindex (Fintype.equivFin ι)⟩).trans ?_
  rw [width_reindex]

theorem exists_width_eq_etreewidth (h : G.etreewidth ≠ ⊤) :
    ∃ n, ∃ D : G.TreeDecomposition (Fin n), (D.width : ℕ∞) = G.etreewidth := by
  have : Nonempty (Σ n : ℕ, G.TreeDecomposition (Fin n)) := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    exact h (iInf_of_empty _)
  obtain ⟨⟨n, D⟩, hD⟩ := ciInf_mem (fun D : (Σ n : ℕ, G.TreeDecomposition (Fin n)) =>
    (D.2.width : ℕ∞))
  exact ⟨n, D, hD⟩

theorem le_etreewidth_iff {k : ℕ∞} :
    k ≤ G.etreewidth ↔ ∀ n (D : G.TreeDecomposition (Fin n)), k ≤ D.width :=
  ⟨fun h _ D => h.trans (etreewidth_le_width D), fun h => le_iInf fun D => h _ D.2⟩

theorem etreewidth_le_card [Fintype V] : G.etreewidth ≤ (Fintype.card V - 1 : ℕ) :=
  (etreewidth_le_width (singleBag G)).trans_eq (by rw [width_singleBag])

theorem etreewidth_ne_top [Finite V] : G.etreewidth ≠ ⊤ := by
  have := Fintype.ofFinite V
  exact ne_top_of_le_ne_top (ENat.natCast_ne_top _) etreewidth_le_card

/-- `etreewidth G = ⊤` exactly when the vertex type is infinite, whatever the edges of `G`. -/
theorem etreewidth_eq_top_iff : G.etreewidth = ⊤ ↔ Infinite V := by
  refine ⟨fun h => ?_, fun h => ?_⟩
  · by_contra hV
    have := not_infinite_iff_finite.1 hV
    exact etreewidth_ne_top h
  · exact iInf_eq_top.2 fun D => absurd D.2.finite (not_finite_iff_infinite.2 h)

/-- The treewidth of `G`: the least width of a tree decomposition of `G` with finitely many nodes.
This is meaningful for finite `V`, where such a decomposition always exists. For infinite `V` it is
the junk value `0` (see `SimpleGraph.etreewidth_eq_top_iff`). A graph on an empty vertex type has
treewidth `0` (one empty bag), not the value `-1` used by some texts. -/
noncomputable def treewidth (G : SimpleGraph V) : ℕ := G.etreewidth.toNat

theorem coe_treewidth [Finite V] : (G.treewidth : ℕ∞) = G.etreewidth :=
  ENat.natCast_toNat etreewidth_ne_top

theorem treewidth_le_width [Finite V] [Fintype ι] (D : G.TreeDecomposition ι) :
    G.treewidth ≤ D.width := by
  rw [← ENat.natCast_le_natCast, coe_treewidth]
  exact etreewidth_le_width D

theorem exists_width_eq_treewidth [Finite V] :
    ∃ n, ∃ D : G.TreeDecomposition (Fin n), D.width = G.treewidth := by
  obtain ⟨n, D, hD⟩ := exists_width_eq_etreewidth (G := G) etreewidth_ne_top
  exact ⟨n, D, by rw [← ENat.natCast_inj, coe_treewidth, hD]⟩

theorem le_treewidth_iff [Finite V] {k : ℕ} :
    k ≤ G.treewidth ↔ ∀ n (D : G.TreeDecomposition (Fin n)), k ≤ D.width := by
  refine ⟨fun h n D => h.trans (treewidth_le_width D), fun h => ?_⟩
  obtain ⟨n, D, hD⟩ := exists_width_eq_treewidth (G := G)
  exact hD ▸ h n D

theorem treewidth_le_iff [Finite V] {k : ℕ} :
    G.treewidth ≤ k ↔ ∃ n, ∃ D : G.TreeDecomposition (Fin n), D.width ≤ k := by
  refine ⟨fun h => ?_, fun ⟨_, D, hD⟩ => (treewidth_le_width D).trans hD⟩
  obtain ⟨n, D, hD⟩ := exists_width_eq_treewidth (G := G)
  exact ⟨n, D, hD.trans_le h⟩

theorem treewidth_le_card [Fintype V] : G.treewidth ≤ Fintype.card V - 1 :=
  (treewidth_le_width (singleBag G)).trans_eq (width_singleBag G)

/-- Treewidth does not increase along injective homomorphisms. -/
theorem etreewidth_le_of_hom (f : H →g G) (hf : Function.Injective f) :
    H.etreewidth ≤ G.etreewidth :=
  le_etreewidth_iff.2 fun _ D => (etreewidth_le_width (D.comap f hf)).trans
    (ENat.natCast_le_natCast.2 (D.width_comap_le f hf))

/-- Treewidth does not increase along injective homomorphisms into a finite graph. -/
theorem treewidth_le_of_hom [Finite V] (f : H →g G) (hf : Function.Injective f) :
    H.treewidth ≤ G.treewidth :=
  ENat.toNat_le_toNat (etreewidth_le_of_hom f hf) etreewidth_ne_top

/-- Treewidth is monotone under taking subgraphs. -/
theorem treewidth_mono [Finite V] {G' : SimpleGraph V} (h : G' ≤ G) :
    G'.treewidth ≤ G.treewidth :=
  treewidth_le_of_hom (Hom.ofLE h) Function.injective_id

theorem Iso.etreewidth_eq (e : G ≃g H) : G.etreewidth = H.etreewidth :=
  le_antisymm (etreewidth_le_of_hom e.toHom e.injective)
    (etreewidth_le_of_hom e.symm.toHom e.symm.injective)

theorem Iso.treewidth_eq (e : G ≃g H) : G.treewidth = H.treewidth := by
  rw [treewidth, treewidth, e.etreewidth_eq]

end SimpleGraph
