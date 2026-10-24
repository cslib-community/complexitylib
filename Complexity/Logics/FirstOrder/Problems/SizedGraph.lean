/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Logics.FirstOrder.Reduction.QuantifierFree
public import Mathlib.Data.Set.Card
import Complexity.Tactic.FirstOrder
import Mathlib.Tactic.FinCases

/-!
# Independent set, clique and vertex cover as classes of finite structures

An instance of independent set, clique or vertex cover is a graph together with a target size.
Here it is a finite structure of the vocabulary `sizedGraph`: a binary relation `adj`, the edges,
and a unary relation `size`, whose number of elements is the target size. Giving the size as a set
of elements rather than as a number keeps the vocabulary free of numeric predicates, and makes
the reductions below one-dimensional.

The edge relation need not be symmetric, and loops are ignored: an independent set has no edge
between two distinct vertices in either direction, a clique has edges between any two distinct
vertices in both directions, and a vertex cover contains an endpoint of every edge between
distinct vertices. On simple graphs these are the usual problems: clique and node cover
[Karp1972] and independent set [GareyJohnson1979]. The sets
asked for have exactly `|size|` vertices; since subsets of independent sets and of cliques, and
supersets of vertex covers, are again such sets, this is equivalent to the usual thresholds "at
least `|size|`" for independent sets and cliques and "at most `|size|`" for vertex covers, as
`|size|` never exceeds the number of vertices.

The machine-level versions of these problems, on graphs encoded as lists of vertices and edges
with a binary target size, are `Cslib.Complexity.IndependentSet`, `Cslib.Complexity.Clique` and
`Cslib.Complexity.VertexCover`, which are proved `NP`-complete. Those read graphs as simple graphs
on their declared vertices; the classes here are classes of finite structures, closed under
isomorphism, without an encoding, and their reductions are first-order interpretations rather than
polynomial-time functions.

* `sizedGraph.IndependentSet`: the graph has an independent set of `|size|` vertices.
* `sizedGraph.Clique`: the graph has a clique of `|size|` vertices.
* `sizedGraph.VertexCover`: the graph has a vertex cover of `|size|` vertices.

The three classes are closed under isomorphism, and quantifier-free reducible to each other.
Complementing the edge relation off the diagonal (`sizedGraph.complementEdges`) turns independent
sets into cliques and back, and complementing the size relation (`sizedGraph.complementSize`)
turns an instance asking for an independent set of size `k` into one asking for a vertex cover of
size `n - k`: a set is independent exactly when its complement is a vertex cover. Both are
one-dimensional quantifier-free interpretations, and their composite is Karp's reduction from
clique to node cover [Karp1972]. The reductions are proved with `fo_reduction`, which leaves only
these facts about sets of vertices.

## Main definitions

* `Cslib.Logic.FO.SizedGraphRel`, `Cslib.Logic.FO.sizedGraph`: the relation symbols and vocabulary
  of graphs with a size relation.
* `Cslib.Logic.FO.sizedGraph.IndependentSet`, `Cslib.Logic.FO.sizedGraph.Clique`,
  `Cslib.Logic.FO.sizedGraph.VertexCover`: the classes of finite structures.
* `Cslib.Logic.FO.sizedGraph.complementEdges`, `Cslib.Logic.FO.sizedGraph.complementSize`:
  the interpretations complementing the edge relation and the size relation.

## Main results

* `Cslib.Logic.FO.sizedGraph.isoClosed_IndependentSet`,
  `Cslib.Logic.FO.sizedGraph.isoClosed_Clique`, `Cslib.Logic.FO.sizedGraph.isoClosed_VertexCover`:
  closure under isomorphism.
* `Cslib.Logic.FO.sizedGraph.qfReduces_IndependentSet_Clique`,
  `Cslib.Logic.FO.sizedGraph.qfReduces_Clique_IndependentSet`: complementing the edges.
* `Cslib.Logic.FO.sizedGraph.qfReduces_IndependentSet_VertexCover`,
  `Cslib.Logic.FO.sizedGraph.qfReduces_VertexCover_IndependentSet`: complementing the size.
* `Cslib.Logic.FO.sizedGraph.qfReduces_Clique_VertexCover`,
  `Cslib.Logic.FO.sizedGraph.qfReduces_VertexCover_Clique`: by transitivity.

## References

* [N. Immerman, *Descriptive Complexity*][Immerman1999]
* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
-/

@[expose] public section

universe w

open FirstOrder Language Structure CategoryTheory

namespace Cslib.Logic.FO

/-- The relation symbols of graphs with a size relation. -/
inductive SizedGraphRel : ℕ → Type
  /-- The edge relation. -/
  | adj : SizedGraphRel 2
  /-- The size relation, whose number of elements is the target size. -/
  | size : SizedGraphRel 1
  deriving DecidableEq

/-- The vocabulary of graphs with a size relation: a binary edge relation and a unary relation
whose number of elements is a target size. -/
def sizedGraph : Language := ⟨fun _ => Empty, SizedGraphRel⟩
  deriving IsRelational

namespace sizedGraph

/-- The edge relation symbol. -/
protected abbrev adj : sizedGraph.Relations 2 := .adj

/-- The size relation symbol. -/
protected abbrev size : sizedGraph.Relations 1 := .size

/-! ### The classes -/

/-- **Independent set**: the structures whose graph has an independent set, a set of vertices no
two distinct of which are adjacent, with as many vertices as the size relation holds of. -/
def IndependentSet : Set (Bundled.{w} sizedGraph.Structure) :=
  {M | ∃ s : Set M, s.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard ∧
    s.Pairwise fun x y => ¬ RelMap sizedGraph.adj ![x, y]}

/-- **Clique**: the structures whose graph has a clique, a set of vertices any two distinct of
which are adjacent, with as many vertices as the size relation holds of. -/
def Clique : Set (Bundled.{w} sizedGraph.Structure) :=
  {M | ∃ s : Set M, s.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard ∧
    s.Pairwise fun x y => RelMap sizedGraph.adj ![x, y]}

/-- **Vertex cover**: the structures whose graph has a vertex cover, a set of vertices containing
an endpoint of every edge between distinct vertices, with as many vertices as the size relation
holds of. -/
def VertexCover : Set (Bundled.{w} sizedGraph.Structure) :=
  {M | ∃ s : Set M, s.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard ∧
    ∀ x y, x ≠ y → RelMap sizedGraph.adj ![x, y] → x ∈ s ∨ y ∈ s}

variable {M : Bundled.{w} sizedGraph.Structure}

/-- A structure belongs to `IndependentSet` iff it has a pairwise nonadjacent set of `|size|`
vertices. -/
theorem mem_IndependentSet : M ∈ IndependentSet ↔ ∃ s : Set M,
    s.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard ∧
      s.Pairwise fun x y => ¬ RelMap sizedGraph.adj ![x, y] :=
  Iff.rfl

/-- A structure belongs to `Clique` iff it has a pairwise adjacent set of `|size|` vertices. -/
theorem mem_Clique : M ∈ Clique ↔ ∃ s : Set M,
    s.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard ∧
      s.Pairwise fun x y => RelMap sizedGraph.adj ![x, y] :=
  Iff.rfl

/-- A structure belongs to `VertexCover` iff it has a set of `|size|` vertices meeting every edge
between distinct vertices. -/
theorem mem_VertexCover : M ∈ VertexCover ↔ ∃ s : Set M,
    s.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard ∧
      ∀ x y, x ≠ y → RelMap sizedGraph.adj ![x, y] → x ∈ s ∨ y ∈ s :=
  Iff.rfl

/-! ### Closure under isomorphism -/

section IsoClosed

variable {M N : Type*} [sizedGraph.Structure M] [sizedGraph.Structure N]

private theorem ncard_size_eq (e : M ≃[sizedGraph] N) :
    {y : N | RelMap sizedGraph.size ![y]}.ncard = {x : M | RelMap sizedGraph.size ![x]}.ncard := by
  rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq]
  exact (relMap_single_equiv e _ x).symm

private theorem ncard_image (e : M ≃[sizedGraph] N) (s : Set M) : (e '' s).ncard = s.ncard :=
  Set.ncard_image_of_injective s e.injective

/-- Independent set is closed under isomorphism. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isoClosed_IndependentSet : IsoClosed IndependentSet.{w} :=
  IsoClosed.of_forall_imp fun _ _ _ e ⟨s, hs, hind⟩ =>
    ⟨e '' s, by rw [ncard_image, hs, ncard_size_eq e],
    e.injective.injOn.pairwise_image.2 fun x hx y hy hxy => by
      simpa [Function.onFun, relMap_pair_equiv] using hind hx hy hxy⟩

/-- Clique is closed under isomorphism. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isoClosed_Clique : IsoClosed Clique.{w} :=
  IsoClosed.of_forall_imp fun _ _ _ e ⟨s, hs, hcl⟩ =>
    ⟨e '' s, by rw [ncard_image, hs, ncard_size_eq e],
    e.injective.injOn.pairwise_image.2 fun x hx y hy hxy => by
      simpa [Function.onFun, relMap_pair_equiv] using hcl hx hy hxy⟩

/-- Vertex cover is closed under isomorphism. -/
@[aesop safe apply (rule_sets := [FirstOrder])]
theorem isoClosed_VertexCover : IsoClosed VertexCover.{w} := by
  refine IsoClosed.of_forall_imp fun _ _ _ e ⟨s, hs, hcov⟩ =>
    ⟨e '' s, by rw [ncard_image, hs, ncard_size_eq e], fun x y hxy hadj => ?_⟩
  obtain ⟨a, rfl⟩ := e.surjective x
  obtain ⟨b, rfl⟩ := e.surjective y
  rw [relMap_pair_equiv] at hadj
  exact (hcov a b (ne_of_apply_ne e hxy) hadj).imp (Set.mem_image_of_mem e)
    (Set.mem_image_of_mem e)

end IsoClosed

/-! ### Reductions -/

/-- Complement the edge relation off the diagonal, keeping the size relation. -/
def complementEdges : Interpretation sizedGraph sizedGraph Unit where
  domain := ⊤
  rel
    | .adj => ∼(rel₂ sizedGraph.adj (0, ()) (1, ())) ⊓ ∼(varEq (0, ()) (1, ()))
    | .size => rel₁ sizedGraph.size (0, ())

/-- Complement the size relation, keeping the edge relation. -/
def complementSize : Interpretation sizedGraph sizedGraph Unit where
  domain := ⊤
  rel
    | .adj => rel₂ sizedGraph.adj (0, ()) (1, ())
    | .size => ∼(rel₁ sizedGraph.size (0, ()))

/-- A set of vertices is independent exactly when its complement is a vertex cover. -/
private theorem pairwise_not_adj_iff_compl {M : Type*} [sizedGraph.Structure M] (s : Set M) :
    (s.Pairwise fun x y => ¬ RelMap sizedGraph.adj ![x, y]) ↔
      ∀ x y, x ≠ y → RelMap sizedGraph.adj ![x, y] → x ∈ sᶜ ∨ y ∈ sᶜ := by
  refine ⟨fun h x y hxy hadj => ?_, fun h x hx y hy hxy hadj => ?_⟩
  · by_contra hc
    simp only [Set.mem_compl_iff, not_or, not_not] at hc
    exact h hc.1 hc.2 hxy hadj
  · rcases h x y hxy hadj with hc | hc <;> contradiction

private theorem ncard_compl_eq_iff {α : Type*} [Finite α] {s t : Set α} :
    sᶜ.ncard = tᶜ.ncard ↔ s.ncard = t.ncard := by
  have := Set.ncard_add_ncard_compl s
  have := Set.ncard_add_ncard_compl t
  omega

/-- **Independent set reduces to clique** by complementing the edge relation: an independent
set of `G` is a clique of its complement. -/
theorem qfReduces_IndependentSet_Clique : QFReduces IndependentSet.{w} Clique.{w} := by
  fo_reduction complementEdges [mem_IndependentSet, mem_Clique]
  exact fun _ _ => exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun h _ hx _ hy hxy => ⟨h hx hy hxy, hxy⟩, fun h _ hx _ hy hxy => (h hx hy hxy).1⟩

/-- **Clique reduces to independent set** by complementing the edge relation: a clique of `G` is
an independent set of its complement. -/
theorem qfReduces_Clique_IndependentSet : QFReduces Clique.{w} IndependentSet.{w} := by
  fo_reduction complementEdges [mem_IndependentSet, mem_Clique]
  exact fun _ _ => exists_congr fun _ => and_congr_right fun _ =>
    ⟨fun h _ hx _ hy hxy hn => hn.1 (h hx hy hxy),
      fun h _ hx _ hy hxy => by_contra fun hn => h hx hy hxy ⟨hn, hxy⟩⟩

/-- **Independent set reduces to vertex cover** by complementing the size relation: a set of `k`
vertices is independent exactly when its complement, of `n - k` vertices, is a vertex cover. -/
theorem qfReduces_IndependentSet_VertexCover : QFReduces IndependentSet.{w} VertexCover.{w} := by
  fo_reduction complementSize [mem_IndependentSet, mem_VertexCover]
  refine fun _ _ =>
    ⟨fun ⟨s, hs, hind⟩ => ⟨sᶜ, ncard_compl_eq_iff.2 hs, (pairwise_not_adj_iff_compl s).1 hind⟩,
      fun ⟨t, ht, hcov⟩ => ⟨tᶜ, ncard_compl_eq_iff.1 ?_, (pairwise_not_adj_iff_compl _).2 ?_⟩⟩
  · rwa [compl_compl]
  · rwa [compl_compl]

/-- **Vertex cover reduces to independent set** by complementing the size relation: a set of `k`
vertices is a vertex cover exactly when its complement, of `n - k` vertices, is independent. -/
theorem qfReduces_VertexCover_IndependentSet : QFReduces VertexCover.{w} IndependentSet.{w} := by
  fo_reduction complementSize [mem_IndependentSet, mem_VertexCover]
  refine fun _ _ =>
    ⟨fun ⟨t, ht, hcov⟩ => ⟨tᶜ, ncard_compl_eq_iff.2 ht, (pairwise_not_adj_iff_compl _).2 ?_⟩,
      fun ⟨s, hs, hind⟩ => ⟨sᶜ, ncard_compl_eq_iff.1 ?_, (pairwise_not_adj_iff_compl s).1 hind⟩⟩
  · rwa [compl_compl]
  · rwa [compl_compl]

/-- Clique reduces to vertex cover, through independent set. -/
theorem qfReduces_Clique_VertexCover : QFReduces Clique.{w} VertexCover.{w} :=
  qfReduces_Clique_IndependentSet.trans qfReduces_IndependentSet_VertexCover isoClosed_VertexCover

/-- Vertex cover reduces to clique, through independent set. -/
theorem qfReduces_VertexCover_Clique : QFReduces VertexCover.{w} Clique.{w} :=
  qfReduces_VertexCover_IndependentSet.trans qfReduces_IndependentSet_Clique isoClosed_Clique

end sizedGraph

end Cslib.Logic.FO
