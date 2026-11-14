/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph
public import CslibFrontier.Computability.Complexity.Problems.NAEThreeSAT
public import Mathlib.Combinatorics.SimpleGraph.Density
import CslibFrontier.Computability.Complexity.Reduction.Guard
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Length
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Membership
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.Binary
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import CslibFrontier.Foundations.Data.List.Blocks
import Mathlib.Data.List.GetD

/-!
# Unweighted maximum cut

`SimpleMaxCut` is the set of `SimpleMaxCutInstance` values `(G, K)` such that some set `S` of
vertices of the simple graph `G.induced` has at least `K` edges between `S` and its complement
[Arora and Barak, Exercise 2.15][AroraBarak09] [Garey and Johnson, comment on ND16]
[GareyJohnson1979]. The graph is a `Cslib.Complexity.Graph` in the usual binary encoding
`encGraph`, read as the simple graph on its declared vertices, and `K` is in binary. The edges
between `S` and its complement are counted by Mathlib's `SimpleGraph.interedges S Sᶜ`: an edge
`{u, v}` with `u ∈ S` and `v ∉ S` is counted once, as the pair `(u, v)`.

The weighted problem `Cslib.Complexity.MaxCut` has binary weights, and expanding a weight into
that many unit edges is exponential, so its NP-hardness does not give this result.

## Proof of NP-hardness

The reduction is from `NAEEUThreeSAT`, not-all-equal satisfiability with three literals per
clause, in two steps.

1. **A multigraph of unit edges** (`SimpleMaxCut.formulaEdges`). The literal `(i, b)` is the vertex
   `2 * i` when `b` is true and `2 * i + 1` otherwise. Each clause contributes the triangle on its
   three literal vertices and, for each of its literals, an edge between `2 * i` and `2 * i + 1`.
   A triangle has at most two crossing edges, and exactly two when its sides are not all equal,
   so each clause contributes at most `5` crossing edges. A cut of `5 * m` edges in a formula of
   `m` clauses is therefore a maximum one: it separates every pair `2 * i`, `2 * i + 1` and cuts
   two edges of every triangle, which says that the sides of the vertices `2 * i` form an NAE
   assignment (`SimpleMaxCut.exists_le_crossCount_formulaEdges_iff`).
2. **Subdivision** (`SimpleMaxCut.subdivide`). The edges of a multigraph may repeat and form
   loops. Replacing the `k`-th edge `(u, v)` by the path `2u – 4k+1 – 4k+3 – 2v` gives a simple
   graph. A path of three edges has at most `2 + [u, v separated]` crossing edges, with equality
   for a suitable placement of its inner vertices, so the subdivided graph has a cut of
   `2 * |E| + K` edges exactly when the multigraph `E` has a cut of `K` edges
   (`SimpleMaxCut.exists_subdivide_iff`).

The output graph has `18` edges per clause and the bound `17 * m`.

## Main definitions

* `Cslib.Complexity.SimpleMaxCutInstance`, `Cslib.Complexity.encSimpleMaxCut`,
  `Cslib.Complexity.SimpleMaxCut`: instances, their binary encoding and the decision set.
* `Cslib.Complexity.SimpleMaxCut.crossCount`: the crossing edges of a multigraph edge list.
* `Cslib.Complexity.SimpleMaxCut.subdivide`: the simple graph of a multigraph edge list.
* `Cslib.Complexity.SimpleMaxCut.formulaEdges`: the multigraph of a formula.
* `Cslib.Complexity.toSimpleMaxCut`: the reduction from `NAEEUThreeSAT`.

## Main results

* `Cslib.Complexity.SimpleMaxCut.card_interedges_eq_crossCount`: on a simple edge list, the cut of
  the simple graph is the count of crossing list entries.
* `Cslib.Complexity.SimpleMaxCut.mem_NP`: `SimpleMaxCut ∈ NP encSimpleMaxCut`.
* `Cslib.Complexity.toSimpleMaxCut_mem_iff`: correctness of the reduction.
* `Cslib.Complexity.polyTimeReducible_NAEEUThreeSAT_SimpleMaxCut`,
  `Cslib.Complexity.SimpleMaxCut_npHard`, `Cslib.Complexity.SimpleMaxCut_npComplete`:
  unweighted maximum cut is `NP`-complete.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Exercise 2.15][AroraBarak09]
* [M. R. Garey and D. S. Johnson, *Computers and Intractability*][GareyJohnson1979]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM ComputableInPolyTime Cslib.Logic.PL

/-- An instance of **unweighted maximum cut**: a graph and a target number of crossing edges. -/
structure SimpleMaxCutInstance where
  /-- The graph, read as the simple graph `graph.induced` on its declared vertices. -/
  graph : Graph
  /-- The target number of edges between a vertex set and its complement. -/
  bound : ℕ
  deriving DecidableEq, Repr

/-- Instances of `SimpleMaxCut` are encoded as the graph followed by the bound, in binary. -/
enc_structure encSimpleMaxCut : SimpleMaxCutInstance where
  graph : encGraph, bound : encNat

attribute [fun_prop] encSimpleMaxCut_graph_polyTime encSimpleMaxCut_bound_polyTime
  encSimpleMaxCut_mk_polyTime

/-- **Unweighted maximum cut** [Arora and Barak, Exercise 2.15][AroraBarak09]: some set `S` of
vertices of the simple graph `x.graph.induced` has at least `x.bound` edges between `S` and its
complement. -/
@[expose] def SimpleMaxCut : Set SimpleMaxCutInstance :=
  {x | ∃ S : Finset {v // v ∈ x.graph.vertices},
    x.bound ≤ (x.graph.induced.interedges S Sᶜ).card}

namespace SimpleMaxCut

/-! ### Counting crossing pairs -/

/-- The cut of `G.induced` at the declared vertices in `S` is the length of any duplicate-free
list of its crossing pairs `(u, v)`, with `u ∈ S` and `v ∉ S`. -/
theorem card_interedges_eq_length (G : Graph) (S : Finset ℕ) {l : List (ℕ × ℕ)} (hl : l.Nodup)
    (hmem : ∀ p : ℕ × ℕ, p ∈ l ↔ p.1 ∈ G.vertices ∧ p.2 ∈ G.vertices ∧
      G.toSimpleGraph.Adj p.1 p.2 ∧ p.1 ∈ S ∧ p.2 ∉ S) :
    (G.induced.interedges (S.subtype (· ∈ G.vertices))
      (S.subtype (· ∈ G.vertices))ᶜ).card = l.length := by
  rw [← List.toFinset_card_of_nodup hl, ← Finset.card_map
    ((Function.Embedding.subtype (· ∈ G.vertices)).prodMap
      (Function.Embedding.subtype (· ∈ G.vertices)))]
  congr 1
  ext ⟨a, b⟩
  simp only [Finset.mem_map, SimpleGraph.mem_interedges_iff, Finset.mem_compl,
    Finset.mem_subtype, Graph.induced_adj, Function.Embedding.coe_prodMap,
    Function.Embedding.coe_subtype, Prod.exists, Prod.map_apply, Prod.mk.injEq,
    List.mem_toFinset, hmem]
  constructor
  · rintro ⟨u, v, ⟨hu, hv, huv⟩, rfl, rfl⟩
    exact ⟨u.2, v.2, huv, hu, hv⟩
  · rintro ⟨ha, hb, hab, haS, hbS⟩
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨haS, hbS, hab⟩, rfl, rfl⟩

/-- A cut may be given by a set of natural numbers among the declared vertices. -/
theorem mem_SimpleMaxCut_iff {x : SimpleMaxCutInstance} :
    x ∈ SimpleMaxCut ↔ ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      x.bound ≤ (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
        (S.subtype (· ∈ x.graph.vertices))ᶜ).card := by
  constructor
  · rintro ⟨T, hT⟩
    refine ⟨T.map (Function.Embedding.subtype _), fun v hv => ?_, ?_⟩
    · obtain ⟨u, -, rfl⟩ := Finset.mem_map.1 hv
      exact u.2
    · have hT' : (T.map (Function.Embedding.subtype _)).subtype (· ∈ x.graph.vertices) = T := by
        ext u
        simp [u.2]
      rwa [hT']
  · rintro ⟨S, -, hS⟩
    exact ⟨_, hS⟩

/-! ### Membership in NP -/

/-- The ordered pairs `(u, v)` of adjacent distinct declared vertices with `u ∈ S` and `v ∉ S`. -/
def crossingPairs (G : Graph) (S : List ℕ) : List (ℕ × ℕ) :=
  (G.distinctVertices.flatMap fun u => G.distinctVertices.map fun v => (u, v)).filter
    fun p => G.adjBool p.1 p.2 && (decide (p.1 ∈ S) && !decide (p.2 ∈ S))

/-- The check of a side `S` of a cut, given as a list: at least `x.bound` crossing pairs. -/
def check (x : SimpleMaxCutInstance × List ℕ) : Bool :=
  decide (x.1.bound ≤ (crossingPairs x.1.graph x.2).length)

/-- The check of a side of a cut is polynomial-time. -/
theorem computableInPolyTime_check :
    ComputableInPolyTime check (encPair encSimpleMaxCut (encList encNat)) encBool := by
  unfold check crossingPairs
  fun_prop

theorem check_eq_true_iff (x : SimpleMaxCutInstance) (l : List ℕ) :
    check (x, l) = true ↔ x.bound ≤ (x.graph.induced.interedges
      (l.toFinset.subtype (· ∈ x.graph.vertices))
      (l.toFinset.subtype (· ∈ x.graph.vertices))ᶜ).card := by
  have hnd : (crossingPairs x.graph l).Nodup :=
    (x.graph.nodup_distinctVertices.product x.graph.nodup_distinctVertices).filter _
  rw [card_interedges_eq_length x.graph l.toFinset hnd fun p => ?_]
  · simp [check]
  · simp only [crossingPairs, List.mem_filter, List.mem_flatMap, List.mem_map,
      Graph.mem_distinctVertices, Bool.and_eq_true, Graph.adjBool_eq_true_iff,
      decide_eq_true_eq, Bool.not_eq_true', decide_eq_false_iff_not, List.mem_toFinset]
    constructor
    · rintro ⟨⟨u, hu, v, hv, rfl⟩, hadj, h1, h2⟩
      exact ⟨hu, hv, hadj, h1, h2⟩
    · rintro ⟨hu, hv, hadj, h1, h2⟩
      exact ⟨⟨p.1, hu, p.2, hv, rfl⟩, hadj, h1, h2⟩

/-- `SimpleMaxCut` belongs to `NP`: a certificate selects the side `S` of the cut among the
declared vertices. -/
theorem mem_NP : SimpleMaxCut ∈ NP encSimpleMaxCut := by
  have hset : SimpleMaxCut = {x | ∃ S : Finset ℕ, (∀ v ∈ S, v ∈ x.graph.vertices) ∧
      x.bound ≤ (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
        (S.subtype (· ∈ x.graph.vertices))ᶜ).card} :=
    Set.ext fun _ => mem_SimpleMaxCut_iff
  rw [hset]
  exact mem_NP_of_subsetWitness (encγ := encNat) (vs := fun x => x.graph.vertices)
    (P := fun x S => x.bound ≤ (x.graph.induced.interedges (S.subtype (· ∈ x.graph.vertices))
        (S.subtype (· ∈ x.graph.vertices))ᶜ).card)
    (by fun_prop) computableInPolyTime_check fun x l _ _ => check_eq_true_iff x l

/-! ### Simple edge lists -/

/-- The number of entries of the edge list `E` whose endpoints lie on different sides of `side`:
the cut of a multigraph of unit edges, where parallel edges count separately and loops never
cross. -/
@[expose] def crossCount (E : List (ℕ × ℕ)) (side : ℕ → Bool) : ℕ :=
  E.countP fun e => side e.1 != side e.2

theorem crossCount_congr {E : List (ℕ × ℕ)} {side side' : ℕ → Bool}
    (h : ∀ e ∈ E, side e.1 = side' e.1 ∧ side e.2 = side' e.2) :
    crossCount E side = crossCount E side' :=
  List.countP_congr fun e he => by rw [(h e he).1, (h e he).2]

/-- Both orientations of the entries of an edge list. -/
@[expose] def orientations (E : List (ℕ × ℕ)) : List (ℕ × ℕ) := E.flatMap fun e => [e, e.swap]

/-- **Cuts of simple edge lists.** If the orientations of the edges of `G` are pairwise distinct
(no loops and no repeated edge, in either direction) and the edges join declared vertices, then
the cut of `G.induced` at `S` is the number of edges with exactly one endpoint in `S`. -/
theorem card_interedges_eq_crossCount (G : Graph) (S : Finset ℕ)
    (hnd : (orientations G.edges).Nodup) (hV : ∀ e ∈ G.edges, e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices) :
    (G.induced.interedges (S.subtype (· ∈ G.vertices))
      (S.subtype (· ∈ G.vertices))ᶜ).card = crossCount G.edges fun v => decide (v ∈ S) := by
  have hloop : ∀ e ∈ G.edges, e.1 ≠ e.2 := by
    intro e he heq
    have := (List.nodup_flatMap.1 hnd).1 e he
    simp only [List.nodup_cons, List.mem_singleton, List.not_mem_nil, not_false_eq_true,
      List.nodup_nil, and_self, and_true] at this
    exact this (Prod.ext heq heq.symm)
  rw [card_interedges_eq_length G S
    (l := (orientations G.edges).filter fun p => decide (p.1 ∈ S) && !decide (p.2 ∈ S))
    (hnd.filter _) fun p => ?_]
  · unfold orientations crossCount
    induction G.edges with
    | nil => rfl
    | cons e E ih =>
      simp only [List.flatMap_cons, List.filter_append, List.length_append, ih,
        List.countP_cons]
      by_cases h1 : e.1 ∈ S <;> by_cases h2 : e.2 ∈ S <;>
        simp [h1, h2, Prod.swap] <;> omega
  · simp only [orientations, List.mem_filter, List.mem_flatMap, List.mem_cons,
      List.not_mem_nil, or_false, Bool.and_eq_true, decide_eq_true_eq,
      Bool.not_eq_true', decide_eq_false_iff_not, Graph.toSimpleGraph_adj]
    constructor
    · rintro ⟨⟨e, he, hp | hp⟩, h1, h2⟩
      · subst hp
        exact ⟨(hV _ he).1, (hV _ he).2, ⟨hloop _ he, Or.inl he⟩, h1, h2⟩
      · subst hp
        exact ⟨(hV e he).2, (hV e he).1, ⟨(hloop e he).symm, Or.inr (by simpa using he)⟩,
          h1, h2⟩
    · rintro ⟨-, -, ⟨-, hp | hp⟩, h1, h2⟩
      · exact ⟨⟨p, hp, Or.inl rfl⟩, h1, h2⟩
      · exact ⟨⟨p.swap, hp, Or.inr rfl⟩, h1, h2⟩

/-! ### Subdivision -/

/-- The path `2u – 4k+1 – 4k+3 – 2v` replacing the `k`-th edge `(u, v)` of a multigraph. -/
def pathEdges (e : ℕ × ℕ) (k : ℕ) : List (ℕ × ℕ) :=
  [(2 * e.1, 4 * k + 1), (4 * k + 1, 4 * k + 3), (4 * k + 3, 2 * e.2)]

/-- The edges of the paths replacing the edges of `E`. -/
def subdivisionEdges (E : List (ℕ × ℕ)) : List (ℕ × ℕ) :=
  (List.range E.length).flatMap fun k => pathEdges (E.getD k (0, 0)) k

/-- **Subdivision of a multigraph.** Each edge of `E` is replaced by a path of three edges through
two fresh vertices; the result is a simple graph. -/
def subdivide (E : List (ℕ × ℕ)) : Graph :=
  ⟨(subdivisionEdges E).flatMap fun e => [e.1, e.2], subdivisionEdges E⟩

theorem nodup_orientations_subdivide (E : List (ℕ × ℕ)) :
    (orientations (subdivide E).edges).Nodup := by
  simp only [subdivide, subdivisionEdges, orientations, List.flatMap_assoc]
  refine List.nodup_flatMap.2 ⟨fun k _ => ?_, List.nodup_range.imp fun {i j} hij => ?_⟩
  · simp only [pathEdges, List.flatMap_cons, List.flatMap_nil, List.cons_append,
      List.nil_append, List.append_nil, Prod.swap, List.nodup_cons, List.mem_cons,
      List.not_mem_nil, Prod.mk.injEq, or_false, List.nodup_nil, not_or, and_true, true_and,
      not_false_eq_true]
    and_intros <;> omega
  · simp only [Function.onFun, List.disjoint_left, pathEdges, List.flatMap_cons,
      List.flatMap_nil, List.cons_append, List.nil_append, List.append_nil, Prod.swap,
      List.mem_cons, List.not_mem_nil, or_false]
    rintro p (rfl | rfl | rfl | rfl | rfl | rfl) <;>
      simp only [Prod.mk.injEq, not_or] <;> and_intros <;> omega

theorem endpoints_mem_subdivide (E : List (ℕ × ℕ)) :
    ∀ e ∈ (subdivide E).edges, e.1 ∈ (subdivide E).vertices ∧ e.2 ∈ (subdivide E).vertices :=
  fun e he => ⟨List.mem_flatMap.2 ⟨e, he, by simp⟩, List.mem_flatMap.2 ⟨e, he, by simp⟩⟩

theorem crossCount_subdivide (E : List (ℕ × ℕ)) (side : ℕ → Bool) :
    crossCount (subdivide E).edges side =
      ((List.range E.length).map fun k => crossCount (pathEdges (E.getD k (0, 0)) k) side).sum :=
  List.countP_flatMap ..

/-- A path of three edges has at most `2 + [u, v separated]` crossing edges. -/
theorem crossCount_pathEdges_le (e : ℕ × ℕ) (k : ℕ) (side : ℕ → Bool) :
    crossCount (pathEdges e k) side ≤ 2 + crossCount [(2 * e.1, 2 * e.2)] side := by
  simp only [crossCount, pathEdges, List.countP_cons, List.countP_nil]
  generalize side (2 * e.1) = a
  generalize side (4 * k + 1) = b
  generalize side (4 * k + 3) = c
  generalize side (2 * e.2) = d
  revert a b c d
  decide

/-- The crossing edges of a multigraph, counted along its edge positions. -/
theorem crossCount_eq_sum_range (E : List (ℕ × ℕ)) (side : ℕ → Bool) :
    crossCount E side =
      ((List.range E.length).map fun k => crossCount [E.getD k (0, 0)] side).sum := by
  conv_lhs => rw [← List.map_getD_range E (0, 0)]
  unfold crossCount
  rw [List.countP_map]
  induction List.range E.length with
  | nil => rfl
  | cons k l ih => simp only [List.countP_cons, List.map_cons, List.sum_cons, ih,
      Function.comp_apply, List.countP_nil]; omega

/-- **Correctness of subdivision.** The subdivided graph has a cut of `2 * E.length + K` edges
exactly when the multigraph `E` has a cut of `K` edges. -/
theorem exists_subdivide_iff (E : List (ℕ × ℕ)) (K : ℕ) :
    (∃ side : ℕ → Bool, 2 * E.length + K ≤ crossCount (subdivide E).edges side) ↔
      ∃ side : ℕ → Bool, K ≤ crossCount E side := by
  constructor
  · rintro ⟨side, h⟩
    refine ⟨fun v => side (2 * v), ?_⟩
    rw [crossCount_subdivide] at h
    rw [crossCount_eq_sum_range]
    have hle := List.sum_le_sum (l := List.range E.length)
      (f := fun k => crossCount (pathEdges (E.getD k (0, 0)) k) side)
      (g := fun k => 2 + crossCount [E.getD k (0, 0)] fun v => side (2 * v))
      fun k _ => crossCount_pathEdges_le _ k side
    rw [List.sum_map_add, List.map_const', List.sum_replicate, List.length_range,
      smul_eq_mul] at hle
    omega
  · rintro ⟨side, h⟩
    let side' : ℕ → Bool := fun v =>
      if v % 2 = 0 then side (v / 2)
      else if v % 4 = 1 then !side (E.getD (v / 4) (0, 0)).1
      else !side (E.getD (v / 4) (0, 0)).2
    refine ⟨side', ?_⟩
    have hpath (k : ℕ) : crossCount (pathEdges (E.getD k (0, 0)) k) side' =
        2 + crossCount [E.getD k (0, 0)] side := by
      have h1 : (4 * k + 1) % 2 ≠ 0 ∧ (4 * k + 1) % 4 = 1 ∧ (4 * k + 1) / 4 = k := by omega
      have h3 : (4 * k + 3) % 2 ≠ 0 ∧ (4 * k + 3) % 4 ≠ 1 ∧ (4 * k + 3) / 4 = k := by omega
      simp only [crossCount, pathEdges, List.countP_cons, List.countP_nil, side', h1, h3,
        Nat.mul_mod_right, Nat.mul_div_cancel_left _ two_pos, ite_true, ite_false]
      cases side (E.getD k (0, 0)).1 <;> cases side (E.getD k (0, 0)).2 <;> rfl
    rw [crossCount_subdivide, List.map_congr_left fun k _ => hpath k, List.sum_map_add,
      List.map_const', List.sum_replicate, List.length_range, smul_eq_mul,
      ← crossCount_eq_sum_range]
    omega

/-! ### The multigraph of a formula -/

/-- The vertex of the literal `(i, b)`: `2 * i` when `b` is true, `2 * i + 1` otherwise. -/
def literalVertex (l : Literal ℕ) : ℕ := if l.2 then 2 * l.1 else 2 * l.1 + 1

/-- The edge between the two literal vertices of the variable of `l`. -/
def variableEdge (l : Literal ℕ) : ℕ × ℕ := (2 * l.1, 2 * l.1 + 1)

/-- The edges of a clause of three literals `a, b, c`: the triangle on their vertices and the
edges of their variables. -/
def clauseEdges (c : Clause ℕ) : List (ℕ × ℕ) :=
  let a := c.getD 0 (0, false)
  let b := c.getD 1 (0, false)
  let d := c.getD 2 (0, false)
  [(literalVertex a, literalVertex b), (literalVertex b, literalVertex d),
    (literalVertex a, literalVertex d), variableEdge a, variableEdge b, variableEdge d]

/-- The multigraph of a formula: the edges of its clauses. -/
def formulaEdges (φ : CNF ℕ) : List (ℕ × ℕ) := φ.flatMap clauseEdges

theorem length_formulaEdges (φ : CNF ℕ) : (formulaEdges φ).length = 6 * φ.length := by
  simp only [formulaEdges, List.length_flatMap, clauseEdges, List.length_cons, List.length_nil]
  induction φ with
  | nil => rfl
  | cons c φ ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; ring

/-- Crossing counts on Boolean sides: a triangle `a, b, d` has at most two crossing edges, and
exactly two when `a, b, d` are not all equal; a single edge has at most one. -/
private theorem triangle_count (a b d x y z x' y' z' : Bool) :
    (((if (a != b) = true then 1 else 0) + (if (b != d) = true then 1 else 0) +
      (if (a != d) = true then 1 else 0)) ≤ 2) ∧
    ((((if (a != b) = true then 1 else 0) + (if (b != d) = true then 1 else 0) +
      (if (a != d) = true then 1 else 0)) = 2) ↔ ((a || b || d) && (!a || !b || !d)) = true) ∧
    ((if (x != x') = true then 1 else 0) ≤ 1) ∧ ((if (y != y') = true then 1 else 0) ≤ 1) ∧
      ((if (z != z') = true then 1 else 0) ≤ 1) := by
  revert a b d x y z x' y' z'
  decide

/-- A clause has at most five crossing edges. -/
theorem crossCount_clauseEdges_le (c : Clause ℕ) (side : ℕ → Bool) :
    crossCount (clauseEdges c) side ≤ 5 := by
  simp only [crossCount, clauseEdges, variableEdge, List.countP_cons, List.countP_nil]
  have := triangle_count (side (literalVertex (c.getD 0 (0, false))))
    (side (literalVertex (c.getD 1 (0, false)))) (side (literalVertex (c.getD 2 (0, false))))
    (side (2 * (c.getD 0 (0, false)).1)) (side (2 * (c.getD 1 (0, false)).1))
    (side (2 * (c.getD 2 (0, false)).1)) (side (2 * (c.getD 0 (0, false)).1 + 1))
    (side (2 * (c.getD 1 (0, false)).1 + 1)) (side (2 * (c.getD 2 (0, false)).1 + 1))
  omega

/-- The side of a literal vertex, when the two vertices of its variable are separated. -/
theorem side_literalVertex {side : ℕ → Bool} {l : Literal ℕ}
    (h : side (2 * l.1) ≠ side (2 * l.1 + 1)) :
    side (literalVertex l) = l.eval fun i => side (2 * i) := by
  obtain ⟨i, b⟩ := l
  cases b <;> cases hs : side (2 * i) <;> simp_all [literalVertex, Literal.eval]

/-- A clause of three literals has five crossing edges exactly when the vertices of its
variables are separated and its literals are not all equal under the sides of `2 * i`. -/
theorem crossCount_clauseEdges_eq_five_iff {c : Clause ℕ} (hc : c.length = 3)
    (side : ℕ → Bool) :
    crossCount (clauseEdges c) side = 5 ↔ (∀ l ∈ c, side (2 * l.1) ≠ side (2 * l.1 + 1)) ∧
      ((Clause.eval (fun i => side (2 * i)) c &&
        Clause.eval (fun i => !side (2 * i)) c) = true) := by
  match c, hc with
  | [a, b, d], _ =>
    simp only [crossCount, clauseEdges, variableEdge, List.getD_cons_zero,
      List.getD_cons_succ, List.countP_cons, List.countP_nil]
    have ht := triangle_count (side (literalVertex a)) (side (literalVertex b))
      (side (literalVertex d)) (side (2 * a.1)) (side (2 * b.1)) (side (2 * d.1))
      (side (2 * a.1 + 1)) (side (2 * b.1 + 1)) (side (2 * d.1 + 1))
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
    constructor
    · intro h
      have hx : side (2 * a.1) ≠ side (2 * a.1 + 1) := by
        intro hx; simp only [hx, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ht; omega
      have hy : side (2 * b.1) ≠ side (2 * b.1 + 1) := by
        intro hy; simp only [hy, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ht; omega
      have hz : side (2 * d.1) ≠ side (2 * d.1 + 1) := by
        intro hz; simp only [hz, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at h ht; omega
      have hv : (if (side (2 * a.1) != side (2 * a.1 + 1)) = true then 1 else 0) +
          (if (side (2 * b.1) != side (2 * b.1 + 1)) = true then 1 else 0) +
          (if (side (2 * d.1) != side (2 * d.1 + 1)) = true then 1 else 0) = 3 := by
        simp [hx, hy, hz]
      have h2 := ht.2.1.1 (by omega)
      refine ⟨⟨hx, hy, hz⟩, ?_⟩
      rw [side_literalVertex hx, side_literalVertex hy, side_literalVertex hz] at h2
      simpa [Clause.eval, Bool.or_assoc] using h2
    · rintro ⟨⟨hx, hy, hz⟩, h⟩
      have hv : (if (side (2 * a.1) != side (2 * a.1 + 1)) = true then 1 else 0) +
          (if (side (2 * b.1) != side (2 * b.1 + 1)) = true then 1 else 0) +
          (if (side (2 * d.1) != side (2 * d.1 + 1)) = true then 1 else 0) = 3 := by
        simp [hx, hy, hz]
      have h2 := ht.2.1.2 (by
        rw [side_literalVertex hx, side_literalVertex hy, side_literalVertex hz]
        simpa [Clause.eval, Bool.or_assoc] using h)
      omega

/-- Natural numbers at most `5` with sum at least `5 * l.length` are all `5`. -/
private theorem eq_five_of_le_sum {α : Type*} (f : α → ℕ) (hf : ∀ a, f a ≤ 5) :
    ∀ l : List α, 5 * l.length ≤ (l.map f).sum → ∀ a ∈ l, f a = 5
  | [], _ => by simp
  | b :: l, h => by
    simp only [List.length_cons, List.map_cons, List.sum_cons] at h
    have hl : (l.map f).sum ≤ 5 * l.length := by
      simpa [mul_comm] using List.sum_le_sum (l := l) (f := f) (g := fun _ => 5) fun a _ => hf a
    have hb := hf b
    intro a ha
    rcases List.mem_cons.1 ha with rfl | ha
    · omega
    · exact eq_five_of_le_sum f hf l (by omega) a ha

/-- **Correctness of the formula multigraph.** For a formula of three-literal clauses, a cut of
`5 * φ.length` edges exists exactly when the formula is NAE-satisfiable. -/
theorem exists_le_crossCount_formulaEdges_iff {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length = 3) :
    (∃ side : ℕ → Bool, 5 * φ.length ≤ crossCount (formulaEdges φ) side) ↔ φ.NAESatisfiable := by
  have hsum (side : ℕ → Bool) : crossCount (formulaEdges φ) side =
      (φ.map fun c => crossCount (clauseEdges c) side).sum :=
    List.countP_flatMap ..
  constructor
  · rintro ⟨side, h⟩
    rw [hsum] at h
    have h5 := eq_five_of_le_sum (fun c => crossCount (clauseEdges c) side)
      (crossCount_clauseEdges_le · side) φ h
    refine ⟨fun i => side (2 * i), ?_⟩
    rw [CNF.evalNAE, CNF.eval, CNF.eval, Bool.and_eq_true, List.all_eq_true, List.all_eq_true]
    have hc := fun c hc' => ((crossCount_clauseEdges_eq_five_iff (hφ c hc') side).1
      (h5 c hc')).2
    refine ⟨fun c hc' => ?_, fun c hc' => ?_⟩ <;>
      have := hc c hc' <;> simp only [Bool.and_eq_true] at this
    exacts [this.1, this.2]
  · rintro ⟨σ, hσ⟩
    let side : ℕ → Bool := fun v => if v % 2 = 0 then σ (v / 2) else !σ (v / 2)
    have hs0 (i : ℕ) : side (2 * i) = σ i := by simp [side]
    have hs1 (i : ℕ) : side (2 * i + 1) = !σ i := by
      have : (2 * i + 1) % 2 ≠ 0 ∧ (2 * i + 1) / 2 = i := by omega
      simp [side, this]
    refine ⟨side, ?_⟩
    rw [hsum]
    have h5 : ∀ c ∈ φ, crossCount (clauseEdges c) side = 5 := by
      intro c hc
      rw [crossCount_clauseEdges_eq_five_iff (hφ c hc)]
      refine ⟨fun l _ => by simp [hs0, hs1], ?_⟩
      simp only [CNF.evalNAE, CNF.eval, Bool.and_eq_true, List.all_eq_true] at hσ
      simp only [hs0, Bool.and_eq_true]
      exact ⟨hσ.1 c hc, hσ.2 c hc⟩
    rw [List.map_congr_left h5, List.map_const', List.sum_replicate, smul_eq_mul, mul_comm]

/-! ### Polynomial time -/

@[fun_prop]
theorem computableInPolyTime_literalVertex :
    ComputableInPolyTime literalVertex (encPair encNat encBool) encNat := by
  unfold literalVertex
  fun_prop

@[fun_prop]
theorem computableInPolyTime_variableEdge :
    ComputableInPolyTime variableEdge (encPair encNat encBool) (encPair encNat encNat) := by
  unfold variableEdge
  fun_prop

@[fun_prop]
theorem computableInPolyTime_formulaEdges :
    ComputableInPolyTime formulaEdges encCNF (encList (encPair encNat encNat)) := by
  have h0 := EUThreeSAT.computableInPolyTime_literalAt 0
  have h1 := EUThreeSAT.computableInPolyTime_literalAt 1
  have h2 := EUThreeSAT.computableInPolyTime_literalAt 2
  unfold formulaEdges clauseEdges encCNF
  fun_prop

@[fun_prop]
theorem computableInPolyTime_subdivisionEdges :
    ComputableInPolyTime subdivisionEdges (encList (encPair encNat encNat))
      (encList (encPair encNat encNat)) := by
  have hget : ComputableInPolyTime (fun p : List (ℕ × ℕ) × ℕ => p.1.getD p.2 (0, 0))
      (encPair (encList (encPair encNat encNat)) encUnary) (encPair encNat encNat) :=
    ComputableInPolyTime.listGetDWithInput (ComputableInPolyTime.fst _ _)
      (ComputableInPolyTime.snd _ _) (0, 0)
  unfold subdivisionEdges pathEdges
  fun_prop

@[fun_prop]
theorem computableInPolyTime_subdivide :
    ComputableInPolyTime subdivide (encList (encPair encNat encNat)) encGraph := by
  unfold subdivide
  fun_prop

end SimpleMaxCut

/-! ### The reduction -/

/-- **The reduction from `NAEEUThreeSAT` to `SimpleMaxCut`**, on formulas of three-literal
clauses: the subdivided multigraph of the formula, with bound `17 * φ.length`. -/
def toSimpleMaxCut (φ : CNF ℕ) : SimpleMaxCutInstance :=
  ⟨SimpleMaxCut.subdivide (SimpleMaxCut.formulaEdges φ), 17 * φ.length⟩

open SimpleMaxCut in
/-- **Correctness of the reduction to `SimpleMaxCut`.** -/
theorem toSimpleMaxCut_mem_iff {φ : CNF ℕ} (hφ : ∀ c ∈ φ, c.length = 3) :
    toSimpleMaxCut φ ∈ SimpleMaxCut ↔ φ.NAESatisfiable := by
  rw [← exists_le_crossCount_formulaEdges_iff hφ, ← exists_subdivide_iff,
    length_formulaEdges, mem_SimpleMaxCut_iff]
  set G := subdivide (formulaEdges φ)
  have hb : 17 * φ.length = 2 * (6 * φ.length) + 5 * φ.length := by ring
  change (∃ S : Finset ℕ, (∀ v ∈ S, v ∈ G.vertices) ∧ 17 * φ.length ≤
    (G.induced.interedges (S.subtype (· ∈ G.vertices))
      (S.subtype (· ∈ G.vertices))ᶜ).card) ↔ _
  simp only [card_interedges_eq_crossCount G _ (nodup_orientations_subdivide _)
    (endpoints_mem_subdivide _), hb]
  constructor
  · rintro ⟨S, -, hS⟩
    exact ⟨_, hS⟩
  · rintro ⟨side, hside⟩
    refine ⟨(G.vertices.filter side).toFinset, fun v hv => ?_, ?_⟩
    · exact (List.mem_filter.1 (List.mem_toFinset.1 hv)).1
    · rwa [crossCount_congr (side' := side) fun e he => by
        have : e.1 ∈ G.vertices ∧ e.2 ∈ G.vertices := endpoints_mem_subdivide _ e he
        simp [this.1, this.2]]

/-- The output graph has `18` edges per clause: six edges of the clause multigraph, each
subdivided into three. -/
theorem length_edges_toSimpleMaxCut (φ : CNF ℕ) :
    (toSimpleMaxCut φ).graph.edges.length = 18 * φ.length := by
  simp only [toSimpleMaxCut, SimpleMaxCut.subdivide, SimpleMaxCut.subdivisionEdges,
    SimpleMaxCut.pathEdges, List.length_flatMap, List.length_cons, List.length_nil,
    List.map_const', List.sum_replicate, List.length_range, smul_eq_mul,
    SimpleMaxCut.length_formulaEdges]
  ring

/-- The reduction `toSimpleMaxCut` is polynomial-time. -/
@[fun_prop]
theorem computableInPolyTime_toSimpleMaxCut :
    ComputableInPolyTime toSimpleMaxCut encCNF encSimpleMaxCut := by
  unfold toSimpleMaxCut
  fun_prop

/-- The empty graph has no crossing edge, so the bound `1` is unreachable. -/
theorem empty_not_mem_SimpleMaxCut : (⟨⟨[], []⟩, 1⟩ : SimpleMaxCutInstance) ∉ SimpleMaxCut := by
  rintro ⟨S, hS⟩
  have : (Graph.induced ⟨[], []⟩).interedges S Sᶜ = ∅ := by
    ext ⟨u, -⟩
    exact absurd u.2 (List.not_mem_nil)
  simp [this] at hS

/-- `NAEEUThreeSAT` reduces to `SimpleMaxCut` in polynomial time; malformed formulas map to an
unreachable bound on the empty graph. -/
theorem polyTimeReducible_NAEEUThreeSAT_SimpleMaxCut :
    PolyTimeReducible encCNF encSimpleMaxCut NAEEUThreeSAT SimpleMaxCut := by
  refine .of_guard _ EUThreeSAT.computableInPolyTime_syntaxCheck
    computableInPolyTime_toSimpleMaxCut empty_not_mem_SimpleMaxCut fun φ => ?_
  rw [EUThreeSAT.syntaxCheck_iff]
  constructor
  · rintro ⟨h, hs⟩
    exact ⟨h, (toSimpleMaxCut_mem_iff fun c hc => (h c hc).1).2 hs⟩
  · rintro ⟨h, hs⟩
    exact ⟨h, (toSimpleMaxCut_mem_iff fun c hc => (h c hc).1).1 hs⟩

/-- `SimpleMaxCut` is `NP`-hard. -/
theorem SimpleMaxCut_npHard : NPHard encSimpleMaxCut SimpleMaxCut :=
  NAEEUThreeSAT_npHard.trans polyTimeReducible_NAEEUThreeSAT_SimpleMaxCut

/-- **Unweighted maximum cut is NP-complete** [Arora and Barak, Exercise 2.15][AroraBarak09]: given
a simple graph `G` and a number `K` in binary, deciding whether some vertex set has at least `K`
edges to its complement is `NP`-complete. -/
theorem SimpleMaxCut_npComplete : NPComplete encSimpleMaxCut SimpleMaxCut :=
  ⟨SimpleMaxCut.mem_NP, SimpleMaxCut_npHard⟩

end Cslib.Complexity
