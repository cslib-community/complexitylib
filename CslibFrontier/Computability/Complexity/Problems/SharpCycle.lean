/-
Copyright (c) 2026 Christian Reitwiessner. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Christian Reitwiessner
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Hamiltonian
public import Mathlib.Data.Set.Card
import CslibFrontier.Computability.Complexity.Problems.Hamiltonian.Directed
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.List
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Nat.BinaryPair
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain
import Mathlib.Data.List.Permutation
import Mathlib.Data.List.Rotate
import Mathlib.Data.List.Sublists
import Mathlib.Data.Fintype.Pi

/-!
# Counting simple directed cycles: #CYCLE

`SharpCycle G` is the number of simple directed cycles of a graph `G` (`Cslib.Complexity.Graph`),
read as a directed graph through its arcs `(u, v) ∈ G.edges` exactly as `DirHamCycle` reads it.
A simple cycle is a `Cycle ℕ`, a list up to rotation, that is nonempty, has no repeated vertices,
contains only declared vertices, and whose consecutive vertices, read cyclically, are joined by
arcs (`Cslib.Complexity.Graph.IsSimpleCycle`). In particular a self-loop is a cycle of length one.

[Arora and Barak, Theorem 9.4][AroraBarak07] (web draft of 2007-01-08, §9.1, printed p. 173 /
PDF p. 189) shows that computing `#CYCLE` is as hard as deciding whether a digraph has a
Hamiltonian cycle. The reduction (`Cslib.Complexity.SharpCycle.reduce`)
replaces every arc `(u, v)` by a gadget of `m` layers of two nodes, complete between consecutive
layers, from `u` to `v`. It has `2 ^ m` paths from `u` to `v`. A simple cycle of the gadget graph
is a simple cycle of `G` with a path chosen through the gadget of each of its arcs, so a cycle of
length `k` of `G` gives `2 ^ (m * k)` cycles. With `n` distinct vertices and
`m = n * n + n + 1`, `G` has fewer than `2 ^ m` simple cycles, so a Hamiltonian cycle alone gives
`2 ^ (m * n)` cycles and without one the total stays below `2 ^ (m * n)`
(`Cslib.Complexity.SharpCycle.mem_DirHamCycle_iff`). The draft takes `m = n log n + 1`; any
polynomial `m` with `2 ^ m` above the number of cycles of `G` works.

The original vertex `v` becomes `2 * v` (`Cslib.Complexity.SharpCycle.origNode`) and the gadget
nodes are odd (`Cslib.Complexity.SharpCycle.gadgetNode`), so the two kinds never collide. Every
simple cycle of the gadget graph passes through an original vertex, since the layer index grows
along arcs between gadget nodes. Starting there, it decomposes into arcs of `G` and their gadget
paths, and the arcs form a simple cycle of `G`. Conversely, every simple cycle of `G` and every
choice of bits gives a simple cycle of the gadget graph, and different bits give different cycles.

`FP` for a natural-valued function is read as polynomial-time computability with binary output
(`ComputableInPolyTime SharpCycle encGraph encNat`), with graphs in the encoding `encGraph` of
`DirHamCycle`.

## Main definitions

* `Cslib.Complexity.Graph.IsSimpleCycle`: simple directed cycles.
* `Cslib.Complexity.SharpCycle`: the number of simple directed cycles.
* `Cslib.Complexity.SharpCycle.gadgetGraph`, `Cslib.Complexity.SharpCycle.layers`,
  `Cslib.Complexity.SharpCycle.reduce`: the gadget graph with `n * n + n + 1` layers.

## Main results

* `Cslib.Complexity.SharpCycle.finite_setOf_isSimpleCycle`: a graph has finitely many simple
  cycles.
* `Cslib.Complexity.SharpCycle.two_pow_le_of_mem_DirHamCycle`,
  `Cslib.Complexity.SharpCycle.lt_two_pow_of_notMem_DirHamCycle`: the counting inequalities.
* `Cslib.Complexity.SharpCycle.mem_DirHamCycle_iff`:
  `G ∈ DirHamCycle ↔ 2 ^ (m * n) ≤ SharpCycle (reduce G)`.
* `Cslib.Complexity.SharpCycle.computableInPolyTime_reduce`: the gadget graph is computable in
  polynomial time.
* `Cslib.Complexity.SharpCycle.DirHamCycle_mem_P`: if `SharpCycle` is computable in polynomial
  time with binary output, then `DirHamCycle ∈ P encGraph`.
* `Cslib.Complexity.P_eq_NP_of_computableInPolyTime_SharpCycle`: **Theorem 9.4**, if `SharpCycle`
  is computable in polynomial time with binary output (`#CYCLE ∈ FP`), then `P = NP`.

## References

* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, web draft of
  2007-01-08][AroraBarak07]
-/

@[expose] public section

namespace Cslib.Complexity

namespace Graph

/-- `c` is a simple directed cycle of `G`: a nonempty cycle without repeated vertices, of declared
vertices, whose consecutive vertices, read cyclically, are joined by arcs. -/
def IsSimpleCycle (G : Graph) (c : Cycle ℕ) : Prop :=
  c ≠ Cycle.nil ∧ c.Nodup ∧ (∀ v ∈ c, v ∈ G.vertices) ∧ c.Chain fun u v => (u, v) ∈ G.edges

theorem isSimpleCycle_coe {G : Graph} {p : List ℕ} :
    G.IsSimpleCycle (p : Cycle ℕ) ↔ p ≠ [] ∧ p.Nodup ∧ (∀ v ∈ p, v ∈ G.vertices) ∧
      (p : Cycle ℕ).Chain fun u v => (u, v) ∈ G.edges := by
  simp only [IsSimpleCycle, ne_eq, Cycle.coe_eq_nil, Cycle.nodup_coe_iff, Cycle.mem_coe_iff]

end Graph

/-- **#CYCLE** [Arora and Barak, Theorem 9.4][AroraBarak07]: the number of simple directed cycles
of `G`. -/
noncomputable def SharpCycle (G : Graph) : ℕ := {c : Cycle ℕ | G.IsSimpleCycle c}.ncard

namespace SharpCycle

/-! ### Finitely many cycles -/

/-- The lists of distinct elements of `l`, possibly with repetitions in the enumeration. -/
private def nodupLists (l : List ℕ) : List (List ℕ) := l.sublists.flatMap List.permutations

private theorem mem_nodupLists {l p : List ℕ} (hp : p.Nodup) (h : ∀ v ∈ p, v ∈ l) :
    p ∈ nodupLists l := by
  obtain ⟨t, hpt, ht⟩ := hp.subperm h
  exact List.mem_flatMap.2 ⟨t, List.mem_sublists.2 ht, List.mem_permutations.2 hpt.symm⟩

private theorem length_nodupLists_le (l : List ℕ) :
    (nodupLists l).length ≤ 2 ^ l.length * l.length.factorial := by
  rw [nodupLists, List.length_flatMap, ← List.length_sublists]
  have := List.sum_le_length_nsmul (l.sublists.map fun a => a.permutations.length)
    l.length.factorial fun x hx => by
      obtain ⟨s, hs, rfl⟩ := List.mem_map.1 hx
      rw [List.length_permutations]
      exact Nat.factorial_le (List.mem_sublists.1 hs).length_le
  simpa using this

/-- Every simple cycle of `G` is a list of distinct declared vertices up to rotation. -/
private theorem exists_eq_coe_of_isSimpleCycle {G : Graph} {c : Cycle ℕ} (hc : G.IsSimpleCycle c) :
    ∃ p ∈ nodupLists G.distinctVertices, c = (p : Cycle ℕ) := by
  induction c using Quotient.inductionOn' with
  | h p =>
    obtain ⟨-, hnd, hv, -⟩ := Graph.isSimpleCycle_coe.1 hc
    exact ⟨p, mem_nodupLists hnd fun v h => Graph.mem_distinctVertices.2 (hv v h), rfl⟩

/-- A graph has finitely many simple cycles. -/
theorem finite_setOf_isSimpleCycle (G : Graph) : {c : Cycle ℕ | G.IsSimpleCycle c}.Finite := by
  refine ((nodupLists G.distinctVertices).finite_toSet.image
    fun p : List ℕ => (p : Cycle ℕ)).subset fun c hc => ?_
  obtain ⟨p, hp, rfl⟩ := exists_eq_coe_of_isSimpleCycle hc
  exact ⟨p, hp, rfl⟩

/-! ### The gadget graph -/

/-- The node of the original vertex `v` in the gadget graph. -/
def origNode (v : ℕ) : ℕ := 2 * v

/-- Node `b` of layer `j` of the gadget of the arc `(u, v)`. -/
def gadgetNode (u v j : ℕ) (b : Bool) : ℕ := 2 * Nat.pair (Nat.pair u v) (2 * j + b.toNat) + 1

/-- The `2 * m` nodes of the gadget of the arc `e`. -/
def gadgetVertices (m : ℕ) (e : ℕ × ℕ) : List ℕ :=
  (List.range m).flatMap fun j => [gadgetNode e.1 e.2 j false, gadgetNode e.1 e.2 j true]

/-- The arcs of the gadget of the arc `e`: from `e.1` to both nodes of the first layer, from both
nodes of each layer to both nodes of the next, and from both nodes of the last layer to `e.2`. -/
def gadgetArcs (m : ℕ) (e : ℕ × ℕ) : List (ℕ × ℕ) :=
  [false, true].flatMap fun b =>
    (origNode e.1, gadgetNode e.1 e.2 0 b) :: (gadgetNode e.1 e.2 (m - 1) b, origNode e.2) ::
      (List.range (m - 1)).flatMap fun j =>
        [(gadgetNode e.1 e.2 j b, gadgetNode e.1 e.2 (j + 1) false),
          (gadgetNode e.1 e.2 j b, gadgetNode e.1 e.2 (j + 1) true)]

/-- The gadget graph of `G` with `m` layers: the original vertices and a gadget for every arc. -/
def gadgetGraph (m : ℕ) (G : Graph) : Graph :=
  ⟨G.vertices.map origNode ++ G.edges.flatMap (gadgetVertices m),
    G.edges.flatMap (gadgetArcs m)⟩

/-- The number of layers of the reduction, for `n` distinct vertices: `n * n + n + 1`. -/
def layers (G : Graph) : ℕ := G.distinctVertices.length * G.distinctVertices.length +
  G.distinctVertices.length + 1

/-- The reduction from `DirHamCycle` to `#CYCLE` [Arora and Barak, Theorem 9.4][AroraBarak07]. -/
def reduce (G : Graph) : Graph := gadgetGraph (layers G) G

/-! ### Nodes and arcs of the gadget graph -/

theorem origNode_injective : Function.Injective origNode := fun _ _ h => by
  simp only [origNode] at h; omega

theorem origNode_ne_gadgetNode (a u v j : ℕ) (b : Bool) : origNode a ≠ gadgetNode u v j b := by
  simp only [origNode, gadgetNode]; omega

theorem gadgetNode_inj {u v j u' v' j' : ℕ} {b b' : Bool} :
    gadgetNode u v j b = gadgetNode u' v' j' b' ↔ u = u' ∧ v = v' ∧ j = j' ∧ b = b' := by
  refine ⟨fun h => ?_, by rintro ⟨rfl, rfl, rfl, rfl⟩; rfl⟩
  simp only [gadgetNode] at h
  have h1 : Nat.pair (Nat.pair u v) (2 * j + b.toNat) =
      Nat.pair (Nat.pair u' v') (2 * j' + b'.toNat) := by omega
  obtain ⟨h2, h3⟩ := Nat.pair_eq_pair.1 h1
  obtain ⟨rfl, rfl⟩ := Nat.pair_eq_pair.1 h2
  cases b <;> cases b' <;> simp only [Bool.toNat_false, Bool.toNat_true] at h3 <;>
    first | exact ⟨rfl, rfl, by omega, rfl⟩ | (exfalso; omega)

variable {m : ℕ} {G : Graph}

theorem mem_gadgetArcs {u v x y : ℕ} :
    (x, y) ∈ gadgetArcs m (u, v) ↔ (∃ b, x = origNode u ∧ y = gadgetNode u v 0 b) ∨
      (∃ j b b', j + 1 < m ∧ x = gadgetNode u v j b ∧ y = gadgetNode u v (j + 1) b') ∨
      (∃ b, x = gadgetNode u v (m - 1) b ∧ y = origNode v) := by
  simp only [gadgetArcs, List.mem_flatMap, List.mem_cons, List.mem_range, Prod.mk.injEq,
    List.not_mem_nil, or_false]
  constructor
  · rintro ⟨b, -, h | h | ⟨j, hj, h | h⟩⟩
    · exact .inl ⟨b, h⟩
    · exact .inr (.inr ⟨b, h⟩)
    · exact .inr (.inl ⟨j, b, false, by omega, h⟩)
    · exact .inr (.inl ⟨j, b, true, by omega, h⟩)
  · rintro (⟨b, h⟩ | ⟨j, b, b', hj, h⟩ | ⟨b, h⟩)
    · exact ⟨b, by cases b <;> simp, .inl h⟩
    · refine ⟨b, by cases b <;> simp, .inr (.inr ⟨j, by omega, ?_⟩)⟩
      cases b' <;> simp [h]
    · exact ⟨b, by cases b <;> simp, .inr (.inl h)⟩

theorem mem_edges_gadgetGraph {x y : ℕ} :
    (x, y) ∈ (gadgetGraph m G).edges ↔ ∃ e ∈ G.edges, (x, y) ∈ gadgetArcs m e := by
  simp [gadgetGraph]

theorem origNode_mem_vertices_gadgetGraph {v : ℕ} :
    origNode v ∈ (gadgetGraph m G).vertices ↔ v ∈ G.vertices := by
  simp only [gadgetGraph, List.mem_append, List.mem_map, List.mem_flatMap, gadgetVertices,
    List.mem_range, List.mem_cons, List.not_mem_nil, or_false]
  constructor
  · rintro (⟨w, hw, h⟩ | ⟨e, -, j, -, h | h⟩)
    · rwa [← origNode_injective h]
    · exact absurd h (origNode_ne_gadgetNode _ _ _ _ _)
    · exact absurd h (origNode_ne_gadgetNode _ _ _ _ _)
  · exact fun h => .inl ⟨v, h, rfl⟩

theorem gadgetNode_mem_vertices_gadgetGraph {u v j : ℕ} {b : Bool} (huv : (u, v) ∈ G.edges)
    (hj : j < m) : gadgetNode u v j b ∈ (gadgetGraph m G).vertices := by
  simp only [gadgetGraph, List.mem_append, List.mem_flatMap, gadgetVertices, List.mem_range,
    List.mem_cons, List.not_mem_nil, or_false]
  exact .inr ⟨(u, v), huv, j, hj, by cases b <;> simp⟩

/-- The arcs leaving an original vertex enter the first layer of a gadget. -/
theorem eq_gadgetNode_of_origNode {u y : ℕ} (h : (origNode u, y) ∈ (gadgetGraph m G).edges) :
    ∃ v b, (u, v) ∈ G.edges ∧ y = gadgetNode u v 0 b := by
  obtain ⟨⟨u', v'⟩, he, h⟩ := mem_edges_gadgetGraph.1 h
  rcases mem_gadgetArcs.1 h with ⟨b, hx, rfl⟩ | ⟨j, b, b', -, hx, -⟩ | ⟨b, hx, -⟩
  · obtain rfl := origNode_injective hx
    exact ⟨v', b, he, rfl⟩
  · exact absurd hx (origNode_ne_gadgetNode _ _ _ _ _)
  · exact absurd hx (origNode_ne_gadgetNode _ _ _ _ _)

/-- The arcs leaving layer `j` of a gadget enter the next layer, or the end of the arc after the
last layer. -/
theorem of_gadgetNode {u v j y : ℕ} {b : Bool}
    (h : (gadgetNode u v j b, y) ∈ (gadgetGraph m G).edges) :
    (u, v) ∈ G.edges ∧ ((j + 1 < m ∧ ∃ b', y = gadgetNode u v (j + 1) b') ∨
      (j = m - 1 ∧ y = origNode v)) := by
  obtain ⟨⟨u', v'⟩, he, h⟩ := mem_edges_gadgetGraph.1 h
  rcases mem_gadgetArcs.1 h with ⟨b', hx, -⟩ | ⟨j', b', b'', hj, hx, rfl⟩ | ⟨b', hx, rfl⟩
  · exact absurd hx.symm (origNode_ne_gadgetNode _ _ _ _ _)
  · obtain ⟨rfl, rfl, rfl, -⟩ := gadgetNode_inj.1 hx
    exact ⟨he, .inl ⟨hj, b'', rfl⟩⟩
  · obtain ⟨rfl, rfl, rfl, -⟩ := gadgetNode_inj.1 hx
    exact ⟨he, .inr ⟨rfl, rfl⟩⟩

/-! ### Walks through gadgets -/

/-- The nodes of layers `j, j + 1, …` of the gadget of `(u, v)` chosen by the bits `c`. -/
private def layerNodes (u v : ℕ) : ℕ → List Bool → List ℕ
  | _, [] => []
  | j, b :: c => gadgetNode u v j b :: layerNodes u v (j + 1) c

/-- The walk from `u` through the steps `s`: each step `(v, c)` goes from the current vertex to
`v` through the gadget nodes chosen by `c`. The final vertex is not included. -/
private def walk : ℕ → List (ℕ × List Bool) → List ℕ
  | _, [] => []
  | u, (v, c) :: s => origNode u :: (layerNodes u v 0 c ++ walk v s)

/-- The vertex reached by the steps `s` from `u`. -/
private def endpoint : ℕ → List (ℕ × List Bool) → ℕ
  | u, [] => u
  | _, (v, _) :: s => endpoint v s

@[simp] private theorem length_layerNodes (u v j : ℕ) (c : List Bool) :
    (layerNodes u v j c).length = c.length := by
  induction c generalizing j <;> simp [layerNodes, *]

private theorem mem_layerNodes {u v j x : ℕ} {c : List Bool} (h : x ∈ layerNodes u v j c) :
    ∃ i < c.length, ∃ b, x = gadgetNode u v (j + i) b := by
  induction c generalizing j with
  | nil => simp [layerNodes] at h
  | cons b c ih =>
    rcases List.mem_cons.1 h with rfl | h
    · exact ⟨0, by simp, b, rfl⟩
    · obtain ⟨i, hi, b', rfl⟩ := ih h
      exact ⟨i + 1, by simp; omega, b', by rw [Nat.add_right_comm, Nat.add_assoc]⟩

private theorem nodup_layerNodes (u v j : ℕ) (c : List Bool) : (layerNodes u v j c).Nodup := by
  induction c generalizing j with
  | nil => simp [layerNodes]
  | cons b c ih =>
    refine List.nodup_cons.2 ⟨fun h => ?_, ih _⟩
    obtain ⟨i, -, b', h⟩ := mem_layerNodes h
    have := (gadgetNode_inj.1 h).2.2.1
    omega

private theorem layerNodes_injective {u v j : ℕ} {c c' : List Bool}
    (h : layerNodes u v j c = layerNodes u v j c') : c = c' := by
  induction c generalizing j c' with
  | nil => cases c' <;> simp_all [layerNodes]
  | cons b c ih =>
    cases c' with
    | nil => simp [layerNodes] at h
    | cons b' c' =>
      simp only [layerNodes, List.cons.injEq] at h
      rw [(gadgetNode_inj.1 h.1).2.2.2, ih h.2]

private theorem walk_append_endpoint (u v : ℕ) (c : List Bool) (s : List (ℕ × List Bool)) :
    walk u ((v, c) :: s) ++ [origNode (endpoint u ((v, c) :: s))] =
      origNode u :: (layerNodes u v 0 c ++ (walk v s ++ [origNode (endpoint v s)])) := by
  simp [walk, endpoint]

private theorem walk_append_endpoint_eq_cons (u : ℕ) (s : List (ℕ × List Bool)) :
    ∃ l, walk u s ++ [origNode (endpoint u s)] = origNode u :: l := by
  cases s with
  | nil => exact ⟨[], rfl⟩
  | cons p s => exact ⟨_, walk_append_endpoint u p.1 p.2 s⟩

/-- The gadget nodes from layer `j` on, followed by the end of the arc, form a path. -/
private theorem isChain_layerNodes {u v : ℕ} (huv : (u, v) ∈ G.edges) :
    ∀ (c : List Bool) (j : ℕ), c ≠ [] → j + c.length = m →
      (layerNodes u v j c ++ [origNode v]).IsChain fun x y => (x, y) ∈ (gadgetGraph m G).edges
  | [], _, h, _ => absurd rfl h
  | [b], j, _, hj => by
    refine List.isChain_pair.2 (mem_edges_gadgetGraph.2 ⟨(u, v), huv, mem_gadgetArcs.2 ?_⟩)
    simp only [List.length_singleton] at hj
    exact .inr (.inr ⟨b, by rw [← hj]; rfl, rfl⟩)
  | b :: b' :: c, j, _, hj => by
    simp only [List.length_cons] at hj
    have ih := isChain_layerNodes huv (b' :: c) (j + 1) (List.cons_ne_nil _ _)
      (by simp only [List.length_cons]; omega)
    have harc : (gadgetNode u v j b, gadgetNode u v (j + 1) b') ∈ (gadgetGraph m G).edges :=
      mem_edges_gadgetGraph.2 ⟨(u, v), huv,
        mem_gadgetArcs.2 (.inr (.inl ⟨j, b, b', by omega, rfl, rfl⟩))⟩
    simp only [layerNodes, List.cons_append] at ih ⊢
    exact List.IsChain.cons_cons harc ih

/-- The walk through the steps `s`, followed by its endpoint, is a path of the gadget graph when
`s` follows arcs of `G` and every step chooses `m` bits. -/
private theorem isChain_walk (hm : 0 < m) :
    ∀ (u : ℕ) (s : List (ℕ × List Bool)), (∀ p ∈ s, p.2.length = m) →
      (u :: s.map Prod.fst).IsChain (fun x y => (x, y) ∈ G.edges) →
      (walk u s ++ [origNode (endpoint u s)]).IsChain
        fun x y => (x, y) ∈ (gadgetGraph m G).edges
  | u, [], _, _ => by simp [walk, endpoint]
  | u, (v, c) :: s, hs, hc => by
    rw [walk_append_endpoint]
    obtain ⟨huv, hc⟩ := List.isChain_cons_cons.1 hc
    have hcm : c.length = m := hs _ List.mem_cons_self
    have ih := isChain_walk hm v s (fun p hp => hs p (List.mem_cons_of_mem _ hp)) hc
    obtain ⟨l, hl⟩ := walk_append_endpoint_eq_cons v s
    rw [hl] at ih ⊢
    have hne : c ≠ [] := by rintro rfl; simp at hcm; omega
    obtain ⟨b, c', rfl⟩ := List.exists_cons_of_ne_nil hne
    have h1 := isChain_layerNodes huv (b :: c') 0 hne (by simpa using hcm)
    have h2 : (origNode u :: layerNodes u v 0 (b :: c') ++ [origNode v]).IsChain
        fun x y => (x, y) ∈ (gadgetGraph m G).edges := by
      simp only [layerNodes, List.cons_append] at h1 ⊢
      exact List.IsChain.cons_cons
        (mem_edges_gadgetGraph.2 ⟨(u, v), huv, mem_gadgetArcs.2 (.inl ⟨b, rfl, rfl⟩)⟩) h1
    have := h2.append_overlap (l₃ := l) (by simpa using ih) (by simp)
    simpa using this

/-! ### Decomposing paths of the gadget graph -/

/-- A path that enters layer `j` of the gadget of `(u, v)` and ends at an original vertex goes
through the remaining layers to `v`. -/
private theorem decompose_layers {u v : ℕ} :
    ∀ (k j : ℕ) (b : Bool) (L : List ℕ), j + k + 1 = m →
      (gadgetNode u v j b :: L).IsChain (fun x y => (x, y) ∈ (gadgetGraph m G).edges) →
      (∃ t, L.getLast? = some (origNode t)) →
      ∃ c L', c.length = k ∧ L = layerNodes u v (j + 1) c ++ origNode v :: L'
  | k, j, b, [], _, _, ⟨t, ht⟩ => by simp at ht
  | k, j, b, y :: L, hjk, hL, ⟨t, ht⟩ => by
    obtain ⟨hy, hL⟩ := List.isChain_cons_cons.1 hL
    rcases (of_gadgetNode hy).2 with ⟨hj, b', rfl⟩ | ⟨hj, rfl⟩
    · cases k with
      | zero => omega
      | succ k =>
        have hL' : ∃ t, L.getLast? = some (origNode t) := by
          cases L with
          | nil => simp at ht; exact absurd ht.symm (origNode_ne_gadgetNode _ _ _ _ _)
          | cons z L => exact ⟨t, by simpa using ht⟩
        obtain ⟨c, L', hc, rfl⟩ := decompose_layers k (j + 1) b' L (by omega) hL hL'
        exact ⟨b' :: c, L', by simp [hc], by simp [layerNodes]⟩
    · cases k with
      | zero => exact ⟨[], L, rfl, by simp [layerNodes]⟩
      | succ k => omega

private theorem decompose_aux (hm : 0 < m) :
    ∀ (N : ℕ) (L : List ℕ) (u t : ℕ), L.length ≤ N →
      (origNode u :: L).IsChain (fun x y => (x, y) ∈ (gadgetGraph m G).edges) →
      (origNode u :: L).getLast? = some (origNode t) →
      ∃ s : List (ℕ × List Bool), walk u s ++ [origNode (endpoint u s)] = origNode u :: L ∧
        endpoint u s = t ∧ (∀ p ∈ s, p.2.length = m) ∧
        (u :: s.map Prod.fst).IsChain fun x y => (x, y) ∈ G.edges
  | _, [], u, t, _, _, ht => by
    simp only [List.getLast?_singleton, Option.some.injEq] at ht
    obtain rfl := origNode_injective ht
    exact ⟨[], by simp [walk, endpoint], rfl, by simp, by simp⟩
  | 0, _ :: _, _, _, hN, _, _ => by simp at hN
  | N + 1, y :: L, u, t, hN, hL, ht => by
    obtain ⟨hy, hL⟩ := List.isChain_cons_cons.1 hL
    obtain ⟨v, b, huv, rfl⟩ := eq_gadgetNode_of_origNode hy
    have hL' : ∃ t, L.getLast? = some (origNode t) := by
      cases L with
      | nil => simp at ht; exact absurd ht.symm (origNode_ne_gadgetNode _ _ _ _ _)
      | cons z L => exact ⟨t, by simpa using ht⟩
    obtain ⟨c, L', hc, rfl⟩ := decompose_layers (m - 1) 0 b L (by omega) hL hL'
    have hL'' : (origNode v :: L').IsChain fun x y => (x, y) ∈ (gadgetGraph m G).edges := by
      rw [← List.cons_append] at hL
      exact hL.right_of_append
    have ht' : (origNode v :: L').getLast? = some (origNode t) := by
      simp only [← List.cons_append] at ht
      rwa [List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _)] at ht
    obtain ⟨s, hs, hst, hsm, hsc⟩ := decompose_aux hm N L' v t
      (by simp only [List.length_cons, List.length_append] at hN; omega) hL'' ht'
    refine ⟨(v, b :: c) :: s, ?_, hst, ?_, List.IsChain.cons_cons huv hsc⟩
    · rw [walk_append_endpoint, hs]
      simp [layerNodes]
    · simp only [List.mem_cons, forall_eq_or_imp, List.length_cons]
      exact ⟨by omega, hsm⟩

/-- A path of the gadget graph from an original vertex `u` to an original vertex `t` is a walk
through gadgets along a path of `G`. -/
private theorem decompose (hm : 0 < m) (L : List ℕ) (u t : ℕ)
    (hL : (origNode u :: L).IsChain (fun x y => (x, y) ∈ (gadgetGraph m G).edges))
    (ht : (origNode u :: L).getLast? = some (origNode t)) :
    ∃ s : List (ℕ × List Bool), walk u s ++ [origNode (endpoint u s)] = origNode u :: L ∧
      endpoint u s = t ∧ (∀ p ∈ s, p.2.length = m) ∧
      (u :: s.map Prod.fst).IsChain fun x y => (x, y) ∈ G.edges :=
  decompose_aux hm L.length L u t le_rfl hL ht

/-! ### Nodes of walks -/

/-- The original vertex of a node of the gadget graph. -/
private def origOf (x : ℕ) : Option ℕ := if x % 2 = 0 then some (x / 2) else none

@[simp] private theorem origOf_origNode (v : ℕ) : origOf (origNode v) = some v := by
  simp [origOf, origNode]

@[simp] private theorem origOf_gadgetNode (u v j : ℕ) (b : Bool) :
    origOf (gadgetNode u v j b) = none := by
  simp [origOf, gadgetNode]

private theorem eq_origNode_of_origOf {x v : ℕ} (h : origOf x = some v) : x = origNode v := by
  simp only [origOf] at h
  split at h <;> simp_all [origNode]; omega

@[simp] private theorem filterMap_layerNodes (u v j : ℕ) (c : List Bool) :
    (layerNodes u v j c).filterMap origOf = [] := by
  induction c generalizing j <;> simp [layerNodes, *]

private theorem filterMap_walk (u : ℕ) (s : List (ℕ × List Bool)) :
    (walk u s ++ [origNode (endpoint u s)]).filterMap origOf = u :: s.map Prod.fst := by
  induction s generalizing u with
  | nil => simp [walk, endpoint]
  | cons p s ih =>
    obtain ⟨v, c⟩ := p
    rw [walk_append_endpoint]
    simp [ih]

/-- The nodes of the walk from `u` through `s`: original vertices left by the walk, and gadget
nodes of the arcs it follows. -/
private theorem mem_walk {x : ℕ} :
    ∀ {u : ℕ} {s : List (ℕ × List Bool)}, x ∈ walk u s →
      ∃ a ∈ (u :: s.map Prod.fst).dropLast, x = origNode a ∨ ∃ v j b, x = gadgetNode a v j b
  | _, [], h => by simp [walk] at h
  | u, (v, c) :: s, h => by
    simp only [walk, List.mem_cons, List.mem_append] at h
    rcases h with rfl | h | h
    · exact ⟨u, by simp, .inl rfl⟩
    · obtain ⟨i, -, b, rfl⟩ := mem_layerNodes h
      exact ⟨u, by simp, .inr ⟨v, _, b, rfl⟩⟩
    · obtain ⟨a, ha, hx⟩ := mem_walk h
      refine ⟨a, ?_, hx⟩
      simp only [List.map_cons, List.dropLast_cons_cons]
      exact List.mem_cons_of_mem _ ha

/-- A walk whose original vertices are distinct has no repeated nodes. -/
private theorem nodup_walk :
    ∀ {u : ℕ} {s : List (ℕ × List Bool)}, (u :: s.map Prod.fst).dropLast.Nodup →
      (walk u s).Nodup
  | _, [], _ => by simp [walk]
  | u, (v, c) :: s, h => by
    simp only [List.map_cons, List.dropLast_cons_cons, List.nodup_cons] at h
    obtain ⟨hu, h⟩ := h
    have hdis : ∀ x ∈ walk v s, x ≠ origNode u ∧ ∀ v' j b, x ≠ gadgetNode u v' j b := by
      intro x hx
      obtain ⟨a, ha, hx⟩ := mem_walk hx
      have hau : a ≠ u := by rintro rfl; exact hu ha
      rcases hx with rfl | ⟨v'', j', b', rfl⟩
      · exact ⟨fun h => hau (origNode_injective h),
          fun _ _ _ => origNode_ne_gadgetNode _ _ _ _ _⟩
      · exact ⟨fun h => origNode_ne_gadgetNode _ _ _ _ _ h.symm,
          fun _ _ _ h => hau (gadgetNode_inj.1 h).1⟩
    simp only [walk, List.nodup_cons, List.mem_append, not_or, List.nodup_append]
    refine ⟨⟨fun h' => ?_, fun h' => (hdis _ h').1 rfl⟩, nodup_layerNodes _ _ _ _,
      nodup_walk h, fun x hx y hy => ?_⟩
    · obtain ⟨i, -, b, h'⟩ := mem_layerNodes h'
      exact origNode_ne_gadgetNode _ _ _ _ _ h'
    · obtain ⟨i, -, b, rfl⟩ := mem_layerNodes hx
      rintro rfl
      exact (hdis _ hy).2 _ _ _ rfl

/-- The nodes of a walk along arcs of `G` through gadgets of `m` layers are declared. -/
private theorem mem_vertices_of_mem_walk :
    ∀ {u : ℕ} {s : List (ℕ × List Bool)}, (∀ p ∈ s, p.2.length = m) →
      (u :: s.map Prod.fst).IsChain (fun x y => (x, y) ∈ G.edges) →
      (∀ a ∈ u :: s.map Prod.fst, a ∈ G.vertices) →
      ∀ x ∈ walk u s, x ∈ (gadgetGraph m G).vertices
  | _, [], _, _, _, x, hx => by simp [walk] at hx
  | u, (v, c) :: s, hs, hc, hv, x, hx => by
    obtain ⟨huv, hc⟩ := List.isChain_cons_cons.1 hc
    simp only [walk, List.mem_cons, List.mem_append] at hx
    rcases hx with rfl | hx | hx
    · exact origNode_mem_vertices_gadgetGraph.2 (hv u List.mem_cons_self)
    · obtain ⟨i, hi, b, rfl⟩ := mem_layerNodes hx
      exact gadgetNode_mem_vertices_gadgetGraph huv
        (by rw [hs _ List.mem_cons_self] at hi; omega)
    · exact mem_vertices_of_mem_walk (fun p hp => hs p (List.mem_cons_of_mem _ hp)) hc
        (fun a ha => hv a (List.mem_cons_of_mem _ ha)) x hx

/-- Walks along the same vertices with `m` bits in each step are equal only if their bits are. -/
private theorem walk_injective :
    ∀ {u : ℕ} {s s' : List (ℕ × List Bool)}, s.map Prod.fst = s'.map Prod.fst →
      (∀ p ∈ s, p.2.length = m) → (∀ p ∈ s', p.2.length = m) → walk u s = walk u s' → s = s'
  | _, [], [], _, _, _, _ => rfl
  | _, [], _ :: _, h, _, _, _ => by simp at h
  | _, _ :: _, [], h, _, _, _ => by simp at h
  | u, (v, c) :: s, (v', c') :: s', h, hs, hs', hw => by
    simp only [List.map_cons, List.cons.injEq] at h
    obtain ⟨rfl, h⟩ := h
    simp only [walk, List.cons.injEq, true_and] at hw
    obtain ⟨h1, h2⟩ := List.append_inj hw (by
      simp [hs _ List.mem_cons_self, hs' _ List.mem_cons_self])
    rw [layerNodes_injective h1, walk_injective h (fun p hp => hs p (List.mem_cons_of_mem _ hp))
      (fun p hp => hs' p (List.mem_cons_of_mem _ hp)) h2]

/-! ### Cycles of the gadget graph -/

/-- The steps along the vertices `q` with bits `γ i j` for layer `j` of step `i`. -/
private def steps (m : ℕ) (q : List ℕ) (γ : ℕ → ℕ → Bool) : List (ℕ × List Bool) :=
  q.zipIdx.map fun p => (p.1, (List.range m).map (γ p.2))

@[simp] private theorem map_fst_steps (q : List ℕ) (γ : ℕ → ℕ → Bool) :
    (steps m q γ).map Prod.fst = q := by
  simp [steps, Function.comp_def]

private theorem length_snd_of_mem_steps {q : List ℕ} {γ : ℕ → ℕ → Bool} {p : ℕ × List Bool}
    (hp : p ∈ steps m q γ) : p.2.length = m := by
  obtain ⟨_, -, rfl⟩ := List.mem_map.1 hp
  simp

private theorem steps_congr {q : List ℕ} {γ γ' : ℕ → ℕ → Bool}
    (h : ∀ i < q.length, ∀ j < m, γ i j = γ' i j) : steps m q γ = steps m q γ' := by
  refine List.map_congr_left fun p hp => ?_
  have := (List.mem_zipIdx hp).2.1
  simp only [Prod.mk.injEq, true_and]
  exact List.map_congr_left fun j hj => h _ (by simpa using this) _ (List.mem_range.1 hj)

private theorem getElem_steps {q : List ℕ} {γ : ℕ → ℕ → Bool} {i : ℕ}
    (hi : i < (steps m q γ).length) :
    (steps m q γ)[i] = (q[i]'(by simpa [steps] using hi), (List.range m).map (γ i)) := by
  simp [steps]

/-- Steps with `m` bits each are the steps along their vertices with their bits. -/
private theorem steps_eq {s : List (ℕ × List Bool)} (hs : ∀ p ∈ s, p.2.length = m) :
    steps m (s.map Prod.fst) (fun i j => ((s.getD i (0, [])).2).getD j false) = s := by
  refine List.ext_getElem (by simp [steps]) fun i h₁ h₂ => ?_
  rw [getElem_steps]
  have hm := hs _ (List.getElem_mem h₂)
  refine Prod.ext (by simp) (List.ext_getElem (by simp [hm]) fun j hj₁ hj₂ => ?_)
  simp [List.getD_eq_getElem?_getD, h₂, hj₂]

/-- The walk around the gadget graph along the cycle `r` of `G`, starting at the head of `r`,
choosing bit `γ i j` in layer `j` of the gadget of the `i`-th arc. -/
private def cycleWalk (m : ℕ) (r : List ℕ) (γ : ℕ → ℕ → Bool) : List ℕ :=
  walk (r.headD 0) (steps m (r.rotate 1) γ)

private theorem cycleWalk_congr {r : List ℕ} {γ γ' : ℕ → ℕ → Bool}
    (h : ∀ i < r.length, ∀ j < m, γ i j = γ' i j) : cycleWalk m r γ = cycleWalk m r γ' := by
  rw [cycleWalk, cycleWalk, steps_congr (by simpa using h)]

private theorem endpoint_steps_rotate {r : List ℕ} (hr : r ≠ []) (γ : ℕ → ℕ → Bool) :
    endpoint (r.headD 0) (steps m (r.rotate 1) γ) = r.headD 0 := by
  have key : ∀ (u : ℕ) (s : List (ℕ × List Bool)), endpoint u s = (u :: s.map Prod.fst).getLast
      (by simp) := by
    intro u s
    induction s generalizing u with
    | nil => rfl
    | cons p s ih => simp [endpoint, ih]
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  rw [key, map_fst_steps]
  simp

/-- `u :: r.rotate 1 = r ++ [u]` for the head `u` of `r`. -/
private theorem headD_cons_rotate_one {r : List ℕ} (hr : r ≠ []) :
    r.headD 0 :: r.rotate 1 = r ++ [r.headD 0] := by
  obtain ⟨a, r, rfl⟩ := List.exists_cons_of_ne_nil hr
  simp

/-- A cycle of `G` gives a cycle of the gadget graph for every choice of bits. -/
private theorem isSimpleCycle_cycleWalk (hm : 0 < m) {r : List ℕ}
    (hr : G.IsSimpleCycle (r : Cycle ℕ)) (γ : ℕ → ℕ → Bool) :
    (gadgetGraph m G).IsSimpleCycle (cycleWalk m r γ : Cycle ℕ) := by
  obtain ⟨hne, hnd, hv, hc⟩ := Graph.isSimpleCycle_coe.1 hr
  have hchain : (r.headD 0 :: (steps m (r.rotate 1) γ).map Prod.fst).IsChain
      fun x y => (x, y) ∈ G.edges := by
    rw [map_fst_steps, headD_cons_rotate_one hne]
    obtain ⟨a, r', rfl⟩ := List.exists_cons_of_ne_nil hne
    simpa using Cycle.chain_coe_iff_isChain_append_take_one.1 hc
  have hpath := isChain_walk hm _ _ (fun p hp => length_snd_of_mem_steps hp) hchain
  rw [endpoint_steps_rotate hne] at hpath
  have hsne : steps m (r.rotate 1) γ ≠ [] := by
    simpa [steps] using hne
  obtain ⟨⟨v, c⟩, s, hs⟩ := List.exists_cons_of_ne_nil hsne
  refine Graph.isSimpleCycle_coe.2 ⟨?_, ?_, ?_, ?_⟩
  · rw [cycleWalk, hs]; simp [walk]
  · refine nodup_walk ?_
    rw [map_fst_steps, headD_cons_rotate_one hne, List.dropLast_concat]
    exact hnd
  · refine mem_vertices_of_mem_walk (fun p hp => length_snd_of_mem_steps hp) hchain ?_
    rw [map_fst_steps, headD_cons_rotate_one hne]
    intro a ha
    rcases List.mem_append.1 ha with ha | ha
    · exact hv a ha
    · obtain ⟨x, r', rfl⟩ := List.exists_cons_of_ne_nil hne
      simp only [List.mem_singleton] at ha
      exact hv a (by simp [ha])
  · refine Cycle.chain_coe_iff_isChain_append_take_one.2 ?_
    have : (cycleWalk m r γ).take 1 = [origNode (r.headD 0)] := by
      rw [cycleWalk, hs]; simp [walk]
    rw [this]
    exact hpath

/-- A cycle of the gadget graph contains an original vertex: the layer index grows along arcs
between gadget nodes. -/
private theorem exists_origNode_mem {p : List ℕ} (hp : p ≠ [])
    (hc : (p : Cycle ℕ).Chain fun x y => (x, y) ∈ (gadgetGraph m G).edges) :
    ∃ v, origNode v ∈ p := by
  by_contra hno
  push Not at hno
  let f : ℕ → ℕ := fun x => (Nat.unpair (x / 2)).2 / 2
  have hf : ∀ u v j b, f (gadgetNode u v j b) = j := by
    intro u v j b
    simp only [f, gadgetNode]
    rw [show (2 * Nat.pair (Nat.pair u v) (2 * j + b.toNat) + 1) / 2 =
      Nat.pair (Nat.pair u v) (2 * j + b.toNat) by omega, Nat.unpair_pair]
    cases b <;> simp only [Bool.toNat_false, Bool.toNat_true] <;> omega
  have hgad : ∀ x ∈ p, ∀ y, (x, y) ∈ (gadgetGraph m G).edges → y ∈ p →
      f y = f x + 1 := by
    intro x hx y hxy hy
    obtain ⟨⟨u', v'⟩, -, h⟩ := mem_edges_gadgetGraph.1 hxy
    rcases mem_gadgetArcs.1 h with ⟨b, rfl, -⟩ | ⟨j, b, b', -, rfl, rfl⟩ | ⟨b, -, rfl⟩
    · exact absurd hx (hno _)
    · rw [hf, hf]
    · exact absurd hy (hno _)
  obtain ⟨a, l, rfl⟩ := List.exists_cons_of_ne_nil hp
  have hchain := Cycle.chain_coe_iff_isChain_append_take_one.1 hc
  simp only [List.take_succ_cons, List.take_zero, List.cons_append] at hchain
  -- along the closed path the layer index grows by one at each arc
  have key : ∀ (l' : List ℕ) (x : ℕ), (∀ z ∈ x :: l', z ∈ a :: l) →
      (x :: l').IsChain (fun x y => (x, y) ∈ (gadgetGraph m G).edges) →
      f ((x :: l').getLast (by simp)) = f x + l'.length := by
    intro l'
    induction l' with
    | nil => intro x _ _; simp
    | cons y l' ih =>
      intro x hsub hch
      obtain ⟨hxy, hch⟩ := List.isChain_cons_cons.1 hch
      have := ih y (fun z hz => hsub z (List.mem_cons_of_mem _ hz)) hch
      rw [List.getLast_cons (by simp), this,
        hgad x (hsub x List.mem_cons_self) y hxy (hsub y (by simp))]
      simp; omega
  have := key (l ++ [a]) a (by intro z hz; simp at hz ⊢; tauto) hchain
  simp at this

/-- Every cycle of the gadget graph is the walk around a cycle of `G` for some choice of bits. -/
private theorem exists_eq_cycleWalk (hm : 0 < m) {c : Cycle ℕ}
    (hc : (gadgetGraph m G).IsSimpleCycle c) :
    ∃ (r : List ℕ) (γ : ℕ → ℕ → Bool), G.IsSimpleCycle (r : Cycle ℕ) ∧
      c = (cycleWalk m r γ : Cycle ℕ) := by
  induction c using Quotient.inductionOn' with
  | h p =>
  change (gadgetGraph m G).IsSimpleCycle (p : Cycle ℕ) at hc
  change ∃ (r : List ℕ) (γ : ℕ → ℕ → Bool), G.IsSimpleCycle (r : Cycle ℕ) ∧
    (p : Cycle ℕ) = (cycleWalk m r γ : Cycle ℕ)
  obtain ⟨hne, hnd, hv, hch⟩ := Graph.isSimpleCycle_coe.1 hc
  obtain ⟨u, hu⟩ := exists_origNode_mem hne hch
  -- rotate `p` to start at `origNode u`
  obtain ⟨k, hk, hku⟩ := List.getElem_of_mem hu
  set p' := p.rotate k with hp'
  have hpp' : (p : Cycle ℕ) = (p' : Cycle ℕ) := Cycle.coe_eq_coe.2 ⟨k, rfl⟩
  rw [hpp'] at hc ⊢
  obtain ⟨hne', hnd', hv', hch'⟩ := Graph.isSimpleCycle_coe.1 hc
  obtain ⟨L, hL⟩ : ∃ L, p' = origNode u :: L := by
    obtain ⟨a, L, hL⟩ := List.exists_cons_of_ne_nil hne'
    refine ⟨L, ?_⟩
    rw [hL]
    have : p'.head? = some (origNode u) := by
      rw [hp', List.head?_rotate hk, List.getElem?_eq_getElem hk, hku]
    rw [hL, List.head?_cons, Option.some.injEq] at this
    rw [this]
  have hchain := Cycle.chain_coe_iff_isChain_append_take_one.1 hch'
  rw [hL] at hchain
  simp only [List.take_succ_cons, List.take_zero, List.cons_append] at hchain
  obtain ⟨s, hs, hst, hsm, hsc⟩ := decompose hm (L ++ [origNode u]) u u hchain (by
    rw [← List.cons_append, List.getLast?_append_of_ne_nil _ (List.cons_ne_nil _ _),
      List.getLast?_singleton])
  have hws : walk u s = p' := by
    rw [hL]
    have := hs
    rw [hst, ← List.cons_append] at this
    exact List.append_cancel_right this
  set r := p'.filterMap origOf with hr
  have hru : r ++ [u] = u :: s.map Prod.fst := by
    rw [← filterMap_walk, hst, hws, List.filterMap_append, hr]
    simp
  have hrne : r ≠ [] := by
    rintro hr0
    rw [hr0, List.nil_append, List.cons.injEq] at hru
    have hs0 : s = [] := List.map_eq_nil_iff.1 hru.2.symm
    rw [hs0] at hws
    exact hne' (by simpa [walk] using hws.symm)
  have hrhead : r.headD 0 = u := by
    obtain ⟨a, r', hr'⟩ := List.exists_cons_of_ne_nil hrne
    rw [hr'] at hru ⊢
    rw [List.cons_append, List.cons.injEq] at hru
    exact hru.1
  have hrot : s.map Prod.fst = r.rotate 1 := by
    have := headD_cons_rotate_one hrne
    rw [hrhead, hru] at this
    exact (List.cons_injective this).symm
  have hrnd : r.Nodup := by
    rw [hr]
    refine hnd'.filterMap fun a a' b hb hb' => ?_
    rw [eq_origNode_of_origOf hb, eq_origNode_of_origOf hb']
  refine ⟨r, fun i j => ((s.getD i (0, [])).2).getD j false, ?_, ?_⟩
  · refine Graph.isSimpleCycle_coe.2 ⟨hrne, hrnd, fun v hv'' => ?_, ?_⟩
    · obtain ⟨x, hx, hxv⟩ := List.mem_filterMap.1 (hr ▸ hv'')
      rw [eq_origNode_of_origOf hxv] at hx
      exact origNode_mem_vertices_gadgetGraph.1 (hv' _ hx)
    · refine Cycle.chain_coe_iff_isChain_append_take_one.2 ?_
      obtain ⟨a, r', hr'⟩ := List.exists_cons_of_ne_nil hrne
      have ha : a = u := by rw [← hrhead, hr']; rfl
      rw [hr', ha] at hru ⊢
      simp only [List.take_succ_cons, List.take_zero]
      rw [hru]
      exact hsc
  · rw [cycleWalk, hrhead, ← hrot, steps_eq hsm, hws]

/-! ### Counting -/

/-- `γ` extended by `false` outside `Fin k × Fin m`. -/
private def extend (k m : ℕ) (β : Fin k → Fin m → Bool) (i j : ℕ) : Bool :=
  if h : i < k ∧ j < m then β ⟨i, h.1⟩ ⟨j, h.2⟩ else false

/-- A Hamiltonian cycle of `G` gives `2 ^ (m * n)` cycles of the gadget graph. -/
theorem two_pow_le_of_mem_DirHamCycle (hm : 0 < m) (h : G ∈ DirHamCycle) :
    2 ^ (m * G.distinctVertices.length) ≤ SharpCycle (gadgetGraph m G) := by
  obtain ⟨r, hnd, hall, hne, hc⟩ := h
  have hlen : r.length = G.distinctVertices.length := by
    rw [Graph.length_distinctVertices, ← List.toFinset_card_of_nodup hnd]
    congr 1
    ext v
    simp [hall]
  have hr : G.IsSimpleCycle (r : Cycle ℕ) :=
    Graph.isSimpleCycle_coe.2 ⟨hne, hnd, fun v hv => (hall v).1 hv, hc⟩
  set n := G.distinctVertices.length
  let F : (Fin n → Fin m → Bool) → Cycle ℕ := fun β => (cycleWalk m r (extend n m β) : Cycle ℕ)
  have hF : Function.Injective F := by
    intro β β' hββ'
    have hrot := Cycle.coe_eq_coe.1 hββ'
    have hnd₁ := Graph.isSimpleCycle_coe.1 (isSimpleCycle_cycleWalk hm hr (extend n m β))
    have hnd₂ := Graph.isSimpleCycle_coe.1 (isSimpleCycle_cycleWalk hm hr (extend n m β'))
    -- two rotations of a list without repetitions with the same head are equal
    have heq : cycleWalk m r (extend n m β) = cycleWalk m r (extend n m β') := by
      obtain ⟨k, hk⟩ := hrot
      have hsne : steps m (r.rotate 1) (extend n m β) ≠ [] := by simpa [steps] using hne
      obtain ⟨⟨v, c⟩, s, hs⟩ := List.exists_cons_of_ne_nil hsne
      have hsne' : steps m (r.rotate 1) (extend n m β') ≠ [] := by simpa [steps] using hne
      obtain ⟨⟨v', c'⟩, s', hs'⟩ := List.exists_cons_of_ne_nil hsne'
      set l := cycleWalk m r (extend n m β)
      have hl0 : l.head? = some (origNode (r.headD 0)) := by
        simp only [l, cycleWalk, hs, walk, List.head?_cons]
      have hl0' : (cycleWalk m r (extend n m β')).head? = some (origNode (r.headD 0)) := by
        simp only [cycleWalk, hs', walk, List.head?_cons]
      have hlne : l ≠ [] := hnd₁.1
      have hkl : l.rotate (k % l.length) = cycleWalk m r (extend n m β') := by
        rw [List.rotate_mod, hk]
      have hlpos : 0 < l.length := List.length_pos_of_ne_nil hlne
      have hkm : k % l.length < l.length := Nat.mod_lt _ hlpos
      rw [← hkl, List.head?_rotate hkm, List.getElem?_eq_getElem hkm] at hl0'
      rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlpos] at hl0
      have h0 : k % l.length = 0 := by
        have := (hnd₁.2.1.getElem_inj_iff (i := k % l.length) (j := 0)).1 (by
          simp only [Option.some.injEq] at hl0 hl0'; rw [hl0, hl0'])
        exact this
      rw [← hkl, h0, List.rotate_zero]
    have hs := walk_injective (m := m) (u := r.headD 0) (by simp)
      (fun p hp => length_snd_of_mem_steps hp) (fun p hp => length_snd_of_mem_steps hp) heq
    funext i j
    have hi : i.1 < (steps m (r.rotate 1) (extend n m β)).length := by
      simp [steps, hlen]
    have hi' : i.1 < (steps m (r.rotate 1) (extend n m β')).length := by
      simp [steps, hlen]
    have := congrArg (fun s => (s[i.1]?).map fun p => p.2[j.1]?) hs
    simp only [List.getElem?_eq_getElem hi, List.getElem?_eq_getElem hi', getElem_steps,
      Option.map_some, List.getElem?_map, List.getElem?_range j.2, Option.some.injEq] at this
    simpa [extend] using this
  have hfin := finite_setOf_isSimpleCycle (gadgetGraph m G)
  calc 2 ^ (m * n) = Nat.card (Fin n → Fin m → Bool) := by
        simp [pow_mul]
    _ = (Set.range F).ncard := by
        rw [← Set.image_univ, Set.ncard_image_of_injective _ hF, Set.ncard_univ]
    _ ≤ SharpCycle (gadgetGraph m G) := by
        refine Set.ncard_le_ncard ?_ hfin
        rintro _ ⟨β, rfl⟩
        exact isSimpleCycle_cycleWalk hm hr _

/-- A graph with `n` distinct vertices has at most `2 ^ n * n !` lists of distinct vertices. -/
private theorem length_nodupLists_lt (G : Graph) :
    (nodupLists G.distinctVertices).length < 2 ^ layers G := by
  set n := G.distinctVertices.length
  calc (nodupLists G.distinctVertices).length ≤ 2 ^ n * n.factorial := length_nodupLists_le _
    _ ≤ 2 ^ n * 2 ^ (n * n) := by
        gcongr
        calc n.factorial ≤ n ^ n := Nat.factorial_le_pow n
          _ ≤ (2 ^ n) ^ n := Nat.pow_le_pow_left (Nat.lt_two_pow_self).le n
          _ = 2 ^ (n * n) := (pow_mul 2 n n).symm
    _ < 2 ^ (n * n + n + 1) := by
        rw [← pow_add]
        exact Nat.pow_lt_pow_right (by norm_num) (by omega)
    _ = 2 ^ layers G := rfl

/-- Without a Hamiltonian cycle, the gadget graph has fewer than `2 ^ (m * n)` cycles. -/
theorem lt_two_pow_of_notMem_DirHamCycle (h : G ∉ DirHamCycle) :
    SharpCycle (reduce G) < 2 ^ (layers G * G.distinctVertices.length) := by
  set n := G.distinctVertices.length
  set m := layers G
  have hm : 0 < m := by simp [m, layers]
  -- the cycles of `G`, as lists, are shorter than `n`
  have hshort : ∀ r : List ℕ, G.IsSimpleCycle (r : Cycle ℕ) → r.length < n := by
    intro r hr
    obtain ⟨hne, hnd, hv, hc⟩ := Graph.isSimpleCycle_coe.1 hr
    have hsub : r.toFinset ⊆ G.vertices.toFinset := fun v hv' => by
      simpa using hv v (by simpa using hv')
    have hn : n = G.vertices.toFinset.card := Graph.length_distinctVertices G
    have hle : r.length ≤ n := by
      rw [← List.toFinset_card_of_nodup hnd, hn]
      exact Finset.card_le_card hsub
    refine lt_of_le_of_ne hle fun heq => h ⟨r, hnd, fun v => ⟨hv v, fun hv' => ?_⟩, hne, hc⟩
    have hEq := Finset.eq_of_subset_of_card_le hsub (by
      rw [List.toFinset_card_of_nodup hnd, heq, hn])
    have : v ∈ r.toFinset := hEq ▸ List.mem_toFinset.2 hv'
    exact List.mem_toFinset.1 this
  let T : Finset (List ℕ × (Fin (n - 1) → Fin m → Bool)) :=
    ((nodupLists G.distinctVertices).toFinset.filter fun r => r.length < n) ×ˢ Finset.univ
  let F : List ℕ × (Fin (n - 1) → Fin m → Bool) → Cycle ℕ :=
    fun x => (cycleWalk m x.1 (extend (n - 1) m x.2) : Cycle ℕ)
  have hsub : {c : Cycle ℕ | (reduce G).IsSimpleCycle c} ⊆ ↑(T.image F) := by
    intro c hc
    obtain ⟨r, γ, hr, rfl⟩ := exists_eq_cycleWalk hm hc
    have hrn := hshort r hr
    obtain ⟨-, hnd, hv, -⟩ := Graph.isSimpleCycle_coe.1 hr
    refine Finset.mem_coe.2 (Finset.mem_image.2 ⟨(r, fun i j => γ i j), ?_, ?_⟩)
    · simp only [T, Finset.mem_product, Finset.mem_filter, List.mem_toFinset, Finset.mem_univ,
        and_true]
      exact ⟨mem_nodupLists hnd fun v h => Graph.mem_distinctVertices.2 (hv v h), hrn⟩
    · simp only [F]
      congr 1
      refine cycleWalk_congr fun i hi j hj => ?_
      simp [extend, show i < n - 1 by omega, hj]
  calc SharpCycle (reduce G) ≤ (T.image F).card := by
        rw [SharpCycle, ← Set.ncard_coe_finset]
        exact Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ ≤ T.card := Finset.card_image_le
    _ < 2 ^ (m * n) := by
        rcases Nat.eq_zero_or_pos n with hn | hn
        · have : T = ∅ := by
            simp [T, hn]
          simp [this]
        · simp only [T, Finset.card_product, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
            Fintype.card_bool]
          calc _ ≤ (nodupLists G.distinctVertices).length * (2 ^ m) ^ (n - 1) := by
                gcongr
                exact (Finset.card_filter_le _ _).trans (List.toFinset_card_le _)
            _ < 2 ^ m * (2 ^ m) ^ (n - 1) := by
                gcongr
                exact length_nodupLists_lt G
            _ = 2 ^ (m * n) := by
                rw [← pow_succ', ← pow_mul, Nat.sub_add_cancel hn]

/-- **Theorem 9.4, the reduction** [Arora and Barak, Theorem 9.4][AroraBarak07]: with `n`
distinct vertices and `m = n * n + n + 1` layers, `G` has a Hamiltonian cycle exactly when the
gadget graph has at least `2 ^ (m * n)` simple cycles. -/
theorem mem_DirHamCycle_iff (G : Graph) :
    G ∈ DirHamCycle ↔ 2 ^ (layers G * G.distinctVertices.length) ≤ SharpCycle (reduce G) :=
  ⟨two_pow_le_of_mem_DirHamCycle (by simp [layers]),
    fun h => by_contra fun hG => (lt_two_pow_of_notMem_DirHamCycle hG).not_ge h⟩

/-! ### Polynomial time -/

section PolyTime

open Turing.MultiTapeTM ComputableInPolyTime

/-- The node of an original vertex is computable in polynomial time. -/
@[fun_prop]
theorem computableInPolyTime_origNode {α : Type} {enc : α ↪ List Bool} {v : α → ℕ}
    (hv : ComputableInPolyTime v enc encNat) :
    ComputableInPolyTime (fun a => origNode (v a)) enc encNat := by
  unfold origNode
  fun_prop

/-- The gadget nodes are computable in polynomial time, from binary arc ends and a unary layer. -/
@[fun_prop]
theorem computableInPolyTime_gadgetNode {α : Type} {enc : α ↪ List Bool} {u v j : α → ℕ}
    {b : α → Bool} (hu : ComputableInPolyTime u enc encNat)
    (hv : ComputableInPolyTime v enc encNat) (hj : ComputableInPolyTime j enc encUnary)
    (hb : ComputableInPolyTime b enc encBool) :
    ComputableInPolyTime (fun a => gadgetNode (u a) (v a) (j a) (b a)) enc encNat := by
  unfold gadgetNode
  fun_prop

/-- The number of layers is computable in polynomial time in unary. -/
@[fun_prop]
theorem computableInPolyTime_layers : ComputableInPolyTime layers encGraph encUnary := by
  have := (length_list encNat).comp Graph.computableInPolyTime_distinctVertices
  unfold layers
  fun_prop

/-- **The reduction is polynomial-time.** -/
@[fun_prop]
theorem computableInPolyTime_reduce : ComputableInPolyTime reduce encGraph encGraph := by
  have hm := computableInPolyTime_layers
  have hv : ComputableInPolyTime (fun G => G.vertices.map origNode ++
      G.edges.flatMap (gadgetVertices (layers G))) encGraph (encList encNat) := by
    unfold gadgetVertices
    fun_prop
  have he : ComputableInPolyTime (fun G => G.edges.flatMap (gadgetArcs (layers G))) encGraph
      (encList (encPair encNat encNat)) := by
    unfold gadgetArcs
    fun_prop
  exact encGraph_mk_polyTime hv he

/-- **Theorem 9.4, decision** [Arora and Barak, Theorem 9.4][AroraBarak07]: if the number of
simple cycles is computable in polynomial time with binary output, then `DirHamCycle ∈ P`. -/
theorem DirHamCycle_mem_P (h : ComputableInPolyTime SharpCycle encGraph encNat) :
    DirHamCycle ∈ P encGraph := by
  refine ⟨fun G => !decide (SharpCycle (reduce G) < 2 ^ (layers G * G.distinctVertices.length)),
    ?_, fun G => by simp [mem_DirHamCycle_iff]⟩
  have hc := h.comp computableInPolyTime_reduce
  have hn := (length_list encNat).comp Graph.computableInPolyTime_distinctVertices
  have hm := computableInPolyTime_layers
  fun_prop

end PolyTime

end SharpCycle

/-- **Arora–Barak, Theorem 9.4** [Arora and Barak, Theorem 9.4][AroraBarak07]: if `#CYCLE`, the
number of simple directed cycles, is computable in polynomial time with binary output, then
`P = NP`, for every encoding. -/
theorem P_eq_NP_of_computableInPolyTime_SharpCycle
    (h : Turing.MultiTapeTM.ComputableInPolyTime SharpCycle encGraph Turing.MultiTapeTM.encNat)
    {α : Type} (enc : α ↪ List Bool) : P enc = NP enc :=
  DirHamCycle_npComplete.P_eq_NP_of_mem_P (SharpCycle.DirHamCycle_mem_P h) enc

end Cslib.Complexity
