/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork
public import Complexity.Foundations.Data.BitString.Counter
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.List.GetD
import Mathlib.Data.Set.Card

/-!
# Explicit Boolean tensor networks

A Boolean tensor network as an algorithm reads it (`DescribedNetwork T`) is the number of edges,
numbered `0, 1, …`, and a list of vertices, each given by its ordered list of *ports*, the numbers
of the edges at the vertex, and a *descriptor* `t : T` of its tensor. For an evaluator
`eval : T → List Bool → R`, the entry of the vertex when port `i` carries the bit `bs[i]` is
`eval t bs`, and the contraction (`DescribedNetwork.contraction`) sums, over all assignments of
bits to the edges, the product of the entries at the bits on the ports.

An *explicit* network (`ExplicitTensorNetwork R`) has tables as descriptors: the value of the
tensor of a vertex when port `i` carries the bit `bs[i]` is the entry of its table at position
`BitString.lsbValue bs`, the number whose binary digit `i` is `bs[i]`
(`BitString.testBit_lsbValue`).

So a vertex with `k` ports has a table of `2 ^ k` entries. The contraction of an explicit network
(`ExplicitTensorNetwork.contraction`) sums, over all assignments of bits to the edges, the product
of the table entries at the bits on the ports, which is the contraction of the described network
with table lookup as the evaluator (`DescribedNetwork.contraction_entry`). It needs no
well-formedness: a port naming no edge reads `false`, and a position past the end of a table has
entry zero.

Its size measures are the number of edges, the number of vertices, the maximum number of ports of
a vertex (`ExplicitTensorNetwork.maxDegree`) and the total length of the tables
(`ExplicitTensorNetwork.tableLength`). A described network is *rows-first bipartite* with `r`
rows (`DescribedNetwork.IsRowsFirstBipartite`) when every port names an edge and every edge is a
port of exactly one of its first `r` vertices and of exactly one of the others.

**Writing a network out** (`TensorNetwork.toExplicit`). Given numberings of the vertices and the
edges of a Boolean tensor network on finite types, list the edges at each vertex in increasing
order and tabulate its tensor on them. The contraction is unchanged
(`TensorNetwork.contraction_toExplicit`). The ports of a vertex are its incident edges, so the
degree bound carries over (`TensorNetwork.maxDegree_toExplicit_le`), and a numbering that puts
one end of every edge below `r` and the other at or above it gives a rows-first bipartite network
(`TensorNetwork.isRowsFirstBipartite_toExplicit`).

## Main definitions

* `Cslib.Circuits.Frontier.DescribedNetwork`: a Boolean tensor network given by the ports and
  the descriptors of its vertices.
* `Cslib.Circuits.Frontier.DescribedNetwork.contraction`: its contraction, for an evaluator of
  the descriptors.
* `Cslib.Circuits.Frontier.DescribedNetwork.IsRowsFirstBipartite`: the bipartition with the first
  `r` vertices as rows.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork`: an explicit Boolean tensor network, with
  tables as descriptors.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.entry`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.portBits`: table lookup and the bits on a list
  of ports.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.contraction`: the contraction.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.maxDegree`,
  `Cslib.Circuits.Frontier.ExplicitTensorNetwork.tableLength`: size measures.
* `Cslib.Circuits.Frontier.TensorNetwork.explicitPorts`,
  `Cslib.Circuits.Frontier.TensorNetwork.explicitTable`,
  `Cslib.Circuits.Frontier.TensorNetwork.toExplicit`: writing a Boolean tensor network out.

## Main results

* `Cslib.Circuits.Frontier.DescribedNetwork.map_contraction`: the contraction commutes with maps
  of semirings.
* `Cslib.Circuits.Frontier.DescribedNetwork.contraction_entry`: explicit networks are described
  networks with table lookup as the evaluator.
* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.maxDegree_le_iff`: the degree bound.
* `Cslib.Circuits.Frontier.TensorNetwork.entry_explicitTable`: a written-out table evaluates the
  tensor.
* `Cslib.Circuits.Frontier.TensorNetwork.contraction_toExplicit`: writing a network out preserves
  its contraction.
* `Cslib.Circuits.Frontier.TensorNetwork.length_explicitPorts`: a vertex has one port per incident
  edge.
* `Cslib.Circuits.Frontier.TensorNetwork.maxDegree_toExplicit_le`,
  `Cslib.Circuits.Frontier.TensorNetwork.isRowsFirstBipartite_toExplicit`,
  `Cslib.Circuits.Frontier.TensorNetwork.length_table_toExplicit`: degree, bipartition and table
  lengths of a written-out network.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.1 (p. 53).
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

/-- A Boolean tensor network with *described* tensors: the number of edges, numbered from zero,
and a list of vertices. A vertex is given by its ordered list of *ports*, the numbers of its
edges, and a descriptor `t : T` of its tensor. -/
structure DescribedNetwork (T : Type*) where
  /-- The number of edges; the edges are numbered `0, …, numEdges - 1`. -/
  numEdges : ℕ
  /-- The vertices, each given by its ports and the descriptor of its tensor. -/
  vertices : List (List ℕ × T)

namespace DescribedNetwork

variable {T : Type*}

/-- A described network is its number of edges and its list of vertices. -/
def equivProd : DescribedNetwork T ≃ ℕ × List (List ℕ × T) where
  toFun d := (d.numEdges, d.vertices)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The bits that a word, read as an assignment of bits to the edges, puts on a list of ports;
a port past the end of the word reads `false`. -/
def wordBits (word : List Bool) (ports : List ℕ) : List Bool :=
  ports.map fun i => word.getD i false

/-- The *contraction*: the sum over all assignments of bits to the edges of the product of the
entries of the vertices at the bits on their ports, for entries in a commutative semiring. -/
def contraction {R : Type*} [CommSemiring R] (eval : T → List Bool → R)
    (d : DescribedNetwork T) : R :=
  ∑ x : Fin d.numEdges → Bool,
    (d.vertices.map fun v => eval v.2 (wordBits (List.ofFn x) v.1)).prod

/-- The contraction commutes with maps of semirings. -/
theorem map_contraction {R S : Type*} [CommSemiring R] [CommSemiring S] (ψ : R →+* S)
    (eval : T → List Bool → R) (d : DescribedNetwork T) :
    ψ (d.contraction eval) = d.contraction fun t bs => ψ (eval t bs) := by
  rw [contraction, contraction, map_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_list_prod, List.map_map]
  rfl

/-- **Rows-first bipartite**: the first `r` vertices are the *rows* and the others the *columns*,
every port names an edge, and every edge is a port of the rows exactly once and of the columns
exactly once. So every edge joins a row to a column. -/
def IsRowsFirstBipartite (d : DescribedNetwork T) (r : ℕ) : Prop :=
  (∀ v ∈ d.vertices, ∀ i ∈ v.1, i < d.numEdges) ∧
    ∀ i < d.numEdges, ((d.vertices.take r).map fun v => v.1.count i).sum = 1 ∧
      ((d.vertices.drop r).map fun v => v.1.count i).sum = 1

instance (d : DescribedNetwork T) (r : ℕ) : Decidable (d.IsRowsFirstBipartite r) := by
  unfold IsRowsFirstBipartite
  infer_instance

end DescribedNetwork

/-- An *explicit Boolean tensor network* over `R`: a network whose descriptors are *tables*. The
entry of the table of a vertex at position `BitString.lsbValue bs` is the value of its tensor
when port `i` carries the bit `bs[i]`. -/
abbrev ExplicitTensorNetwork (R : Type*) := DescribedNetwork (List R)

namespace ExplicitTensorNetwork

variable {R : Type*} (d : ExplicitTensorNetwork R)

/-- The entry of a table at a list of bits, read little-endian (`BitString.lsbValue`). A position
past the end of the table has entry zero. -/
def entry [Zero R] (table : List R) (bs : List Bool) : R :=
  table.getD (BitString.lsbValue bs) 0

/-- The bits on a list of ports under an assignment of bits to the edges. A port naming no edge
reads `false`. -/
def portBits (x : Fin d.numEdges → Bool) (ports : List ℕ) : List Bool :=
  ports.map fun i => if h : i < d.numEdges then x ⟨i, h⟩ else false

/-- The *contraction* of an explicit network: the sum over all assignments of bits to the edges of
the product, over the vertices, of the table entries at the bits on their ports. -/
def contraction [CommSemiring R] : R :=
  ∑ x : Fin d.numEdges → Bool, (d.vertices.map fun v => entry v.2 (d.portBits x v.1)).prod

/-- The *maximum degree*: the largest number of ports of a vertex, or zero without vertices. -/
def maxDegree : ℕ :=
  (d.vertices.map fun v => v.1.length).foldr max 0

/-- The total length of the tables. -/
def tableLength : ℕ :=
  (d.vertices.map fun v => v.2.length).sum

private theorem foldr_max_le_iff (l : List ℕ) (k : ℕ) : l.foldr max 0 ≤ k ↔ ∀ n ∈ l, n ≤ k := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih]

/-- The maximum degree is at most `k` exactly when every vertex has at most `k` ports. -/
theorem maxDegree_le_iff {k : ℕ} : d.maxDegree ≤ k ↔ ∀ v ∈ d.vertices, v.1.length ≤ k := by
  rw [maxDegree, foldr_max_le_iff]
  constructor
  · exact fun h v hv => h _ (List.mem_map_of_mem hv)
  · rintro h _ hn
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hn
    exact h v hv

/-- Every vertex has at most `maxDegree` ports. -/
theorem length_le_maxDegree {v : List ℕ × List R} (hv : v ∈ d.vertices) :
    v.1.length ≤ d.maxDegree :=
  d.maxDegree_le_iff.mp le_rfl v hv

end ExplicitTensorNetwork

private theorem getD_ofFn {n : ℕ} (x : Fin n → Bool) (i : ℕ) :
    (List.ofFn x).getD i false = if h : i < n then x ⟨i, h⟩ else false := by
  by_cases h : i < n
  · rw [dite_eq_left h, List.getD_eq_getElem _ _ (by simpa using h), List.getElem_ofFn]
  · rw [dite_eq_right h, List.getD_eq_default _ _ (by simp only [List.length_ofFn]; omega)]

/-- **Explicit networks**: with table lookup as the evaluator, the contraction of a described
network is that of the explicit network. -/
theorem DescribedNetwork.contraction_entry {R : Type*} [CommSemiring R]
    (d : ExplicitTensorNetwork R) :
    DescribedNetwork.contraction ExplicitTensorNetwork.entry d = d.contraction := by
  refine Finset.sum_congr rfl fun x _ => ?_
  simp only [wordBits, ExplicitTensorNetwork.portBits]
  congr 1
  refine List.map_congr_left fun v _ => ?_
  congr 2
  funext i
  exact getD_ofFn x i

/-! ### Writing a tensor network out -/

namespace TensorNetwork

variable {R V E : Type*} [DecidableEq V] {n m : ℕ} (N : TensorNetwork R Bool V E) (ev : V ≃ Fin n)
  (ee : E ≃ Fin m)

/-- The ports of a vertex when the edges are numbered by `ee`: the numbers of the edges at the
vertex, in increasing order. -/
def explicitPorts (v : V) : List (Fin m) :=
  (List.finRange m).filter fun j => N.src (ee.symm j) = v ∨ N.tgt (ee.symm j) = v

/-- An edge is a port of `v` exactly when it is incident to `v`. -/
@[simp] theorem mem_explicitPorts {v : V} {j : Fin m} :
    j ∈ N.explicitPorts ee v ↔ N.src (ee.symm j) = v ∨ N.tgt (ee.symm j) = v := by
  simp [explicitPorts]

/-- The table of a vertex: its tensor at each list of bits on its ports, by position. -/
def explicitTable (v : V) : List R :=
  (List.range (2 ^ (N.explicitPorts ee v).length)).map fun j =>
    N.tensor v fun e => j.testBit ((N.explicitPorts ee v).idxOf (ee e))

/-- **A written-out table evaluates the tensor.** At the bits that an assignment puts on the ports
of `v`, the table of `v` has the value of the tensor at that assignment. -/
theorem entry_explicitTable [Zero R] (v : V) (x : Fin m → Bool) :
    ExplicitTensorNetwork.entry (N.explicitTable ee v) ((N.explicitPorts ee v).map x) =
      N.tensor v (x ∘ ee) := by
  set ps := N.explicitPorts ee v
  have hlt : BitString.lsbValue (ps.map x) < (N.explicitTable ee v).length := by
    simpa [explicitTable, ps] using BitString.lsbValue_lt (ps.map x)
  rw [ExplicitTensorNetwork.entry, List.getD_eq_getElem _ _ hlt]
  simp only [explicitTable, List.getElem_map, List.getElem_range]
  refine N.tensor_congr v _ _ fun e he => ?_
  have hmem : ee e ∈ ps := (N.mem_explicitPorts ee).mpr (by simpa using he)
  have hidx := List.idxOf_lt_length_of_mem hmem
  rw [BitString.testBit_lsbValue, List.getD_eq_getElem _ _ (by simpa using hidx), List.getElem_map,
    List.getElem_idxOf hidx, Function.comp_apply]

/-- An edge is a port of a vertex at most once. -/
theorem nodup_explicitPorts (v : V) : (N.explicitPorts ee v).Nodup :=
  (List.nodup_finRange m).filter _

/-- **The ports of a vertex are its incident edges**: their number is its degree. -/
theorem length_explicitPorts (v : V) :
    (N.explicitPorts ee v).length = (N.incidenceSet v).ncard := by
  classical
  rw [← List.toFinset_card_of_nodup (N.nodup_explicitPorts ee v),
    ← Set.ncard_image_of_injective _ ee.injective, ← Set.ncard_coe_finset]
  congr 1
  ext j
  simp [Multigraph.mem_incidenceSet]

/-- The number of times the edge numbered `j` is a port of `v`: once if it is incident to `v`, and
never otherwise. -/
theorem count_explicitPorts (v : V) (j : Fin m) :
    ((N.explicitPorts ee v).map Fin.val).count j.val =
      if N.src (ee.symm j) = v ∨ N.tgt (ee.symm j) = v then 1 else 0 := by
  rw [List.Nodup.count ((N.nodup_explicitPorts ee v).map Fin.val_injective)]
  simp only [List.mem_map, Fin.val_inj, exists_eq_right, mem_explicitPorts]

/-- A table lists the values of the tensor at all `2 ^ (number of ports)` lists of bits on the
ports. -/
theorem length_explicitTable (v : V) :
    (N.explicitTable ee v).length = 2 ^ (N.explicitPorts ee v).length := by
  simp [explicitTable]

/-- Every entry of a written-out table is a value of the tensor. -/
theorem exists_tensor_of_mem_explicitTable {v : V} {a : R} (ha : a ∈ N.explicitTable ee v) :
    ∃ y, a = N.tensor v y := by
  obtain ⟨j, -, rfl⟩ := List.mem_map.mp ha
  exact ⟨_, rfl⟩

/-- A Boolean tensor network on finite types written out as an explicit network, numbering the
vertices by `ev` and the edges by `ee`: vertex `i` is `ev.symm i`, with its ports in increasing
order and its table. -/
def toExplicit : ExplicitTensorNetwork R where
  numEdges := m
  vertices := List.ofFn fun i =>
    ((N.explicitPorts ee (ev.symm i)).map Fin.val, N.explicitTable ee (ev.symm i))

/-- The vertices of the written-out network are the ports and tables of the vertices. -/
theorem mem_vertices_toExplicit {p : List ℕ × List R} :
    p ∈ (N.toExplicit ev ee).vertices ↔
      ∃ v, p = ((N.explicitPorts ee v).map Fin.val, N.explicitTable ee v) := by
  simp only [toExplicit, List.mem_ofFn]
  constructor
  · rintro ⟨i, rfl⟩
    exact ⟨_, rfl⟩
  · rintro ⟨v, rfl⟩
    exact ⟨ev v, by simp⟩

/-- **The degree bound carries over**: a vertex of the written-out network has as many ports as
the vertex has incident edges. -/
theorem maxDegree_toExplicit_le [Finite E] {D : ℕ} (hD : N.MaxDegreeLE D) :
    (N.toExplicit ev ee).maxDegree ≤ D := by
  rw [ExplicitTensorNetwork.maxDegree_le_iff]
  intro p hp
  obtain ⟨v, rfl⟩ := (N.mem_vertices_toExplicit ev ee).mp hp
  rw [List.length_map, length_explicitPorts]
  exact hD v

/-- Every table of the written-out network has an entry for every list of bits on its ports. -/
theorem length_table_toExplicit {p : List ℕ × List R} (hp : p ∈ (N.toExplicit ev ee).vertices) :
    p.2.length = 2 ^ p.1.length := by
  obtain ⟨v, rfl⟩ := (N.mem_vertices_toExplicit ev ee).mp hp
  simp [length_explicitTable]

/-- Every table entry of the written-out network is a value of a tensor. -/
theorem exists_tensor_of_mem_toExplicit {p : List ℕ × List R}
    (hp : p ∈ (N.toExplicit ev ee).vertices) {a : R} (ha : a ∈ p.2) :
    ∃ v y, a = N.tensor v y := by
  obtain ⟨v, rfl⟩ := (N.mem_vertices_toExplicit ev ee).mp hp
  exact ⟨v, N.exists_tensor_of_mem_explicitTable ee ha⟩

private theorem sum_drop_ofFn (f : Fin n → ℕ) (r : ℕ) :
    ((List.ofFn f).drop r).sum = ∑ a with ¬ a.val < r, f a := by
  have h := List.sum_take_add_sum_drop (List.ofFn f) r
  rw [List.sum_take_ofFn, List.sum_ofFn,
    ← Finset.sum_filter_add_sum_filter_not Finset.univ (fun a : Fin n => a.val < r)] at h
  omega

/-- **Rows first.** If every edge joins a vertex numbered below `r` to one numbered at least `r`,
the written-out network is bipartite with the first `r` vertices as rows. -/
theorem isRowsFirstBipartite_toExplicit (r : ℕ)
    (hside : ∀ e, (ev (N.src e) : ℕ) < r ↔ ¬ (ev (N.tgt e) : ℕ) < r) :
    (N.toExplicit ev ee).IsRowsFirstBipartite r := by
  refine ⟨fun p hp i hi => ?_, fun i hi => ?_⟩
  · obtain ⟨v, rfl⟩ := (N.mem_vertices_toExplicit ev ee).mp hp
    obtain ⟨j, -, rfl⟩ := List.mem_map.mp hi
    exact j.isLt
  · -- The edge numbered `i` is a port of its source and its target, which are distinct.
    set j : Fin m := ⟨i, hi⟩
    set e := ee.symm j
    have hne : N.src e ≠ N.tgt e := fun h => by
      have := hside e
      rw [h] at this
      tauto
    have hcount : ∀ a : Fin n, ((N.explicitPorts ee (ev.symm a)).map Fin.val).count i =
        (if ev (N.src e) = a then 1 else 0) + (if ev (N.tgt e) = a then 1 else 0) := by
      intro a
      rw [show i = j.val from rfl, count_explicitPorts]
      simp only [Equiv.eq_symm_apply]
      by_cases hs : ev (N.src e) = a <;> by_cases ht : ev (N.tgt e) = a
      · exact absurd (ev.injective (hs.trans ht.symm)) hne
      all_goals simp [e, hs, ht]
    have hsum : ∀ s : Finset (Fin n),
        ∑ a ∈ s, ((N.explicitPorts ee (ev.symm a)).map Fin.val).count i =
          (if ev (N.src e) ∈ s then 1 else 0) + (if ev (N.tgt e) ∈ s then 1 else 0) := by
      intro s
      simp only [hcount, Finset.sum_add_distrib, Finset.sum_ite_eq]
    have hv : (N.toExplicit ev ee).vertices = List.ofFn fun a =>
        ((N.explicitPorts ee (ev.symm a)).map Fin.val, N.explicitTable ee (ev.symm a)) := rfl
    rw [hv, List.map_take, List.map_drop, List.map_ofFn, List.sum_take_ofFn, sum_drop_ofFn]
    simp only [Function.comp_def]
    rw [hsum, hsum]
    have := hside e
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    by_cases h : (ev (N.src e) : ℕ) < r <;> simp_all

/-- **Writing a network out preserves its contraction.** -/
theorem contraction_toExplicit [CommSemiring R] [Fintype V] [Fintype E] [DecidableEq E] :
    (N.toExplicit ev ee).contraction = N.contraction := by
  rw [ExplicitTensorNetwork.contraction, contraction]
  refine Fintype.sum_equiv (ee.symm.arrowCongr (Equiv.refl Bool)) _ _ fun x => ?_
  have hv : (N.toExplicit ev ee).vertices = List.ofFn fun i =>
      ((N.explicitPorts ee (ev.symm i)).map Fin.val, N.explicitTable ee (ev.symm i)) := rfl
  rw [hv, List.map_ofFn, List.prod_ofFn, ← ev.symm.prod_comp]
  refine Finset.prod_congr rfl fun i _ => ?_
  -- Every port names an edge, so the bits on the ports are those of the assignment.
  have hbits : (N.toExplicit ev ee).portBits x ((N.explicitPorts ee (ev.symm i)).map Fin.val) =
      (N.explicitPorts ee (ev.symm i)).map x := by
    unfold ExplicitTensorNetwork.portBits
    rw [List.map_map]
    exact List.map_congr_left fun j _ => dite_eq_left j.isLt
  simp only [Function.comp_apply]
  rw [hbits, entry_explicitTable]
  rfl

end TensorNetwork

end Cslib.Circuits.Frontier
