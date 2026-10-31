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

/-!
# Explicit Boolean tensor networks

An *explicit* Boolean tensor network (`ExplicitTensorNetwork R`) is the data an algorithm reads:
the number of edges, numbered `0, 1, …`, and a list of vertices, each given by

* its ordered list of *ports*, the numbers of the edges at the vertex, and
* its *table*: the value of its tensor when port `i` carries the bit `bs[i]` is the entry at
  position `BitString.lsbValue bs`, the number whose binary digit `i` is `bs[i]`
  (`BitString.testBit_lsbValue`).

So a vertex with `k` ports has a table of `2 ^ k` entries. The contraction of an explicit network
(`ExplicitTensorNetwork.contraction`) sums, over all assignments of bits to the edges, the product
of the table entries at the bits on the ports. It needs no well-formedness: a port naming no edge
reads `false`, and a position past the end of a table has entry zero.

Its size measures are the number of edges, the number of vertices, the maximum number of ports of
a vertex (`ExplicitTensorNetwork.maxDegree`) and the total length of the tables
(`ExplicitTensorNetwork.tableLength`).

**Writing a network out** (`TensorNetwork.toExplicit`). Given numberings of the vertices and the
edges of a Boolean tensor network on finite types, list the edges at each vertex in increasing
order and tabulate its tensor on them. The contraction is unchanged
(`TensorNetwork.contraction_toExplicit`).

## Main definitions

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork`: an explicit Boolean tensor network.
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

* `Cslib.Circuits.Frontier.ExplicitTensorNetwork.maxDegree_le_iff`: the degree bound.
* `Cslib.Circuits.Frontier.TensorNetwork.entry_explicitTable`: a written-out table evaluates the
  tensor.
* `Cslib.Circuits.Frontier.TensorNetwork.contraction_toExplicit`: writing a network out preserves
  its contraction.

## References

* [OpenAI, *The Exponential Time Hypothesis is False*][OpenAI2026ETH], Appendix D.1 (p. 53).
-/

@[expose] public section

namespace Cslib.Circuits.Frontier

/-- An *explicit Boolean tensor network* over `R`: the number of edges, numbered from zero, and a
list of vertices. A vertex is given by its ordered list of *ports*, the numbers of its edges, and
its *table*, whose entry at position `BitString.lsbValue bs` is the value of its tensor when
port `i` carries the bit `bs[i]`. -/
structure ExplicitTensorNetwork (R : Type*) where
  /-- The number of edges; the edges are numbered `0, …, numEdges - 1`. -/
  numEdges : ℕ
  /-- The vertices, each given by its ports and its table. -/
  vertices : List (List ℕ × List R)

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

/-- A Boolean tensor network on finite types written out as an explicit network, numbering the
vertices by `ev` and the edges by `ee`: vertex `i` is `ev.symm i`, with its ports in increasing
order and its table. -/
def toExplicit : ExplicitTensorNetwork R where
  numEdges := m
  vertices := List.ofFn fun i =>
    ((N.explicitPorts ee (ev.symm i)).map Fin.val, N.explicitTable ee (ev.symm i))

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
