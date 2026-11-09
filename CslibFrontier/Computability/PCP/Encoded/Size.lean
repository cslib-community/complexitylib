/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.Basic
import CslibFrontier.Computability.Machines.Turing.MultiTape.Encodings.Length

/-!
# Encoded size of constraint graphs

The encoding charges unary vertex identifiers and each constraint descriptor, including the
frames around the endpoint pairs and the edge list. Well-formed graphs therefore have encoded
size bounded by their vertex and edge counts together with the descriptor lengths.

## Main results

* `Cslib.PCP.Encoded.Edge.length_encoding`: exact size of one encoded edge.
* `Cslib.PCP.Encoded.Graph.length_encoding`: exact size of the whole encoded graph.
* `Cslib.PCP.Encoded.Graph.WellFormed.length_encoding_le`: cardinality and descriptor-size bound.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Turing.MultiTapeTM

variable {C : Type} (enc : C ↪ List Bool)

/-- Both unary endpoints are framed; the final descriptor is stored without another inner frame. -/
theorem Edge.length_encoding (edge : Edge C) :
    (Edge.encoding enc edge).length =
      2 * edge.src + 2 * edge.dst + (enc edge.constraint).length + 2 := by
  change (encPair encUnary (encPair encUnary enc) (edge.src, edge.dst, edge.constraint)).length = _
  simp only [length_encPair, encUnary_apply, List.length_replicate]
  ring

/-- Each edge receives an outer list frame, and the declared vertex count its own unary frame. -/
theorem Graph.length_encoding (g : Graph C) :
    (Graph.encoding enc g).length = 2 * g.vertices + 1 +
      (g.edges.map fun edge =>
        4 * edge.src + 4 * edge.dst + 2 * (enc edge.constraint).length + 5).sum := by
  change (encPair encUnary (encList (Edge.encoding enc)) (g.vertices, g.edges)).length = _
  simp only [length_encPair, encUnary_apply, List.length_replicate, length_encList,
    Edge.length_encoding]
  congr 3
  funext edge
  ring

/-- Endpoint bounds give a full encoded-size bound for arbitrary bounded descriptors. -/
theorem Graph.WellFormed.length_encoding_le {g : Graph C} (hg : g.WellFormed) (bound : ℕ)
    (hbound : ∀ edge ∈ g.edges, (enc edge.constraint).length ≤ bound) :
    (Graph.encoding enc g).length ≤
      2 * g.vertices + 1 + g.edges.length * (8 * g.vertices + 2 * bound + 5) := by
  have he (edge : Edge C) (hedge : edge ∈ g.edges) :
      (Edge.encoding enc edge).length ≤ 4 * g.vertices + bound + 2 := by
    rw [Edge.length_encoding]
    have hend := hg edge hedge
    have hdesc := hbound edge hedge
    lia
  have hlist := length_encList_le (Edge.encoding enc) g.edges he
  change (encPair encUnary (encList (Edge.encoding enc)) (g.vertices, g.edges)).length ≤ _
  simp only [length_encPair, encUnary_apply, List.length_replicate]
  nlinarith

end Cslib.PCP.Encoded
