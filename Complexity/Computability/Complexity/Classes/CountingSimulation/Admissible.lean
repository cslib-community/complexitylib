/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.Circuit.Frontier.TensorNetwork.Explicit
public import Mathlib.Data.Nat.Log

/-!
# Admissible explicit networks for the counting simulation

The interfaces of the counting simulation of #1833
(`Cslib.Complexity.CountingSimulation.NetworkFamily`,
`Cslib.Complexity.CountingSimulation.ContractionAlgorithm`) are parameterized by an
admissibility predicate `Admissible C s G` on networks. This module fixes the predicate for
explicit Boolean tensor networks with a number of row vertices,
`Cslib.Complexity.CountingSimulation.ExplicitAdmissible`, the form in which the block-counting
networks are built (milestone H3) and the contraction theorem consumes them (milestone T2).

A network `(r, G)` is admissible at size `s` with constant `C` when `G` is bipartite with its
first `r` vertices as rows (`Cslib.Circuits.Frontier.ExplicitTensorNetwork.IsRowsFirstBipartite`),
it has at most `C s` edges and at most `C s` vertices, its maximum degree is at most `C ⌊log₂ s⌋`,
every table lists the values at all bit strings on its ports, and it has at least `s` edges. The
last two conditions spare the contraction algorithm short tables and networks much smaller than
the size parameter.
-/

public section

namespace Cslib.Complexity.CountingSimulation

open Cslib.Circuits.Frontier

/-- **Admissible explicit networks** at size `s` with constant `C`: a network `G` with `r` row
vertices is rows-first bipartite, has between `s` and `C s` edges, at most `C s` vertices,
maximum degree at most `C ⌊log₂ s⌋`, and a table of length `2 ^ (number of ports)` at every
vertex. -/
@[expose] def ExplicitAdmissible (C s : ℕ) (G : ℕ × ExplicitTensorNetwork ℕ) : Prop :=
  G.2.IsRowsFirstBipartite G.1 ∧ G.2.numEdges ≤ C * s ∧ G.2.maxDegree ≤ C * Nat.log 2 s ∧
    G.2.vertices.length ≤ C * s ∧ (∀ v ∈ G.2.vertices, v.2.length = 2 ^ v.1.length) ∧
    s ≤ G.2.numEdges

end Cslib.Complexity.CountingSimulation
