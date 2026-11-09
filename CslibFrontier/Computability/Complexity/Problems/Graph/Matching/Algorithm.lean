/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Instance
public import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Subgraph
public import CslibFrontier.Computability.PolyTime.CSP.Edge.Solver.Endpoint
import CslibFrontier.Computability.Complexity.Problems.Graph.PerfectMatchingPolyTime
import CslibFrontier.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Option

/-!
# Executable unweighted matching algorithms

The native even-delta-matroid optimizer is applied to `Graph.matchingInstance`. Original edges
whose two endpoint bits are true are returned in normalized edge-list order, retaining their
original binary endpoint labels and orientation. Loops, undeclared endpoints and duplicates
in either orientation follow `Graph.induced`; duplicate declarations have no effect.

All enumeration is funded by actual vertex, edge, scope, row and occurrence lists. No interval
below a raw binary name is constructed. Explicit exactly-one tables have one stored one-hot row
per port, so their row widths enter the native polynomial certificate. This is a specialization
of [KazdaKolmogorovRolinek2018], not a tight classical Edmonds operation-bound claim.
-/

public section

namespace Cslib.Complexity.Graph

open Cslib.Logic.PL Turing.MultiTapeTM

/-- Framed lists of original binary edge pairs, the public matching output encoding. -/
abbrev encMatching := encList (encPair encNat encNat)

/-- A complete framed graph followed by its framed occurrence-bit buffer. -/
abbrev encMatchingBuffer := encPair encGraph (encList encBool)

/-- Read whether every actual occurrence of a named edge is true. -/
@[expose] def selectedBit (F : CSP CSP.Table ℕ) (bits : List Bool) (x : ℕ) : Bool :=
  F.occurrences.all fun o => decide (o.2.2 ≠ x) || CSP.EdgeAugmenting.readRecord F bits o

/-- Original edge positions mutually selected by the optimizer's occurrence buffer. -/
@[expose] def matchingPositions (G : Graph) (bits : List Bool) : List ℕ :=
  (List.range G.edgeList.length).filter fun i => selectedBit G.matchingInstance bits (2 * i)

/-- Executable conversion from normalized positions to original graph edge pairs. -/
@[expose] def edgesAtPositions (G : Graph) (positions : List ℕ) : List (ℕ × ℕ) :=
  positions.map fun i => G.edgeList.getD i (0, 0)

/-- Total maximum-cardinality search, returning canonical positions of original graph edges. -/
@[expose] def maximumMatchingPositions (G : Graph) : List ℕ :=
  matchingPositions G ((CSP.EdgeSolver.optimize G.matchingInstance).getD [])

/-- Total maximum-cardinality search on complete raw graphs. The internal failure branch is
unreachable: the generated instance passes the full model guard on every graph. -/
@[expose] def maximumMatching (G : Graph) : List (ℕ × ℕ) :=
  G.edgesAtPositions G.maximumMatchingPositions

/-- The Mathlib subgraph represented by the returned canonical original positions. -/
@[expose] def maximumMatchingSubgraph (G : Graph) : G.induced.Subgraph :=
  G.matchingOfPositions G.maximumMatchingPositions.toFinset

/-- Check coverage of every distinct declared vertex by selected original edges. -/
@[expose] def coversVertices (G : Graph) (edges : List (ℕ × ℕ)) : Bool :=
  G.distinctVertices.all fun v => edges.any fun e => incident e v

/-- Total perfect-matching search, including the empty perfect matching on an empty graph. -/
@[expose] def perfectMatching (G : Graph) : Option (List (ℕ × ℕ)) :=
  let edges := G.maximumMatching
  if G.coversVertices edges then some edges else none

/-- Perfect-matching decision on every complete raw framed graph. -/
@[expose] def decidePerfectMatching (G : Graph) : Bool := G.perfectMatching.isSome

/-- Every generated instance passes all actual finite model tests. -/
theorem checkModel_matchingInstance (G : Graph) :
    CSP.EdgeSolver.checkModel G.matchingInstance = true :=
  (CSP.EdgeSolver.checkModel_eq_true _).mpr
    ⟨G.edgeInstance_matchingInstance, G.evenConstraints_matchingInstance⟩

/-- The full optimizer always produces an optimal original occurrence labeling. -/
theorem matching_optimizer_spec (G : Graph) :
    ∃ bits, CSP.EdgeSolver.optimize G.matchingInstance = some bits ∧
      CSP.IsOptimalLabeling CSP.Table.sem (CSP.EdgeAugmenting.labeling G.matchingInstance bits) :=
  CSP.EdgeSolver.optimize_spec _ G.checkModel_matchingInstance

/-- The finite selected-edge scan reads exactly the actual occurrence labeling. -/
theorem selectedBit_eq_true {F : CSP CSP.Table ℕ} (bits : List Bool) (x : ℕ) :
    selectedBit F bits x = true ↔ ∀ o : CSP.Occurrence F,
      o.var = x → CSP.EdgeAugmenting.labeling F bits o = true := by
  simp only [selectedBit, List.all_eq_true, Bool.or_eq_true, decide_eq_true_eq]
  constructor
  · intro h o ho
    have hh := h o.record (CSP.mem_occurrences.mpr ⟨o, rfl⟩)
    exact (CSP.EdgeAugmenting.read_record bits o) ▸
      hh.resolve_left (by simp only [CSP.Occurrence.record, ho, ne_eq, not_true_eq_false,
        not_false_eq_true])
  · intro h r hr
    obtain ⟨o, rfl⟩ := CSP.mem_occurrences.mp hr
    by_cases ho : o.var = x
    · exact Or.inr ((CSP.EdgeAugmenting.read_record bits o).trans (h o ho))
    · exact Or.inl ho

/-- A returned position is in range and its original edge is mutually selected. -/
theorem mem_matchingPositions (G : Graph) (bits : List Bool) (i : ℕ) :
    i ∈ G.matchingPositions bits ↔ i < G.edgeList.length ∧
      2 * i ∈ CSP.selectedVariables (CSP.EdgeAugmenting.labeling G.matchingInstance bits) := by
  simp only [matchingPositions, List.mem_filter, List.mem_range, selectedBit_eq_true,
    CSP.mem_selectedVariables]
  constructor
  · rintro ⟨hi, hall⟩
    exact ⟨hi, (G.mem_vars_matchingInstance).mpr (Or.inl ⟨i, hi, rfl⟩), hall⟩
  · exact fun ⟨hi, _, hall⟩ => ⟨hi, hall⟩

end Cslib.Complexity.Graph
