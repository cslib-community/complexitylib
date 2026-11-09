/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.Basic

/-!
# Parallel edges and loops in executable constraint graphs

An executable constraint graph (`Cslib.PCP.Encoded.Graph`) stores a list of edge occurrences, so
it may contain parallel edges (two occurrences with the same ordered pair of endpoints) and loops
(an occurrence whose two endpoints coincide). This file names the two restrictions.

* A graph has **no parallel edges** (`Graph.NoParallelEdges`) when no two of its edge occurrences
  have the same ordered pair of endpoints. Edges in opposite directions between the same two
  vertices are allowed, and so are loops, each at most once per vertex. The predicate is
  therefore weaker than simplicity in the sense of `SimpleGraph`, which also excludes loops.
* A graph is **loopless** (`Graph.IsLoopless`) when no edge occurrence has equal endpoints.

The definitions do not refer to the constraints, so they apply to every constraint type. In a
Label Cover instance (`Cslib.Complexity.GapLabelCover`) the left and right vertices are numbered
separately, so an edge with `src = dst` joins two different vertices; having no parallel edges
there says that each pair of a left and a right vertex is joined by at most one projection.

Without parallel edges, the uniformly random edge of a Label Cover instance is a question pair of a
two-prover game whose acceptance test is the constraint on that edge alone. This is how the
parallel repetition theorem is transferred to Label Cover in
`CslibFrontier.Computability.PCP.Approximation.LabelCover.Repetition`.

## Main definitions

* `Cslib.PCP.Encoded.Graph.NoParallelEdges`: no two edge occurrences have the same ordered
  endpoints.
* `Cslib.PCP.Encoded.Graph.IsLoopless`: no edge occurrence is a loop.

## Main results

* `Cslib.PCP.Encoded.Graph.NoParallelEdges.eq_of_src_eq_of_dst_eq`: without parallel edges, an
  edge occurrence is determined by its endpoints.
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

variable {C : Type}

/-- A graph has **no parallel edges** when no two of its edge occurrences have the same ordered
pair of endpoints: the list of `(src, dst)` pairs has no duplicates. Loops are allowed. -/
def NoParallelEdges (g : Graph C) : Prop :=
  (g.edges.map fun d => (d.src, d.dst)).Nodup

/-- A graph is **loopless** when no edge occurrence has equal endpoints. -/
def IsLoopless (g : Graph C) : Prop :=
  ∀ d ∈ g.edges, d.src ≠ d.dst

instance (g : Graph C) : Decidable g.NoParallelEdges := by
  unfold NoParallelEdges
  infer_instance

instance (g : Graph C) : Decidable g.IsLoopless := by
  unfold IsLoopless
  infer_instance

/-- **Without parallel edges, an edge occurrence is determined by its endpoints.** -/
theorem NoParallelEdges.eq_of_src_eq_of_dst_eq {g : Graph C} (hg : g.NoParallelEdges)
    {i j : Fin g.edges.length} (hsrc : (g.edges.get i).src = (g.edges.get j).src)
    (hdst : (g.edges.get i).dst = (g.edges.get j).dst) : i = j := by
  have hlen : (g.edges.map fun d => (d.src, d.dst)).length = g.edges.length := List.length_map _
  have h := (List.nodup_iff_injective_get.mp hg)
    (a₁ := Fin.cast hlen.symm i) (a₂ := Fin.cast hlen.symm j)
    (by simpa using And.intro hsrc hdst)
  ext
  simpa using congrArg Fin.val h

/-- A graph without edges has no parallel edges. -/
theorem noParallelEdges_of_edges_eq_nil {g : Graph C} (hg : g.edges = []) :
    g.NoParallelEdges := by
  simp [NoParallelEdges, hg]

/-- A graph without edges is loopless. -/
theorem isLoopless_of_edges_eq_nil {g : Graph C} (hg : g.edges = []) : g.IsLoopless := by
  simp [IsLoopless, hg]

end Cslib.PCP.Encoded.Graph
