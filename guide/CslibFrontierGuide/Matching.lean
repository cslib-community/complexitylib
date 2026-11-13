/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
import VersoManual
import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Endpoint

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

set_option pp.rawOnError true
set_option verso.code.warnLineLength 80

#doc (Manual) "Unweighted Graph Matching" =>
%%%
tag := "unweighted-graph-matching"
%%%

Import the endpoint below for executable perfect search, maximum search, and ordinary native
polynomial-time certificates. The mathematical model is the existing Mathlib subgraph of
{name}`Cslib.Complexity.Graph.induced`.

```
import CslibFrontier.Computability.Complexity.Problems.Graph.Matching.Endpoint

open Cslib.Complexity Cslib.Complexity.Graph Turing.MultiTapeTM
```

```lean -show
open Cslib.Complexity Cslib.Complexity.Graph Turing.MultiTapeTM
```

# Search and interpret the result

A {name}`Cslib.Complexity.Graph` stores declared natural-number names in
{name}`Cslib.Complexity.Graph.vertices` and original endpoint pairs in
{name}`Cslib.Complexity.Graph.edges`. Names are binary, even when numerically large. The matching
interpretation is undirected: it discards loops and undeclared endpoints, and deduplicates
parallel or reversed edges and repeated declarations. Selected pairs retain their original
orientation; the input record retains its original lists.

```lean
def oneEdge : Graph := ⟨[7, 42, 7], [(7, 7), (42, 7), (7, 42)]⟩

example : oneEdge.maximumMatching = [(42, 7)] := by decide +kernel

example : oneEdge.perfectMatching = some [(42, 7)] := by decide +kernel

example : oneEdge.decidePerfectMatching = true := by decide +kernel
```

{name}`Cslib.Complexity.Graph.maximumMatching` always returns a maximum matching, including
when the graph has isolates or an odd cycle. {name}`Cslib.Complexity.Graph.perfectMatching`
returns `none` when some declared vertex cannot be covered. On the empty graph it returns
`some []`.

The output has an associated subgraph in the original mathematical model. Its edges are
exactly the returned pairs in either orientation:

```lean
example (G : Graph) : G.maximumMatchingSubgraph.IsMaximumMatching :=
  maximumMatchingSubgraph_isMaximumMatching G

example (G : Graph) (M : G.induced.Subgraph) (hM : M.IsMatching) :
    M.edgeSet.ncard ≤ G.maximumMatching.length :=
  maximumMatching_cardinality G M hM

example (G : Graph) {edges : List (ℕ × ℕ)}
    (h : G.perfectMatching = some edges) :
    edges = G.maximumMatching ∧ G.maximumMatchingSubgraph.IsPerfectMatching :=
  perfectMatching_spec h

example (G : Graph) : G.decidePerfectMatching = true ↔
    ∃ M : G.induced.Subgraph, M.IsPerfectMatching :=
  decidePerfectMatching_eq_true G
```

For clients storing edge positions, {name}`Cslib.Complexity.Graph.maximumMatchingPositions`
returns positions in the normalized edge list, and
{name}`Cslib.Complexity.Graph.edgesAtPositions` converts them to original pairs executably.

# Use the resource certificates

The input encoding {name}`Cslib.Complexity.encGraph` charges both complete framed lists,
including binary names. The output encoding {name}`Cslib.Complexity.Graph.encMatching` is a
framed list of binary endpoint pairs. No model, degree bound, perfect solver, or runtime witness
is supplied by the caller.

```lean
example : ComputableInPolyTime maximumMatching encGraph encMatching :=
  computableInPolyTime_maximumMatching

example : ComputableInPolyTime perfectMatching encGraph
    (encOption encMatching) :=
  computableInPolyTime_perfectMatching

example : perfectMatchingProblem ∈ P encGraph := perfectMatchingProblem_mem_P
```

The implementation specializes the Kazda–Kolmogorov–Rolinek even-delta-matroid solver. Each
vertex chooses an incident edge or a private unmatched port, whose other end is pinned false.
Mutually true original edges form a matching; the exact defect identity makes minimum defect
equivalent to maximum cardinality. All generated table rows, their widths, retained name bits,
intermediate solver states and output bits enter polynomial composition. Loops enumerate only
actual lists, including for sparse binary names. These certificates do not assert a tight
classical Edmonds operation bound or solve weighted/min-cost matching. Typed encoded inputs
also do not by themselves provide a parser for malformed bit strings.
