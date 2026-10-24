/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.AssignmentTester
public import Complexity.Computability.PCP.Encoded.GenericComposition
public import Complexity.Computability.PCP.Composition

/-!
# Executable composition with the Hadamard assignment tester

Composition replaces each original edge by the tester's coin-to-query edges. Supplied finite
numberings give disjoint identifiers to input-table bits, proof-table bits, and coin vertices.
Explicit lists enumerate coins and queries; the exact interpretation and soundness results
require each list to enumerate its type once. The program itself also handles empty or incomplete
lists, and preserves endpoint bounds for every well-formed input graph.

The alphabet, its numbering, and the coin/query lists are fixed independently of the input graph.
The uniform polynomial-time certificate charges graph enumeration, tester queries, copying, and
output storage. These constants can be enormous: this establishes asymptotic constructibility,
not a practical bound on the size of a fully expanded tester gadget.

`composeTabulated` materializes each output constraint as a Boolean table over the fixed answer
alphabet. Its certificate hides internal coin/query encodings and composes with a graph routine
written in the client's input representation.

## Main definitions

* `Cslib.PCP.Encoded.Graph.compose`: executable gadget enumeration and vertex numbering.
* `Cslib.PCP.Encoded.Graph.composeTabulated`: composition with tabulated output constraints.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_composeTabulated`: uniform, compositional cost certificate.
* `Cslib.PCP.Encoded.Graph.toGraph_compose`: exact agreement with mathematical composition.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_compose`: the existing `1/476` gap bound transfers.
* `Cslib.PCP.Encoded.Graph.satisfiable_composeTabulated_iff`: satisfiability is preserved.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Cslib.PCP.HadamardTester Turing.MultiTapeTM

namespace HadamardTester

/-- Executable conjunction tester data used by the legacy composition API. -/
def implementation {α : Type} [Fintype α] [DecidableEq α] :
    AssignmentTester.Implementation α (α → Bool) (LinPos α ⊕ QuadPos α) (Rand α) Query Bool where
  query := query
  accepts := accepts

/-- The executable conjunction tester implements the mathematical assignment tester exactly. -/
theorem realizes_implementation {α : Type} [Fintype α] [DecidableEq α] :
    (implementation (α := α)).Realizes Cslib.PCP.HadamardTester.assignmentTester where
  query_eq := query_eq
  accepts_eq_true := accepts_eq_true

end HadamardTester

namespace Graph

variable {α Input : Type} [Fintype α] [DecidableEq α]
  {input : Input ↪ List Bool} {width : ℕ}

/-- The local slots in one numbered block: an input-table bit, a proof-table bit, or a coin
vertex. The block's owner is the old vertex or edge index. -/
abbrev ComposeSlot (α : Type) : Type :=
  AssignmentTester.ComposeSlot (α → Bool) (LinPos α ⊕ QuadPos α) (Rand α)

/-- Number a queried proof position using a supplied finite slot numbering. -/
def composePosition (number : ComposeSlot α ≃ Fin width) (edge src dst : ℕ) : Pos α → ℕ :=
  AssignmentTester.Implementation.composePosition number edge src dst

/-- Build the edge from one coin vertex to one of the seventeen queried proof positions. -/
def composeEdge (number : ComposeSlot α ≃ Fin width) (edge : Edge (α → α → Bool))
    (index : ℕ) (coins : Rand α) (i : Query) : Edge ((α → α → Bool) × Rand α × Query) :=
  Encoded.HadamardTester.implementation.composeEdge number edge index coins i

/-- Verify the claimed answers and their agreement with the queried proof symbol. -/
def composeEval (descriptor : (α → α → Bool) × Rand α × Query)
    (a b : Bool × (Query → Bool)) : Bool :=
  Encoded.HadamardTester.implementation.composeEval descriptor a b

/-- Enumerate all supplied random strings and queries for every original edge, in list order. -/
def composeDarts (coins : List (Rand α)) (queries : List Query)
    (g : Graph (α → α → Bool)) : List ((ℕ × Rand α) × Query) :=
  AssignmentTester.Implementation.composeDarts coins queries g

/-- Compose an encoded graph with a specified list of coins and queries.
Full alphabet reduction requires each of those lists to enumerate its type exactly once. -/
def compose (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α))
    (queries : List Query) (g : Graph (α → α → Bool)) :
    Graph ((α → α → Bool) × Rand α × Query) :=
  Encoded.HadamardTester.implementation.compose number coins queries g

omit [Fintype α] [DecidableEq α] in
/-- Position numbering charges all runtime indices; finite dispatch only concerns the fixed
alphabet's local proof position. -/
@[fun_prop]
theorem isPolyTime_composePosition [Finite α] (number : ComposeSlot α ≃ Fin width)
    {edge src dst : Input → ℕ} {position : Input → Pos α}
    {positionEncoding : Pos α ↪ List Bool}
    (hedge : ComputableInPolyTime edge input encUnary)
    (hsrc : ComputableInPolyTime src input encUnary)
    (hdst : ComputableInPolyTime dst input encUnary)
    (hposition : ComputableInPolyTime position input positionEncoding) :
    ComputableInPolyTime
      (fun x => composePosition number (edge x) (src x) (dst x) (position x)) input encUnary :=
  AssignmentTester.Implementation.isPolyTime_composePosition number hedge hsrc hdst hposition

/-- A gadget edge is computed uniformly in the original edge, its index, coins, and query. -/
@[fun_prop]
theorem isPolyTime_composeEdge (number : ComposeSlot α ≃ Fin width)
    {edge : Input → Edge (α → α → Bool)} {index : Input → ℕ}
    {coins : Input → Rand α} {query : Input → Query}
    {coinsEncoding : Rand α ↪ List Bool} {queryEncoding : Query ↪ List Bool}
    (hedge : ComputableInPolyTime edge input (Edge.encoding (encPi (encPi encBool))))
    (hindex : ComputableInPolyTime index input encUnary)
    (hcoins : ComputableInPolyTime coins input coinsEncoding)
    (hquery : ComputableInPolyTime query input queryEncoding) :
    ComputableInPolyTime (fun x => composeEdge number (edge x) (index x) (coins x) (query x))
      input (Edge.encoding (encPair (encPi (encPi encBool))
        (encPair coinsEncoding queryEncoding))) :=
  Encoded.HadamardTester.implementation.isPolyTime_composeEdge number hedge hindex hcoins hquery

/-- The verifier's edge predicate charges all supplied finite tables and query answers. -/
@[fun_prop]
theorem isPolyTime_composeEval (coinsEncoding : Rand α ↪ List Bool)
    (queryEncoding : Query ↪ List Bool) :
    ComputableInPolyTime
      (fun p : ((α → α → Bool) × Rand α × Query) ×
          (Bool × (Query → Bool)) × (Bool × (Query → Bool)) => composeEval p.1 p.2.1 p.2.2)
      (encPair (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding))
        (encPair (encPair encBool (encPi encBool)) (encPair encBool (encPi encBool)))) encBool :=
  Encoded.HadamardTester.implementation.isPolyTime_composeEval encBool coinsEncoding queryEncoding

/-- The full construction charges the old graph, enumeration, each tester call, copying,
and the complete output graph. The finite alphabet and supplied lists are fixed. -/
@[fun_prop]
theorem isPolyTime_compose (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α))
    (queries : List Query) (coinsEncoding : Rand α ↪ List Bool)
    (queryEncoding : Query ↪ List Bool) :
    ComputableInPolyTime (compose number coins queries)
      (encoding (encPi (encPi encBool)))
      (encoding (encPair (encPi (encPi encBool)) (encPair coinsEncoding queryEncoding))) :=
  Encoded.HadamardTester.implementation.isPolyTime_compose number coins queries coinsEncoding
    queryEncoding

/-- Return composition to the fixed Boolean-table descriptor type over its answer alphabet. -/
def composeTabulated (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α))
    (queries : List Query) (g : Graph (α → α → Bool)) :
    Graph ((Bool × (Query → Bool)) → (Bool × (Query → Bool)) → Bool) :=
  Encoded.HadamardTester.implementation.composeTabulated number coins queries g

/-- Tabulated composition fixes its internal finite encodings, so clients only certify the
input graph in their own input representation. Every output constraint table is charged. -/
@[fun_prop]
theorem isPolyTime_composeTabulated {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableInPolyTime graph input (encoding (encPi (encPi encBool))))
    (number : ComposeSlot α ≃ Fin width) (coins : List (Rand α)) (queries : List Query) :
    ComputableInPolyTime (fun x => (graph x).composeTabulated number coins queries)
      input (encoding (encPi (encPi encBool))) :=
  Encoded.HadamardTester.implementation.isPolyTime_composeTabulated hgraph number coins queries

/-- Each original edge produces one edge for every supplied pair of coins and query. -/
@[simp]
theorem length_edges_compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool)) :
    (g.compose number coins queries).edges.length =
      g.edges.length * coins.length * queries.length :=
  Encoded.HadamardTester.implementation.length_edges_compose number coins queries g

/-- The declared vertex count grows by a fixed factor in the old vertices and edges. -/
@[simp]
theorem vertices_compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool)) :
    (g.compose number coins queries).vertices = (g.vertices + g.edges.length) * width :=
  Encoded.HadamardTester.implementation.vertices_compose number coins queries g

/-- Split a mathematical composed vertex into its owner index and local slot. -/
def composeOwner {E : Type} (index : E → ℕ) :
    ConstraintGraph.ComposePos ℕ E α ⊕ E × Rand α → ℕ × ComposeSlot α :=
  AssignmentTester.Implementation.composeOwner index

/-- The same explicit numbering on all mathematical proof positions and coin vertices. -/
def composeVertex {E : Type} (number : ComposeSlot α ≃ Fin width) (index : E → ℕ)
    (vertex : ConstraintGraph.ComposePos ℕ E α ⊕ E × Rand α) : ℕ :=
  AssignmentTester.Implementation.composeVertex number index vertex

omit [Fintype α] [DecidableEq α] in
/-- Distinct table positions and coin vertices retain distinct identifiers. -/
theorem composeVertex_injective {E : Type} (number : ComposeSlot α ≃ Fin width)
    {index : E → ℕ} (hindex : Function.Injective index) :
    Function.Injective (composeVertex number index) :=
  AssignmentTester.Implementation.composeVertex_injective number hindex

omit [Fintype α] [DecidableEq α] in
/-- The explicit endpoint selection agrees with `ConstraintGraph.testerPos`. -/
theorem composePosition_eq (number : ComposeSlot α ≃ Fin width)
    (g : Graph (α → α → Bool)) (e : Fin g.edges.length) (p : Pos α) :
    composePosition number e.val (g.edges.get e).src (g.edges.get e).dst p =
      composeVertex number Fin.val (.inl ((g.toGraph id).testerPos e p)) :=
  AssignmentTester.Implementation.composePosition_eq number g e p

omit [Fintype α] [DecidableEq α] in
/-- The dart enumeration includes exactly the valid old indices and listed coins/queries. -/
@[simp]
theorem mem_composeDarts_iff (coins : List (Rand α)) (queries : List Query)
    (g : Graph (α → α → Bool)) (p : (ℕ × Rand α) × Query) :
    p ∈ g.composeDarts coins queries ↔
      p.1.1 < g.edges.length ∧ p.1.2 ∈ coins ∧ p.2 ∈ queries :=
  AssignmentTester.Implementation.mem_composeDarts_iff coins queries g p

/-- Valid old endpoints give valid output endpoints, even for empty or incomplete coin lists. -/
theorem WellFormed.compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) {g : Graph (α → α → Bool)}
    (hg : g.WellFormed) : (g.compose number coins queries).WellFormed :=
  Encoded.HadamardTester.implementation.wellFormed_compose number coins queries hg

omit [Fintype α] [DecidableEq α] in
/-- Listing each coin and query once lists each composed dart once. -/
theorem nodup_composeDarts (coins : List (Rand α)) (queries : List Query)
    (g : Graph (α → α → Bool)) (hcoins : coins.Nodup) (hqueries : queries.Nodup) :
    (g.composeDarts coins queries).Nodup :=
  AssignmentTester.Implementation.nodup_composeDarts coins queries g hcoins hqueries

open Classical in
/-- Composition retains the ordered edge, coin and query occurrences, even when stored
edge values coincide. -/
noncomputable def composeEnumeration (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    List.Enumeration (g.compose number coins queries).edges
      (fun p : (Fin g.edges.length × Rand α) × Query =>
        composeEdge number (g.edgeAt (fun _ _ => false) p.1.1.val) p.1.1.val p.1.2 p.2) :=
  Encoded.HadamardTester.implementation.composeEnumeration number coins queries g hcoins hqueries
    hmemCoins hmemQueries

/-- Enumerating every coin and query once gives exactly the existing composed graph, with
the specified vertex numbering and the explicit output edge order. -/
theorem toGraph_compose (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    (g.compose number coins queries).toGraph composeEval =
      ((g.toGraph id).compose.map (composeVertex number Fin.val)).comap
        (g.composeEnumeration number coins queries hcoins hqueries
          hmemCoins hmemQueries).equiv :=
  Encoded.HadamardTester.implementation.toGraph_compose
    Encoded.HadamardTester.realizes_implementation number coins queries g hcoins hqueries
    hmemCoins hmemQueries

/-- Exact interpretation and injective numbering preserve the mathematical composition value. -/
theorem unsatVal_compose_eq (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.compose number coins queries).toGraph composeEval).unsatVal =
      (g.toGraph id).compose.unsatVal :=
  Encoded.HadamardTester.implementation.unsatVal_compose_eq
    Encoded.HadamardTester.realizes_implementation number coins queries g hcoins hqueries
    hmemCoins hmemQueries

/-- Full executable composition preserves satisfiability. -/
theorem satisfiable_compose_iff [Nonempty α] (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.compose number coins queries).toGraph composeEval).Satisfiable ↔
      (g.toGraph id).Satisfiable :=
  Encoded.HadamardTester.implementation.satisfiable_compose_iff
  Encoded.HadamardTester.realizes_implementation isComplete_assignmentTester
    sound_assignmentTester (by norm_num) number coins queries g hcoins hqueries hmemCoins
    hmemQueries

/-- Full executable composition retains at least the existing `1/476` fraction of the gap. -/
theorem le_unsatVal_compose [Nonempty α] (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    (g.toGraph id).unsatVal / 476 ≤
      ((g.compose number coins queries).toGraph composeEval).unsatVal := by
  have h := Encoded.HadamardTester.implementation.le_unsatVal_compose
    Encoded.HadamardTester.realizes_implementation sound_assignmentTester
    (by norm_num) number coins queries g hcoins hqueries hmemCoins hmemQueries
  norm_num only [card_query, Nat.cast_ofNat] at h
  exact h

/-- Tabulating the output constraints preserves the exact mathematical composition value. -/
theorem unsatVal_composeTabulated_eq (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.composeTabulated number coins queries).toGraph id).unsatVal =
      (g.toGraph id).compose.unsatVal :=
  Encoded.HadamardTester.implementation.unsatVal_composeTabulated_eq
    Encoded.HadamardTester.realizes_implementation number coins queries g hcoins hqueries
    hmemCoins hmemQueries

/-- Tabulated full composition preserves satisfiability. -/
theorem satisfiable_composeTabulated_iff [Nonempty α] (number : ComposeSlot α ≃ Fin width)
    (coins : List (Rand α)) (queries : List Query) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.composeTabulated number coins queries).toGraph id).Satisfiable ↔
      (g.toGraph id).Satisfiable :=
  Encoded.HadamardTester.implementation.satisfiable_composeTabulated_iff
  Encoded.HadamardTester.realizes_implementation isComplete_assignmentTester
    sound_assignmentTester (by norm_num) number coins queries g hcoins hqueries hmemCoins
    hmemQueries

end Graph

end Cslib.PCP.Encoded
