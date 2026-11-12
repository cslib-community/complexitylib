/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.Complexity.Problems.ChromaticNumber
public import CslibFrontier.Computability.Complexity.Problems.Clique
import CslibFrontier.Computability.Complexity.Classes.NP.Witness
import CslibFrontier.Foundations.Combinatorics.SimpleGraph.CliqueCover

/-!
# Clique cover

`CliqueCover` is Karp's problem CLIQUE COVER [Karp1972]: given a graph `G` and a number `l`, the
declared vertices of `G` are the union of at most `l` cliques of the graph induced on them
(`Cslib.Complexity.Graph.CoveredByCliques`). Instances (`Cslib.Complexity.CliqueCoverInstance`)
are encoded by `Cslib.Complexity.encCliqueCover`, as for `Cslib.Complexity.ChromaticNumber`.

The cliques of a cover may be taken to be the color classes of a coloring of the complement
(`SimpleGraph.exists_cliqueCover_iff_colorable_compl`), so complementing the graph on its declared
vertices (`Cslib.Complexity.Graph.compl`) reduces `CliqueCover` and `ChromaticNumber` to each
other. Karp's reduction from CHROMATIC NUMBER maps `⟨G, k⟩` to the complement of `G` with `k`
cliques (`Cslib.Complexity.Graph.compl_mem_CliqueCover_iff`); the converse reduction gives `NP`
membership.

## Main definitions

* `Cslib.Complexity.CliqueCoverInstance`: instance `(graph, cliques)` of Clique Cover.
* `Cslib.Complexity.encCliqueCover`: polynomial-time encoding of `CliqueCoverInstance`.
* `Cslib.Complexity.Graph.CoveredByCliques`: covers of the declared vertices by cliques.
* `Cslib.Complexity.CliqueCover`: graphs with a number of cliques that suffices.

## Main results

* `Cslib.Complexity.Graph.mem_CliqueCover_iff_compl`: a cover by `l` cliques is an `l`-coloring
  of the complement.
* `Cslib.Complexity.Graph.compl_mem_CliqueCover_iff`: correctness of Karp's reduction.
* `Cslib.Complexity.polyTimeReducible_ChromaticNumber_CliqueCover`,
  `Cslib.Complexity.polyTimeReducible_CliqueCover_ChromaticNumber`: the two reductions.
* `Cslib.Complexity.CliqueCover.mem_NP`, `Cslib.Complexity.CliqueCover_npHard`,
  `Cslib.Complexity.CliqueCover_npComplete`: `CliqueCover` is `NP`-complete.

## References

* [R. M. Karp, *Reducibility among combinatorial problems*][Karp1972]
-/

public section

namespace Cslib.Complexity

open Turing.MultiTapeTM

/-- An instance `(graph, cliques)` of **Clique Cover**. -/
@[ext]
structure CliqueCoverInstance where
  /-- The graph whose declared vertices are to be covered. -/
  graph : Graph
  /-- The maximum number of cliques allowed in the cover. -/
  cliques : ℕ
  deriving DecidableEq, Repr, Inhabited

/-- Encoding of `CliqueCoverInstance` as a pair `(graph, cliques)`. -/
enc_structure encCliqueCover : CliqueCoverInstance where
  graph : encGraph,
  cliques : encNat

attribute [fun_prop] encCliqueCover_graph_polyTime encCliqueCover_cliques_polyTime
  encCliqueCover_mk_polyTime

/-- The declared vertices of `G` are the union of at most `l` cliques of the graph induced on
them. -/
@[expose]
def Graph.CoveredByCliques (G : Graph) (l : ℕ) : Prop :=
  ∃ S : Finset (Finset {v // v ∈ G.vertices}), S.card ≤ l ∧
    (∀ s ∈ S, G.induced.IsClique (s : Set {v // v ∈ G.vertices})) ∧ ∀ v, ∃ s ∈ S, v ∈ s

/-- **Clique cover** [Karp1972]: the graphs whose declared vertices are the union of at most the
given number of cliques. -/
@[expose]
def CliqueCover : Set CliqueCoverInstance := {x | x.graph.CoveredByCliques x.cliques}

/-- Membership in `CliqueCover` unfolds to `Graph.CoveredByCliques`. -/
@[simp]
theorem mem_CliqueCover_iff {G : Graph} {l : ℕ} :
    (⟨G, l⟩ : CliqueCoverInstance) ∈ CliqueCover ↔ G.CoveredByCliques l :=
  Iff.rfl

/-- A graph has a cover by `l` cliques exactly when its complement is `l`-colorable. -/
theorem Graph.mem_CliqueCover_iff_compl {G : Graph} {l : ℕ} :
    (⟨G, l⟩ : CliqueCoverInstance) ∈ CliqueCover ↔
      (⟨G.compl, l⟩ : ChromaticNumberInstance) ∈ ChromaticNumber := by
  change G.CoveredByCliques l ↔ G.compl.induced.Colorable l
  rw [Graph.induced_compl]
  exact SimpleGraph.exists_cliqueCover_iff_colorable_compl

/-- **Karp's reduction from `ChromaticNumber`.** A graph is `k`-colorable exactly when its
complement is covered by `k` cliques. -/
theorem Graph.compl_mem_CliqueCover_iff {G : Graph} {k : ℕ} :
    (⟨G.compl, k⟩ : CliqueCoverInstance) ∈ CliqueCover ↔
      (⟨G, k⟩ : ChromaticNumberInstance) ∈ ChromaticNumber := by
  change G.compl.CoveredByCliques k ↔ G.induced.Colorable k
  unfold Graph.CoveredByCliques
  rw [SimpleGraph.exists_cliqueCover_iff_colorable_compl, Graph.induced_compl]
  exact iff_of_eq (congrArg (fun H => SimpleGraph.Colorable H k) (compl_compl G.induced))

/-- `ChromaticNumber` reduces to `CliqueCover` in polynomial time by complementing the graph
[Karp1972]. -/
theorem polyTimeReducible_ChromaticNumber_CliqueCover :
    PolyTimeReducible encChromaticNumber encCliqueCover ChromaticNumber CliqueCover :=
  ⟨fun x => ⟨x.graph.compl, x.colors⟩, by fun_prop, fun _ => Graph.compl_mem_CliqueCover_iff.symm⟩

/-- `CliqueCover` reduces to `ChromaticNumber` in polynomial time by complementing the graph. -/
theorem polyTimeReducible_CliqueCover_ChromaticNumber :
    PolyTimeReducible encCliqueCover encChromaticNumber CliqueCover ChromaticNumber :=
  ⟨fun x => ⟨x.graph.compl, x.cliques⟩, by fun_prop, fun _ => Graph.mem_CliqueCover_iff_compl⟩

/-- `CliqueCover` belongs to `NP`. -/
theorem CliqueCover.mem_NP : CliqueCover ∈ NP encCliqueCover :=
  polyTimeReducible_CliqueCover_ChromaticNumber.mem_NP ChromaticNumber.mem_NP

/-- `CliqueCover` is `NP`-hard. -/
theorem CliqueCover_npHard : NPHard encCliqueCover CliqueCover :=
  ChromaticNumber_npHard.trans polyTimeReducible_ChromaticNumber_CliqueCover

/-- **Clique cover is NP-complete**, with the number of cliques in binary [Karp1972]. -/
theorem CliqueCover_npComplete : NPComplete encCliqueCover CliqueCover :=
  ⟨CliqueCover.mem_NP, CliqueCover_npHard⟩

end Cslib.Complexity
