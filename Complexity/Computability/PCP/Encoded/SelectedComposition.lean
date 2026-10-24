/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.GenericComposition
public import Complexity.Computability.PCP.Encoded.SelectedAssignmentTester
public import Complexity.Computability.PCP.SelectedComposition

/-!
# Executable composition with the selected assignment tester

The six-query tester supplies an executable realization to the shared graph compiler. Slot
numbering, edge enumeration, interpretation, and resource accounting use the same implementation
as conjunction composition. Complete coin and query lists recover mathematical selected
composition; incomplete lists still give a well-formed graph when the input is well formed.

## Main definitions

* `Cslib.PCP.Encoded.SelectedHadamardTester.implementation`: executable queries and decisions.
* `Cslib.PCP.Encoded.Graph.composeSelectedTabulated`: composition with Boolean output tables.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_composeSelectedTabulated`: the full construction certificate.
* `Cslib.PCP.Encoded.Graph.unsatVal_composeSelectedTabulated_eq`: exact interpretation.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_composeSelectedTabulated`: the `1/840` gap bound.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Cslib.PCP.HadamardTester Turing.MultiTapeTM

variable {α : Type} [Fintype α] [DecidableEq α]

/-- The selected tester's query and acceptance algorithms, independent of its specification. -/
def SelectedHadamardTester.implementation :
    AssignmentTester.Implementation α (α → Bool) (LinPos α ⊕ QuadPos α)
      (Fin 5 × Rand α) (Fin 6) Bool where
  query := SelectedHadamardTester.query
  accepts := SelectedHadamardTester.accepts

/-- The executable algorithms realize the mathematical selected tester. -/
theorem SelectedHadamardTester.realizes_implementation :
    (implementation (α := α)).Realizes selectedAssignmentTester where
  query_eq := SelectedHadamardTester.query_eq
  accepts_eq_true := SelectedHadamardTester.accepts_eq_true

namespace Graph

/-- Input, auxiliary-proof, and selected-coin slots in a numbered composition block. -/
abbrev SelectedComposeSlot (α : Type) : Type :=
  AssignmentTester.ComposeSlot (α → Bool) (LinPos α ⊕ QuadPos α) (Fin 5 × Rand α)

variable {width : ℕ}

/-- Compile the selected tester and materialize the constraints over its 128-symbol alphabet. -/
def composeSelectedTabulated (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) (g : Graph (α → α → Bool)) :
    Graph (SelectedAlphabet → SelectedAlphabet → Bool) :=
  SelectedHadamardTester.implementation.composeTabulated number coins queries g

/-- The shared compiler charges the graph, every selected query, and the full output tables. -/
@[fun_prop]
theorem isPolyTime_composeSelectedTabulated {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableInPolyTime graph input (encoding (encPi (encPi encBool))))
    (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) :
    ComputableInPolyTime (fun x => (graph x).composeSelectedTabulated number coins queries)
      input (encoding (encPi (encPi encBool))) :=
  SelectedHadamardTester.implementation.isPolyTime_composeTabulated hgraph number coins queries

/-- The output reserves a fixed block for each old vertex and edge. -/
@[simp]
theorem vertices_composeSelectedTabulated (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) (g : Graph (α → α → Bool)) :
    (g.composeSelectedTabulated number coins queries).vertices =
      (g.vertices + g.edges.length) * width := rfl

/-- Every listed coin and query contributes one occurrence for each old edge. -/
@[simp]
theorem length_edges_composeSelectedTabulated (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) (g : Graph (α → α → Bool)) :
    (g.composeSelectedTabulated number coins queries).edges.length =
      g.edges.length * coins.length * queries.length := by
  simp only [composeSelectedTabulated, AssignmentTester.Implementation.composeTabulated,
    length_edges_mapConstraints, AssignmentTester.Implementation.length_edges_compose]

/-- Selected composition preserves endpoint bounds for arbitrary supplied coin and query lists. -/
theorem WellFormed.composeSelectedTabulated (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) {g : Graph (α → α → Bool)}
    (hg : g.WellFormed) : (g.composeSelectedTabulated number coins queries).WellFormed :=
  (wellFormed_mapConstraints_iff _ _).mpr
    (SelectedHadamardTester.implementation.wellFormed_compose number coins queries hg)

/-- Complete enumeration gives exactly the value of mathematical selected composition. -/
theorem unsatVal_composeSelectedTabulated_eq (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.composeSelectedTabulated number coins queries).toGraph id).unsatVal =
      (g.toGraph id).composeSelected.unsatVal :=
  SelectedHadamardTester.implementation.unsatVal_composeTabulated_eq
    SelectedHadamardTester.realizes_implementation number coins queries g
    hcoins hqueries hmemCoins hmemQueries

/-- Complete selected composition preserves satisfiability. -/
theorem satisfiable_composeSelectedTabulated_iff [Nonempty α]
    (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    ((g.composeSelectedTabulated number coins queries).toGraph id).Satisfiable ↔
      (g.toGraph id).Satisfiable :=
  SelectedHadamardTester.implementation.satisfiable_composeTabulated_iff
    SelectedHadamardTester.realizes_implementation
    isComplete_selectedAssignmentTester sound_selectedAssignmentTester (by norm_num)
    number coins queries g hcoins hqueries hmemCoins hmemQueries

/-- The six-query gadget retains at least `1/840` of the input's unsatisfied fraction. -/
theorem le_unsatVal_composeSelectedTabulated [Nonempty α]
    (number : SelectedComposeSlot α ≃ Fin width)
    (coins : List (Fin 5 × Rand α)) (queries : List (Fin 6)) (g : Graph (α → α → Bool))
    (hcoins : coins.Nodup) (hqueries : queries.Nodup)
    (hmemCoins : ∀ ω, ω ∈ coins) (hmemQueries : ∀ i, i ∈ queries) :
    (g.toGraph id).unsatVal / 840 ≤
      ((g.composeSelectedTabulated number coins queries).toGraph id).unsatVal := by
  rw [unsatVal_composeSelectedTabulated_eq number coins queries g
    hcoins hqueries hmemCoins hmemQueries]
  exact ConstraintGraph.le_unsatVal_composeSelected _

end Graph

end Cslib.PCP.Encoded
