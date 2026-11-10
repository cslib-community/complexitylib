/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import CslibFrontier.Computability.PCP.Encoded.AssignmentTester.Enumeration
public import CslibFrontier.Computability.PCP.Encoded.GenericComposition.Enumeration
public import CslibFrontier.Computability.PCP.Encoded.SelectedAssignmentTester
public import CslibFrontier.Computability.PCP.SelectedComposition

/-!
# Executable composition with the selected assignment tester

The six-query tester supplies an executable realization to the shared graph compiler
(`Cslib.PCP.AssignmentTester.Implementation`). Composition runs every coin, a choice of one of five
checks with the Hadamard product coins, and all six queries, enumerated constructively; the
enumerations are fixed with the alphabet, while the graph and its output tables remain charged
runtime data. The result is mathematical selected composition, up to an injective numbering.

## Main definitions

* `Cslib.PCP.Encoded.SelectedHadamardTester.implementation`: executable queries and decisions.
* `Cslib.PCP.Encoded.Graph.composeSelectedEnumerated`: complete selected composition, with
  Boolean output tables.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_composeSelectedEnumerated`: the construction certificate.
* `Cslib.PCP.Encoded.Graph.satisfiable_composeSelectedEnumerated_iff`: satisfiability transfer.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_composeSelectedEnumerated`: retention of `1/840` of value.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Cslib.PCP.HadamardTester Turing.MultiTapeTM

section Implementation

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

end Implementation

namespace Graph

/-- Input, auxiliary-proof, and selected-coin slots in a numbered composition block. -/
abbrev SelectedComposeSlot (α : Type) : Type :=
  AssignmentTester.ComposeSlot (α → Bool) (LinPos α ⊕ QuadPos α) (Fin 5 × Rand α)

section Enumerated

attribute [local instance] HadamardTester.instFinEnumBool HadamardTester.Rand.finEnum

/-- Constructively number all input, proof, and selected-coin slots. -/
@[instance_reducible]
def SelectedComposeSlot.finEnum (α : Type) [FinEnum α] : FinEnum (SelectedComposeSlot α) :=
  inferInstanceAs (FinEnum (_ ⊕ (_ ⊕ _) ⊕ (_ × _)))

attribute [local instance] SelectedComposeSlot.finEnum

variable {α : Type} [FinEnum α]

/-- Run every selected check and query, then materialize the output constraints. -/
def composeSelectedEnumerated (g : Graph (α → α → Bool)) :
    Graph (SelectedAlphabet → SelectedAlphabet → Bool) :=
  SelectedHadamardTester.implementation.composeEnumerated g

/-- Selected composition accepts any certified input-constraint encoding. -/
@[fun_prop]
theorem isPolyTime_composeSelectedEnumerated {Input : Type} {input : Input ↪ List Bool}
    {constraintEncoding : (α → α → Bool) ↪ List Bool}
    {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableInPolyTime graph input (encoding constraintEncoding)) :
    ComputableInPolyTime (fun x => (graph x).composeSelectedEnumerated)
      input (encoding encConstraintTable) :=
  SelectedHadamardTester.implementation.isPolyTime_composeEnumerated hgraph

/-- Each old vertex and edge reserves a complete local slot block. -/
@[simp]
theorem vertices_composeSelectedEnumerated (g : Graph (α → α → Bool)) :
    g.composeSelectedEnumerated.vertices =
      (g.vertices + g.edges.length) * Fintype.card (SelectedComposeSlot α) := by
  simpa only [composeSelectedEnumerated, Fintype.card_eq_nat_card] using
    SelectedHadamardTester.implementation.vertices_composeEnumerated g

/-- Each old edge occurs once for every selected coin and query pair. -/
@[simp]
theorem length_edges_composeSelectedEnumerated (g : Graph (α → α → Bool)) :
    g.composeSelectedEnumerated.edges.length =
      g.edges.length * Fintype.card (Fin 5 × Rand α) * 6 := by
  simpa only [composeSelectedEnumerated, Fintype.card_eq_nat_card, Nat.card_fin] using
    SelectedHadamardTester.implementation.length_edges_composeEnumerated g

/-- Complete selected composition preserves endpoint bounds. -/
theorem WellFormed.composeSelectedEnumerated {g : Graph (α → α → Bool)} (hg : g.WellFormed) :
    g.composeSelectedEnumerated.WellFormed :=
  SelectedHadamardTester.implementation.wellFormed_composeEnumerated hg

/-- Complete enumeration realizes the exact selected-composition value. -/
private theorem unsatVal_composeSelectedEnumerated_eq (g : Graph (α → α → Bool)) :
    (g.composeSelectedEnumerated.toGraph id).unsatVal = (g.toGraph id).composeSelected.unsatVal :=
  SelectedHadamardTester.implementation.unsatVal_composeEnumerated_eq
    SelectedHadamardTester.realizes_implementation g

/-- Complete selected composition preserves satisfiability. -/
theorem satisfiable_composeSelectedEnumerated_iff [Nonempty α] (g : Graph (α → α → Bool)) :
    (g.composeSelectedEnumerated.toGraph id).Satisfiable ↔ (g.toGraph id).Satisfiable :=
  SelectedHadamardTester.implementation.satisfiable_composeEnumerated_iff
    SelectedHadamardTester.realizes_implementation
    isComplete_selectedAssignmentTester sound_selectedAssignmentTester (by norm_num) g

/-- The compiled selected tester retains `1/840` of the input value. -/
theorem le_unsatVal_composeSelectedEnumerated [Nonempty α] (g : Graph (α → α → Bool)) :
    (g.toGraph id).unsatVal / 840 ≤ (g.composeSelectedEnumerated.toGraph id).unsatVal := by
  rw [unsatVal_composeSelectedEnumerated_eq]
  exact ConstraintGraph.le_unsatVal_composeSelected _

end Enumerated

end Graph

end Cslib.PCP.Encoded
