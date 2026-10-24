/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.SelectedComposition
public import Complexity.Computability.PCP.Encoded.GenericComposition.Enumeration
public import Complexity.Computability.PCP.Encoded.AssignmentTester.Enumeration

/-!
# Complete enumeration for selected composition

The selected tester uses the shared complete-enumeration compiler. Its coins add a choice of one
of five checks to the Hadamard product coins, and its queries are indexed by `Fin 6`. All finite
enumerations are fixed with the alphabet; the graph and its tables remain charged runtime data.

## Main definitions

* `Cslib.PCP.Encoded.Graph.composeSelectedEnumerated`: complete selected composition.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_composeSelectedEnumerated`: the construction certificate.
* `Cslib.PCP.Encoded.Graph.satisfiable_composeSelectedEnumerated_iff`: satisfiability transfer.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_composeSelectedEnumerated`: retention of `1/840` of value.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Turing.MultiTapeTM Cslib.PCP.HadamardTester

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
      input (encoding (encPi (encPi encBool))) :=
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

end Cslib.PCP.Encoded.Graph
