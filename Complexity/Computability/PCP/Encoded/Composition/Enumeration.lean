/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Composition
public import Complexity.Computability.PCP.Encoded.GenericComposition.Enumeration
public import Complexity.Computability.PCP.Encoded.AssignmentTester.Enumeration

/-!
# Complete enumeration for executable composition

Constructive finite enumerations supply the assignment tester's slot numbering, coins, and
queries. The alphabet is fixed; the graph remains runtime input. Composition preserves the
existing exact interpretation and charges all intermediate and output constraint tables.
The fixed enumerations and tables can be enormous; the certificate is asymptotic in graph size,
not a claim of practical runtime at arbitrary fixed alphabets.

## Main definitions

* `Cslib.PCP.Encoded.Graph.ComposeSlot.finEnum`: constructive slot numbering, used with the coin
  enumeration of `Complexity.Computability.PCP.Encoded.AssignmentTester.Enumeration`.
* `Cslib.PCP.Encoded.Graph.composeEnumerated`: tabulated composition with complete enumerations.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_composeEnumerated`: uniform construction from any fixed
  encoding of the input constraint tables.
* `Cslib.PCP.Encoded.Graph.unsatVal_composeEnumerated_eq`: exact mathematical composition value.
* `Cslib.PCP.Encoded.Graph.satisfiable_composeEnumerated_iff`: preservation of satisfiability.
* `Cslib.PCP.Encoded.Graph.le_unsatVal_composeEnumerated`: retention of a `1/476` fraction of value.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP

open Turing.MultiTapeTM Cslib.PCP.HadamardTester

attribute [local instance] HadamardTester.instFinEnumBool HadamardTester.Rand.finEnum

namespace Encoded.Graph

/-- Constructively number the input, proof, and coin slots of one assignment-tester block. -/
@[instance_reducible]
def ComposeSlot.finEnum (α : Type) [FinEnum α] : FinEnum (ComposeSlot α) :=
  inferInstanceAs (FinEnum (_ ⊕ (_ ⊕ _) ⊕ _))

attribute [local instance] ComposeSlot.finEnum

variable {α : Type} [FinEnum α]

/-- Apply every assignment-tester coin and query, then tabulate the output constraints. -/
def composeEnumerated (g : Graph (α → α → Bool)) :
    Graph ((Bool × (Query → Bool)) → (Bool × (Query → Bool)) → Bool) :=
  Encoded.HadamardTester.implementation.composeEnumerated g

/-- Compose a certified runtime graph, charging a conversion from its fixed constraint encoding
and every output table. The input need not use the implementation's finite enumeration. -/
@[fun_prop]
theorem isPolyTime_composeEnumerated {Input : Type} {input : Input ↪ List Bool}
    {constraintEncoding : (α → α → Bool) ↪ List Bool}
    {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableInPolyTime graph input (encoding constraintEncoding)) :
    ComputableInPolyTime (fun x => (graph x).composeEnumerated)
      input (encoding (encPi (encPi encBool))) :=
  Encoded.HadamardTester.implementation.isPolyTime_composeEnumerated hgraph

/-- The declared vertex count includes the complete input, proof, and coin slots. -/
@[simp]
theorem vertices_composeEnumerated (g : Graph (α → α → Bool)) :
    g.composeEnumerated.vertices =
      (g.vertices + g.edges.length) * Fintype.card (ComposeSlot α) := by
  simpa only [Fintype.card_eq_nat_card, composeEnumerated] using
    Encoded.HadamardTester.implementation.vertices_composeEnumerated g

/-- Each original edge contributes one edge per coin and query pair. -/
@[simp]
theorem length_edges_composeEnumerated (g : Graph (α → α → Bool)) :
    g.composeEnumerated.edges.length =
      g.edges.length * Fintype.card (Rand α) * Fintype.card Query := by
  simpa only [Fintype.card_eq_nat_card, composeEnumerated] using
    Encoded.HadamardTester.implementation.length_edges_composeEnumerated g

/-- Valid input endpoints give valid endpoints in the completely enumerated gadget graph. -/
theorem WellFormed.composeEnumerated {g : Graph (α → α → Bool)} (hg : g.WellFormed) :
    g.composeEnumerated.WellFormed :=
  Encoded.HadamardTester.implementation.wellFormed_composeEnumerated hg

/-- Complete constructive enumeration preserves the exact mathematical composition value. -/
theorem unsatVal_composeEnumerated_eq (g : Graph (α → α → Bool)) :
    (g.composeEnumerated.toGraph id).unsatVal = (g.toGraph id).compose.unsatVal :=
  Encoded.HadamardTester.implementation.unsatVal_composeEnumerated_eq
    Encoded.HadamardTester.realizes_implementation g

/-- Complete tabulated composition preserves satisfiability. -/
theorem satisfiable_composeEnumerated_iff [Nonempty α] (g : Graph (α → α → Bool)) :
    (g.composeEnumerated.toGraph id).Satisfiable ↔ (g.toGraph id).Satisfiable :=
  Encoded.HadamardTester.implementation.satisfiable_composeEnumerated_iff
    Encoded.HadamardTester.realizes_implementation isComplete_assignmentTester
    sound_assignmentTester (by norm_num) g

/-- Complete tabulated composition retains the tester's `1/476` fraction of the input value. -/
theorem le_unsatVal_composeEnumerated [Nonempty α] (g : Graph (α → α → Bool)) :
    (g.toGraph id).unsatVal / 476 ≤ (g.composeEnumerated.toGraph id).unsatVal := by
  rw [unsatVal_composeEnumerated_eq]
  exact ConstraintGraph.le_unsatVal_compose _

end Encoded.Graph

end Cslib.PCP
