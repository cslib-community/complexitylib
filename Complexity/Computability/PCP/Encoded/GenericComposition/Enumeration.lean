/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.GenericComposition
public import Mathlib.Data.FinEnum

/-!
# Complete enumeration for executable assignment testers

Constructive finite enumerations supply a tester implementation's slot numbering, coins, and
queries. The compiler charges all materialized constraint tables and retains edge occurrences.
The alphabets and enumerations are fixed; polynomial time is uniform in the input graph.

## Main definitions

* `Cslib.PCP.AssignmentTester.Implementation.composeEnumerated`: fully enumerated composition.

## Main results

* `Cslib.PCP.AssignmentTester.Implementation.isPolyTime_composeEnumerated`: compositional
  certification from any fixed input-constraint encoding.
* `Cslib.PCP.AssignmentTester.Implementation.unsatVal_composeEnumerated_eq`: exact interpretation.
* `Cslib.PCP.AssignmentTester.Implementation.satisfiable_composeEnumerated_iff`: satisfiability
  transfer under the tester's completeness and soundness contracts.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.AssignmentTester.Implementation

open Encoded Encoded.Graph Turing.MultiTapeTM

variable {α I P R Q Γ : Type} [FinEnum I] [FinEnum P] [FinEnum R]
  [FinEnum Q] [BEq Γ] (impl : Implementation α I P R Q Γ)

/-- Apply every coin and query, then tabulate the output constraints over the answer alphabet. -/
def composeEnumerated (g : Graph (α → α → Bool)) :
    Graph ((Γ × (Q → Γ)) → (Γ × (Q → Γ)) → Bool) :=
  impl.composeTabulated FinEnum.equiv (FinEnum.toList R) (FinEnum.toList Q) g

/-- Charge the input-encoding conversion and every output table in completely enumerated
composition. Input graphs need not use the implementation's own finite encoding. -/
@[fun_prop]
theorem isPolyTime_composeEnumerated [Finite α] [Fintype Γ]
    {Input : Type} {input : Input ↪ List Bool}
    {constraintEncoding : (α → α → Bool) ↪ List Bool}
    {graph : Input → Graph (α → α → Bool)}
    (hgraph : ComputableInPolyTime graph input (encoding constraintEncoding)) :
    ComputableInPolyTime (fun x => impl.composeEnumerated (graph x))
      input (encoding (encPi (encPi encBool))) := by
  let := Fintype.ofFinite α
  have hconvert : ComputableInPolyTime (id : (α → α → Bool) → _)
      constraintEncoding (encPi (encPi encBool)) := .of_finite _
  simpa only [composeEnumerated, mapConstraints_id] using
    impl.isPolyTime_composeTabulated (isPolyTime_mapConstraints hgraph hconvert)
      FinEnum.equiv (FinEnum.toList R) (FinEnum.toList Q)

/-- Every old vertex and edge receives one complete local slot block. -/
@[simp]
theorem vertices_composeEnumerated (g : Graph (α → α → Bool)) :
    (impl.composeEnumerated g).vertices =
      (g.vertices + g.edges.length) * Fintype.card (ComposeSlot I P R) := by
  simp only [composeEnumerated, composeTabulated, vertices_mapConstraints, vertices_compose,
    FinEnum.card_eq_fintypeCard]

/-- Every old edge occurrence contributes one edge per coin and query pair. -/
@[simp]
theorem length_edges_composeEnumerated (g : Graph (α → α → Bool)) :
    (impl.composeEnumerated g).edges.length =
      g.edges.length * Fintype.card R * Fintype.card Q := by
  simp only [composeEnumerated, composeTabulated, length_edges_mapConstraints, length_edges_compose,
    FinEnum.toList, List.length_map, List.length_finRange, FinEnum.card_eq_fintypeCard]

/-- Complete enumeration preserves endpoint bounds. -/
theorem wellFormed_composeEnumerated {g : Graph (α → α → Bool)} (hg : g.WellFormed) :
    (impl.composeEnumerated g).WellFormed :=
  (wellFormed_mapConstraints_iff _ _).mpr
    (impl.wellFormed_compose FinEnum.equiv (FinEnum.toList R) (FinEnum.toList Q) hg)

variable {T : AssignmentTester α I P R Q Γ} (hreal : impl.Realizes T)
  [Fintype R] [Fintype Q] [LawfulBEq Γ] [Nonempty R] [Nonempty Γ]

include hreal

/-- Complete enumeration preserves the exact value of the realized mathematical composition. -/
theorem unsatVal_composeEnumerated_eq (g : Graph (α → α → Bool)) :
    ((impl.composeEnumerated g).toGraph id).unsatVal = (T.compose (g.toGraph id)).unsatVal :=
  impl.unsatVal_composeTabulated_eq hreal
    FinEnum.equiv (FinEnum.toList R) (FinEnum.toList Q) g
    FinEnum.nodup_toList FinEnum.nodup_toList FinEnum.mem_toList FinEnum.mem_toList

omit [Fintype Q] in
/-- Completeness and positive decoder soundness transfer satisfiability through the compiler. -/
theorem satisfiable_composeEnumerated_iff [Nonempty α] [Nonempty Q]
    (hcomplete : T.IsComplete) {decode : (I → Γ) → α} {δ : ℝ}
    (hsound : T.Sound decode δ) (hδ : 0 < δ) (g : Graph (α → α → Bool)) :
    ((impl.composeEnumerated g).toGraph id).Satisfiable ↔ (g.toGraph id).Satisfiable :=
  impl.satisfiable_composeTabulated_iff hreal hcomplete hsound hδ
    FinEnum.equiv (FinEnum.toList R) (FinEnum.toList Q) g
    FinEnum.nodup_toList FinEnum.nodup_toList FinEnum.mem_toList FinEnum.mem_toList

/-- Complete compilation retains the soundness loss of the supplied tester. -/
theorem le_unsatVal_composeEnumerated [Nonempty Q]
    {decode : (I → Γ) → α} {δ : ℝ} (hsound : T.Sound decode δ) (hδ : 0 < δ)
    (g : Graph (α → α → Bool)) :
    (g.toGraph id).unsatVal / (Fintype.card Q / δ) ≤
      ((impl.composeEnumerated g).toGraph id).unsatVal := by
  rw [impl.unsatVal_composeEnumerated_eq hreal]
  exact T.le_unsatVal_compose hsound hδ _

end Cslib.PCP.AssignmentTester.Implementation
