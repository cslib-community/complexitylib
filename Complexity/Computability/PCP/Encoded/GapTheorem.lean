/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.ThreeSAT
public import Complexity.Computability.PCP.Encoded.SelectedComposition.Enumeration
public import Complexity.Computability.PCP.Encoded.Amplification.Arithmetic
public import Complexity.Logics.Propositional.CNF.ThreeCNF
import Complexity.Logics.Propositional.CNF.ThreeCNF.PolyTime
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# An executable constant-gap reduction from SAT

Split clauses to width three, compact variable names, construct the initial constraint graph,
normalize its alphabet by composition, and apply logarithmically many arithmetic amplification
rounds. Every stage is a functional program. The expander and all finite enumerations are fixed
constructively; the enormous fixed parameters make this an asymptotic construction.

The reduction accepts arbitrary CNF formulas and preserves satisfiability. Unsatisfiable inputs
produce graphs above the fixed positive gap, with all endpoints in the declared vertex range.

## Main definitions

* `Cslib.PCP.Encoded.gapGraph`: the complete functional SAT-to-gap-graph pipeline.

## Main results

* `Cslib.PCP.Encoded.satisfiable_gapGraph_iff`: completeness and qualitative soundness.
* `Cslib.PCP.Encoded.gap_le_unsatVal_gapGraph`: the fixed positive soundness gap.
* `Cslib.PCP.Encoded.isPolyTime_gapGraph`: a uniform certificate for the complete reduction.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [S. Arora, B. Barak, *Computational Complexity: A Modern Approach*, Chapter 22][AroraBarak09]
-/

@[expose] public section

namespace Cslib.PCP.Encoded

open Cslib.Logic.PL
open Turing.MultiTapeTM
open ConstraintGraph.Amplification.Arithmetic

attribute [local instance] Cslib.PCP.HadamardTester.instFinEnumBool

/-- Split, compact, normalize, and amplify a CNF formula using the concrete arithmetic family. -/
def gapGraph {V : Type} [DecidableEq V] (φ : CNF V) :
    Graph (SelectedAlphabet → SelectedAlphabet → Bool) :=
  (Graph.ofCompactCNF φ.to3CNF).composeSelectedEnumerated.arithmeticAmplify

/-- The whole reduction is polynomial-time in any efficiently computed input formula. Variable
names retain their supplied encoding until compaction, including sparse or repeated names. -/
@[fun_prop]
theorem isPolyTime_gapGraph {V Input : Type} [DecidableEq V]
    {enc : V ↪ List Bool} {input : Input ↪ List Bool} {formula : Input → CNF V}
    (hformula : ComputableInPolyTime formula input
      (encList (encList (encPair enc encBool)))) :
    ComputableInPolyTime (fun x => gapGraph (formula x)) input
      (Graph.encoding (encPi (encPi encBool))) := by
  unfold gapGraph
  apply Graph.isPolyTime_arithmeticAmplify
  · exact Graph.isPolyTime_composeSelectedEnumerated
      (Graph.isPolyTime_ofCompactCNF ((CNF.isPolyTime_to3CNF enc).comp hformula))
  · exact fun x => (Graph.wellFormed_ofCompactCNF (formula x).to3CNF).composeSelectedEnumerated

/-- Every output edge has endpoints in the declared finite vertex range. -/
theorem wellFormed_gapGraph {V : Type} [DecidableEq V] (φ : CNF V) :
    (gapGraph φ).WellFormed :=
  Graph.wellFormed_arithmeticAmplify
    (Graph.wellFormed_ofCompactCNF φ.to3CNF).composeSelectedEnumerated

/-- The complete construction preserves satisfiability for arbitrary clause lengths. -/
theorem satisfiable_gapGraph_iff {V : Type} [DecidableEq V] (φ : CNF V) :
    ((gapGraph φ).toGraph id).Satisfiable ↔ φ.Satisfiable := by
  rw [gapGraph, Graph.satisfiable_arithmeticAmplify_iff,
    Graph.satisfiable_composeSelectedEnumerated_iff, Graph.satisfiable_ofCompactCNF_iff,
    CNF.satisfiable_to3CNF]
  exact fun _ => CNF.length_le_three_of_mem_to3CNF

/-- Every unsatisfiable formula produces a graph above the fixed arithmetic gap. -/
theorem gap_le_unsatVal_gapGraph {V : Type} [DecidableEq V] (φ : CNF V)
    (hφ : ¬ φ.Satisfiable) :
    gap ≤ ((gapGraph φ).toGraph id).unsatVal := by
  apply Graph.gap_le_unsatVal_arithmeticAmplify
  intro h
  exact hφ ((satisfiable_gapGraph_iff φ).mp
    ((Graph.satisfiable_arithmeticAmplify_iff _).mpr h))

end Cslib.PCP.Encoded
