/-
Copyright (c) 2026 Bolton Bailey, Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bolton Bailey, Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Encoded.Amplification.Iteration
public import Complexity.Computability.PCP.Encoded.SelectedComposition.Enumeration
public import Complexity.Computability.PCP.Amplification.Arithmetic
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.TowerTable.Family
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Family
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# A concrete executable gap amplifier

Use the certified arithmetic expander, complete constructive enumerations, and fixed numerical
parameters to iterate the normalized amplification round. The program has no unimplemented
expander or enumeration premise. Its asymptotic polynomial-time certificate charges the complete
encoded tables, while its enormous fixed parameters prevent practical execution.

## Main definitions

* `Cslib.PCP.Encoded.Graph.arithmeticAmplify`: logarithmically many concrete amplification rounds.

## Main results

* `Cslib.PCP.Encoded.Graph.isPolyTime_arithmeticAmplify`: the complete construction certificate.
* `Cslib.PCP.Encoded.Graph.satisfiable_arithmeticAmplify_iff`: preservation of satisfiability.
* `Cslib.PCP.Encoded.Graph.gap_le_unsatVal_arithmeticAmplify`: an unconditional fixed soundness gap.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
* [O. Reingold, S. Vadhan, A. Wigderson, *Entropy waves, the zig-zag graph product, and new
  constant-degree expanders*][ReingoldVadhanWigderson2002]
-/

@[expose] public section

namespace Cslib.PCP.Encoded.Graph

open Cslib.PCP.HadamardTester Turing.MultiTapeTM
open ConstraintGraph.Amplification.Arithmetic

local notation "Constraint" => (SelectedAlphabet → SelectedAlphabet → Bool)
local notation "Label" => RotationMap.AffinePlaneFamilyLabel (ZMod 257) 257

/-- Concrete enumeration of the arithmetic expander's fixed field. -/
local instance instFinEnumZMod257 : FinEnum (ZMod 257) :=
  FinEnum.ofEquiv (Fin 257) (ZMod.finEquiv 257).toEquiv.symm

attribute [local instance] HadamardTester.instFinEnumBool
  Cslib.PCP.HadamardTester.Rand.finEnum SelectedComposeSlot.finEnum

/-- Complete normalized rounds with fixed arithmetic expanders and fixed numerical parameters. -/
@[irreducible]
def arithmeticAmplify (g : Graph Constraint) : Graph Constraint :=
  amplifyIter (fun _ _ => true) RotationMap.arithmeticExpanderRotate walkLength killRate
    (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    (Nat.clog 2 g.edges.length) g

/-- The concrete amplifier is polynomial-time in any efficiently computed well-formed input. -/
@[fun_prop]
theorem isPolyTime_arithmeticAmplify {Input : Type} {input : Input ↪ List Bool}
    {graph : Input → Graph Constraint}
    (hgraph : ComputableInPolyTime graph input (encoding (encPi (encPi encBool))))
    (hwellFormed : ∀ x, (graph x).WellFormed) :
    ComputableInPolyTime (fun x => arithmeticAmplify (graph x))
      input (encoding (encPi (encPi encBool))) := by
  have hgraph := hgraph.tidy
  refine .of_tidy ?_
  have hcost := RotationMap.polytime_arithmeticExpanderRotate (encFinEnum Label)
  unfold arithmeticAmplify
  exact (isPolyTime_amplifyIter_clog (.of_tidy hgraph) hwellFormed RotationMap.arithmeticExpander
    RotationMap.arithmeticExpanderRotate RotationMap.arithmeticExpanderRotate_eq (.of_tidy hcost)
    (fun _ _ => true) walkLength killRate (FinEnum.toList _) FinEnum.equiv
    (FinEnum.toList _) (FinEnum.toList _)).tidy

/-- Valid endpoint indices are preserved, including when the program performs no rounds. -/
theorem wellFormed_arithmeticAmplify {g : Graph Constraint} (hg : g.WellFormed) :
    g.arithmeticAmplify.WellFormed := by
  unfold arithmeticAmplify amplifyIter
  cases Nat.clog 2 g.edges.length with
  | zero => exact hg
  | succ k =>
    rw [Function.iterate_succ_apply']
    exact wellFormed_amplify _ id (fun _ _ => true) RotationMap.arithmeticExpander
      RotationMap.arithmeticExpanderRotate RotationMap.arithmeticExpanderRotate_eq
      walkLength killRate (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)

/-- The fully specified arithmetic construction preserves satisfiability. -/
theorem satisfiable_arithmeticAmplify_iff (g : Graph Constraint) :
    (g.arithmeticAmplify.toGraph id).Satisfiable ↔ (g.toGraph id).Satisfiable := by
  unfold arithmeticAmplify
  exact satisfiable_amplifyIter_iff (fun _ _ => true) RotationMap.arithmeticExpander
    RotationMap.arithmeticExpanderRotate RotationMap.arithmeticExpanderRotate_eq
    walkLength killRate (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList FinEnum.nodup_toList FinEnum.nodup_toList
    FinEnum.mem_toList FinEnum.mem_toList _ RotationMap.spectralExpansion_arithmeticExpander_le
    (by norm_num) one_le_walkLength two_le_killRate _ g

/-- Every unsatisfiable graph reaches the fixed positive gap after logarithmically many rounds. -/
theorem gap_le_unsatVal_arithmeticAmplify {g : Graph Constraint}
    (hunsat : ¬ (g.toGraph id).Satisfiable) :
    gap ≤ (g.arithmeticAmplify.toGraph id).unsatVal := by
  unfold arithmeticAmplify
  exact gap_le_unsatVal_amplifyIter_clog (fun _ _ => true) RotationMap.arithmeticExpander
    RotationMap.arithmeticExpanderRotate RotationMap.arithmeticExpanderRotate_eq
    walkLength killRate (FinEnum.toList _) FinEnum.equiv (FinEnum.toList _) (FinEnum.toList _)
    FinEnum.nodup_toList FinEnum.mem_toList FinEnum.nodup_toList FinEnum.nodup_toList
    FinEnum.mem_toList FinEnum.mem_toList _ RotationMap.spectralExpansion_arithmeticExpander_le
    (by norm_num) two_le_killRate walkLength_eq gap_pos.le gap_le_one gain hunsat

end Cslib.PCP.Encoded.Graph
