/-
Copyright (c) 2026 Samuel Schlesinger. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Samuel Schlesinger
-/

module
-- upstream: candidate

public import Complexity.Computability.PCP.Power.WithInput
public import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.RotationMap.Walk
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Encodings.Finite
import Complexity.Computability.Machines.Turing.MultiTape.Complexity.PolyTime.Plain

/-!
# Polynomial-time evaluation of powered constraints

The walk length, killing rate and finite edge-label type are fixed. The graph, starting vertex,
and both endpoint opinion tables are runtime data; their encodings are charged in full. This is
not a certificate uniform in varying walk lengths, killing rates or alphabet encodings.

## Main results

* `Cslib.PCP.RegularConstraintGraph.isPolyTime_powerRelationWithInput`: joint evaluation cost.

## References

* [I. Dinur, *The PCP theorem by gap amplification*][Dinur2007]
-/

@[expose] public section

namespace Cslib.PCP.RegularConstraintGraph

open Turing.MultiTapeTM ComputableInPolyTime RotationMap

variable {P W D α : Type}
  {input : P ↪ List Bool} {vertex : W ↪ List Bool}
  {label : D ↪ List Bool} {alphabet : α ↪ List Bool}
  {rotate : P × (W × D) → W × D} {rel : P × ((W × D) × (α × α)) → Bool}

variable [Fintype D]

/-- The runtime graph, vertex, complete walk and both opinion tables are all stored explicitly. -/
noncomputable def powerInputEncoding (input : P ↪ List Bool) (vertex : W ↪ List Bool)
    (label : D ↪ List Bool) (alphabet : α ↪ List Bool) (T q : ℕ)
    (signal : Fin q ↪ List Bool) : PowerInput P W D α T q ↪ List Bool :=
  encPair input (encPair (encPair vertex (encPair (encPi label) (encPi signal)))
    (encPair (encPi alphabet) (encPi alphabet)))

/-- Every original relation call, intermediate walk vertex, reverse-label table and opinion
lookup is charged. The finite dispatch depends only on the fixed walk parameters. -/
@[fun_prop]
theorem isPolyTime_powerRelationWithInput
    (hrotate : ComputableInPolyTime rotate
      (encPair input (encPair vertex label)) (encPair vertex label))
    (hrel : ComputableInPolyTime rel
      (encPair input (encPair (encPair vertex label) (encPair alphabet alphabet))) encBool)
    (T q : ℕ) [NeZero q] (signal : Fin q ↪ List Bool) :
    ComputableInPolyTime (powerRelationWithInput rotate rel T q)
      (powerInputEncoding input vertex label alphabet T q signal) encBool := by
  let enc := powerInputEncoding input vertex label alphabet T q signal
  have hbranch (s : (Fin T → D) × (Fin T → Fin q)) : ComputableInPolyTime
      (fun p : PowerInput P W D α T q =>
        powerRelationWithInput rotate rel T q (p.1, (p.2.1.1, s), p.2.2)) enc encBool := by
    have hreturned : ComputableInPolyTime
        (fun p : PowerInput P W D α T q => killedPowRotWithInput rotate T q (p.1, p.2.1.1, s))
        enc (encPair vertex (encPair (encPi label) (encPi signal))) :=
      (ComputableInPolyTime.rotationMap_killedPowRotWithInput hrotate T q signal).comp
        ((fst _ _).prod (((snd _ _).fst'.fst').prod (const s)))
    let check (p : PowerInput P W D α T q) (i : Fin T) : Bool :=
      if i.val < killTime s.2 then
        rel (p.1, (walkAtWithInput rotate (p.1, p.2.1.1, s.1) i.val, s.1 i),
          p.2.2.1 (.take i.val i.isLt.le s.1),
          p.2.2.2 (.take (killTime s.2 - (i.val + 1)) ((Nat.sub_le _ _).trans (killTime_le _))
            (killedPowRotWithInput rotate T q (p.1, p.2.1.1, s)).2.1))
      else true
    have hcheck (i : Fin T) : ComputableInPolyTime (fun p => check p i) enc encBool := by
      by_cases hi : i.val < killTime s.2
      · have hwalk : ComputableInPolyTime
            (fun p : PowerInput P W D α T q => walkAtWithInput rotate (p.1, p.2.1.1, s.1) i.val)
            enc vertex := (ComputableInPolyTime.rotationMap_walkAtWithInput hrotate T i.val).comp
          ((fst _ _).prod (((snd _ _).fst'.fst').prod (const s.1)))
        have hleft : ComputableInPolyTime
            (fun p : PowerInput P W D α T q => p.2.2.1 (.take i.val i.isLt.le s.1))
            enc alphabet := (pi_apply alphabet _).comp ((snd _ _).snd'.fst')
        have hprefix : ComputableInPolyTime
            (fun k : Fin T → D => WalkLabels.take (killTime s.2 - (i.val + 1))
              ((Nat.sub_le _ _).trans (killTime_le _)) k)
            (encPi label) (encFinite (WalkLabels D T)) := .of_finite _
        have hright := ((snd _ _).snd'.snd').pi_apply' (hprefix.comp hreturned.snd'.fst')
        simpa only [check, ite_eq_left hi, Function.comp_def, enc, powerInputEncoding] using
          hrel.comp ((fst _ _).prod ((hwalk.prod (const (s.1 i))).prod (hleft.prod hright)))
      · simpa only [check, ite_eq_right hi] using (const (encIn := enc) true)
    exact allWithInput (encA := encFinEnum (Fin T)) (const (List.finRange T))
      ((snd _ _).finite_cases fun i => (hcheck i).comp (fst _ _))
  exact ((snd _ _).fst'.snd').finite_cases hbranch

end Cslib.PCP.RegularConstraintGraph
