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

private theorem polytime_finTail (T : ℕ) :
    ComputableInPolyTime (@Fin.tail T (fun _ => D)) (encPi label) (encPi label) :=
  pi fun i => pi_apply label i.succ

private theorem polytime_finSnoc (T : ℕ) :
    ComputableInPolyTime (fun p : (Fin T → D) × D => Fin.snoc p.1 p.2)
      (encPair (encPi label) label) (encPi label) := by
  apply pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa only [Fin.snoc_last] using snd (encPi label) label
  · simpa only [Fin.snoc_castSucc, Function.comp_def] using
      (pi_apply label j).comp (fst (encPi label) label)

private theorem polytime_finTake {T n : ℕ} (hn : n ≤ T) :
    ComputableInPolyTime (Fin.take n hn (α := fun _ => D)) (encPi label) (encPi label) :=
  pi fun i => pi_apply label (i.castLE hn)

private theorem polytime_powRotWithInput
    (hrotate : ComputableInPolyTime rotate
      (encPair input (encPair vertex label)) (encPair vertex label)) (T : ℕ) :
    ComputableInPolyTime (RotationMap.powRotWithInput rotate T)
      (encPair input (encPair vertex (encPi label))) (encPair vertex (encPi label)) := by
  induction T with
  | zero => exact snd _ _
  | succ T ih =>
    have hhead : ComputableInPolyTime
        (fun p : P × (W × (Fin (T + 1) → D)) => rotate (p.1, p.2.1, p.2.2 0))
        (encPair input (encPair vertex (encPi label))) (encPair vertex label) :=
      hrotate.comp ((fst _ _).prod
        (((snd _ _).fst').prod ((pi_apply label 0).comp ((snd _ _).snd'))))
    have hrest := ih.comp ((fst _ _).prod (hhead.fst'.prod
      ((polytime_finTail (label := label) T).comp ((snd _ _).snd'))))
    exact hrest.fst'.prod ((polytime_finSnoc (label := label) T).comp (hrest.snd'.prod hhead.snd'))

private theorem polytime_walkAtWithInput
    (hrotate : ComputableInPolyTime rotate
      (encPair input (encPair vertex label)) (encPair vertex label)) (T m : ℕ) :
    ComputableInPolyTime
      (fun p : P × (W × (Fin T → D)) => RotationMap.walkAtWithInput rotate p m)
      (encPair input (encPair vertex (encPi label))) vertex :=
  ((polytime_powRotWithInput hrotate (min m T)).comp
    ((fst _ _).prod (((snd _ _).fst').prod
      ((polytime_finTake (Nat.min_le_right m T)).comp ((snd _ _).snd'))))).fst'

private theorem polytime_killedPowRotWithInput
    (hrotate : ComputableInPolyTime rotate
      (encPair input (encPair vertex label)) (encPair vertex label))
    (T q : ℕ) [NeZero q] (signal : Fin q ↪ List Bool) :
    ComputableInPolyTime
      (RotationMap.killedPowRotWithInput rotate T q)
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
  have hbranch (c : Fin T → Fin q) : ComputableInPolyTime
      (fun p : P × (W × ((Fin T → D) × (Fin T → Fin q))) =>
        RotationMap.killedPowRotWithInput rotate T q (p.1, p.2.1, p.2.2.1, c))
      (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
      (encPair vertex (encPair (encPi label) (encPi signal))) := by
    have hwalk : ComputableInPolyTime
        (fun p : P × (W × ((Fin T → D) × (Fin T → Fin q))) =>
          RotationMap.powRotWithInput rotate (killTime c)
            (p.1, p.2.1, Fin.take _ (killTime_le c) p.2.2.1))
        (encPair input (encPair vertex (encPair (encPi label) (encPi signal))))
        (encPair vertex (encPi label)) :=
      (polytime_powRotWithInput hrotate (killTime c)).comp
        ((fst _ _).prod (((snd _ _).fst').prod
          ((polytime_finTake (killTime_le c)).comp ((snd _ _).snd'.fst'))))
    dsimp only [RotationMap.killedPowRotWithInput]
    apply hwalk.fst'.prod
    apply prod ?_ (const c)
    apply pi
    intro i
    by_cases hi : i.val < killTime c
    · simpa only [dite_eq_left hi, Function.comp_def] using
        (pi_apply label ⟨i.val, hi⟩).comp hwalk.snd'
    · simpa only [dite_eq_right hi, Function.comp_def] using
        (pi_apply label i).comp ((snd input _).snd'.fst')
  exact ((snd input (encPair vertex (encPair (encPi label) (encPi signal)))).snd'.snd').finite_cases
    hbranch

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
      (polytime_killedPowRotWithInput hrotate T q signal).comp
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
            enc vertex := (polytime_walkAtWithInput hrotate T i.val).comp
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
